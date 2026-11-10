import ODELowerBoundExtensions.Release.Registers
import AdaptiveHamiltonianLowerBound.Access.Native
import SparseHamiltonian.MaskedProgram

set_option autoImplicit false

/-!
# Masked lifts: fixed layouts of masked spectator registers

The released time-dependent oracle families place an operator `A` on a workspace through fixed
registers only: untouched spectators, fixed relabellings, and control masks that apply `A` on some
branches of a known register and the identity on the others (the controlled time-indexed oracle
`TimeDependentExtensions.BlockEncoding.primitive`, `|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`, the
formalisation of the coherent and controlled access of the manuscript, eq. `hs:eq:blockspecial`;
the controlled call forms of the native access with
inverses and the controls of Lemma `access:lem:control` of Section `hsl:sec:main`).

* `IsMaskedLift Φ`: there are a finite register `Ω`, a fixed isometric identification
  `U : K ≃ ℂ^Ω ⊗ W` and a mask `m : Ω → Bool` with `Φ A = U⁻¹ (masked m A) U` for every `A`.
  Masks (`isMaskedLift_masked`), homogeneous spectators (`isMaskedLift_fiber`) and spectator
  wrappers (`ODELowerBoundExtensions.Release.IsWrap`; `isMaskedLift_of_isWrap`,
  `IsMaskedLift.wrap`) are masked lifts; masked lifts are closed under fixed relabellings
  (`IsMaskedLift.conj`) and further masks (`IsMaskedLift.masked`).
* A masked lift is unital, multiplicative and preserves adjoints and unitarity
  (`IsMaskedLift.map_one`, `map_mul`, `map_star`, `map_unitary`), so it carries a program over a
  family to a program over the lifted family (`liftProgram`, `eval_liftProgram`,
  `cost_liftProgram`).
* **A masked lift of an admissible label is admissible** with the same weight
  (`IsMaskedLift.admissible`): a masked native call is a native call whose masked branches apply
  the identity, and a masked input-independent unitary is an input-independent unitary.

Masked lifts contain the package's fixed-register forms: spectator wrappers
(`ODELowerBoundExtensions.Release.IsWrap`, `isMaskedLift_of_isWrap`) and the normal form
`A ↦ U⁻¹ (1_Ω ⊗ A) U` of `TimeDependentHamiltonianLowerBound.admissible_of_normal_form`
(`isMaskedLift_normal_form`). Unlike those, a mask may leave some branches untouched, which the
controlled call forms need. `IsMaskedLift.admissible` is the
`AdaptiveHamiltonianLowerBound.Access.Admissible` counterpart of
`TimeDependentLowerBoundExtensions.Core.maskedAccess` for Boolean certificates.
-/

namespace TimeDependentLowerBoundExtensions.Measured

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open ODELowerBoundExtensions.Release (IsWrap)
open SparseLowerBounds.Helpers.Adaptive.Access (masked_true_eq_fiber)
open scoped InnerProduct

variable {W K K' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- **Masked lifts**: `Φ A = U⁻¹ (masked m A) U` for a fixed finite register `Ω`, a fixed
isometric identification `U : K ≃ ℂ^Ω ⊗ W` and a fixed mask `m : Ω → Bool` (the operator on
the branches with `m = true`, the identity on the others). -/
def IsMaskedLift (Φ : (W →L[ℂ] W) → (K →L[ℂ] K)) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (U : K ≃ₗᵢ[ℂ] Joint Ω W) (m : Ω → Bool),
    ∀ A, Φ A = U.symm.conjStarAlgEquiv (MaskedProgram.masked m A)

/-! ### Register identities -/

/-- A mask of a conjugate is the conjugate of the mask by the fixed blockwise relabelling
`1 ⊗ V`. -/
theorem masked_conj {ι : Type*} [Fintype ι] (m : ι → Bool) (V : K ≃ₗᵢ[ℂ] K')
    (A : K' →L[ℂ] K') :
    MaskedProgram.masked m (V.symm.conjStarAlgEquiv A) =
      (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => V)).symm.conjStarAlgEquiv
        (MaskedProgram.masked m A) := by
  ext v i
  cases h : m i <;>
    simp [MaskedProgram.masked_apply, h, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- Two nested masks are one mask on the product register (active where both are), up to the
fixed flattening. -/
theorem masked_masked {ι Ω : Type} [Fintype ι] [Fintype Ω] (m' : ι → Bool) (m : Ω → Bool)
    (A : W →L[ℂ] W) :
    MaskedProgram.masked m' (MaskedProgram.masked m A) =
      (ODELowerBoundExtensions.Release.jointFlatten ι Ω W).conjStarAlgEquiv
        (MaskedProgram.masked (fun p : ι × Ω => m' p.1 && m p.2) A) := by
  ext v i ω
  cases h' : m' i <;> cases h : m ω <;>
    simp [MaskedProgram.masked_apply, h, h'] <;>
    rfl

/-- A mask of a block diagonal is a block diagonal on the product register (the identity on
the inactive branches), up to the fixed flattening. -/
theorem masked_diagonal {Ω S : Type} [Fintype Ω] [Fintype S] (m : Ω → Bool)
    (f : S → W →L[ℂ] W) :
    MaskedProgram.masked m (WeightedClock.diagonal f) =
      (ODELowerBoundExtensions.Release.jointFlatten Ω S W).conjStarAlgEquiv
        (WeightedClock.diagonal fun p : Ω × S => if m p.1 then f p.2 else 1) := by
  ext v ω σ
  cases h : m ω <;>
    simp [MaskedProgram.masked_apply, h] <;>
    rfl

/-! ### Closure -/

/-- A control mask is a masked lift. -/
theorem isMaskedLift_masked (Ω : Type) [Fintype Ω] (m : Ω → Bool) :
    IsMaskedLift (K := Joint Ω W) (MaskedProgram.masked m) :=
  ⟨Ω, inferInstance, LinearIsometryEquiv.refl ℂ _, m, fun _ => rfl⟩

/-- A homogeneous spectator register is a masked lift. -/
theorem isMaskedLift_fiber (Ω : Type) [Fintype Ω] :
    IsMaskedLift (K := Joint Ω W) (fun A => Joint.fiber (fun _ : Ω => A)) :=
  ⟨Ω, inferInstance, LinearIsometryEquiv.refl ℂ _, fun _ => true, fun A => by
    rw [masked_true_eq_fiber]; rfl⟩

/-- A spectator wrapper is a masked lift (the mask is everywhere active). -/
theorem isMaskedLift_of_isWrap {Wr : (W →L[ℂ] W) → (K →L[ℂ] K)} (hW : IsWrap Wr) :
    IsMaskedLift Wr := by
  obtain ⟨Ω, hΩ, U, hU⟩ := hW
  exact ⟨Ω, hΩ, U, fun _ => true, fun A => by rw [hU, masked_true_eq_fiber]⟩

/-- The normal form `A ↦ U⁻¹ (1_Ω ⊗ A) U` (a homogeneous spectator register under a fixed
isometric identification) is a masked lift. -/
theorem isMaskedLift_normal_form (Ω : Type) [Fintype Ω] (U : K ≃ₗᵢ[ℂ] Joint Ω W) :
    IsMaskedLift (fun A : W →L[ℂ] W => U.symm.conjStarAlgEquiv (Joint.fiber fun _ : Ω => A)) :=
  isMaskedLift_of_isWrap ⟨Ω, inferInstance, U, fun _ => rfl⟩

namespace IsMaskedLift

variable {Φ : (W →L[ℂ] W) → (K →L[ℂ] K)}

/-- Post-composition with a fixed relabelling. -/
theorem conj (hΦ : IsMaskedLift Φ) (V : K ≃ₗᵢ[ℂ] K') :
    IsMaskedLift (fun A => V.conjStarAlgEquiv (Φ A)) := by
  obtain ⟨Ω, hΩ, U, m, hU⟩ := hΦ
  exact ⟨Ω, hΩ, V.symm.trans U, m, fun A => by beta_reduce; rw [hU A]; rfl⟩

/-- A further control mask of a masked lift is a masked lift (the two masks combine on the
product register). -/
theorem masked (hΦ : IsMaskedLift Φ) (ι : Type) [Fintype ι] (m' : ι → Bool) :
    IsMaskedLift (fun A => MaskedProgram.masked m' (Φ A)) := by
  obtain ⟨Ω, _, U, m, hU⟩ := hΦ
  refine ⟨ι × Ω, inferInstance,
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => U)).trans
      (ODELowerBoundExtensions.Release.jointFlatten ι Ω W).symm,
    fun p => m' p.1 && m p.2, fun A => ?_⟩
  beta_reduce
  rw [hU A, masked_conj, masked_masked, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.conjStarAlgEquiv_trans,
    StarAlgEquiv.trans_apply]

/-- A spectator wrapper of a masked lift is a masked lift. -/
theorem wrap (hΦ : IsMaskedLift Φ) {Wr : (K →L[ℂ] K) → (K' →L[ℂ] K')} (hW : IsWrap Wr) :
    IsMaskedLift (fun A => Wr (Φ A)) := by
  obtain ⟨Ω', _, U', hU'⟩ := hW
  have e : (fun A => Wr (Φ A)) = fun A =>
      U'.symm.conjStarAlgEquiv (MaskedProgram.masked (fun _ : Ω' => true) (Φ A)) :=
    funext fun A => by rw [hU', masked_true_eq_fiber]
  rw [e]
  exact (hΦ.masked Ω' (fun _ => true)).conj U'.symm

/-! ### Algebra -/

/-- A masked lift is unital. -/
theorem map_one (hΦ : IsMaskedLift Φ) : Φ 1 = 1 := by
  obtain ⟨Ω, _, U, m, hU⟩ := hΦ
  rw [hU, MaskedProgram.masked_one, _root_.map_one]

/-- A masked lift is multiplicative. -/
theorem map_mul (hΦ : IsMaskedLift Φ) (A A' : W →L[ℂ] W) : Φ (A * A') = Φ A * Φ A' := by
  obtain ⟨Ω, _, U, m, hU⟩ := hΦ
  rw [hU, hU, hU, MaskedProgram.masked_mul, _root_.map_mul]

/-- A masked lift preserves adjoints. -/
theorem map_star (hΦ : IsMaskedLift Φ) (A : W →L[ℂ] W) : Φ (star A) = star (Φ A) := by
  obtain ⟨Ω, _, U, m, hU⟩ := hΦ
  have h : MaskedProgram.masked m (star A) = star (MaskedProgram.masked m A) := by
    simp only [star_eq_adjoint, MaskedProgram.masked_adjoint]
  rw [hU, hU, h]
  exact U.symm.conjStarAlgEquiv.map_star' _

/-- A masked lift preserves unitarity. -/
theorem map_unitary (hΦ : IsMaskedLift Φ) {A : W →L[ℂ] W} (hA : IsUnitary A) :
    IsUnitary (Φ A) := by
  obtain ⟨Ω, _, U, m, hU⟩ := hΦ
  rw [hU]
  exact (MaskedProgram.masked_unitary m A hA).transport U.symm

/-- **A masked lift of an admissible label is admissible** with the same weight. -/
theorem admissible (hΦ : IsMaskedLift Φ) {X N Z : Type*} [Fintype N] [DecidableEq N]
    [Fintype Z] [AddCommGroup Z] {s : ℕ} {D : NativeSparseBlockEncoding.Data X N Z s}
    {O : X → W →L[ℂ] W} {w : ℕ} (hO : AdaptiveHamiltonianLowerBound.Access.Admissible D O w) :
    AdaptiveHamiltonianLowerBound.Access.Admissible D (fun x => Φ (O x)) w := by
  rcases hO with ⟨⟨S, _, ℓ, call, hcall⟩, hw⟩ | ⟨hc, hu⟩
  · obtain ⟨Ω, _, U, m, hU⟩ := hΦ
    refine Or.inl ⟨⟨Ω × S, inferInstance,
      U.trans ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Ω => ℓ)).trans
        (ODELowerBoundExtensions.Release.jointFlatten Ω S _).symm),
      fun p => if m p.1 then call p.2 else none, fun x => ?_⟩, hw⟩
    have hif : (WeightedClock.diagonal fun p : Ω × S =>
        if m p.1 then AdaptiveHamiltonianLowerBound.Access.callOp D (call p.2) x else 1) =
        WeightedClock.diagonal fun p : Ω × S => AdaptiveHamiltonianLowerBound.Access.callOp D
          (if m p.1 then call p.2 else none) x := by
      congr 1
      funext p
      split_ifs <;> rfl
    beta_reduce
    rw [hU, hcall x, masked_conj, masked_diagonal, hif, LinearIsometryEquiv.symm_trans,
      LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_symm,
      LinearIsometryEquiv.conjStarAlgEquiv_trans, LinearIsometryEquiv.conjStarAlgEquiv_trans,
      StarAlgEquiv.trans_apply, StarAlgEquiv.trans_apply]
  · exact Or.inr ⟨fun x x' => congrArg Φ (hc x x'), fun x => hΦ.map_unitary (hu x)⟩

end IsMaskedLift

/-! ### Programs -/

variable {X L L' : Type*} {O : L → X → W →L[ℂ] W} {B : L' → X → K →L[ℂ] K}

/-- **A program carried through a masked lift**: fixed unitaries are lifted, every call of `l`
becomes a call of `g l` (the labelled counterpart of `SparseHamiltonian.MaskedProgram.compile`,
which is the case of one label and a fixed mask). -/
def liftProgram {Φ : (W →L[ℂ] W) → (K →L[ℂ] K)} (hΦ : IsMaskedLift Φ) (g : L → L') :
    MultiOracleCircuit.Program O → MultiOracleCircuit.Program B
  | .fixed U hU => .fixed (Φ U) (hΦ.map_unitary hU)
  | .query l => .query (g l)
  | .queryAdjoint l => .queryAdjoint (g l)
  | .seq p q => .seq (liftProgram hΦ g p) (liftProgram hΦ g q)

/-- The lifted program evaluates to the lift of the program, when the label `g l` of `B` is the
lift of the label `l` of `O`. -/
theorem eval_liftProgram {Φ : (W →L[ℂ] W) → (K →L[ℂ] K)} (hΦ : IsMaskedLift Φ) (g : L → L')
    (hB : ∀ l x, B (g l) x = Φ (O l x)) (p : MultiOracleCircuit.Program O) (x : X) :
    (liftProgram (B := B) hΦ g p).eval x = Φ (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => exact hB l x
  | queryAdjoint l =>
    show star (B (g l) x) = Φ (star (O l x))
    rw [hB, hΦ.map_star]
  | seq p q hp hq =>
    show (liftProgram (B := B) hΦ g p).eval x * (liftProgram (B := B) hΦ g q).eval x =
      Φ (p.eval x * q.eval x)
    rw [hp, hq, hΦ.map_mul]

/-- The lifted program has the cost of the program under the pulled-back weight. -/
theorem cost_liftProgram {Φ : (W →L[ℂ] W) → (K →L[ℂ] K)} (hΦ : IsMaskedLift Φ) (g : L → L')
    (p : MultiOracleCircuit.Program O) (w : L' → ℕ) :
    (liftProgram (B := B) hΦ g p).cost w = p.cost (fun l => w (g l)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    show (liftProgram (B := B) hΦ g p).cost w + (liftProgram (B := B) hΦ g q).cost w =
      p.cost (fun l => w (g l)) + q.cost (fun l => w (g l))
    rw [hp, hq]

end

end TimeDependentLowerBoundExtensions.Measured
