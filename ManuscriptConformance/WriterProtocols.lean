import ManuscriptConformance.WriterAccess
import SparseLinearSystems.Protocol.Tree

/-!
# Writer access in the physical workspaces, with further supplied calls and measured protocols

The converted workspace of a physical workspace `K` is `PiLp 2 (fun _ : Z => K)`: `K` with one
more register holding a word of the value type `Z`, the scratch register, clean in its zero word
(`single0`). `Impl` in this form (the encoding `single0`) passes through the fixed register layers
from which the physical families are built (`fconj`, `fdiag`, `fspectator`, `fmasked`), keeping
the converted workspace one register larger than the package's own physical workspace at every
layer; every converted call is the primitive call under one fixed unital star-algebra
homomorphism (`HomOf`). Further supplied calls on the physical workspace (the source preparations
of the ODE and linear-system theorems) act with the scratch register a spectator (`fextra`).

The measured protocols (`ODERepeatProtocol.TrialFamily`, `Protocol`, and the adaptive
`SparseLinearSystems.Protocol.TestRun`, `Tree`) are moved to the encoding by compiling every
circuit and encoding every seed and output isometry: every Born probability, the success mass and
the successful and conditional output densities are unchanged, and the worst-case weighted cost
is the cost of the original protocol under the converted weights.
-/

namespace SparseHamiltonian.WriterAccess

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxHeartbeats 1000000

/-! ### The scratch register outermost -/

section Flat
variable {K K₂ : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
  {X L M L₂ : Type*}

/-- The scratch register in its zero word. -/
abbrev single0 (Z K : Type*) [Fintype Z] [DecidableEq Z] [AddCommGroup Z]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] : K →L[ℂ] PiLp 2 (fun _ : Z => K) :=
  WeightedClock.boundary (fun t : Z => if t = 0 then 1 else 0) (fun _ => 1)

omit [CompleteSpace K] in
theorem single0_apply (v : K) (t : Z) : single0 Z K v t = if t = 0 then v else 0 := by
  rw [WeightedClock.boundary_apply]
  split_ifs <;> simp

theorem single0_isometry : (single0 Z K)† ∘L single0 Z K = 1 :=
  WeightedClock.boundary_isometry _ (fun t => by split_ifs <;> norm_num)
    (by simp) _ (fun _ => by ext v; simp)

/-- Swap two finite indices. -/
def swapPi (ι Z : Type*) [Fintype ι] [Fintype Z] :
    PiLp 2 (fun _ : ι => PiLp 2 (fun _ : Z => K)) ≃ₗᵢ[ℂ]
      PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => K)) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : ι) (_ : Z) => K)).symm.trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.sigmaEquivProd ι Z)).trans
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.prodComm ι Z)).trans
        ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.sigmaEquivProd Z ι).symm).trans
          (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Z) (_ : ι) => K)))))

omit [CompleteSpace K] in
@[simp] theorem swapPi_apply (ι Z : Type*) [Fintype ι] [Fintype Z]
    (u : PiLp 2 (fun _ : ι => PiLp 2 (fun _ : Z => K))) (t : Z) (i : ι) :
    swapPi ι Z u t i = u i t := rfl

omit [CompleteSpace K] in
@[simp] theorem swapPi_symm_apply (ι Z : Type*) [Fintype ι] [Fintype Z]
    (u : PiLp 2 (fun _ : Z => PiLp 2 (fun _ : ι => K))) (i : ι) (t : Z) :
    (swapPi ι Z).symm u i t = u t i := rfl

/-- The converted calls are images of the primitive calls under one fixed unital star-algebra
homomorphism (spectator registers). -/
def HomOf {H K' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    (Ow : M → X → K' →L[ℂ] K') (Ow₀ : M → X → H →L[ℂ] H) : Prop :=
  ∃ Φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K' →L[ℂ] K'), ∀ m x, Ow m x = Φ (Ow₀ m x)

theorem HomOf.refl {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Ow₀ : M → X → H →L[ℂ] H) : HomOf Ow₀ Ow₀ :=
  ⟨StarAlgHom.id ℂ _, fun _ _ => rfl⟩

theorem HomOf.conj {H K' K'' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    [NormedAddCommGroup K''] [InnerProductSpace ℂ K''] [CompleteSpace K'']
    {Ow : M → X → K' →L[ℂ] K'} {Ow₀ : M → X → H →L[ℂ] H} (h : HomOf Ow Ow₀) (g : K' ≃ₗᵢ[ℂ] K'') :
    HomOf (fun m x => g.conjStarAlgEquiv (Ow m x)) Ow₀ := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨(g.conjStarAlgEquiv : (K' →L[ℂ] K') →⋆ₐ[ℂ] (K'' →L[ℂ] K'')).comp Φ,
    fun m x => by simp only [hΦ]; rfl⟩

theorem HomOf.diag {H K' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    {Ow : M → X → K' →L[ℂ] K'} {Ow₀ : M → X → H →L[ℂ] H} (h : HomOf Ow Ow₀)
    (ι : Type*) [Fintype ι] :
    HomOf (fun m x => WeightedClock.diagonal (fun _ : ι => Ow m x)) Ow₀ := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨(diagHom ι).comp Φ, fun m x => by simp only [hΦ]; rfl⟩

/-- The same program over a family with further labels. -/
def relabelInl {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    {Ow : M → X → K' →L[ℂ] K'} {U : L₂ → X → K' →L[ℂ] K'} :
    MultiOracleCircuit.Program Ow → MultiOracleCircuit.Program (Sum.elim Ow U)
  | .fixed V hV => .fixed V hV
  | .query m => .query (.inl m)
  | .queryAdjoint m => .queryAdjoint (.inl m)
  | .seq p q => .seq (relabelInl p) (relabelInl q)

theorem relabelInl_eval {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] {Ow : M → X → K' →L[ℂ] K'} {U : L₂ → X → K' →L[ℂ] K'}
    (p : MultiOracleCircuit.Program Ow) (x : X) :
    (relabelInl (U := U) p).eval x = p.eval x := by
  induction p with
  | fixed V hV => rfl
  | query m => rfl
  | queryAdjoint m => rfl
  | seq p q hp hq => simp only [relabelInl, MultiOracleCircuit.Program.eval_seq, hp, hq]

theorem relabelInl_cost {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] {Ow : M → X → K' →L[ℂ] K'} {U : L₂ → X → K' →L[ℂ] K'}
    (p : MultiOracleCircuit.Program Ow) (w : M ⊕ L₂ → ℕ) :
    (relabelInl (U := U) p).cost w = p.cost (fun m => w (.inl m)) := by
  induction p with
  | fixed V hV => rfl
  | query m => rfl
  | queryAdjoint m => rfl
  | seq p q hp hq => simp only [relabelInl, MultiOracleCircuit.Program.cost_seq, hp, hq]

variable {O : L → X → K →L[ℂ] K} {Ow : M → X → PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K)}
  {circ : L → MultiOracleCircuit.Program Ow} {c : L → (M → ℕ) → ℕ}

/-- A fixed change of coordinates of the physical workspace. -/
theorem Impl.fconj (h : Impl O Ow (single0 Z K) circ c) (f : K ≃ₗᵢ[ℂ] K₂) :
    Impl (fun l x => f.conjStarAlgEquiv (O l x))
      (fun m x => (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Z => f)).conjStarAlgEquiv (Ow m x))
      (single0 Z K₂)
      (fun l => (circ l).transport (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Z => f))) c where
  iso := single0_isometry
  unitary l x := (h.unitary l x).transport f
  unitaryW m x := (h.unitaryW m x).transport _
  intertwines l x := by
    apply ContinuousLinearMap.ext
    intro v
    rw [MultiOracleCircuit.Program.eval_transport]
    have h1 : (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Z => f)).symm (single0 Z K₂ v) =
        single0 Z K (f.symm v) := by
      apply PiLp.ext
      intro t
      change f.symm (single0 Z K₂ v t) = _
      rw [single0_apply, single0_apply]
      split_ifs <;> simp
    have h2 : ∀ w : K, (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Z => f)) (single0 Z K w) =
        single0 Z K₂ (f w) := by
      intro w
      apply PiLp.ext
      intro t
      change f (single0 Z K w t) = _
      rw [single0_apply, single0_apply]
      split_ifs <;> simp
    have hv := congrArg (fun T => T (f.symm v)) (h.intertwines l x)
    simp only [comp_apply] at hv
    simp only [comp_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, h1, hv, h2]
  cost l w := by rw [MultiOracleCircuit.Program.cost_transport, h.cost]

/-- Diagonal over a finite index; the scratch register stays outermost. -/
theorem Impl.fdiag (h : Impl O Ow (single0 Z K) circ c) (ι : Type*) [Fintype ι] :
    Impl (fun l x => WeightedClock.diagonal (fun _ : ι => O l x))
      (fun m x => (swapPi (K := K) ι Z).conjStarAlgEquiv
        (WeightedClock.diagonal (fun _ : ι => Ow m x)))
      (single0 Z (PiLp 2 (fun _ : ι => K)))
      (fun l => (diagProg ι (circ l)).transport (swapPi (K := K) ι Z)) c where
  iso := single0_isometry
  unitary l x := CoherentQuerySchedule.diagonal_unitary _ (fun _ => h.unitary l x)
  unitaryW m x :=
    (CoherentQuerySchedule.diagonal_unitary _ (fun _ => h.unitaryW m x)).transport _
  intertwines l x := by
    apply ContinuousLinearMap.ext
    intro v
    rw [MultiOracleCircuit.Program.eval_transport, diagProg_eval]
    have h1 : (swapPi (K := K) ι Z).symm (single0 Z (PiLp 2 (fun _ : ι => K)) v) =
        WithLp.toLp 2 (fun i => single0 Z K (v i)) := by
      apply PiLp.ext
      intro i
      apply PiLp.ext
      intro t
      rw [swapPi_symm_apply, single0_apply]
      change _ = single0 Z K (v i) t
      rw [single0_apply]
      split_ifs <;> rfl
    have hv : ∀ i, (circ l).eval x (single0 Z K (v i)) = single0 Z K (O l x (v i)) := fun i => by
      have := congrArg (fun T => T (v i)) (h.intertwines l x)
      simpa only [comp_apply] using this
    simp only [comp_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, h1]
    apply PiLp.ext
    intro t
    apply PiLp.ext
    intro i
    rw [swapPi_apply, WeightedClock.diagonal_apply]
    change (circ l).eval x (single0 Z K (v i)) t = _
    rw [hv, single0_apply, single0_apply]
    split_ifs <;> rfl
  cost l w := by rw [MultiOracleCircuit.Program.cost_transport, diagProg_cost, h.cost]

/-- **A converted implementation**: the calls of the physical family `O` on `K` are implemented on
`K` with the scratch register, by a family whose calls are the primitive calls `Ow₀` under one fixed
unital star-algebra homomorphism, at the weighted costs `c`. -/
def FImplH (Z : Type*) [Fintype Z] [DecidableEq Z] [AddCommGroup Z] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (O : L → X → K →L[ℂ] K) (Ow₀ : M → X → H →L[ℂ] H) (c : L → (M → ℕ) → ℕ) : Prop :=
  ∃ (Ow : M → X → PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K))
    (circ : L → MultiOracleCircuit.Program Ow),
    Impl O Ow (single0 Z K) circ c ∧ HomOf Ow Ow₀

namespace FImplH
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Ow₀ : M → X → H →L[ℂ] H}

theorem congr {O O' : L → X → K →L[ℂ] K} (h : FImplH Z O Ow₀ c) (hO : ∀ l x, O l x = O' l x) :
    FImplH Z O' Ow₀ c := by
  obtain ⟨Ow, circ, hI, hH⟩ := h
  exact ⟨Ow, circ, hI.congr hO, hH⟩

theorem conj {O : L → X → K →L[ℂ] K} (h : FImplH Z O Ow₀ c) (f : K ≃ₗᵢ[ℂ] K₂) :
    FImplH Z (fun l x => f.conjStarAlgEquiv (O l x)) Ow₀ c := by
  obtain ⟨Ow, circ, hI, hH⟩ := h
  exact ⟨_, _, hI.fconj f, hH.conj _⟩

theorem diag {O : L → X → K →L[ℂ] K} (h : FImplH Z O Ow₀ c) (ι : Type*) [Fintype ι] :
    FImplH Z (fun l x => WeightedClock.diagonal (fun _ : ι => O l x)) Ow₀ c := by
  obtain ⟨Ow, circ, hI, hH⟩ := h
  exact ⟨_, _, hI.fdiag ι, (hH.diag ι).conj _⟩

theorem spectator {B : Type*} [Fintype B] [DecidableEq B] (S : Type*) [Fintype S]
    {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} (h : FImplH Z F Ow₀ c) :
    FImplH Z (fun l x => LookupFromBasisOracle.spectator (S := S) (F l x)) Ow₀ c :=
  (h.diag S).conj (RegisterEquivalences.productFlatten S B)

theorem masked {B : Type*} [Fintype B] [DecidableEq B] (ι : Type*) [Fintype ι]
    {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} (h : FImplH Z F Ow₀ c) :
    FImplH Z (NativeMaskedProgram.oracle (ι := ι) F) Ow₀ c := by
  refine ((h.spectator ((Bool × B) × B)).diag ι).congr fun l x => ?_
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rfl

end FImplH

/-- Further supplied calls on the physical workspace, with the scratch register a spectator, one
call each. -/
theorem Impl.fextra (h : Impl O Ow (single0 Z K) circ c) (U : L₂ → X → K →L[ℂ] K)
    (hU : ∀ l x, IsUnitary (U l x)) :
    Impl (Sum.elim O U) (Sum.elim Ow (fun l x => WeightedClock.diagonal (fun _ : Z => U l x)))
      (single0 Z K)
      (Sum.elim (fun l => relabelInl (circ l)) (fun l => .query (.inr l)))
      (Sum.elim (fun l w => c l (fun m => w (.inl m))) (fun l w => w (.inr l))) where
  iso := h.iso
  unitary k x := by
    cases k with
    | inl l => exact h.unitary l x
    | inr l => exact hU l x
  unitaryW k x := by
    cases k with
    | inl m => exact h.unitaryW m x
    | inr l => exact CoherentQuerySchedule.diagonal_unitary _ (fun _ => hU l x)
  intertwines k x := by
    cases k with
    | inl l =>
      change (relabelInl (circ l)).eval x ∘L _ = _ ∘L O l x
      rw [relabelInl_eval]
      exact h.intertwines l x
    | inr l =>
      apply ContinuousLinearMap.ext
      intro v
      apply PiLp.ext
      intro t
      change U l x (single0 Z K v t) = single0 Z K (U l x v) t
      rw [single0_apply, single0_apply]
      split_ifs <;> simp
  cost k w := by
    cases k with
    | inl l =>
      change (relabelInl (circ l)).cost w = c l (fun m => w (.inl m))
      rw [relabelInl_cost, h.cost]
    | inr l => rfl

/-- Further supplied calls, for a converted implementation: the converted family has the primitive
calls under a fixed unital star-algebra homomorphism and the further calls with the scratch register
a spectator. -/
theorem FImplH.extra {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Ow₀ : M → X → H →L[ℂ] H} {O : L → X → K →L[ℂ] K} (h : FImplH Z O Ow₀ c)
    (U : L₂ → X → K →L[ℂ] K) (hU : ∀ l x, IsUnitary (U l x)) :
    ∃ (Ow : M ⊕ L₂ → X → PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K))
      (circ : L ⊕ L₂ → MultiOracleCircuit.Program Ow)
      (Φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (PiLp 2 (fun _ : Z => K) →L[ℂ] PiLp 2 (fun _ : Z => K))),
      Impl (Sum.elim O U) Ow (single0 Z K) circ
        (Sum.elim (fun l w => c l (fun m => w (.inl m))) (fun l w => w (.inr l))) ∧
      (∀ m x, Ow (.inl m) x = Φ (Ow₀ m x)) ∧
      (∀ l x, Ow (.inr l) x = diagHom (K' := K) Z (U l x)) := by
  obtain ⟨Ow, circ, hI, Φ, hΦ⟩ := h
  exact ⟨_, _, Φ, hI.fextra U hU, fun m x => hΦ m x, fun l x => rfl⟩

end Flat

/-! ### Measured protocols on the encoding -/

section Protocols
variable {K K' P F : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {X L M : Type*}
  {O : L → X → K →L[ℂ] K} {Ow : M → X → K' →L[ℂ] K'} {E : K →L[ℂ] K'}
  {circ : L → MultiOracleCircuit.Program Ow} {c : L → (M → ℕ) → ℕ}

theorem encode_isometry (h : Impl O Ow E circ c) {J : P →L[ℂ] K} (hJ : J† ∘L J = 1) :
    (E ∘L J)† ∘L (E ∘L J) = 1 := by
  rw [adjoint_comp, comp_assoc, ← comp_assoc _ E J, h.iso, one_def, id_comp]
  exact hJ

/-- The trial family with every circuit compiled and the seed and output encoded. -/
def encodeTrials (h : Impl O Ow E circ c) (t : ODERepeatProtocol.TrialFamily O P) :
    ODERepeatProtocol.TrialFamily Ow P where
  choices := t.choices
  choices_pos := t.choices_pos
  circuit j := EncodedLabeledProgram.compile E h.iso circ (t.circuit j)
  seed := E t.seed
  seed_unit := by rw [norm_encode h.iso, t.seed_unit]
  output := E ∘L t.output
  output_isometry := encode_isometry h t.output_isometry

theorem encodeTrials_amplitude (h : Impl O Ow E circ c)
    (t : ODERepeatProtocol.TrialFamily O P) (x : X) (j : Fin t.choices) :
    (encodeTrials h t).amplitude x j = t.amplitude x j := by
  have hE : ∀ v, (E†) (E v) = v := fun v => by
    simpa only [comp_apply, one_def, id_apply] using congrArg (fun T => T v) h.iso
  change ((E ∘L t.output)†) ((EncodedLabeledProgram.compile E h.iso circ (t.circuit j)).eval x
    (E t.seed)) = (t.output†) ((t.circuit j).eval x t.seed)
  have hc := congrArg (fun T => T t.seed) ((transfer h (t.circuit j)).2.1 x)
  simp only [comp_apply] at hc
  rw [hc, adjoint_comp, comp_apply, hE]

theorem encodeTrials_probability (h : Impl O Ow E circ c)
    (t : ODERepeatProtocol.TrialFamily O P) (x : X) (j : Fin t.choices) :
    (encodeTrials h t).probability x j = t.probability x j := by
  unfold ODERepeatProtocol.TrialFamily.probability
  rw [encodeTrials_amplitude]

theorem encodeTrials_meanSuccess (h : Impl O Ow E circ c)
    (t : ODERepeatProtocol.TrialFamily O P) (x : X) :
    (encodeTrials h t).meanSuccess x = t.meanSuccess x := by
  unfold ODERepeatProtocol.TrialFamily.meanSuccess
  simp only [encodeTrials_probability]
  rfl

theorem encodeTrials_oneTrialDensity (h : Impl O Ow E circ c)
    (t : ODERepeatProtocol.TrialFamily O P) (x : X) :
    (encodeTrials h t).oneTrialDensity x = t.oneTrialDensity x := by
  unfold ODERepeatProtocol.TrialFamily.oneTrialDensity
    ODERepeatProtocol.TrialFamily.outputDirection
  simp only [encodeTrials_probability, encodeTrials_amplitude]
  rfl

theorem encodeTrials_maxCost (h : Impl O Ow E circ c)
    (t : ODERepeatProtocol.TrialFamily O P) (w : M → ℕ) :
    (encodeTrials h t).maxCost w = t.maxCost (fun l => c l w) := by
  unfold ODERepeatProtocol.TrialFamily.maxCost
  exact congrArg (Finset.univ.sup ·) (funext fun j => (transfer h (t.circuit j)).1 w)

/-- The protocol with every trial family encoded. -/
def encodeProtocol (h : Impl O Ow E circ c) :
    ODERepeatProtocol.Protocol O P → ODERepeatProtocol.Protocol Ow P
  | .abort => .abort
  | .freshTrial t k => .freshTrial (encodeTrials h t) (encodeProtocol h k)

theorem encodeProtocol_failureMass (h : Impl O Ow E circ c)
    (p : ODERepeatProtocol.Protocol O P) (x : X) :
    (encodeProtocol h p).failureMass x = p.failureMass x := by
  induction p with
  | abort => rfl
  | freshTrial t k hk =>
    simp only [encodeProtocol, ODERepeatProtocol.Protocol.failureMass, hk,
      encodeTrials_meanSuccess]

theorem encodeProtocol_successMass (h : Impl O Ow E circ c)
    (p : ODERepeatProtocol.Protocol O P) (x : X) :
    (encodeProtocol h p).successMass x = p.successMass x := by
  simp only [ODERepeatProtocol.Protocol.successMass, encodeProtocol_failureMass]

theorem encodeProtocol_successDensity (h : Impl O Ow E circ c)
    (p : ODERepeatProtocol.Protocol O P) (x : X) :
    (encodeProtocol h p).successDensity x = p.successDensity x := by
  induction p with
  | abort => rfl
  | freshTrial t k hk =>
    simp only [encodeProtocol, ODERepeatProtocol.Protocol.successDensity, hk,
      encodeTrials_meanSuccess, encodeTrials_oneTrialDensity]

theorem encodeProtocol_conditionalDensity (h : Impl O Ow E circ c)
    (p : ODERepeatProtocol.Protocol O P) (x : X) :
    (encodeProtocol h p).conditionalDensity x = p.conditionalDensity x := by
  simp only [ODERepeatProtocol.Protocol.conditionalDensity, encodeProtocol_successMass,
    encodeProtocol_successDensity]

theorem encodeProtocol_worstCost (h : Impl O Ow E circ c)
    (p : ODERepeatProtocol.Protocol O P) (w : M → ℕ) :
    (encodeProtocol h p).worstCost w = p.worstCost (fun l => c l w) := by
  induction p with
  | abort => rfl
  | freshTrial t k hk =>
    simp only [encodeProtocol, ODERepeatProtocol.Protocol.worstCost, hk, encodeTrials_maxCost]

theorem encodeProtocol_repeat (h : Impl O Ow E circ c)
    (t : ODERepeatProtocol.TrialFamily O P) (r : ℕ) :
    encodeProtocol h (ODERepeatProtocol.Protocol.repeatTrials t r) =
      ODERepeatProtocol.Protocol.repeatTrials (encodeTrials h t) r := by
  induction r with
  | zero => rfl
  | succ r hr =>
    simp only [ODERepeatProtocol.Protocol.repeatTrials, encodeProtocol, hr]

/-- The four-trial protocol of the ODE theorems, encoded: the same protocol of the compiled
circuits on the encoded seed and output isometry. -/
theorem encodeProtocol_fourTrials (h : Impl O Ow E circ c)
    (q : ℕ → MultiOracleCircuit.Program O) (Mc : ℕ) (hM : 0 < Mc) (ψ : K) (hψ : ‖ψ‖ = 1)
    (J : P →L[ℂ] K) (hJ : J† ∘L J = 1) :
    encodeProtocol h (ODERepeatProtocol.fourTrials q Mc hM ψ hψ J hJ) =
      ODERepeatProtocol.fourTrials (fun j => EncodedLabeledProgram.compile E h.iso circ (q j))
        Mc hM (E ψ) (by rw [norm_encode h.iso, hψ]) (E ∘L J) (encode_isometry h hJ) := by
  unfold ODERepeatProtocol.fourTrials
  rw [encodeProtocol_repeat]
  rfl

/-- A test run with its circuit compiled and its seed and flag encoded. -/
def encodeRun (h : Impl O Ow E circ c) (t : SparseLinearSystems.Protocol.TestRun O F) :
    SparseLinearSystems.Protocol.TestRun Ow F where
  circuit := EncodedLabeledProgram.compile E h.iso circ t.circuit
  seed := E t.seed
  seed_unit := by rw [norm_encode h.iso, t.seed_unit]
  flag := E ∘L t.flag
  flag_isometry := encode_isometry h t.flag_isometry

theorem encodeRun_probability (h : Impl O Ow E circ c)
    (t : SparseLinearSystems.Protocol.TestRun O F) (x : X) :
    (encodeRun h t).probability x = t.probability x := by
  have hE : ∀ v, (E†) (E v) = v := fun v => by
    simpa only [comp_apply, one_def, id_apply] using congrArg (fun T => T v) h.iso
  unfold SparseLinearSystems.Protocol.TestRun.probability
  change ‖((E ∘L t.flag)†) ((EncodedLabeledProgram.compile E h.iso circ t.circuit).eval x
    (E t.seed))‖ ^ 2 = _
  have hc := congrArg (fun T => T t.seed) ((transfer h t.circuit).2.1 x)
  simp only [comp_apply] at hc
  rw [hc, adjoint_comp, comp_apply, hE]

/-- The adaptive protocol with every run and leaf encoded. -/
def encodeTree (h : Impl O Ow E circ c) :
    SparseLinearSystems.Protocol.Tree O F P → SparseLinearSystems.Protocol.Tree Ow F P
  | .final p => .final (encodeProtocol h p)
  | .test t s f => .test (encodeRun h t) (encodeTree h s) (encodeTree h f)

theorem encodeTree_successMass (h : Impl O Ow E circ c)
    (T : SparseLinearSystems.Protocol.Tree O F P) (x : X) :
    (encodeTree h T).successMass x = T.successMass x := by
  unfold SparseLinearSystems.Protocol.Tree.successMass
  induction T with
  | final p => exact encodeProtocol_successMass h p x
  | test t s f hs hf =>
    simp only [encodeTree, SparseLinearSystems.Protocol.Tree.expect, hs, hf,
      encodeRun_probability]

theorem encodeTree_successDensity (h : Impl O Ow E circ c)
    (T : SparseLinearSystems.Protocol.Tree O F P) (x : X) :
    (encodeTree h T).successDensity x = T.successDensity x := by
  unfold SparseLinearSystems.Protocol.Tree.successDensity
  induction T with
  | final p => exact encodeProtocol_successDensity h p x
  | test t s f hs hf =>
    simp only [encodeTree, SparseLinearSystems.Protocol.Tree.expect, hs, hf,
      encodeRun_probability]

theorem encodeTree_conditionalDensity (h : Impl O Ow E circ c)
    (T : SparseLinearSystems.Protocol.Tree O F P) (x : X) :
    (encodeTree h T).conditionalDensity x = T.conditionalDensity x := by
  simp only [SparseLinearSystems.Protocol.Tree.conditionalDensity, encodeTree_successMass,
    encodeTree_successDensity]

theorem encodeTree_worstCost (h : Impl O Ow E circ c)
    (T : SparseLinearSystems.Protocol.Tree O F P) (w : M → ℕ) :
    (encodeTree h T).worstCost w = T.worstCost (fun l => c l w) := by
  induction T with
  | final p => exact encodeProtocol_worstCost h p w
  | test t s f hs hf =>
    simp only [encodeTree, SparseLinearSystems.Protocol.Tree.worstCost, hs, hf]
    rw [show (encodeRun h t).circuit = EncodedLabeledProgram.compile E h.iso circ t.circuit from rfl,
      (transfer h t.circuit).1]

end Protocols

/-! ### Scaled weights and the base factorization -/

section Scaled
variable {K P F : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {X L : Type*} {O : L → X → K →L[ℂ] K}

theorem cost_le_mul (p : MultiOracleCircuit.Program O) {w₁ w₂ : L → ℕ} {k : ℕ}
    (h : ∀ l, w₁ l ≤ k * w₂ l) : p.cost w₁ ≤ k * p.cost w₂ := by
  induction p with
  | fixed V hV => simp
  | query l => exact h l
  | queryAdjoint l => exact h l
  | seq p q hp hq =>
    simp only [MultiOracleCircuit.Program.cost_seq]
    rw [Nat.mul_add]
    exact Nat.add_le_add hp hq

theorem protocol_worstCost_le_mul (p : ODERepeatProtocol.Protocol O P) {w₁ w₂ : L → ℕ} {k : ℕ}
    (h : ∀ l, w₁ l ≤ k * w₂ l) : p.worstCost w₁ ≤ k * p.worstCost w₂ := by
  induction p with
  | abort => simp [ODERepeatProtocol.Protocol.worstCost]
  | freshTrial t r hr =>
    simp only [ODERepeatProtocol.Protocol.worstCost]
    rw [Nat.mul_add]
    refine Nat.add_le_add ?_ hr
    unfold ODERepeatProtocol.TrialFamily.maxCost
    refine Finset.sup_le fun j _ => (cost_le_mul (t.circuit j) h).trans ?_
    exact Nat.mul_le_mul_left k (Finset.le_sup (f := fun i => (t.circuit i).cost w₂)
      (Finset.mem_univ j))

theorem tree_worstCost_le_mul (T : SparseLinearSystems.Protocol.Tree O F P) {w₁ w₂ : L → ℕ}
    {k : ℕ} (h : ∀ l, w₁ l ≤ k * w₂ l) : T.worstCost w₁ ≤ k * T.worstCost w₂ := by
  induction T with
  | final p => exact protocol_worstCost_le_mul p h
  | test t s f hs hf =>
    simp only [SparseLinearSystems.Protocol.Tree.worstCost]
    rw [Nat.mul_add]
    refine Nat.add_le_add (cost_le_mul t.circuit h) (max_le ?_ ?_)
    · exact hs.trans (Nat.mul_le_mul_left k (le_max_left _ _))
    · exact hf.trans (Nat.mul_le_mul_left k (le_max_right _ _))

end Scaled


section Base
variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- The primitive conversion in this form: its scratch register is already outermost. -/
theorem fimpl_writer (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1) :
    Impl (oracles D) (writerOracles D W) (single0 Z (SparseFlagEmbedding.Space (n × n) Z))
      (circuits D W) wcost :=
  impl_writer D W hWu c hW

/-- The primitive conversion as a converted implementation. -/
theorem fimplH_writer (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1) :
    FImplH Z (oracles D) (writerOracles D W) wcost :=
  ⟨_, _, fimpl_writer D W hWu c hW, HomOf.refl _⟩

/-- The flattened primitives. -/
theorem fimplH_flat (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1) :
    FImplH Z (NativeSparseMaskedAccess.flatOracle D) (writerOracles D W) wcost :=
  (fimplH_writer D W hWu c hW).conj (NativeSparseMaskedAccess.layout (n := n) (Z := Z))

/-- Weights of the writer access with one further label: matrix calls (locators and writer) and
the further calls. -/
def wMatW : WQuery ⊕ Unit → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

def wSrcW : WQuery ⊕ Unit → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The converted weights of one further label. -/
abbrev wcostU : Query ⊕ Unit → (WQuery ⊕ Unit → ℕ) → ℕ :=
  Sum.elim (fun l w => wcost l (fun m => w (.inl m))) (fun l w => w (.inr l))

theorem wcostU_wMat_le (l : Query ⊕ Unit) :
    wcostU l wMatW ≤ 2 * Sum.elim (fun _ => 1) (fun _ => 0) l := by
  rcases l with l | l
  · cases l <;> simp [wcostU, wcost, wMatW]
  · simp [wcostU, wMatW]

theorem wcostU_wSrc (l : Query ⊕ Unit) :
    wcostU l wSrcW = Sum.elim (fun _ => 0) (fun _ => 1) l := by
  rcases l with l | l
  · cases l <;> simp [wcostU, wcost, wSrcW]
  · simp [wcostU, wSrcW]

end Base

section BaseBool

/-- The converted weights of two further labels (the two source interfaces of the ODE theorems). -/
abbrev wcostB : Query ⊕ Bool → (WQuery ⊕ Bool → ℕ) → ℕ :=
  Sum.elim (fun l w => wcost l (fun m => w (.inl m))) (fun l w => w (.inr l))

/-- Matrix calls (locators and writer) of the writer access with two further labels. -/
def wMatB : WQuery ⊕ Bool → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- Calls of one further label. -/
def wSrcB (b : Bool) : WQuery ⊕ Bool → ℕ := Sum.elim (fun _ => 0) (fun c => if c = b then 1 else 0)

theorem wcostB_wMat_le (l : Query ⊕ Bool) :
    wcostB l wMatB ≤ 2 * Sum.elim (fun _ => 1) (fun _ => 0) l := by
  rcases l with l | l
  · cases l <;> simp [wcostB, wcost, wMatB]
  · simp [wcostB, wMatB]

theorem wcostB_wSrc (b : Bool) (l : Query ⊕ Bool) :
    wcostB l (wSrcB b) = Sum.elim (fun _ => 0) (fun c => if c = b then 1 else 0) l := by
  rcases l with l | l
  · cases l <;> simp [wcostB, wcost, wSrcB]
  · simp [wcostB, wSrcB]

end BaseBool

end
end SparseHamiltonian.WriterAccess
