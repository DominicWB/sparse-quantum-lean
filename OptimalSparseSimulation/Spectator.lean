import NativeSignedFactor.Simulation

set_option autoImplicit false

/-!
# Native queries with spectator registers, up to a fixed change of coordinates

The constructions combined in Theorem `hs:thm:optimal` (the baseline simulation for
bounded `h`, the native signed factor and the large-sparsity core) act on different physical
workspaces. In each of them every oracle call is an original native primitive with spectator
registers. `SpectatorForm O O'` states this exactly: after one fixed linear isometric
equivalence `e : K ≃ ℂ^ι ⊗ W` (the space `PiLp 2 (fun _ : ι => W)`), every call `O' l x` is the
call `O l x` on `W` with the spectator register `ℂ^ι` (`CoherentQuerySchedule.oracle`). The
equivalence depends neither on the label nor on the instance.

* `SpectatorForm.oracle`, `SpectatorForm.spectator_conj`: base cases (a spectator extension of
  `O`, and the spectator extension of a fixed flattening of `O`); `SpectatorForm.diagonal`: the
  form is stable under a further spectator register.
* `Implements O V ε q`: the common form of `NativeSignedFactor.Simulates` for an arbitrary target
  family `V` (`simulates_iff`).
* `implements_of_spectatorForm`, `simulates_of_spectatorForm`: an implementation over `O'` with
  a known isometric input becomes one in the common form over `O`, with the same number of calls,
  the same unitarity and the same full-output error.
-/

namespace OptimalSparseSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian OracleCircuit
open scoped InnerProduct

section Generic

variable {W K : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {X L : Type*}

/-- `O'` is the oracle family `O` with a spectator register, up to one fixed change of
coordinates: a finite type `ι` and a fixed linear isometric equivalence
`e : K ≃ PiLp 2 (fun _ : ι => W)` with `e ∘ O' l x ∘ e⁻¹ = 1 ⊗ O l x` for every label `l` and
every instance `x`. -/
def SpectatorForm (O : L → X → W →L[ℂ] W) (O' : L → X → K →L[ℂ] K) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : K ≃ₗᵢ[ℂ] PiLp 2 (fun _ : ι => W)),
    ∀ l x, e.conjStarAlgEquiv (O' l x) = CoherentQuerySchedule.oracle (ι := ι) O l x

/-- A further spectator register keeps the form: the two spectator registers are merged into one
(`LinearIsometryEquiv.piLpCurry`). -/
theorem SpectatorForm.diagonal {O : L → X → W →L[ℂ] W} {O' : L → X → K →L[ℂ] K}
    (h : SpectatorForm O O') (κ : Type) [Fintype κ] :
    SpectatorForm O (CoherentQuerySchedule.oracle (ι := κ) O') := by
  obtain ⟨ι, hι, e, he⟩ := h
  refine ⟨Σ _ : κ, ι, inferInstance,
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : κ => e)).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : κ) (_ : ι) => W)).symm, fun l x => ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨k, i⟩
  have hk := congrArg (fun A : PiLp 2 (fun _ : ι => W) →L[ℂ] PiLp 2 (fun _ : ι => W) =>
    A (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : κ) (_ : ι) => W) v k) i) (he l x)
  exact hk

/-- The spectator extension of a fixed flattening of `O` has the form, with the spectator
register of the extension. -/
theorem SpectatorForm.spectator_conj {B S : Type} [Fintype B] [Fintype S]
    (O : L → X → W →L[ℂ] W) (e : W ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    SpectatorForm O
      (fun l x => LookupFromBasisOracle.spectator (S := S) (e.conjStarAlgEquiv (O l x))) := by
  refine ⟨S, inferInstance, (RegisterEquivalences.productFlatten S B).symm.trans
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : S => e.symm)), fun l x => ?_⟩
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  simp only [LookupFromBasisOracle.spectator, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.piLpCongrRight_apply, LinearIsometryEquiv.piLpCongrRight_symm,
    WeightedClock.diagonal_apply, CoherentQuerySchedule.oracle, PiLp.toLp_apply]

omit [CompleteSpace K] in
/-- The all-active mask is the diagonal operator. -/
theorem masked_true {ι : Type*} [Fintype ι] (U : K →L[ℂ] K) :
    MaskedProgram.masked (fun _ : ι => true) U = WeightedClock.diagonal (fun _ : ι => U) := rfl

/-! ### Programs over equal oracle families -/

/-- Read a program over one oracle family as a program over a pointwise equal family. -/
def ofEq {O₁ O₂ : L → X → K →L[ℂ] K} (h : ∀ l x, O₁ l x = O₂ l x) :
    MultiOracleCircuit.Program O₁ → MultiOracleCircuit.Program O₂
  | .fixed U hU => .fixed U hU
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (ofEq h p) (ofEq h q)

@[simp] theorem count_ofEq {O₁ O₂ : L → X → K →L[ℂ] K} (h : ∀ l x, O₁ l x = O₂ l x)
    (p : MultiOracleCircuit.Program O₁) : (ofEq h p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [ofEq, MultiOracleCircuit.Program.count_seq, hp, hq]

@[simp] theorem cost_ofEq {O₁ O₂ : L → X → K →L[ℂ] K} (h : ∀ l x, O₁ l x = O₂ l x)
    (p : MultiOracleCircuit.Program O₁) (w : L → ℕ) : (ofEq h p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [ofEq, MultiOracleCircuit.Program.cost_seq, hp, hq]

theorem eval_ofEq {O₁ O₂ : L → X → K →L[ℂ] K} (h : ∀ l x, O₁ l x = O₂ l x)
    (p : MultiOracleCircuit.Program O₁) (x : X) : (ofEq h p).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => exact (h l x).symm
  | queryAdjoint l =>
      change star (O₂ l x) = star (O₁ l x)
      rw [h l x]
  | seq p q hp hq => simp only [ofEq, MultiOracleCircuit.Program.eval_seq, hp, hq]

/-! ### Transport of a simulation to the common form -/

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- A known isometric input moved by a fixed linear isometric equivalence stays isometric. -/
theorem isometry_comp {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] (e : K ≃ₗᵢ[ℂ] K') (inp : P →L[ℂ] K) (hinp : inp† ∘L inp = 1) :
    (e.toLinearIsometry.toContinuousLinearMap ∘L inp)† ∘L
      (e.toLinearIsometry.toContinuousLinearMap ∘L inp) = 1 := by
  rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self] at hinp ⊢
  intro v
  change ‖e (inp v)‖ = ‖v‖
  rw [e.norm_map, hinp]

omit [CompleteSpace P] in
/-- The full-output error is unchanged when the program and the input are moved by the same
fixed linear isometric equivalence. -/
theorem conj_error {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] (e : K ≃ₗᵢ[ℂ] K') (A : K →L[ℂ] K) (inp : P →L[ℂ] K) (U : P →L[ℂ] P) :
    ‖e.conjStarAlgEquiv A ∘L (e.toLinearIsometry.toContinuousLinearMap ∘L inp) -
        (e.toLinearIsometry.toContinuousLinearMap ∘L inp) ∘L U‖ = ‖A ∘L inp - inp ∘L U‖ := by
  have hA : e.conjStarAlgEquiv A ∘L (e.toLinearIsometry.toContinuousLinearMap ∘L inp) -
      (e.toLinearIsometry.toContinuousLinearMap ∘L inp) ∘L U =
      e.toLinearIsometry.toContinuousLinearMap ∘L (A ∘L inp - inp ∘L U) := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [sub_apply, comp_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.symm_apply_apply, map_sub]
  rw [hA, LinearIsometry.norm_toContinuousLinearMap_comp]

/-- `Implements O V ε q`: the target family `V` is implemented in the common form of
`NativeSignedFactor.Simulates`, with the target `V x` in place of `e^{-itH(x)}`: a finite label
type `ι`, a known isometry `inp : P → ℂ^ι ⊗ W` and a program whose only oracle calls are calls
of `O` on every block of `ℂ^ι ⊗ W`, with at most `q` calls counting adjoints, unitary for every
instance, and with full-output error at most `ε` for `V x` with the same known embedding on input
and output. `Simulates O H t ε q` is `Implements O (fun x => e^{-itH(x)}) ε q`. -/
def Implements (O : L → X → W →L[ℂ] W) (V : X → P →L[ℂ] P) (ε q : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (inp : P →L[ℂ] PiLp 2 (fun _ : ι => W))
    (p : MultiOracleCircuit.Program (CoherentQuerySchedule.oracle (ι := ι) O)),
    inp† ∘L inp = 1 ∧ (p.count : ℝ) ≤ q ∧
      ∀ x, IsUnitary (p.eval x) ∧ ‖p.eval x ∘L inp - inp ∘L V x‖ ≤ ε

/-- `Simulates` is the case `V x = e^{-itH(x)}` of `Implements`. -/
theorem simulates_iff {O : L → X → W →L[ℂ] W} (H : X → P →L[ℂ] P) (t ε q : ℝ) :
    NativeSignedFactor.Simulates O H t ε q ↔
      Implements O (fun x => NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)) ε q :=
  Iff.rfl

/-- The spectator extension of `O` itself has the form. -/
theorem SpectatorForm.oracle (O : L → X → W →L[ℂ] W) (ι : Type) [Fintype ι] :
    SpectatorForm O (CoherentQuerySchedule.oracle (ι := ι) O) :=
  ⟨ι, inferInstance, LinearIsometryEquiv.refl ℂ _, fun _ _ => rfl⟩

/-- **Transport to the common form.** An implementation over a family `O'` of the form
`SpectatorForm O O'`, with a known isometric input, at most `q` calls, unitary for every
instance and with full-output error at most `ε`, gives `Implements O`. -/
theorem implements_of_spectatorForm {O : L → X → W →L[ℂ] W} {O' : L → X → K →L[ℂ] K}
    (hO : SpectatorForm O O') (V : X → P →L[ℂ] P) (ε q : ℝ) (inp : P →L[ℂ] K)
    (hinp : inp† ∘L inp = 1) (p : MultiOracleCircuit.Program O') (hcount : (p.count : ℝ) ≤ q)
    (hp : ∀ x, IsUnitary (p.eval x) ∧ ‖p.eval x ∘L inp - inp ∘L V x‖ ≤ ε) :
    Implements O V ε q := by
  obtain ⟨ι, hι, e, he⟩ := hO
  refine ⟨ι, hι, e.toLinearIsometry.toContinuousLinearMap ∘L inp,
    ofEq he (p.transport e), isometry_comp e inp hinp, ?_, fun x => ⟨?_, ?_⟩⟩
  · rw [count_ofEq, MultiOracleCircuit.Program.count_transport]
    exact hcount
  · rw [eval_ofEq, MultiOracleCircuit.Program.eval_transport]
    exact (hp x).1.transport e
  · rw [eval_ofEq, MultiOracleCircuit.Program.eval_transport, conj_error]
    exact (hp x).2

/-- **Transport of a simulation to the common form** `NativeSignedFactor.Simulates O`. -/
theorem simulates_of_spectatorForm {O : L → X → W →L[ℂ] W} {O' : L → X → K →L[ℂ] K}
    (hO : SpectatorForm O O') (H : X → P →L[ℂ] P) (t ε q : ℝ) (inp : P →L[ℂ] K)
    (hinp : inp† ∘L inp = 1) (p : MultiOracleCircuit.Program O') (hcount : (p.count : ℝ) ≤ q)
    (hp : ∀ x, IsUnitary (p.eval x) ∧
      ‖p.eval x ∘L inp - inp ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ ε) :
    NativeSignedFactor.Simulates O H t ε q :=
  implements_of_spectatorForm hO _ ε q inp hinp p hcount hp

end Generic

end

end OptimalSparseSimulation
