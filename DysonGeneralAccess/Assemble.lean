import DysonGeneralAccess.Model
import DysonGeneralAccess.Cost

set_option autoImplicit false

/-!
# A parallel stage over a general access is a heralded single program

Manuscript, proof of Lemma `odel:lem:dyson` ("Mixing the two trials and repeating a constant number
of times gives heralded success probability at least `2/3`") and the output model of Section
`odel:sec:main`. The parallel
stages of `DysonSingleProgram.Parallel` (attempts on separate registers, first-success herald and
readout) run over any unitary access `O`; their program lives over two nested spectator registers.
This module reads a stage as a `Model.HeraldedSolver` over `fiberOracle (S.I × Fin M) O` for an
arbitrary relation of valid instances, in the fixed layout `Release.jointFlatten`; it is the
general-access form of `DysonSingleProgram.exists_solver_of_stage` and
`DysonSingleProgram.exists_solver_of_good`.

* `flatProg`, `eval_flatProg`, `cost_flatProg`: the stage's program over one spectator register
  (`Register.reflatten`; `eval_flatProg` is `Register.eval_reflatten` and `cost_flatProg` is
  `Cost.cost_reflatten` at this program);
* `ofStage`: a stage with a seed of norm at most one, a herald projection, an isometric readout,
  success at least `2/3` and heralded accuracy on every valid instance;
* `ofGood`: a stage reproducing a released retry protocol (`Parallel.Stage.Good`) with success
  mass at least `2/3` and `2ε`-accurate conditional expectations on every valid instance.
-/

namespace DysonGeneralAccess.Assemble

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit Model
open DysonSingleProgram DysonSingleProgram.Register DysonSingleProgram.Parallel
open ODELowerBoundExtensions.Release (jointFlatten)
open scoped InnerProduct InnerProductSpace

variable {X L : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [FiniteDimensional ℂ W] {M : ℕ} {N : Type} [Fintype N] [DecidableEq N]
  {O : L → X → W →L[ℂ] W}

/-- **The stage's program over one spectator register** `S.I × Fin M`. -/
def flatProg (S : Stage O M N) : MultiOracleCircuit.Program (fiberOracle (S.I × Fin M) O) :=
  reflatten S.I (Fin M) S.prog

omit [FiniteDimensional ℂ W] [DecidableEq N] in
/-- The flattened program is the stage's program in the fixed layout `jointFlatten`. -/
theorem eval_flatProg (S : Stage O M N) (x : X) :
    (flatProg S).eval x = (jointFlatten S.I (Fin M) W).symm.conjStarAlgEquiv (S.prog.eval x) :=
  DysonSingleProgram.Register.eval_reflatten S.I (Fin M) S.prog x

omit [FiniteDimensional ℂ W] [DecidableEq N] in
/-- The flattened program keeps every weighted count. -/
@[simp] theorem cost_flatProg (S : Stage O M N) (w : L → ℕ) :
    (flatProg S).cost w = S.prog.cost w :=
  Cost.cost_reflatten _ _ _ w

omit [FiniteDimensional ℂ W] [DecidableEq N] in
/-- The flattened program on a flattened vector is the flattened stage output. -/
theorem flatProg_eval_symm (S : Stage O M N) (x : X) (v : Joint S.I (Joint (Fin M) W)) :
    (flatProg S).eval x ((jointFlatten S.I (Fin M) W).symm v) =
      (jointFlatten S.I (Fin M) W).symm (S.prog.eval x v) := by
  rw [flatProg, DysonSingleProgram.Register.eval_reflatten,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply]

omit [FiniteDimensional ℂ W] [DecidableEq N] in
/-- The conjugated herald acts on flattened vectors as the herald. -/
theorem herald_conj_symm (S : Stage O M N) (v : Joint S.I (Joint (Fin M) W)) :
    (jointFlatten S.I (Fin M) W).symm.conjStarAlgEquiv S.herald
        ((jointFlatten S.I (Fin M) W).symm v) =
      (jointFlatten S.I (Fin M) W).symm (S.herald v) := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply]

/-- **A stage with the solver properties is a heralded single program** with program
`flatProg S`, seed `layout⁻¹ (S.seed μ)`, herald `layout⁻¹ P layout` and readout
`e ∘ layout`, `layout = jointFlatten S.I (Fin M) W`. -/
def ofStage (S : Stage O M N) (μ : Joint (Fin M) W) (Valid : X → EuclideanSpace ℂ N → Prop)
    (ε : ℝ) (hseed : ‖S.seed μ‖ ≤ 1) (hP : IsStarProjection S.herald)
    (he : S.out.adjoint ∘L S.out = 1)
    (hsucc : ∀ x y, Valid x y → 2 / 3 ≤ ‖S.herald (S.prog.eval x (S.seed μ))‖ ^ 2)
    (hacc : ∀ x y, Valid x y →
      Readout.HeraldedAccurate S.out S.herald (S.prog.eval x (S.seed μ))
        (ODEStateNormalization.unitDirection y) ε) :
    HeraldedSolver (fiberOracle (S.I × Fin M) O) Valid (Joint S.Γ (Joint (Fin M) W)) ε where
  prog := flatProg S
  seed := (jointFlatten S.I (Fin M) W).symm (S.seed μ)
  seed_norm_le := by rw [LinearIsometryEquiv.norm_map]; exact hseed
  out := S.out ∘L (jointFlatten S.I (Fin M) W).toLinearIsometry.toContinuousLinearMap
  out_isometry := comp_isometryEquiv_isometry S.out he _
  herald := (jointFlatten S.I (Fin M) W).symm.conjStarAlgEquiv S.herald
  herald_proj := isStarProjection_conj_isometryEquiv _ hP
  success := fun x y hv => by
    rw [flatProg_eval_symm, herald_conj_symm, LinearIsometryEquiv.norm_map]; exact hsucc x y hv
  accurate := fun x y hv => by
    rw [flatProg_eval_symm]
    exact heraldedAccurate_isometryEquiv _ _ _ _ _ _ (hacc x y hv)

omit [FiniteDimensional ℂ W] in
/-- The heralded success of `ofStage` is the stage's heralded success. -/
theorem ofStage_success (S : Stage O M N) (μ : Joint (Fin M) W)
    (Valid : X → EuclideanSpace ℂ N → Prop) (ε : ℝ) (hseed : ‖S.seed μ‖ ≤ 1)
    (hP : IsStarProjection S.herald) (he : S.out.adjoint ∘L S.out = 1)
    (hsucc : ∀ x y, Valid x y → 2 / 3 ≤ ‖S.herald (S.prog.eval x (S.seed μ))‖ ^ 2)
    (hacc : ∀ x y, Valid x y →
      Readout.HeraldedAccurate S.out S.herald (S.prog.eval x (S.seed μ))
        (ODEStateNormalization.unitDirection y) ε) (x : X) :
    ‖(ofStage S μ Valid ε hseed hP he hsucc hacc).herald
        ((ofStage S μ Valid ε hseed hP he hsucc hacc).prog.eval x
          (ofStage S μ Valid ε hseed hP he hsucc hacc).seed)‖ =
      ‖S.herald (S.prog.eval x (S.seed μ))‖ := by
  show ‖(jointFlatten S.I (Fin M) W).symm.conjStarAlgEquiv S.herald
      ((flatProg S).eval x ((jointFlatten S.I (Fin M) W).symm (S.seed μ)))‖ = _
  rw [flatProg_eval_symm, herald_conj_symm, LinearIsometryEquiv.norm_map]

/-- **A stage reproducing a released protocol is a heralded single program**: if the stage `S`
with unit main seed `μ` reproduces a protocol `p` (`Stage.Good`) whose success mass is at least
`2/3` and whose conditional expectations are `2ε`-accurate on every valid instance. -/
def ofGood (S : Stage O M N) (μ : Joint (Fin M) W) (hμ : ‖μ‖ = 1) {Lt : Type*}
    {Ot : Lt → X → W →L[ℂ] W} (p : ODERepeatProtocol.Protocol Ot (EuclideanSpace ℂ N))
    (Valid : X → EuclideanSpace ℂ N → Prop) (ε : ℝ) (hS : S.Good μ p)
    (hsucc : ∀ x y, Valid x y → (2 : ℝ) / 3 ≤ p.successMass x)
    (hacc : ∀ x y, Valid x y → ∀ A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N,
      IsSelfAdjoint A → ‖A‖ ≤ 1 →
      |LinearSystemLowerBound.corr A (p.conditionalDensity x) -
        (⟪ODEStateNormalization.unitDirection y,
          A (ODEStateNormalization.unitDirection y)⟫_ℂ).re| ≤ 2 * ε) :
    HeraldedSolver (fiberOracle (S.I × Fin M) O) Valid (Joint S.Γ (Joint (Fin M) W)) ε :=
  ofStage S μ Valid ε (Stage.norm_seed S μ hμ hS.weight_norm).le hS.herald_proj hS.out_isometry
    (fun x y hv => by rw [hS.success x]; exact hsucc x y hv)
    (fun x y hv => DysonSingleProgram.heraldedAccurate_of_corr p x S.out S.herald _ _ ε
      (lt_of_lt_of_le (by norm_num) (hsucc x y hv)) (hS.success x) (hS.corr x) (hacc x y hv))

omit [FiniteDimensional ℂ W] in
/-- `ofGood` runs the flattened stage program. -/
@[simp] theorem ofGood_prog (S : Stage O M N) (μ : Joint (Fin M) W) (hμ : ‖μ‖ = 1) {Lt : Type*}
    {Ot : Lt → X → W →L[ℂ] W} (p : ODERepeatProtocol.Protocol Ot (EuclideanSpace ℂ N))
    (Valid : X → EuclideanSpace ℂ N → Prop) (ε : ℝ) (hS : S.Good μ p)
    (hsucc : ∀ x y, Valid x y → (2 : ℝ) / 3 ≤ p.successMass x)
    (hacc : ∀ x y, Valid x y → ∀ A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N,
      IsSelfAdjoint A → ‖A‖ ≤ 1 →
      |LinearSystemLowerBound.corr A (p.conditionalDensity x) -
        (⟪ODEStateNormalization.unitDirection y,
          A (ODEStateNormalization.unitDirection y)⟫_ℂ).re| ≤ 2 * ε) :
    (ofGood S μ hμ p Valid ε hS hsucc hacc).prog = flatProg S := rfl

omit [FiniteDimensional ℂ W] in
/-- **The heralded success of `ofGood` is the protocol's success mass**, on every input. -/
theorem ofGood_success (S : Stage O M N) (μ : Joint (Fin M) W) (hμ : ‖μ‖ = 1) {Lt : Type*}
    {Ot : Lt → X → W →L[ℂ] W} (p : ODERepeatProtocol.Protocol Ot (EuclideanSpace ℂ N))
    (Valid : X → EuclideanSpace ℂ N → Prop) (ε : ℝ) (hS : S.Good μ p)
    (hsucc : ∀ x y, Valid x y → (2 : ℝ) / 3 ≤ p.successMass x)
    (hacc : ∀ x y, Valid x y → ∀ A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N,
      IsSelfAdjoint A → ‖A‖ ≤ 1 →
      |LinearSystemLowerBound.corr A (p.conditionalDensity x) -
        (⟪ODEStateNormalization.unitDirection y,
          A (ODEStateNormalization.unitDirection y)⟫_ℂ).re| ≤ 2 * ε) (x : X) :
    ‖(ofGood S μ hμ p Valid ε hS hsucc hacc).herald
        ((ofGood S μ hμ p Valid ε hS hsucc hacc).prog.eval x
          (ofGood S μ hμ p Valid ε hS hsucc hacc).seed)‖ ^ 2 = p.successMass x := by
  rw [ofGood, ofStage_success, hS.success x]

end

end DysonGeneralAccess.Assemble
