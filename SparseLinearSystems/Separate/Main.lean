import SparseLinearSystems.Separate.Decode
import SparseLinearSystems.Protocol.Leaf
import SparseLinearSystems.Endpoint.Main
import GeneralODE.Solver.Interface

/-!
# Corollary `qls:cor:separate`: separate matrix and preparation query bounds

Conditional on the external solver interface `SeparateSolver cM cb q₀` (Gao–Ji–Liu), one finite
protocol solves the native sparse linear system of Theorem `qls:thm:main` with success at least
`2/3`, conditional trace distance at most `ε`, and, on every history,

* matrix queries `Q_A ≤ C_A √s κ log(1/ε)`, for every input;
* preparation queries `Q_b ≤ C_b κ/ν`, `ν = ‖A⁻¹ b‖`, for every valid input with a public
  estimate `ν/2 ≤ ν̂ ≤ 2ν`.

The protocol (`protocol`) repeats `N = ⌈6/q₀⌉` times one public trial (`trial`): the external
solver for `B y = J (b, 0)` with `κ_B = 4√s κ`, `δ = ε/8` and `η = (9/8) √s max(ν̂, 1/2)`
(`= (9/8) √s ν̂` on every valid instance), compiled to the native oracles (`compiled`), the
herald routing (`flip`) and the decoder (`circLcu` with `G = 1`). It is chosen before the
instance `x`; `ν̂` is a classical input whose cost is not counted. The constants are
`C_A = 54 N (12 cM + 1)` and `C_b = (73/9) N cb` (`constA`, `constB`). The manuscript instead
runs the measured solver of Gao, Ji and Liu five times; both give the corollary's bounds.

The interface is a hypothesis of the theorem, not an axiom, and is not proved in this package.
-/

set_option autoImplicit false

namespace SparseLinearSystems.Separate

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit
open scoped InnerProduct Ring
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8192

universe uX uN uZ

variable {X : Type uX} {n : Type uN} {Z : Type uZ} [Fintype n] [DecidableEq n] [Fintype Z]
  [AddCommGroup Z] [DecidableEq Z] {s : ℕ}


/-! ### The compiled solver -/

section Compiled

variable (D : NativeSparseBlockEncoding.Data X n Z s)
  (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) {w : ℕ}

/-- The solver's branches `(false, i)` with `ctrl i`. -/
def solverMask (ctrl : Fin w → Bool) : Bool × Fin w → Bool := fun p => !p.1 && ctrl p.2

/-- The oracle input seen by the solver: the block encoding of `B` and the preparation. -/
def solverInput (x : X) : Input (Pair (Reg n Z)) := (UB D x, PB D Ub x)

/-- The physical letters of the two solver labels. -/
def letters (ctrl : Fin w → Bool) (b : Bool) : MultiOracleCircuit.Program (sepOracle D Ub w) :=
  if b then circP D Ub w (solverMask ctrl)
  else circLcu D Ub w (reflNat D) (reflNat_unitary D) (solverMask ctrl)

/-- The solver workspace, in the flag-false sector of the physical workspace. -/
def encS (w : ℕ) : Space (Pair (Reg n Z)) w →L[ℂ] Phys n Z w := enc D w ∘L sector false

theorem encS_isometry (w : ℕ) : (encS D w)† ∘L encS D w = 1 := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro v
  rw [encS, comp_apply, norm_enc, norm_sector]

omit [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem masked_sector {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ctrl : Fin w → Bool) (Q : K →L[ℂ] K) (v : PiLp 2 (fun _ : Fin w => K)) :
    MaskedProgram.masked (solverMask ctrl) Q (sector false v) =
      sector false (MaskedProgram.masked ctrl Q v) := by
  apply PiLp.ext
  intro p
  rcases p with ⟨f, i⟩
  cases f <;> simp [solverMask]

theorem letters_intertwine (ctrl : Fin w → Bool) (b : Bool) (x : X) :
    (letters D Ub ctrl b).eval x ∘L encS D w =
      encS D w ∘L solverOracle (Pair (Reg n Z)) w ctrl b (solverInput D Ub x) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [comp_apply, comp_apply, encS, comp_apply, comp_apply]
  cases b
  · simp only [letters, Bool.false_eq_true, if_false, circLcu_apply, solverOracle, solverInput]
    rw [masked_sector]
    rfl
  · simp only [letters, if_true, circP_apply, solverOracle, solverInput]
    rw [masked_sector]

/-- **The compiled solver**: every logical call replaced by its physical letter, public gates
lifted along the clean encoding. -/
def compiled (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle (Pair (Reg n Z)) w ctrl)) :
    MultiOracleCircuit.Program (sepOracle D Ub w) :=
  EncodedLabeledProgram.compile (encS D w) (encS_isometry D w) (letters D Ub ctrl)
    (S.reindex (solverInput D Ub))

theorem compiled_apply (hUb : ∀ x, IsUnitary (Ub x)) (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle (Pair (Reg n Z)) w ctrl)) (x : X)
    (ψ : Space (Pair (Reg n Z)) w) :
    (compiled D Ub ctrl S).eval x (encS D w ψ) = encS D w (S.eval (solverInput D Ub x) ψ) := by
  have h := EncodedLabeledProgram.compile_eval (encS D w) (encS_isometry D w) (letters D Ub ctrl)
    (sepOracle_unitary D Ub hUb w)
    (fun b y => solverOracle_unitary w ctrl (solverInput D Ub y) (UB_unitary D y)
      (PB_unitary D Ub y (hUb y)) b)
    (fun b y => letters_intertwine D Ub ctrl b y) (S.reindex (solverInput D Ub)) x
  rw [MultiOracleCircuit.Program.eval_reindex] at h
  rw [compiled, ← comp_apply, h, comp_apply]

theorem letters_cost_mat (ctrl : Fin w → Bool) (b : Bool) :
    (letters D Ub ctrl b).cost Step.wMat = if b then 0 else 54 := by
  cases b
  · simp only [letters, Bool.false_eq_true, if_false, circLcu_cost_mat]
  · simp only [letters, if_true, circP_cost_mat]

theorem letters_cost_src (ctrl : Fin w → Bool) (b : Bool) :
    (letters D Ub ctrl b).cost Step.wSrc = if b then 1 else 0 := by
  cases b
  · simp only [letters, Bool.false_eq_true, if_false, circLcu_cost_src]
  · simp only [letters, if_true, circP_cost_src]

omit [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem cost_bool {K Y : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {O : Bool → Y → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) (c₀ c₁ : ℕ) :
    p.cost (fun b => if b then c₁ else c₀) = c₀ * p.labelCount false + c₁ * p.labelCount true := by
  rw [MultiOracleCircuit.Program.cost_eq_sum_labelCount, Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

/-- **Matrix cost of the compiled solver**: 54 per block-encoding call, none per preparation. -/
theorem compiled_cost_mat (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle (Pair (Reg n Z)) w ctrl)) :
    (compiled D Ub ctrl S).cost Step.wMat = 54 * S.labelCount false := by
  rw [compiled, EncodedLabeledProgram.compile_cost, MultiOracleCircuit.Program.cost_reindex]
  simp only [letters_cost_mat]
  rw [cost_bool]
  ring

/-- **Preparation cost of the compiled solver**: one per preparation call, none per
block-encoding call. -/
theorem compiled_cost_src (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle (Pair (Reg n Z)) w ctrl)) :
    (compiled D Ub ctrl S).cost Step.wSrc = S.labelCount true := by
  rw [compiled, EncodedLabeledProgram.compile_cost, MultiOracleCircuit.Program.cost_reindex]
  simp only [letters_cost_src]
  rw [cost_bool]
  ring

end Compiled

/-! ### One trial -/

section Trial

variable (D : NativeSparseBlockEncoding.Data X n Z s)
  (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) {w : ℕ}
  (w₀ : Fin w) (ctrl : Fin w → Bool)
  (S : MultiOracleCircuit.Program (solverOracle (Pair (Reg n Z)) w ctrl))
  (out : SparseEdgeMoments.OrientedSpace n →L[ℂ] Space (Pair (Reg n Z)) w) (hout : out† ∘L out = 1)

/-- **One trial**: the compiled solver, the herald routing and the decoder. -/
def trial : MultiOracleCircuit.Program (sepOracle D Ub w) :=
  .seq (circLcu D Ub w 1 isUnitary_one (fun p => p.1))
    (.seq (fixL D Ub w (flip D w₀ out hout) (flip_unitary D w₀ out hout)) (compiled D Ub ctrl S))

/-- The trial's seed: the solver's initial state, in the clean encoding. -/
def trialSeed (sv : EuclideanSpace ℂ n) : Phys n Z w := encS D w (initial w₀ (seedVec D sv))

/-- The trial's output selector. -/
def trialOut : EuclideanSpace ℂ n →L[ℂ] Phys n Z w := enc D w ∘L selector D w₀

theorem trialSeed_norm (sv : EuclideanSpace ℂ n) (hsv : ‖sv‖ = 1) : ‖trialSeed D w₀ sv‖ = 1 := by
  rw [trialSeed, encS, comp_apply, norm_enc, norm_sector, norm_initial, norm_seedVec, hsv]

theorem trialOut_isometry : (trialOut D w₀)† ∘L trialOut D w₀ = 1 := by
  apply (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp
  intro u
  rw [trialOut, comp_apply, norm_enc, norm_selector]

theorem trial_unitary (hUb : ∀ x, IsUnitary (Ub x)) (x : X) :
    IsUnitary ((trial D Ub w₀ ctrl S out hout).eval x) :=
  (trial D Ub w₀ ctrl S out hout).eval_unitary (sepOracle_unitary D Ub hUb w) x

/-- **The selected vector of a trial** is `T (out† S ψ₀)`. -/
theorem trial_amplitude (hUb : ∀ x, IsUnitary (Ub x)) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (sv : EuclideanSpace ℂ n) :
    ((trialOut D w₀)†) ((trial D Ub w₀ ctrl S out hout).eval x (trialSeed D w₀ sv)) =
      decodeMap D x hA1 ((out†) (S.eval (solverInput D Ub x) (initial w₀ (seedVec D sv)))) := by
  have hE : ∀ y : Paired n Z w, ((enc D w)†) (enc D w y) = y := fun y =>
    congrArg (fun A : Paired n Z w →L[ℂ] Paired n Z w => A y) (enc_isometry D w)
  rw [trial, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_seq,
    mul_apply_eq_comp, mul_apply_eq_comp, trialSeed, compiled_apply D Ub hUb, encS, comp_apply,
    fixL_apply, flip_sector, circLcu_apply, one_mul, trialOut, adjoint_comp, comp_apply, hE]
  exact selected D w₀ x hA1 out _

theorem trial_cost_mat :
    (trial D Ub w₀ ctrl S out hout).cost Step.wMat = 54 + 54 * S.labelCount false := by
  simp only [trial, fixL, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, circLcu_cost_mat, compiled_cost_mat, zero_add]

theorem trial_cost_src :
    (trial D Ub w₀ ctrl S out hout).cost Step.wSrc = S.labelCount true := by
  simp only [trial, fixL, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, circLcu_cost_src, compiled_cost_src, zero_add]

end Trial

/-! ### Repetition -/

/-- The number of attempts, `N = ⌈6/q₀⌉`. -/
def reps (q₀ : ℝ) : ℕ := ⌈6 / q₀⌉₊

/-- **The protocol**: at most `N` fresh attempts of the trial; the first heralded success is
returned. -/
def protocol (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (N : ℕ) {w : ℕ}
    (w₀ : Fin w) (ctrl : Fin w → Bool)
    (S : MultiOracleCircuit.Program (solverOracle (Pair (Reg n Z)) w ctrl))
    (out : SparseEdgeMoments.OrientedSpace n →L[ℂ] Space (Pair (Reg n Z)) w)
    (hout : out† ∘L out = 1) (sv : EuclideanSpace ℂ n)
    (hsv : ‖sv‖ = 1) : ODERepeatProtocol.Protocol (sepOracle D Ub w) (EuclideanSpace ℂ n) :=
  ODERepeatProtocol.Protocol.repeatTrials
    (Protocol.single (trial D Ub w₀ ctrl S out hout) (trialSeed D w₀ sv)
      (trialSeed_norm D w₀ sv hsv) (trialOut D w₀) (trialOut_isometry D w₀)) N

section Repeat

variable {K E Y L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {O : L → Y → K →L[ℂ] K}

theorem single_worstCost (c : MultiOracleCircuit.Program O) (ψ : K) (hψ : ‖ψ‖ = 1)
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (r : ℕ) (wt : L → ℕ) :
    (ODERepeatProtocol.Protocol.repeatTrials (Protocol.single c ψ hψ F hF) r).worstCost wt =
      r * c.cost wt := by
  rw [ODERepeatProtocol.Protocol.repeat_worstCost]
  congr 1
  exact Finset.sup_const (Finset.univ_nonempty (α := Fin 1)) _

/-- **Finite repetition of one heralded trial.** If one attempt succeeds with probability at least
`q₀/3`, then `⌈6/q₀⌉` attempts succeed with probability at least `2/3`, and the conditional output
is the pure state of the normalised selected vector. -/
theorem repeat_guarantee (c : MultiOracleCircuit.Program O) (ψ : K) (hψ : ‖ψ‖ = 1)
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (y : Y) (hU : IsUnitary (c.eval y)) (q₀ : ℝ)
    (hq₀ : 0 < q₀) (hp : q₀ / 3 ≤ ‖(F†) (c.eval y ψ)‖ ^ 2) :
    2 / 3 ≤ (ODERepeatProtocol.Protocol.repeatTrials (Protocol.single c ψ hψ F hF)
        (reps q₀)).successMass y ∧
      (ODERepeatProtocol.Protocol.repeatTrials (Protocol.single c ψ hψ F hF)
        (reps q₀)).conditionalDensity y =
        ODEMixedOutput.pureOperator
          (ODEStateNormalization.unitDirection ((F†) (c.eval y ψ))) := by
  set p := ‖(F†) (c.eval y ψ)‖ ^ 2 with hpdef
  have hprob := (Protocol.single c ψ hψ F hF).probability_bounds y (fun _ => hU) ⟨0, Nat.one_pos⟩
  have hp' : (Protocol.single c ψ hψ F hF).probability y ⟨0, Nat.one_pos⟩ = p := rfl
  rw [hp'] at hprob
  obtain ⟨hp0, hp1⟩ := hprob
  have hN : 6 / q₀ ≤ (reps q₀ : ℝ) := Nat.le_ceil _
  have hNp : 2 ≤ (reps q₀ : ℝ) * p := by
    have h1 : 6 / q₀ * (q₀ / 3) = 2 := by field_simp; norm_num
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 6) hq₀]
  have hpow := Endpoint.one_sub_pow_le p hp0 hp1 (reps q₀)
  have hfrac : 1 / (1 + (reps q₀ : ℝ) * p) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hmass := Protocol.single_successMass c ψ hψ F hF y (reps q₀)
  have hsucc : 2 / 3 ≤ (ODERepeatProtocol.Protocol.repeatTrials (Protocol.single c ψ hψ F hF)
      (reps q₀)).successMass y := by
    rw [hmass, ← hpdef]
    linarith
  refine ⟨hsucc, ?_⟩
  obtain ⟨-, -, -, hdens⟩ := Protocol.single_leaf_spec c ψ hψ F hF y hU (reps q₀)
  rw [ODERepeatProtocol.Protocol.conditionalDensity, hdens, smul_smul]
  have hm : ((ODERepeatProtocol.Protocol.repeatTrials (Protocol.single c ψ hψ F hF)
      (reps q₀)).successMass y : ℂ) ≠ 0 := by
    exact_mod_cast (show (0 : ℝ) < _ by linarith).ne'
  rw [inv_mul_cancel₀ hm, one_smul]

end Repeat

/-- A pure state within `ε` of a unit target up to a phase is a density operator within trace
distance `ε`. -/
theorem pure_traceDistance {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ε : ℝ) (ω : ℂ)
    (hω : ‖ω‖ = 1) (hclose : ‖ω • u - v‖ ≤ ε) :
    ODEMixedOutput.IsDensity (ODEMixedOutput.pureOperator u) ∧
      ∃ h : (ODEMixedOutput.pureOperator u - ODEMixedOutput.pureOperator v).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (ODEMixedOutput.pureOperator u)
          (ODEMixedOutput.pureOperator v) h ≤ ε := by
  have hens : ODEMixedOutput.ensemble (fun _ : Unit => (1 : ℝ)) (fun _ => u) =
      ODEMixedOutput.pureOperator u := by
    simp [ODEMixedOutput.ensemble]
  have h := ODEMixedOutput.ensemble_trace_distance_le (fun _ : Unit => (1 : ℝ)) (fun _ => u) v ε
    (fun _ => zero_le_one) (by simp) (fun _ _ => hu) hv (fun _ _ => ⟨ω, hω, hclose⟩)
  rwa [hens] at h

/-! ### Scalar inequalities -/

/-- `log(2/δ) ≤ 3 log(1/ε)` for `δ = ε/8`, `0 < ε ≤ 1/10`. -/
theorem log_budget (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    Real.log (2 / (ε / 8)) ≤ 3 * Real.log (1 / ε) := by
  have h3 : 3 * Real.log (1 / ε) = Real.log ((1 / ε) ^ 3) := by
    rw [Real.log_pow]
    norm_num
  rw [h3]
  apply Real.log_le_log (by positivity)
  rw [div_pow, one_pow, show 2 / (ε / 8) = 16 / ε by field_simp; norm_num,
    div_le_div_iff₀ hε (by positivity)]
  nlinarith [pow_pos hε 2, pow_pos hε 3]

/-- The matrix constant `C_A = 54 N (12 cM + 1)`. -/
def constA (cM q₀ : ℝ) : ℝ := 54 * (reps q₀ : ℝ) * (12 * cM + 1)

/-- The preparation constant `C_b = (73/9) N cb`. -/
def constB (cb q₀ : ℝ) : ℝ := 73 / 9 * (reps q₀ : ℝ) * cb

theorem constA_pos (cM q₀ : ℝ) (hcM : 0 ≤ cM) (hq₀ : 0 < q₀) : 0 < constA cM q₀ := by
  have hN : 0 < (reps q₀ : ℝ) := by
    have : 6 / q₀ ≤ (reps q₀ : ℝ) := Nat.le_ceil _
    linarith [div_pos (by norm_num : (0 : ℝ) < 6) hq₀]
  unfold constA
  positivity

theorem constB_pos (cb q₀ : ℝ) (hcb : 0 < cb) (hq₀ : 0 < q₀) : 0 < constB cb q₀ := by
  have hN : 0 < (reps q₀ : ℝ) := by
    have : 6 / q₀ ≤ (reps q₀ : ℝ) := Nat.le_ceil _
    linarith [div_pos (by norm_num : (0 : ℝ) < 6) hq₀]
  unfold constB
  positivity

/-! ### The corollary -/

/-- **Corollary `qls:cor:separate`, conditional on the external solver interface.** For the
native input conventions of Theorem `qls:thm:main`, a public `κ ≥ 1`, `0 < ε ≤ 1/10` and a public
scalar `ν̂`, there is one protocol, chosen before the instance, whose worst-case matrix cost is at
most `C_A √s κ log(1/ε)`, and which, on every valid instance with `ν/2 ≤ ν̂ ≤ 2ν`
(`ν = ‖A⁻¹ b‖`), has worst-case preparation cost at most `C_b κ/ν`, success probability at least
`2/3`, and conditional output a density operator within trace distance `ε` of `A⁻¹b/‖A⁻¹b‖`. -/
theorem main (cM cb q₀ : ℝ) (hcM : 0 ≤ cM) (hcb : 0 ≤ cb) (hq₀ : 0 < q₀)
    (hS : SeparateSolver.{uN, max uN uZ} cM cb q₀)
    (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hUb : ∀ x, IsUnitary (Ub x))
    (sv : EuclideanSpace ℂ n) (hsv : ‖sv‖ = 1) (κ ε νh : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∃ (w : ℕ) (A : ODERepeatProtocol.Protocol (sepOracle D Ub w) (EuclideanSpace ℂ n)),
      (A.worstCost Step.wMat : ℝ) ≤ constA cM q₀ * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Endpoint.Promise D κ x →
        ‖(Facts.Aop D x)⁻¹ʳ (Ub x sv)‖ / 2 ≤ νh → νh ≤ 2 * ‖(Facts.Aop D x)⁻¹ʳ (Ub x sv)‖ →
        (A.worstCost Step.wSrc : ℝ) ≤ constB cb q₀ * κ / ‖(Facts.Aop D x)⁻¹ʳ (Ub x sv)‖ ∧
        2 / 3 ≤ A.successMass x ∧ ODEMixedOutput.IsDensity (A.conditionalDensity x) ∧
        ∃ h : (A.conditionalDensity x -
            ODEMixedOutput.pureOperator (Endpoint.solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance (A.conditionalDensity x)
            (ODEMixedOutput.pureOperator (Endpoint.solutionState D Ub sv x)) h ≤ ε := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hsq1 : 1 ≤ Real.sqrt (s : ℝ) := Real.one_le_sqrt.mpr hs1
  have hL := Endpoint.two_le_logInv ε hε hε1
  set κB := 4 * Real.sqrt (s : ℝ) * κ with hκB
  set δ := ε / 8 with hδ
  set νh' := max νh (1 / 2) with hνh'
  set η := 9 / 8 * Real.sqrt (s : ℝ) * νh' with hη
  have h2 : 2 ≤ κB := by nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 / 2 := by linarith
  have hδ80 : δ ≤ 1 / 80 := by linarith
  have hνh'pos : 0 < νh' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hηpos : 0 < η := by positivity
  have hseed : ‖seedVec D sv‖ = 1 := by rw [norm_seedVec, hsv]
  obtain ⟨w, w₀, ctrl, S, out, hout, hcM', hcb', hcorr⟩ :=
    hS (SparseEdgeMoments.OrientedSpace n) (Pair (Reg n Z)) (sysEnc D) (sysEnc_isometry D)
      (seedVec D sv) hseed κB δ η h2 hδ0
      hδ1 hηpos
  have hN0 : (0 : ℝ) ≤ reps q₀ := Nat.cast_nonneg _
  refine ⟨w, protocol D Ub (reps q₀) w₀ ctrl S out hout sv hsv, ?_, ?_⟩
  · -- the matrix budget, for every input
    rw [protocol, single_worstCost, trial_cost_mat]
    push_cast
    have hlog := log_budget ε hε hε1
    have hc : (S.labelCount false : ℝ) ≤ cM * (4 * Real.sqrt (s : ℝ) * κ) *
        (3 * Real.log (1 / ε)) := by
      refine hcM'.trans ?_
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    have h1 : 1 ≤ Real.sqrt (s : ℝ) * κ * Real.log (1 / ε) := by
      have : 1 ≤ Real.sqrt (s : ℝ) * κ := by nlinarith
      nlinarith
    unfold constA
    have hlc0 : (0 : ℝ) ≤ S.labelCount false := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hc hN0, mul_le_mul_of_nonneg_left h1 hN0]
  · intro x hP hlo hhi
    have hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1 := hP.norm_le
    set b := Ub x sv with hbdef
    have hb : ‖b‖ = 1 := by rw [hbdef, IsUnitary.norm_apply (hUb x), hsv]
    set z := (Facts.Aop D x)⁻¹ʳ b with hzdef
    have hAz : Facts.Aop D x z = b := hP.apply_inverse b
    have hz1 : 1 ≤ ‖z‖ := by
      have h := (Facts.Aop D x).le_opNorm z
      rw [hAz, hb] at h
      nlinarith [norm_nonneg z]
    have hzκ : ‖z‖ ≤ κ := by
      have h := ((Facts.Aop D x)⁻¹ʳ).le_opNorm b
      rw [hb, mul_one] at h
      exact h.trans hP.inverse_norm_le
    have hz0 : z ≠ 0 := by
      intro h
      rw [h, norm_zero] at hz1
      linarith
    have hνh : νh' = νh := max_eq_left (by linarith)
    -- the interface inputs
    set β := bdry D (rhs b) with hβdef
    have hβ : ‖β‖ = 1 := by rw [hβdef, norm_bdry, norm_rhs, hb]
    have hblock := UB_block D x hA1
    have hinv : ∀ v, ‖v‖ ≤ κB * ‖((sysEnc D)† ∘L UB D x ∘L sysEnc D) v‖ := by
      intro v
      rw [hblock]
      exact enlarged_inverse D x hA1 κ hκ hP.lower v
    have hy : ((sysEnc D)† ∘L UB D x ∘L sysEnc D) (solution D x z) = β := by
      rw [hblock, enlarged_solution_eq D x hA1 z]
      exact congrArg (fun u => bdry D (rhs u)) hAz
    obtain ⟨hη1, hη2⟩ := estimate_transfer D x hA1 z νh hlo hhi
    rw [← hνh] at hη1 hη2
    have hprep := PB_seed D Ub x sv
    have hUu := UB_unitary D x
    have hPu := PB_unitary D Ub x (hUb x)
    have hamp := trial_amplitude D Ub w₀ ctrl S out hout hUb x hA1 sv
    have hsolIn : solverInput D Ub x = (UB D x, PB D Ub x) := rfl
    rw [hsolIn] at hamp
    -- the external interface sees the concrete operators only through their values
    generalize hUd : UB D x = U at hinv hy hamp hUu
    generalize hPd : PB D Ub x = P at hprep hamp hPu
    generalize hιd : sysEnc D = ι at hcorr hinv hy hprep
    generalize hrd : seedVec D sv = r₀ at hcorr hprep hamp
    generalize hyd : solution D x z = y at hy hη1 hη2
    obtain ⟨hq, ω, hω, hclose⟩ := hcorr U P hUu hPu β y hβ hprep hinv hy hη1 hη2
    subst hyd
    obtain ⟨hp, ω', hω', hdir⟩ := decode_success D x hA1 z hz0
      ((out†) (S.eval (U, P) (initial w₀ r₀))) q₀ δ hq₀ hq hδ80 ω hω hclose
    rw [← hamp] at hp hdir
    obtain ⟨hsucc, hcond⟩ := repeat_guarantee (trial D Ub w₀ ctrl S out hout) (trialSeed D w₀ sv)
      (trialSeed_norm D w₀ sv hsv) (trialOut D w₀) (trialOut_isometry D w₀) x
      (trial_unitary D Ub w₀ ctrl S out hout hUb x) q₀ hq₀ hp
    refine ⟨?_, hsucc, ?_⟩
    · -- the preparation budget, for every valid input
      rw [protocol, single_worstCost, trial_cost_src]
      push_cast
      have hr := ratio_bound κ νh ‖z‖ hs1 (by linarith) hzκ hlo
      rw [← hνh] at hr
      unfold constB
      have hc : (S.labelCount true : ℝ) ≤ cb * (73 / 9 * (κ / ‖z‖)) :=
        hcb'.trans (mul_le_mul_of_nonneg_left hr hcb)
      calc (reps q₀ : ℝ) * (S.labelCount true : ℝ)
          ≤ (reps q₀ : ℝ) * (cb * (73 / 9 * (κ / ‖z‖))) := mul_le_mul_of_nonneg_left hc hN0
        _ = 73 / 9 * (reps q₀ : ℝ) * cb * κ / ‖z‖ := by ring
    · -- the output
      have hTa0 : ((trialOut D w₀)†) ((trial D Ub w₀ ctrl S out hout).eval x
          (trialSeed D w₀ sv)) ≠ 0 := by
        intro h
        rw [h, norm_zero] at hp
        nlinarith
      have hu := ODEStateNormalization.unitDirection_norm _ hTa0
      have hv : ‖Endpoint.solutionState D Ub sv x‖ = 1 :=
        ODEStateNormalization.unitDirection_norm _ hz0
      rw [protocol, hcond]
      exact pure_traceDistance _ _ hu hv ε ω' hω' (hdir.trans (by linarith))

end

end SparseLinearSystems.Separate
