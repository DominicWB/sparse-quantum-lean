import DysonSingleProgram.Shape
import DysonSingleProgram.Register.Fiber
import ODELowerBoundExtensions.Release.Purify

set_option autoImplicit false

/-!
# One attempt with a coherent cutoff register

Manuscript lines 4687-4689 (proof of Lemma `odel:lem:dyson`): "Amplitude amplification with a
known lower bound on success probability costs `O(ḡ e^z)` and gives constant heralded success."
The released attempt draws its cutoff `j < M` uniformly at random and runs `j` amplification steps
(`ODERepeatProtocol.TrialFamily`). A single program holds the cutoff in a register instead:
the label register `Fin M` starts in the uniform superposition, and step `i` (`i < M - 1`) of the
amplification is applied with its three fixed reflections controlled on `i < j`; the preparation
`A` and its inverse are applied uncontrolled. On label `j` the steps `i ≥ j` evaluate to
`A A† = 1`. No oracle call is controlled; all controls are on fixed unitaries.

* `ctrl M i U`: the fixed unitary `Σ_j |j⟩⟨j| ⊗ (U if i < j, else 1)` (`ctrl_unitary`,
  `ctrl_apply`);
* `step`, `steps`, `trial`: the attempt program over `Register.fiberOracle (Fin M) O`;
* `steps_eval_apply`, `trial_eval_apply`: on label `j` the steps `0, …, n - 1` act as
  `(U₁ A U₂ A† U₃)^{min n j}`, and the attempt is `(U₁ A U₂ A† U₃)^j A`;
* `count_steps`, `labelCount_steps`: the steps `0, …, n - 1` make `2n` times the calls of the
  preparation, in total and label by label;
* `count_trial`, `labelCount_trial`: `(2(M - 1) + 1)` times the calls of the preparation, the
  calls of the released trial with the largest cutoff;
* `labelSeed M ψ = M^{-1/2} Σ_j |j⟩ ⊗ ψ` (the constant joint vector `SparseLowerBounds.Joint.const`,
  `norm_labelSeed`) and `trial_eval_labelSeed`: the attempt prepares the
  purified attempt state `Release.trialVec` of the released trial family
  (`ODERepeatProtocol.ofCircuits`), for any trial family with the amplification shape.
-/

namespace DysonSingleProgram.Coherent

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit Register
open scoped InnerProduct

variable {X L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {O : L → X → W →L[ℂ] W}

/-- **The cutoff-controlled fixed unitary**: `U` on the labels `j > i`, the identity otherwise. -/
def ctrl (M i : ℕ) (U : W →L[ℂ] W) : Joint (Fin M) W →L[ℂ] Joint (Fin M) W :=
  Joint.fiber (fun j => if i < (j : ℕ) then U else 1)

/-- The cutoff-controlled unitary of a unitary is unitary (an instance of
`SparseLowerBounds.PhaseCircuit.isUnitary_fiber`). -/
theorem ctrl_unitary (M i : ℕ) {U : W →L[ℂ] W} (hU : IsUnitary U) : IsUnitary (ctrl M i U) :=
  SparseLowerBounds.PhaseCircuit.isUnitary_fiber _ (fun j => by
    split_ifs
    exacts [hU, isUnitary_one])

omit [CompleteSpace W] in
/-- Components of the cutoff-controlled unitary: label `j` gets `U` if `i < j`, else the
identity. -/
@[simp] theorem ctrl_apply (M i : ℕ) (U : W →L[ℂ] W) (v : Joint (Fin M) W) (j : Fin M) :
    ctrl M i U v j = (if i < (j : ℕ) then U else 1) (v j) := rfl

variable (M : ℕ) (a : MultiOracleCircuit.Program O) {U₁ U₂ U₃ : W →L[ℂ] W}
  (h₁ : IsUnitary U₁) (h₂ : IsUnitary U₂) (h₃ : IsUnitary U₃)

/-- **Amplification step `i`** with cutoff-controlled reflections: `ctrl U₁ · A · ctrl U₂ · A† ·
ctrl U₃` (`A`, `A†` uncontrolled). -/
def step (i : ℕ) : MultiOracleCircuit.Program (fiberOracle (Fin M) O) :=
  .seq (.fixed (ctrl M i U₁) (ctrl_unitary M i h₁))
    (.seq (.seq (.seq (spectate (Fin M) a) (.fixed (ctrl M i U₂) (ctrl_unitary M i h₂)))
      (spectate (Fin M) a.adjoint)) (.fixed (ctrl M i U₃) (ctrl_unitary M i h₃)))

/-- Steps `0, …, n - 1`, step `0` first. -/
def steps : ℕ → MultiOracleCircuit.Program (fiberOracle (Fin M) O)
  | 0 => MultiOracleCircuit.Program.identity
  | n + 1 => .seq (step M a h₁ h₂ h₃ n) (steps n)

/-- **The attempt with a coherent cutoff**: the preparation, then steps `0, …, M - 2`. -/
def trial : MultiOracleCircuit.Program (fiberOracle (Fin M) O) :=
  .seq (steps M a h₁ h₂ h₃ (M - 1)) (spectate (Fin M) a)

/-- On label `j`, steps `0, …, n - 1` act as `(U₁ A U₂ A† U₃)^{min n j}`, for unitary
oracles. -/
theorem steps_eval_apply (hO : ∀ l x, IsUnitary (O l x)) (x : X) (n : ℕ)
    (v : Joint (Fin M) W) (j : Fin M) :
    (steps M a h₁ h₂ h₃ n).eval x v j =
      ((U₁ * a.eval x * U₂ * star (a.eval x) * U₃) ^ min n (j : ℕ)) (v j) := by
  have hA : ∀ y, a.eval x (star (a.eval x) y) = y := fun y => by
    rw [← mul_apply_eq_comp, (MultiOracleCircuit.Program.eval_unitary a hO x).2,
      one_apply_eq_self]
  induction n with
  | zero => simp [steps]
  | succ n ih =>
    simp only [steps, step, MultiOracleCircuit.Program.eval_seq,
      MultiOracleCircuit.Program.eval_fixed, MultiOracleCircuit.Program.eval_adjoint,
      eval_spectate, mul_apply_eq_comp, ctrl_apply, Joint.fiber_apply, ih]
    split_ifs with hn
    · rw [Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), pow_succ']
      simp only [mul_apply_eq_comp]
    · rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      simp only [one_apply_eq_self, hA]

/-- **On label `j` the attempt is `(U₁ A U₂ A† U₃)^j A`**, for unitary oracles. -/
theorem trial_eval_apply (hO : ∀ l x, IsUnitary (O l x)) (x : X) (v : Joint (Fin M) W)
    (j : Fin M) :
    (trial M a h₁ h₂ h₃).eval x v j =
      ((U₁ * a.eval x * U₂ * star (a.eval x) * U₃) ^ (j : ℕ) * a.eval x) (v j) := by
  simp only [trial, MultiOracleCircuit.Program.eval_seq, mul_apply_eq_comp,
    steps_eval_apply M a h₁ h₂ h₃ hO x, eval_spectate, Joint.fiber_apply]
  rw [Nat.min_eq_right (by omega)]

/-- Steps `0, …, n - 1` make `2n` times the calls of the preparation. -/
theorem count_steps (n : ℕ) : (steps M a h₁ h₂ h₃ n).count = n * (2 * a.count) := by
  induction n with
  | zero => simp [steps]
  | succ n ih =>
    simp only [steps, step, MultiOracleCircuit.Program.count_seq,
      MultiOracleCircuit.Program.count_fixed, MultiOracleCircuit.Program.count_adjoint,
      count_spectate, ih]
    ring

/-- Steps `0, …, n - 1` make `2n` times the calls of the preparation, label by label. -/
theorem labelCount_steps [DecidableEq L] (l : L) (n : ℕ) :
    (steps M a h₁ h₂ h₃ n).labelCount l = n * (2 * a.labelCount l) := by
  induction n with
  | zero => simp [steps, MultiOracleCircuit.Program.identity]
  | succ n ih =>
    simp only [steps, step, MultiOracleCircuit.Program.labelCount_seq,
      MultiOracleCircuit.Program.labelCount_fixed, MultiOracleCircuit.Program.labelCount_adjoint,
      labelCount_spectate, ih]
    ring

/-- The attempt makes `2(M - 1) + 1` times the calls of the preparation. -/
theorem count_trial : (trial M a h₁ h₂ h₃).count = (2 * (M - 1) + 1) * a.count := by
  rw [trial, MultiOracleCircuit.Program.count_seq, count_steps, count_spectate]
  ring

/-- The attempt makes `2(M - 1) + 1` times the calls of the preparation, label by label. -/
theorem labelCount_trial [DecidableEq L] (l : L) :
    (trial M a h₁ h₂ h₃).labelCount l = (2 * (M - 1) + 1) * a.labelCount l := by
  rw [trial, MultiOracleCircuit.Program.labelCount_seq, labelCount_steps, labelCount_spectate]
  ring

/-- **The uniform cutoff seed** `M^{-1/2} Σ_j |j⟩ ⊗ ψ`. -/
def labelSeed (ψ : W) : Joint (Fin M) W :=
  Joint.const ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) • ψ)

omit [CompleteSpace W] in
/-- The uniform cutoff seed of a unit vector is a unit vector. -/
theorem norm_labelSeed (hM : 0 < M) (ψ : W) (hψ : ‖ψ‖ = 1) : ‖labelSeed M ψ‖ = 1 := by
  have h2 : ‖labelSeed M ψ‖ ^ 2 = 1 := by
    rw [labelSeed, Joint.norm_const_sq, norm_smul, hψ, mul_one, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), Fintype.card_fin]
    exact mul_inv_cancel₀ (by exact_mod_cast hM.ne')
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2

/-- **The attempt prepares the purified released attempt** `Release.trialVec`: for a trial
family `q` with the amplification shape of the preparation `a`, the attempt on the uniform
cutoff seed is `M^{-1/2} Σ_j |j⟩ ⊗ q_j(x) ψ`. -/
theorem trial_eval_labelSeed {Lq E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {Oq : Lq → X → W →L[ℂ] W} (q : ℕ → MultiOracleCircuit.Program Oq)
    (w : Lq → ℕ) (w' : L → ℕ) (h : GroverShape q w a w' U₁ U₂ U₃)
    (hO : ∀ l x, IsUnitary (O l x)) (hM : 0 < M) (ψ : W) (hψ : ‖ψ‖ = 1)
    (Fo : E →L[ℂ] W) (hFo : Fo.adjoint ∘L Fo = 1) (x : X) :
    (trial M a h.unitary₁ h.unitary₂ h.unitary₃).eval x (labelSeed M ψ) =
      ODELowerBoundExtensions.Release.trialVec
        (ODERepeatProtocol.ofCircuits q M hM ψ hψ Fo hFo) x := by
  ext j
  rw [trial_eval_apply M a _ _ _ hO x _ j, ← h.eval_eq j x]
  exact map_smul ((q j).eval x) _ ψ

end

end DysonSingleProgram.Coherent
