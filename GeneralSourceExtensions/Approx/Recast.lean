import GateEfficientSynthesis.Perturb
import GeneralSourceODE.Oracles
import SparseHamiltonian.OracleStability

/-!
# Programs over approximate oracles and the perturbed four-attempt protocol

A program of `MultiOracleCircuit` fixes its syntax before the oracles: the same instructions run
over any oracle family with the same labels (`recast`), on any input type, with the same weighted
costs (`cost_recast`). With unitary oracles, the recast program at an input `y` is within
`δ · cost w` of the original at `x` whenever every oracle `l` at `y` is within `δ · w l` of the
oracle at `x` (`eval_recast_sub_le`).

The released four-attempt protocol depends only on the trial evaluations, the public seed and the
public output flag. If every trial of a family with mean Born success at least `1/4` and
phase-free direction error `δ` is moved by at most `η ≤ 1/400` in operator norm, four fresh
trials of the moved family succeed with probability at least `2/3` and their conditional output
is a density operator within trace distance `6 δ + 12 η` of the target (`perturbed_four`, from
`GateSynth.perturb_four`).

`ApproxCertificate` is the guarantee of the four-attempt protocol over the supplied source
oracles without the success constant `175/256`: success at least `2/3`, the released worst-case
counts of matrix queries and of `P_w`, `U_load` and `P_w†`, a density output within trace
distance `ε` of the normalised target. `approx_certificate` transfers the released complete
certificate of a counted two-interface family at one input to the recast actual-oracle family at
another input, when the matrix oracles agree and every supplied source oracle is within `δ` in
operator norm, under `30 g δ ≤ 1/400` and `30 g δ ≤ ε/20`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions

noncomputable section
open ContinuousLinearMap OracleCircuit
open ODEStateNormalization (unitDirection unitDirection_norm)
open GeneralSourceODE (SourceCall)
open scoped InnerProduct BigOperators

/-! ### Recasting a program -/

section Recast

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {L X Y : Type*} {O : L → X → K →L[ℂ] K} {O' : L → Y → K →L[ℂ] K}

/-- The same program syntax over another oracle family with the same labels. -/
def recast : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O'
  | .fixed U hU => .fixed U hU
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (recast p) (recast q)

/-- Recasting keeps every weighted cost. -/
@[simp] theorem cost_recast (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (recast (O' := O') p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [recast, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- With equal oracles at `x` and `y`, the recast program at `y` is the program at `x`. -/
theorem eval_recast_eq (p : MultiOracleCircuit.Program O) (x : X) (y : Y)
    (h : ∀ l, O' l y = O l x) : (recast (O' := O') p).eval y = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => exact h l
  | queryAdjoint l =>
      simp only [recast, MultiOracleCircuit.Program.eval_queryAdjoint, h]
  | seq p q hp hq => simp only [recast, MultiOracleCircuit.Program.eval_seq, hp, hq]

/-- **Perturbation of a recast program.** With unitary oracles, if every oracle `l` at `y` is
within `δ · w l` of the oracle at `x`, the recast program at `y` is within `δ · cost w` of the
program at `x`; inverse calls have the error of forward calls. -/
theorem eval_recast_sub_le (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (hO' : ∀ l y, IsUnitary (O' l y)) (x : X) (y : Y)
    (δ : ℝ) (w : L → ℕ) (h : ∀ l, ‖O' l y - O l x‖ ≤ δ * w l) :
    ‖(recast (O' := O') p).eval y - p.eval x‖ ≤ δ * p.cost w := by
  induction p with
  | fixed U hU => simp [recast]
  | query l => exact h l
  | queryAdjoint l =>
      simp only [recast, MultiOracleCircuit.Program.eval_queryAdjoint,
        MultiOracleCircuit.Program.cost_queryAdjoint, ← star_sub, norm_star]
      exact h l
  | seq p q hp hq =>
      simp only [recast, MultiOracleCircuit.Program.eval_seq,
        MultiOracleCircuit.Program.cost_seq, Nat.cast_add, mul_add]
      exact (product_error_le _ _ _ _ ((recast (O' := O') q).eval_unitary hO' y).norm_le_one
        (p.eval_unitary hO x).norm_le_one).trans (add_le_add hp hq)

end Recast

/-! ### The perturbed four-attempt protocol -/

section Perturbed

variable {P R : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- An isometry has a contractive adjoint. -/
theorem norm_adjoint_apply_le (F : P →L[ℂ] R) (hF : F† ∘L F = 1) (w : R) :
    ‖(F†) w‖ ≤ ‖w‖ := by
  have h := ODERepeatProtocol.herald_probability_partition F hF w
  have h0 := sq_nonneg ‖w - F ((F†) w)‖
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith)

variable [FiniteDimensional ℂ P]
variable {L₁ L₂ X₁ X₂ : Type*} {O₁ : L₁ → X₁ → R →L[ℂ] R} {O₂ : L₂ → X₂ → R →L[ℂ] R}

/-- **The perturbed four-attempt protocol.** Let the trials `q₁ j` at `x₁` have mean Born success
at least `1/4` and phase-free direction error `δ` for a unit target `v`, and let every trial
`q₂ j` at `x₂` be within `η ≤ 1/400` of `q₁ j` at `x₁` in operator norm (both unitary). Then four
fresh trials of `q₂` succeed with probability at least `2/3`, and their conditional output is a
density operator within trace distance `6 δ + 12 η` of `|v⟩⟨v|`. -/
theorem perturbed_four (q₁ : ℕ → MultiOracleCircuit.Program O₁)
    (q₂ : ℕ → MultiOracleCircuit.Program O₂) {M : ℕ} (hM : 0 < M) {ψ : R} (hψ : ‖ψ‖ = 1)
    {F : P →L[ℂ] R} (hF : F† ∘L F = 1) (x₁ : X₁) (x₂ : X₂) (v : P) (hv : ‖v‖ = 1)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη1 : η ≤ 1 / 400)
    (hU₁ : ∀ j, IsUnitary ((q₁ j).eval x₁)) (hU₂ : ∀ j, IsUnitary ((q₂ j).eval x₂))
    (hclose : ∀ j, j < M → ‖(q₂ j).eval x₂ - (q₁ j).eval x₁‖ ≤ η)
    (hmean : (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range M,
      ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) / (M : ℝ))
    (hdir : ∀ j, j < M → (F†) ((q₁ j).eval x₁ ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection ((F†) ((q₁ j).eval x₁ ψ)) - v‖ ≤ δ) :
    (2 : ℝ) / 3 ≤ (ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).successMass x₂ ∧
    ODEMixedOutput.IsDensity
      ((ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂) ∧
    ∃ h : ((ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂ -
        ODEMixedOutput.pureOperator v).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance
        ((ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂)
        (ODEMixedOutput.pureOperator v) h ≤ 6 * δ + 12 * η := by
  let t₁ := ODERepeatProtocol.ofCircuits q₁ M hM ψ hψ F hF
  let t₂ := ODERepeatProtocol.ofCircuits q₂ M hM ψ hψ F hF
  have hu₁ : ∀ j, IsUnitary ((t₁.circuit j).eval x₁) := fun j => hU₁ j.val
  have hu₂ : ∀ j, IsUnitary ((t₂.circuit j).eval x₂) := fun j => hU₂ j.val
  have hb₁ := t₁.probability_bounds x₁ hu₁
  have hb₂ := t₂.probability_bounds x₂ hu₂
  have ha : ∀ j, ‖t₁.amplitude x₁ j‖ ≤ 1 := fun j =>
    (sq_le_one_iff₀ (norm_nonneg _)).mp (hb₁ j).2
  have ha' : ∀ j, ‖t₂.amplitude x₂ j‖ ≤ 1 := fun j =>
    (sq_le_one_iff₀ (norm_nonneg _)).mp (hb₂ j).2
  have hclose' : ∀ j : Fin t₂.choices, ‖t₂.amplitude x₂ j - t₁.amplitude x₁ j‖ ≤ η := by
    intro j
    change ‖(F†) ((q₂ j.val).eval x₂ ψ) - (F†) ((q₁ j.val).eval x₁ ψ)‖ ≤ η
    rw [← map_sub, ← sub_apply]
    refine (norm_adjoint_apply_le F hF _).trans ?_
    refine ((le_opNorm _ _).trans ?_)
    rw [hψ, mul_one]
    exact hclose j.val j.isLt
  have hmean' : (1 : ℝ) / 4 ≤
      ODERepeatProbability.mean (fun j : Fin M => ‖t₁.amplitude x₁ j‖ ^ 2) := by
    unfold ODERepeatProbability.mean
    have hsum : (∑ j : Fin M, ‖t₁.amplitude x₁ j‖ ^ 2) =
        ∑ j ∈ Finset.range M,
          ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) M]
      exact Finset.sum_congr rfl (fun j _ => t₁.probability_eq_projected x₁ j)
    rw [hsum]
    exact hmean
  have hdir' : ∀ j : Fin t₁.choices, t₁.amplitude x₁ j ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection (t₁.amplitude x₁ j) - v‖ ≤ δ :=
    fun j hz => hdir j.val j.isLt hz
  obtain ⟨hS2, hD, hh, htr⟩ := GateSynth.perturb_four hM (t₁.amplitude x₁) (t₂.amplitude x₂) v hv
    hδ hη1 ha ha' hclose' hmean' hdir'
  have hsucc : (ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).successMass x₂ =
      ODERepeatProbability.successProbability (t₂.probability x₂) :=
    ODERepeatProtocol.Protocol.four_successMass_eq t₂ x₂
  have hdens : (ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂ =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight (t₂.probability x₂))
        (fun b => t₂.outputDirection x₂ b.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq t₂ x₂
  refine ⟨?_, ?_, ?_⟩
  · rw [hsucc]
    exact hS2
  · rw [hdens]
    exact hD
  · rw [hdens]
    exact ⟨hh, htr⟩

end Perturbed

/-! ### The certificate over approximate source oracles -/

section Certificate

variable {P R Y : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **Guarantee of a protocol over approximately implemented source oracles**: success at
least `2/3`, the released worst-case counts of matrix queries and of `P_w`, `U_load` and `P_w†`
over all histories, and a density output within trace distance `ε` of the normalised target. It is
`GeneralSourceODE.Oracles.ActualCertificate` without the success constant `175/256`. -/
structure ApproxCertificate {O : NativeSparseBlockEncoding.Query ⊕ SourceCall → Y → R →L[ℂ] R}
    (A : ODERepeatProtocol.Protocol O P) (y : Y) (target : P) (s Θ ell g ε : ℝ) :
    Prop where
  success_two_thirds : (2 : ℝ) / 3 ≤ A.successMass y
  matrix_queries :
    (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
      1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell
  weight_calls : (A.worstCost (GeneralSourceODE.Oracles.calls .weight) : ℝ) ≤ 40 * g
  load_calls : (A.worstCost (GeneralSourceODE.Oracles.calls .load) : ℝ) ≤ 40 * g
  unweight_calls : (A.worstCost (GeneralSourceODE.Oracles.calls .unweight) : ℝ) ≤ 40 * g
  source_calls : (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ 120 * g
  output_density : ODEMixedOutput.IsDensity (A.conditionalDensity y)
  conditional_error :
    ∃ h : (A.conditionalDensity y -
        ODEMixedOutput.pureOperator (unitDirection target)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (A.conditionalDensity y)
        (ODEMixedOutput.pureOperator (unitDirection target)) h ≤ ε

/-- The released guarantee over exact oracles gives the approximate one. -/
theorem ApproxCertificate.of_actual
    {O : NativeSparseBlockEncoding.Query ⊕ SourceCall → Y → R →L[ℂ] R}
    {A : ODERepeatProtocol.Protocol O P} {y : Y} {target : P} {s Θ ell g ε : ℝ}
    (h : GeneralSourceODE.Oracles.ActualCertificate A y target s Θ ell g ε) :
    ApproxCertificate A y target s Θ ell g ε :=
  { success_two_thirds := h.success_two_thirds
    matrix_queries := h.matrix_queries
    weight_calls := h.weight_calls
    load_calls := h.load_calls
    unweight_calls := h.unweight_calls
    source_calls := h.source_calls
    output_density := h.output_density
    conditional_error := h.conditional_error }

set_option maxHeartbeats 1000000 in
/-- **Transfer to approximate source oracles.** Let a counted two-interface family `q` satisfy
the released complete certificate at the input `x₁`, and let `q₁` over the exact actual oracles
`O₁` have the same evaluations at `x₁`, the same matrix counts, one `P_w` and one `U_load` call
per preparation call and one `P_w†` call per unpreparation call. If, at another input `x₂`, the
oracles `O₂` agree with `O₁` at `x₁` on the matrix labels and are within `δ` on the three source
labels, with `30 g δ ≤ 1/400` and `30 g δ ≤ ε/20`, then four fresh trials of the recast family
over `O₂` satisfy `ApproxCertificate` at `x₂`. -/
theorem approx_certificate {L X₁ X₂ : Type*} {O : (L ⊕ Bool) → X₁ → R →L[ℂ] R}
    {O₁ : NativeSparseBlockEncoding.Query ⊕ SourceCall → X₁ → R →L[ℂ] R}
    {O₂ : NativeSparseBlockEncoding.Query ⊕ SourceCall → X₂ → R →L[ℂ] R}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R} {F : P →L[ℂ] R} {x₁ : X₁}
    {target : P} {s Θ ell g ε : ℝ}
    (hCert : ODECompleteTrial.Certificate q M ψ F x₁ target s Θ ell g ε)
    (q₁ : ℕ → MultiOracleCircuit.Program O₁) (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hEval : ∀ j, (q₁ j).eval x₁ = (q j).eval x₁)
    (hMatrix : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (hWeight : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .weight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hLoad : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .load) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hUnweight : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .unweight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hSource : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.sourceCalls =
      2 * (q j).cost (ODESourceQueryBudget.sourceWeight false) +
        (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hO₁ : ∀ l y, IsUnitary (O₁ l y)) (hO₂ : ∀ l y, IsUnitary (O₂ l y))
    (x₂ : X₂) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdev : ∀ l, ‖O₂ l x₂ - O₁ l x₁‖ ≤ δ * GeneralSourceODE.Oracles.sourceCalls l)
    (hδ1 : 30 * g * δ ≤ 1 / 400) (hδε : 30 * g * δ ≤ ε / 20) (hTarget : target ≠ 0) :
    ApproxCertificate
      (ODERepeatProtocol.fourTrials (fun j => recast (O' := O₂) (q₁ j)) M hM ψ hψ F hF) x₂
      target s Θ ell g ε := by
  have hTrial := hCert.trial
  have hε : 0 ≤ ε := by
    obtain ⟨_, h⟩ := hCert.conditional_error
    exact (ODEMixedOutput.hermitianTraceDistance_nonneg _ _ _).trans h
  let q₂ : ℕ → MultiOracleCircuit.Program O₂ := fun j => recast (O' := O₂) (q₁ j)
  have hcost₂ : ∀ (w : NativeSparseBlockEncoding.Query ⊕ SourceCall → ℕ) j,
      (q₂ j).cost w = (q₁ j).cost w := fun w j => cost_recast (q₁ j) w
  -- Per-trial perturbation.
  have hclose : ∀ j, j < M → ‖(q₂ j).eval x₂ - (q₁ j).eval x₁‖ ≤ 30 * g * δ := by
    intro j hj
    have h := eval_recast_sub_le (O' := O₂) (q₁ j) hO₁ hO₂ x₁ x₂ δ
      GeneralSourceODE.Oracles.sourceCalls hdev
    refine h.trans ?_
    have hc : ((q₁ j).cost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ 30 * g := by
      rw [hSource j]
      push_cast
      have h1 := hTrial.source_queries j hj false
      have h2 := hTrial.source_queries j hj true
      linarith
    calc δ * ((q₁ j).cost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ δ * (30 * g) :=
          mul_le_mul_of_nonneg_left hc hδ
      _ = 30 * g * δ := by ring
  have hU₁ : ∀ j, IsUnitary ((q₁ j).eval x₁) := fun j => (q₁ j).eval_unitary hO₁ x₁
  have hU₂ : ∀ j, IsUnitary ((q₂ j).eval x₂) := fun j => (q₂ j).eval_unitary hO₂ x₂
  have hmean : (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range M,
      ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) / (M : ℝ) := by
    simp only [hEval]
    exact hTrial.mean_success
  have hdir : ∀ j, j < M → (F†) ((q₁ j).eval x₁ ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection ((F†) ((q₁ j).eval x₁ ψ)) -
        unitDirection target‖ ≤ ε / 500 := by
    intro j hj hz
    rw [hEval j] at hz ⊢
    exact hTrial.direction_error j hj hz
  obtain ⟨hS2, hD, hh, htr⟩ := perturbed_four q₁ q₂ hM hψ hF x₁ x₂ (unitDirection target)
    (unitDirection_norm target hTarget) (δ := ε / 500) (by positivity) hδ1 hU₁ hU₂ hclose
    hmean hdir
  refine
    { success_two_thirds := hS2
      matrix_queries := ?_
      weight_calls := ?_
      load_calls := ?_
      unweight_calls := ?_
      source_calls := ?_
      output_density := hD
      conditional_error := ⟨hh, htr.trans (by linarith)⟩ }
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      GeneralSourceODE.Oracles.matrixCalls
      (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
      (fun j hj => by rw [hcost₂, hMatrix j]; exact hTrial.matrix_queries j hj)
    calc
      _ ≤ 4 * (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) := h
      _ = 1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by ring
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      (GeneralSourceODE.Oracles.calls .weight) (10 * g)
      (fun j hj => by rw [hcost₂, hWeight j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      (GeneralSourceODE.Oracles.calls .load) (10 * g)
      (fun j hj => by rw [hcost₂, hLoad j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      (GeneralSourceODE.Oracles.calls .unweight) (10 * g)
      (fun j hj => by rw [hcost₂, hUnweight j]; exact hTrial.source_queries j hj true)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      GeneralSourceODE.Oracles.sourceCalls (30 * g) (fun j hj => by
        rw [hcost₂, hSource j]
        push_cast
        have h1 := hTrial.source_queries j hj false
        have h2 := hTrial.source_queries j hj true
        linarith)
    linarith

end Certificate

end

end SparseHamiltonian.GeneralSourceExtensions
