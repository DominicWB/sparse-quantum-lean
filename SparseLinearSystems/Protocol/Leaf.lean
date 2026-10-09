import SparseLinearSystems.Protocol.Tree

/-!
# The final repeat-until-herald preparation

The final leaf repeats one public circuit (fresh seed each time) a bounded
number of times and stops at the first heralded success
(`ODERepeatProtocol.Protocol.repeatTrials` of a single-choice trial family).
With per-attempt success probability `p = ‖F† C_x ψ‖²` and decoded amplitude
`a = F† C_x ψ`:

* `single_successMass`: the success mass is `1 - (1 - p)^r`;
* `single_successDensity`: the unnormalised output is
  `(1 - (1 - p)^r) |â⟩⟨â|`, `â = a / ‖a‖`.
-/

namespace SparseLinearSystems.Protocol

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit ODEMixedOutput
open scoped InnerProduct

variable {K E X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {O : L → X → K →L[ℂ] K}

/-- A single-choice trial family. -/
def single (c : MultiOracleCircuit.Program O) (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K)
    (hF : F† ∘L F = 1) : ODERepeatProtocol.TrialFamily O E :=
  ODERepeatProtocol.ofCircuits (fun _ => c) 1 one_pos ψ hψ F hF

variable (c : MultiOracleCircuit.Program O) (ψ : K) (hψ : ‖ψ‖ = 1) (F : E →L[ℂ] K)
  (hF : F† ∘L F = 1) (x : X)

theorem single_amplitude (j : Fin 1) :
    (single c ψ hψ F hF).amplitude x j = (F†) (c.eval x ψ) := rfl

theorem single_meanSuccess :
    (single c ψ hψ F hF).meanSuccess x = ‖(F†) (c.eval x ψ)‖ ^ 2 := by
  show (∑ j : Fin 1, ‖(single c ψ hψ F hF).amplitude x j‖ ^ 2) / ((1 : ℕ) : ℝ) = _
  rw [Fin.sum_univ_one, Nat.cast_one, div_one]
  rfl

theorem single_oneTrialDensity :
    (single c ψ hψ F hF).oneTrialDensity x = pureOperator ((F†) (c.eval x ψ)) := by
  rw [ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus]
  show ((1 : ℕ) : ℂ)⁻¹ • ∑ j : Fin 1, pureOperator ((single c ψ hψ F hF).amplitude x j) = _
  rw [Fin.sum_univ_one, Nat.cast_one, inv_one, one_smul]
  rfl

theorem single_successMass (r : ℕ) :
    (ODERepeatProtocol.Protocol.repeatTrials (single c ψ hψ F hF) r).successMass x =
      1 - (1 - ‖(F†) (c.eval x ψ)‖ ^ 2) ^ r := by
  rw [ODERepeatProtocol.Protocol.repeat_successMass, single_meanSuccess]

theorem single_successDensity (r : ℕ) :
    (ODERepeatProtocol.Protocol.repeatTrials (single c ψ hψ F hF) r).successDensity x =
      (((1 - (1 - ‖(F†) (c.eval x ψ)‖ ^ 2) ^ r : ℝ)) : ℂ) •
        pureOperator (ODEStateNormalization.unitDirection ((F†) (c.eval x ψ))) := by
  set a := (F†) (c.eval x ψ) with ha
  have hborn := bornWeight_pureDirection a
  induction r with
  | zero =>
    show (0 : E →L[ℂ] E) = _
    simp
  | succ r ih =>
    show (single c ψ hψ F hF).oneTrialDensity x +
      ((1 - (single c ψ hψ F hF).meanSuccess x : ℝ) : ℂ) •
        (ODERepeatProtocol.Protocol.repeatTrials (single c ψ hψ F hF) r).successDensity x = _
    rw [ih, single_oneTrialDensity, single_meanSuccess, ← ha, ← hborn, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- The output specification of a single-choice repeat leaf. -/
theorem single_leaf_spec (hU : IsUnitary (c.eval x)) (r : ℕ) :
    let p := ODERepeatProtocol.Protocol.repeatTrials (single c ψ hψ F hF) r
    0 ≤ p.successMass x ∧ p.successMass x ≤ 1 ∧
      (p.successMass x ≠ 0 →
        ‖ODEStateNormalization.unitDirection ((F†) (c.eval x ψ))‖ = 1) ∧
      p.successDensity x = ((p.successMass x : ℝ) : ℂ) •
        pureOperator (ODEStateNormalization.unitDirection ((F†) (c.eval x ψ))) := by
  intro p
  have hprob := (single c ψ hψ F hF).probability_bounds x (fun _ => hU) ⟨0, Nat.one_pos⟩
  have hp : (single c ψ hψ F hF).probability x ⟨0, Nat.one_pos⟩ = ‖(F†) (c.eval x ψ)‖ ^ 2 := rfl
  rw [hp] at hprob
  obtain ⟨hp0, hp1⟩ := hprob
  have hm : p.successMass x = 1 - (1 - ‖(F†) (c.eval x ψ)‖ ^ 2) ^ r := single_successMass c ψ hψ F hF x r
  have hq0 : 0 ≤ 1 - ‖(F†) (c.eval x ψ)‖ ^ 2 := by linarith
  have hq1 : 1 - ‖(F†) (c.eval x ψ)‖ ^ 2 ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hm]
    have := pow_le_one₀ hq0 hq1 (n := r)
    linarith
  · rw [hm]
    have := pow_nonneg hq0 r
    linarith
  · intro hne
    apply ODEStateNormalization.unitDirection_norm
    intro ha
    apply hne
    rw [hm, ha, norm_zero]
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h]; simp
    · simp [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  · rw [single_successDensity, hm]

/-- The output direction of a fresh-trial leaf: the normalised decoded amplitude
of its first label. -/
def leafDir (x : X) : ODERepeatProtocol.Protocol O E → E
  | .abort => 0
  | .freshTrial t _ => ODEStateNormalization.unitDirection (t.amplitude x ⟨0, t.choices_pos⟩)

theorem leafDir_single (r : ℕ) :
    leafDir x (ODERepeatProtocol.Protocol.repeatTrials (single c ψ hψ F hF) (r + 1)) =
      ODEStateNormalization.unitDirection ((F†) (c.eval x ψ)) := rfl

end

end SparseLinearSystems.Protocol
