import SparseLowerBounds.ODE.Theorem

set_option autoImplicit false

/-!
# The arithmetic of Theorem `odel:thm:combined`

Manuscript: the proof of Theorem `odel:thm:combined` (the class contains the joint
family and the `g = 1` families of Lemma `odel:lem:herald`; the maximum of their lower bounds is
at least a fixed fraction of their sum).

`combinedBound_le_max`: three reals `Q_J`, `Q_M`, `Q_P` satisfying the joint bound
`c_J ḡ √s τ ≤ Q_J` (`c_J = jointConst = 1/400`) and the precision and mixed bounds of the
released assembly `SparseLowerBounds.Hamiltonian.assembly` (in the cases where they hold) have
`c (ḡ √s τ + √(sτr) + r) ≤ max(Q_J, Q_M, Q_P)`, `c = combinedConst = log 2/(8192π)`. It is the
step of `SparseLowerBounds.ODE.combined_max` stated for arbitrary reals, so that every max form
of the theorem (sampled-time access, padded families, the released solver's oracle) reduces to
three per-family bounds.
-/

namespace AdaptiveODELowerBound

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **The arithmetic of Theorem `odel:thm:combined`** (proof of Theorem `odel:thm:combined`): on
`CombinedRange`, reals `Q_J`, `Q_M`, `Q_P` satisfying the joint bound `c_J ḡ √s τ ≤ Q_J` and the
precision and mixed bounds of Lemma `odel:lem:herald` (in the cases where they hold) have
`c (ḡ √s τ + √(sτr) + r) ≤ max(Q_J, Q_M, Q_P)`, `c = log 2/(8192π)`. -/
theorem combinedBound_le_max (h : CombinedRange s τ gbar ε) {QJ QM QP : ℝ}
    (hJ : jointConst * gbar * Real.sqrt s * τ ≤ QJ)
    (hP : 64 * τ ≤ hsL ε → hsR τ ε / 32 ≤ QP ∧
      ((s : ℝ) < 64 * precN τ ε / τ → Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ QP))
    (hM : 64 * τ ≤ hsL ε → 64 * (precN τ ε : ℝ) / τ ≤ s →
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ QM) :
    combinedBound s τ gbar ε ≤ max QJ (max QM QP) := by
  have hH := h.toHSRange
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) (by linarith [h.tau_ge])
  have hcJ : cT ≤ jointConst * gbar := by
    have := cT_le_inv_200
    unfold jointConst
    linarith [h.gbar_ge]
  have hT : cT * Real.sqrt s * τ ≤ QJ := by
    calc cT * Real.sqrt s * τ = cT * (Real.sqrt s * τ) := by ring
      _ ≤ jointConst * gbar * (Real.sqrt s * τ) := mul_le_mul_of_nonneg_right hcJ hS
      _ = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hmax := assembly hH hT hP hM
  have hg : c0 * gbar * (Real.sqrt s * τ) ≤ jointConst * gbar * (Real.sqrt s * τ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right c0_le_jointConst (by linarith [h.gbar_ge])) hS
  have hle := le_max_left QJ (max QM QP)
  have hJ' : jointConst * gbar * (Real.sqrt s * τ) ≤ QJ := by
    calc jointConst * gbar * (Real.sqrt s * τ) = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hsτ : gbar * Real.sqrt s * τ = gbar * (Real.sqrt s * τ) := by ring
  unfold combinedBound
  rw [combinedConst_eq, hsτ]
  linarith [mul_nonneg c0_pos.le hS]

end

end AdaptiveODELowerBound
