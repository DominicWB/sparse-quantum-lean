import SparseHamiltonian.CayleyApproximation

/-!
# Chronological composition of an explicitly constructed catalyst

Each private time slot receives the local catalyst for the public state that
reaches that slot. The finite Hilbert norm adds its squared costs, and the
public action is the corresponding power of the local public action.
-/

namespace SparseHamiltonian.ChronologicalCatalyst

noncomputable section

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent
open scoped BigOperators

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Stack a private response along successive public powers. -/
def stackedResponse (Γ : P →L[ℂ] V) (U : P →L[ℂ] P) (T : ℕ) :
    P →L[ℂ] BlockOperator.H T V :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin T => V)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun r : Fin T => Γ ∘L (U ^ (r : ℕ)))

@[simp] theorem stackedResponse_apply (Γ : P →L[ℂ] V) (U : P →L[ℂ] P)
    (T : ℕ) (p : P) (r : Fin T) : stackedResponse Γ U T p r = Γ ((U ^ (r : ℕ)) p) := rfl

/-- The public trajectory with an arbitrary initial public state. -/
def publicState (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (y : ℕ → V) (p : P) (n : ℕ) : P :=
  (u ^ n) p + forcedPublicState u B y n

@[simp] theorem publicState_zero (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (y : ℕ → V) (p : P) : publicState u B y p 0 = p := by
  simp [publicState]

theorem publicState_succ (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (y : ℕ → V) (p : P) (n : ℕ) :
    publicState u B y p (n + 1) = u (publicState u B y p n) + B (y n) := by
  simp only [publicState, forcedPublicState_succ, pow_succ', mul_apply_eq_comp, map_add]
  abel

/-- Local transduction propagates the actual public trajectory by powers of U. -/
theorem catalyst_publicState (Γ : P →L[ℂ] V) (U u : P →L[ℂ] P)
    (B : V →L[ℂ] P) (hPublic : u + B ∘L Γ = U) (p : P) (n : ℕ) :
    publicState u B (fun k => Γ ((U ^ k) p)) p n = (U ^ n) p := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [publicState_succ, hn, pow_succ', mul_apply_eq_comp]
      exact congrArg (fun L : P →L[ℂ] P => L ((U ^ n) p)) hPublic

/-- The stacked catalyst is stationary under the actual finite chronological
private block, including the input from the initial public state. -/
theorem catalyst_private_transduction
    (D : V →L[ℂ] V) (A Γ : P →L[ℂ] V) (U u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hPrivate : A + D ∘L Γ = Γ) (hPublic : u + B ∘L Γ = U) (T : ℕ) :
    stackedResponse A u T + chronologicalOperator D A u B T ∘L stackedResponse Γ U T =
      stackedResponse Γ U T := by
  ext p r
  simp only [add_apply, comp_apply, PiLp.add_apply, stackedResponse_apply]
  have hInput : stackedResponse Γ U T p =
      WithLp.toLp 2 (fun k : Fin T => Γ ((U ^ (k : ℕ)) p)) := rfl
  rw [hInput, chronologicalOperator_apply D A u B (fun k => Γ ((U ^ k) p)) r]
  simp only [chronologicalPrivateState]
  have hPub := catalyst_publicState Γ U u B hPublic p (r : ℕ)
  have hPrivate' := congrArg (fun L : P →L[ℂ] V => L ((U ^ (r : ℕ)) p)) hPrivate
  simp only [add_apply, comp_apply] at hPrivate'
  have hA := congrArg A hPub
  simp only [publicState, map_add] at hA
  rw [← hA] at hPrivate'
  convert hPrivate' using 1
  abel

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
/-- Powers of a norm-preserving public map preserve every input norm. -/
theorem public_pow_norm (U : P →L[ℂ] P) (hU : ∀ p, ‖U p‖ = ‖p‖)
    (n : ℕ) (p : P) : ‖(U ^ n) p‖ = ‖p‖ := by
  induction n with
  | zero => simp
  | succ n hn => simpa only [pow_succ', mul_apply_eq_comp, hU] using hn

/-- Squared catalyst costs add over the chronological slots in the genuine
Hilbert direct-sum norm. -/
theorem stackedResponse_norm_sq_le (Γ : P →L[ℂ] V) (U : P →L[ℂ] P)
    (hU : ∀ p, ‖U p‖ = ‖p‖) (C : ℝ) (hΓ : ‖Γ‖ ^ 2 ≤ C) (T : ℕ) :
    ‖stackedResponse Γ U T‖ ^ 2 ≤ (T : ℝ) * C := by
  have hC : 0 ≤ C := (sq_nonneg ‖Γ‖).trans hΓ
  have hTC : 0 ≤ (T : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC
  have hBound : ‖stackedResponse Γ U T‖ ≤ Real.sqrt ((T : ℝ) * C) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
    intro p
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hTC, PiLp.norm_sq_eq_of_L2]
    calc
      ∑ r : Fin T, ‖stackedResponse Γ U T p r‖ ^ 2 ≤
          ∑ _ : Fin T, C * ‖p‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        rw [stackedResponse_apply]
        calc
          ‖Γ ((U ^ (r : ℕ)) p)‖ ^ 2 ≤ (‖Γ‖ * ‖(U ^ (r : ℕ)) p‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (le_opNorm _ _) 2
          _ = ‖Γ‖ ^ 2 * ‖p‖ ^ 2 := by rw [public_pow_norm U hU, mul_pow]
          _ ≤ C * ‖p‖ ^ 2 := mul_le_mul_of_nonneg_right hΓ (sq_nonneg _)
      _ = (T : ℝ) * C * ‖p‖ ^ 2 := by simp [mul_assoc]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hBound 2
  simpa only [Real.sq_sqrt hTC] using hs

end

end SparseHamiltonian.ChronologicalCatalyst
