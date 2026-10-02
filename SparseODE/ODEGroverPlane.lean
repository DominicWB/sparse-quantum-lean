import SparseODE.ODEGroverRay

/-!
The exact invariant-plane formula for repeated signed Grover rotations.
The rank-one compression hypotheses are proved separately for the ray of the
actual prepared state. No action of the Grover iterate is assumed here.
-/

namespace SparseHamiltonian.ODEGroverPlane

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K]

/-- The signed product of the prepared-ray and successful-subspace reflections. -/
def grover (P Q : K →L[ℂ] K) : K →L[ℂ] K :=
  ((2 : ℂ) • P - 1) * (1 - (2 : ℂ) • Q)

/-- Mathematical coordinates only: these normalizations do not enter a circuit. -/
def goodVector (Q : K →L[ℂ] K) (ψ : K) (θ : ℝ) : K :=
  (Real.sin θ : ℂ)⁻¹ • Q ψ

def badVector (Q : K →L[ℂ] K) (ψ : K) (θ : ℝ) : K :=
  (Real.cos θ : ℂ)⁻¹ • (ψ - Q ψ)

def stateAt (Q : K →L[ℂ] K) (ψ : K) (θ φ : ℝ) : K :=
  (Real.sin φ : ℂ) • goodVector Q ψ θ +
    (Real.cos φ : ℂ) • badVector Q ψ θ

omit [CompleteSpace K] in
theorem stateAt_initial (Q : K →L[ℂ] K) (ψ : K) (θ : ℝ)
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) :
    stateAt Q ψ θ θ = ψ := by
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs
  have hcC : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hc
  simp only [stateAt, goodVector, badVector, smul_smul,
    mul_inv_cancel₀ hsC, mul_inv_cancel₀ hcC, one_smul]
  abel

theorem good_fixed (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ψ : K) (θ : ℝ) :
    Q (goodVector Q ψ θ) = goodVector Q ψ θ := by
  have hQQ : Q (Q ψ) = Q ψ :=
    congrArg (fun A : K →L[ℂ] K => A ψ) hQ.2
  simp only [goodVector, map_smul, hQQ]

theorem bad_killed (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ψ : K) (θ : ℝ) :
    Q (badVector Q ψ θ) = 0 := by
  have hQQ : Q (Q ψ) = Q ψ :=
    congrArg (fun A : K →L[ℂ] K => A ψ) hQ.2
  simp only [badVector, map_smul, map_sub, hQQ, sub_self, smul_zero]

omit [CompleteSpace K] in
theorem prepared_good (P Q : K →L[ℂ] K) (ψ : K) (θ : ℝ)
    (hs : Real.sin θ ≠ 0)
    (hPQ : P (Q ψ) = (Real.sin θ : ℂ) ^ 2 • ψ) :
    P (goodVector Q ψ θ) = (Real.sin θ : ℂ) • ψ := by
  have hsC : (Real.sin θ : ℂ) ≠ 0 := by exact_mod_cast hs
  simp only [goodVector, map_smul, hPQ, smul_smul]
  congr 1
  field_simp

omit [CompleteSpace K] in
theorem prepared_bad (P Q : K →L[ℂ] K) (ψ : K) (θ : ℝ)
    (hc : Real.cos θ ≠ 0) (hP : P ψ = ψ)
    (hPQ : P (Q ψ) = (Real.sin θ : ℂ) ^ 2 • ψ) :
    P (badVector Q ψ θ) = (Real.cos θ : ℂ) • ψ := by
  have hcC : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hc
  have hcs : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hcsC : 1 - (Real.sin θ : ℂ) ^ 2 = (Real.cos θ : ℂ) ^ 2 := by
    exact_mod_cast hcs
  calc
    P (badVector Q ψ θ) =
        (Real.cos θ : ℂ)⁻¹ • (ψ - (Real.sin θ : ℂ) ^ 2 • ψ) := by
          simp only [badVector, map_smul, map_sub, hP, hPQ]
    _ = ((Real.cos θ : ℂ)⁻¹ * (1 - (Real.sin θ : ℂ) ^ 2)) • ψ := by
          module
    _ = (Real.cos θ : ℂ) • ψ := by
          rw [hcsC]
          congr 1
          field_simp

/-- The sine coordinate after a single two-reflection rotation. -/
theorem sine_step (θ φ : ℝ) :
    2 * (-Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) * Real.sin θ +
      Real.sin φ = Real.sin (φ + 2 * θ) := by
  have hsc := congrArg (fun x : ℝ => Real.sin φ * x) (Real.sin_sq_add_cos_sq θ)
  rw [show φ + 2 * θ = (φ + θ) + θ by ring,
    Real.sin_add, Real.sin_add, Real.cos_add]
  nlinarith

/-- The complementary cosine coordinate after the same rotation. -/
theorem cosine_step (θ φ : ℝ) :
    2 * (-Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) * Real.cos θ -
      Real.cos φ = Real.cos (φ + 2 * θ) := by
  have hsc := congrArg (fun x : ℝ => Real.cos φ * x) (Real.sin_sq_add_cos_sq θ)
  rw [show φ + 2 * θ = (φ + θ) + θ by ring,
    Real.cos_add, Real.cos_add, Real.sin_add]
  nlinarith

/-- The Grover operator itself, rather than a stipulated plane action, advances
the angle by exactly twice the original successful amplitude angle. -/
theorem grover_stateAt (P Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ψ : K) (θ φ : ℝ)
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (hP : P ψ = ψ)
    (hPQ : P (Q ψ) = (Real.sin θ : ℂ) ^ 2 • ψ) :
    grover P Q (stateAt Q ψ θ φ) = stateAt Q ψ θ (φ + 2 * θ) := by
  have hg := prepared_good P Q ψ θ hs hPQ
  have hb := prepared_bad P Q ψ θ hc hP hPQ
  have hsplit : ψ = (Real.sin θ : ℂ) • goodVector Q ψ θ +
      (Real.cos θ : ℂ) • badVector Q ψ θ :=
    (stateAt_initial Q ψ θ hs hc).symm
  calc
    grover P Q (stateAt Q ψ θ φ) =
        ((2 * (-Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) : ℝ) : ℂ) • ψ +
          (Real.sin φ : ℂ) • goodVector Q ψ θ -
          (Real.cos φ : ℂ) • badVector Q ψ θ := by
      simp only [grover, stateAt, mul_apply_eq_comp, sub_apply, smul_apply,
        one_def, id_apply, map_add, map_sub, map_smul, map_zero,
        good_fixed Q hQ ψ θ, bad_killed Q hQ ψ θ, smul_zero, hg, hb,
        Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
      module
    _ = ((2 * (-Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) : ℝ) : ℂ) •
          ((Real.sin θ : ℂ) • goodVector Q ψ θ +
            (Real.cos θ : ℂ) • badVector Q ψ θ) +
          (Real.sin φ : ℂ) • goodVector Q ψ θ -
          (Real.cos φ : ℂ) • badVector Q ψ θ := by
      exact congrArg (fun v : K =>
        ((2 * (-Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) : ℝ) : ℂ) • v +
          (Real.sin φ : ℂ) • goodVector Q ψ θ -
          (Real.cos φ : ℂ) • badVector Q ψ θ) hsplit
    _ =
        ((2 * (-Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) *
          Real.sin θ + Real.sin φ : ℝ) : ℂ) • goodVector Q ψ θ +
        ((2 * (-Real.sin φ * Real.sin θ + Real.cos φ * Real.cos θ) *
          Real.cos θ - Real.cos φ : ℝ) : ℂ) • badVector Q ψ θ := by
      simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_neg, Complex.ofReal_ofNat]
      module
    _ = stateAt Q ψ θ (φ + 2 * θ) := by
      simp only [stateAt, sine_step, cosine_step]

/-- All iteration counts use the same two-dimensional plane. -/
theorem power_action (P Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ψ : K) (θ : ℝ)
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (hP : P ψ = ψ)
    (hPQ : P (Q ψ) = (Real.sin θ : ℂ) ^ 2 • ψ) (j : ℕ) :
    (grover P Q ^ j) ψ = stateAt Q ψ θ ((2 * (j : ℝ) + 1) * θ) := by
  induction j with
  | zero => simpa only [pow_zero, one_def, id_apply, Nat.cast_zero,
      mul_zero, zero_add, one_mul] using (stateAt_initial Q ψ θ hs hc).symm
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp, ih,
      grover_stateAt P Q hQ ψ θ _ hs hc hP hPQ]
    congr 1
    push_cast
    ring

theorem projected_stateAt (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ψ : K) (θ φ : ℝ) :
    Q (stateAt Q ψ θ φ) =
      ((Real.sin φ / Real.sin θ : ℝ) : ℂ) • Q ψ := by
  calc
    Q (stateAt Q ψ θ φ) = (Real.sin φ : ℂ) • goodVector Q ψ θ := by
      simp only [stateAt, map_add, map_smul, good_fixed Q hQ ψ θ,
        bad_killed Q hQ ψ θ, smul_zero, add_zero]
    _ = ((Real.sin φ / Real.sin θ : ℝ) : ℂ) • Q ψ := by
      simp only [goodVector, smul_smul, div_eq_mul_inv,
        Complex.ofReal_mul, Complex.ofReal_inv]

/-- Successful projection preserves the prepared good direction, with the
standard real scalar (which can be negative, giving only a global phase). -/
theorem projected_power (P Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ψ : K) (θ : ℝ)
    (hs : Real.sin θ ≠ 0) (hc : Real.cos θ ≠ 0) (hP : P ψ = ψ)
    (hPQ : P (Q ψ) = (Real.sin θ : ℂ) ^ 2 • ψ) (j : ℕ) :
    Q ((grover P Q ^ j) ψ) =
      ((Real.sin ((2 * (j : ℝ) + 1) * θ) / Real.sin θ : ℝ) : ℂ) • Q ψ := by
  rw [power_action P Q hQ ψ θ hs hc hP hPQ j]
  exact projected_stateAt Q hQ ψ θ _

/-- The probability of the actual successful projection is the familiar
odd-angle sine squared. No distribution of iteration counts is assumed. -/
theorem success_probability (P Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ψ : K) (θ : ℝ)
    (hs : 0 < Real.sin θ) (hc : Real.cos θ ≠ 0) (hP : P ψ = ψ)
    (hPQ : P (Q ψ) = (Real.sin θ : ℂ) ^ 2 • ψ)
    (hnorm : ‖Q ψ‖ = Real.sin θ) (j : ℕ) :
    ‖Q ((grover P Q ^ j) ψ)‖ ^ 2 =
      Real.sin ((2 * (j : ℝ) + 1) * θ) ^ 2 := by
  have hnormj : ‖Q ((grover P Q ^ j) ψ)‖ =
      |Real.sin ((2 * (j : ℝ) + 1) * θ)| := by
    rw [projected_power P Q hQ ψ θ (ne_of_gt hs) hc hP hPQ j,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, hnorm,
      abs_div, abs_of_pos hs]
    exact div_mul_cancel₀ _ (ne_of_gt hs)
  rw [hnormj, sq_abs]

end
end SparseHamiltonian.ODEGroverPlane
