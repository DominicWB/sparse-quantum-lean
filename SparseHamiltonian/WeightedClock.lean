import SparseHamiltonian.ClockOperators

/-!
# Weighted finite Hilbert direct sums of clock branches

The branch spaces may depend on the branch index, so clock lengths need not
coincide. All global norms are the genuine Hilbert direct-sum norms. The
boundary map uses square-root probabilities and its resolvent energy is the
weighted average of the branch energies.
-/

namespace SparseHamiltonian.WeightedClock

noncomputable section
open scoped BigOperators ComplexConjugate
open ContinuousLinearMap

variable {ι : Type*} [Fintype ι]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)]

/-- The actual bounded diagonal operator on the finite Hilbert sum. -/
def diagonal (A : ∀ i, V i →L[ℂ] V i) : PiLp 2 V →L[ℂ] PiLp 2 V :=
  (PiLp.continuousLinearEquiv 2 ℂ V).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i => (A i).comp (ContinuousLinearMap.proj i))).comp
      (PiLp.continuousLinearEquiv 2 ℂ V).toContinuousLinearMap)

omit [Fintype ι] in
@[simp] theorem diagonal_apply (A : ∀ i, V i →L[ℂ] V i)
    (x : PiLp 2 V) (i : ι) : diagonal A x i = A i (x i) := rfl

/-- Boundary preparation with coherent square-root branch weights. -/
def boundary (p : ι → ℝ) (J : ∀ i, P →L[ℂ] V i) : P →L[ℂ] PiLp 2 V :=
  (PiLp.continuousLinearEquiv 2 ℂ V).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (Real.sqrt (p i) : ℂ) • J i))

omit [Fintype ι] in
@[simp] theorem boundary_apply (p : ι → ℝ) (J : ∀ i, P →L[ℂ] V i)
    (x : P) (i : ι) : boundary p J x i = (Real.sqrt (p i) : ℂ) • J i x := rfl

theorem sqrt_weight_sq (p : ℝ) (hp : 0 ≤ p) :
    ‖(Real.sqrt p : ℂ)‖ ^ 2 = p := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt hp]

theorem boundary_energy (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (J : ∀ i, P →L[ℂ] V i) (x : P) :
    ‖boundary p J x‖ ^ 2 = ∑ i, p i * ‖J i x‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i hi
  rw [boundary_apply, norm_smul, mul_pow, sqrt_weight_sq _ (hp i)]

theorem norm_diagonal_le (A : ∀ i, V i →L[ℂ] V i)
    (Q : ℝ) (hQ : 0 ≤ Q) (hA : ∀ i, ‖A i‖ ≤ Q) : ‖diagonal A‖ ≤ Q := by
  apply ContinuousLinearMap.opNorm_le_bound _ hQ
  intro x
  have hsq : ‖diagonal A x‖ ^ 2 ≤ (Q * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i, ‖diagonal A x i‖ ^ 2 ≤ ∑ i, (Q * ‖x i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact ((A i).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
      _ = (Q * ‖x‖) ^ 2 := by
        simp_rw [mul_pow]
        rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hQ (norm_nonneg _))).mp hsq

omit [Fintype ι] in
theorem diagonal_comp (A B : ∀ i, V i →L[ℂ] V i) :
    (diagonal A).comp (diagonal B) = diagonal (fun i => (A i).comp (B i)) := by
  ext x i
  rfl

omit [Fintype ι] in
theorem diagonal_one : diagonal (fun i => (1 : V i →L[ℂ] V i)) = 1 := by
  ext x i
  rfl

theorem diagonal_one_sub (A : ∀ i, V i →L[ℂ] V i) :
    diagonal (fun i => 1 - A i) = 1 - diagonal A := by
  ext x i
  rfl

theorem diagonal_resolvent_right (D R : ∀ i, V i →L[ℂ] V i)
    (hR : ∀ i, (1 - D i).comp (R i) = 1) :
    (1 - diagonal D).comp (diagonal R) = 1 := by
  rw [← diagonal_one_sub, diagonal_comp]
  simpa only [hR] using (diagonal_one (V := V))

theorem diagonal_resolvent_left (D R : ∀ i, V i →L[ℂ] V i)
    (hR : ∀ i, (R i).comp (1 - D i) = 1) :
    (diagonal R).comp (1 - diagonal D) = 1 := by
  rw [← diagonal_one_sub, diagonal_comp]
  simpa only [hR] using (diagonal_one (V := V))

omit [Fintype ι] in
theorem diagonal_boundary (p : ι → ℝ) (A : ∀ i, V i →L[ℂ] V i)
    (J : ∀ i, P →L[ℂ] V i) :
    (diagonal A).comp (boundary p J) = boundary p (fun i => (A i).comp (J i)) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, diagonal_apply, boundary_apply, map_smul]

theorem diagonal_boundary_energy (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (R : ∀ i, V i →L[ℂ] V i) (J : ∀ i, P →L[ℂ] V i) (x : P) :
    ‖diagonal R (boundary p J x)‖ ^ 2 = ∑ i, p i * ‖R i (J i x)‖ ^ 2 := by
  have h := congrArg (fun A : P →L[ℂ] PiLp 2 V => A x) (diagonal_boundary p R J)
  change diagonal R (boundary p J x) = boundary p (fun i => (R i).comp (J i)) x at h
  rw [h, boundary_energy p hp]
  rfl

theorem weighted_endpoint_energy_le (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (R : ∀ i, V i →L[ℂ] V i) (J : ∀ i, P →L[ℂ] V i)
    (hRJ : ∀ i x, ‖R i (J i x)‖ ^ 2 ≤ q i / 2 * ‖x‖ ^ 2) (x : P) :
    ‖diagonal R (boundary p J x)‖ ^ 2 ≤ (∑ i, p i * q i) / 2 * ‖x‖ ^ 2 := by
  rw [diagonal_boundary_energy p hp]
  calc
    ∑ i, p i * ‖R i (J i x)‖ ^ 2 ≤ ∑ i, p i * (q i / 2 * ‖x‖ ^ 2) := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hRJ i x) (hp i)
    _ = (∑ i, p i * q i) / 2 * ‖x‖ ^ 2 := by
      simp only [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem norm_weighted_endpoint_le (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (R : ∀ i, V i →L[ℂ] V i) (J : ∀ i, P →L[ℂ] V i)
    (hRJ : ∀ i x, ‖R i (J i x)‖ ^ 2 ≤ q i / 2 * ‖x‖ ^ 2) :
    ‖(diagonal R).comp (boundary p J)‖ ≤ Real.sqrt ((∑ i, p i * q i) / 2) := by
  have hqbar : 0 ≤ (∑ i, p i * q i) / 2 :=
    div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hq i)) (by norm_num)
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hqbar]
  exact weighted_endpoint_energy_le p q hp R J hRJ x

section Adjoint
variable [CompleteSpace P] [∀ i, CompleteSpace (V i)]

theorem diagonal_adjoint (A : ∀ i, V i →L[ℂ] V i) :
    (diagonal A).adjoint = diagonal (fun i => (A i).adjoint) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, diagonal_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem diagonal_isometry (D : ∀ i, V i →L[ℂ] V i)
    (hD : ∀ i, (D i).adjoint.comp (D i) = 1) :
    (diagonal D).adjoint.comp (diagonal D) = 1 := by
  rw [diagonal_adjoint, diagonal_comp]
  simpa only [hD] using (diagonal_one (V := V))

theorem boundary_adjoint_apply (p : ι → ℝ) (J : ∀ i, P →L[ℂ] V i)
    (x : PiLp 2 V) :
    (boundary p J).adjoint x = ∑ i, (Real.sqrt (p i) : ℂ) • (J i).adjoint (x i) := by
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, boundary_apply,
    sum_inner, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    ContinuousLinearMap.adjoint_inner_left]

/-- Compression on the common public space averages with probabilities, not amplitudes. -/
theorem boundary_compression (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (A : ∀ i, V i →L[ℂ] V i) (J : ∀ i, P →L[ℂ] V i) :
    (boundary p J).adjoint.comp ((diagonal A).comp (boundary p J)) =
      ∑ i, (p i : ℂ) • ((J i).adjoint.comp ((A i).comp (J i))) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, boundary_adjoint_apply, diagonal_apply,
    boundary_apply, map_smul, smul_smul, _root_.sum_apply,
    _root_.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact_mod_cast (Real.mul_self_sqrt (hp i))

theorem boundary_isometry (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (J : ∀ i, P →L[ℂ] V i) (hJ : ∀ i, (J i).adjoint.comp (J i) = 1) :
    (boundary p J).adjoint.comp (boundary p J) = 1 := by
  have h := boundary_compression p hp (fun i => (1 : V i →L[ℂ] V i)) J
  rw [diagonal_one] at h
  simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, hJ] at h
  rw [h, ← Finset.sum_smul]
  have hs : ∑ i, (p i : ℂ) = 1 := by exact_mod_cast hsum
  rw [hs, one_smul]
  rfl

/-- The public generator averaged with branch probabilities. -/
def generator (p : ι → ℝ) (H : ι → P →L[ℂ] P) : P →L[ℂ] P :=
  ∑ i, (p i : ℂ) • H i

theorem generator_selfAdjoint (p : ι → ℝ) (H : ι → P →L[ℂ] P)
    (hH : ∀ i, (H i).adjoint = H i) : (generator p H).adjoint = generator p H := by
  simp only [generator, map_sum, map_smulₛₗ, Complex.conj_ofReal, hH]

omit [CompleteSpace P] in
theorem norm_generator_le (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (H : ι → P →L[ℂ] P) (hH : ∀ i, ‖H i‖ ≤ 1) :
    ‖generator p H‖ ≤ 1 := by
  calc
    ‖generator p H‖ ≤ ∑ i, ‖(p i : ℂ) • H i‖ := norm_sum_le _ _
    _ ≤ ∑ i, p i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i)]
      simpa using mul_le_mul_of_nonneg_left (hH i) (hp i)
    _ = 1 := hsum

/-- The weighted direct sum preserves the Cayley clock boundary formula. -/
theorem resolvent_boundary_compression (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (R : ∀ i, V i →L[ℂ] V i)
    (J : ∀ i, P →L[ℂ] V i) (H : ι → P →L[ℂ] P)
    (hR : ∀ i, (J i).adjoint.comp ((R i).comp (J i)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • H i)) :
    (boundary p J).adjoint.comp ((diagonal R).comp (boundary p J)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • generator p H) := by
  rw [boundary_compression p hp R J]
  simp only [hR, smul_add, smul_smul, Finset.sum_add_distrib]
  have hsumC : ∑ i, (p i : ℂ) = 1 := by exact_mod_cast hsum
  have hconst : (∑ i, ((p i : ℂ) * (2 : ℂ)⁻¹) • (1 : P →L[ℂ] P)) =
      (2 : ℂ)⁻¹ • (1 : P →L[ℂ] P) := by
    rw [← Finset.sum_smul, ← Finset.sum_mul, hsumC, one_mul]
  rw [hconst]
  congr 1
  simp only [generator, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- A probability average is bounded by a common branch clock budget. -/
theorem average_length_le (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (Q : ℝ) (hq : ∀ i, q i ≤ Q) :
    ∑ i, p i * q i ≤ Q := by
  calc
    ∑ i, p i * q i ≤ ∑ i, p i * Q :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hq i) (hp i)
    _ = Q := by rw [← Finset.sum_mul, hsum, one_mul]

/-- All analytic clock promises assemble on the weighted Hilbert direct sum.
The endpoint budget is the average branch length, while the full inverse is
controlled by the maximum branch length. -/
theorem weighted_clock_promises (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) (hq : ∀ i, 0 ≤ q i) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqQ : ∀ i, q i ≤ Q) (D R : ∀ i, V i →L[ℂ] V i)
    (J : ∀ i, P →L[ℂ] V i) (H : ι → P →L[ℂ] P)
    (hD : ∀ i, (D i).adjoint.comp (D i) = 1)
    (hJ : ∀ i, (J i).adjoint.comp (J i) = 1)
    (hRleft : ∀ i, (R i).comp (1 - D i) = 1)
    (hRright : ∀ i, (1 - D i).comp (R i) = 1)
    (hRnorm : ∀ i, ‖R i‖ ≤ q i)
    (hcompression : ∀ i, (J i).adjoint.comp ((R i).comp (J i)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • H i))
    (hHerm : ∀ i, (H i).adjoint = H i) (hHnorm : ∀ i, ‖H i‖ ≤ 1)
    (henergy : ∀ i x, ‖R i (J i x)‖ ^ 2 ≤ q i / 2 * ‖x‖ ^ 2) :
    (diagonal D).adjoint.comp (diagonal D) = 1 ∧
    (boundary p J).adjoint.comp (boundary p J) = 1 ∧
    (diagonal R).comp (1 - diagonal D) = 1 ∧
    (1 - diagonal D).comp (diagonal R) = 1 ∧
    ‖diagonal R‖ ≤ Q ∧
    (boundary p J).adjoint.comp ((diagonal R).comp (boundary p J)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • generator p H) ∧
    (generator p H).adjoint = generator p H ∧
    ‖generator p H‖ ≤ 1 ∧
    ‖(diagonal R).comp (boundary p J)‖ ≤ Real.sqrt ((∑ i, p i * q i) / 2) ∧
    (Real.sqrt ((∑ i, p i * q i) / 2)) ^ 2 = (∑ i, p i * q i) / 2 ∧
    ∑ i, p i * q i ≤ Q := by
  refine ⟨diagonal_isometry D hD, boundary_isometry p hp hsum J hJ,
    diagonal_resolvent_left D R hRleft, diagonal_resolvent_right D R hRright,
    norm_diagonal_le R Q hQ (fun i => (hRnorm i).trans (hqQ i)),
    resolvent_boundary_compression p hp hsum R J H hcompression,
    generator_selfAdjoint p H hHerm, norm_generator_le p hp hsum H hHnorm,
    norm_weighted_endpoint_le p q hp hq R J henergy, ?_,
    average_length_le p q hp hsum Q hqQ⟩
  exact Real.sq_sqrt
    (div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hq i)) (by norm_num))

end Adjoint
end
end SparseHamiltonian.WeightedClock
