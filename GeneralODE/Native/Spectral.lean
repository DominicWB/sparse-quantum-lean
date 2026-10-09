import GeneralODE.Native.Arcsine
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# The arcsine LCU for a self-adjoint operator

For a self-adjoint operator `X` on a finite-dimensional space with
`‖X‖ ≤ 1/2`,
`‖∑_{k<N} ∑_{r<2N} c_{k,r} e^{i(2k+1-2r)X} - X‖ ≤ 4^{-N}`.
The proof diagonalises `X` in an orthonormal eigenbasis: on each eigenvector
the left side is the scalar truncation `p_N(sin λ) - λ`.
-/

namespace SparseHamiltonian.GeneralODE.Spectral

noncomputable section
open ContinuousLinearMap Arcsine FractionalAngleCoefficients
open scoped BigOperators InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The exponential acts on an eigenvector by the scalar exponential. -/
theorem exp_apply_of_eigen (T : E →L[ℂ] E) (v : E) (μ : ℂ) (hv : T v = μ • v) :
    NormedSpace.exp T v = Complex.exp μ • v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hpow : ∀ k : ℕ, (T ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, mul_apply_eq_comp, hv, map_smul, ih, smul_smul, pow_succ']
  have hS : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • T ^ k) (NormedSpace.exp T) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) T
  have hSv := hS.mapL (ContinuousLinearMap.apply ℂ E v)
  have hs : HasSum (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • μ ^ k) (Complex.exp μ) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ
  have hsv := hs.smul_const v
  have heq : (fun k : ℕ => ContinuousLinearMap.apply ℂ E v (((k.factorial : ℂ)⁻¹) • T ^ k)) =
      (fun k : ℕ => (((k.factorial : ℂ)⁻¹) • μ ^ k) • v) := by
    funext k
    rw [ContinuousLinearMap.apply_apply, smul_apply, hpow, smul_smul, smul_eq_mul]
  rw [heq] at hSv
  exact hSv.unique hsv

omit [FiniteDimensional ℂ E] in
/-- An operator diagonal in an orthonormal basis has norm at most the
largest modulus of its diagonal entries. -/
theorem norm_le_of_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ E) (T : E →L[ℂ] E) (μ : ι → ℂ)
    (hT : ∀ i, T (b i) = μ i • b i) (c : ℝ) (hc0 : 0 ≤ c) (hμ : ∀ i, ‖μ i‖ ≤ c) :
    ‖T‖ ≤ c := by
  apply ContinuousLinearMap.opNorm_le_bound _ hc0
  intro w
  have hrepr : b.repr (T w) = WithLp.toLp 2 (fun i => μ i * b.repr w i) := by
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum, map_sum]
    ext i
    simp only [map_smul, hT, OrthonormalBasis.repr_self, PiLp.smul_apply, Finset.sum_apply,
      WithLp.ofLp_sum, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro j _ hj
      simp [hj.symm]
    · simp
  rw [← b.repr.norm_map (T w), ← b.repr.norm_map w, hrepr]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simp only [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hμ i) 2) (by positivity)

/-- The arcsine Fourier LCU of a self-adjoint operator of norm at most `1/2`. -/
theorem lcu_approx (X : E →L[ℂ] E) (hX : IsSelfAdjoint X) (hXn : ‖X‖ ≤ 1 / 2) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, ∑ r ∈ Finset.range (2 * N),
        lcuCoef k r • NormedSpace.exp (((freq k r : ℂ) * Complex.I) • X) - X‖ ≤ (1 / 4) ^ N := by
  have hT : (X : E →ₗ[ℂ] E).IsSymmetric := hX.isSymmetric
  set b := hT.eigenvectorBasis (n := Module.finrank ℂ E) rfl with hb
  set lam := hT.eigenvalues (n := Module.finrank ℂ E) rfl with hlam
  have hev : ∀ i, X (b i) = ((lam i : ℝ) : ℂ) • b i := fun i => hT.apply_eigenvectorBasis rfl i
  have hlam_le : ∀ i, |lam i| ≤ 1 / 2 := by
    intro i
    have h1 : ‖X (b i)‖ = |lam i| := by
      rw [hev, norm_smul, b.orthonormal.1 i, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [← h1]
    calc ‖X (b i)‖ ≤ ‖X‖ * ‖b i‖ := X.le_opNorm _
      _ = ‖X‖ := by rw [b.orthonormal.1 i, mul_one]
      _ ≤ 1 / 2 := hXn
  apply norm_le_of_diagonal b _
    (fun i => (((correction 0 N).eval (Real.sin (lam i)) : ℝ) : ℂ) - ((lam i : ℝ) : ℂ))
  · intro i
    rw [sub_apply, hev, sum_apply, correction_sin_eq, sub_smul, Finset.sum_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [sum_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro r _
    rw [smul_apply, exp_apply_of_eigen _ (b i) ((freq k r : ℂ) * Complex.I * (lam i : ℝ))]
    · rw [smul_smul]
      congr 2
      ring_nf
    · rw [smul_apply, hev, smul_smul]
  · positivity
  · intro i
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact correction_sin_sub_le (lam i) (hlam_le i) N

end

end SparseHamiltonian.GeneralODE.Spectral
