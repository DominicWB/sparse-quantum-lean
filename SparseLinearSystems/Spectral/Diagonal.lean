import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Diagonal quadratic forms and the inertia lemma

Elementary finite-dimensional spectral tools used by the kernel-walk gap
argument (manuscript Lemma `qls:lem:walk`).

* `inner_basis_apply`, `inner_apply_diag`: matrix elements of an operator that
  acts diagonally on an orthonormal basis.
* `inverseOfInjective`: the two-sided continuous inverse of an injective
  endomorphism of a finite-dimensional space.
* `inertia_injective`: if `B` is self-adjoint and its nonzero eigenvalues have
  modulus at least `d`, and `Δ` is self-adjoint with `0 < ⟪x, Δ x⟫ ≤ q ‖x‖²`
  for `x ≠ 0` and `q < d`, then `B + Δ` is injective.  The proof splits a vector
  into the negative and non-negative spectral parts of `B`; no eigenvalue
  perturbation theorem is used.
-/

namespace SparseLinearSystems.Diagonal

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

section Basis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix elements of a basis-diagonal operator. -/
theorem inner_basis_apply (b : OrthonormalBasis ι ℂ V) (M : V →L[ℂ] V) (f : ι → ℂ)
    (hM : ∀ i, M (b i) = f i • b i) (i : ι) (w : V) :
    inner ℂ (b i) (M w) = f i * inner ℂ (b i) w := by
  conv_lhs => rw [← b.sum_repr' w]
  rw [map_sum, inner_sum]
  have hterm : ∀ j : ι, inner ℂ (b i) (M (inner ℂ (b j) w • b j)) =
      if i = j then f i * inner ℂ (b i) w else 0 := by
    intro j
    rw [map_smul, hM, smul_smul, inner_smul_right,
      orthonormal_iff_ite.mp b.orthonormal i j]
    by_cases h : i = j
    · subst h; simp [mul_comm]
    · simp [h]
  simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Bilinear form of a basis-diagonal operator. -/
theorem inner_apply_diag (b : OrthonormalBasis ι ℂ V) (M : V →L[ℂ] V) (f : ι → ℂ)
    (hM : ∀ i, M (b i) = f i • b i) (y w : V) :
    inner ℂ y (M w) = ∑ i, conj (inner ℂ (b i) y) * (f i * inner ℂ (b i) w) := by
  rw [← b.sum_inner_mul_inner y (M w)]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_basis_apply b M f hM i w, ← inner_conj_symm y (b i)]

/-- Quadratic form of a basis-diagonal operator with real diagonal entries. -/
theorem inner_self_apply_diag (b : OrthonormalBasis ι ℂ V) (M : V →L[ℂ] V) (f : ι → ℝ)
    (hM : ∀ i, M (b i) = (f i : ℂ) • b i) (w : V) :
    inner ℂ w (M w) = ((∑ i, f i * ‖inner ℂ (b i) w‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_apply_diag b M (fun i => (f i : ℂ)) hM w w]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm, Complex.conj_mul']

/-- Real part of the quadratic form of a real basis-diagonal operator. -/
theorem re_inner_self_apply_diag (b : OrthonormalBasis ι ℂ V) (M : V →L[ℂ] V) (f : ι → ℝ)
    (hM : ∀ i, M (b i) = (f i : ℂ) • b i) (w : V) :
    (inner ℂ w (M w)).re = ∑ i, f i * ‖inner ℂ (b i) w‖ ^ 2 := by
  rw [inner_self_apply_diag b M f hM w, Complex.ofReal_re]

/-- A basis-diagonal operator with real entries is self-adjoint. -/
theorem adjoint_eq_of_diag_real [CompleteSpace V] (b : OrthonormalBasis ι ℂ V)
    (M : V →L[ℂ] V) (f : ι → ℝ) (hM : ∀ i, M (b i) = (f i : ℂ) • b i) : M† = M := by
  ext a
  apply ext_inner_left ℂ
  intro c
  rw [adjoint_inner_right, ← inner_conj_symm, inner_apply_diag b M _ hM a c,
    inner_apply_diag b M _ hM c a, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

omit [DecidableEq ι] in
/-- Parseval in the form used below. -/
theorem norm_sq_eq_sum (b : OrthonormalBasis ι ℂ V) (w : V) :
    ‖w‖ ^ 2 = ∑ i, ‖inner ℂ (b i) w‖ ^ 2 :=
  (b.sum_sq_norm_inner_right w).symm

end Basis

section Inverse

variable [FiniteDimensional ℂ V]

/-- The continuous two-sided inverse of an injective endomorphism. -/
def inverseOfInjective (T : V →L[ℂ] V) (hT : Function.Injective T) : V →L[ℂ] V :=
  (LinearEquiv.ofInjectiveEndo (T : V →ₗ[ℂ] V) hT).symm.toLinearMap.toContinuousLinearMap

theorem mul_inverseOfInjective (T : V →L[ℂ] V) (hT : Function.Injective T) :
    T * inverseOfInjective T hT = 1 := by
  ext x
  change (LinearEquiv.ofInjectiveEndo (T : V →ₗ[ℂ] V) hT)
    ((LinearEquiv.ofInjectiveEndo (T : V →ₗ[ℂ] V) hT).symm x) = x
  exact LinearEquiv.apply_symm_apply _ x

theorem inverseOfInjective_mul (T : V →L[ℂ] V) (hT : Function.Injective T) :
    inverseOfInjective T hT * T = 1 := by
  ext x
  change (LinearEquiv.ofInjectiveEndo (T : V →ₗ[ℂ] V) hT).symm
    ((LinearEquiv.ofInjectiveEndo (T : V →ₗ[ℂ] V) hT) x) = x
  exact LinearEquiv.symm_apply_apply _ x

theorem apply_inverseOfInjective (T : V →L[ℂ] V) (hT : Function.Injective T) (x : V) :
    T (inverseOfInjective T hT x) = x := by
  have h := congrArg (fun A : V →L[ℂ] V => A x) (mul_inverseOfInjective T hT)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

theorem inverseOfInjective_apply (T : V →L[ℂ] V) (hT : Function.Injective T) (x : V) :
    inverseOfInjective T hT (T x) = x := by
  have h := congrArg (fun A : V →L[ℂ] V => A x) (inverseOfInjective_mul T hT)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using h

omit [FiniteDimensional ℂ V] in
/-- A two-sided inverse is unique. -/
theorem inverse_unique (T S S' : V →L[ℂ] V) (hS : S * T = 1) (hS' : T * S' = 1) :
    S = S' := by
  calc S = S * (T * S') := by rw [hS', mul_one]
    _ = (S * T) * S' := by rw [mul_assoc]
    _ = S' := by rw [hS, one_mul]

end Inverse

section Symmetric

variable [FiniteDimensional ℂ V] [CompleteSpace V]

omit [FiniteDimensional ℂ V] in
/-- Self-adjoint continuous operators are symmetric linear maps. -/
theorem isSymmetric_of_adjoint_eq {K : V →L[ℂ] V} (hK : K† = K) :
    (K : V →ₗ[ℂ] V).IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  rw [IsSelfAdjoint, star_eq_adjoint, hK]

/-- Abbreviation for the eigenvector basis of a self-adjoint operator. -/
abbrev eigenBasis (K : V →L[ℂ] V) (hK : K† = K) :
    OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V :=
  (isSymmetric_of_adjoint_eq hK).eigenvectorBasis rfl

/-- The corresponding real eigenvalues. -/
abbrev eigenValues (K : V →L[ℂ] V) (hK : K† = K) : Fin (Module.finrank ℂ V) → ℝ :=
  (isSymmetric_of_adjoint_eq hK).eigenvalues rfl

theorem apply_eigenBasis (K : V →L[ℂ] V) (hK : K† = K) (i : Fin (Module.finrank ℂ V)) :
    K (eigenBasis K hK i) = (eigenValues K hK i : ℂ) • eigenBasis K hK i :=
  (isSymmetric_of_adjoint_eq hK).apply_eigenvectorBasis rfl i

theorem eigenBasis_ne_zero (K : V →L[ℂ] V) (hK : K† = K) (i : Fin (Module.finrank ℂ V)) :
    eigenBasis K hK i ≠ 0 :=
  (eigenBasis K hK).orthonormal.ne_zero i

/-- An operator bound controls every eigenvalue. -/
theorem abs_eigenValues_le (K : V →L[ℂ] V) (hK : K† = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (i : Fin (Module.finrank ℂ V)) :
    |eigenValues K hK i| ≤ k₀ := by
  have h := hk (eigenBasis K hK i)
  rw [apply_eigenBasis, norm_smul, (eigenBasis K hK).orthonormal.1 i, mul_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end Symmetric

section Inertia

variable [FiniteDimensional ℂ V] [CompleteSpace V]

/-- **Inertia lemma.**  A self-adjoint operator whose nonzero eigenvalues have
modulus at least `d`, perturbed by a strictly positive self-adjoint operator
whose quadratic form is at most `q < d`, has trivial kernel. -/
theorem inertia_injective (B Δ : V →L[ℂ] V) (hB : B† = B) (hΔ : Δ† = Δ) (d q : ℝ)
    (hgap : ∀ (x : V) (c : ℂ), x ≠ 0 → B x = c • x → c ≠ 0 → d ≤ ‖c‖)
    (hpos : ∀ x : V, x ≠ 0 → 0 < (inner ℂ x (Δ x)).re)
    (hupper : ∀ x : V, (inner ℂ x (Δ x)).re ≤ q * ‖x‖ ^ 2)
    (hqd : q < d) (x : V) (hx : (B + Δ) x = 0) : x = 0 := by
  classical
  set e := eigenBasis B hB with he_def
  set lam := eigenValues B hB with hlam_def
  have he : ∀ i, B (e i) = (lam i : ℂ) • e i := apply_eigenBasis B hB
  -- negative eigenvalues are at most `-d`
  have hneg : ∀ i, lam i < 0 → lam i ≤ -d := by
    intro i hi
    have h := hgap (e i) (lam i : ℂ) (eigenBasis_ne_zero B hB i) (he i)
      (by exact_mod_cast hi.ne)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hi] at h
    linarith
  -- spectral split
  set xm : V := ∑ i, (if lam i < 0 then inner ℂ (e i) x else 0) • e i with hxm_def
  set xp : V := x - xm with hxp_def
  have coord_m : ∀ j, inner ℂ (e j) xm = if lam j < 0 then inner ℂ (e j) x else 0 := by
    intro j
    rw [hxm_def, inner_sum]
    have hterm : ∀ i, inner ℂ (e j) ((if lam i < 0 then inner ℂ (e i) x else 0) • e i) =
        if j = i then (if lam j < 0 then inner ℂ (e j) x else 0) else 0 := by
      intro i
      rw [inner_smul_right, orthonormal_iff_ite.mp e.orthonormal j i]
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    simp only [hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have coord_p : ∀ j, inner ℂ (e j) xp = if lam j < 0 then 0 else inner ℂ (e j) x := by
    intro j
    rw [hxp_def, inner_sub_right, coord_m j]
    split_ifs <;> simp
  have hsplit : x = xp + xm := by rw [hxp_def]; abel
  -- quadratic and cross terms of `B`
  have hBdiag : ∀ y w : V, inner ℂ y (B w) =
      ∑ i, conj (inner ℂ (e i) y) * ((lam i : ℂ) * inner ℂ (e i) w) :=
    fun y w => inner_apply_diag e B (fun i => (lam i : ℂ)) he y w
  have cross1 : inner ℂ xp (B xm) = 0 := by
    rw [hBdiag]
    apply Finset.sum_eq_zero
    intro i _
    rw [coord_p i, coord_m i]
    split_ifs <;> simp
  have cross2 : inner ℂ xm (B xp) = 0 := by
    rw [hBdiag]
    apply Finset.sum_eq_zero
    intro i _
    rw [coord_p i, coord_m i]
    split_ifs <;> simp
  have quad_m : (inner ℂ xm (B xm)).re ≤ -d * ‖xm‖ ^ 2 := by
    rw [re_inner_self_apply_diag e B lam he xm, norm_sq_eq_sum e xm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [coord_m i]
    by_cases hi : lam i < 0
    · simp only [hi, if_true]
      exact mul_le_mul_of_nonneg_right (hneg i hi) (sq_nonneg _)
    · simp [hi]
  have quad_p : 0 ≤ (inner ℂ xp (B xp)).re := by
    rw [re_inner_self_apply_diag e B lam he xp]
    apply Finset.sum_nonneg
    intro i _
    rw [coord_p i]
    by_cases hi : lam i < 0
    · simp [hi]
    · simp only [hi, if_false]
      exact mul_nonneg (not_lt.mp hi) (sq_nonneg _)
  -- the two projected equations
  have hBx : B x + Δ x = 0 := by simpa only [add_apply] using hx
  have eqp : inner ℂ xp (B x + Δ x) = 0 := by rw [hBx, inner_zero_right]
  have eqm : inner ℂ xm (B x + Δ x) = 0 := by rw [hBx, inner_zero_right]
  rw [hsplit, map_add, map_add, inner_add_right, inner_add_right, inner_add_right,
    cross1] at eqp
  rw [hsplit, map_add, map_add, inner_add_right, inner_add_right, inner_add_right,
    cross2] at eqm
  -- self-adjointness of `Δ` relates the two cross terms
  have hΔcross : inner ℂ xm (Δ xp) = conj (inner ℂ xp (Δ xm)) := by
    calc inner ℂ xm (Δ xp) = conj (inner ℂ (Δ xp) xm) := (inner_conj_symm _ _).symm
      _ = conj (inner ℂ xp ((Δ†) xm)) := by rw [adjoint_inner_right]
      _ = conj (inner ℂ xp (Δ xm)) := by rw [hΔ]
  have rep := congrArg Complex.re eqp
  have rem := congrArg Complex.re eqm
  simp only [Complex.add_re, Complex.zero_re, zero_add, add_zero] at rep rem
  rw [hΔcross, Complex.conj_re] at rem
  -- from the positive part: Re c ≤ -⟪xp, Δ xp⟫ ≤ 0
  -- from the negative part: Re c ≥ (d - q) ‖xm‖²
  have hm_up := hupper xm
  have hxm0 : xm = 0 := by
    by_contra hne
    have hpos' : 0 < ‖xm‖ ^ 2 := by
      have : 0 < ‖xm‖ := norm_pos_iff.mpr hne
      positivity
    have hpp : 0 ≤ (inner ℂ xp (Δ xp)).re := by
      by_cases hxp : xp = 0
      · simp [hxp]
      · exact (hpos xp hxp).le
    nlinarith
  have hxp0 : xp = 0 := by
    by_contra hne
    have hpp := hpos xp hne
    have hxm' : (inner ℂ xp (Δ xm)).re = 0 := by simp [hxm0]
    linarith
  rw [hsplit, hxp0, hxm0, add_zero]

/-- The same conclusion for a strictly negative perturbation. -/
theorem inertia_injective_neg (B Δ : V →L[ℂ] V) (hB : B† = B) (hΔ : Δ† = Δ) (d q : ℝ)
    (hgap : ∀ (x : V) (c : ℂ), x ≠ 0 → B x = c • x → c ≠ 0 → d ≤ ‖c‖)
    (hneg : ∀ x : V, x ≠ 0 → (inner ℂ x (Δ x)).re < 0)
    (hlower : ∀ x : V, -(q * ‖x‖ ^ 2) ≤ (inner ℂ x (Δ x)).re)
    (hqd : q < d) (x : V) (hx : (B + Δ) x = 0) : x = 0 := by
  apply inertia_injective (-B) (-Δ) (by rw [map_neg, hB]) (by rw [map_neg, hΔ]) d q
  · intro y c hy hyc hc
    have h := hgap y (-c) hy (by
      have := congrArg Neg.neg hyc
      simpa [neg_smul] using this) (neg_ne_zero.mpr hc)
    simpa [norm_neg] using h
  · intro y hy
    have := hneg y hy
    simp only [neg_apply, inner_neg_right, Complex.neg_re]
    linarith
  · intro y
    have := hlower y
    simp only [neg_apply, inner_neg_right, Complex.neg_re]
    linarith
  · exact hqd
  · have h' : B x + Δ x = 0 := by simpa only [add_apply] using hx
    simp only [add_apply, neg_apply]
    rw [← neg_add, h', neg_zero]

end Inertia

end
end SparseLinearSystems.Diagonal

namespace SparseLinearSystems

/-- Extensionality for `L²` products through the two coordinate projections. -/
theorem prodExt {α β : Type*} [AddCommGroup α] [AddCommGroup β] {x y : WithLp 2 (α × β)}
    (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h1 h2)

end SparseLinearSystems
