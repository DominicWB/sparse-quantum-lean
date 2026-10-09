import SparseLinearSystems.Spectral.Diagonal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Averaging filters for unitary operators (Remark `qls:rem:averaging`)

Let `W` be unitary on a finite-dimensional complex Hilbert space, and let `P`
be the orthogonal projection onto its eigenvalue-one space.  Suppose every
eigenvalue `z ≠ 1` of `W` satisfies `|z - 1| ≥ 2b`, i.e. `|sin(θ/2)| ≥ b`.
For the averaging filter `f_N(W) = N⁻¹ ∑_{j<N} W^j` and its `k`th power,

* `filter_fixed`: `f_N(W)^k u = u` for every fixed vector `u`;
* `filter_sub_proj_le`: `‖(f_N(W)^k - P) x‖ ≤ (N b)^{-k} ‖x‖`;
* `filter_norm_sq`: `‖f_N(W)^k x‖² = ‖P x‖² + ‖(f_N(W)^k - P) x‖²`
  (equation `qls:eq:filterprobability`).

The lower bound `‖(W - 1) y‖ ≥ 2b ‖y‖` on the orthogonal complement of the
fixed space is proved from the spectral theorem for the self-adjoint operator
`(W - 1)†(W - 1)`: every nonzero eigenvalue of this operator equals
`|z - 1|²` for an eigenvalue `z ≠ 1` of `W`.
-/

namespace SparseLinearSystems.UnitaryFilter

noncomputable section
open ContinuousLinearMap Diagonal
open scoped InnerProduct ComplexConjugate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]

/-- Two-sided unitarity in operator-algebra form. -/
structure Unitary (W : V →L[ℂ] V) : Prop where
  left : star W * W = 1
  right : W * star W = 1

variable {W : V →L[ℂ] V}

omit [FiniteDimensional ℂ V] in
theorem Unitary.adjoint_comp_self (hW : Unitary W) : (W†) ∘L W = 1 := by
  rw [← mul_def, ← star_eq_adjoint]; exact hW.left

omit [FiniteDimensional ℂ V] in
theorem Unitary.comp_adjoint_self (hW : Unitary W) : W ∘L (W†) = 1 := by
  rw [← mul_def, ← star_eq_adjoint]; exact hW.right

omit [FiniteDimensional ℂ V] in
theorem Unitary.norm_apply (hW : Unitary W) (v : V) : ‖W v‖ = ‖v‖ :=
  (W.norm_map_iff_adjoint_comp_self.mpr hW.adjoint_comp_self) v

omit [FiniteDimensional ℂ V] in
theorem Unitary.adjoint_apply_apply (hW : Unitary W) (v : V) : (W†) (W v) = v := by
  have h := congrArg (fun A : V →L[ℂ] V => A v) hW.adjoint_comp_self
  simpa only [comp_apply, one_apply_eq_self] using h

omit [FiniteDimensional ℂ V] in
theorem Unitary.apply_adjoint_apply (hW : Unitary W) (v : V) : W ((W†) v) = v := by
  have h := congrArg (fun A : V →L[ℂ] V => A v) hW.comp_adjoint_self
  simpa only [comp_apply, one_apply_eq_self] using h

omit [FiniteDimensional ℂ V] in
theorem Unitary.pow (hW : Unitary W) (k : ℕ) : Unitary (W ^ k) := by
  induction k with
  | zero => exact ⟨by simp, by simp⟩
  | succ k ih =>
    constructor
    · rw [pow_succ', star_mul, mul_assoc, ← mul_assoc (star W) W, hW.left, one_mul]
      exact ih.left
    · rw [pow_succ, star_mul, mul_assoc, ← mul_assoc W (star W), hW.right, one_mul]
      exact ih.right

omit [FiniteDimensional ℂ V] in
theorem Unitary.norm_eigenvalue (hW : Unitary W) {z : ℂ} {v : V} (hv : v ≠ 0)
    (hWv : W v = z • v) : ‖z‖ = 1 := by
  have hn := hW.norm_apply v
  rw [hWv, norm_smul] at hn
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  calc ‖z‖ = ‖z‖ * ‖v‖ / ‖v‖ := by field_simp
    _ = 1 := by rw [hn, div_self hv']

omit [FiniteDimensional ℂ V] in
theorem Unitary.adjoint_eigen (hW : Unitary W) {z : ℂ} {v : V} (hv : v ≠ 0)
    (hWv : W v = z • v) : (W†) v = conj z • v := by
  have hz := hW.norm_eigenvalue hv hWv
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hz; exact zero_ne_one hz
  have h1 : z • (W†) v = v := by
    rw [← map_smul, ← hWv, hW.adjoint_apply_apply]
  have hconj : conj z * z = 1 := by
    rw [RCLike.conj_mul, hz]; simp
  calc (W†) v = (conj z * z) • (W†) v := by rw [hconj, one_smul]
    _ = conj z • v := by rw [mul_smul, h1]

/-! ### The fixed space -/

/-- The eigenvalue-one space `ker (W - 1)`. -/
def fixedSpace (W : V →L[ℂ] V) : Submodule ℂ V :=
  LinearMap.ker ((W - 1 : V →L[ℂ] V) : V →ₗ[ℂ] V)

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem mem_fixedSpace {v : V} : v ∈ fixedSpace W ↔ W v = v := by
  rw [fixedSpace, LinearMap.mem_ker]
  change (W - 1) v = 0 ↔ W v = v
  rw [sub_apply, one_apply_eq_self, sub_eq_zero]

/-- The orthogonal projection onto the fixed space. -/
abbrev fixedProj (W : V →L[ℂ] V) : V →L[ℂ] V := (fixedSpace W).starProjection

omit [FiniteDimensional ℂ V] in
theorem Unitary.adjoint_fixed (hW : Unitary W) {u : V} (hu : W u = u) : (W†) u = u := by
  conv_rhs => rw [← hW.adjoint_apply_apply u]
  rw [hu]

omit [FiniteDimensional ℂ V] in
/-- The orthogonal complement of the fixed space is invariant. -/
theorem Unitary.orth_invariant (hW : Unitary W) {y : V} (hy : y ∈ (fixedSpace W)ᗮ) :
    W y ∈ (fixedSpace W)ᗮ := by
  rw [Submodule.mem_orthogonal] at hy ⊢
  intro u hu
  rw [← adjoint_inner_left, hW.adjoint_fixed (mem_fixedSpace.mp hu)]
  exact hy u hu

/-! ### The spectral lower bound -/

/-- `T = (W - 1)†(W - 1)`. -/
def defect (W : V →L[ℂ] V) : V →L[ℂ] V := ((W - 1)†) ∘L (W - 1)

omit [FiniteDimensional ℂ V] in
theorem defect_adjoint (W : V →L[ℂ] V) : ((defect W)†) = defect W := by
  rw [defect, adjoint_comp, adjoint_adjoint]

omit [FiniteDimensional ℂ V] in
theorem re_inner_defect (W : V →L[ℂ] V) (y : V) :
    (inner ℂ y (defect W y)).re = ‖W y - y‖ ^ 2 := by
  rw [defect, comp_apply, adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp only [sub_apply, one_apply_eq_self]
  norm_cast

omit [FiniteDimensional ℂ V] in
theorem adjoint_one_apply' (y : V) : ((1 : V →L[ℂ] V)†) y = y := by
  have : ((1 : V →L[ℂ] V)†) = 1 := by rw [← star_eq_adjoint, star_one]
  rw [this, one_apply_eq_self]

omit [FiniteDimensional ℂ V] in
theorem Unitary.defect_eq (hW : Unitary W) :
    defect W = (2 : ℂ) • (1 : V →L[ℂ] V) - (W†) - W := by
  ext y
  simp only [defect, comp_apply, sub_apply, one_apply_eq_self, smul_apply, map_sub,
    hW.adjoint_apply_apply, adjoint_one_apply']
  module

omit [FiniteDimensional ℂ V] in
theorem Unitary.defect_commute (hW : Unitary W) (y : V) :
    defect W (W y) = W (defect W y) := by
  rw [hW.defect_eq]
  simp only [sub_apply, smul_apply, one_apply_eq_self, map_sub, map_smul,
    hW.adjoint_apply_apply, hW.apply_adjoint_apply]

/-- Every nonzero eigenvalue of the defect operator is at least `4 b²`. -/
theorem Unitary.defect_eigen_lower (hW : Unitary W) (b : ℝ)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (hb : 0 ≤ b) (i : Fin (Module.finrank ℂ V))
    (hti : eigenValues (defect W) (defect_adjoint W) i ≠ 0) :
    4 * b ^ 2 ≤ eigenValues (defect W) (defect_adjoint W) i := by
  set t := eigenValues (defect W) (defect_adjoint W) i with ht
  set E := Module.End.eigenspace ((defect W : V →L[ℂ] V) : V →ₗ[ℂ] V) (t : ℂ) with hE
  have heE : eigenBasis (defect W) (defect_adjoint W) i ∈ E := by
    rw [hE, Module.End.mem_eigenspace_iff]
    exact apply_eigenBasis _ _ i
  have hWE : ∀ x ∈ E, (W : V →ₗ[ℂ] V) x ∈ E := by
    intro x hx
    rw [hE, Module.End.mem_eigenspace_iff] at hx ⊢
    change defect W (W x) = (t : ℂ) • W x
    rw [hW.defect_commute, show defect W x = (t : ℂ) • x from hx, map_smul]
  haveI : Nontrivial E :=
    ⟨⟨⟨_, heE⟩, 0, fun h => eigenBasis_ne_zero _ _ i (congrArg Subtype.val h)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((W : V →ₗ[ℂ] V).restrict hWE)
  obtain ⟨⟨v, hvE⟩, hv⟩ := hc.exists_hasEigenvector
  have hv0 : v ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hWv : W v = c • v := by
    have h1 := Module.End.mem_eigenspace_iff.mp hv.1
    have h2 := congrArg Subtype.val h1
    simpa only [LinearMap.restrict_apply, Submodule.coe_smul, ContinuousLinearMap.coe_coe]
      using h2
  have hTv : defect W v = (t : ℂ) • v := by
    have := Module.End.mem_eigenspace_iff.mp hvE
    exact this
  have hc1 := hW.norm_eigenvalue hv0 hWv
  -- compute the defect on `v`
  have hTv' : defect W v = ((‖c - 1‖ ^ 2 : ℝ) : ℂ) • v := by
    rw [hW.defect_eq]
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    rw [hW.adjoint_eigen hv0 hWv, hWv]
    have hnorm : ((‖c - 1‖ ^ 2 : ℝ) : ℂ) = 2 - conj c - c := by
      have e1 : ((‖c - 1‖ ^ 2 : ℝ) : ℂ) = conj (c - 1) * (c - 1) := by
        rw [Complex.conj_mul']; norm_cast
      have e2 : conj c * c = 1 := by rw [Complex.conj_mul', hc1]; simp
      rw [e1, map_sub, map_one]
      linear_combination e2
    rw [hnorm]
    module
  have htc : t = ‖c - 1‖ ^ 2 := by
    have h := hTv.symm.trans hTv'
    have h2 : ((t : ℂ) - ((‖c - 1‖ ^ 2 : ℝ) : ℂ)) • v = 0 := by rw [sub_smul, h, sub_self]
    have h3 := (smul_eq_zero.mp h2).resolve_right hv0
    exact_mod_cast sub_eq_zero.mp h3
  have hc_ne : c ≠ 1 := by
    intro hc'
    apply hti
    rw [htc, hc', sub_self, norm_zero]; ring
  have hg := hgap c v hv0 hWv hc_ne
  rw [htc]
  nlinarith [norm_nonneg (c - 1)]

/-- The spectral lower bound `‖(W - 1) y‖ ≥ 2b ‖y‖` on the complement of the
fixed space. -/
theorem Unitary.lower_bound (hW : Unitary W) (b : ℝ) (hb : 0 ≤ b)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    {y : V} (hy : y ∈ (fixedSpace W)ᗮ) : 2 * b * ‖y‖ ≤ ‖W y - y‖ := by
  set e := eigenBasis (defect W) (defect_adjoint W)
  set t := eigenValues (defect W) (defect_adjoint W)
  have he : ∀ i, defect W (e i) = (t i : ℂ) • e i := apply_eigenBasis _ _
  have htnn : ∀ i, 0 ≤ t i := by
    intro i
    have h := re_inner_defect W (e i)
    rw [he i, inner_smul_right, inner_self_eq_norm_sq_to_K, e.orthonormal.1 i] at h
    have h' : t i = ‖W (e i) - e i‖ ^ 2 := by simpa using h
    rw [h']; positivity
  have hzero : ∀ i, t i = 0 → inner ℂ (e i) y = 0 := by
    intro i hti
    have hfix : e i ∈ fixedSpace W := by
      rw [mem_fixedSpace]
      have h := re_inner_defect W (e i)
      rw [he i, hti] at h
      have h0 : ‖W (e i) - e i‖ ^ 2 = 0 := by simpa using h.symm
      have : ‖W (e i) - e i‖ = 0 := by nlinarith [norm_nonneg (W (e i) - e i)]
      exact sub_eq_zero.mp (norm_eq_zero.mp this)
    exact (Submodule.mem_orthogonal _ _).mp hy _ hfix
  have hsq : 4 * b ^ 2 * ‖y‖ ^ 2 ≤ ‖W y - y‖ ^ 2 := by
    rw [← re_inner_defect W y, re_inner_self_apply_diag e (defect W) t he y,
      norm_sq_eq_sum e y, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hti : t i = 0
    · rw [hzero i hti, norm_zero]; simp
    · exact mul_le_mul_of_nonneg_right (hW.defect_eigen_lower b hgap hb i hti) (sq_nonneg _)
  have h2 : (2 * b * ‖y‖) ^ 2 ≤ ‖W y - y‖ ^ 2 := by nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h2

/-! ### The averaging filter -/

/-- `f_N(W) = N⁻¹ ∑_{j<N} W^j`. -/
def avg (W : V →L[ℂ] V) (N : ℕ) : V →L[ℂ] V :=
  ((N : ℂ)⁻¹) • ∑ j ∈ Finset.range N, W ^ j

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem avg_fixed {u : V} (hu : W u = u) (N : ℕ) (hN : 0 < N) : avg W N u = u := by
  have hpow : ∀ j : ℕ, (W ^ j) u = u := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_apply_eq_comp, hu, ih]
  simp only [avg, smul_apply, sum_apply, hpow, Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN.ne'),
    one_smul]

omit [FiniteDimensional ℂ V] in
theorem avg_orth (hW : Unitary W) (N : ℕ) {y : V} (hy : y ∈ (fixedSpace W)ᗮ) :
    avg W N y ∈ (fixedSpace W)ᗮ := by
  have hpow : ∀ j : ℕ, (W ^ j) y ∈ (fixedSpace W)ᗮ := by
    intro j
    induction j with
    | zero => simpa using hy
    | succ j ih => rw [pow_succ', mul_apply_eq_comp]; exact hW.orth_invariant ih
  simp only [avg, smul_apply, sum_apply]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => hpow j)

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem sub_one_avg (W : V →L[ℂ] V) (N : ℕ) (y : V) :
    W (avg W N y) - avg W N y = ((N : ℂ)⁻¹) • ((W ^ N) y - y) := by
  have h := mul_geom_sum W N
  have h2 := congrArg (fun A : V →L[ℂ] V => ((N : ℂ)⁻¹) • A y) h
  simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at h2
  rw [← h2]
  simp only [avg, smul_apply, map_smul, smul_sub]

/-- One averaging filter contracts the complement by `1/(N b)`. -/
theorem avg_bound (hW : Unitary W) (b : ℝ) (hb : 0 < b)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (N : ℕ) (hN : 0 < N) {y : V} (hy : y ∈ (fixedSpace W)ᗮ) :
    ‖avg W N y‖ ≤ ‖y‖ / (N * b) := by
  have hlow := hW.lower_bound b hb.le hgap (avg_orth hW N hy)
  rw [sub_one_avg, norm_smul, norm_inv, Complex.norm_natCast] at hlow
  have hpow := (hW.pow N).norm_apply y
  have htri : ‖(W ^ N) y - y‖ ≤ 2 * ‖y‖ := by
    have := norm_sub_le ((W ^ N) y) y
    rw [hpow] at this; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 2 * b * ‖avg W N y‖ ≤ (N : ℝ)⁻¹ * (2 * ‖y‖) :=
    hlow.trans (mul_le_mul_of_nonneg_left htri (by positivity))
  have h1' : 2 * b * ‖avg W N y‖ ≤ 2 * ‖y‖ / N := by
    rw [div_eq_inv_mul]; exact h1
  have h2 := (le_div_iff₀ hNpos).mp h1'
  rw [le_div_iff₀ (by positivity)]
  nlinarith [h2]

/-- The `k`-fold averaging filter. -/
def filter (W : V →L[ℂ] V) (N k : ℕ) : V →L[ℂ] V := avg W N ^ k

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem filter_fixed {u : V} (hu : W u = u) (N k : ℕ) (hN : 0 < N) :
    filter W N k u = u := by
  induction k with
  | zero => simp [filter]
  | succ k ih => rw [filter, pow_succ, mul_apply_eq_comp, avg_fixed hu N hN, ← filter, ih]

theorem filter_orth (hW : Unitary W) (b : ℝ) (hb : 0 < b)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (N : ℕ) (hN : 0 < N) (k : ℕ) {y : V} (hy : y ∈ (fixedSpace W)ᗮ) :
    filter W N k y ∈ (fixedSpace W)ᗮ ∧ ‖filter W N k y‖ ≤ (1 / (N * b)) ^ k * ‖y‖ := by
  induction k with
  | zero => simp [filter, hy]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨?_, ?_⟩
    · rw [filter, pow_succ', mul_apply_eq_comp, ← filter]; exact avg_orth hW N h1
    · rw [filter, pow_succ', mul_apply_eq_comp, ← filter]
      calc ‖avg W N (filter W N k y)‖ ≤ ‖filter W N k y‖ / (N * b) :=
            avg_bound hW b hb hgap N hN h1
        _ ≤ (1 / (N * b)) ^ k * ‖y‖ / (N * b) :=
            div_le_div_of_nonneg_right h2 (by positivity)
        _ = (1 / (N * b)) ^ (k + 1) * ‖y‖ := by rw [pow_succ]; ring

/-- **Remark `qls:rem:averaging`.**  `‖(f_N(W)^k - P) x‖ ≤ (N b)^{-k} ‖x‖`. -/
theorem filter_sub_proj_le (hW : Unitary W) (b : ℝ) (hb : 0 < b)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (N : ℕ) (hN : 0 < N) (k : ℕ) (x : V) :
    ‖filter W N k x - fixedProj W x‖ ≤ (1 / (N * b)) ^ k * ‖x‖ := by
  set p := fixedProj W x with hp
  have hpmem : p ∈ fixedSpace W := Submodule.starProjection_apply_mem _ x
  have horth : x - p ∈ (fixedSpace W)ᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hsplit : filter W N k x - p = filter W N k (x - p) := by
    rw [map_sub, filter_fixed (mem_fixedSpace.mp hpmem) N k hN]
  rw [hsplit]
  have h := (filter_orth hW b hb hgap N hN k horth).2
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  -- `‖x - P x‖ ≤ ‖x‖`
  have hinner : inner ℂ p (x - p) = 0 := (Submodule.mem_orthogonal _ _).mp horth p hpmem
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p (x - p) hinner
  have hx : p + (x - p) = x := by abel
  rw [hx] at hpyth
  apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg x)
  nlinarith [norm_nonneg p]

/-- Spectral orthogonality, equation `qls:eq:filterprobability`. -/
theorem filter_norm_sq (hW : Unitary W) (b : ℝ) (hb : 0 < b)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (N : ℕ) (hN : 0 < N) (k : ℕ) (x : V) :
    ‖filter W N k x‖ ^ 2 = ‖fixedProj W x‖ ^ 2 + ‖filter W N k x - fixedProj W x‖ ^ 2 := by
  set p := fixedProj W x with hp
  have hpmem : p ∈ fixedSpace W := Submodule.starProjection_apply_mem _ x
  have horth : x - p ∈ (fixedSpace W)ᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hF : filter W N k x = p + filter W N k (x - p) := by
    rw [map_sub, filter_fixed (mem_fixedSpace.mp hpmem) N k hN]; abel
  have hq := (filter_orth hW b hb hgap N hN k horth).1
  have hinner : inner ℂ p (filter W N k (x - p)) = 0 :=
    (Submodule.mem_orthogonal _ _).mp hq p hpmem
  have hsub : filter W N k x - p = filter W N k (x - p) := by rw [hF]; abel
  rw [hsub, hF]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero p
    (filter W N k (x - p)) hinner
  nlinarith [this]

end

end SparseLinearSystems.UnitaryFilter
