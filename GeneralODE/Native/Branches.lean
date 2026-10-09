import GeneralODE.Native.LCU
import GeneralODE.Native.Matrix
import SparseHamiltonian.LabeledAdjointSimulation

/-!
# The branch table of Lemma `ode:lem:block`

Branches `(σ, k, r)` carry the Fourier term `e^{i(2k+1-2r) X_σ}` of the arcsine
LCU for `X_± = K_±/(4Λ)`, with coefficient `(2√2)⁻¹ w_σ c_{k,r}` where
`w_+ = -(1+i)/2`, `w_- = (1-i)/2`.  Two extra branches carry cancelling
identity terms `±p` that make the coefficient one-norm exactly one.  The
branch evolutions are `e^{-i s K}` with signed durations
`s = -(2k+1-2r)/(4Λ)`, and zero on the padding.  Their combination is within
`4^{-N}/2` of `A/(8√2 Λ)`.
-/

namespace SparseHamiltonian.GeneralODE.NativeBlock

noncomputable section
open ContinuousLinearMap ODEMatrixEnergy SparseStateOverlap Arcsine FractionalAngleCoefficients
open scoped BigOperators InnerProduct ComplexConjugate

/-- Branch labels. -/
abbrev Branch (N : ℕ) := (Bool × (Fin N × Fin (2 * N))) ⊕ Bool

/-- The LCHS parameter of each branch: `K_+` for `σ = true`, `K_-` otherwise. -/
def kTab (N : ℕ) : Branch N → ℝ
  | .inl (σ, _) => if σ then 1 else -1
  | .inr _ => 1

/-- Signed durations. -/
def sTab (N : ℕ) (Λ : ℝ) : Branch N → ℝ
  | .inl (_, kr) => -(freq kr.1 kr.2 : ℝ) / (4 * Λ)
  | .inr _ => 0

theorem abs_kTab_le (N : ℕ) (i : Branch N) : |kTab N i| ≤ 1 := by
  rcases i with ⟨σ, _⟩ | b
  · cases σ <;> simp [kTab]
  · simp [kTab]

theorem abs_freq_le (N : ℕ) (k : Fin N) (r : Fin (2 * N)) : |(freq k r : ℝ)| ≤ 4 * N := by
  unfold freq
  have hk := k.isLt
  have hr := r.isLt
  push_cast
  rw [abs_le]
  have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hr' : (r : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hr
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  constructor <;> linarith

theorem abs_sTab_le (N : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (i : Branch N) :
    |sTab N Λ i| ≤ N / Λ := by
  rcases i with ⟨σ, k, r⟩ | b
  · simp only [sTab]
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 * Λ), div_le_div_iff₀
      (by positivity) hΛ]
    have := abs_freq_le N k r
    nlinarith
  · simp only [sTab, abs_zero]
    positivity

/-- The two phases of the decomposition `A = 4Λ (w_+ X_+ + w_- X_-)`. -/
def weight : Bool → ℂ
  | true => -(1 + Complex.I) / 2
  | false => (1 - Complex.I) / 2

theorem norm_weight (σ : Bool) : ‖weight σ‖ = Real.sqrt 2 / 2 := by
  have h : ∀ z : ℂ, z = 1 + Complex.I ∨ z = 1 - Complex.I → ‖z‖ = Real.sqrt 2 := by
    intro z hz
    rcases hz with rfl | rfl
    · rw [Complex.norm_eq_sqrt_sq_add_sq]; simp; norm_num
    · rw [Complex.norm_eq_sqrt_sq_add_sq]; simp; norm_num
  cases σ
  · simp only [weight]
    rw [norm_div, h _ (Or.inr rfl), Complex.norm_two]
  · simp only [weight]
    rw [norm_div, norm_neg, h _ (Or.inl rfl), Complex.norm_two]

/-- Half the arcsine coefficient mass. -/
def mass (N : ℕ) : ℝ := (1 / 2) * ∑ k ∈ Finset.range N, coefficient 0 k

theorem mass_nonneg (N : ℕ) : 0 ≤ mass N := by
  unfold mass
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => coefficient_zero_nonneg k))

theorem mass_le_one (N : ℕ) : mass N ≤ 1 := by
  unfold mass
  have := sum_coefficient_zero_le_two N
  linarith

/-- The padding weight. -/
def pad (N : ℕ) : ℝ := (1 - mass N) / 2

theorem pad_nonneg (N : ℕ) : 0 ≤ pad N := by
  unfold pad; linarith [mass_le_one N]

/-- LCU coefficients of the branches. -/
def coef (N : ℕ) : Branch N → ℂ
  | .inl (σ, kr) => (((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ * lcuCoef kr.1 kr.2
  | .inr b => (if b then 1 else -1) * (pad N : ℂ)

theorem sum_fin_prod {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → ℕ → M) :
    ∑ kr : Fin N × Fin (2 * N), f kr.1 kr.2 =
      ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range (2 * N), f k r := by
  rw [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ r ∈ Finset.range (2 * N), f k r) N]
  apply Finset.sum_congr rfl
  intro k _
  exact Fin.sum_univ_eq_sum_range (fun r => f k r) (2 * N)

/-- The coefficient one-norm is exactly one. -/
theorem sum_norm_coef (N : ℕ) : ∑ i, ‖coef N i‖ = 1 := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hpad := pad_nonneg N
  have hinl : ∀ σ : Bool, ∑ kr : Fin N × Fin (2 * N), ‖coef N (.inl (σ, kr))‖ = mass N / 2 := by
    intro σ
    have hterm : ∀ kr : Fin N × Fin (2 * N), ‖coef N (.inl (σ, kr))‖ =
        (2 * Real.sqrt 2)⁻¹ * (Real.sqrt 2 / 2) * ‖lcuCoef kr.1 kr.2‖ := by
      intro kr
      simp only [coef]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        norm_weight]
    simp only [hterm]
    rw [← Finset.mul_sum, sum_fin_prod N (fun k r => ‖lcuCoef k r‖), sum_norm_lcuCoef]
    unfold mass
    have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
  rw [Fintype.sum_bool, hinl true, hinl false]
  simp only [coef, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, one_mul, neg_one_mul,
    norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpad]
  unfold pad
  ring

variable {n : Type} [Fintype n] [DecidableEq n]

local notation "Op" => EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n

/-- The tagged Hamiltonian `K_k`. -/
def Kop (M : Matrix n n ℂ) (k : ℝ) : Op := matrixOperator (lchsHamiltonian M k)

omit [DecidableEq n] in
theorem Kop_star (M : Matrix n n ℂ) (k : ℝ) : star (Kop M k) = Kop M k :=
  SparseValuePrecision.matrixOperator_star_eq _ (lchsHamiltonian_isHermitian M k)

/-- `X_σ = K_σ / (4Λ)`. -/
def Xop (Λ : ℝ) (M : Matrix n n ℂ) (σ : Bool) : Op :=
  (((4 * Λ)⁻¹ : ℝ) : ℂ) • Kop M (if σ then 1 else -1)

omit [DecidableEq n] in
theorem Xop_selfAdjoint (Λ : ℝ) (M : Matrix n n ℂ) (σ : Bool) : IsSelfAdjoint (Xop Λ M σ) := by
  unfold Xop IsSelfAdjoint
  rw [star_smul, Kop_star, Complex.star_def, Complex.conj_ofReal]

omit [DecidableEq n] in
theorem norm_Xop_le (Λ : ℝ) (hΛ : 0 < Λ) (M : Matrix n n ℂ) (hM : ‖matrixOperator M‖ ≤ Λ)
    (σ : Bool) : ‖Xop Λ M σ‖ ≤ 1 / 2 := by
  unfold Xop Kop
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h := NativeMatrix.norm_lchs_le M (if σ then 1 else -1)
  have hk : |(if σ then (1 : ℝ) else -1)| = 1 := by cases σ <;> simp
  rw [hk] at h
  rw [inv_mul_le_iff₀ (by positivity)]
  linarith

/-- The branch evolutions `e^{-i s K}`. -/
def branchEvolution (N : ℕ) (Λ : ℝ) (M : Matrix n n ℂ) (i : Branch N) : Op :=
  NormedSpace.exp ((-Complex.I * (sTab N Λ i : ℂ)) • Kop M (kTab N i))

omit [DecidableEq n] in
theorem branchEvolution_inl (N : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (M : Matrix n n ℂ) (σ : Bool)
    (k : Fin N) (r : Fin (2 * N)) :
    branchEvolution N Λ M (.inl (σ, (k, r))) =
      NormedSpace.exp (((freq k r : ℂ) * Complex.I) • Xop Λ M σ) := by
  unfold branchEvolution Xop
  congr 1
  simp only [sTab, kTab]
  rw [smul_smul]
  congr 1
  have hΛ' : (Λ : ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  push_cast
  field_simp

omit [DecidableEq n] in
theorem branchEvolution_inr (N : ℕ) (Λ : ℝ) (M : Matrix n n ℂ) (b : Bool) :
    branchEvolution N Λ M (.inr b) = 1 := by
  unfold branchEvolution
  have h0 : (-Complex.I * ((sTab N Λ (.inr b) : ℝ) : ℂ)) • Kop M (kTab N (.inr b)) = 0 := by
    ext1 v; simp [sTab]
  rw [h0, NormedSpace.exp_zero]

omit [DecidableEq n] in
/-- The branch combination approximates `A/(8√2 Λ)` with `A = -M`. -/
theorem lcu_block_approx (N : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (M : Matrix n n ℂ)
    (hM : ‖matrixOperator M‖ ≤ Λ) :
    ‖∑ i, coef N i • branchEvolution N Λ M i -
        (((8 * Real.sqrt 2 * Λ)⁻¹ : ℝ) : ℂ) • (-matrixOperator M)‖ ≤ (1 / 4) ^ N / 2 := by
  have hs2 : 0 < Real.sqrt 2 := by positivity
  set L : Bool → Op := fun σ => ∑ k ∈ Finset.range N, ∑ r ∈ Finset.range (2 * N),
    lcuCoef k r • NormedSpace.exp (((freq k r : ℂ) * Complex.I) • Xop Λ M σ) with hL
  -- the branch sum
  have hsum : ∑ i, coef N i • branchEvolution N Λ M i =
      ∑ σ : Bool, ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • L σ := by
    rw [Fintype.sum_sum_type]
    have hpadsum : ∑ b : Bool, coef N (.inr b) • branchEvolution N Λ M (.inr b) = 0 := by
      simp only [Fintype.sum_bool, coef, branchEvolution_inr, if_true, Bool.false_eq_true,
        if_false, one_mul, neg_one_mul]
      ext1 v
      simp
    rw [hpadsum, add_zero, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro σ _
    have hterm : ∀ y : Fin N × Fin (2 * N),
        coef N (.inl (σ, y)) • branchEvolution N Λ M (.inl (σ, y)) =
          ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) •
            (lcuCoef y.1 y.2 • NormedSpace.exp (((freq y.1 y.2 : ℂ) * Complex.I) • Xop Λ M σ)) := by
      intro y
      rw [branchEvolution_inl N Λ hΛ M σ y.1 y.2, smul_smul]
      rfl
    rw [Finset.sum_congr rfl (fun y _ => hterm y), ← Finset.smul_sum,
      sum_fin_prod N (fun k r => lcuCoef k r •
        NormedSpace.exp (((freq k r : ℂ) * Complex.I) • Xop Λ M σ))]
  -- the target
  have htarget : (((8 * Real.sqrt 2 * Λ)⁻¹ : ℝ) : ℂ) • (-matrixOperator M) =
      ∑ σ : Bool, ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • Xop Λ M σ := by
    rw [NativeMatrix.neg_matrixOperator_eq, Fintype.sum_bool]
    simp only [Xop, weight, if_true, Bool.false_eq_true, if_false, smul_add, smul_smul]
    have hΛ' : (Λ : ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
    have hs' : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs2.ne'
    congr 1 <;> (unfold Kop; congr 1; push_cast; field_simp; ring)
  rw [hsum, htarget, ← Finset.sum_sub_distrib]
  calc ‖∑ σ : Bool, (((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • L σ -
          ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • Xop Λ M σ)‖
      ≤ ∑ σ : Bool, ‖((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • L σ -
          ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • Xop Λ M σ‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Bool, (1 / 4) * (1 / 4) ^ N := by
        apply Finset.sum_le_sum
        intro σ _
        rw [show ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • L σ -
            ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • Xop Λ M σ =
            ((((2 * Real.sqrt 2)⁻¹ : ℝ) : ℂ) * weight σ) • (L σ - Xop Λ M σ) from
          (smul_sub _ _ _).symm, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity), norm_weight]
        have happrox := Spectral.lcu_approx (Xop Λ M σ) (Xop_selfAdjoint Λ M σ)
          (norm_Xop_le Λ hΛ M hM σ) N
        have hc : (2 * Real.sqrt 2)⁻¹ * (Real.sqrt 2 / 2) = 1 / 4 := by
          have hsq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          field_simp
          linarith
        rw [hc]
        exact mul_le_mul_of_nonneg_left happrox (by norm_num)
    _ = (1 / 4) ^ N / 2 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool]; ring

end

end SparseHamiltonian.GeneralODE.NativeBlock
