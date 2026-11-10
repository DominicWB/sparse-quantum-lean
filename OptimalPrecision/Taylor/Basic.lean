import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Taylor coefficients at the origin and uniform clock functionals

For `f : ℂ → E`, `coeff f k = f^{(k)}(0) / k!` is the `k`-th Taylor coefficient
at the origin, and

  `ces f j = ∑_{k<j} (1 - k/j) [w^k] f`

is the finite Cesàro functional of the uniform public clock of a `j`-reuse
circuit (`opt:eq:cesaro`). The coefficient calculus below (linearity, products,
derivatives, monomials) is all that the exact moment construction of
Theorem `opt:thm:weights` uses about the transfer functions.
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Filter
open scoped Topology

section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The `k`-th Taylor coefficient at the origin, `f^{(k)}(0) / k!`. -/
def coeff (f : ℂ → E) (k : ℕ) : E := ((k ! : ℂ)⁻¹) • iteratedDeriv k f 0

/-- The uniform clock functional `Ces_j(F) = ∑_{k<j} (1 - k/j) [w^k] F` of
`opt:eq:cesaro`. -/
def ces (f : ℂ → E) (j : ℕ) : E :=
  ∑ k ∈ range j, ((1 : ℂ) - (k : ℂ) / (j : ℂ)) • coeff f k

theorem coeff_zero_eq (f : ℂ → E) : coeff f 0 = f 0 := by
  simp [coeff]

theorem iteratedDeriv_eq_factorial_smul_coeff (f : ℂ → E) (k : ℕ) :
    iteratedDeriv k f 0 = (k ! : ℂ) • coeff f k := by
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  simp [coeff, smul_smul, mul_inv_cancel₀ hk]

/-- Coefficients only see the germ at the origin. -/
theorem coeff_congr {f g : ℂ → E} (h : f =ᶠ[𝓝 0] g) (k : ℕ) : coeff f k = coeff g k := by
  simp [coeff, h.iteratedDeriv_eq k]

theorem ces_congr {f g : ℂ → E} (h : f =ᶠ[𝓝 0] g) (j : ℕ) : ces f j = ces g j := by
  simp [ces, coeff_congr h]

@[simp] theorem ces_zero (f : ℂ → E) : ces f 0 = 0 := by simp [ces]

/-- The one-slot clock reads only the constant term. -/
theorem ces_one (f : ℂ → E) : ces f 1 = f 0 := by
  simp [ces, coeff_zero_eq]

theorem coeff_neg (f : ℂ → E) (k : ℕ) : coeff (fun w => -f w) k = -coeff f k := by
  simp [coeff]

theorem coeff_const_smul_field (c : ℂ) (f : ℂ → E) (k : ℕ) :
    coeff (fun w => c • f w) k = c • coeff f k := by
  simp only [coeff, iteratedDeriv_fun_const_smul_field, smul_comm c]

theorem ces_const_smul_field (c : ℂ) (f : ℂ → E) (j : ℕ) :
    ces (fun w => c • f w) j = c • ces f j := by
  simp only [ces, coeff_const_smul_field, Finset.smul_sum, smul_comm c]

/-- The derivative shifts the coefficient sequence. -/
theorem coeff_deriv (f : ℂ → E) (k : ℕ) :
    coeff (deriv f) k = ((k + 1 : ℕ) : ℂ) • coeff f (k + 1) := by
  have h := iteratedDeriv_succ' (n := k) (f := f)
  simp only [coeff, ← h, smul_smul]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp

end Defs

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem coeff_add {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    coeff (fun w => f w + g w) k = coeff f k + coeff g k := by
  simp only [coeff, iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, smul_add]

theorem coeff_sub {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    coeff (fun w => f w - g w) k = coeff f k - coeff g k := by
  simp only [coeff, iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, smul_sub]

theorem coeff_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (k : ℕ) :
    coeff (fun w => ∑ i ∈ s, f i w) k = ∑ i ∈ s, coeff (f i) k := by
  simp only [coeff, iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt), Finset.smul_sum]

omit [CompleteSpace E] in
/-- A scalar function multiplying a constant vector. -/
theorem coeff_smul_const {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (v : E) (k : ℕ) :
    coeff (fun w => f w • v) k = coeff f k • v := by
  simp only [coeff, iteratedDeriv_smul_const hf.contDiffAt v, smul_assoc]

theorem ces_add {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (j : ℕ) :
    ces (fun w => f w + g w) j = ces f j + ces g j := by
  simp only [ces, coeff_add hf hg, smul_add, Finset.sum_add_distrib]

theorem ces_sub {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (j : ℕ) :
    ces (fun w => f w - g w) j = ces f j - ces g j := by
  simp only [ces, coeff_sub hf hg, smul_sub, Finset.sum_sub_distrib]

theorem ces_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) 0) (j : ℕ) :
    ces (fun w => ∑ i ∈ s, f i w) j = ∑ i ∈ s, ces (f i) j := by
  simp only [ces, coeff_sum s hf, Finset.smul_sum]
  exact Finset.sum_comm

omit [CompleteSpace E] in
theorem ces_smul_const {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (v : E) (j : ℕ) :
    ces (fun w => f w • v) j = ces f j • v := by
  simp only [ces, coeff_smul_const hf v, Finset.sum_smul, smul_assoc]

/-- Leibniz rule for a scalar function times a vector-valued function, in
Taylor coefficients: the coefficient sequence of a product is the Cauchy
product of the coefficient sequences. -/
theorem coeff_smul {f : ℂ → ℂ} {g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (k : ℕ) :
    coeff (fun w => f w • g w) k =
      ∑ i ∈ range (k + 1), coeff f i • coeff g (k - i) := by
  have h := iteratedDerivWithin_smul (Set.mem_univ (0 : ℂ)) uniqueDiffOn_univ
    (n := k) (f := f) (g := g) hf.contDiffAt.contDiffWithinAt hg.contDiffAt.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at h
  have h' : iteratedDeriv k (fun w => f w • g w) 0 =
      ∑ i ∈ range (k + 1), k.choose i • iteratedDeriv i f 0 • iteratedDeriv (k - i) g 0 := h
  change ((k ! : ℂ)⁻¹) • iteratedDeriv k (fun w => f w • g w) 0 = _
  rw [h', Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have e1 : iteratedDeriv i f 0 = (i ! : ℂ) * coeff f i := by
    rw [iteratedDeriv_eq_factorial_smul_coeff f i, smul_eq_mul]
  have e2 : iteratedDeriv (k - i) g 0 = ((k - i) ! : ℂ) • coeff g (k - i) :=
    iteratedDeriv_eq_factorial_smul_coeff g (k - i)
  rw [e1, e2, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul, smul_smul]
  congr 1
  have hfac : (k ! : ℂ) = (k.choose i : ℂ) * (i ! : ℂ) * ((k - i) ! : ℂ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hik).symm
  have h1 : (i ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
  have h2 : ((k - i) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (k - i)).ne'
  have h3 : (k.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hik).ne'
  rw [hfac]
  field_simp

end Complete

section Scalar

/-- Leibniz rule for two scalar functions. -/
theorem coeff_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    coeff (fun w => f w * g w) k =
      ∑ i ∈ range (k + 1), coeff f i * coeff g (k - i) := by
  simpa only [smul_eq_mul] using coeff_smul hf hg k

/-- Monomials. -/
theorem coeff_pow (m k : ℕ) :
    coeff (fun w : ℂ => w ^ m) k = if k = m then 1 else 0 := by
  simp only [coeff, iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst h
    have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
    simp [hk]
  · simp

theorem coeff_const (c : ℂ) (k : ℕ) :
    coeff (fun _ : ℂ => c) k = if k = 0 then c else 0 := by
  rcases k with _ | k
  · simp [coeff_zero_eq]
  · simp [coeff, iteratedDeriv_succ']

/-- Multiplication by the variable shifts coefficients up by one. -/
theorem coeff_X_mul {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (k : ℕ) :
    coeff (fun w => w * f w) (k + 1) = coeff f k := by
  have hid : AnalyticAt ℂ (fun w : ℂ => w) 0 := analyticAt_id
  rw [coeff_mul hid hf, Finset.sum_eq_single 1]
  · have h1 : coeff (fun w : ℂ => w) 1 = 1 := by simpa using coeff_pow 1 1
    rw [h1, one_mul, Nat.add_sub_cancel]
  · intro b _ hb
    have : coeff (fun w : ℂ => w) b = 0 := by simpa [hb] using coeff_pow 1 b
    rw [this, zero_mul]
  · intro h; simp at h

theorem coeff_X_mul_zero (f : ℂ → ℂ) : coeff (fun w => w * f w) 0 = 0 := by
  simp [coeff_zero_eq]

end Scalar

end

end OptimalPrecision
