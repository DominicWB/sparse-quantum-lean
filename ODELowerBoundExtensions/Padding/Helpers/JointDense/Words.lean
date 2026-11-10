import SparseLowerBounds.ODE.JointInstance

/-!
# Rescaled words and the joint generator off the core (helper of `Padding/JointDense`)

Manuscript: the construction before Theorem `odel:thm:joint` (the joint family's dyadic words) and
the end of its proof (the dense block). The dense padding stores the joint family's core words
`w ∈ (-2^μ, 2^μ]` (`SparseLowerBounds.ODE.jointTable_word_mem`) as `2^{B-μ} w ∈ (-2^B, 2^B]`, which
decode to the same entry `w/2^μ` (`denseWord_scale_mem`, `denseWord_scale_decode`), and the block
word `1` or `0` (`denseWord_ite_mem`). The joint generator vanishes on the rows and columns of the
`Fin s` block (`denseJointGen_inr_left`, `denseJointGen_inr_right`, from
`SparseLowerBounds.ODE.jointGen_support`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE

/-- A core word rescaled by `2^{B-μ}` stays in `(-2^B, 2^B]`. -/
theorem denseWord_scale_mem {μ B : ℕ} (hμB : μ ≤ B) {w : ℤ} (h1 : -(2 : ℤ) ^ μ < w)
    (h2 : w ≤ 2 ^ μ) : -(2 : ℤ) ^ B < 2 ^ (B - μ) * w ∧ 2 ^ (B - μ) * w ≤ 2 ^ B := by
  have hp : (2 : ℤ) ^ (B - μ) * 2 ^ μ = 2 ^ B := by rw [← pow_add, Nat.sub_add_cancel hμB]
  have hpos : (0 : ℤ) < 2 ^ (B - μ) := by positivity
  rw [← hp]
  constructor <;> nlinarith

/-- A core word rescaled by `2^{B-μ}` decodes to the same entry: `2^{B-μ} w/2^B = w/2^μ`. -/
theorem denseWord_scale_decode {μ B : ℕ} (hμB : μ ≤ B) (w : ℤ) :
    Complex.I * (((2 ^ (B - μ) * w : ℤ) : ℂ) / 2 ^ B) = Complex.I * ((w : ℂ) / 2 ^ μ) := by
  have hB : ((2 : ℂ) ^ B) = 2 ^ (B - μ) * 2 ^ μ := by rw [← pow_add, Nat.sub_add_cancel hμB]
  rw [hB]
  push_cast
  rw [mul_div_mul_left _ _ (pow_ne_zero _ two_ne_zero)]

/-- The block word `1` (or `0`) lies in `(-2^B, 2^B]`. -/
theorem denseWord_ite_mem (B : ℕ) (dense : Bool) :
    -(2 : ℤ) ^ B < (if dense then 1 else 0) ∧ (if dense then 1 else 0 : ℤ) ≤ 2 ^ B := by
  have h1 : (1 : ℤ) ≤ 2 ^ B := one_le_pow₀ (by norm_num)
  cases dense <;> simp only [Bool.false_eq_true, if_false, if_pos] <;> constructor <;> linarith

variable {M n μ s : ℕ}

/-- The joint generator vanishes on the rows of the `Fin s` block. -/
theorem denseJointGen_inr_left (j : Positions M n (2 ^ μ)) (k : Fin (n + 2)) (t : Fin s)
    (i' : JointIndex M μ s) : jointGen j k (Sum.inr t) i' = 0 := by
  by_contra h
  obtain ⟨_, _, _, _, hi, _⟩ := jointGen_support h
  exact Sum.inr_ne_inl hi

/-- The joint generator vanishes on the columns of the `Fin s` block. -/
theorem denseJointGen_inr_right (j : Positions M n (2 ^ μ)) (k : Fin (n + 2))
    (i : JointIndex M μ s) (t : Fin s) : jointGen j k i (Sum.inr t) = 0 := by
  by_contra h
  obtain ⟨_, _, _, _, _, hi⟩ := jointGen_support h
  exact Sum.inr_ne_inl hi

end

end ODELowerBoundExtensions.Padding
