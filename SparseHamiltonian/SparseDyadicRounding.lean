import SparseHamiltonian.NativeSparseMaskedAccess

/-!
# A finite conjugation-compatible dyadic matrix-value decoder

Each real component is truncated toward zero on the mesh `2⁻ᵇ` and saturated
at an explicit magnitude code bound. Signs and bounded natural magnitudes form
an actual finite code alphabet. Saturation makes the encoder total, including
on inputs outside its certified range. Zero and complex conjugation are
preserved exactly for every input. Inside the range the entry error is at most
`2 / 2^b`; sparse operator and evolution bounds then use the proved decoder
interface. This construction does not assert an elementary-gate implementation
of arithmetic on arbitrary real inputs.
-/

namespace SparseHamiltonian.SparseDyadicRounding

noncomputable section
open SparseValuePrecision SparseStateOverlap
open scoped ComplexConjugate

/-- Dyadic denominator for `b` fractional bits. -/
def scale (b : ℕ) : ℝ := 2 ^ b

@[simp] theorem scale_pos (b : ℕ) : 0 < scale b := by unfold scale; positivity

theorem scale_ne_zero (b : ℕ) : scale b ≠ 0 := ne_of_gt (scale_pos b)

/-- One explicit sign bit and a bounded magnitude; both signs may encode zero. -/
abbrev SignedCode (M : ℕ) := Bool × Fin (M + 1)

/-- A finite pair of signed dyadic real components. -/
abbrev Code (M : ℕ) := SignedCode M × SignedCode M

/-- The magnitude is a floor of the absolute scaled input, clipped to its range. -/
def magnitude (b M : ℕ) (x : ℝ) : ℕ := min ⌊|x| * scale b⌋₊ M

/-- Total finite encoding, with sign chosen before magnitude truncation. -/
def encodeReal (b M : ℕ) (x : ℝ) : SignedCode M :=
  (decide (x < 0), ⟨magnitude b M x, Nat.lt_succ_of_le (min_le_right _ _)⟩)

/-- Exact real value represented by a signed finite code. -/
def decodeReal (b : ℕ) {M : ℕ} (c : SignedCode M) : ℝ :=
  if c.1 then -((c.2.val : ℝ) / scale b) else (c.2.val : ℝ) / scale b

/-- Concrete real dyadic rounding, including saturation. -/
def roundReal (b M : ℕ) (x : ℝ) : ℝ := decodeReal b (encodeReal b M x)

theorem roundReal_eq (b M : ℕ) (x : ℝ) :
    roundReal b M x =
      if x < 0 then -((magnitude b M x : ℝ) / scale b)
      else (magnitude b M x : ℝ) / scale b := by
  simp [roundReal, decodeReal, encodeReal]

@[simp] theorem magnitude_zero (b M : ℕ) : magnitude b M 0 = 0 := by
  simp [magnitude]

@[simp] theorem magnitude_neg (b M : ℕ) (x : ℝ) :
    magnitude b M (-x) = magnitude b M x := by simp [magnitude]

@[simp] theorem roundReal_zero (b M : ℕ) : roundReal b M 0 = 0 := by
  simp [roundReal_eq]

/-- Symmetric truncation commutes with negation, unlike an ordinary floor. -/
@[simp] theorem roundReal_neg (b M : ℕ) (x : ℝ) :
    roundReal b M (-x) = -roundReal b M x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [roundReal_eq, roundReal_eq, magnitude_neg]
    by_cases hpos : x < 0
    · simp [hpos, show ¬ -x < 0 by linarith]
    · simp [hpos, show 0 < x from lt_of_le_of_ne (le_of_not_gt hpos) (Ne.symm hx)]

/-- Exact finite-code encoder for complex entries. -/
def encode (b M : ℕ) (z : ℂ) : Code M :=
  (encodeReal b M z.re, encodeReal b M z.im)

/-- Exact complex value represented by the two signed dyadic codes. -/
def decode (b : ℕ) {M : ℕ} (c : Code M) : ℂ :=
  ⟨decodeReal b c.1, decodeReal b c.2⟩

/-- The rounded complex entry actually produced by the finite decoder. -/
def value (b M : ℕ) (z : ℂ) : ℂ := decode b (encode b M z)

@[simp] theorem value_re (b M : ℕ) (z : ℂ) :
    (value b M z).re = roundReal b M z.re := rfl

@[simp] theorem value_im (b M : ℕ) (z : ℂ) :
    (value b M z).im = roundReal b M z.im := rfl

@[simp] theorem value_zero (b M : ℕ) : value b M 0 = 0 := by
  apply Complex.ext <;> simp

/-- Conjugation compatibility is global, even when the input saturates. -/
@[simp] theorem value_star (b M : ℕ) (z : ℂ) :
    value b M (star z) = star (value b M z) := by
  apply Complex.ext <;> simp

/-- Concrete finite decoder satisfying the previously abstract precision interface. -/
def decoder (b M : ℕ) : FiniteValueDecoder (Code M) where
  encode := encode b M
  decode := decode b
  zero_exact := value_zero b M
  star_exact := value_star b M

@[simp] theorem decoder_value (b M : ℕ) (z : ℂ) :
    (decoder b M).value z = value b M z := rfl

/-- The exact alphabet size, including the two sign bits. -/
theorem card_code (M : ℕ) : Fintype.card (Code M) = (2 * (M + 1)) ^ 2 := by
  simp [Code, SignedCode, Fintype.card_prod, pow_two]

/-- Magnitude truncation never exceeds the absolute input, even after clipping. -/
theorem magnitude_le_scaled_abs (b M : ℕ) (x : ℝ) :
    (magnitude b M x : ℝ) ≤ |x| * scale b := by
  apply (Nat.cast_le.mpr (min_le_left _ _)).trans
  exact Nat.floor_le (mul_nonneg (abs_nonneg x) (scale_pos b).le)

/-- The absolute rounded value is its encoded nonnegative magnitude. -/
theorem abs_roundReal (b M : ℕ) (x : ℝ) :
    |roundReal b M x| = (magnitude b M x : ℝ) / scale b := by
  rw [roundReal_eq]
  split_ifs <;> simp [abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (scale_pos b).le)]

/-- This concrete rule cannot increase the absolute value of either component. -/
theorem abs_roundReal_le (b M : ℕ) (x : ℝ) : |roundReal b M x| ≤ |x| := by
  rw [abs_roundReal]
  exact (div_le_iff₀ (scale_pos b)).mpr (magnitude_le_scaled_abs b M x)

/-- All rounded real outputs lie inside the finite encoded range. -/
theorem abs_roundReal_le_range (b M : ℕ) (x : ℝ) :
    |roundReal b M x| ≤ (M : ℝ) / scale b := by
  rw [abs_roundReal]
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (min_le_right _ _)) (scale_pos b).le

/-- The rounding error is the discarded nonnegative absolute magnitude. -/
theorem abs_roundReal_error_eq (b M : ℕ) (x : ℝ) :
    |x - roundReal b M x| = |x| - (magnitude b M x : ℝ) / scale b := by
  have hq : (magnitude b M x : ℝ) / scale b ≤ |x| := by
    simpa only [abs_roundReal] using abs_roundReal_le b M x
  rw [roundReal_eq]
  by_cases hx : x < 0
  · rw [if_pos hx, abs_of_neg hx] at *
    rw [abs_of_nonpos (by linarith)]
    ring
  · rw [if_neg hx, abs_of_nonneg (le_of_not_gt hx)] at *
    exact abs_of_nonneg (sub_nonneg.mpr hq)

/-- Saturation is inactive throughout its promised scalar range. -/
theorem magnitude_eq_floor (b M : ℕ) (x : ℝ) (hx : |x| * scale b ≤ (M : ℝ)) :
    magnitude b M x = ⌊|x| * scale b⌋₊ := by
  exact min_eq_left (Nat.floor_le_of_le hx)

/-- One real component has error at most one dyadic mesh width. -/
theorem roundReal_error_le (b M : ℕ) (x : ℝ) (hx : |x| * scale b ≤ (M : ℝ)) :
    |x - roundReal b M x| ≤ 1 / scale b := by
  rw [abs_roundReal_error_eq, magnitude_eq_floor b M x hx]
  apply (le_div_iff₀ (scale_pos b)).mpr
  have hfloor := Nat.lt_floor_add_one (|x| * scale b)
  have hdiv := div_mul_cancel₀ ((⌊|x| * scale b⌋₊ : ℕ) : ℝ) (scale_ne_zero b)
  nlinarith

/-- Known entry magnitude bounds determine a concrete finite code range. -/
def capacity (b : ℕ) (A : ℝ) : ℕ := ⌈A * scale b⌉₊

/-- Every component of a complex entry bounded by `A` fits the selected range. -/
theorem component_fits (b : ℕ) (A x : ℝ) (hx : |x| ≤ A) :
    |x| * scale b ≤ (capacity b A : ℝ) := by
  exact (mul_le_mul_of_nonneg_right hx (scale_pos b).le).trans (Nat.le_ceil _)

/-- The explicit finite decoder has the required complex-entry accuracy. -/
theorem value_error_le (b : ℕ) (A : ℝ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    ‖z - value b (capacity b A) z‖ ≤ 2 / scale b := by
  calc
    _ ≤ |(z - value b (capacity b A) z).re| +
        |(z - value b (capacity b A) z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / scale b + 1 / scale b := by
      simp only [Complex.sub_re, Complex.sub_im, value_re, value_im]
      exact add_le_add
        (roundReal_error_le b _ z.re (component_fits b A z.re ((Complex.abs_re_le_norm z).trans hz)))
        (roundReal_error_le b _ z.im (component_fits b A z.im ((Complex.abs_im_le_norm z).trans hz)))
    _ = 2 / scale b := by ring

/-- Rounding toward zero also preserves every complex-entry magnitude bound. -/
theorem norm_value_le (b M : ℕ) (z : ℂ) : ‖value b M z‖ ≤ ‖z‖ := by
  have hr : (roundReal b M z.re) ^ 2 ≤ z.re ^ 2 := sq_le_sq.mpr (abs_roundReal_le b M z.re)
  have hi : (roundReal b M z.im) ^ 2 ≤ z.im ^ 2 := sq_le_sq.mpr (abs_roundReal_le b M z.im)
  have hv := Complex.normSq_eq_norm_sq (value b M z)
  have hz := Complex.normSq_eq_norm_sq z
  simp only [Complex.normSq_apply, value_re, value_im] at hv hz
  nlinarith [norm_nonneg (value b M z), norm_nonneg z]

/-- The displayed error constant is exactly twice the usual `2⁻ᵇ` mesh. -/
theorem error_eq_dyadic (b : ℕ) :
    2 / scale b = 2 * (2 : ℝ) ^ (-(b : ℤ)) := by
  simp [scale, zpow_neg, div_eq_mul_inv]

/-- A maximum-entry exponent also bounds the concrete finite magnitude alphabet. -/
theorem capacity_le_pow (b k : ℕ) (A : ℝ) (hA : A ≤ (2 : ℝ) ^ k) :
    capacity b A ≤ 2 ^ (b + k) := by
  apply Nat.ceil_le.mpr
  calc
    A * scale b ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ b :=
      mul_le_mul_of_nonneg_right hA (scale_pos b).le
    _ = (2 : ℝ) ^ (b + k) := by rw [pow_add]; ring
    _ = ((2 ^ (b + k) : ℕ) : ℝ) := by norm_cast

/-- A bounded entry exponent gives an explicit binary capacity for both signed
components. This bounds storage, not the gate cost of producing the code. -/
theorem card_code_le_binary (b k : ℕ) (A : ℝ) (hA : A ≤ (2 : ℝ) ^ k) :
    Fintype.card (Code (capacity b A)) ≤ 2 ^ (2 * (b + k + 2)) := by
  have hM := capacity_le_pow b k A hA
  have hp : 0 < (2 : ℕ) ^ (b + k) := pow_pos (by decide) _
  have hs : 2 * (capacity b A + 1) ≤ 2 ^ (b + k + 2) := by
    rw [show b + k + 2 = (b + k) + 1 + 1 by omega, pow_succ, pow_succ]
    omega
  rw [card_code]
  calc
    (2 * (capacity b A + 1)) ^ 2 ≤ (2 ^ (b + k + 2)) ^ 2 := by gcongr
    _ = 2 ^ (2 * (b + k + 2)) := by rw [← pow_mul]; congr 1; omega

/-- A concrete fractional-bit schedule for the sparse evolution error budget. -/
def precisionBits (s : ℕ) (t ε : ℝ) : ℕ :=
  ⌈Real.log (max 1 (2 * (s : ℝ) * |t| / ε)) / Real.log 2⌉₊

/-- The dyadic denominator selected by the schedule dominates the required ratio. -/
theorem precisionBits_scale (s : ℕ) (t ε : ℝ) :
    2 * (s : ℝ) * |t| / ε ≤ scale (precisionBits s t ε) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < max 1 (2 * (s : ℝ) * |t| / ε) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hn : Real.log (max 1 (2 * (s : ℝ) * |t| / ε)) ≤
      (precisionBits s t ε : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog).mp (Nat.le_ceil _)
  have hh := Real.exp_le_exp.mpr hn
  rw [Real.exp_log hA, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  exact (le_max_right _ _).trans hh

/-- The chosen finite precision makes the full sparse input-rounding evolution
error at most the requested positive allowance, including zero time/sparsity. -/
theorem precisionBits_error (s : ℕ) (t ε : ℝ) (hε : 0 < ε) :
    |t| * ((s : ℝ) * (2 / scale (precisionBits s t ε))) ≤ ε := by
  have h := (div_le_iff₀ hε).mp (precisionBits_scale s t ε)
  calc
    _ = (2 * (s : ℝ) * |t|) / scale (precisionBits s t ε) := by ring
    _ ≤ ε := (div_le_iff₀ (scale_pos _)).mpr (by nlinarith)

/-- The actual integer bit budget is logarithmic in the precision ratio. -/
theorem precisionBits_lt (s : ℕ) (t ε : ℝ) :
    (precisionBits s t ε : ℝ) <
      Real.log (max 1 (2 * (s : ℝ) * |t| / ε)) / Real.log 2 + 1 := by
  apply Nat.ceil_lt_add_one
  exact div_nonneg (Real.log_nonneg (le_max_left _ _)) (Real.log_pos (by norm_num)).le

section Matrices
variable {I J : Type*} [Fintype I] [Fintype J]

/-- The actual entrywise finite dyadic approximation of a matrix. -/
def matrix (b : ℕ) (A : ℝ) (H : Matrix I J ℂ) : Matrix I J ℂ :=
  (decoder b (capacity b A)).matrix H

omit [Fintype I] [Fintype J] in
@[simp] theorem matrix_apply (b : ℕ) (A : ℝ) (H : Matrix I J ℂ) (i : I) (j : J) :
    matrix b A H i j = value b (capacity b A) (H i j) := rfl

omit [Fintype I] in
/-- The rounded row never introduces a nonzero entry outside the original support. -/
theorem support_subset (b : ℕ) (A : ℝ) (f : J → ℂ) :
    nonzeroPositions (fun j => value b (capacity b A) (f j)) ⊆ nonzeroPositions f :=
  (decoder b (capacity b A)).support_subset f

omit [Fintype I] in
/-- Difference support is likewise contained in the original support. -/
theorem difference_support_subset (b : ℕ) (A : ℝ) (f : J → ℂ) :
    nonzeroPositions (fun j => f j - value b (capacity b A) (f j)) ⊆ nonzeroPositions f :=
  (decoder b (capacity b A)).difference_support_subset f

omit [Fintype I] in
/-- The concrete rounded matrix retains the original row sparsity budget. -/
theorem row_sparse (b : ℕ) (A : ℝ) (H : Matrix I J ℂ) (s : ℕ)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s) :
    ∀ i, (nonzeroPositions (matrix b A H i)).card ≤ s :=
  (decoder b (capacity b A)).row_sparse H s hRow

omit [Fintype J] in
/-- The same finite encoding preserves column sparsity. -/
theorem column_sparse (b : ℕ) (A : ℝ) (H : Matrix I J ℂ) (s : ℕ)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s) :
    ∀ j, (nonzeroPositions (fun i => matrix b A H i j)).card ≤ s :=
  (decoder b (capacity b A)).column_sparse H s hCol

omit [Fintype I] [Fintype J] in
/-- Each decoded entry obeys the explicit dyadic error bound. -/
theorem matrix_entry_error (b : ℕ) (A : ℝ) (H : Matrix I J ℂ)
    (hH : ∀ i j, ‖H i j‖ ≤ A) (i : I) (j : J) :
    ‖H i j - matrix b A H i j‖ ≤ 2 / scale b :=
  value_error_le b A (H i j) (hH i j)

omit [Fintype I] [Fintype J] in
/-- Original magnitude bounds remain valid for the finite rounded entries. -/
theorem matrix_entry_bound (b : ℕ) (A : ℝ) (H : Matrix I J ℂ)
    (hH : ∀ i j, ‖H i j‖ ≤ A) (i : I) (j : J) :
    ‖matrix b A H i j‖ ≤ A :=
  (norm_value_le b (capacity b A) (H i j)).trans (hH i j)

/-- The actual finite dyadic decoder incurs operator error at most `2s/2^b`.
The original sparse supports control the difference; no doubled sparsity is used. -/
theorem operator_error_le (b : ℕ) (A : ℝ) (H : Matrix I J ℂ) (s : ℕ)
    (hH : ∀ i j, ‖H i j‖ ≤ A)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s) :
    ‖matrixOperator H - matrixOperator (matrix b A H)‖ ≤ (s : ℝ) * (2 / scale b) := by
  exact (decoder b (capacity b A)).operator_error_le H s (2 / scale b)
    (div_nonneg (by norm_num) (scale_pos b).le) hRow hCol (matrix_entry_error b A H hH)

end Matrices

section Hermitian
variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- The concrete sign-symmetric rounding preserves Hermiticity exactly. -/
theorem isHermitian (b : ℕ) (A : ℝ) (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    (matrix b A H).IsHermitian :=
  (decoder b (capacity b A)).isHermitian H hH

/-- Hamiltonian evolution under the concrete rounded matrix has time-linear error. -/
theorem evolution_error_le (b : ℕ) (A : ℝ) (H : Matrix n n ℂ) (s : ℕ) (t : ℝ)
    (hA : ∀ i j, ‖H i j‖ ≤ A) (hH : H.IsHermitian)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator (matrix b A H))‖ ≤
      |t| * ((s : ℝ) * (2 / scale b)) := by
  exact (decoder b (capacity b A)).evolution_error_le H s t (2 / scale b)
    (div_nonneg (by norm_num) (scale_pos b).le) hH hRow hCol (matrix_entry_error b A H hA)

/-- Adding dyadic input precision to a complete simulator's output error needs
no separate postselection or dimension factor. -/
theorem output_error_le {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (b : ℕ) (A : ℝ) (H : Matrix n n ℂ) (S F : EuclideanSpace ℂ n →L[ℂ] K)
    (s : ℕ) (t ε : ℝ) (hA : ∀ i j, ‖H i j‖ ≤ A) (hH : H.IsHermitian)
    (hF : ‖F‖ ≤ 1)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s)
    (hError : ‖S - F ∘L NormedSpace.exp
      ((-Complex.I * (t : ℂ)) • matrixOperator (matrix b A H))‖ ≤ ε) :
    ‖S - F ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H)‖ ≤
      ε + |t| * ((s : ℝ) * (2 / scale b)) := by
  exact (decoder b (capacity b A)).output_error_le H S F s t ε (2 / scale b)
    (div_nonneg (by norm_num) (scale_pos b).le) hH hF hRow hCol (matrix_entry_error b A H hA) hError

/-- The explicit schedule instantiates the concrete matrix-evolution guarantee. -/
theorem scheduled_evolution_error (A : ℝ) (H : Matrix n n ℂ) (s : ℕ) (t ε : ℝ)
    (hε : 0 < ε) (hA : ∀ i j, ‖H i j‖ ≤ A) (hH : H.IsHermitian)
    (hRow : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hCol : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        matrixOperator (matrix (precisionBits s t ε) A H))‖ ≤ ε :=
  (evolution_error_le _ A H s t hA hH hRow hCol).trans (precisionBits_error s t ε hε)

end Hermitian
end
end SparseHamiltonian.SparseDyadicRounding
