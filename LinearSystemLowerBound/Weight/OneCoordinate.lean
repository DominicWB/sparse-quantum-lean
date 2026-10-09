import LinearSystemLowerBound.Weight.Coordinates

/-!
# One hidden coordinate: weight, single-bit queries and parity

On one hidden position `q : Fin m` let `P = |u⟩⟨u|` be the uniform projector (`avg m`),
`w = 2I - P` the weight (`weight m`) with inverse `w⁻¹ = (I + P)/2` (`weightInv m`), and
`Z = diag((-1)^q)` the position parity (`parityMat m`).  All statements hold for families
with values in an arbitrary complex inner-product space, i.e. for these matrices tensored
with an identity.

* `norm_sq_act_weightInv_le`: `‖w⁻¹ φ‖ ≤ ‖φ‖`.
* `weight_growth_bit`: a query whose action depends on the single bit `[q = q₀]`
  (operators `V₀`, `V₁` preserving norms) satisfies `‖w Ô φ‖ ≤ (1 + 2/√m) ‖w φ‖`; the proof
  is `w Ô w⁻¹ = Ô - [P, Ô] w⁻¹` with `‖[P, Ô]‖ ≤ 2/√m`.
* `norm_sq_act_parityKernel_le`: for even `m`, `‖w⁻¹ Z w⁻¹ ξ‖ ≤ ‖ξ‖/2`.
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace Matrix

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ### Cauchy--Schwarz for finite sums of vectors -/

omit [InnerProductSpace ℂ V] in
theorem norm_sum_sq_le {α : Type*} (s : Finset α) (f : α → V) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖f i‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h2
  calc ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- Weighted Cauchy--Schwarz with weights in `{0, 1}`. -/
theorem norm_sum_indicator_sq_le {α : Type*} (s : Finset α) (e : α → ℝ)
    (he : ∀ i, e i = 0 ∨ e i = 1) (f : α → V) :
    ‖∑ i ∈ s, e i • f i‖ ^ 2 ≤ (∑ i ∈ s, e i) * ∑ i ∈ s, e i * ‖f i‖ ^ 2 := by
  have hsq : ∀ i, e i * e i = e i := fun i => by rcases he i with h | h <;> simp [h]
  have hnn : ∀ i, 0 ≤ e i := fun i => by rcases he i with h | h <;> simp [h]
  have h1 : ‖∑ i ∈ s, e i • f i‖ ≤ ∑ i ∈ s, e i * (e i * ‖f i‖) := by
    calc ‖∑ i ∈ s, e i • f i‖ ≤ ∑ i ∈ s, ‖e i • f i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, e i * (e i * ‖f i‖) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn i), ← mul_assoc, hsq]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s e (fun i => e i * ‖f i‖)
  have h3 : ∑ i ∈ s, e i ^ 2 = ∑ i ∈ s, e i := by
    apply Finset.sum_congr rfl; intro i _; rw [sq, hsq]
  have h4 : ∑ i ∈ s, (e i * ‖f i‖) ^ 2 = ∑ i ∈ s, e i * ‖f i‖ ^ 2 := by
    apply Finset.sum_congr rfl; intro i _; rw [mul_pow, sq (e i), hsq]
  have h0 : 0 ≤ ∑ i ∈ s, e i * (e i * ‖f i‖) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hnn i) (mul_nonneg (hnn i) (norm_nonneg _))
  calc ‖∑ i ∈ s, e i • f i‖ ^ 2 ≤ (∑ i ∈ s, e i * (e i * ‖f i‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by rw [← h3, ← h4]; exact h2

/-! ### The one-coordinate matrices -/

section Matrices

variable (m : ℕ)

/-- The uniform projector `P = |u⟩⟨u|`, `u = m^{-1/2} ∑ |q⟩`. -/
def avg : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun _ _ => (m : ℂ)⁻¹

/-- The weight `w = 2I - P`. -/
def weight : Matrix (Fin m) (Fin m) ℂ := (2 : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) - avg m

/-- The inverse weight `w⁻¹ = (I + P)/2`. -/
def weightInv : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • ((1 : Matrix (Fin m) (Fin m) ℂ) + avg m)

/-- The sign `(-1)^q` of a position. -/
def sgn (q : Fin m) : ℝ := (-1) ^ q.val

/-- The position parity `Z = diag((-1)^q)`. -/
def parityMat : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal fun q => (sgn m q : ℂ)

/-- The one-coordinate parity kernel `w⁻¹ Z w⁻¹`. -/
def parityKernel : Matrix (Fin m) (Fin m) ℂ := weightInv m * parityMat m * weightInv m

variable {m}

theorem avg_mul_avg (hm : m ≠ 0) : avg m * avg m = avg m := by
  ext q q'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  simp only [avg, Matrix.mul_apply, Matrix.of_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem weight_mul_weightInv (hm : m ≠ 0) : weight m * weightInv m = 1 := by
  simp only [weight, weightInv, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, avg_mul_avg hm]
  module

theorem weightInv_mul_weight (hm : m ≠ 0) : weightInv m * weight m = 1 := by
  simp only [weight, weightInv, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, avg_mul_avg hm]
  module

theorem avg_conjTranspose : (avg m)ᴴ = avg m := by
  ext q q'
  simp [avg, Matrix.conjTranspose_apply]

theorem weight_conjTranspose : (weight m)ᴴ = weight m := by
  simp [weight, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, avg_conjTranspose]

theorem weightInv_conjTranspose : (weightInv m)ᴴ = weightInv m := by
  rw [weightInv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    avg_conjTranspose]
  congr 1
  simp

theorem sgn_sq (q : Fin m) : sgn m q * sgn m q = 1 := by
  simp only [sgn, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem sgn_eq (q : Fin m) : sgn m q = 1 ∨ sgn m q = -1 := by
  rcases neg_one_pow_eq_or ℝ q.val with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem sum_neg_one_pow_even (k : ℕ) : ∑ i ∈ Finset.range (2 * k), (-1 : ℝ) ^ i = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, pow_succ, pow_mul]
      simp

theorem sum_sgn (hm : Even m) : ∑ q : Fin m, sgn m q = 0 := by
  obtain ⟨k, hk⟩ := hm
  have h := Fin.sum_univ_eq_sum_range (fun i => (-1 : ℝ) ^ i) m
  simp only [sgn]
  rw [h, hk, ← two_mul]
  exact sum_neg_one_pow_even k

end Matrices

/-! ### Actions of the one-coordinate matrices -/

section Actions

variable {m : ℕ}

theorem act_avg_apply (φ : Fam (Fin m) V) (q : Fin m) :
    act (avg m) φ q = (m : ℂ)⁻¹ • ∑ q', φ q' := by
  simp [act_apply, avg, Finset.smul_sum]

theorem act_weight (φ : Fam (Fin m) V) :
    act (weight m) φ = (2 : ℂ) • φ - act (avg m) φ := by
  rw [weight, act_sub_matrix, act_smul_matrix, act_one]

theorem act_weightInv (φ : Fam (Fin m) V) :
    act (weightInv m) φ = (1 / 2 : ℂ) • (φ + act (avg m) φ) := by
  rw [weightInv, act_smul_matrix, act_add_matrix, act_one]

/-- `‖P φ‖² = ‖∑ φ‖² / m`. -/
theorem norm_sq_act_avg (hm : m ≠ 0) (φ : Fam (Fin m) V) :
    ‖act (avg m) φ‖ ^ 2 = ‖∑ q, φ q‖ ^ 2 / m := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  rw [norm_sq_fam]
  simp only [act_avg_apply, norm_smul, norm_inv, Complex.norm_natCast, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow]
  field_simp

/-- `⟪φ, P φ⟫ = ‖∑ φ‖² / m`. -/
theorem inner_act_avg (φ : Fam (Fin m) V) :
    ⟪φ, act (avg m) φ⟫_ℂ = ((‖∑ q, φ q‖ ^ 2 / m : ℝ) : ℂ) := by
  rw [inner_fam]
  simp only [act_avg_apply, inner_smul_right]
  rw [← Finset.mul_sum, ← sum_inner, inner_self_cpx]
  push_cast
  ring

omit [InnerProductSpace ℂ V] in
theorem norm_sq_sum_le (φ : Fam (Fin m) V) : ‖∑ q, φ q‖ ^ 2 ≤ m * ‖φ‖ ^ 2 := by
  have h := norm_sum_sq_le (Finset.univ : Finset (Fin m)) (fun q => φ q)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [norm_sq_fam]
  exact h

/-- **The inverse weight is a contraction.** -/
theorem norm_sq_act_weightInv_le (hm : m ≠ 0) (φ : Fam (Fin m) V) :
    ‖act (weightInv m) φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  rw [act_weightInv, norm_smul, mul_pow, norm_add_sq (𝕜 := ℂ), inner_act_avg,
    norm_sq_act_avg hm]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  have hS := norm_sq_sum_le φ
  have hdiv : ‖∑ q, φ q‖ ^ 2 / m ≤ ‖φ‖ ^ 2 := by
    rw [div_le_iff₀ hmR]; linarith
  have hnn : 0 ≤ ‖∑ q, φ q‖ ^ 2 / m := by positivity
  norm_num
  nlinarith

end Actions

/-! ### A query depending on one bit -/

section Bit

variable {m : ℕ}

/-- A query whose action on the value register depends only on the bit `[q = q₀]`. -/
def bitOp (q₀ : Fin m) (V₀ V₁ : V →L[ℂ] V) : Fin m → V →L[ℂ] V :=
  fun q => if q = q₀ then V₁ else V₀

theorem bitOp_apply (q₀ : Fin m) (V₀ V₁ : V →L[ℂ] V) (q : Fin m) (v : V) :
    bitOp q₀ V₀ V₁ q v = V₀ v + (if q = q₀ then (V₁ - V₀) v else 0) := by
  by_cases h : q = q₀ <;> simp [bitOp, h]

theorem joint_sub {X : Type*} (O : X → V →L[ℂ] V) (ψ φ : Fam X V) :
    joint O (ψ - φ) = joint O ψ - joint O φ := by
  ext j; simp

theorem joint_smul {X : Type*} (O : X → V →L[ℂ] V) (z : ℂ) (ψ : Fam X V) :
    joint O (z • ψ) = z • joint O ψ := by
  ext j; simp

/-- The commutator `[P, Ô]` at one position. -/
theorem commutator_apply (q₀ : Fin m) (V₀ V₁ : V →L[ℂ] V) (η : Fam (Fin m) V) (q : Fin m) :
    (act (avg m) (joint (bitOp q₀ V₀ V₁) η) - joint (bitOp q₀ V₀ V₁) (act (avg m) η)) q =
      (m : ℂ)⁻¹ • (V₁ - V₀) (η q₀ - if q = q₀ then ∑ q', η q' else 0) := by
  have hsumO : ∑ q', bitOp q₀ V₀ V₁ q' (η q') = V₀ (∑ q', η q') + (V₁ - V₀) (η q₀) := by
    simp only [bitOp_apply, Finset.sum_add_distrib, map_sum, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  simp only [PiLp.sub_apply, act_avg_apply, joint_apply]
  rw [hsumO]
  by_cases h : q = q₀
  · simp only [h, bitOp, if_true, map_smul, map_sub, FunLike.coe_sub, Pi.sub_apply,
      smul_add, smul_sub]
    abel
  · simp only [h, bitOp, if_false, map_smul, FunLike.coe_sub, Pi.sub_apply, sub_zero,
      smul_add, smul_sub]
    abel

/-- **Commutator bound** `‖[P, Ô] η‖² ≤ (4/m) ‖η‖²` when `V₀`, `V₁` preserve norms. -/
theorem norm_sq_commutator_le (hm : m ≠ 0) (q₀ : Fin m) (V₀ V₁ : V →L[ℂ] V)
    (h₀ : ∀ v, ‖V₀ v‖ = ‖v‖) (h₁ : ∀ v, ‖V₁ v‖ = ‖v‖) (η : Fam (Fin m) V) :
    ‖act (avg m) (joint (bitOp q₀ V₀ V₁) η) - joint (bitOp q₀ V₀ V₁) (act (avg m) η)‖ ^ 2 ≤
      4 / m * ‖η‖ ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  set D := V₁ - V₀
  have hD : ∀ v, ‖D v‖ ^ 2 ≤ 4 * ‖v‖ ^ 2 := by
    intro v
    have : ‖D v‖ ≤ 2 * ‖v‖ := by
      calc ‖D v‖ = ‖V₁ v - V₀ v‖ := rfl
        _ ≤ ‖V₁ v‖ + ‖V₀ v‖ := norm_sub_le _ _
        _ = 2 * ‖v‖ := by rw [h₀, h₁]; ring
    nlinarith [norm_nonneg (D v), norm_nonneg v]
  set S := ∑ q', η q'
  set E := Finset.univ.erase q₀
  have hcard : (E.card : ℝ) = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ m := Nat.pos_of_ne_zero hm
    push_cast [this]
    ring
  have hpt : ∀ q, ‖(act (avg m) (joint (bitOp q₀ V₀ V₁) η) -
      joint (bitOp q₀ V₀ V₁) (act (avg m) η)) q‖ ^ 2 =
      (m : ℝ)⁻¹ ^ 2 * ‖D (η q₀ - if q = q₀ then S else 0)‖ ^ 2 := by
    intro q
    rw [commutator_apply, norm_smul, norm_inv, Complex.norm_natCast, mul_pow]
  rw [norm_sq_fam, Finset.sum_congr rfl (fun q _ => hpt q),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ q₀)]
  have hE : ∑ q ∈ E, (m : ℝ)⁻¹ ^ 2 * ‖D (η q₀ - if q = q₀ then S else 0)‖ ^ 2 =
      (E.card : ℝ) * ((m : ℝ)⁻¹ ^ 2 * ‖D (η q₀)‖ ^ 2) := by
    rw [Finset.sum_congr rfl (g := fun _ => (m : ℝ)⁻¹ ^ 2 * ‖D (η q₀)‖ ^ 2), Finset.sum_const,
      nsmul_eq_mul]
    intro q hq
    rw [if_neg (Finset.ne_of_mem_erase hq), sub_zero]
  rw [hE, if_pos rfl]
  have hS : η q₀ - S = -∑ q ∈ E, η q := by
    have hS' : S = η q₀ + ∑ q ∈ E, η q :=
      (Finset.add_sum_erase _ (fun q => η q) (Finset.mem_univ q₀)).symm
    rw [hS']
    abel
  rw [hS]
  have hA := hD (-∑ q ∈ E, η q)
  have hB := hD (η q₀)
  have hC := norm_sum_sq_le E (fun q => η q)
  rw [norm_neg] at hA
  rw [norm_sq_fam, ← Finset.add_sum_erase _ (fun q => ‖η q‖ ^ 2) (Finset.mem_univ q₀)]
  rw [hcard] at hC ⊢
  have hinv : 0 ≤ (m : ℝ)⁻¹ ^ 2 := by positivity
  have hE0 : 0 ≤ ∑ q ∈ E, ‖η q‖ ^ 2 := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hq0 : 0 ≤ ‖η q₀‖ ^ 2 := sq_nonneg _
  have hm1' : (0 : ℝ) ≤ m - 1 := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.pos_of_ne_zero hm
    linarith
  have e1 : (m : ℝ)⁻¹ ^ 2 * ‖D (-∑ q ∈ E, η q)‖ ^ 2 ≤
      (m : ℝ)⁻¹ ^ 2 * (4 * ((m - 1) * ∑ q ∈ E, ‖η q‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hC (by norm_num))) hinv
  have e2 : (m - 1) * ((m : ℝ)⁻¹ ^ 2 * ‖D (η q₀)‖ ^ 2) ≤
      (m - 1) * ((m : ℝ)⁻¹ ^ 2 * (4 * ‖η q₀‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hinv) hm1'
  have hm1 : (m : ℝ)⁻¹ ^ 2 * (m - 1) ≤ (m : ℝ)⁻¹ := by
    rw [sq, mul_assoc]
    apply mul_le_of_le_one_right (inv_nonneg.mpr hmR.le)
    rw [inv_mul_le_iff₀ hmR]
    linarith
  have key : (m : ℝ)⁻¹ ^ 2 * ‖D (-∑ q ∈ E, η q)‖ ^ 2 +
      (m - 1) * ((m : ℝ)⁻¹ ^ 2 * ‖D (η q₀)‖ ^ 2) ≤
      4 * ((m : ℝ)⁻¹ ^ 2 * (m - 1)) * (‖η q₀‖ ^ 2 + ∑ q ∈ E, ‖η q‖ ^ 2) := by
    nlinarith
  calc _ ≤ 4 * ((m : ℝ)⁻¹ ^ 2 * (m - 1)) * (‖η q₀‖ ^ 2 + ∑ q ∈ E, ‖η q‖ ^ 2) := key
    _ ≤ 4 * (m : ℝ)⁻¹ * (‖η q₀‖ ^ 2 + ∑ q ∈ E, ‖η q‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ (add_nonneg hq0 hE0)
      linarith
    _ = 4 / m * (‖η q₀‖ ^ 2 + ∑ q ∈ E, ‖η q‖ ^ 2) := by ring

/-- **One-coordinate weight growth** for a single-bit query: `‖w Ô φ‖ ≤ (1 + 2/√m) ‖w φ‖`. -/
theorem weight_growth_bit (hm : m ≠ 0) (q₀ : Fin m) (V₀ V₁ : V →L[ℂ] V)
    (h₀ : ∀ v, ‖V₀ v‖ = ‖v‖) (h₁ : ∀ v, ‖V₁ v‖ = ‖v‖) (φ : Fam (Fin m) V) :
    ‖act (weight m) (joint (bitOp q₀ V₀ V₁) φ)‖ ≤
      (1 + 2 / Real.sqrt m) * ‖act (weight m) φ‖ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  set ξ := act (weight m) φ with hξ
  have hφ : φ = act (weightInv m) ξ := by
    rw [hξ, ← act_mul, weightInv_mul_weight hm, act_one]
  set O := bitOp q₀ V₀ V₁
  have hO : ∀ v (q : Fin m), ‖O q v‖ = ‖v‖ := by
    intro v q
    by_cases h : q = q₀
    · simp only [O, bitOp, h, if_true, h₁]
    · simp only [O, bitOp, h, if_false, h₀]
  have hid : act (weight m) (joint O φ) =
      joint O ξ - (act (avg m) (joint O φ) - joint O (act (avg m) φ)) := by
    rw [hξ, act_weight, act_weight, joint_sub, joint_smul]
    abel
  have hcomm := norm_sq_commutator_le hm q₀ V₀ V₁ h₀ h₁ φ
  have hcomm' : ‖act (avg m) (joint O φ) - joint O (act (avg m) φ)‖ ≤
      2 / Real.sqrt m * ‖φ‖ := by
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
    have hrhs : 0 ≤ 2 / Real.sqrt m * ‖φ‖ := by positivity
    apply le_of_sq_le_sq _ hrhs
    · rw [mul_pow, div_pow, Real.sq_sqrt hmR.le]
      norm_num
      linarith [hcomm]
  have hφξ : ‖φ‖ ≤ ‖ξ‖ := by
    have := norm_sq_act_weightInv_le hm ξ
    rw [← hφ] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  rw [hid]
  calc ‖joint O ξ - (act (avg m) (joint O φ) - joint O (act (avg m) φ))‖
      ≤ ‖joint O ξ‖ + ‖act (avg m) (joint O φ) - joint O (act (avg m) φ)‖ := norm_sub_le _ _
    _ ≤ ‖ξ‖ + 2 / Real.sqrt m * ‖ξ‖ := by
      rw [norm_joint O (fun q v => hO v q)]
      gcongr
      exact hcomm'.trans (mul_le_mul_of_nonneg_left hφξ (by positivity))
    _ = (1 + 2 / Real.sqrt m) * ‖ξ‖ := by ring

end Bit

/-! ### Parity -/

/-- The parity sign `(-1)^{F(j)} = ∏_b (-1)^{j b}` of hidden inputs `j : ι → Fin m`. -/
def parSign {ι : Type*} [Fintype ι] {m : ℕ} (j : ι → Fin m) : ℝ := ∏ b, sgn m (j b)

section Parity

variable {m : ℕ}

theorem act_parityMat_apply (η : Fam (Fin m) V) (q : Fin m) :
    act (parityMat m) η q = (sgn m q : ℂ) • η q := by
  simp [act_apply, parityMat, Matrix.diagonal_apply]

/-- Explicit action of `w⁻¹ Z w⁻¹` for even `m`. -/
theorem act_parityKernel_apply (hm : Even m) (ξ : Fam (Fin m) V) (q : Fin m) :
    act (parityKernel m) ξ q = (1 / 4 : ℂ) • ((sgn m q : ℂ) • ξ q +
      (sgn m q : ℂ) • ((m : ℂ)⁻¹ • ∑ q', ξ q') +
      (m : ℂ)⁻¹ • ∑ q', (sgn m q' : ℂ) • ξ q') := by
  rw [parityKernel, act_mul, act_mul, act_weightInv]
  simp only [PiLp.smul_apply, PiLp.add_apply, act_avg_apply, act_parityMat_apply,
    act_weightInv]
  have hsum : ∑ q', (sgn m q' : ℂ) • (1 / 2 : ℂ) • (ξ q' + (m : ℂ)⁻¹ • ∑ q'', ξ q'') =
      (1 / 2 : ℂ) • ∑ q', (sgn m q' : ℂ) • ξ q' := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
    have h0 : ∑ q' : Fin m, (sgn m q' : ℂ) = 0 := by exact_mod_cast sum_sgn hm
    simp only [smul_comm (_ : ℂ) (1 / 2 : ℂ), ← Finset.smul_sum, h0,
      zero_smul, smul_zero, add_zero]
  rw [hsum]
  simp only [smul_add, smul_smul]
  module

/-- Bessel's inequality for the two orthogonal vectors `u` and `Z u`. -/
theorem bessel_parity (hm : Even m) (ξ : Fam (Fin m) V) :
    ‖∑ q, ξ q‖ ^ 2 + ‖∑ q, (sgn m q : ℂ) • ξ q‖ ^ 2 ≤ m * ‖ξ‖ ^ 2 := by
  set e : Fin m → ℝ := fun q => (1 + sgn m q) / 2
  set o : Fin m → ℝ := fun q => (1 - sgn m q) / 2
  have he : ∀ q, e q = 0 ∨ e q = 1 := by
    intro q; rcases sgn_eq q with h | h <;> simp [e, h]
  have ho : ∀ q, o q = 0 ∨ o q = 1 := by
    intro q; rcases sgn_eq q with h | h <;> simp [o, h]
  have hs := sum_sgn hm
  have hesum : ∑ q, e q = m / 2 := by
    simp only [e, ← Finset.sum_div, Finset.sum_add_distrib, hs, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, add_zero]
  have hosum : ∑ q, o q = m / 2 := by
    simp only [o, ← Finset.sum_div, Finset.sum_sub_distrib, hs, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, sub_zero]
  set Ev := ∑ q, e q • ξ q
  set Od := ∑ q, o q • ξ q
  have hS0 : ∑ q, ξ q = Ev + Od := by
    simp only [Ev, Od, ← Finset.sum_add_distrib, ← add_smul, e, o]
    apply Finset.sum_congr rfl; intro q _; rw [show (1 + sgn m q) / 2 + (1 - sgn m q) / 2 = 1 by
      ring, one_smul]
  have hS1 : ∑ q, (sgn m q : ℂ) • ξ q = Ev - Od := by
    simp only [Ev, Od, ← Finset.sum_sub_distrib, ← sub_smul, e, o]
    apply Finset.sum_congr rfl; intro q _
    rw [show (1 + sgn m q) / 2 - (1 - sgn m q) / 2 = sgn m q by ring]
    rfl
  have hE := norm_sum_indicator_sq_le Finset.univ e he (fun q => ξ q)
  have hO := norm_sum_indicator_sq_le Finset.univ o ho (fun q => ξ q)
  rw [hesum] at hE
  rw [hosum] at hO
  rw [hS0, hS1, parallelogram_law_with_norm ℂ, norm_sq_fam]
  have htot : ∑ q, e q * ‖ξ q‖ ^ 2 + ∑ q, o q * ‖ξ q‖ ^ 2 = ∑ q, ‖ξ q‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro q _; simp only [e, o]; ring
  nlinarith

/-- **Parity bound** `‖w⁻¹ Z w⁻¹ ξ‖² ≤ ‖ξ‖²/4` for even `m`. -/
theorem norm_sq_act_parityKernel_le (hm : Even m) (hm0 : m ≠ 0) (ξ : Fam (Fin m) V) :
    ‖act (parityKernel m) ξ‖ ^ 2 ≤ 1 / 4 * ‖ξ‖ ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  set S0 := ∑ q, ξ q
  set S1 := ∑ q, (sgn m q : ℂ) • ξ q
  set ζ : Fam (Fin m) V := WithLp.toLp 2 (fun q => (sgn m q : ℂ) • ξ q)
  set α : Fam (Fin m) V := WithLp.toLp 2 (fun q => (sgn m q : ℂ) • ((m : ℂ)⁻¹ • S0))
  set β : Fam (Fin m) V := WithLp.toLp 2 (fun _ => (m : ℂ)⁻¹ • S1)
  have hform : act (parityKernel m) ξ = (1 / 4 : ℂ) • (ζ + α + β) := by
    ext q
    rw [act_parityKernel_apply hm]
    rfl
  have hsC : ∀ q, (starRingEnd ℂ) (sgn m q : ℂ) * (sgn m q : ℂ) = 1 := by
    intro q
    rw [Complex.conj_ofReal]
    exact_mod_cast sgn_sq q
  have hsum0 : ∑ q : Fin m, (sgn m q : ℂ) = 0 := by exact_mod_cast sum_sgn hm
  have hζ : ‖ζ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [norm_sq_fam, norm_sq_fam]
    apply Finset.sum_congr rfl; intro q _
    change ‖(sgn m q : ℂ) • ξ q‖ ^ 2 = _
    rw [norm_smul]
    rcases sgn_eq q with h | h <;> simp [h]
  have hα : ‖α‖ ^ 2 = ‖S0‖ ^ 2 / m := by
    rw [norm_sq_fam]
    have : ∀ q : Fin m, ‖α q‖ ^ 2 = (m : ℝ)⁻¹ ^ 2 * ‖S0‖ ^ 2 := by
      intro q
      change ‖(sgn m q : ℂ) • ((m : ℂ)⁻¹ • S0)‖ ^ 2 = _
      rw [norm_smul, norm_smul, norm_inv, Complex.norm_natCast]
      rcases sgn_eq q with h | h <;> simp [h, mul_pow]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hβ : ‖β‖ ^ 2 = ‖S1‖ ^ 2 / m := by
    rw [norm_sq_fam]
    have : ∀ q : Fin m, ‖β q‖ ^ 2 = (m : ℝ)⁻¹ ^ 2 * ‖S1‖ ^ 2 := by
      intro q
      change ‖(m : ℂ)⁻¹ • S1‖ ^ 2 = _
      rw [norm_smul, norm_inv, Complex.norm_natCast, mul_pow]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hζα : ⟪ζ, α⟫_ℂ = ((‖S0‖ ^ 2 / m : ℝ) : ℂ) := by
    rw [inner_fam]
    change ∑ q, ⟪(sgn m q : ℂ) • ξ q, (sgn m q : ℂ) • ((m : ℂ)⁻¹ • S0)⟫_ℂ = _
    have hpt : ∀ q, ⟪(sgn m q : ℂ) • ξ q, (sgn m q : ℂ) • ((m : ℂ)⁻¹ • S0)⟫_ℂ =
        (m : ℂ)⁻¹ * ⟪ξ q, S0⟫_ℂ := by
      intro q
      rw [inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal]
      have hC : (sgn m q : ℂ) * (sgn m q : ℂ) = 1 := by exact_mod_cast sgn_sq q
      calc (sgn m q : ℂ) * ((sgn m q : ℂ) * ((m : ℂ)⁻¹ * ⟪ξ q, S0⟫_ℂ)) =
          ((sgn m q : ℂ) * (sgn m q : ℂ)) * ((m : ℂ)⁻¹ * ⟪ξ q, S0⟫_ℂ) := by ring
        _ = _ := by rw [hC, one_mul]
    rw [Finset.sum_congr rfl (fun q _ => hpt q), ← Finset.mul_sum, ← sum_inner, inner_self_cpx]
    push_cast
    ring
  have hζβ : ⟪ζ, β⟫_ℂ = ((‖S1‖ ^ 2 / m : ℝ) : ℂ) := by
    rw [inner_fam]
    change ∑ q, ⟪(sgn m q : ℂ) • ξ q, (m : ℂ)⁻¹ • S1⟫_ℂ = _
    simp only [inner_smul_right]
    rw [← Finset.mul_sum, ← sum_inner]
    have : ∑ q, (sgn m q : ℂ) • ξ q = S1 := rfl
    rw [this, inner_self_cpx]
    push_cast
    ring
  have hαβ : ⟪α, β⟫_ℂ = 0 := by
    rw [inner_fam]
    change ∑ q, ⟪(sgn m q : ℂ) • ((m : ℂ)⁻¹ • S0), (m : ℂ)⁻¹ • S1⟫_ℂ = 0
    simp only [inner_smul_left, Complex.conj_ofReal]
    rw [← Finset.sum_mul, hsum0, zero_mul]
  have hexp : ‖ζ + α + β‖ ^ 2 = ‖ξ‖ ^ 2 + 3 * ((‖S0‖ ^ 2 + ‖S1‖ ^ 2) / m) := by
    rw [norm_add_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ), inner_add_left, hζα, hζβ, hαβ, hζ, hα, hβ]
    simp only [RCLike.re_to_complex, Complex.ofReal_re, add_zero]
    ring
  have hB := bessel_parity hm ξ
  rw [hform, norm_smul, mul_pow, hexp]
  have hB' : (‖S0‖ ^ 2 + ‖S1‖ ^ 2) / m ≤ ‖ξ‖ ^ 2 := by
    rw [div_le_iff₀ hmR]; linarith
  have h4 : ‖(1 / 4 : ℂ)‖ ^ 2 = 1 / 16 := by norm_num
  rw [h4]
  nlinarith

end Parity

end

end LinearSystemLowerBound
