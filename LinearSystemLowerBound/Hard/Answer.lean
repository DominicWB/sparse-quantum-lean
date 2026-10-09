import LinearSystemLowerBound.Hard.Dilation
import SparseHamiltonian.ODEStateNormalization

/-!
# The answer region and its decoder

The decoder measures the sector, the clock and the gadget position; in the solution sector
and the answer region (clock values `t ≥ n`) it reports the position parity, otherwise a
uniformly random bit.  Its correlation observable is the diagonal operator `M` with entries
`(-1)^a` on `(true, t, a)`, `t ≥ n`, and `0` elsewhere (`decoder`); `‖M‖ ≤ 1`.

* `inner_sol_decoder`: `⟨y, M y⟩ = (-1)^{F(x)} ∑_{t ≥ n} 4 r^{2t}`, since on the answer region
  the history state carries the logical parity `F(x)`.
* `norm_sq_sol`: `‖y‖² = ∑_t 4 r^{2t}`.
* `answer_correlation`: for `T + 1 = 2n` the normalised solution satisfies
  `Re⟨x̂, M x̂⟩ = (-1)^{F(x)} p` with `p = r^{2n} / (1 + r^{2n})` (paper, equation
  `qlsl:eq:p`).
-/

namespace LinearSystemLowerBound.Hard

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
open LinearSystemLowerBound SparseHamiltonian

variable {n m T : ℕ} [NeZero m]

/-- The decoder observable: `(-1)^a` on the answer region `(true, t ≥ n, a)`. -/
def decoderEntry (n : ℕ) (p : Idx T m) : ℝ :=
  if p.1 = true ∧ n ≤ p.2.1.val then sgn m p.2.2 else 0

/-- The decoder observable as an operator. -/
def decoder (n T m : ℕ) [NeZero m] : EuclideanSpace ℂ (Idx T m) →L[ℂ] EuclideanSpace ℂ (Idx T m) :=
  SparseStateOverlap.matrixOperator (Matrix.diagonal fun p => (decoderEntry (T := T) (m := m) n p : ℂ))

omit [NeZero m] in
theorem decoderEntry_abs_le (p : Idx T m) : |decoderEntry (T := T) (m := m) n p| ≤ 1 := by
  unfold decoderEntry
  split_ifs
  · rcases sgn_eq (m := m) p.2.2 with h | h <;> simp [h]
  · simp

theorem decoder_apply (v : EuclideanSpace ℂ (Idx T m)) (p : Idx T m) :
    decoder n T m v p = (decoderEntry (T := T) (m := m) n p : ℂ) * v p := by
  simp [decoder, SparseStateOverlap.matrixOperator_apply, Matrix.diagonal_apply]

theorem decoder_norm_le (v : EuclideanSpace ℂ (Idx T m)) : ‖decoder n T m v‖ ≤ ‖v‖ := by
  have h : ‖decoder n T m v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro p _
    rw [decoder_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    have h1 := decoderEntry_abs_le (n := n) (T := T) (m := m) p
    have h2 : |decoderEntry (T := T) (m := m) n p| ^ 2 ≤ 1 := by
      have := abs_nonneg (decoderEntry (T := T) (m := m) n p)
      nlinarith
    nlinarith [sq_nonneg ‖v p‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-! ### The solution on the answer region -/

theorem norm_sq_sol (hm : Even m) (r : ℝ) (x : Fin n → Fin m) :
    ‖(sol (T := T) r x : EuclideanSpace ℂ (Idx T m))‖ ^ 2 =
      ∑ t : Fin (T + 1), 4 * r ^ (2 * t.val) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sol, PiLp.toLp_apply, if_true,
    Bool.false_eq_true, if_false, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro t _
  simp only [norm_mul, mul_pow, ← Finset.mul_sum, sum_logical_sq hm _ (prefixSign_pm x t.val),
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

theorem re_inner_decoder (v : EuclideanSpace ℂ (Idx T m)) :
    (⟪v, decoder n T m v⟫_ℂ).re = ∑ p, decoderEntry (T := T) (m := m) n p * ‖v p‖ ^ 2 := by
  rw [inner_fam, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [decoder_apply, ← smul_eq_mul, inner_smul_right, inner_self_cpx, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul, Complex.ofReal_re]

theorem inner_sol_decoder (hm : Even m) (r : ℝ) (x : Fin n → Fin m) :
    (⟪(sol (T := T) r x : EuclideanSpace ℂ (Idx T m)),
      decoder n T m (sol r x)⟫_ℂ).re =
      parSign x * ∑ t : Fin (T + 1), if n ≤ t.val then 4 * r ^ (2 * t.val) else 0 := by
  rw [re_inner_decoder]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, sol, PiLp.toLp_apply, if_true,
    Bool.false_eq_true, if_false, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, Finset.sum_const_zero, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : n ≤ t.val
  · simp only [decoderEntry, ht, and_self, if_true]
    have e : ∀ a : Fin m, sgn m a * ‖((2 * r ^ t.val : ℝ) : ℂ) *
        logical (prefixSign x t.val) a‖ ^ 2 =
        4 * r ^ (2 * t.val) * (sgn m a * ‖logical (prefixSign x t.val) a‖ ^ 2) := by
      intro a
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, pow_mul]
      ring
    simp only [e]
    rw [← Finset.mul_sum, sum_sgn_logical_sq hm _ (prefixSign_pm x t.val),
      prefixSign_of_le x t.val ht]
    ring
  · simp only [decoderEntry, ht, and_false, if_false, zero_mul, Finset.sum_const_zero,
      mul_zero]

/-! ### The answer probability -/

theorem sum_clock_split (r : ℝ) (hT : T + 1 = 2 * n) :
    ∑ t : Fin (T + 1), 4 * r ^ (2 * t.val) = 4 * (1 + r ^ (2 * n)) *
        ∑ k ∈ Finset.range n, r ^ (2 * k) ∧
      ∑ t : Fin (T + 1), (if n ≤ t.val then 4 * r ^ (2 * t.val) else 0) =
        4 * r ^ (2 * n) * ∑ k ∈ Finset.range n, r ^ (2 * k) := by
  have h1 : ∀ f : ℕ → ℝ, ∑ t : Fin (T + 1), f t.val = ∑ k ∈ Finset.range (n + n), f k := by
    intro f
    rw [Fin.sum_univ_eq_sum_range f (T + 1), hT, two_mul]
  constructor
  · rw [h1 (fun k => 4 * r ^ (2 * k)), Finset.sum_range_add, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [show 2 * (n + k) = 2 * n + 2 * k by ring, pow_add]
    ring
  · rw [h1 (fun k => if n ≤ k then 4 * r ^ (2 * k) else 0), Finset.sum_range_add]
    have hlow : ∑ k ∈ Finset.range n, (if n ≤ k then 4 * r ^ (2 * k) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]
    rw [hlow, zero_add, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [if_pos (by omega), show 2 * (n + k) = 2 * n + 2 * k by ring, pow_add]
    ring

/-- The answer probability `p = r^{2n} / (1 + r^{2n})`. -/
def answerProb (r : ℝ) (n : ℕ) : ℝ := r ^ (2 * n) / (1 + r ^ (2 * n))

/-- **Answer correlation** of the normalised solution:
`Re⟨x̂, M x̂⟩ = (-1)^{F(x)} r^{2n}/(1 + r^{2n})`. -/
theorem answer_correlation (hm : Even m) (hn : 0 < n) (hT : T + 1 = 2 * n) (r : ℝ)
    (hr : 0 < r) (x : Fin n → Fin m) :
    (⟪ODEStateNormalization.unitDirection (sol (T := T) r x : EuclideanSpace ℂ (Idx T m)),
      decoder n T m (ODEStateNormalization.unitDirection (sol r x))⟫_ℂ).re =
      parSign x * answerProb r n := by
  obtain ⟨hall, hans⟩ := sum_clock_split (T := T) r hT
  have hS : 0 < ∑ k ∈ Finset.range n, r ^ (2 * k) :=
    Finset.sum_pos (fun k _ => by positivity) ⟨0, Finset.mem_range.mpr hn⟩
  have hnorm := norm_sq_sol (T := T) hm r x
  rw [hall] at hnorm
  set u : EuclideanSpace ℂ (Idx T m) := sol (T := T) r x
  have hinner := inner_sol_decoder (T := T) (n := n) hm r x
  rw [hans] at hinner
  have hu : ODEStateNormalization.unitDirection u = ((‖u‖⁻¹ : ℝ) : ℂ) • u := by
    simp only [ODEStateNormalization.unitDirection, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl
  rw [hu, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc,
    ← Complex.ofReal_mul, Complex.re_ofReal_mul, hinner]
  have hn2 : ‖u‖⁻¹ * ‖u‖⁻¹ = 1 / (4 * (1 + r ^ (2 * n)) * ∑ k ∈ Finset.range n, r ^ (2 * k)) := by
    rw [← hnorm, ← mul_inv, ← sq, one_div]
  rw [hn2, answerProb]
  have h1 : 0 < 1 + r ^ (2 * n) := by positivity
  field_simp

end

end LinearSystemLowerBound.Hard
