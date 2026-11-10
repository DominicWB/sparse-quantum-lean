import ODELowerBoundExtensions.Psd.Readout

/-!
# Gadget-family words and locators

Manuscript: the proof of Theorem `odel:thm:psd` (dyadic entries, public
supports, sparsity at most `2m + 1`). The PSD generator `psdSearchMat` is packaged with the
Hamiltonian lower bound's one-bit builder `Hamiltonian.bitData` (next module); this module gives
its word table and its location lists.

**Locators** (input-independent, the "public supports" of Theorem `odel:thm:psd`). Core row
`p = (k, a)` lists the successor block in slots `t < m` and the predecessor block in slots
`m ≤ t < 2m` exactly as `Hamiltonian.searchLocFun`, and **itself in slot `2m`** (the diagonal `1/2`
of `(I - H)/2`); all other slots are padding indices. Reference and padding rows are those of
`Hamiltonian.fullLoc`. Injectivity needs `n ≥ 1` (for `n = 0` the successor of `k` is `k`).

**Words** with `B = F + μ + σ + 1` (`F = psdBits n u`, `m = 2^μ`, `σ = ⌈log₂ s⌉`), read through
the position-independent decode `valMinAbs z / 2^B` (`Hamiltonian.wordDecode`):

* gadget entry `-½ b'_k (2/m - y)` of membership bit `y`: word `-N_k (2 - 2^μ y) 2^σ`
  (the address is `Hamiltonian.searchAddr`, the bit of the Hamiltonian family);
* diagonal `1/2` of a path vertex: word `2^{F+μ+σ}` (known, no query);
* padding entry `2^{-σ}`: word `2^{F+μ+1}`; eigenvalue-one vertex: word `2^B`.

Every word lies in `(-2^B, 2^B]` for every `μ` (`psdSearchTable_bound`: `|2 - 2^μ y| ≤ 2^{μ+1}`
and `N_k < 2^F`, so a gadget word has absolute value below `2^{F+μ+1+σ} = 2^B`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds SparseLowerBounds.Hamiltonian

/-! ### Locators -/

/-- The PSD gadget-family row list of core row `p`: `Hamiltonian.searchLocFun` with the
diagonal in slot `2m`. -/
def psdSearchLocFun (n μ s : ℕ) (p : SearchCore n μ) (t : Fin s) : SearchIndex n μ s :=
  if (t : ℕ) = 2 * 2 ^ μ then Sum.inl p else searchLocFun n μ s p t

/-- The row list is injective for `n ≥ 1`. -/
theorem psdSearchLocFun_injective {n : ℕ} (μ s : ℕ) (hn : 1 ≤ n) (p : SearchCore n μ) :
    Function.Injective (psdSearchLocFun n μ s p) := by
  have hk := p.1.isLt
  have h1 : ((p.1 : ℕ) + 1) % (n + 1) ≠ p.1 := by
    rw [HardDataScalar.mod_of_lt_two_mul (by omega : (p.1 : ℕ) + 1 < 2 * (n + 1))]
    split_ifs <;> omega
  have h2 : ((p.1 : ℕ) + n) % (n + 1) ≠ p.1 := by
    rw [HardDataScalar.mod_of_lt_two_mul (by omega : (p.1 : ℕ) + n < 2 * (n + 1))]
    split_ifs <;> omega
  -- off the diagonal slot, the Hamiltonian row list never lists the row itself
  have key : ∀ t : Fin s, searchLocFun n μ s p t ≠ Sum.inl p := by
    intro t he
    unfold searchLocFun at he
    split_ifs at he
    · simp only [Sum.inl.injEq, Prod.ext_iff, Fin.ext_iff] at he
      exact h1 he.1
    · simp only [Sum.inl.injEq, Prod.ext_iff, Fin.ext_iff] at he
      exact h2 he.1
  intro t₁ t₂ h
  unfold psdSearchLocFun at h
  apply Fin.ext
  split_ifs at h with ha hb hb
  · omega
  · exact absurd h.symm (key t₂)
  · exact absurd h (key t₁)
  · exact congrArg Fin.val (searchLocFun_injective n μ s p h)

/-- The PSD gadget-family row list of core row `p`, as an embedding. -/
def psdSearchLoc (n μ s : ℕ) (hn : 1 ≤ n) (p : SearchCore n μ) : Fin s ↪ SearchIndex n μ s :=
  ⟨psdSearchLocFun n μ s p, psdSearchLocFun_injective μ s hn p⟩

/-! ### Words -/

/-- Fractional bits of the PSD gadget-family words, `B = F + μ + ⌈log₂ s⌉ + 1`. -/
def psdSearchBits (n μ s : ℕ) (u : ℝ) : ℕ := psdBits n u + μ + padExp s + 1

/-- The integer words of the PSD gadget-family generator at scale `2^B`. -/
def psdSearchWord (n μ s : ℕ) (u : ℝ) : SearchIndex n μ s × SearchIndex n μ s → Bool → ℤ
  | (Sum.inl p, Sum.inl q), y =>
    if p = q then 2 ^ (psdBits n u + μ + padExp s)
    else if (p.1 : ℕ) = q.1 + 1 then
      -((psdNum n u q.1 : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s)
    else if (q.1 : ℕ) = p.1 + 1 then
      -((psdNum n u p.1 : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s)
    else 0
  | (Sum.inr (Sum.inl r), Sum.inr (Sum.inl r')), _ =>
    if r = 1 ∧ r' = 1 then 2 ^ psdSearchBits n μ s u else 0
  | (Sum.inr (Sum.inr _), Sum.inr (Sum.inr _)), _ => 2 ^ (psdBits n u + μ + 1)
  | _, _ => 0

/-- The PSD gadget-family word table: the addresses (membership bits) of the Hamiltonian
gadget family, `Hamiltonian.searchAddr`, and the words `psdSearchWord`. -/
def psdSearchTable (n μ s : ℕ) (u : ℝ) :
    BitTable (Fin n × Fin (2 ^ μ)) (SearchIndex n μ s × SearchIndex n μ s) :=
  ⟨searchAddr n μ s, psdSearchWord n μ s u⟩

variable {n μ s : ℕ} {u : ℝ}

/-- **The words are in the decode range** `(-2^B, 2^B]`. -/
theorem psdSearchTable_bound (ad : SearchIndex n μ s × SearchIndex n μ s)
    (y : Bool) :
    -(2 : ℤ) ^ psdSearchBits n μ s u < (psdSearchTable n μ s u).word ad y ∧
      (psdSearchTable n μ s u).word ad y ≤ 2 ^ psdSearchBits n μ s u := by
  have hB : (2 : ℤ) ^ psdSearchBits n μ s u =
      2 ^ psdBits n u * (2 * 2 ^ μ) * 2 ^ padExp s := by
    rw [psdSearchBits, pow_succ, pow_add, pow_add]; ring
  have hM : (1 : ℤ) ≤ 2 ^ μ := one_le_pow₀ (by norm_num)
  have hS : (0 : ℤ) < 2 ^ padExp s := by positivity
  -- gadget words: `|N (2 - 2^μ c) 2^σ| ≤ N 2^{μ+1} 2^σ < 2^B` for `c ∈ {0, 1}`
  have hgad : ∀ (k : ℕ) (c : ℤ), (c = 0 ∨ c = 1) →
      |(psdNum n u k : ℤ) * (2 - 2 ^ μ * c) * 2 ^ padExp s| < 2 ^ psdSearchBits n μ s u := by
    intro k c hc
    have hN : (psdNum n u k : ℤ) < 2 ^ psdBits n u := by exact_mod_cast psdNum_lt n u k
    have hN0 : (0 : ℤ) ≤ psdNum n u k := by positivity
    have h2 : |(2 : ℤ) - 2 ^ μ * c| ≤ 2 * 2 ^ μ := by
      rcases hc with rfl | rfl <;> rw [abs_le] <;> constructor <;> linarith
    rw [abs_mul, abs_mul, abs_of_nonneg hN0, abs_of_pos hS, hB]
    calc (psdNum n u k : ℤ) * |2 - 2 ^ μ * c| * 2 ^ padExp s
        ≤ (psdNum n u k : ℤ) * (2 * 2 ^ μ) * 2 ^ padExp s := by gcongr
      _ < 2 ^ psdBits n u * (2 * 2 ^ μ) * 2 ^ padExp s := by
        apply mul_lt_mul_of_pos_right _ hS
        exact mul_lt_mul_of_pos_right hN (by positivity)
  have hw : ∀ k : ℕ,
      -(2 : ℤ) ^ psdSearchBits n μ s u <
          -((psdNum n u k : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s) ∧
        -((psdNum n u k : ℤ) * (2 - 2 ^ μ * (if y then 1 else 0)) * 2 ^ padExp s) ≤
          2 ^ psdSearchBits n μ s u := by
    intro k
    have := abs_lt.mp (hgad k (if y then 1 else 0) (by cases y <;> simp))
    constructor <;> linarith [this.1, this.2]
  have hdiag : (2 : ℤ) ^ (psdBits n u + μ + padExp s) ≤ 2 ^ psdSearchBits n μ s u :=
    pow_le_pow_right₀ (by norm_num) (by unfold psdSearchBits; omega)
  have hpad : (2 : ℤ) ^ (psdBits n u + μ + 1) ≤ 2 ^ psdSearchBits n μ s u :=
    pow_le_pow_right₀ (by norm_num) (by unfold psdSearchBits; omega)
  have hd0 : (0 : ℤ) < 2 ^ (psdBits n u + μ + padExp s) := by positivity
  have hp0 : (0 : ℤ) < 2 ^ (psdBits n u + μ + 1) := by positivity
  have hB0 : (0 : ℤ) < 2 ^ psdSearchBits n μ s u := by positivity
  obtain ⟨p | r | t, q | r' | t'⟩ := ad <;> simp only [psdSearchTable, psdSearchWord]
  · by_cases hpq : p = q
    · rw [if_pos hpq]
      exact ⟨by linarith, hdiag⟩
    rw [if_neg hpq]
    by_cases h1 : (p.1 : ℕ) = q.1 + 1
    · rw [if_pos h1]
      exact hw _
    rw [if_neg h1]
    by_cases h2 : (q.1 : ℕ) = p.1 + 1
    · rw [if_pos h2]
      exact hw _
    rw [if_neg h2]
    constructor <;> linarith
  all_goals first
    | (constructor <;> linarith)
    | (split_ifs <;> constructor <;> linarith)

end

end ODELowerBoundExtensions.Psd
