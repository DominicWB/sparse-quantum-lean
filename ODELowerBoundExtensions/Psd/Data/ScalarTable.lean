import ODELowerBoundExtensions.Psd.Readout

/-!
# Scalar-family words and locators

Manuscript lines 4063-4077 and 4119-4121 (the gadgets
replaced by scalar signs; the PSD matrix is three-sparse). Word table and location lists of
`psdScalarMat`, packaged by `Hamiltonian.bitData` in the next module.

**Locators** (input-independent). Core row `k` lists `k + 1` in slot `0` and `k - 1` in slot `1`
exactly as `Hamiltonian.scalarLocFun`, and **itself in slot `2`** (the diagonal `1/2`); all
other slots are padding indices. Injectivity needs `n ≥ 1`.

**Words** with `B = F + σ + 1` (`F = psdBits n u`, `σ = ⌈log₂ s⌉`):

* signed edge entry `-½ b'_k (-1)^{x_k}`: word `-(-1)^{x_k} N_k 2^σ` (address
  `Hamiltonian.scalarAddr`, bit `k`);
* diagonal `1/2`: word `2^{F+σ}`; padding entry `2^{-σ}`: word `2^{F+1}`; eigenvalue one: `2^B`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds SparseLowerBounds.Hamiltonian

/-! ### Locators -/

/-- The PSD scalar-family row list of core row `k`: `Hamiltonian.scalarLocFun` with the
diagonal in slot `2`. -/
def psdScalarLocFun (n s : ℕ) (k : Fin (n + 1)) (t : Fin s) : ScalarIndex n s :=
  if (t : ℕ) = 2 then Sum.inl k else scalarLocFun n s k t

/-- The row list is injective for `n ≥ 1`. -/
theorem psdScalarLocFun_injective {n : ℕ} (s : ℕ) (hn : 1 ≤ n) (k : Fin (n + 1)) :
    Function.Injective (psdScalarLocFun n s k) := by
  intro t₁ t₂ h
  have hk := k.isLt
  have h1 : ((k : ℕ) + 1) % (n + 1) ≠ k := by
    rw [HardDataScalar.mod_of_lt_two_mul (by omega : (k : ℕ) + 1 < 2 * (n + 1))]
    split_ifs <;> omega
  have h2 : 2 ≤ n → ((k : ℕ) + n) % (n + 1) ≠ k := fun hn2 => by
    rw [HardDataScalar.mod_of_lt_two_mul (by omega : (k : ℕ) + n < 2 * (n + 1))]
    split_ifs <;> omega
  have hne := fun hn2 : 2 ≤ n => HardDataScalar.succ_mod_ne_add_mod hn2 hk
  unfold psdScalarLocFun scalarLocFun at h
  apply Fin.ext
  split_ifs at h <;> simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.ext_iff] at h <;>
    omega

/-- The PSD scalar-family row list of core row `k`, as an embedding. -/
def psdScalarLoc (n s : ℕ) (hn : 1 ≤ n) (k : Fin (n + 1)) : Fin s ↪ ScalarIndex n s :=
  ⟨psdScalarLocFun n s k, psdScalarLocFun_injective s hn k⟩

/-! ### Words -/

/-- Fractional bits of the PSD scalar-family words, `B = F + ⌈log₂ s⌉ + 1`. -/
def psdScalarBits (n s : ℕ) (u : ℝ) : ℕ := psdBits n u + padExp s + 1

/-- The integer words of the PSD scalar-family generator at scale `2^B`. -/
def psdScalarWord (n s : ℕ) (u : ℝ) : ScalarIndex n s × ScalarIndex n s → Bool → ℤ
  | (Sum.inl i, Sum.inl i'), y =>
    if i = i' then 2 ^ (psdBits n u + padExp s)
    else if (i : ℕ) = i' + 1 then -((if y then -1 else 1) * (psdNum n u i' : ℤ) * 2 ^ padExp s)
    else if (i' : ℕ) = i + 1 then -((if y then -1 else 1) * (psdNum n u i : ℤ) * 2 ^ padExp s)
    else 0
  | (Sum.inr (Sum.inl r), Sum.inr (Sum.inl r')), _ =>
    if r = 1 ∧ r' = 1 then 2 ^ psdScalarBits n s u else 0
  | (Sum.inr (Sum.inr _), Sum.inr (Sum.inr _)), _ => 2 ^ (psdBits n u + 1)
  | _, _ => 0

/-- The PSD scalar-family word table: addresses `Hamiltonian.scalarAddr`, words
`psdScalarWord`. -/
def psdScalarTable (n s : ℕ) (u : ℝ) : BitTable (Fin n) (ScalarIndex n s × ScalarIndex n s) :=
  ⟨scalarAddr n s, psdScalarWord n s u⟩

variable {n s : ℕ} {u : ℝ}

/-- **The words are in the decode range** `(-2^B, 2^B]`. -/
theorem psdScalarTable_bound (ad : ScalarIndex n s × ScalarIndex n s) (y : Bool) :
    -(2 : ℤ) ^ psdScalarBits n s u < (psdScalarTable n s u).word ad y ∧
      (psdScalarTable n s u).word ad y ≤ 2 ^ psdScalarBits n s u := by
  have hB : (0 : ℤ) < 2 ^ psdScalarBits n s u := by positivity
  have hD : (2 : ℤ) ^ (psdBits n u + padExp s) ≤ 2 ^ psdScalarBits n s u :=
    pow_le_pow_right₀ (by norm_num) (by unfold psdScalarBits; omega)
  have hF : ∀ k, ((psdNum n u k : ℤ) * 2 ^ padExp s) < 2 ^ psdScalarBits n s u := by
    intro k
    refine lt_of_lt_of_le ?_ hD
    rw [pow_add]
    have h' : (psdNum n u k : ℤ) < 2 ^ psdBits n u := by exact_mod_cast psdNum_lt n u k
    exact mul_lt_mul_of_pos_right h' (by positivity)
  have hN : ∀ k, (0 : ℤ) ≤ (psdNum n u k : ℤ) * 2 ^ padExp s := fun k => by positivity
  have hpad : (2 : ℤ) ^ (psdBits n u + 1) ≤ 2 ^ psdScalarBits n s u :=
    pow_le_pow_right₀ (by norm_num) (by unfold psdScalarBits; omega)
  have hD0 : (0 : ℤ) < 2 ^ (psdBits n u + padExp s) := by positivity
  have hF0 : (0 : ℤ) < 2 ^ (psdBits n u + 1) := by positivity
  obtain ⟨i | r | t, i' | r' | t'⟩ := ad <;> simp only [psdScalarTable, psdScalarWord]
  · have e1 := hF i
    have e2 := hF i'
    have e3 := hN i
    have e4 := hN i'
    split_ifs <;> (try simp only [neg_mul, one_mul, neg_neg]) <;> constructor <;> linarith
  all_goals first
    | (constructor <;> linarith)
    | (split_ifs <;> constructor <;> linarith)

end

end ODELowerBoundExtensions.Psd
