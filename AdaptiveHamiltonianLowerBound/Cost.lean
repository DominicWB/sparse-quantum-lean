import AdaptiveHamiltonianLowerBound.Readout
import AdaptiveHamiltonianLowerBound.Model.Reindex

set_option autoImplicit false

/-!
# Cost bounds for adaptive protocols from a uniform parity correlation

`SearchGrowth m O w` says that every label `l` of an oracle family over hidden inputs
`j : ι → Fin m` behaves, for every search weight `W_a = P_u + a² P_v + a R` with `a ≥ 1`
(`SparseLowerBounds.SearchWeight.w m a`), like at most `w l` single-bit calls: it multiplies
the weighted norm squared by at most `(λ²)^{w l}` (`λ = searchLam m a`) in both directions.
Admissible labels over data with one-bit entries have it (`searchGrowth_admissible`).

* `search_tree_cost` (Lemma `hsl:lem:search` for adaptive protocols, lines 2151-2203): if
  the heralded output has parity correlation with a contraction at least `β₀ ∈ (0, 1]` on
  average over the `mⁿ` hidden inputs, `n ≥ 1` and `m ≥ 4 β₀^{-1/n}`, then
  `worstCost ≥ (log 2/24) n √m β₀^{1/(2n)}`; `search_tree_cost_worst` assumes the
  correlation on every input. The weight parameter is the paper's `a = 2β₀^{-1/(2n)}`; one
  call costs one factor `λ² ≤ (1 + 12a/√m)²`.
* `precision_tree_cost` (the counting step of Lemma `hsl:lem:precision` for adaptive
  protocols, lines 2348-2370, proved with the weight method instead of the polynomial degree):
  for one hidden bit per position (`m = 2`), a positive total parity correlation forces
  `worstCost ≥ n/2`. With `λ ≤ 7a²` the parity sum is at most `2ⁿ 49^Q a^{4Q-2n}`, which
  tends to `0` as `a → ∞` unless `2Q ≥ n`.
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open LinearSystemLowerBound

/-- **Search-weight growth of a labelled family**: for every `a ≥ 1`, label `l` has growth
`(λ²)^{w l}` for the search weight `W_a^{⊗ι}`, forwards and backwards. -/
def SearchGrowth {ι K L : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (m : ℕ) (O : L → (ι → Fin m) → K →L[ℂ] K)
    (w : L → ℕ) : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∀ l,
    WGrowth (SparseLowerBounds.SearchWeight.w m a) (O l) ((searchLam m a ^ 2) ^ w l) ∧
      WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => star (O l j))
        ((searchLam m a ^ 2) ^ w l)

/-- **Admissible labels over data with one-bit entries** have search-weight growth, read
along the map `g` of inputs. -/
theorem searchGrowth_admissible {n m : ℕ} (hm : Even m) {X N Z : Type*} [Fintype N]
    [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}
    (D : NativeSparseBlockEncoding.Data X N Z s) (g : (Fin n → Fin m) → X)
    (hD : Access.HardAccess D g) {K L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (O : L → X → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Access.Admissible D (O l) (w l)) :
    SearchGrowth m (fun l j => O l (g j)) w :=
  fun _ ha l => Access.wgrowth_admissible hm ha D g hD (O l) (w l) (hO l)

variable {K F E L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]

/-- **Lemma `hsl:lem:search` for adaptive protocols** (average correlation over the `mⁿ`
hidden inputs, eq. `hsl:eq:searchbound`). -/
theorem search_tree_cost {n m : ℕ} (hn : 1 ≤ n) (hm : Even m)
    {O : L → (Fin n → Fin m) → K →L[ℂ] K} (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (hO : SearchGrowth m O w) (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (T : Tree O F E) {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ1 : β₀ ≤ 1)
    (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ m)
    (hsum : (m : ℝ) ^ n * β₀ ≤ ∑ j, parSign j * corr M (T.successDensity j)) :
    Real.log 2 / 24 * n * Real.sqrt m * β₀ ^ (1 / (2 * (n : ℝ))) ≤ T.worstCost w := by
  set a := SparseLowerBounds.SearchWeight.searchA n β₀ with ha_def
  have ha1 : 1 ≤ a := SparseLowerBounds.SearchWeight.one_le_searchA hβ₀ hβ1
  have ham : a ≤ Real.sqrt m := SparseLowerBounds.SearchWeight.searchA_le_sqrt hβ₀ hmβ
  have hm0 : 0 < m := SparseLowerBounds.SearchWeight.pos_of_hmβ hβ₀ hmβ
  have hxor := search_tree_xor hm ha1 hU w (fun l => (hO a ha1 l).1) (fun l => (hO a ha1 l).2)
    M hM T
  rw [Fintype.card_fin] at hxor
  set Q := T.worstCost w
  have hmn : (0 : ℝ) < (m : ℝ) ^ n := by positivity
  have hβ : β₀ ≤ ((a ^ 2)⁻¹) ^ n * (searchLam m a ^ 2) ^ Q := by
    have h2 := hsum.trans ((le_abs_self _).trans hxor)
    have h3 : (m : ℝ) ^ n * β₀ ≤ (m : ℝ) ^ n * (((a ^ 2)⁻¹) ^ n * (searchLam m a ^ 2) ^ Q) := by
      linarith
    exact le_of_mul_le_mul_left h3 hmn
  have hlam : (searchLam m a ^ 2) ^ Q ≤ Real.exp (24 * a * Q / Real.sqrt m) := by
    have h1 : searchLam m a ≤ 1 + 12 * a / Real.sqrt m := searchLam_le_twelve (by linarith) ham
    have h0 : 0 ≤ searchLam m a := by linarith [one_le_searchLam m (show (0 : ℝ) ≤ a by linarith)]
    calc (searchLam m a ^ 2) ^ Q = searchLam m a ^ (2 * Q) := by rw [← pow_mul]
      _ ≤ (1 + 12 * a / Real.sqrt m) ^ (2 * Q) := pow_le_pow_left₀ h0 h1 _
      _ ≤ Real.exp (24 * a * Q / Real.sqrt m) :=
          SparseLowerBounds.SearchWeight.lam_pow_le (by linarith) m Q
  exact SparseLowerBounds.SearchWeight.search_final hn hβ₀
    (hβ.trans (mul_le_mul_of_nonneg_left hlam (by positivity)))

/-- **Lemma `hsl:lem:search` for adaptive protocols**, worst-case form: parity correlation
at least `β₀` on every hidden input. -/
theorem search_tree_cost_worst {n m : ℕ} (hn : 1 ≤ n) (hm : Even m)
    {O : L → (Fin n → Fin m) → K →L[ℂ] K} (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (hO : SearchGrowth m O w) (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (T : Tree O F E) {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ1 : β₀ ≤ 1)
    (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ m)
    (hcorr : ∀ j, β₀ ≤ parSign j * corr M (T.successDensity j)) :
    Real.log 2 / 24 * n * Real.sqrt m * β₀ ^ (1 / (2 * (n : ℝ))) ≤ T.worstCost w := by
  refine search_tree_cost hn hm hU w hO M hM T hβ₀ hβ1 hmβ ?_
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcorr j)
  have hcard : (Finset.univ : Finset (Fin n → Fin m)).card = m ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at h
  push_cast at h
  exact h

/-- **Lemma `hsl:lem:precision` for adaptive protocols**, counting step by the weight method:
for one hidden bit per position, a positive total parity correlation forces
`worstCost ≥ n/2`. -/
theorem precision_tree_cost {n : ℕ} {O : L → (Fin n → Fin 2) → K →L[ℂ] K}
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j)) (w : L → ℕ) (hO : SearchGrowth 2 O w)
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (T : Tree O F E)
    (hpos : 0 < ∑ j, parSign j * corr M (T.successDensity j)) :
    (n : ℝ) / 2 ≤ T.worstCost w := by
  set S := ∑ j, parSign j * corr M (T.successDensity j)
  set Q := T.worstCost w
  by_contra hlt
  push Not at hlt
  have hQn : 4 * Q + 2 ≤ 2 * n := by
    have h1 : ((2 * Q : ℕ) : ℝ) < n := by push_cast; linarith
    have h2 : 2 * Q < n := by exact_mod_cast h1
    omega
  set c : ℝ := 2 ^ n * 49 ^ Q with hc_def
  have hc : 0 < c := by positivity
  set a : ℝ := 1 + c / S with ha_def
  have hcS : 0 ≤ c / S := div_nonneg hc.le hpos.le
  have ha1 : 1 ≤ a := by linarith
  have ha0 : 0 < a := by linarith
  have hxor := search_tree_xor (m := 2) even_two ha1 hU w (fun l => (hO a ha1 l).1)
    (fun l => (hO a ha1 l).2) M hM T
  rw [Fintype.card_fin] at hxor
  have hlam : searchLam 2 a ^ 2 ≤ 49 * a ^ 4 := by
    have h := searchLam_two_le ha1
    have h0 : 0 ≤ searchLam 2 a := by linarith [one_le_searchLam 2 ha0.le]
    calc searchLam 2 a ^ 2 ≤ (7 * a ^ 2) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = 49 * a ^ 4 := by ring
  have hpowQ : (searchLam 2 a ^ 2) ^ Q ≤ 49 ^ Q * a ^ (4 * Q) := by
    calc (searchLam 2 a ^ 2) ^ Q ≤ (49 * a ^ 4) ^ Q := pow_le_pow_left₀ (by positivity) hlam Q
      _ = 49 ^ Q * a ^ (4 * Q) := by rw [mul_pow, ← pow_mul]
  have hinv : ((a ^ 2)⁻¹) ^ n ≤ (a ^ (4 * Q + 2))⁻¹ := by
    rw [inv_pow, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ ha1 hQn)
  have hbound : S ≤ c / a ^ 2 := by
    have hx : |S| ≤ ((a ^ 2)⁻¹) ^ n * (searchLam 2 a ^ 2) ^ Q * (2 : ℝ) ^ n := by
      have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h2] at hxor
      exact hxor
    calc S ≤ |S| := le_abs_self _
      _ ≤ ((a ^ 2)⁻¹) ^ n * (searchLam 2 a ^ 2) ^ Q * (2 : ℝ) ^ n := hx
      _ ≤ (a ^ (4 * Q + 2))⁻¹ * (49 ^ Q * a ^ (4 * Q)) * 2 ^ n := by gcongr
      _ = c / a ^ 2 := by
          rw [hc_def, pow_add]
          field_simp
  have hca : c / a ^ 2 ≤ c / a := by
    apply div_le_div_of_nonneg_left hc.le ha0
    nlinarith
  have hlt2 : c / a < S := by
    rw [div_lt_iff₀ ha0]
    have hSa : S * a = S + c := by
      rw [ha_def, mul_add, mul_one, mul_div_cancel₀ _ hpos.ne']
    linarith
  linarith

end

end AdaptiveHamiltonianLowerBound
