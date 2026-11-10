import AdaptiveHamiltonianLowerBound.Cost
import SparseLowerBounds.Hamiltonian.SearchFamily
import SparseLowerBounds.Hamiltonian.Numerics

set_option autoImplicit false

/-!
# The three hard families against adaptive protocols

For each hard family of Theorem `hsl:thm:main`, an adaptive
protocol `T : SparseLinearSystems.Protocol.Tree O F E` that on every input heralds success with
probability at least `2/3` and whose conditional output is `ε`-accurate for
`e^{-iτH}ψ_in` (`DensityAccurate`, observable form of trace distance) must have a large
worst-case cost `T.worstCost w`.

* `*_tree_general`: any oracle family with search-weight growth (`SearchGrowth`): the time
  family (`(log 2/48) n √m`), the mixed family at the main parameters (`(log 2/48) √(mnτ)`)
  and the precision family at the main parameters (`n/2`, inputs read through `toBits`).
* `time_tree`, `mixed_tree`, `precision_tree`: every oracle label admissible for the hard data
  (`Access.Admissible`: native calls with spectators, controls, masks, inverses and coherent
  choices of the native query, counted with their weight; input-independent unitaries of any
  weight). The bounds are those of `Hamiltonian/Theorem.lean` with the paper's constants:
  `c_T √s τ`, `(log 2/(384√2)) √(sτr)`, `r/32` and `√(sτr)/(64√2)` (for `s < 64n/τ`).

The correlations are those of the heralded proof (Lemma `odel:lem:herald`):
`(2/3)(7A/8 - 2ε) ≥ 1/4` (time), `≥ A/2` (mixed, `A ≥ 16ε`), `> 0` (precision). One value
call costs one growth factor, so the general bounds are twice the paper's value-query bounds
(`log 2/96`, `n/4`), and the paper's constants follow (`time_final`, `mixrbound`, `rbound`,
`failedmix`).
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open LinearSystemLowerBound SparseLowerBounds SparseLowerBounds.Readout
open SparseLowerBounds.Hamiltonian

-- The nested spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ} {K F E G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

theorem abs_parSign_le {n m : ℕ} (j : Fin n → Fin m) : |parSign j| ≤ 1 := by
  rcases parSign_pm j with h | h <;> simp [h]

theorem even_two_pow_hsMu (h : 32 ≤ s) : Even (2 ^ hsMu s) :=
  Nat.even_pow.mpr ⟨even_two, by have := one_le_hsMu h; omega⟩

theorem cast_two_pow (μ : ℕ) : (((2 ^ μ : ℕ)) : ℝ) = (2 : ℝ) ^ μ := by
  push_cast
  rfl

/-! ### Any family with search-weight growth -/

/-- **Time family, adaptive protocols** (Lemma `hsl:lem:time`): heralded success `≥ 2/3` and
conditional accuracy `ε` force `worstCost ≥ (log 2/48) n √m` (`n = timeN τ`,
`m = 2^{hsMu s}`). -/
theorem time_tree_general (h : HSRange τ s ε)
    {O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K}
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j)) (w : L → ℕ)
    (hO : SearchGrowth (2 ^ hsMu s) O w) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ T.successMass j)
    (hacc : ∀ j, DensityAccurate e (T.conditionalDensity j)
      (evolve (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ
        (searchInput (timeN τ) (hsMu s) s)) ε) :
    Real.log 2 / 48 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) ≤ T.worstCost w := by
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have hA : 1 / 2 ≤ chainAmp (timeN τ) (timeC τ) τ := half_le_timeAmp h.one_le_tau
  have hε := h.eps_le
  have hε0 := h.eps_pos
  have hobs := searchObs_contraction (timeN τ) (hsMu s) s
  have hcorr : ∀ j, (1 / 4 : ℝ) ≤ parSign j *
      corr (outObs e (searchObs (timeN τ) (hsMu s) s)) (T.successDensity j) := by
    intro j
    have hideal := search_corr (s := s) (one_le_timeN τ) (one_le_hsMu h.s_ge) (timeC_pos hτ0)
      (timeC_le_one τ) hτ0 (by linarith) j
    rw [parity_eq_parSign] at hideal
    have h1 := tree_correlation e T j _ ε (hacc j) (hsucc j) _ hobs.1 hobs.2
      (abs_parSign_le j) hideal (by linarith)
    linarith
  have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ hsMu s := by exact_mod_cast (hsM_range h.s_ge).1
  have hb := search_tree_cost_worst (one_le_timeN τ) (even_two_pow_hsMu h.s_ge) hU w hO _
    (outObs_contraction e he _ hobs.2) T (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
    (by rw [cast_two_pow]; exact (quarter_hyp (one_le_timeN τ)).trans h16) hcorr
  rw [cast_two_pow] at hb
  have hc : 0 ≤ Real.log 2 / 24 * (timeN τ : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  calc Real.log 2 / 48 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s)
      = Real.log 2 / 24 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) * (1 / 2) := by ring
    _ ≤ Real.log 2 / 24 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) *
          (1 / 4 : ℝ) ^ (1 / (2 * (timeN τ : ℝ))) :=
        mul_le_mul_of_nonneg_left (quarter_root (timeN τ)) hc
    _ ≤ T.worstCost w := hb

/-- **Mixed family, adaptive protocols** (Lemma `hsl:lem:mixed`, at the
main parameters `L ≥ 64τ`, `s ≥ 64n/τ`): `worstCost ≥ (log 2/48) √(mnτ)`. -/
theorem mixed_tree_general (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    {O : L → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K}
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j)) (w : L → ℕ)
    (hO : SearchGrowth (2 ^ hsMu s) O w) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ T.successMass j)
    (hacc : ∀ j, DensityAccurate e (T.conditionalDensity j)
      (evolve (searchHam (precN τ ε) (hsMu s) s 1 τ j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε) :
    Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) ≤ T.worstCost w := by
  obtain ⟨hn2, hrn, hτr, -⟩ := precN_range h hL
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have hτn : τ ≤ precN τ ε := by linarith
  have hn1 : 1 ≤ precN τ ε := by omega
  have h16 := sixteen_eps_le h hL
  have hamp := amp_ge hn1 hτ0 hτn
  have hε0 := h.eps_pos
  have hA : chainAmp (precN τ ε) 1 τ = Real.sin (τ / precN τ ε) ^ precN τ ε := by
    rw [chainAmp, one_mul]
  have hApos : 0 < chainAmp (precN τ ε) 1 τ := by rw [hA]; linarith
  have hobs := searchObs_contraction (precN τ ε) (hsMu s) s
  -- Eq. `odel:eq:heraldcorr` with `A ≥ 16ε`: the correlation is at least `A/2`.
  have hcorr : ∀ j, Real.sin (τ / precN τ ε) ^ precN τ ε / 2 ≤ parSign j *
      corr (outObs e (searchObs (precN τ ε) (hsMu s) s)) (T.successDensity j) := by
    intro j
    have hideal := search_corr (s := s) hn1 (one_le_hsMu h.s_ge) one_pos le_rfl hτ0 hApos j
    rw [parity_eq_parSign, hA] at hideal
    have h1 := tree_correlation e T j _ ε (hacc j) (hsucc j) _ hobs.1 hobs.2
      (abs_parSign_le j) hideal (by linarith)
    linarith
  have hsin := sin_div_pos hn1 hτ0 hτn
  have hβ1 : Real.sin (τ / precN τ ε) ^ precN τ ε / 2 ≤ 1 := by
    have := pow_le_one₀ hsin.le (Real.sin_le_one (τ / precN τ ε)) (n := precN τ ε)
    linarith
  have hb := search_tree_cost_worst hn1 (even_two_pow_hsMu h.s_ge) hU w hO _
    (outObs_contraction e he _ hobs.2) T (by positivity) hβ1
    (by rw [cast_two_pow]; exact (mixed_hyp hn2 hτ0 hτn).trans (mixed_m_cond h hs)) hcorr
  rw [cast_two_pow] at hb
  have hc : 0 ≤ Real.log 2 / 24 * (precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  calc Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ)
      = Real.log 2 / 24 * precN τ ε * Real.sqrt ((2 : ℝ) ^ hsMu s) *
          (1 / 2 * Real.sqrt (τ / precN τ ε)) :=
        (mixed_cost_arith hn1 hτ0 (by positivity)).symm
    _ ≤ Real.log 2 / 24 * precN τ ε * Real.sqrt ((2 : ℝ) ^ hsMu s) *
          (Real.sin (τ / precN τ ε) ^ precN τ ε / 2) ^ (1 / (2 * (precN τ ε : ℝ))) :=
        mul_le_mul_of_nonneg_left (mixed_root hn2 hτ0 hτn) hc
    _ ≤ T.worstCost w := hb

/-- **Precision family, adaptive protocols** (Lemma `hsl:lem:precision`, at
the main parameters `L ≥ 64τ`): inputs `x : Fin n → Bool`, labels with search-weight growth
along `toBits`; `worstCost ≥ n/2` (`n = ⌊r/4⌋`). -/
theorem precision_tree_general (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    {O : L → (Fin (precN τ ε) → Bool) → K →L[ℂ] K}
    (hU : ∀ l x, OracleCircuit.IsUnitary (O l x)) (w : L → ℕ)
    (hO : SearchGrowth 2 (fun l j => O l (Access.toBits j)) w) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x)
      (evolve (scalarHam (precN τ ε) s τ x) τ (scalarInput (precN τ ε) s)) ε) :
    (precN τ ε : ℝ) / 2 ≤ T.worstCost w := by
  obtain ⟨hn2, hrn, hτr, -⟩ := precN_range h hL
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have hτn : τ ≤ precN τ ε := by linarith
  have hn1 : 1 ≤ precN τ ε := by omega
  have h16 := sixteen_eps_le h hL
  have hamp := amp_ge hn1 hτ0 hτn
  have hε0 := h.eps_pos
  have hA : chainAmp (precN τ ε) 1 τ = Real.sin (τ / precN τ ε) ^ precN τ ε := by
    rw [chainAmp, one_mul]
  have hApos : 0 < chainAmp (precN τ ε) 1 τ := by rw [hA]; linarith
  have hobs := scalarObs_contraction (precN τ ε) s
  -- Eq. `odel:eq:heraldcorr`: the heralded parity correlation is positive on every input.
  have hpos : ∀ x, 0 < BitDegree.bitParity x *
      corr (outObs e (scalarObs (precN τ ε) s)) (T.successDensity x) := by
    intro x
    have hideal := scalar_corr (s := s) hn1 hτ0 hApos x
    rw [hA] at hideal
    have h1 := tree_correlation e T x _ ε (hacc x) (hsucc x) _ hobs.1 hobs.2
      (le_of_eq (BitDegree.abs_bitParity x)) hideal (by linarith)
    linarith
  have hsum : 0 < ∑ j, parSign j * corr (outObs e (scalarObs (precN τ ε) s))
      ((Reindex.tree Access.toBits T).successDensity j) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro j _
    rw [Reindex.successDensity_tree, ← bitParity_toBits]
    exact hpos _
  have hb := precision_tree_cost (fun l j => hU l (Access.toBits j)) w hO _
    (outObs_contraction e he _ hobs.2) (Reindex.tree Access.toBits T) hsum
  rwa [Reindex.worstCost_tree] at hb

/-! ### Admissible labels over the hard data -/

/-- **Time family, admissible labels** (eq. `hsl:eq:timelower`, for adaptive
protocols): `worstCost ≥ c_T √s τ`, `c_T = log 2/(192π)`. -/
theorem time_tree (h : HSRange τ s ε)
    (O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Access.Admissible (timeData τ s h.s_ge) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ T.successMass j)
    (hacc : ∀ j, DensityAccurate e (T.conditionalDensity j)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    cT * Real.sqrt s * τ ≤ T.worstCost w := by
  have hb := time_tree_general h (fun l j => Access.admissible_unitary _ _ _ (hO l) j) w
    (searchGrowth_admissible (even_two_pow_hsMu h.s_ge) _ _
      (Access.hardAccess_timeData τ s h.s_ge) O w hO) T e he hsucc hacc
  have hX : 0 ≤ Real.log 2 / 96 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  linarith [time_final h.one_le_tau h.s_ge]

/-- **Mixed family, admissible labels** (eq. `hsl:eq:mixrbound`, for adaptive
protocols): for `L ≥ 64τ` and `s ≥ 64n/τ`, `worstCost ≥ (log 2/(384√2)) √(sτr)`. -/
theorem mixed_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    (O : L → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Access.Admissible (mixedMainData τ ε s h.s_ge) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ T.successMass j)
    (hacc : ∀ j, DensityAccurate e (T.conditionalDensity j)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s))
      ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ T.worstCost w := by
  have hb := mixed_tree_general h hL hs (fun l j => Access.admissible_unitary _ _ _ (hO l) j) w
    (searchGrowth_admissible (even_two_pow_hsMu h.s_ge) _ _
      (Access.hardAccess_mixedMainData τ ε s h.s_ge) O w hO) T e he hsucc hacc
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  linarith [mixrbound h hL]

/-- **Precision family, admissible labels** (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`, for adaptive
protocols): for `L ≥ 64τ`, `worstCost ≥ r/32`, and `worstCost ≥ √(sτr)/(64√2)` when `s < 64n/τ`. -/
theorem precision_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (O : L → (Fin (precN τ ε) → Bool) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Access.Admissible (precisionMainData τ ε s h.s_ge) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    hsR τ ε / 32 ≤ T.worstCost w ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ T.worstCost w) := by
  have hb := precision_tree_general h hL (fun l x => Access.admissible_unitary _ _ _ (hO l) x) w
    (searchGrowth_admissible even_two _ _ (Access.hardAccess_precisionMainData τ ε s h.s_ge)
      O w hO) T e he hsucc hacc
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  refine ⟨by linarith [rbound h hL], fun hs' => ?_⟩
  linarith [failedmix h hL hs']

end

end AdaptiveHamiltonianLowerBound
