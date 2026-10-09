import SparseLowerBounds.Query.Reduction
import SparseLowerBounds.Hamiltonian.HardData

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The search-decorated families: time and mixed lower bounds

Manuscript lines 2308-2338 (Lemma `hsl:lem:mixed`, eq. `hsl:eq:mixedlower`)
and 2372-2409 (the time bound, eq. `hsl:eq:timelower`), for **any** labelled
oracle family whose labels are implementable on a fixed isometric encoding
with `w l` Boolean one-hot queries (`EncodedOracle.ImplementsOn`, packaged as
`Adaptive.Access.BooleanAccess`). The bound is on the Boolean cost `p.cost w`;
the native corollaries (`Hamiltonian/Native`, `w = hardCost`) halve it.

* `search_cost_of_corr`: correlation form. If an input-independent contraction
  `A` has parity correlation at least `β₀ > 0` on every hidden input and
  `2^μ ≥ 4 β₀^{-1/n}`, then `p.cost w ≥ (log 2/24) n √m β₀^{1/(2n)}`
  (compile with `Reduction.exists_boolean_program_inner`, then
  `SearchWeight.search_lemma_worst`). Shared with `Hamiltonian/Herald`.
* `time_general`: the time family (`n = timeN τ`, `a = timeC τ`,
  `m = 2^{hsMu s}`): correlation `≥ 7A/8 - 2ε ≥ 13/32 > 1/4`, `β₀ = 1/4`, so
  `p.cost w ≥ (log 2/48) n √m ≥ 2 c_T √s τ`.
* `mixed_general`: the mixed family (`a = 1`, any `n ≥ 2`, `0 < τ ≤ n`,
  `m ≥ 16n/τ`, `ε ≤ (τ/(2n))^n/8`): `β₀ = A/2`, so
  `p.cost w ≥ (log 2/48) √(m n τ)`.

Accuracy is `Readout.Accurate` (observable form of eq. `hsl:eq:accuracy`) for
the target `e^{-iτH_X} ψ_in`, unconditional (no herald).

Intermediate statements (all per output vector, so that the program form is
`fun j => … (hacc j)` and the endpoint form of `Hamiltonian/ReleaseForm` can
use them directly):

* `outObs_searchObs_contraction`: the workspace readout `e† (M ⊗ 1) e` of the
  search observable `M` of eq. `hsl:eq:readout` is a contraction.
* `time_corr`: an `ε`-accurate output (`ε ≤ 1/64`) of the time family has
  parity correlation `≥ 7/16 - 2/64 = 13/32` (lines 2392-2398).
* `mixed_corr`: an `ε`-accurate output (`ε ≤ (τ/(2n))^n/8`) of the mixed
  family has parity correlation `≥ 5A/8 ≥ A/2 = β₀`, `A = sin(τ/n)^n`
  (lines 2321-2323).
* `mixed_one_le_mu`, `mixed_cost_arith`: the side condition `μ ≥ 1` (implied
  by `m ≥ 16n/τ ≥ 16`) and the final identity
  `(log 2/24) n √m · ½√(τ/n) = (log 2/48) √(m n τ)` (lines 2330-2337).
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

variable {K K' G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Correlation form of the search bound** (Lemma `hsl:lem:search` through
the reduction `q ≤ Σ_l w l · Q_l`, line 2336). -/
theorem search_cost_of_corr {n μ : ℕ} (hμ : 1 ≤ μ) (P : ProjFamily K' (Fin n × Fin (2 ^ μ)))
    (E : K →L[ℂ] K') (hE : E† ∘L E = 1)
    (O : L → (Fin n → Fin (2 ^ μ)) → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (A : K →L[ℂ] K) (hA : ‖A‖ ≤ 1) {β₀ : ℝ} (hβ₀ : 0 < β₀)
    (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ (2 : ℝ) ^ μ)
    (hcorr : ∀ j, β₀ ≤ parity j * (⟪p.eval j φ₀, A (p.eval j φ₀)⟫_ℂ).re) :
    Real.log 2 / 24 * n * Real.sqrt ((2 : ℝ) ^ μ) * β₀ ^ (1 / (2 * (n : ℝ))) ≤ p.cost w := by
  -- Proof sketch: `obtain ⟨c, hc, hinner⟩ := Reduction.exists_boolean_program_inner E hE
  --   (fun j => isUnitary_oneHotOracle P j) hO w hw p`; apply
  -- `SearchWeight.search_lemma_worst (m := 2 ^ μ)` (`Even (2 ^ μ)` from `hμ` via
  -- `Nat.even_pow`) to `c`, seed `E φ₀` (`Reduction.norm_encode`) and
  -- `Reduction.encodeObs E A` (`Reduction.norm_encodeObs_le`), rewriting each
  -- correlation with `hinner j φ₀ A` and the cast `((2 ^ μ : ℕ) : ℝ) = 2 ^ μ`
  -- (`Nat.cast_pow`); finish with `hc : c.count ≤ p.cost w`.
  obtain ⟨c, hc, hinner⟩ := Reduction.exists_boolean_program_inner E hE
    (fun j => isUnitary_oneHotOracle P j) hO w hw p
  have hm : Even (2 ^ μ) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hcast : ((2 ^ μ : ℕ) : ℝ) = (2 : ℝ) ^ μ := by push_cast; rfl
  have key := SearchWeight.search_lemma_worst (m := 2 ^ μ) hm P c (E φ₀)
    (by rw [Reduction.norm_encode E hE]; exact hφ₀) (Reduction.encodeObs E A)
    ((Reduction.norm_encodeObs_le E hE A).trans hA) hβ₀ (by rw [hcast]; exact hmβ)
    (fun j => by rw [hinner j φ₀ A]; exact hcorr j)
  rw [hcast] at key
  exact key.trans (by exact_mod_cast hc)

/-! ### Readout correlations of the two search families -/

/-- The workspace readout of the search observable is a contraction:
`‖e† (M ⊗ 1) e‖ ≤ ‖M‖ ≤ 1` (`Readout.norm_outObs_le`,
`searchObs_contraction`). -/
theorem outObs_searchObs_contraction (n μ s : ℕ) (e : K →L[ℂ] SysGarb (SearchIndex n μ s) G)
    (he : e† ∘L e = 1) : ‖outObs e (searchObs n μ s)‖ ≤ 1 :=
  (norm_outObs_le e he _).trans (searchObs_contraction n μ s).2

/-- **Time-family correlation** (lines 2392-2398): an `ε`-accurate output
(`ε ≤ 1/64`) of the time family on hidden input `j` has parity correlation at
least `(7/8)(1/2) - 2/64 = 13/32` (`> 1/4 = β₀`, by `norm_num`) with the readout
of eq. `hsl:eq:readout`.

Proof sketch: `search_corr` at `n = timeN τ ≥ 1`, `μ = hsMu s ≥ 1`
(`one_le_hsMu hs`), `a = timeC τ ∈ (0, 1]` (`timeC_pos`, `timeC_le_one`), with
amplitude `chainAmp (timeN τ) (timeC τ) τ ≥ 1/2` (`half_le_timeAmp`, the same
term by `rfl`), then `corr_of_accurate` with `sgn = parity j`
(`abs_parity`) and `M = searchObs` (`searchObs_contraction`). -/
theorem time_corr {τ ε : ℝ} {s : ℕ} (hτ : 1 ≤ τ) (hs : 32 ≤ s) (hε : ε ≤ 1 / 64)
    (e : K →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G)
    (j : Fin (timeN τ) → Fin (2 ^ hsMu s)) (Φ : K)
    (hacc : Accurate e Φ
      (evolve (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ
        (searchInput (timeN τ) (hsMu s) s)) ε) :
    13 / 32 ≤ parity j * (⟪Φ, outObs e (searchObs (timeN τ) (hsMu s) s) Φ⟫_ℂ).re := by
  have hτ0 : 0 < τ := by linarith
  have hA : (1 : ℝ) / 2 ≤ chainAmp (timeN τ) (timeC τ) τ := half_le_timeAmp hτ
  have hcorr := search_corr (s := s) (one_le_timeN τ) (one_le_hsMu hs) (timeC_pos hτ0)
    (timeC_le_one τ) hτ0 (lt_of_lt_of_le (by norm_num) hA) j
  have h2 := corr_of_accurate e Φ _ ε hacc (searchObs (timeN τ) (hsMu s) s)
    (searchObs_contraction _ _ _).1 (searchObs_contraction _ _ _).2 (abs_parity j).le hcorr
  linarith

/-- **Mixed-family correlation** (lines 2321-2323): for `n ≥ 1`, `0 < τ ≤ n`
and `ε ≤ (τ/(2n))^n/8` (eq. `hsl:eq:mixepsilon`), an `ε`-accurate output of the
mixed family on hidden input `j` has parity correlation at least
`β₀ = A/2`, `A = sin(τ/n)^n`.

Proof sketch: `A ≥ (τ/(2n))^n > 0` (`amp_ge`), so `ε ≤ A/8`; `search_corr`
with `a = 1` gives ideal correlation `≥ 7A/8` (`chainAmp n 1 τ` unfolds to
`Real.sin (1 * τ / n) ^ n`; rewrite with `one_mul`), and `corr_of_accurate`
gives `≥ 7A/8 - 2ε ≥ 5A/8 ≥ A/2`. -/
theorem mixed_corr {n μ s : ℕ} {τ ε : ℝ} (hn : 1 ≤ n) (hμ : 1 ≤ μ) (hτ : 0 < τ)
    (hτn : τ ≤ n) (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (e : K →L[ℂ] SysGarb (SearchIndex n μ s) G) (j : Fin n → Fin (2 ^ μ)) (Φ : K)
    (hacc : Accurate e Φ (evolve (searchHam n μ s 1 τ j) τ (searchInput n μ s)) ε) :
    Real.sin (τ / n) ^ n / 2 ≤ parity j * (⟪Φ, outObs e (searchObs n μ s) Φ⟫_ℂ).re := by
  have hA0 : 0 < Real.sin (τ / n) ^ n := pow_pos (sin_div_pos hn hτ hτn) n
  have hge := amp_ge hn hτ hτn
  have hcA : chainAmp n 1 τ = Real.sin (τ / n) ^ n := by
    rw [chainAmp, one_mul]
  have hcorr := search_corr (s := s) hn hμ one_pos le_rfl hτ (by rw [hcA]; exact hA0) j
  rw [hcA] at hcorr
  have h2 := corr_of_accurate e Φ _ ε hacc (searchObs n μ s)
    (searchObs_contraction _ _ _).1 (searchObs_contraction _ _ _).2 (abs_parity j).le hcorr
  linarith

/-- The mixed family's side condition `μ ≥ 1` (needed by
`search_corr`) follows from `2^μ ≥ 16n/τ ≥ 16` for `0 < τ ≤ n`. -/
theorem mixed_one_le_mu {n μ : ℕ} {τ : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hm : 16 * n / τ ≤ (2 : ℝ) ^ μ) : 1 ≤ μ := by
  by_contra h0
  have hμ0 : μ = 0 := by omega
  subst hμ0
  rw [pow_zero] at hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h16 : (16 : ℝ) ≤ 16 * n / τ := by
    rw [le_div_iff₀ hτ]
    nlinarith
  linarith

/-- The final identity of Lemma `hsl:lem:mixed` (lines 2330-2337):
`(log 2/24) n √m · ½ √(τ/n) = (log 2/48) √(m n τ)`, since
`n √(τ/n) = √(n τ)`. -/
theorem mixed_cost_arith {n : ℕ} {τ m : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hm : 0 ≤ m) :
    Real.log 2 / 24 * n * Real.sqrt m * (1 / 2 * Real.sqrt (τ / n)) =
      Real.log 2 / 48 * Real.sqrt (m * n * τ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : Real.sqrt (m * n * τ) = Real.sqrt m * (n * Real.sqrt (τ / n)) := by
    rw [mul_assoc, Real.sqrt_mul hm]
    congr 1
    rw [show (n : ℝ) * τ = (n : ℝ) ^ 2 * (τ / n) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  rw [h1]
  ring

/-! ### The family bounds -/

/-- **The time lower bound, general form** (lines 2379-2409). Any algorithm
over a 2-query-implementable labelled family that is `ε`-accurate
(`ε ≤ 1/64`) on every input of the time family has Boolean cost
`p.cost w ≥ (log 2/48) n √m ≥ 2 c_T √s τ`. -/
theorem time_general {τ ε : ℝ} {s : ℕ} (hτ : 1 ≤ τ) (hs : 32 ≤ s) (hε : ε ≤ 1 / 64)
    (P : ProjFamily K' (Fin (timeN τ) × Fin (2 ^ hsMu s))) (E : K →L[ℂ] K') (hE : E† ∘L E = 1)
    (O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hw : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ
        (searchInput (timeN τ) (hsMu s) s)) ε) :
    Real.log 2 / 48 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) ≤ p.cost w ∧
      2 * cT * Real.sqrt s * τ ≤ p.cost w := by
  -- Proof sketch: `search_cost_of_corr (one_le_hsMu hs) … (outObs e (searchObs …))
  --   (outObs_searchObs_contraction _ _ _ e he) (β₀ := 1/4)`, with
  -- `hmβ := (quarter_hyp (one_le_timeN τ)).trans` (`16 ≤ 2^{hsMu s}`, `hsM_range`,
  -- cast) and `hcorr j := (by norm_num : 1/4 ≤ 13/32).trans (time_corr … (hacc j))`;
  -- then `quarter_root` (`(1/4)^{1/(2n)} ≥ 1/2`) for the first conjunct and
  -- `time_final` (`c_T √s τ ≤ (log 2/96) n √m`) for the second.
  have hμ := one_le_hsMu hs
  have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ hsMu s := by exact_mod_cast (hsM_range hs).1
  have key := search_cost_of_corr hμ P E hE O hO w hw p φ₀ hφ₀
    (outObs e (searchObs (timeN τ) (hsMu s) s)) (outObs_searchObs_contraction _ _ _ e he)
    (β₀ := 1 / 4) (by norm_num) ((quarter_hyp (one_le_timeN τ)).trans h16)
    (fun j => (by norm_num : (1 : ℝ) / 4 ≤ 13 / 32).trans (time_corr hτ hs hε e j _ (hacc j)))
  have hr := quarter_root (timeN τ)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpos : 0 ≤ Real.log 2 / 24 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) := by positivity
  have h1 : Real.log 2 / 48 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) ≤ p.cost w := by
    calc Real.log 2 / 48 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s)
        = Real.log 2 / 24 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) * (1 / 2) := by ring
      _ ≤ Real.log 2 / 24 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) *
            (1 / 4 : ℝ) ^ (1 / (2 * (timeN τ : ℝ))) := mul_le_mul_of_nonneg_left hr hpos
      _ ≤ p.cost w := key
  refine ⟨h1, ?_⟩
  have ht := time_final hτ hs
  linarith

/-- **Lemma `hsl:lem:mixed`, general form** (lines 2308-2338). For `n ≥ 2`,
`0 < τ ≤ n`, `m = 2^μ ≥ 16n/τ` and `ε ≤ (τ/(2n))^n/8`
(eq. `hsl:eq:mixepsilon`), any algorithm over a 2-query-implementable
labelled family that is `ε`-accurate on every input of the mixed family has
Boolean cost `p.cost w ≥ (log 2/48) √(m n τ)`. -/
theorem mixed_general {n μ s : ℕ} {τ ε : ℝ} (hn : 2 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hm : 16 * n / τ ≤ (2 : ℝ) ^ μ) (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (P : ProjFamily K' (Fin n × Fin (2 ^ μ))) (E : K →L[ℂ] K') (hE : E† ∘L E = 1)
    (O : L → (Fin n → Fin (2 ^ μ)) → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hw : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex n μ s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve (searchHam n μ s 1 τ j) τ (searchInput n μ s)) ε) :
    Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ μ * n * τ) ≤ p.cost w := by
  -- Proof sketch: `hμ := mixed_one_le_mu (by omega) hτ hτn hm`;
  -- `search_cost_of_corr hμ … (outObs e (searchObs n μ s))
  --   (outObs_searchObs_contraction _ _ _ e he) (β₀ := Real.sin (τ / n) ^ n / 2)`
  -- with `hβ₀` from `amp_ge`, `hmβ := (mixed_hyp hn hτ hτn).trans hm`,
  -- `hcorr j := mixed_corr (by omega) hμ hτ hτn hε e j _ (hacc j)`; then
  -- `mixed_root` (`β₀^{1/(2n)} ≥ ½ √(τ/n)`) and `mixed_cost_arith`.
  have hn1 : 1 ≤ n := by omega
  have hμ := mixed_one_le_mu hn1 hτ hτn hm
  have hsin := sin_div_pos hn1 hτ hτn
  have hβ₀ : 0 < Real.sin (τ / n) ^ n / 2 := div_pos (pow_pos hsin n) two_pos
  have key := search_cost_of_corr hμ P E hE O hO w hw p φ₀ hφ₀
    (outObs e (searchObs n μ s)) (outObs_searchObs_contraction _ _ _ e he) hβ₀
    ((mixed_hyp hn hτ hτn).trans hm)
    (fun j => mixed_corr hn1 hμ hτ hτn hε e j _ (hacc j))
  have hr := mixed_root hn hτ hτn
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpos : 0 ≤ Real.log 2 / 24 * n * Real.sqrt ((2 : ℝ) ^ μ) := by positivity
  rw [← mixed_cost_arith (m := (2 : ℝ) ^ μ) hn1 hτ (by positivity)]
  exact (mul_le_mul_of_nonneg_left hr hpos).trans key

end

end SparseLowerBounds.Hamiltonian
end
