import SparseLowerBounds.Hamiltonian.Power

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Lemma `odel:lem:herald`: the Hamiltonian-simulation bound with heralding

Manuscript lines 3954-3999. The bound of Theorem `hsl:thm:main` remains
valid, with the same constants, when the simulator heralds success with
probability at least `2/3` on each input and has conditional trace error at
most `ε` (`Readout.HeraldedAccurate`: the conditional statement multiplied
through by the success probability, so no division occurs and the success
probability may depend on the input).

Route (lines 3972-3998). With the input-independent workspace observable
`Π (e† (M ⊗ 1) e) Π` (`Π` the herald, `M` the family's readout observable of
`Hamiltonian/Amplitude`), `Readout.heralded_correlation` turns the ideal
parity-corrected expectation `≥ 7A/8` (`search_corr`, `scalar_corr`) into the
unconditional correlation `≥ (2/3)(7A/8 - 2ε)` (eq. `odel:eq:heraldcorr`):

* time family: `A ≥ 1/2`, `ε ≤ 1/64`, so the correlation is
  `≥ (2/3)(13/32) > 1/4`, the correlation of the unheralded proof;
* mixed family at the main parameters: `A ≥ (τ/(2n))^n ≥ 16ε`
  (`amp_ge`, `sixteen_eps_le`), so the correlation is
  `≥ A/2`, again the correlation of the unheralded proof;
* precision family: the correlation is positive.

Then the family bounds (`search_cost_of_corr`, `precision_cost_of_corr`) and
`native_bound_of_cost` give the constants of `Hamiltonian/Theorem`.

The heralded theorems are stated at the main parameters only (where
`A ≥ 16ε`), exactly as Lemma `odel:lem:herald`: for any 2-query-implementable
labelled family (`*_herald_general`, Boolean cost), for the native primitives
(`*_herald_native`) and with a spectator register (`*_herald`), plus the
combined max form `main_max_herald`. Controlled calls
reduce to `*_herald` as in the module docstring of `Hamiltonian/Theorem`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ} {K K' G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The heralded workspace observable `Π (e† (M ⊗ 1) e) Π` is a contraction. -/
theorem norm_heraldObs_le {S : Type*} [Fintype S] [DecidableEq S] (e : K →L[ℂ] SysGarb S G)
    (he : e† ∘L e = 1) (herald : K →L[ℂ] K) (hherald : IsStarProjection herald)
    {M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S} (hM : ‖M‖ ≤ 1) :
    ‖herald ∘L outObs e M ∘L herald‖ ≤ 1 := by
  have hP1 : ‖herald‖ ≤ 1 := IsStarProjection.norm_le herald hherald
  have hA : ‖outObs e M‖ ≤ 1 := (norm_outObs_le e he M).trans hM
  calc ‖herald ∘L outObs e M ∘L herald‖ ≤ ‖herald‖ * (‖outObs e M‖ * ‖herald‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (1 * 1) := by gcongr
    _ = 1 := by norm_num

/-! ### Any 2-query-implementable family, main parameters -/

/-- **Lemma `odel:lem:herald`, time family, general form** (lines 3985-3987):
heralded success `≥ 2/3` and conditional accuracy `ε` give Boolean cost
`p.cost w ≥ (log 2/48) n √m` (`n = timeN τ`, `m = 2^{hsMu s}`). -/
theorem time_herald_general (h : HSRange τ s ε)
    (P : ProjFamily K' (Fin (timeN τ) × Fin (2 ^ hsMu s))) (E : K →L[ℂ] K') (hE : E† ∘L E = 1)
    (O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hw : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (herald : K →L[ℂ] K) (hherald : IsStarProjection herald)
    (hsucc : ∀ j, 2 / 3 ≤ ‖herald (p.eval j φ₀)‖ ^ 2)
    (hacc : ∀ j, HeraldedAccurate e herald (p.eval j φ₀)
      (evolve (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ
        (searchInput (timeN τ) (hsMu s) s)) ε) :
    Real.log 2 / 48 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) ≤ p.cost w := by
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have hA : 1 / 2 ≤ chainAmp (timeN τ) (timeC τ) τ := half_le_timeAmp h.one_le_tau
  have hε := h.eps_le
  have hobs := searchObs_contraction (timeN τ) (hsMu s) s
  have hcorr : ∀ j, (1 / 4 : ℝ) ≤ parity j *
      (⟪p.eval j φ₀, (herald ∘L outObs e (searchObs (timeN τ) (hsMu s) s) ∘L herald)
        (p.eval j φ₀)⟫_ℂ).re := by
    intro j
    have hideal := search_corr (s := s) (one_le_timeN τ) (one_le_hsMu h.s_ge) (timeC_pos hτ0)
      (timeC_le_one τ) hτ0 (by linarith) j
    have h1 := (heralded_correlation e he herald hherald (p.eval j φ₀) _ ε (hacc j) (hsucc j) _
      hobs.1 hobs.2 (le_of_eq (abs_parity j)) hideal (by linarith)).1
    linarith
  have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ hsMu s := by exact_mod_cast (hsM_range h.s_ge).1
  have hb := search_cost_of_corr (one_le_hsMu h.s_ge) P E hE O hO w hw p φ₀ hφ₀ _
    (norm_heraldObs_le e he herald hherald hobs.2) (by norm_num)
    ((quarter_hyp (one_le_timeN τ)).trans h16) hcorr
  have hc : 0 ≤ Real.log 2 / 24 * (timeN τ : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  calc Real.log 2 / 48 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s)
      = Real.log 2 / 24 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) * (1 / 2) := by ring
    _ ≤ Real.log 2 / 24 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) *
          (1 / 4 : ℝ) ^ (1 / (2 * (timeN τ : ℝ))) :=
        mul_le_mul_of_nonneg_left (quarter_root (timeN τ)) hc
    _ ≤ p.cost w := hb

/-- **Lemma `odel:lem:herald`, mixed family, general form** (lines 3988-3994):
at the main parameters with `L ≥ 64τ` and `s ≥ 64n/τ`, the heralded
correlation is `≥ A/2`, so `p.cost w ≥ (log 2/48) √(m n τ)`. -/
theorem mixed_herald_general (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    (P : ProjFamily K' (Fin (precN τ ε) × Fin (2 ^ hsMu s))) (E : K →L[ℂ] K')
    (hE : E† ∘L E = 1) (O : L → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (herald : K →L[ℂ] K) (hherald : IsStarProjection herald)
    (hsucc : ∀ j, 2 / 3 ≤ ‖herald (p.eval j φ₀)‖ ^ 2)
    (hacc : ∀ j, HeraldedAccurate e herald (p.eval j φ₀)
      (evolve (searchHam (precN τ ε) (hsMu s) s 1 τ j) τ (searchInput (precN τ ε) (hsMu s) s)) ε) :
    Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) ≤ p.cost w := by
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
  have hcorr : ∀ j, Real.sin (τ / precN τ ε) ^ precN τ ε / 2 ≤ parity j *
      (⟪p.eval j φ₀, (herald ∘L outObs e (searchObs (precN τ ε) (hsMu s) s) ∘L herald)
        (p.eval j φ₀)⟫_ℂ).re := by
    intro j
    have hideal := search_corr (s := s) hn1 (one_le_hsMu h.s_ge) one_pos le_rfl hτ0 hApos j
    have h1 := (heralded_correlation e he herald hherald (p.eval j φ₀) _ ε (hacc j) (hsucc j) _
      hobs.1 hobs.2 (le_of_eq (abs_parity j)) hideal (by rw [hA]; linarith)).1
    rw [hA] at h1
    linarith
  have hb := search_cost_of_corr (one_le_hsMu h.s_ge) P E hE O hO w hw p φ₀ hφ₀ _
    (norm_heraldObs_le e he herald hherald hobs.2) (by linarith)
    ((mixed_hyp hn2 hτ0 hτn).trans (mixed_m_cond h hs)) hcorr
  -- `√(m n τ) = n √m √(τ/n)`.
  have hn0 : (0 : ℝ) < precN τ ε := by exact_mod_cast (show 0 < precN τ ε by omega)
  have hy : 0 ≤ (precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) * Real.sqrt (τ / precN τ ε) := by
    positivity
  have hsq : ((precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) * Real.sqrt (τ / precN τ ε)) *
      ((precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) * Real.sqrt (τ / precN τ ε)) =
      (2 : ℝ) ^ hsMu s * precN τ ε * τ := by
    have h1 := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ hsMu s)
    have h2 := Real.mul_self_sqrt (div_nonneg hτ0.le hn0.le)
    calc _ = ((precN τ ε : ℝ) * precN τ ε) *
          (Real.sqrt ((2 : ℝ) ^ hsMu s) * Real.sqrt ((2 : ℝ) ^ hsMu s)) *
          (Real.sqrt (τ / precN τ ε) * Real.sqrt (τ / precN τ ε)) := by ring
      _ = ((precN τ ε : ℝ) * precN τ ε) * (2 : ℝ) ^ hsMu s * (τ / precN τ ε) := by rw [h1, h2]
      _ = (2 : ℝ) ^ hsMu s * precN τ ε * τ * (precN τ ε / precN τ ε) := by ring
      _ = (2 : ℝ) ^ hsMu s * precN τ ε * τ := by rw [div_self hn0.ne', mul_one]
  have key : Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) =
      (precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) * Real.sqrt (τ / precN τ ε) := by
    rw [← hsq]
    exact Real.sqrt_mul_self hy
  have hc : 0 ≤ Real.log 2 / 24 * (precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) hn0.le)
      (Real.sqrt_nonneg _)
  calc Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ)
      = Real.log 2 / 24 * precN τ ε * Real.sqrt ((2 : ℝ) ^ hsMu s) *
          (1 / 2 * Real.sqrt (τ / precN τ ε)) := by rw [key]; ring
    _ ≤ Real.log 2 / 24 * precN τ ε * Real.sqrt ((2 : ℝ) ^ hsMu s) *
          (Real.sin (τ / precN τ ε) ^ precN τ ε / 2) ^ (1 / (2 * (precN τ ε : ℝ))) :=
        mul_le_mul_of_nonneg_left (mixed_root hn2 hτ0 hτn) hc
    _ ≤ p.cost w := hb

/-- **Lemma `odel:lem:herald`, precision family, general form** (lines
3988-3996): at the main parameters with `L ≥ 64τ`, the heralded parity
correlation is positive, so `p.cost w ≥ n/2` (`n = ⌊r/4⌋`). -/
theorem precision_herald_general (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (P : ProjFamily K' (Fin (precN τ ε))) (E : K →L[ℂ] K') (hE : E† ∘L E = 1)
    (O : L → (Fin (precN τ ε) → Bool) → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hw : ∀ l, EncodedOracle.ImplementsOn (bitOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K)
    (e : K →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G) (he : e† ∘L e = 1)
    (herald : K →L[ℂ] K) (hherald : IsStarProjection herald)
    (hsucc : ∀ x, 2 / 3 ≤ ‖herald (p.eval x φ₀)‖ ^ 2)
    (hacc : ∀ x, HeraldedAccurate e herald (p.eval x φ₀)
      (evolve (scalarHam (precN τ ε) s τ x) τ (scalarInput (precN τ ε) s)) ε) :
    (precN τ ε : ℝ) / 2 ≤ p.cost w := by
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
      (⟪p.eval x φ₀, (herald ∘L outObs e (scalarObs (precN τ ε) s) ∘L herald)
        (p.eval x φ₀)⟫_ℂ).re := by
    intro x
    have hideal := scalar_corr (s := s) hn1 hτ0 hApos x
    have h1 := (heralded_correlation e he herald hherald (p.eval x φ₀) _ ε (hacc x) (hsucc x) _
      hobs.1 hobs.2 (le_of_eq (BitDegree.abs_bitParity x)) hideal (by rw [hA]; linarith)).1
    rw [hA] at h1
    linarith
  exact precision_cost_of_corr P E hE O hO w hw p φ₀ _
    (Finset.sum_pos (fun x _ => hpos x) Finset.univ_nonempty)

/-! ### Spectator form -/

/-- **Lemma `odel:lem:herald`, time family** (spectator form): heralded
success `≥ 2/3` and conditional accuracy `ε` force `Q ≥ c_T √s τ`. -/
theorem time_herald (h : HSRange τ s ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (timeData τ s h.s_ge)))
    (φ₀ : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (herald : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hherald : IsStarProjection herald)
    (hsucc : ∀ j, 2 / 3 ≤ ‖herald (p.eval j φ₀)‖ ^ 2)
    (hacc : ∀ j, HeraldedAccurate e herald (p.eval j φ₀)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count := by
  have hb := time_herald_general h (searchSpecBoolean Ω (timeN τ) (hsMu s) s (timeC τ) τ)
    (ancillaEmbed _) ancillaEmbed_isometry (specOracles Ω (timeData τ s h.s_ge))
    (specOracles_unitary Ω _) hardCost
    (implementsOn_searchData_spec Ω (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge))
    p φ₀ hφ₀ e he herald hherald hsucc hacc
  exact native_bound_of_cost p (by linarith [hb, time_final h.one_le_tau h.s_ge])

/-- **Lemma `odel:lem:herald`, mixed family** (spectator form): for
`L ≥ 64τ` and `s ≥ 64n/τ`, `Q ≥ (log 2/(384√2)) √(sτr)`. -/
theorem mixed_herald (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (mixedMainData τ ε s h.s_ge)))
    (φ₀ : Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (herald : Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hherald : IsStarProjection herald)
    (hsucc : ∀ j, 2 / 3 ≤ ‖herald (p.eval j φ₀)‖ ^ 2)
    (hacc : ∀ j, HeraldedAccurate e herald (p.eval j φ₀)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  have hb := mixed_herald_general h hL hs (searchSpecBoolean Ω (precN τ ε) (hsMu s) s 1 τ)
    (ancillaEmbed _) ancillaEmbed_isometry (specOracles Ω (mixedMainData τ ε s h.s_ge))
    (specOracles_unitary Ω _) hardCost
    (implementsOn_searchData_spec Ω (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge))
    p φ₀ hφ₀ e he herald hherald hsucc hacc
  exact native_bound_of_cost p (by linarith [hb, mixrbound h hL])

/-- **Lemma `odel:lem:herald`, precision family** (spectator form): for
`L ≥ 64τ`, `Q ≥ r/32`, and `Q ≥ √(sτr)/(64√2)` when `s < 64n/τ`. -/
theorem precision_herald (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (precisionMainData τ ε s h.s_ge)))
    (φ₀ : Joint Ω (ScalarSpace (precN τ ε) s τ))
    (e : Joint Ω (ScalarSpace (precN τ ε) s τ) →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G)
    (he : e† ∘L e = 1)
    (herald : Joint Ω (ScalarSpace (precN τ ε) s τ) →L[ℂ] Joint Ω (ScalarSpace (precN τ ε) s τ))
    (hherald : IsStarProjection herald)
    (hsucc : ∀ x, 2 / 3 ≤ ‖herald (p.eval x φ₀)‖ ^ 2)
    (hacc : ∀ x, HeraldedAccurate e herald (p.eval x φ₀)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    hsR τ ε / 32 ≤ p.labelCount .value ∧ hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  have hb := precision_herald_general h hL (scalarSpecBoolean Ω (precN τ ε) s τ)
    (ancillaEmbed _) ancillaEmbed_isometry (specOracles Ω (precisionMainData τ ε s h.s_ge))
    (specOracles_unitary Ω _) hardCost
    (implementsOn_scalarData_spec Ω (le_trans (by norm_num) h.s_ge))
    p φ₀ e he herald hherald hsucc hacc
  have hq := native_bound_of_cost (b := (precN τ ε : ℝ) / 4) p (by linarith [hb])
  have hrb := rbound h hL
  refine ⟨by linarith [hq.1], by linarith [hq.2], fun hs' => ?_⟩
  linarith [failedmix h hL hs', hq.1]

/-! ### Native form (no spectator) -/

/-- `time_herald` for programs over the native primitives. -/
theorem time_herald_native (h : HSRange τ s ε)
    (p : MultiOracleCircuit.Program (oracles (timeData τ s h.s_ge)))
    (φ₀ : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (herald : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ →L[ℂ]
      SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) (hherald : IsStarProjection herald)
    (hsucc : ∀ j, 2 / 3 ≤ ‖herald (p.eval j φ₀)‖ ^ 2)
    (hacc : ∀ j, HeraldedAccurate e herald (p.eval j φ₀)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count := by
  have hb := time_herald_general h (searchBoolean (timeN τ) (hsMu s) s (timeC τ) τ)
    (ancillaEmbed _) ancillaEmbed_isometry (oracles (timeData τ s h.s_ge))
    (oracles_unitary _) hardCost
    (implementsOn_searchData (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge))
    p φ₀ hφ₀ e he herald hherald hsucc hacc
  exact native_bound_of_cost p (by linarith [hb, time_final h.one_le_tau h.s_ge])

/-- `mixed_herald` for programs over the native primitives. -/
theorem mixed_herald_native (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    (p : MultiOracleCircuit.Program (oracles (mixedMainData τ ε s h.s_ge)))
    (φ₀ : SearchSpace (precN τ ε) (hsMu s) s 1 τ) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : SearchSpace (precN τ ε) (hsMu s) s 1 τ →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (herald : SearchSpace (precN τ ε) (hsMu s) s 1 τ →L[ℂ] SearchSpace (precN τ ε) (hsMu s) s 1 τ)
    (hherald : IsStarProjection herald)
    (hsucc : ∀ j, 2 / 3 ≤ ‖herald (p.eval j φ₀)‖ ^ 2)
    (hacc : ∀ j, HeraldedAccurate e herald (p.eval j φ₀)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  have hb := mixed_herald_general h hL hs (searchBoolean (precN τ ε) (hsMu s) s 1 τ)
    (ancillaEmbed _) ancillaEmbed_isometry (oracles (mixedMainData τ ε s h.s_ge))
    (oracles_unitary _) hardCost
    (implementsOn_searchData (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge))
    p φ₀ hφ₀ e he herald hherald hsucc hacc
  exact native_bound_of_cost p (by linarith [hb, mixrbound h hL])

/-- `precision_herald` for programs over the native primitives. -/
theorem precision_herald_native (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (p : MultiOracleCircuit.Program (oracles (precisionMainData τ ε s h.s_ge)))
    (φ₀ : ScalarSpace (precN τ ε) s τ)
    (e : ScalarSpace (precN τ ε) s τ →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G)
    (he : e† ∘L e = 1)
    (herald : ScalarSpace (precN τ ε) s τ →L[ℂ] ScalarSpace (precN τ ε) s τ)
    (hherald : IsStarProjection herald)
    (hsucc : ∀ x, 2 / 3 ≤ ‖herald (p.eval x φ₀)‖ ^ 2)
    (hacc : ∀ x, HeraldedAccurate e herald (p.eval x φ₀)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    hsR τ ε / 32 ≤ p.labelCount .value ∧ hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  have hb := precision_herald_general h hL (scalarBoolean (precN τ ε) s τ)
    (ancillaEmbed _) ancillaEmbed_isometry (oracles (precisionMainData τ ε s h.s_ge))
    (oracles_unitary _) hardCost (implementsOn_scalarData (le_trans (by norm_num) h.s_ge))
    p φ₀ e he herald hherald hsucc hacc
  have hq := native_bound_of_cost (b := (precN τ ε : ℝ) / 4) p (by linarith [hb])
  have hrb := rbound h hL
  refine ⟨by linarith [hq.1], by linarith [hq.2], fun hs' => ?_⟩
  linarith [failedmix h hL hs', hq.1]

/-! ### Combined statement -/

/-- **Lemma `odel:lem:herald`, combined max form** (lines
3995-3998): with heralding, `max(Q_T, Q_M, Q_P) ≥ c₀ (√s τ + √(sτr) + r)`,
`c₀ = log 2/(4096π)` unchanged (spectator form; as
`main_max`). -/
theorem main_max_herald (h : HSRange τ s ε) (ΩT ΩM ΩP : Type*)
    [Fintype ΩT] [Fintype ΩM] [Fintype ΩP] {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (specOracles ΩT (timeData τ s h.s_ge)))
    (φT : Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hφT : ‖φT‖ ≤ 1)
    (eT : Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (heraldT : Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hheraldT : IsStarProjection heraldT)
    (hsuccT : ∀ j, 2 / 3 ≤ ‖heraldT (pT.eval j φT)‖ ^ 2)
    (haccT : ∀ j, HeraldedAccurate eT heraldT (pT.eval j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (pM : MultiOracleCircuit.Program (specOracles ΩM (mixedMainData τ ε s h.s_ge)))
    (φM : Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hφM : ‖φM‖ ≤ 1)
    (eM : Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (heraldM : Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hheraldM : IsStarProjection heraldM)
    (hsuccM : ∀ j, 2 / 3 ≤ ‖heraldM (pM.eval j φM)‖ ^ 2)
    (haccM : ∀ j, HeraldedAccurate eM heraldM (pM.eval j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (pP : MultiOracleCircuit.Program (specOracles ΩP (precisionMainData τ ε s h.s_ge)))
    (φP : Joint ΩP (ScalarSpace (precN τ ε) s τ))
    (eP : Joint ΩP (ScalarSpace (precN τ ε) s τ) →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP)
    (heP : eP† ∘L eP = 1)
    (heraldP : Joint ΩP (ScalarSpace (precN τ ε) s τ) →L[ℂ] Joint ΩP (ScalarSpace (precN τ ε) s τ))
    (hheraldP : IsStarProjection heraldP)
    (hsuccP : ∀ x, 2 / 3 ≤ ‖heraldP (pP.eval x φP)‖ ^ 2)
    (haccP : ∀ x, HeraldedAccurate eP heraldP (pP.eval x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  refine assembly h (time_herald h ΩT pT φT hφT eT heT heraldT hheraldT hsuccT haccT).1
    (fun hL => ?_) (fun hL hs => ?_)
  · have := precision_herald h hL ΩP pP φP eP heP heraldP hheraldP hsuccP haccP
    exact ⟨this.1, this.2.2⟩
  · exact (mixed_herald h hL hs ΩM pM φM hφM eM heM heraldM hheraldM hsuccM haccM).1

end

end SparseLowerBounds.Hamiltonian
end
