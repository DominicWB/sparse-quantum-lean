import ODELowerBoundExtensions.Psd.Family

/-!
# The gadget-family bound of Theorem `odel:thm:psd`

Manuscript lines 4094-4117. Heralded output (success
probability at least `2/3` on every input, conditional accuracy `ε`, the model of `ODE.Solver`),
line 4029 ("the same heralded output as before").

* `psd_heralded_corr` (lines 4094-4095): an ideal parity-corrected expectation `≥ 7a/8` of a
  Hermitian contraction becomes, through the input-independent observable `Π (e† (M ⊗ 1) e) Π`
  (`Π` the herald), an unconditional correlation `≥ (2/3)(7a/8 - 2ε) ≥ a/4` for any amplitude
  `a ≥ 8ε` (`Readout.heralded_correlation`, eq. `odel:eq:heraldcorr`).
* `psd_search_cost` (eqs. `odel:eq:smallbias`, `odel:eq:psdmixedlocal`): with `β₀ = a/4`, the
  small-correlation search-parity lemma `hsl:lem:search` (`Hamiltonian.search_cost_of_corr`)
  gives Boolean cost `q ≥ (log 2/24) n √m β₀^{1/(2n)} ≥ (log 2/96) √(m n u)` once
  `m ≥ 64n/τ = 32n/u` (`psd_hyp`, `psd_root`), for any labelled oracle family implementable by
  one-hot Boolean queries.
* `psd_search_forces_local`: eq. `odel:eq:psdmixedlocal`, `Q_A ≥ (log 2/192) √(m n u)`, for
  the gadget family (two Boolean queries per value call, `implementsOn_psdSearchData_spec`,
  `Hamiltonian.native_bound_of_cost`; solver transfer `forces_of_spec_heat`).
* `psd_search_forces`: for `s ≥ 512n/τ`, `Q_A ≥ (log 2/(1536√2)) √(sτr)` (line 4116).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian SparseLowerBounds.ODE Readout
open scoped InnerProduct InnerProductSpace

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ} {K K' G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Heralded correlation at the PSD amplitude** (lines 4094-4095): if the output `Φ` is
heralded-accurate for `ψ` with success probability at least `2/3`, and a Hermitian contraction
`M` has signed ideal expectation `≥ 7a/8` in `ψ` for an amplitude `a ≥ 8ε` (at the main
parameters `a = psdAmp n (τ/2)`, `eight_eps_le_psdAmp`), then the heralded workspace observable
has signed correlation `≥ (2/3)(7a/8 - 2ε) ≥ a/4`. -/
theorem psd_heralded_corr (hε : 0 ≤ ε) {a : ℝ} (ha : 8 * ε ≤ a) {S : Type*} [Fintype S]
    [DecidableEq S]
    (e : K →L[ℂ] SysGarb S G) (he : e† ∘L e = 1) (herald : K →L[ℂ] K)
    (hherald : IsStarProjection herald) (Φ : K) (ψ : EuclideanSpace ℂ S)
    (hsucc : 2 / 3 ≤ ‖herald Φ‖ ^ 2) (hacc : HeraldedAccurate e herald Φ ψ ε)
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (hM : IsSelfAdjoint M) (hM1 : ‖M‖ ≤ 1)
    {sgn : ℝ} (hsgn : |sgn| ≤ 1) (hideal : 7 * a / 8 ≤ sgn * (⟪ψ, M ψ⟫_ℂ).re) :
    a / 4 ≤ sgn * (⟪Φ, (herald ∘L outObs e M ∘L herald) Φ⟫_ℂ).re := by
  have hεa : 2 * ε ≤ 7 * a / 8 := by linarith
  have h1 := (heralded_correlation e he herald hherald Φ ψ ε hacc (p₀ := 2 / 3) hsucc M hM hM1
    hsgn hideal hεa).1
  linarith

/-- **Eq. `odel:eq:psdmixedlocal`, Boolean-cost form** (lines 4097-4108): at the main
parameters with `m = 2^{psdMu s} ≥ 64n/τ`, any heralded program over a labelled oracle family
whose labels are implementable on a fixed isometric encoding with `w l` one-hot Boolean
queries, heralded-accurate (success `≥ 2/3`, conditional error `ε`) for the normalised
endpoints of the gadget family, has Boolean cost `p.cost w ≥ (log 2/96) √(m n u)`, `u = τ/2`. -/
theorem psd_search_cost (h : PsdRange τ s ε)
    (hm : 64 * (precN τ ε : ℝ) / τ ≤ (2 : ℝ) ^ psdMu s)
    (P : ProjFamily K' (Fin (precN τ ε) × Fin (2 ^ psdMu s))) (E : K →L[ℂ] K')
    (hE : E† ∘L E = 1) (O : L → (Fin (precN τ ε) → Fin (2 ^ psdMu s)) → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (precN τ ε) (psdMu s) s) G) (he : e† ∘L e = 1)
    (herald : K →L[ℂ] K) (hherald : IsStarProjection herald)
    (hsucc : ∀ j, 2 / 3 ≤ ‖herald (p.eval j φ₀)‖ ^ 2)
    (hacc : ∀ j, HeraldedAccurate e herald (p.eval j φ₀)
      (ODEStateNormalization.unitDirection
        (heat (psdSearchMat (precN τ ε) (psdMu s) s (τ / 2) j) τ
          (searchInput (precN τ ε) (psdMu s) s))) ε) :
    Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) ≤ p.cost w := by
  have hn1 := h.one_le_precN
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have ha8 := eight_eps_le_psdAmp h
  have hapos := psdAmp_pos hn1 (by linarith : (0 : ℝ) < τ / 2)
  have hobs := psdSearchObs_contraction (precN τ ε) (psdMu s) s
  -- Eq. `odel:eq:heraldcorr` with `a ≥ 8ε`: the heralded correlation is at least `a/4`.
  have hcorr : ∀ j, psdAmp (precN τ ε) (τ / 2) / 4 ≤ parity j *
      (⟪p.eval j φ₀, (herald ∘L outObs e (psdSearchObs (precN τ ε) (psdMu s) s) ∘L herald)
        (p.eval j φ₀)⟫_ℂ).re := fun j =>
    psd_heralded_corr h.eps_pos.le ha8 e he herald hherald (p.eval j φ₀) _ (hsucc j) (hacc j) _
      hobs.1 hobs.2 (abs_parity j).le
      (psd_search_corr (s := s) hn1 (one_le_psdMu h.s_ge) hτ0 j)
  have hb := search_cost_of_corr (one_le_psdMu h.s_ge) P E hE O hO w hw p φ₀ hφ₀ _
    (norm_heraldObs_le e he herald hherald hobs.2) (by linarith) ((psd_hyp h).trans hm) hcorr
  -- `√(m n u) = n √m √(u/n)`.
  have hn0 : (0 : ℝ) < precN τ ε := by exact_mod_cast (show 0 < precN τ ε by omega)
  have hu0 : (0 : ℝ) ≤ τ / 2 := by linarith
  have hy : 0 ≤ (precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ psdMu s) *
      Real.sqrt (τ / 2 / precN τ ε) := by positivity
  have hsq : ((precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ psdMu s) * Real.sqrt (τ / 2 / precN τ ε)) *
      ((precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ psdMu s) * Real.sqrt (τ / 2 / precN τ ε)) =
      (2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2) := by
    have h1 := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ psdMu s)
    have h2 := Real.mul_self_sqrt (div_nonneg hu0 hn0.le)
    calc _ = ((precN τ ε : ℝ) * precN τ ε) *
          (Real.sqrt ((2 : ℝ) ^ psdMu s) * Real.sqrt ((2 : ℝ) ^ psdMu s)) *
          (Real.sqrt (τ / 2 / precN τ ε) * Real.sqrt (τ / 2 / precN τ ε)) := by ring
      _ = ((precN τ ε : ℝ) * precN τ ε) * (2 : ℝ) ^ psdMu s * (τ / 2 / precN τ ε) := by
          rw [h1, h2]
      _ = (2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2) * (precN τ ε / precN τ ε) := by ring
      _ = (2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2) := by rw [div_self hn0.ne', mul_one]
  have key : Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) =
      (precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ psdMu s) * Real.sqrt (τ / 2 / precN τ ε) := by
    rw [← hsq]
    exact Real.sqrt_mul_self hy
  have hc : 0 ≤ Real.log 2 / 24 * (precN τ ε : ℝ) * Real.sqrt ((2 : ℝ) ^ psdMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) hn0.le)
      (Real.sqrt_nonneg _)
  calc Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2))
      = Real.log 2 / 24 * precN τ ε * Real.sqrt ((2 : ℝ) ^ psdMu s) *
          (1 / 4 * Real.sqrt (τ / 2 / precN τ ε)) := by rw [key]; ring
    _ ≤ Real.log 2 / 24 * precN τ ε * Real.sqrt ((2 : ℝ) ^ psdMu s) *
          (psdAmp (precN τ ε) (τ / 2) / 4) ^ (1 / (2 * (precN τ ε : ℝ))) :=
        mul_le_mul_of_nonneg_left (psd_root h) hc
    _ ≤ p.cost w := hb

/-- **Eq. `odel:eq:psdmixedlocal`** (line 4108): for `m ≥ 64n/τ = 32n/u`, every heralded
solver of the gadget family makes at least `(log 2/192) √(m n u)` value queries (and as many
matrix queries). -/
theorem psd_search_forces_local (h : PsdRange τ s ε)
    (hm : 64 * (precN τ ε : ℝ) / τ ≤ (2 : ℝ) ^ psdMu s) :
    (psdSearchFamilyAt h).Forces ε
      (Real.log 2 / 192 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2))) := by
  intro ι _ G _ _ _ A
  exact forces_of_spec_heat (psdSearchDataAt h) τ _ (searchInput (precN τ ε) (psdMu s) s) A
    fun p hsucc hacc => native_bound_of_cost p (by
      linarith [psd_search_cost h hm
        (psdSearchSpecBoolean (ι × Fin 1) (precN τ ε) (psdMu s) s (τ / 2)) (ancillaEmbed _)
        ancillaEmbed_isometry (specOracles (ι × Fin 1) (psdSearchDataAt h))
        (specOracles_unitary _ _) hardCost
        (implementsOn_psdSearchData_spec (ι × Fin 1) h.one_le_precN
          (two_mul_psdM_add_one_le h.s_ge))
        p A.seed A.seed_norm_le A.out A.out_isometry A.herald A.herald_proj hsucc hacc])

/-- **The gadget-family bound** (lines 4111-4117): for `s ≥ 512n/τ`, every heralded solver of
the gadget family makes at least `(log 2/(1536√2)) √(sτr)` value queries (and as many matrix
queries). -/
theorem psd_search_forces (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s) :
    (psdSearchFamilyAt h).Forces ε (psdGadgetConst * Real.sqrt (s * τ * hsR τ ε)) := by
  intro ι _ G _ _ _ A
  have hb := psd_search_forces_local h (psd_m_cond h hs) ι G A
  have ha := psd_gadget_arith h
  exact ⟨ha.trans hb.1, ha.trans hb.2⟩

end

end ODELowerBoundExtensions.Psd
