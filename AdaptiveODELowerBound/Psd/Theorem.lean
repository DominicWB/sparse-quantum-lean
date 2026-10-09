import AdaptiveODELowerBound.Psd.Transfer

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:psd` for adaptive protocols

Manuscript lines 4453-4571 (Theorem `odel:thm:psd`, eq. `odel:eq:psd`): for `s ≥ 32`, `τ ≥ 1`
and `L ≥ 64τ` (`PsdRange`, which contains the manuscript's `τ ≥ 2`), the homogeneous
constant-coefficient families `ẋ = -D_X x` with `D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`, `1 ≤ g ≤ √2`
(`ODELowerBoundExtensions.Psd.psdSearchFamilyAt`, `psdScalarFamilyAt`) force
`Q_A ≥ psdConst (√(sτr) + r)` on adaptive solvers with the heralded output, with the constants of
the released single-program statements.

The count is by the weight method of the adaptive Hamiltonian lower bound
(`AdaptiveHamiltonianLowerBound.search_tree_cost_worst`, `precision_tree_cost`) instead of the
Boolean small-correlation search-parity lemma: one value call costs one growth factor, so the
general bounds on value calls equal the released Boolean-cost bounds and are twice the
value-call bounds derived from them.

* `psd_search_tree_general` (eqs. `odel:eq:smallbias`, `odel:eq:psdmixedlocal`): any oracle
  family with search-weight growth; the heralded correlation `(2/3)(7a/8 - 2ε) ≥ a/4`
  (`AdaptiveHamiltonianLowerBound.tree_correlation`, `psd_search_corr`, `a ≥ 8ε`) and the weight
  `β₀ = a/4` give `worstCost ≥ (log 2/96) √(m n u)`, `u = τ/2`, once `m ≥ 64n/τ`.
* `psd_scalar_tree_general` (lines 4555-4563): inputs read through `toBits`; a positive parity
  correlation gives `worstCost ≥ n/2`.
* `psd_search_forces_local_tree` (eq. `odel:eq:psdmixedlocal`, `(log 2/192) √(m n u)` for
  `m ≥ 64n/τ`), `psd_search_forces_tree` (`s ≥ 512n/τ`: `psdGadgetConst √(sτr)`, lines 4547-4553),
  `psd_scalar_forces_tree` (`r/32`, lines 4555-4562), `psd_scalar_forces_sqrt_tree`
  (`√(sτr)/256` for `s < 512n/τ`, lines 4565-4568), and the witnesses.
* `psd_max_tree`, `psd_max_cost_tree` (max forms), `psd_tree` (family form, eq. `odel:eq:psd`).
-/

namespace AdaptiveODELowerBound.Psd

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate SearchGrowth)
open AdaptiveHamiltonianLowerBound.Access (valueWeight toBits)
open ODELowerBoundExtensions.Psd
open AdaptiveODELowerBound.Model
open AdaptiveHamiltonianLowerBound (tree_correlation parity_eq_parSign abs_parSign_le
  search_tree_cost_worst outObs_contraction cast_two_pow precision_tree_cost bitParity_toBits
  searchGrowth_admissible)
open AdaptiveHamiltonianLowerBound.Access (admissible_unitary)
open SparseLowerBounds.Readout (outObs)
open LinearSystemLowerBound (corr parSign)
open scoped InnerProduct InnerProductSpace

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- The PSD amplitude `a = e^{-u} sinh(u/n)^n` is at most one for `u ≥ 0`
(`sinh(u/n) ≤ e^{u/n}`). -/
theorem psdAmp_le_one {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) : psdAmp n u ≤ 1 := by
  unfold psdAmp
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hx : 0 ≤ u / n := div_nonneg hu (Nat.cast_nonneg _)
  have h0 : 0 ≤ Real.sinh (u / n) := Real.sinh_nonneg_iff.mpr hx
  have h1 : Real.sinh (u / n) ≤ Real.exp (u / n) := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos (-(u / n)), Real.exp_pos (u / n)]
  have h2 : Real.sinh (u / n) ^ n ≤ Real.exp (u / n) ^ n := pow_le_pow_left₀ h0 h1 n
  have h3 : Real.exp (u / n) ^ n = Real.exp u := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [h3] at h2
  calc Real.exp (-u) * Real.sinh (u / n) ^ n ≤ Real.exp (-u) * Real.exp u :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

variable {τ ε : ℝ} {s : ℕ}

/-- **Eq. `odel:eq:psdmixedlocal` for adaptive protocols, general form** (lines 4532-4545): at
the main parameters with `m = 2^{psdMu s} ≥ 64n/τ`, an adaptive protocol over any oracle family
with search-weight growth, heralded-accurate (success `≥ 2/3`, conditional error `ε`) for the
normalised endpoints of the gadget family, has worst-case cost at least
`(log 2/96) √(m n u)`, `u = τ/2`. -/
theorem psd_search_tree_general (h : PsdRange τ s ε)
    (hm : 64 * (precN τ ε : ℝ) / τ ≤ (2 : ℝ) ^ psdMu s) {L K Fl E G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : L → (Fin (precN τ ε) → Fin (2 ^ psdMu s)) → K →L[ℂ] K}
    (hU : ∀ l j, IsUnitary (O l j)) (w : L → ℕ) (hO : SearchGrowth (2 ^ psdMu s) O w)
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (SearchIndex (precN τ ε) (psdMu s) s) G)
    (he : e† ∘L e = 1) (hsucc : ∀ j, 2 / 3 ≤ T.successMass j)
    (hacc : ∀ j, DensityAccurate e (T.conditionalDensity j)
      (ODEStateNormalization.unitDirection
        (heat (psdSearchMat (precN τ ε) (psdMu s) s (τ / 2) j) τ
          (searchInput (precN τ ε) (psdMu s) s))) ε) :
    Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) ≤ T.worstCost w := by
  have hn1 := h.one_le_precN
  have hμ := one_le_psdMu h.s_ge
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have ha8 := eight_eps_le_psdAmp h
  have hapos := psdAmp_pos hn1 (by linarith : (0 : ℝ) < τ / 2)
  have ha1 := psdAmp_le_one hn1 (by linarith : (0 : ℝ) ≤ τ / 2)
  have hε0 := h.eps_pos
  have hobs := psdSearchObs_contraction (precN τ ε) (psdMu s) s
  -- Eq. `odel:eq:heraldcorr` with `a ≥ 8ε`: the heralded correlation is at least `a/4`.
  have hcorr : ∀ j, psdAmp (precN τ ε) (τ / 2) / 4 ≤ parSign j *
      corr (outObs e (psdSearchObs (precN τ ε) (psdMu s) s)) (T.successDensity j) := by
    intro j
    have hideal := psd_search_corr (s := s) hn1 hμ hτ0 j
    rw [parity_eq_parSign] at hideal
    have h1 := tree_correlation e T j _ ε (hacc j) (hsucc j) _ hobs.1 hobs.2
      (abs_parSign_le j) hideal (by linarith)
    linarith
  have heven : Even (2 ^ psdMu s) := (Nat.even_pow' (by omega)).mpr even_two
  have hb := search_tree_cost_worst hn1 heven hU w hO _
    (outObs_contraction e he _ hobs.2) T (by positivity) (by linarith)
    (by rw [cast_two_pow]; exact (psd_hyp h).trans hm) hcorr
  rw [cast_two_pow] at hb
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
    _ ≤ T.worstCost w := hb

/-- **The scalar family for adaptive protocols, general form** (lines 4555-4563): inputs
`x : Fin n → Bool`, labels with search-weight growth along `toBits`, heralded-accurate for the
normalised endpoints of the scalar family; `worstCost ≥ n/2` (`n = ⌊r/4⌋`). -/
theorem psd_scalar_tree_general (h : PsdRange τ s ε) {L K Fl E G : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : L → (Fin (precN τ ε) → Bool) → K →L[ℂ] K}
    (hU : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hO : SearchGrowth 2 (fun l j => O l (toBits j)) w) (T : Tree O Fl E)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x)
      (ODEStateNormalization.unitDirection
        (heat (psdScalarMat (precN τ ε) s (τ / 2) x) τ (scalarInput (precN τ ε) s))) ε) :
    (precN τ ε : ℝ) / 2 ≤ T.worstCost w := by
  have hn1 := h.one_le_precN
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have ha8 := eight_eps_le_psdAmp h
  have hapos := psdAmp_pos hn1 (by linarith : (0 : ℝ) < τ / 2)
  have hε0 := h.eps_pos
  have hobs := psdScalarObs_contraction (precN τ ε) s
  -- Eq. `odel:eq:heraldcorr`: the heralded parity correlation is positive on every input.
  have hpos : ∀ x, 0 < BitDegree.bitParity x *
      corr (outObs e (psdScalarObs (precN τ ε) s)) (T.successDensity x) := by
    intro x
    have hideal := psd_scalar_corr (s := s) hn1 hτ0 x
    have h1 := tree_correlation e T x _ ε (hacc x) (hsucc x) _ hobs.1 hobs.2
      (le_of_eq (BitDegree.abs_bitParity x)) hideal (by linarith)
    linarith
  have hsum : 0 < ∑ j, parSign j * corr (outObs e (psdScalarObs (precN τ ε) s))
      ((AdaptiveHamiltonianLowerBound.Reindex.tree toBits T).successDensity j) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro j _
    rw [AdaptiveHamiltonianLowerBound.Reindex.successDensity_tree, ← bitParity_toBits]
    exact hpos _
  have hb := precision_tree_cost (fun l j => hU l (toBits j)) w hO _
    (outObs_contraction e he _ hobs.2) (AdaptiveHamiltonianLowerBound.Reindex.tree toBits T)
    hsum
  rwa [AdaptiveHamiltonianLowerBound.Reindex.worstCost_tree] at hb

/-- **The scalar family tree-forces `n/2`** (lines 4555-4562, `n = ⌊r/4⌋`): the sampled-time
access and its call forms are admissible for the scalar data, which have one-bit entries along
`toBits`, so `psd_scalar_tree_general` applies. -/
theorem psd_scalar_forces_half_tree (h : PsdRange τ s ε) :
    TreeForces (psdScalarFamilyAt h) ε ((precN τ ε : ℝ) / 2) := by
  have hD := hardAccess_psdScalarData (precN τ ε) s (τ / 2) h.one_le_precN
    (by have := h.s_ge; omega)
  refine treeForces_of_heat (psdScalarDataAt h) τ _ (scalarInput (precN τ ε) s)
    hD.row_const hD.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO P e he hsucc hacc
  exact psd_scalar_tree_general h (O := O) (fun l x => admissible_unitary _ _ _ (hO l) x) w
    (searchGrowth_admissible even_two _ _ hD O w hO) P e he hsucc hacc

/-- **Eq. `odel:eq:psdmixedlocal` for adaptive protocols** (lines 4542-4545; as
`ODELowerBoundExtensions.Psd.psd_search_forces_local`): for `m = 2^{psdMu s} ≥ 64n/τ`, the gadget
family tree-forces `(log 2/192) √(m n u)` value calls (and as many calls in total), `u = τ/2`. -/
theorem psd_search_forces_local_tree (h : PsdRange τ s ε)
    (hm : 64 * (precN τ ε : ℝ) / τ ≤ (2 : ℝ) ^ psdMu s) :
    TreeForces (psdSearchFamilyAt h) ε
      (Real.log 2 / 192 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2))) := by
  have hD := hardAccess_psdSearchData (precN τ ε) (psdMu s) s (τ / 2) h.one_le_precN
    (two_mul_psdM_add_one_le h.s_ge)
  have heven : Even (2 ^ psdMu s) :=
    (Nat.even_pow' (by have := one_le_psdMu h.s_ge; omega)).mpr even_two
  have hX : 0 ≤ Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) := Real.sqrt_nonneg _
  have hl : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  have hlX := mul_nonneg hl hX
  refine treeForces_of_heat (psdSearchDataAt h) τ _ (searchInput (precN τ ε) (psdMu s) s)
    hD.row_const hD.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO P e he hsucc hacc
  have hb := psd_search_tree_general h hm (O := O)
    (fun l j => admissible_unitary _ _ _ (hO l) j) w
    (searchGrowth_admissible heven _ _ hD O w hO) P e he hsucc hacc
  linarith

/-- **The gadget-family bound for adaptive protocols** (lines 4547-4553): for `s ≥ 512n/τ`, the
gadget family tree-forces `(log 2/(1536√2)) √(sτr)` value calls (and as many calls in total). -/
theorem psd_search_forces_tree (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s) :
    TreeForces (psdSearchFamilyAt h) ε (psdGadgetConst * Real.sqrt (s * τ * hsR τ ε)) := by
  exact treeForces_of_cost fun _ hq => (psd_gadget_arith h).trans
    ((psd_search_forces_local_tree h (psd_m_cond h hs)).le_cost hq)

/-- **The scalar-family bound for adaptive protocols** (lines 4555-4562): the scalar family
tree-forces `r/32` value calls (and as many calls in total). -/
theorem psd_scalar_forces_tree (h : PsdRange τ s ε) :
    TreeForces (psdScalarFamilyAt h) ε (hsR τ ε / 32) := by
  have hn : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have hb : hsR τ ε / 32 ≤ (precN τ ε : ℝ) / 2 := by linarith [rbound h.toHSRange h.hL]
  exact treeForces_of_cost fun _ hq => hb.trans ((psd_scalar_forces_half_tree h).le_cost hq)

/-- **The scalar family for small sparsity, adaptive protocols** (lines 4565-4568): for
`s < 512n/τ`, the scalar family tree-forces `√(sτr)/256` value calls. -/
theorem psd_scalar_forces_sqrt_tree (h : PsdRange τ s ε) (hs : (s : ℝ) < 512 * precN τ ε / τ) :
    TreeForces (psdScalarFamilyAt h) ε (Real.sqrt (s * τ * hsR τ ε) / 256) := by
  have hn : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have hb : Real.sqrt (s * τ * hsR τ ε) / 256 ≤ (precN τ ε : ℝ) / 2 := by
    linarith [psd_scalar_sqrt h hs]
  exact treeForces_of_cost fun _ hq => hb.trans ((psd_scalar_forces_half_tree h).le_cost hq)

/-- **The gadget family tree-witnesses `(log 2/(1536√2)) √(sτr)`** for `s ≥ 512n/τ` and any
`ḡ ≥ √2`. -/
theorem psd_search_witness_tree (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s)
    {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    TreeWitnesses (psdSearchFamilyAt h) τ gbar ε
      (psdGadgetConst * Real.sqrt (s * τ * hsR τ ε)) := by
  exact ⟨psdSearchFamilyAt_inClass h hg, psdSearchFamilyAt_T h, psd_search_forces_tree h hs⟩

/-- **The scalar family tree-witnesses `r/32`** for any `ḡ ≥ √2`. -/
theorem psd_scalar_witness_tree (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    TreeWitnesses (psdScalarFamilyAt h) τ gbar ε (hsR τ ε / 32) := by
  exact ⟨psdScalarFamilyAt_inClass h hg, psdScalarFamilyAt_T h, psd_scalar_forces_tree h⟩

/-- **Theorem `odel:thm:psd` for adaptive protocols, max form**: for one adaptive solver of the
gadget family and one of the scalar family over the sampled-time access, the larger worst-case
value count is at least `psdConst (√(sτr) + r)`, `psdConst = log 2/(3072√2)`. -/
theorem psd_max_tree (h : PsdRange τ s ε) {ιG ιS FlG FlS EG ES GG GS : Type}
    [Fintype ιG] [Fintype ιS]
    [NormedAddCommGroup FlG] [InnerProductSpace ℂ FlG] [CompleteSpace FlG]
    [NormedAddCommGroup FlS] [InnerProductSpace ℂ FlS] [CompleteSpace FlS]
    [NormedAddCommGroup EG] [InnerProductSpace ℂ EG] [CompleteSpace EG] [FiniteDimensional ℂ EG]
    [NormedAddCommGroup ES] [InnerProductSpace ℂ ES] [CompleteSpace ES] [FiniteDimensional ℂ ES]
    [NormedAddCommGroup GG] [InnerProductSpace ℂ GG] [CompleteSpace GG]
    [NormedAddCommGroup GS] [InnerProductSpace ℂ GS] [CompleteSpace GS]
    (AG : TreeSolver (psdSearchFamilyAt h) ((psdSearchFamilyAt h).access ιG) FlG EG GG ε)
    (AS : TreeSolver (psdScalarFamilyAt h) ((psdScalarFamilyAt h).access ιS) FlS ES GS ε) :
    psdBound s τ ε ≤
      max (AG.tree.worstCost valueWeight : ℝ) (AS.tree.worstCost valueWeight : ℝ) := by
  unfold psdBound
  exact psd_assembly h ((psd_scalar_forces_tree h).1 ιS FlS ES GS AS).1
    (fun hs => ((psd_scalar_forces_sqrt_tree h hs).1 ιS FlS ES GS AS).1)
    (fun hs => ((psd_search_forces_tree h hs).1 ιG FlG EG GG AG).1)

/-- **Theorem `odel:thm:psd` for adaptive protocols, max form over realised counts**: for realised
worst-case value counts of adaptive solvers of the two families, each over the sampled-time access
or over its call forms, `psdConst (√(sτr) + r) ≤ max(q_G, q_S)`. -/
theorem psd_max_cost_tree (h : PsdRange τ s ε) {qG qS : ℝ}
    (hG : TreeCost (psdSearchFamilyAt h) ε qG) (hS : TreeCost (psdScalarFamilyAt h) ε qS) :
    psdBound s τ ε ≤ max qG qS := by
  unfold psdBound
  exact psd_assembly h ((psd_scalar_forces_tree h).le_cost hS)
    (fun hs => (psd_scalar_forces_sqrt_tree h hs).le_cost hS)
    (fun hs => (psd_search_forces_tree h hs).le_cost hG)

/-- **Theorem `odel:thm:psd` for adaptive protocols** (eq. `odel:eq:psd`, lines 4453-4466): for
`s ≥ 32`, `τ ≥ 1`, `L ≥ 64τ` (`PsdRange`) and any `ḡ ≥ √2`, one of the two homogeneous
constant-coefficient PSD families (`D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`, `1 ≤ g ≤ √2`) is in the class
(`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `psdConst (√(sτr) + r)` value calls (and as many calls in
total) on every adaptive solver with the heralded output, over the sampled-time access or over
its call forms, `psdConst = log 2/(3072√2)`. The instance facts are those of the released
families: no source, `B = 1`, `T = τ` and `1 ≤ g ≤ √2`
(`ODELowerBoundExtensions.Psd.psdSearchFamilyAt_props`, `psdScalarFamilyAt_props`), and
`‖D_X‖ = 1` with maximum sparsity exactly `s` by the dense PSD padding
(`ODELowerBoundExtensions.Psd.psdSearchMat_props`, `psdScalarMat_props`). -/
theorem psd_tree (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    TreeWitnesses (psdSearchFamilyAt h) τ gbar ε (psdBound s τ ε) ∨
      TreeWitnesses (psdScalarFamilyAt h) τ gbar ε (psdBound s τ ε) := by
  rcases forces_or_of_cost₂ (P₁ := TreeCost (psdSearchFamilyAt h) ε)
      (P₂ := TreeCost (psdScalarFamilyAt h) ε) (b := psdBound s τ ε)
      (fun _ _ h₁ h₂ => psd_max_cost_tree h h₁ h₂) with hf | hf
  · exact Or.inl
      ⟨psdSearchFamilyAt_inClass h hg, psdSearchFamilyAt_T h, treeForces_of_cost hf⟩
  · exact Or.inr
      ⟨psdScalarFamilyAt_inClass h hg, psdScalarFamilyAt_T h, treeForces_of_cost hf⟩

end

end AdaptiveODELowerBound.Psd
