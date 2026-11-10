import OptimalLowerBounds.AdaptiveAccess

set_option synthInstance.maxHeartbeats 400000

/-!
# Proposition `hsl:prop:two-norm` for adaptive protocols

Proposition `hsl:prop:two-norm` (manuscript section `twonorml:sec:lower`) states "The output need
only satisfy the known-input system trace-distance guarantee [eq. `hsl:eq:accuracy`], with physical
time `t` replacing `τ` in the target state, permitting mixed states but no postselection"; its proof
reduces the enlarged families to the original ones
("Its lower bound is therefore `Ω(√s₀ θ + √(s₀ θ r_μ) + r_μ)`"). Theorem `hsl:thm:main` covers
adaptive algorithms ("Purification and deferred measurement include adaptive and randomised
algorithms", proof of Lemma `hsl:lem:precision`); its adaptive form is
`AdaptiveHamiltonianLowerBound.main_max_tree`. This module proves the proposition for the same
**adaptive protocols** (`SparseLinearSystems.Protocol.Tree`: fresh measured runs with classical
branching on the outcomes, random trial labels and repeated trials, a heralded output), with every
oracle label admissible for the enlarged data (native calls with spectators, controls, masks,
inverses and coherent choices of the native query, counted with their weight; input-independent
unitaries of any weight), success probability at least `2/3` on every input and conditional output
`ε`-accurate in trace distance (`DensityAccurate`, mixed outputs allowed).

* **Discarding the ancilla from a mixed output** (`densityAccurate_of_embedU`): conditional
  accuracy for `V φ = φ ⊗ u_m`, read through `e`, is conditional accuracy for `φ` read through
  `regroup ∘ e` (the ancilla joins the garbage); the observable `M` is tested as `M ⊗ 1_m`
  (`outObs_regroup`, module `Embedding`). With `evolve_enlarge` this turns accuracy on an
  enlarged family into accuracy on the original family at time `θ = c m t`
  (`densityAccurate_search_of_two`, `densityAccurate_scalar_of_two`).
* **The family bounds** (`time_two_tree`, `mixed_two_tree`, `precision_two_tree`): the enlarged
  data have one-bit entries (`hardAccess_timeTwo`, …), so admissible labels have search-weight
  growth (`AdaptiveHamiltonianLowerBound.searchGrowth_admissible`) and the general bounds of the
  weight method apply (`AdaptiveHamiltonianLowerBound.time_tree_general`, …), with the paper's
  constants: `c_T √s₀ θ`, `(log 2/(384√2)) √(s₀ θ r_μ)`, `r_μ/32` and `√(s₀ θ r_μ)/(64√2)` (for
  `s₀ < 64n/θ`).
* **`two_norm_main_max_tree`** (eq. `twonorml:eq:lower`, max form): for any three adaptive
  protocols, `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(Q_T, Q_M, Q_P)`, `Q` the worst-case weighted
  number of calls over all transcripts, `c₀ = log 2/(4096π)`.
* **`precision_scalar_tree`**: Lemma `hsl:lem:precision` at the main parameters for adaptive
  protocols on the signed scalar chain of any sparsity (used for the denominator paragraph, where
  the chain has sparsity two; `AdaptiveHamiltonianLowerBound.precision_tree_general` is stated in
  the range `HSRange τ s ε`, which ties the chain's sparsity to `s ≥ 32`, so its proof is
  repeated with the sparsity free); **`denom_lower_tree`** (`r_μ/32` for `k ≥ 47`) and
  **`wrong_denominator_tree`** (more than `C · wrongShape` for `k ≥ max(47, ⌈(384 C)² + 3⌉)`).
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open SparseLinearSystems.Protocol LinearSystemLowerBound
open AdaptiveHamiltonianLowerBound (DensityAccurate SearchGrowth)
open AdaptiveHamiltonianLowerBound.Access (Admissible toBits)
open scoped InnerProduct InnerProductSpace BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### Discarding the uniform ancilla from a mixed output -/

section Density

variable {N : Type} [Fintype N] [DecidableEq N] {G : Type*} [NormedAddCommGroup G]
  [InnerProductSpace ℂ G] [CompleteSpace G]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Discarding the ancilla preserves the accuracy of a mixed output** (proof of
`hsl:prop:two-norm`, on discarding the added register: "Trace distance contracts under this
operation, so an `ε`-accurate enlarged output yields an `ε`-accurate old output, even when the
simulation output is mixed"): if the output `ρ` read through `e` into
`ℂ^{N × Fin m} ⊗ G` is `ε`-accurate for `V φ = φ ⊗ u_m`, then `ρ` read through `regroup ∘ e` into
`ℂ^N ⊗ (ℂ^m ⊗ G)` is `ε`-accurate for `φ`. -/
theorem densityAccurate_of_embedU (m : ℕ) (hm : 0 < m) (e : E →L[ℂ] SysGarb (N × Fin m) G)
    (ρ : E →L[ℂ] E) (φ : EuclideanSpace ℂ N) (ε : ℝ)
    (hacc : DensityAccurate e ρ (embedU m φ) ε) :
    DensityAccurate (((regroup N (Fin m) G) :
      SysGarb (N × Fin m) G →L[ℂ] SysGarb N (Joint (Fin m) G)) ∘L e) ρ φ ε := by
  intro M hM hM1
  have h := hacc (liftU m M) (isSelfAdjoint_liftU m hM) ((norm_liftU_le m M).trans hM1)
  rw [outObs_regroup, ← inner_embedU_liftU m hm M φ]
  exact h

end Density

/-! ### Accuracy on an enlarged family is accuracy on the original family -/

section Transfer

variable {m : ℕ} {c t ε : ℝ} {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Conditional accuracy for an enlarged search family at time `t` is conditional accuracy for
the original family at time `τ = c m t`, the ancilla moved to the garbage. -/
theorem densityAccurate_search_of_two {n μ s : ℕ} {a τ : ℝ} (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s)
    (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = τ)
    (e : E →L[ℂ] SysGarb (SearchIndex n μ s × Fin m) G) (ρ : E →L[ℂ] E)
    (j : Fin n → Fin (2 ^ μ))
    (hacc : DensityAccurate e ρ (evolve ((searchTwo n μ s a τ hμ hs m hm c hc).matrix j) t
      (embedU m (searchInput n μ s))) ε) :
    DensityAccurate (((regroup (SearchIndex n μ s) (Fin m) G) :
        SysGarb (SearchIndex n μ s × Fin m) G →L[ℂ]
          SysGarb (SearchIndex n μ s) (Joint (Fin m) G)) ∘L e) ρ
      (evolve (searchHam n μ s a τ j) τ (searchInput n μ s)) ε := by
  rw [searchTwo_matrix, evolve_enlarge, hθ] at hacc
  exact densityAccurate_of_embedU m hm e ρ _ ε hacc

/-- Conditional accuracy for the enlarged scalar family at time `t` is conditional accuracy for
the original family at time `τ = c m t`. -/
theorem densityAccurate_scalar_of_two {n s : ℕ} {τ : ℝ} (hs : 2 ≤ s) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = τ) (e : E →L[ℂ] SysGarb (ScalarIndex n s × Fin m) G) (ρ : E →L[ℂ] E)
    (x : Fin n → Bool)
    (hacc : DensityAccurate e ρ (evolve ((scalarTwo n s τ hs m hm c hc).matrix x) t
      (embedU m (scalarInput n s))) ε) :
    DensityAccurate (((regroup (ScalarIndex n s) (Fin m) G) :
        SysGarb (ScalarIndex n s × Fin m) G →L[ℂ]
          SysGarb (ScalarIndex n s) (Joint (Fin m) G)) ∘L e) ρ
      (evolve (scalarHam n s τ x) τ (scalarInput n s)) ε := by
  rw [scalarTwo_matrix, evolve_enlarge, hθ] at hacc
  exact densityAccurate_of_embedU m hm e ρ _ ε hacc

end Transfer

/-! ### The family bounds for adaptive protocols -/

section Families

variable {θ ε : ℝ} {s m : ℕ} {c t : ℝ} {K F E G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Enlarged time family, adaptive protocols** (eq. `hsl:eq:timelower` at `s₀`, `θ`): every
adaptive protocol over admissible labels of `timeTwo` that heralds success with probability at
least `2/3` on every input and is conditionally `ε`-accurate for `e^{-itH_X}(ψ_in ⊗ u_m)`
(`c m t = θ`) has worst-case cost at least `c_T √s₀ θ`. -/
theorem time_two_tree (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    (O : L → (Fin (timeN θ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (timeTwo θ s h.s_ge m hm c hc) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ T.successMass j)
    (hacc : ∀ j, DensityAccurate e (T.conditionalDensity j)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε) :
    cT * Real.sqrt s * θ ≤ T.worstCost w := by
  have hb := AdaptiveHamiltonianLowerBound.time_tree_general h
    (fun l j => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) j) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible
      (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ _
      (hardAccess_timeTwo h.s_ge hm hc) O w hO) T _ (regroup_comp_isometry m e he) hsucc
    (fun j => densityAccurate_search_of_two _ _ hm hc hθ e _ j (hacc j))
  have hX : 0 ≤ Real.log 2 / 96 * timeN θ * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  linarith [time_final h.one_le_tau h.s_ge]

/-- **Enlarged mixed family, adaptive protocols** (eq. `hsl:eq:mixrbound` at `s₀`, `θ`): for
`L ≥ 64θ` and `s₀ ≥ 64n/θ`, worst-case cost at least `(log 2/(384√2)) √(s₀ θ r_μ)`. -/
theorem mixed_two_tree (h : HSRange θ s ε) (hL : 64 * θ ≤ hsL ε)
    (hs : 64 * (precN θ ε : ℝ) / θ ≤ s) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    (O : L → (Fin (precN θ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (mixedTwo θ ε s h.s_ge m hm c hc) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) G) (he : e† ∘L e = 1)
    (hsucc : ∀ j, 2 / 3 ≤ T.successMass j)
    (hacc : ∀ j, DensityAccurate e (T.conditionalDensity j)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * θ * hsR θ ε) ≤ T.worstCost w := by
  have hb := AdaptiveHamiltonianLowerBound.mixed_tree_general h hL hs
    (fun l j => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) j) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible
      (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ _
      (hardAccess_mixedTwo h.s_ge hm hc) O w hO) T _ (regroup_comp_isometry m e he) hsucc
    (fun j => densityAccurate_search_of_two _ _ hm hc hθ e _ j (hacc j))
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN θ ε * θ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  linarith [mixrbound h hL]

/-- **Enlarged precision family, adaptive protocols** (eqs. `hsl:eq:rbound`,
`hsl:eq:failedmix` at `s₀`, `θ`): for `L ≥ 64θ`, worst-case cost at least `r_μ/32`, and at least
`√(s₀ θ r_μ)/(64√2)` when `s₀ < 64n/θ`. -/
theorem precision_two_tree (h : HSRange θ s ε) (hL : 64 * θ ≤ hsL ε) (hm : 0 < m)
    (hc : c ≠ 0) (hθ : c * m * t = θ)
    (O : L → (Fin (precN θ ε) → Bool) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (precisionTwo θ ε s h.s_ge m hm c hc) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    hsR θ ε / 32 ≤ T.worstCost w ∧
      ((s : ℝ) < 64 * precN θ ε / θ →
        Real.sqrt (s * θ * hsR θ ε) / (64 * Real.sqrt 2) ≤ T.worstCost w) := by
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general h hL
    (fun l x => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) x) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible even_two _ _
      (hardAccess_precisionTwo h.s_ge hm hc) O w hO) T _ (regroup_comp_isometry m e he) hsucc
    (fun x => densityAccurate_scalar_of_two _ hm hc hθ e _ x (hacc x))
  have hn0 : (0 : ℝ) ≤ precN θ ε := Nat.cast_nonneg _
  refine ⟨by linarith [rbound h hL], fun hs' => ?_⟩
  linarith [failedmix h hL hs']

/-- **Lemma `hsl:lem:precision` at the main parameters, adaptive protocols, any sparsity**: for
`θ ≥ 1`, `0 < ε ≤ 1/64` (the range `HSRange θ 32 ε` only carries these here), `L ≥ 64θ` and
every sparsity parameter `s₀`, every adaptive protocol whose labels have search-weight growth
along `toBits`, with success probability at least `2/3` and conditional output `ε`-accurate for
the signed scalar chain of length `n = ⌊r/4⌋` (`scalarHam n s₀ θ`), has worst-case cost at least
`r/32`. -/
theorem precision_scalar_tree (h : HSRange θ 32 ε) (hL : 64 * θ ≤ hsL ε) {s₀ : ℕ}
    {O : L → (Fin (precN θ ε) → Bool) → K →L[ℂ] K} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth 2 (fun l j => O l (toBits j)) w) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s₀) G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x)
      (evolve (scalarHam (precN θ ε) s₀ θ x) θ (scalarInput (precN θ ε) s₀)) ε) :
    hsR θ ε / 32 ≤ T.worstCost w := by
  obtain ⟨hn2, hrn, hτr, -⟩ := precN_range h hL
  have hτ0 : 0 < θ := by linarith [h.one_le_tau]
  have hτn : θ ≤ precN θ ε := by linarith
  have hn1 : 1 ≤ precN θ ε := by omega
  have h16 := sixteen_eps_le h hL
  have hamp := amp_ge hn1 hτ0 hτn
  have hε0 := h.eps_pos
  have hA : chainAmp (precN θ ε) 1 θ = Real.sin (θ / precN θ ε) ^ precN θ ε := by
    rw [chainAmp, one_mul]
  have hApos : 0 < chainAmp (precN θ ε) 1 θ := by rw [hA]; linarith
  have hobs := scalarObs_contraction (precN θ ε) s₀
  -- Eq. `odel:eq:heraldcorr`: the heralded parity correlation is positive on every input.
  have hpos : ∀ x, 0 < BitDegree.bitParity x *
      corr (outObs e (scalarObs (precN θ ε) s₀)) (T.successDensity x) := by
    intro x
    have hideal := scalar_corr (s := s₀) hn1 hτ0 hApos x
    rw [hA] at hideal
    have h1 := AdaptiveHamiltonianLowerBound.tree_correlation e T x _ ε (hacc x) (hsucc x) _
      hobs.1 hobs.2 (le_of_eq (BitDegree.abs_bitParity x)) hideal (by linarith)
    linarith
  have hsum : 0 < ∑ j, parSign j * corr (outObs e (scalarObs (precN θ ε) s₀))
      ((AdaptiveHamiltonianLowerBound.Reindex.tree toBits T).successDensity j) := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro j _
    rw [AdaptiveHamiltonianLowerBound.Reindex.successDensity_tree,
      ← AdaptiveHamiltonianLowerBound.bitParity_toBits]
    exact hpos _
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_cost (fun l j => hU l (toBits j)) w hO _
    (AdaptiveHamiltonianLowerBound.outObs_contraction e he _ hobs.2)
    (AdaptiveHamiltonianLowerBound.Reindex.tree toBits T) hsum
  rw [AdaptiveHamiltonianLowerBound.Reindex.worstCost_tree] at hb
  have hrb := rbound h hL
  have hn0 : (0 : ℝ) ≤ precN θ ε := Nat.cast_nonneg _
  linarith

end Families

/-! ### Proposition `hsl:prop:two-norm` for adaptive protocols -/

variable {θ ε : ℝ} {s m : ℕ} {c t : ℝ}

/-- **Proposition `hsl:prop:two-norm` for adaptive protocols, max form** (eq.
`twonorml:eq:lower`): for any three adaptive protocols over admissible labels of the enlarged
time, mixed and precision families respectively, each heralding success with probability at
least `2/3` on every input with conditional output `ε`-accurate in trace distance for
`e^{-itH_X}(ψ_in ⊗ u_m)` (`c m t = θ`), and `s = s₀ m`, `η = |c|√m`, `μ = |c|`,
`r_μ = hsR θ ε`: `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(Q_T, Q_M, Q_P)`, where `Q` is the
worst-case weighted number of calls over all transcripts and `c₀ = log 2/(4096π)`. -/
theorem two_norm_main_max_tree (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = θ)
    {KT FT ET GT LT KM FM EM GM LM KP FP EP GP LP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup FT] [InnerProductSpace ℂ FT] [CompleteSpace FT]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup FM] [InnerProductSpace ℂ FM] [CompleteSpace FM]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    [NormedAddCommGroup FP] [InnerProductSpace ℂ FP] [CompleteSpace FP]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (OT : LT → (Fin (timeN θ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT) (wT : LT → ℕ)
    (hOT : ∀ l, Admissible (timeTwo θ s h.s_ge m hm c hc) (OT l) (wT l)) (TT : Tree OT FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TT.successMass j)
    (haccT : ∀ j, DensityAccurate eT (TT.conditionalDensity j)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε)
    (OM : LM → (Fin (precN θ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM) (wM : LM → ℕ)
    (hOM : ∀ l, Admissible (mixedTwo θ ε s h.s_ge m hm c hc) (OM l) (wM l)) (TM : Tree OM FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) GM)
    (heM : eM† ∘L eM = 1) (hsuccM : ∀ j, 2 / 3 ≤ TM.successMass j)
    (haccM : ∀ j, DensityAccurate eM (TM.conditionalDensity j)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε)
    (OP : LP → (Fin (precN θ ε) → Bool) → KP →L[ℂ] KP) (wP : LP → ℕ)
    (hOP : ∀ l, Admissible (precisionTwo θ ε s h.s_ge m hm c hc) (OP l) (wP l))
    (TP : Tree OP FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TP.successMass x)
    (haccP : ∀ x, DensityAccurate eP (TP.conditionalDensity x)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
      max (TT.worstCost wT : ℝ) (max (TM.worstCost wM : ℝ) (TP.worstCost wP)) := by
  rw [two_shape_eq hθ h.tau_pos]
  exact assembly h (time_two_tree h hm hc hθ OT wT hOT TT eT heT hsuccT haccT)
    (fun hL => precision_two_tree h hL hm hc hθ OP wP hOP TP eP heP hsuccP haccP)
    (fun hL hs => mixed_two_tree h hL hs hm hc hθ OM wM hOM TM eM heM hsuccM haccM)

/-! ### The denominator paragraph for adaptive protocols -/

/-- **The required queries for adaptive protocols** (eq. `twonorml:eq:necessary-denominator`):
for `k ≥ 47` every adaptive protocol over admissible labels of `denomData k` that heralds success
with probability at least `2/3` and is conditionally `ε`-accurate (`ε = e^{-L}`) for
`e^{-iH_x}(ψ_in ⊗ u_m)` at `t = 1` has worst-case cost at least `r_μ/32` (Lemma
`hsl:lem:precision` with `n = ⌊r_μ/4⌋` at time `θ = √m`). -/
theorem denom_lower_tree {k : ℕ} (hk : 47 ≤ k) {K F E G L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (O : L → (Fin (precN (denomTheta k) (denomEps k)) → Bool) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (denomData k) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k)) G)
    (he : e† ∘L e = 1) (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x) (evolve ((denomData k).matrix x) 1
      (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) :
    hsR (denomTheta k) (denomEps k) / 32 ≤ T.worstCost w :=
  precision_scalar_tree (denom_range (by omega)) (denom_L_ge hk)
    (fun l x => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) x) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible even_two _ _ (hardAccess_denomData k)
      O w hO) T _ (regroup_comp_isometry _ e he) hsucc
    (fun x => densityAccurate_scalar_of_two le_rfl (denomM_pos k) (denomMu_pos k).ne'
      (denom_params k).1 e _ x (hacc x))

/-- **The logarithmic denominator must change, adaptive protocols**: for every constant `C` and
every `k ≥ max(47, ⌈(384 C)² + 3⌉)`, every adaptive protocol over admissible labels of
`denomData k` that heralds success with probability at least `2/3` and is conditionally
`ε`-accurate (`ε = e^{-L}`) for `e^{-iH_x}(ψ_in ⊗ u_m)` at `t = 1` has worst-case cost more than
`C (√s η|t| + √(sμ|t| r̃) + r̃)`, at `s = 2m`, `η = 1`, `μ = m^{-1/2}`. -/
theorem wrong_denominator_tree (C : ℝ) {k : ℕ} (hk : max 47 ⌈(384 * C) ^ 2 + 3⌉₊ ≤ k)
    {K F E G L : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (O : L → (Fin (precN (denomTheta k) (denomEps k)) → Bool) → K →L[ℂ] K) (w : L → ℕ)
    (hO : ∀ l, Admissible (denomData k) (O l) (w l)) (T : Tree O F E)
    (e : E →L[ℂ] SysGarb (ScalarIndex (precN (denomTheta k) (denomEps k)) 2 × Fin (denomM k)) G)
    (he : e† ∘L e = 1) (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x) (evolve ((denomData k).matrix x) 1
      (embedU (denomM k) (scalarInput (precN (denomTheta k) (denomEps k)) 2))) (denomEps k)) :
    C * wrongShape (2 * denomM k) 1 (denomMu k) 1 (denomEps k) < T.worstCost w := by
  have hk47 : 47 ≤ k := le_of_max_le_left hk
  have hkC : (384 * C) ^ 2 + 3 ≤ k :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hk)
  exact wrong_lt_of_lower C hk47 hkC (denom_lower_tree hk47 O w hO T e he hsucc hacc)

end

end OptimalLowerBounds
