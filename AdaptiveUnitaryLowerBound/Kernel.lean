import AdaptiveODELowerBound.Adversary.Decision
import UnitaryImplementationExtensions.Search

set_option autoImplicit false

/-!
# Unstructured search for adaptive protocols

The lower half of corollary `hs:cor:unitary` of the manuscript rests on the `Ω(√N)` bound for
unstructured search. The corollary does not mention adaptive algorithms; their treatment follows the
convention of the lower-bound sections of the manuscript ("Purification and deferred measurement
include adaptive and randomised algorithms", proof of Lemma `hsl:lem:precision`). This module proves
the search bound for the adaptive protocols `SparseLinearSystems.Protocol.Tree`, with the worst-case
weighted cost `Tree.worstCost w` in place of the query count of the non-adaptive
`UnitaryImplementationExtensions.Search.count_ge`, and the same constant.

The oracle labels are implemented on an isometric encoding by Boolean phase
queries of the marked strings `Search.markedString c m` (one marked element of
`Fin N`). The adversary matrix is the all-pairs search matrix
`Search.adversary N` with the Schur certificate `Search.schurCert`
(`λ = sqrt (N - 1)`) and row sums `N - 1`; the progress of the Gram kernel of
the purified protocol (`AdaptiveODELowerBound.Adversary.treeKernel`) is
`AdaptiveODELowerBound.Adversary.abs_treeKernel_progress_le`.

* `tree_search_count_ge`: if `Re κ_T(m, m') ≤ 1 - κ` for all `m ≠ m'`, then
  `κ sqrt (N - 1) ≤ 2 worstCost_w(T)`.
* `treeKernel_re_le_of_gap`: since the kernel does not depend on the readout,
  a contraction `A` whose heralded correlations on `m` and `m'` differ by at
  least `2β ≥ 0` gives `Re κ_T(m, m') ≤ 1 - β²/2` (lossless purification
  `exists_tree_purification` and `PositiveAdversary.norm_inner_le_of_gap`); the
  contraction may depend on the pair.
* `tree_search_count_ge_of_gap`: pairwise gaps `2β` give
  `β² sqrt (N - 1) ≤ 4 worstCost_w(T)`.
-/

namespace AdaptiveUnitaryLowerBound.Kernel

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLinearSystems.Protocol
open AdaptiveODELowerBound.Adversary (treeKernel)
open LinearSystemLowerBound (corr)
open UnitaryImplementationExtensions
open scoped InnerProduct InnerProductSpace

variable {E W Fl X L B I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- **Pairwise separation from a correlation gap.** For an adaptive protocol of
unitary runs on finite-dimensional spaces, if a contraction `A` on the output
space has heralded correlations on `x` and `x'` that differ by at least
`2β ≥ 0`, then `Re κ_T(x, x') ≤ 1 - β²/2`. This is the separation step of
`AdaptiveODELowerBound.Adversary.tree_decision_count_ge`, for a contraction that
may depend on the pair. -/
theorem treeKernel_re_le_of_gap [FiniteDimensional ℂ W] [FiniteDimensional ℂ E]
    {O : L → X → W →L[ℂ] W} (hO : ∀ l x, OracleCircuit.IsUnitary (O l x))
    (T : Tree O Fl E) (A : E →L[ℂ] E) (hA : ‖A‖ ≤ 1) {β : ℝ} (hβ : 0 ≤ β) {x x' : X}
    (hgap : 2 * β ≤ corr A (T.successDensity x) - corr A (T.successDensity x')) :
    (treeKernel T x x').re ≤ 1 - β ^ 2 / 2 := by
  obtain ⟨H, _, _, Ψ, R, hΨ, hR, hG, hC⟩ :=
    AdaptiveODELowerBound.Adversary.exists_tree_purification hO T A hA
  rw [← hC x, ← hC x'] at hgap
  have hgap' : 2 * β ≤ |(⟪Ψ x, R (Ψ x)⟫_ℂ).re - (⟪Ψ x', R (Ψ x')⟫_ℂ).re| :=
    hgap.trans (le_abs_self _)
  have h := PositiveAdversary.norm_inner_le_of_gap hR ((hΨ x).trans (hΨ x').symm)
    (hΨ x).le (mul_nonneg two_pos.le hβ) hgap'
  rw [hΨ x, hG x x'] at h
  have hre := Complex.re_le_norm (treeKernel T x x')
  nlinarith

/-- **Unstructured search for adaptive protocols, overlap form.** If every label
of a unitary family over the instances `Fin N` is implemented on the isometric
encoding `Enc` by at most `w l` queries of the phase oracle of the marked
strings of `c`, and the Gram kernel of the protocol satisfies
`Re κ_T(m, m') ≤ 1 - κ` for all `m ≠ m'`, then
`κ sqrt (N - 1) ≤ 2 worstCost_w(T)`. -/
theorem tree_search_count_ge [Fintype I] {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I)
    (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (T : Tree O Fl E) {κ : ℝ}
    (hsep : ∀ m m', m ≠ m' → (treeKernel T m m').re ≤ 1 - κ) :
    κ * Real.sqrt ((N : ℝ) - 1) ≤ 2 * T.worstCost w := by
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hs : 0 < Real.sqrt ((N : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hΓ0 : ∀ m m' : Fin N, 0 ≤ Search.adversary N m m' := fun m m' => by
    unfold Search.adversary; split_ifs <;> norm_num
  have hΓs : ∀ m m' : Fin N, Search.adversary N m m' = Search.adversary N m' m :=
    fun m m' => by
      unfold Search.adversary
      by_cases h : m = m'
      · simp [h]
      · simp [h, Ne.symm h]
  have hrow : ∀ m : Fin N, ∑ m', Search.adversary N m m' = (N : ℝ) - 1 := by
    intro m
    have hterm : ∀ m', Search.adversary N m m' = if m' = m then 0 else 1 := by
      intro m'
      by_cases h : m' = m
      · simp [Search.adversary, h]
      · simp [Search.adversary, h, Ne.symm h]
    rw [Finset.sum_congr rfl fun m' _ => hterm m', Finset.sum_ite, Finset.sum_const_zero,
      zero_add, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_ne' Finset.univ m,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega), Nat.cast_one]
  have hprog := AdaptiveODELowerBound.Adversary.abs_treeKernel_progress_le P
    (Search.markedString c) (Search.adversary N) hΓ0 hΓs (Real.sqrt_nonneg _)
    (fun i => Search.schurCert hN c i) Enc hEnc hO w hw T
  have hfin : ∑ m, ∑ m', Search.adversary N m m' * ((treeKernel T m m').re - 1) ≤
      ∑ m, ∑ m', Search.adversary N m m' * (-κ) := by
    refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun m' _ => ?_
    by_cases h : m = m'
    · simp [Search.adversary, h]
    · have e : Search.adversary N m m' = 1 := by simp [Search.adversary, h]
      rw [e, one_mul, one_mul]
      linarith [hsep m m' h]
  have hsum : ∑ m, ∑ m', Search.adversary N m m' * (-κ) =
      -κ * ((N : ℝ) * ((N : ℝ) - 1)) := by
    have hm : ∀ m : Fin N, ∑ m', Search.adversary N m m' * (-κ) = -κ * ((N : ℝ) - 1) := by
      intro m
      rw [← Finset.sum_mul, hrow m, mul_comm]
    rw [Finset.sum_congr rfl fun m _ => hm m, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have h3 := (abs_le.mp hprog).1
  rw [Fintype.card_fin] at h3
  have hNpos : (0 : ℝ) < N := by linarith
  have hsq : (N : ℝ) - 1 = Real.sqrt ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) :=
    (Real.mul_self_sqrt (by linarith)).symm
  have hmain : κ * ((N : ℝ) * ((N : ℝ) - 1)) ≤
      2 * Real.sqrt ((N : ℝ) - 1) * T.worstCost w * N := by
    linarith
  have key : ((N : ℝ) * Real.sqrt ((N : ℝ) - 1)) * (κ * Real.sqrt ((N : ℝ) - 1)) ≤
      ((N : ℝ) * Real.sqrt ((N : ℝ) - 1)) * (2 * T.worstCost w) := by
    calc ((N : ℝ) * Real.sqrt ((N : ℝ) - 1)) * (κ * Real.sqrt ((N : ℝ) - 1)) =
          κ * ((N : ℝ) * (Real.sqrt ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1))) := by ring
      _ = κ * ((N : ℝ) * ((N : ℝ) - 1)) := by rw [← hsq]
      _ ≤ 2 * Real.sqrt ((N : ℝ) - 1) * T.worstCost w * N := hmain
      _ = ((N : ℝ) * Real.sqrt ((N : ℝ) - 1)) * (2 * T.worstCost w) := by ring
  exact le_of_mul_le_mul_left key (mul_pos hNpos hs)

/-- **Unstructured search for adaptive protocols, gap form.** Under the access
hypotheses of `tree_search_count_ge`, on finite-dimensional spaces, if for every
pair `m ≠ m'` some contraction on the output space has heralded correlations on
`m` and `m'` that differ by at least `2β ≥ 0`, then
`β² sqrt (N - 1) ≤ 4 worstCost_w(T)`. -/
theorem tree_search_count_ge_of_gap [Fintype I] [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ E] {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I)
    (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (T : Tree O Fl E) {β : ℝ} (hβ : 0 ≤ β)
    (hgap : ∀ m m', m ≠ m' → ∃ A : E →L[ℂ] E, ‖A‖ ≤ 1 ∧
      2 * β ≤ corr A (T.successDensity m) - corr A (T.successDensity m')) :
    β ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * T.worstCost w := by
  have h := tree_search_count_ge (κ := β ^ 2 / 2) hN P c Enc hEnc hO w hw T
    (fun m m' hne => by
      obtain ⟨A, hA, hg⟩ := hgap m m' hne
      exact treeKernel_re_le_of_gap hO T A hA hβ hg)
  linarith

end
end AdaptiveUnitaryLowerBound.Kernel
