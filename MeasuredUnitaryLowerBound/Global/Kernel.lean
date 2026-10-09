import MeasuredUnitaryLowerBound.Global.Sum
import AdaptiveODELowerBound.Adversary.Decision

set_option autoImplicit false

/-!
# The summed adversary progress and the endpoint kernel bound

For the lower half of Corollary `hs:cor:unitary` of the manuscript (lines 1647-1666 and
1711-1718), adaptive protocols `SparseLinearSystems.Protocol.Tree` over labels implemented by
Boolean phase queries of the marked strings of a position map `c : I → Fin N`. The positive-weight
adversary of the package (`AdaptiveODELowerBound.Adversary.abs_treeKernel_progress_le`, with the
all-pairs search matrix and its Schur certificate
`UnitaryImplementationExtensions.Search.schurCert`, `λ = √(N - 1)`) bounds the summed kernel deficit
of the purified protocol (`AdaptiveODELowerBound.Adversary.treeKernel`):

* `adversary_deficit_le`: `∑_{x ≠ x'} (1 - Re κ_T(x, x')) ≤ 2 √(N - 1) N worstCost_w(T)`.
* `tree_count_ge_of_kernel_gaps`: with gaps `g` as in `Global.sum_le_of_gaps` for the kernel,
  `b² ≤ 4 (N - 1) √(N - 1) worstCost_w(T)`.

No uniform pair gap is assumed: this is the form that reaches the endpoint `ε = 1/2`.
-/

namespace MeasuredUnitaryLowerBound.Global

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLinearSystems.Protocol
open AdaptiveODELowerBound.Adversary (treeKernel)
open UnitaryImplementationExtensions
open scoped InnerProduct InnerProductSpace

variable {E W Fl L B I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- **The summed adversary progress for search.** If every label of a unitary family over the
instances `Fin N`, `N ≥ 2`, is implemented on the isometric encoding `Enc` by at most `w l`
queries of the phase oracle of the marked strings of `c`, the Gram kernel of every adaptive
protocol over the family satisfies
`∑_{x ≠ x'} (1 - Re κ_T(x, x')) ≤ 2 √(N - 1) N worstCost_w(T)`. -/
theorem adversary_deficit_le [Fintype I] {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I)
    (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (T : Tree O Fl E) :
    ∑ x, ∑ x', Search.adversary N x x' * (1 - (treeKernel T x x').re) ≤
      2 * Real.sqrt ((N : ℝ) - 1) * T.worstCost w * N := by
  classical
  have hΓ0 : ∀ m m' : Fin N, 0 ≤ Search.adversary N m m' := fun m m' => by
    unfold Search.adversary; split_ifs <;> norm_num
  have hΓs : ∀ m m' : Fin N, Search.adversary N m m' = Search.adversary N m' m :=
    fun m m' => by
      unfold Search.adversary
      by_cases h : m = m'
      · simp [h]
      · simp [h, Ne.symm h]
  have hprog := AdaptiveODELowerBound.Adversary.abs_treeKernel_progress_le P
    (Search.markedString c) (Search.adversary N) hΓ0 hΓs (Real.sqrt_nonneg _)
    (fun i => Search.schurCert hN c i) Enc hEnc hO w hw T
  rw [Fintype.card_fin] at hprog
  have heq : ∑ x, ∑ x', Search.adversary N x x' * (1 - (treeKernel T x x').re) =
      -∑ x, ∑ x', Search.adversary N x x' * ((treeKernel T x x').re - 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x' _ => ?_
    ring
  rw [heq]
  exact (neg_le_abs _).trans hprog

/-- **The endpoint search bound at the kernel level.** Under the access hypotheses of
`adversary_deficit_le`, if `Re κ_T(x, x') ≤ 1` and `Re κ_T(x, x') ≤ 1 - g(x, x')²/8` whenever
`g(x, x') ≥ 0`, for all `x ≠ x'`, and the gaps sum to at least `2 N b` over the ordered pairs,
`b ≥ 0`, then `b² ≤ 4 (N - 1) √(N - 1) worstCost_w(T)`. The condition `Re κ_T(x, x') ≤ 1` holds
for unitary runs on finite-dimensional spaces
(`AdaptiveUnitaryLowerBound.Kernel.treeKernel_re_le_of_gap` with the zero observable);
`tree_count_ge_of_reads` derives it there. -/
theorem tree_count_ge_of_kernel_gaps [Fintype I] {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I)
    (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (T : Tree O Fl E) (g : Fin N → Fin N → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hk : ∀ x x', x ≠ x' → (treeKernel T x x').re ≤ 1)
    (hkg : ∀ x x', x ≠ x' → 0 ≤ g x x' → (treeKernel T x x').re ≤ 1 - g x x' ^ 2 / 8)
    (hsum : 2 * (N : ℝ) * b ≤ ∑ x, ∑ x', Search.adversary N x x' * g x x') :
    b ^ 2 ≤ 4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost w := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hS := sum_le_of_gaps hN (fun x x' => (treeKernel T x x').re) g hb hk hkg hsum
  have hD := adversary_deficit_le hN P c Enc hEnc hO w hw T
  have hmul := mul_le_mul_of_nonneg_left hD (by linarith : (0 : ℝ) ≤ 2 * ((N : ℝ) - 1))
  have h4 : (N : ℝ) * b ^ 2 ≤
      (N : ℝ) * (4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost w) := by
    have := hS.trans hmul
    linarith
  exact le_of_mul_le_mul_left h4 (by positivity)

end
end MeasuredUnitaryLowerBound.Global
