import AdaptiveUnitaryLowerBound.Correlation
import AdaptiveUnitaryLowerBound.Kernel

set_option autoImplicit false

/-!
# Search with accurate heralded outputs for adaptive protocols

The generic form of the lower half of corollary `hs:cor:unitary` of the
manuscript (lines 1664-1665 and 1711-1718): an adaptive protocol
`SparseLinearSystems.Protocol.Tree` over a unitary family whose labels are
implemented by Boolean phase queries of the marked strings of a position map
`c : I → Fin N`, which on every instance `m` heralds success with probability
at least `s₀ > 0` and whose conditional output is `ε₀`-accurate for `|m⟩`
(`AdaptiveHamiltonianLowerBound.DensityAccurate`, `ε₀ ≤ 1/2`), has worst-case
weighted cost

  `(s₀ (1 - 2ε₀))² sqrt (N - 1) ≤ 4 worstCost_w(T)`

(`tree_search_count_ge_of_accurate`). The proof combines the pair gaps
`Correlation.pair_gap` (gap `2 s₀ (1 - 2ε₀)` for the pair observable) with the
adaptive search bound `Kernel.tree_search_count_ge_of_gap`.

Here `ε₀` is trace-distance accuracy. The bound is positive for `ε₀ < 1/2`;
at `ε₀ = 1/2` the pair gap `2 s₀ (1 - 2ε₀)` vanishes and the bound is empty.
-/

namespace AdaptiveUnitaryLowerBound.Accuracy

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open UnitaryImplementationExtensions
open Observable
open scoped InnerProduct InnerProductSpace

variable {E W Fl L B I G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Unstructured search for adaptive protocols with accurate heralded
outputs.** If every label of a unitary family over the instances `Fin N`,
`N ≥ 2`, on a finite-dimensional workspace is implemented on the isometric
encoding `Enc` by at most `w l` queries of the phase oracle of the marked
strings of `c`, and on every instance `m` the protocol succeeds with probability
at least `s₀ > 0` and its conditional output, read through the isometry `e`, is
`ε₀`-accurate for `|m⟩` with `ε₀ ≤ 1/2`, then
`(s₀ (1 - 2ε₀))² sqrt (N - 1) ≤ 4 worstCost_w(T)`. -/
theorem tree_search_count_ge_of_accurate [Fintype I] [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ E] {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I)
    (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m) (ket m) ε₀) :
    (s₀ * (1 - 2 * ε₀)) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * T.worstCost w :=
  Kernel.tree_search_count_ge_of_gap hN P c Enc hEnc hO w hw T
    (β := s₀ * (1 - 2 * ε₀)) (mul_nonneg hs₀.le (by linarith))
    (fun m m' h => ⟨outObs e (pairObs m m'), Correlation.norm_outObs_pairObs_le e he m m',
      Correlation.pair_gap e T hs₀ hε₀ h (hsucc m) (hsucc m') (hacc m) (hacc m')⟩)

end
end AdaptiveUnitaryLowerBound.Accuracy
