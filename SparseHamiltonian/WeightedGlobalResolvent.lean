import SparseHamiltonian.GlobalResidual

/-!
# Global resolvents for unequal weighted clock branches

This specialization constructs the chronological inverse from individual
branch-clock promises. The coherent boundary preparation, global clock,
weighted endpoint budget and averaged public generator are explicit
constructions; none is postulated as a global boundary identity.
-/

namespace SparseHamiltonian.WeightedGlobalResolvent

noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProduct
open SparseHamiltonian.WeightedClock SparseHamiltonian.ChronologicalResolvent

variable {ι : Type*} [Fintype ι]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)]

/-- A probability-weighted family of branch clocks yields the global
chronological resolvent with `qbar = ∑ i, p i * q i`.
The bound retains the average branch cost in both the prefactor and exponent. -/
theorem exists_weighted_global_resolvent
    (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (Q : ℝ) (hQ : 0 < Q) (hqQ : ∀ i, q i ≤ Q)
    (D R : ∀ i, V i →L[ℂ] V i) (J : ∀ i, P →L[ℂ] V i)
    (H : ι → P →L[ℂ] P)
    (hD : ∀ i, (D i)† ∘L D i = 1) (hJ : ∀ i, (J i)† ∘L J i = 1)
    (hRleft : ∀ i, R i ∘L (1 - D i) = 1)
    (hRright : ∀ i, (1 - D i) ∘L R i = 1)
    (hRnorm : ∀ i, ‖R i‖ ≤ q i)
    (hcompression : ∀ i, (J i)† ∘L R i ∘L J i =
      (2 : ℂ)⁻¹ • (1 + Complex.I • H i))
    (hHerm : ∀ i, (H i)† = H i) (hHnorm : ∀ i, ‖H i‖ ≤ 1)
    (henergy : ∀ i x, ‖R i (J i x)‖ ^ 2 ≤ q i / 2 * ‖x‖ ^ 2)
    (c κ σ w : ℝ) (T : ℕ) (z : ℂ)
    (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ S : BlockOperator.H T (PiLp 2 V) →L[ℂ] BlockOperator.H T (PiLp 2 V),
      (z • 1 - GlobalResolvent.globalPrivateBlock (diagonal D) (boundary p J) c κ σ T) ∘L S = 1 ∧
      S ∘L (z • 1 - GlobalResolvent.globalPrivateBlock (diagonal D) (boundary p J) c κ σ T) = 1 ∧
      ‖S‖ ≤ 3 * (Q + (T : ℝ) * w * (∑ i, p i * q i)) *
        Real.exp (3 * ((T : ℝ) * w * (∑ i, p i * q i)) / (4 * Q)) := by
  obtain ⟨hDg, hJg, hRleftg, hRrightg, hRnormg, hcompressiong,
    hHermg, hHnormg, henergyg, hsqg, hqQg⟩ :=
    weighted_clock_promises p q hp hsum hq Q hQ.le hqQ D R J H hD hJ hRleft
      hRright hRnorm hcompression hHerm hHnorm henergy
  exact GlobalResolvent.exists_global_resolvent
    (diagonal D) (diagonal R) (boundary p J) (generator p H)
    c κ σ w Q (Real.sqrt ((∑ i, p i * q i) / 2)) (∑ i, p i * q i) T z
    hQ hw hκ hκUpper hκc hσc hσw hDg hJg hRrightg hRleftg hRnormg
    hcompressiong hHermg hHnormg henergyg hsqg.le hqQg hz

end
end SparseHamiltonian.WeightedGlobalResolvent
