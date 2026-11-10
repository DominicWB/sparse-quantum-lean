import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import LinearSystemLowerBound.Theorem
import LinearSystemLowerBound.Bridge

/-!
# Conformance: the linear-system lower bound

Theorem `qlsl:thm:main` in the manuscript's model:

* **Access.** Native sparse data with the hard matrices (`NativeSparseBlockEncoding.Data`: value
  oracle and in-place row and column locators); the locators are input independent and the value
  table is a fixed encoding of the entries. The bound holds for every such access.
* **Algorithms.** Adaptive protocols (`SparseLinearSystems.Protocol.Tree`: fresh measured runs
  with classical branching, then bounded fresh-trial preparations) over admissible oracle labels
  (`LinearSystemLowerBound.Native.Admissible`): a label is either a native call — in a fixed
  isometric layout of the workspace as spectator branches of the native space, every branch
  applies the identity, one native query or its inverse, which includes spectators, controlled
  and masked versions and inverses — of weight at least one, or an input-independent unitary (for
  instance the right-hand-side preparation) of any weight.
* **Guarantee.** On every promised input: success probability at least `2/3`, and conditional on
  success the output, reduced to the output register by the partial trace over a garbage
  register identified by a fixed isometry, within trace distance `ε` of `|x_A⟩⟨x_A|`,
  `x_A = A⁻¹b/‖A⁻¹b‖` (eq. `qlsl:eq:target`).
* **Cost.** `T.worstCost w`, the maximum over all transcripts of the weighted number of calls.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems.Protocol
open scoped InnerProduct InnerProductSpace

universe uZ uK uF uL uE uG

set_option maxHeartbeats 4000000 in
/-- **Theorem `qlsl:thm:main`** (eqs. `qlsl:eq:target`, `qlsl:eq:main`).
Let `κ ≥ 32`, let `s ≥ 5` be an integer, and let `0 < ε ≤ 1/64`. There is a family of real
symmetric, indefinite matrices `A_X` (hidden input `X`: `n` marked positions in `Fin m`) with
`‖A_X‖ ≤ 1`, `A_X` invertible, `‖A_X⁻¹‖ ≤ κ`, at most `s` nonzeros in every row and column,
dimension `N = Θ(sκ ln(1/ε))` (`sκ ln(1/ε)/32 < N ≤ (s - 1)κ ln(1/ε)`), and an input-independent
unit right-hand side `b`, with native sparse access (input-independent locators) — and for every
such access, every algorithm of the model that succeeds with probability at least `2/3` on every
input and whose conditional output is within trace distance `ε` of `|x_A⟩⟨x_A|` makes in the
worst case more than `κ √s ln(1/ε)/3072` matrix-oracle queries (`Q = Ω(√s κ ln(1/ε))`), even with
location oracles, their inverses and controlled versions supplied (they are input independent;
only value queries convey the hidden input). Formal restrictions: the algorithms are adaptive
protocols of fresh measured runs with classical branching; measurements inside a run with the
post-measurement state kept are not in the class. For the same hard family,
`DeferredMeasurementLowerBounds.Corollaries.lower_bound_measured` covers measured algorithms with
such measurements, with the same constant `1/3072`. -/
theorem qlsl_thm_main {κ ε : ℝ} {s : ℕ} (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    ∃ (n m : ℕ) (N : Type) (_ : Fintype N) (_ : DecidableEq N)
      (A : (Fin n → Fin m) → Matrix N N ℂ) (b : EuclideanSpace ℂ N),
      (∀ x, ‖SparseStateOverlap.matrixOperator (A x)‖ ≤ 1 ∧
        IsUnit (SparseStateOverlap.matrixOperator (A x)) ∧
        ‖Ring.inverse (SparseStateOverlap.matrixOperator (A x))‖ ≤ κ) ∧
      (∀ x i j, A x i j = A x j i ∧ (A x i j).im = 0) ∧
      (∀ x, ∃ v w : EuclideanSpace ℂ N,
        0 < (⟪v, SparseStateOverlap.matrixOperator (A x) v⟫_ℂ).re ∧
        (⟪w, SparseStateOverlap.matrixOperator (A x) w⟫_ℂ).re < 0) ∧
      (∀ x i, (Finset.univ.filter fun j => A x i j ≠ 0).card ≤ s ∧
        (Finset.univ.filter fun j => A x j i ≠ 0).card ≤ s) ∧
      ((s : ℝ) * κ * Real.log (1 / ε) / 32 < Fintype.card N ∧
        (Fintype.card N : ℝ) ≤ ((s : ℝ) - 1) * κ * Real.log (1 / ε)) ∧
      ‖b‖ = 1 ∧
      (∃ D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N (ZMod 8) s,
        D.matrix = A ∧ (∀ x x', D.rowOracle x = D.rowOracle x') ∧
        (∀ x x', D.columnOracle x = D.columnOracle x') ∧
        ∃ enc : ℂ → ZMod 8, ∀ x α, D.table x α = enc (D.matrix x α.1 α.2)) ∧
      ∀ {Z : Type uZ} [Fintype Z] [AddCommGroup Z]
        (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s), D.matrix = A →
        (∀ x x', D.rowOracle x = D.rowOracle x') → (∀ x x', D.columnOracle x = D.columnOracle x') →
        (∃ enc : (N × N) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2)) →
        ∀ {K : Type uK} {F : Type uF} {L : Type uL}
          [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
          [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
          (O : L → (Fin n → Fin m) → K →L[ℂ] K) (w : L → ℕ),
          (∀ l, LinearSystemLowerBound.Native.Admissible D (O l) (w l)) →
          ∀ {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
            [FiniteDimensional ℂ E] {G : Type uG} [Fintype G] [DecidableEq G]
            (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (N × G)) (T : Tree O F E),
            (∀ x, 2 / 3 ≤ T.successMass x ∧
              TraceDistanceLE (LinearSystemLowerBound.ptrace
                  (V.conjStarAlgEquiv (T.conditionalDensity x)))
                ((‖Ring.inverse (SparseStateOverlap.matrixOperator (A x)) b‖⁻¹ : ℝ) •
                  Ring.inverse (SparseStateOverlap.matrixOperator (A x)) b) ε) →
            κ * Real.sqrt s * Real.log (1 / ε) / 3072 < T.worstCost w := by
  obtain ⟨hcard, hlo, hhi⟩ := LinearSystemLowerBound.family_dimension_sharp κ ε s hκ hs hε hε1
  refine ⟨_, _, LinearSystemLowerBound.Ind κ ε s, inferInstance, inferInstance,
    LinearSystemLowerBound.family κ ε s, LinearSystemLowerBound.rhsVec κ ε s,
    fun x => LinearSystemLowerBound.family_promise κ ε s hκ x,
    LinearSystemLowerBound.family_real_symm κ ε s,
    LinearSystemLowerBound.family_indefinite κ ε s, fun x i => ?_, ⟨hlo, hhi⟩,
    LinearSystemLowerBound.rhsVec_norm κ ε s hs,
    LinearSystemLowerBound.exists_access κ ε s hκ hs hε hε1, ?_⟩
  · obtain ⟨hsupp, hmem⟩ := LinearSystemLowerBound.family_sparse κ ε s hs i
    refine ⟨(Finset.card_le_card fun j hj => (hmem x j).1 (Finset.mem_filter.mp hj).2).trans hsupp,
      (Finset.card_le_card fun j hj => (hmem x j).2 (Finset.mem_filter.mp hj).2).trans hsupp⟩
  · intro Z _ _ D hDm hrow hcol henc K F L _ _ _ _ _ _ O w hO E _ _ _ _ G _ _ V T hT
    exact LinearSystemLowerBound.lower_bound κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO V T hT

end

end ManuscriptConformance
