import TimeDependentLowerBoundExtensions.BlockEncoding.Bound

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The block-encoding lower bound is not vacuous

The constant Hermitian block encodings of the hard instances satisfy every instance hypothesis
of `TimeDependentExtensions.BlockEncoding.simulation` (`beConst_hyps`: Hermitian, unitary
samples and an isometric boundary), so on every admissible mesh the released block-encoding
simulator supplies a program over the family of `main_max_block` that meets its criterion
`BECriterion` with its clean isometric encoding (`exists_beProgram`), with at most
`2304 (α_BE τ + 1 + log(3/ε))` calls (eq. `hs:eq:blockadditive`).
-/

namespace TimeDependentLowerBoundExtensions.BlockEncoding

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds
open scoped InnerProduct InnerProductSpace

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The constant block encodings are instances of the block-encoding class**: Hermitian,
unitary samples and an isometric public boundary. -/
theorem beConst_hyps (D : Data X N Z s) (M : ℕ) :
    (∀ x r, star (beConst D M x r) = beConst D M x r) ∧ (∀ x r, IsUnitary (beConst D M x r)) ∧
      (beJ D)† ∘L beJ D = 1 ∧ 0 < beAlpha D := by
  exact ⟨fun x _ => beOp_selfAdjoint D x, fun x _ => beOp_unitary D x, beJ_isometry D,
    beAlpha_pos D⟩

/-- **The released block-encoding simulator meets the criterion of `main_max_block`** on the
constant data: under the mesh and slot conditions of
`TimeDependentExtensions.BlockEncoding.simulation`
at normalisation `α_BE = beAlpha D`, there is a program over the aligned block-encoding family
with at most `2304 (α_BE T + 1 + log(3/ε))` calls whose clean isometric input encoding satisfies
`BECriterion`. -/
theorem exists_beProgram (D : Data X N Z s) {M : ℕ} (hM : 0 < M) (b₀ : BEBasis N Z)
    (t : ℕ → ℝ) (T ε : ℝ) (Nsl : ℕ) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1) (hN : 0 < Nsl)
    (hmesh : TimeDependentExtensions.IsMesh t M T)
    (hClock : 4 * (beAlpha D * T) ≤ Nsl)
    (hCayley : 9 * (beAlpha D * T) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (beAlpha D * T) ≤ ε * Nsl) :
    ∃ p : MultiOracleCircuit.Program
        (TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) Nsl (beAlpha D) T ε),
      (p.count : ℝ) ≤ 2304 * (beAlpha D * T + 1 + Real.log (3 / ε)) ∧
      (TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ (beJ D) (beJ_isometry D) t Nsl
          (beAlpha D) T ε)† ∘L
        TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ (beJ D) (beJ_isometry D) t Nsl
          (beAlpha D) T ε = 1 ∧
      BECriterion p.eval
        (TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ (beJ D) (beJ_isometry D) t Nsl
          (beAlpha D) T ε)
        (beConst D M) (beJ D) (beAlpha D) t T ε := by
  obtain ⟨p, hc, hin, hall⟩ := TimeDependentExtensions.BlockEncoding.simulation (beConst D M)
    (fun x _ => beOp_selfAdjoint D x) (fun x _ => beOp_unitary D x) hM b₀ (beJ D)
    (beJ_isometry D) t (beAlpha D) T ε Nsl (beAlpha_pos D) hT hε hεOne hN hmesh hClock hCayley
    hRefine
  exact ⟨p, hc, hin, fun x => (hall x).2⟩

end

end TimeDependentLowerBoundExtensions.BlockEncoding
