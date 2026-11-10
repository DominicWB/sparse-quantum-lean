import LowerBoundRemarks.HamiltonianPadding
import SparseLowerBounds.ODE.Theorem

/-!
# Heralded readout of a zero-padded output

Section `part:odel` of the manuscript: the padding remarks
"Known zero padding permits any sufficiently large qubit register" (end of the proof of
Theorem `odel:thm:joint`) and "Pad dimensions to a common known size if desired"
(proof of Theorem `odel:thm:combined`). The ODE output model is the heralded
readout model (`SparseLowerBounds.ODE.Solver`, `Readout.HeraldedAccurate`, Section `odel:sec:main`).

This module extends the readout transfer of `LowerBoundRemarks.HamiltonianPadding`
(`padReadout`, `accurate_padReadout`) from `Readout.Accurate` to `Readout.HeraldedAccurate`:
an output that is heralded-accurate for a padded target `ψ ⊕ 0` through a readout `e` on
`ℂ^{N ⊕ P}` is heralded-accurate for `ψ` through `padReadout P G i₀ ∘ e` on `ℂ^N`, with the same
herald and the same `ε` (`heraldedAccurate_padReadout`). The herald and the success probability
are untouched; only the system observable changes, to the Hermitian contraction
`M ⊕ M_{i₀ i₀} 1_P` of `outObs_padReadout`. It also records that normalisation commutes with the
extension by zero (`unitDirection_inlOp`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
  LowerBoundRemarks.HamiltonianPadding
open scoped InnerProduct InnerProductSpace

variable {N : Type*} [Fintype N] [DecidableEq N] {P : Type*} [Fintype P] [DecidableEq P]

/-- The extension by zero `ψ ↦ ψ ⊕ 0` preserves norms (the case `x = y` of
`LowerBoundRemarks.HamiltonianPadding.inner_inlOp`). -/
theorem norm_inlOp (ψ : EuclideanSpace ℂ N) : ‖HsInstance.inlOp N P ψ‖ = ‖ψ‖ := by
  have h := inner_inlOp P ψ ψ
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖HsInstance.inlOp N P ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

/-- **Normalisation commutes with the extension by zero**:
`(ψ ⊕ 0)/‖ψ ⊕ 0‖ = (ψ/‖ψ‖) ⊕ 0`. The `HsInstance.inlOp` twin of
`LowerBoundRemarks.LinearSystemPadding.unitDirection_emb`. -/
theorem unitDirection_inlOp (ψ : EuclideanSpace ℂ N) :
    ODEStateNormalization.unitDirection (HsInstance.inlOp N P ψ) =
      HsInstance.inlOp N P (ODEStateNormalization.unitDirection ψ) := by
  unfold ODEStateNormalization.unitDirection
  rw [norm_inlOp, ContinuousLinearMap.map_smul_of_tower]

/-- **Heralded readout transfer without loss** (the heralded analogue of
`accurate_padReadout`). If the output `Φ`, read through `e` on the padded system `N ⊕ P` and
conditioned on the herald `Π`, is `ε`-accurate for the padded target `ψ ⊕ 0`, then the same
output, read through `padReadout P G i₀ ∘ e` on the original system `N` and conditioned on the
same herald, is `ε`-accurate for `ψ`. -/
theorem heraldedAccurate_padReadout {G K : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (i₀ : N) (e : K →L[ℂ] SysGarb (N ⊕ P) G) (herald : K →L[ℂ] K) (Φ : K)
    (ψ : EuclideanSpace ℂ N) (ε : ℝ)
    (h : HeraldedAccurate e herald Φ (HsInstance.inlOp N P ψ) ε) :
    HeraldedAccurate (padReadout P G i₀ ∘L e) herald Φ ψ ε := by
  intro M hM hM1
  have hA : (obsMat M).IsHermitian := hM.map _
  have hc : star (obsMat M i₀ i₀) = obsMat M i₀ i₀ := hA.apply i₀ i₀
  have hn : ‖blockObs P M (obsMat M i₀ i₀)‖ ≤ 1 :=
    (norm_blockObs_le M _).trans (max_le hM1 ((norm_obsMat_apply_le M i₀ i₀).trans hM1))
  have h' := h _ (isSelfAdjoint_blockObs hM hc) hn
  rw [blockObs_inlOp, inner_inlOp] at h'
  rw [outObs_padReadout]
  exact h'

end

end ODELowerBoundExtensions.Padding
