import SparseODE.ODETaggedSupport

/-!
# Applying the tagged support construction to the actual LCHS branches

The support and energy hypotheses of the generic tagged construction are
discharged using the original matrix and its two Hermitian parts. No locator
for their support union and no separate value oracle for either part is used.
The native implementation of the tagged diagonal remains a later task.
-/

namespace SparseHamiltonian.ODETaggedLCHS

noncomputable section
open ContinuousLinearMap ODETaggedSupport ODEMatrixEnergy
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Exact LCHS operator overlap using the original sparse-data lists. -/
theorem native_overlap (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (k : ℝ) :
    (leftFrame (D.rowloc x) (D.colloc x))† ∘L
        diagonal (D.matrix x) (lchsHamiltonian (D.matrix x) k) ∘L
        rightFrame (D.rowloc x) (D.colloc x) =
      ODEHermitianReduction.lchsHamiltonian
        (SparseStateOverlap.matrixOperator (D.matrix x)) k := by
  have h := native_frame_certificate D x (lchsHamiltonian (D.matrix x) k)
    (fun i j hij hji => lchsHamiltonian_eq_zero (D.matrix x) k i j hij hji)
  exact h.2.2.trans (matrixOperator_lchsHamiltonian (D.matrix x) k)

/-- A common cutoff certifies both tagged boundary energies and the full
diagonal norm. These are derived bounds for the concrete branch, not supplied
moment or implementation certificates. -/
theorem native_energy_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (etaH etaD k R : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hk : |k| ≤ R)
    (hRowH : ∀ i, ∑ j, ‖hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hColH : ∀ j, ∑ i, ‖hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hRowD : ∀ i, ∑ j, ‖dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hColD : ∀ j, ∑ i, ‖dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    ‖diagonal (D.matrix x) (lchsHamiltonian (D.matrix x) k)‖ ≤ etaH + R * etaD ∧
      ∀ v : EuclideanSpace ℂ n,
        ‖((diagonal (D.matrix x) (lchsHamiltonian (D.matrix x) k))†)
          (leftFrame (D.rowloc x) (D.colloc x) v)‖ ^ 2 ≤
            (etaH + R * etaD) ^ 2 * ‖v‖ ^ 2 ∧
        ‖diagonal (D.matrix x) (lchsHamiltonian (D.matrix x) k)
          (rightFrame (D.rowloc x) (D.colloc x) v)‖ ^ 2 ≤
            (etaH + R * etaD) ^ 2 * ‖v‖ ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg k).trans hk
  have hEnergy := lchs_energies_le_radius (D.matrix x) etaH etaD k R
    hH hD hk hRowH hColH hRowD hColD
  refine ⟨diagonal_norm_le _ _ _ (add_nonneg hH (mul_nonneg hR hD))
    (lchs_entry_norm_le_radius (D.matrix x) etaH etaD k R hH hD hk hRowH hRowD), ?_⟩
  intro v
  exact native_boundary_energy_certificate D x (lchsHamiltonian (D.matrix x) k)
    (etaH + R * etaD) hEnergy.1 hEnergy.2 v

end
end SparseHamiltonian.ODETaggedLCHS
