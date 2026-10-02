import SparseHamiltonian.BaseTransfer

/-!
# Connecting the local inverse to the chronological transfer

The public transfer obtained by eliminating a local private register is
exactly the boundary transfer used in the stability estimates. The denominator
identities connect the rank-updated clock to the same Woodbury inverse.
-/

namespace SparseHamiltonian

noncomputable section

open ContinuousLinearMap

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The actual scalar entrance and exit couplings give the boundary transfer. -/
theorem woodbury_chronological_transfer (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ) (c σ : ℝ)
    (hK : K ∘L (1 + κ • (B ∘L R ∘L J)) = 1) :
    (c : ℂ) • (1 : P →L[ℂ] P) +
      ((-(σ : ℂ)) • B) ∘L woodburyInverse R J K B κ ∘L ((σ : ℂ) • J) =
      BoundaryTransfer.transfer (c : ℂ) (σ ^ 2) (B ∘L R ∘L J) K := by
  have hScalar : (σ : ℂ) * (σ : ℂ) = ((σ ^ 2 : ℝ) : ℂ) := by
    simp only [pow_two, Complex.ofReal_mul]
  simp only [smul_comp, comp_smul, smul_smul, smul_neg, neg_comp,
    woodbury_inclusion_endpoint R J K B κ hK, hScalar,
    neg_smul, BoundaryTransfer.transfer, mul_def, comp_assoc, sub_eq_add_neg]

/-- A local additive rank update has precisely the Woodbury denominator. -/
theorem local_denominator_additive (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (B : V →L[ℂ] P) (κ z : ℂ) :
    z • (1 : V →L[ℂ] V) - (D - κ • (J ∘L B)) =
      (z • (1 : V →L[ℂ] V) - D) + κ • (J ∘L B) := by
  abel

/-- The factored clock update gives the same denominator. Taking `L = J†`
produces the orthogonal-boundary clock appearing in the transducer. -/
theorem local_denominator_factored (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (L : V →L[ℂ] P) (κ z : ℂ) :
    z • (1 : V →L[ℂ] V) - ((1 - κ • (J ∘L L)) ∘L D) =
      (z • (1 : V →L[ℂ] V) - D) + κ • (J ∘L (L ∘L D)) := by
  simp only [sub_comp, smul_comp, one_def, id_comp, comp_assoc]
  abel

end

end SparseHamiltonian
