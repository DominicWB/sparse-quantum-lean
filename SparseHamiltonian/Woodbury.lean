import SparseHamiltonian.ResolventEndpoints

/-!
# Exact finite-rank resolvent identities

The public and private spaces are independently typed normed complex spaces.
This module proves the two-sided Woodbury inverse and its two boundary
identities from explicitly supplied two-sided inverses. No spectral or norm
estimate is assumed or asserted.
-/

namespace SparseHamiltonian

noncomputable section

open ContinuousLinearMap

section TypedOperators

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The finite-rank correction to the unperturbed inverse. -/
def woodburyInverse (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ) : V →L[ℂ] V :=
  R - κ • (R ∘L J ∘L K ∘L B ∘L R)

/-- The right endpoint of the corrected inverse. -/
theorem woodbury_inclusion_endpoint (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ)
    (hK : K ∘L (1 + κ • (B ∘L R ∘L J)) = 1) :
    woodburyInverse R J K B κ ∘L J = R ∘L J ∘L K := by
  have hCancel : 1 - κ • (K ∘L (B ∘L R ∘L J)) = K := by
    have h := hK
    simp only [comp_add, comp_smul, one_def, comp_id] at h
    exact (eq_sub_of_add_eq h).symm
  calc
    woodburyInverse R J K B κ ∘L J =
        (R ∘L J) ∘L (1 - κ • (K ∘L (B ∘L R ∘L J))) := by
      simp only [woodburyInverse, sub_comp, smul_comp, comp_sub, comp_smul,
        one_def, comp_id, comp_assoc]
    _ = R ∘L J ∘L K := by rw [hCancel, comp_assoc]

/-- The left endpoint of the corrected inverse. -/
theorem woodbury_observation_endpoint (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ)
    (hK : (1 + κ • (B ∘L R ∘L J)) ∘L K = 1) :
    B ∘L woodburyInverse R J K B κ = K ∘L B ∘L R := by
  have hCancel : 1 - κ • ((B ∘L R ∘L J) ∘L K) = K := by
    have h := hK
    simp only [add_comp, smul_comp, one_def, id_comp] at h
    exact (eq_sub_of_add_eq h).symm
  calc
    B ∘L woodburyInverse R J K B κ =
        (1 - κ • ((B ∘L R ∘L J) ∘L K)) ∘L (B ∘L R) := by
      simp only [woodburyInverse, comp_sub, comp_smul, sub_comp, smul_comp,
        one_def, id_comp, comp_assoc]
    _ = K ∘L B ∘L R := by rw [hCancel]

/-- The Woodbury correction is a right inverse of the rank-updated operator. -/
theorem woodbury_right_inverse (X R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ)
    (hXR : X ∘L R = 1)
    (hK : (1 + κ • (B ∘L R ∘L J)) ∘L K = 1) :
    (X + κ • (J ∘L B)) ∘L woodburyInverse R J K B κ = 1 := by
  have hXS : X ∘L woodburyInverse R J K B κ =
      1 - κ • (J ∘L K ∘L B ∘L R) := by
    simp only [woodburyInverse, comp_sub, comp_smul]
    rw [hXR, ← comp_assoc X R, hXR, one_def, id_comp]
  calc
    (X + κ • (J ∘L B)) ∘L woodburyInverse R J K B κ =
        X ∘L woodburyInverse R J K B κ +
          κ • (J ∘L (B ∘L woodburyInverse R J K B κ)) := by
      simp only [add_comp, smul_comp, comp_assoc]
    _ = 1 := by
      rw [hXS, woodbury_observation_endpoint R J K B κ hK]
      simp only [sub_add_cancel]

/-- The Woodbury correction is a left inverse of the rank-updated operator. -/
theorem woodbury_left_inverse (X R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ)
    (hRX : R ∘L X = 1)
    (hK : K ∘L (1 + κ • (B ∘L R ∘L J)) = 1) :
    woodburyInverse R J K B κ ∘L (X + κ • (J ∘L B)) = 1 := by
  have hSX : woodburyInverse R J K B κ ∘L X =
      1 - κ • (R ∘L J ∘L K ∘L B) := by
    simp only [woodburyInverse, sub_comp, smul_comp, comp_assoc, hRX,
      one_def, comp_id]
  calc
    woodburyInverse R J K B κ ∘L (X + κ • (J ∘L B)) =
        woodburyInverse R J K B κ ∘L X +
          κ • ((woodburyInverse R J K B κ ∘L J) ∘L B) := by
      simp only [comp_add, comp_smul, comp_assoc]
    _ = 1 := by
      rw [hSX, woodbury_inclusion_endpoint R J K B κ hK]
      simp only [comp_assoc, sub_add_cancel]

end TypedOperators

section TransferDifference

variable {𝓐 : Type*} [Ring 𝓐] [Algebra ℂ 𝓐]

/-- Exact difference of the boundary transfers, without dividing by κ. -/
theorem woodbury_transfer_difference (F F₀ K K₀ : 𝓐) (κ : ℂ)
    (hLK : (1 + κ • F) * K = 1) (hKL : K * (1 + κ • F) = 1)
    (hL₀K₀ : (1 + κ • F₀) * K₀ = 1)
    (hK₀L₀ : K₀ * (1 + κ • F₀) = 1) :
    F * K - F₀ * K₀ = K * (F - F₀) * K₀ := by
  have hComm : (1 + κ • F) * F = F * (1 + κ • F) := by
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  have hFirst : (1 + κ • F) * (F * K) * (1 + κ • F₀) =
      F * (1 + κ • F₀) := by
    rw [← mul_assoc (1 + κ • F) F K, hComm,
      mul_assoc F (1 + κ • F) K, hLK, mul_one]
  have hSecond : (1 + κ • F) * (F₀ * K₀) * (1 + κ • F₀) =
      (1 + κ • F) * F₀ := by
    simp only [mul_assoc, hK₀L₀, mul_one]
  have hMiddle :
      (1 + κ • F) * (F * K - F₀ * K₀) * (1 + κ • F₀) = F - F₀ := by
    rw [mul_sub, sub_mul, hFirst, hSecond]
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
    abel
  calc
    F * K - F₀ * K₀ =
        K * ((1 + κ • F) * (F * K - F₀ * K₀) * (1 + κ • F₀)) * K₀ := by
      symm
      calc
        _ = (K * (1 + κ • F)) * (F * K - F₀ * K₀) *
            ((1 + κ • F₀) * K₀) := by simp only [mul_assoc]
        _ = F * K - F₀ * K₀ := by rw [hKL, hL₀K₀, one_mul, mul_one]
    _ = K * (F - F₀) * K₀ := by rw [hMiddle]

end TransferDifference

end

end SparseHamiltonian
