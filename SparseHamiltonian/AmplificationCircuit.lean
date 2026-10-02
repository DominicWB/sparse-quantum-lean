import SparseHamiltonian.FilterError

/-!
# One round of oblivious amplitude amplification

The input and output Hilbert spaces are independently typed. Reflections about
the ranges of two isometries give an isometry whose compressed block is the
usual cubic amplification polynomial. These are identities of genuine bounded
operators; no matrix-coordinate or equal-space identification is used.
-/

namespace SparseHamiltonian

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Reflection about the range of an isometry. -/
def rangeReflection (J : P →L[ℂ] K) : K →L[ℂ] K :=
  (2 : ℂ) • (J ∘L J†) - 1

/-- The adjoint of the range reflection is itself. -/
theorem rangeReflection_adjoint (J : P →L[ℂ] K) :
    (rangeReflection J)† = rangeReflection J := by
  simp [rangeReflection, two_smul]

/-- The range reflection is an involution when its defining map is an isometry. -/
theorem rangeReflection_comp_self (J : P →L[ℂ] K)
    (hJ : J† ∘L J = 1) :
    rangeReflection J ∘L rangeReflection J = 1 := by
  have hJv (v : P) : (J†) (J v) = v := by
    have h := congrArg (fun A : P →L[ℂ] P => A v) hJ
    simpa using h
  ext v
  simp only [rangeReflection, two_smul, comp_apply, sub_apply, add_apply,
    one_def, id_apply, map_sub, map_add, hJv]
  abel

/-- In particular each range reflection is an isometry. -/
theorem rangeReflection_isometry (J : P →L[ℂ] K)
    (hJ : J† ∘L J = 1) :
    (rangeReflection J)† ∘L rangeReflection J = 1 := by
  rw [rangeReflection_adjoint]
  exact rangeReflection_comp_self J hJ

/-- The signed pair of reflections implementing one amplification round. -/
def reflectedAmplification (J T : P →L[ℂ] K) : P →L[ℂ] K :=
  -(rangeReflection T ∘L (rangeReflection J ∘L T))

/-- One round of amplification preserves the full output norm. -/
theorem reflectedAmplification_isometry (J T : P →L[ℂ] K)
    (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1) :
    (reflectedAmplification J T)† ∘L reflectedAmplification J T = 1 := by
  have hR (A : P →L[ℂ] K) (hA : A† ∘L A = 1)
      (B : P →L[ℂ] K) :
      rangeReflection A ∘L (rangeReflection A ∘L B) = B := by
    rw [← comp_assoc, rangeReflection_comp_self A hA, one_def, id_comp]
  simp only [reflectedAmplification, map_neg, adjoint_comp,
    rangeReflection_adjoint, neg_comp, comp_neg, neg_neg, comp_assoc]
  rw [hR T hT, hR J hJ, hT]

/-- The public block of the reflection circuit is the cubic amplification map. -/
theorem reflectedAmplification_compression (J T : P →L[ℂ] K)
    (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1) :
    J† ∘L reflectedAmplification J T =
      (3 : ℂ) • (J† ∘L T) -
        (4 : ℂ) • ((J† ∘L T) ∘L (J† ∘L T)† ∘L (J† ∘L T)) := by
  have hJv (v : P) : (J†) (J v) = v := by
    have h := congrArg (fun A : P →L[ℂ] P => A v) hJ
    simpa using h
  have hTv (v : P) : (T†) (T v) = v := by
    have h := congrArg (fun A : P →L[ℂ] P => A v) hT
    simpa using h
  have hThree : (3 : ℂ) = 1 + 1 + 1 := by norm_num
  have hFour : (4 : ℂ) = 1 + 1 + 1 + 1 := by norm_num
  ext v
  simp only [reflectedAmplification, rangeReflection, adjoint_comp, adjoint_adjoint,
    two_smul, hThree, hFour, add_smul, one_smul, comp_apply,
    sub_apply, add_apply, neg_apply, one_def, id_apply, map_sub, map_add, map_neg, hJv, hTv]
  abel

end

end SparseHamiltonian
