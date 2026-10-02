import SparseHamiltonian.ChronologicalInverse

/-!
# Two-sided finite chronological inversion

The chronological response operators act on a genuine finite ℓ² direct sum.
Their two-sided inverse identities are derived from the proved sequence
recurrences, using restriction and zero extension. No finite inverse formula
or spectrum-free hypothesis is assumed.
-/

namespace SparseHamiltonian.FiniteChronologicalInverse

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent
open SparseHamiltonian.ChronologicalInverse

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Restriction of a sequence to its first `T` time slots in the ℓ² direct sum. -/
def restrictSequence (T : ℕ) (x : ℕ → V) : BlockOperator.H T V :=
  WithLp.toLp 2 (fun k : Fin T => x k)

/-- Extend a finite trajectory by zero after its final time slot. -/
def extendSequence {T : ℕ} (x : BlockOperator.H T V) (n : ℕ) : V :=
  if h : n < T then x ⟨n, h⟩ else 0

omit [NormedAddCommGroup V] [NormedSpace ℂ V] in
@[simp] theorem restrictSequence_apply (T : ℕ) (x : ℕ → V) (k : Fin T) :
    restrictSequence T x k = x k := rfl

omit [NormedSpace ℂ V] in
@[simp] theorem extendSequence_apply {T : ℕ} (x : BlockOperator.H T V) (k : Fin T) :
    extendSequence x k = x k := by
  simp [extendSequence, k.isLt]

omit [NormedSpace ℂ V] in
/-- Zero extension is a right inverse of restriction. -/
@[simp] theorem restrict_extend {T : ℕ} (x : BlockOperator.H T V) :
    restrictSequence T (extendSequence x) = x := by
  ext k
  simp

/-- The finite forward chronological equations. -/
noncomputable def forwardOperator (X : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  chronologicalOperator X (-A) c B T

/-- The finite inverse obtained by the local elimination recurrence. -/
noncomputable def inverseOperator (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  chronologicalOperator R (R ∘L A) (c + B ∘L R ∘L A) (B ∘L R) T

/-- Restricting the proved forward sequence recurrence gives exactly the finite
forward operator. -/
theorem forwardOperator_restrict (X : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) (x : ℕ → V) :
    forwardOperator X A c B T (restrictSequence T x) =
      restrictSequence T (forwardResponse X A c B x) := by
  ext k
  change chronologicalOperator X (-A) c B T (WithLp.toLp 2 (fun j : Fin T => x j)) k =
    forwardResponse X A c B x k
  rw [chronologicalOperator_apply]
  simp [chronologicalPrivateState, forwardResponse, sub_eq_add_neg]

/-- The finite inverse operator is the restriction of the explicitly derived
inverse sequence recurrence. -/
theorem inverseOperator_restrict (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) (y : ℕ → V) :
    inverseOperator R A c B T (restrictSequence T y) =
      restrictSequence T (inverseResponse R A c B y) := by
  ext k
  exact chronologicalOperator_apply R (R ∘L A) (c + B ∘L R ∘L A) (B ∘L R) y k

/-- The forward chronological equations with local diagonal `z I - Dloc` are
exactly the resolvent denominator of the constructed finite private block. -/
theorem forwardOperator_resolvent_denominator (Dloc : V →L[ℂ] V)
    (A : P →L[ℂ] V) (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) (z : ℂ) :
    forwardOperator (z • 1 - Dloc) A c B T =
      z • 1 - chronologicalOperator Dloc A c B T := by
  have hseq (x : ℕ → V) :
      forwardOperator (z • 1 - Dloc) A c B T (restrictSequence T x) =
        (z • 1 - chronologicalOperator Dloc A c B T) (restrictSequence T x) := by
    rw [forwardOperator_restrict]
    ext k
    change forwardResponse (z • 1 - Dloc) A c B x k =
      z • x k - chronologicalOperator Dloc A c B T
        (WithLp.toLp 2 (fun j : Fin T => x j)) k
    rw [chronologicalOperator_apply]
    simp [forwardResponse, chronologicalPrivateState, sub_add_eq_sub_sub]
  apply ContinuousLinearMap.ext
  intro x
  simpa using hseq (extendSequence x)

/-- A right local inverse gives a genuine right inverse on the finite ℓ²
trajectory space. -/
theorem forward_inverse (X R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) (hXR : X ∘L R = 1) :
    forwardOperator X A c B T ∘L inverseOperator R A c B T = 1 := by
  have hseq (y : ℕ → V) :
      forwardOperator X A c B T (inverseOperator R A c B T (restrictSequence T y)) =
        restrictSequence T y := by
    rw [inverseOperator_restrict, forwardOperator_restrict]
    congr 1
    funext n
    exact ChronologicalInverse.forward_inverse X R A c B hXR y n
  apply ContinuousLinearMap.ext
  intro y
  simpa using hseq (extendSequence y)

/-- Two-sided local inversion gives a genuine left inverse on the finite ℓ²
trajectory space as well. -/
theorem inverse_forward (X R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ)
    (hXR : X ∘L R = 1) (hRX : R ∘L X = 1) :
    inverseOperator R A c B T ∘L forwardOperator X A c B T = 1 := by
  have hseq (x : ℕ → V) :
      inverseOperator R A c B T (forwardOperator X A c B T (restrictSequence T x)) =
        restrictSequence T x := by
    rw [forwardOperator_restrict, inverseOperator_restrict,
      ChronologicalInverse.inverse_forward X R A c B hXR hRX]
  apply ContinuousLinearMap.ext
  intro x
  simpa using hseq (extendSequence x)

/-- Both finite inverse identities packaged together for downstream resolvent
and norm estimates. -/
theorem two_sided_inverse (X R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ)
    (hXR : X ∘L R = 1) (hRX : R ∘L X = 1) :
    forwardOperator X A c B T ∘L inverseOperator R A c B T = 1 ∧
      inverseOperator R A c B T ∘L forwardOperator X A c B T = 1 :=
  ⟨forward_inverse X R A c B T hXR, inverse_forward X R A c B T hXR hRX⟩

/-- Local inversion at `z` produces a two-sided inverse of the actual finite
resolvent denominator `z I - D`, where `D` is the chronological private block. -/
theorem resolvent_two_sided_inverse (Dloc R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (c : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) (z : ℂ)
    (hRight : (z • 1 - Dloc) ∘L R = 1) (hLeft : R ∘L (z • 1 - Dloc) = 1) :
    (z • 1 - chronologicalOperator Dloc A c B T) ∘L inverseOperator R A c B T = 1 ∧
      inverseOperator R A c B T ∘L (z • 1 - chronologicalOperator Dloc A c B T) = 1 := by
  rw [← forwardOperator_resolvent_denominator]
  exact two_sided_inverse (z • 1 - Dloc) R A c B T hRight hLeft

end SparseHamiltonian.FiniteChronologicalInverse
