import SparseHamiltonian.NativeSparseClock

/-!
# Weighted analytic promises for mixed native program clocks

The actual heterogeneous native clocks, their resolvents and fixed weighted
boundaries are transported into the same flattened layout used by the active
native-query implementation. Counts enter only through the maximum and the
weighted average of the genuine count-plus-two clock lengths.
-/
namespace SparseHamiltonian.NativeWeightedClockBounds
noncomputable section
open ContinuousLinearMap OracleCircuit NativeHeterogeneousActiveClock
open FlattenedLookupClockBounds
open scoped InnerProduct BigOperators

variable {X I B L : Type*} [Fintype I] [Fintype B] [DecidableEq B]
  [Fintype L] [DecidableEq L]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The explicit heterogeneous inverse in the single clock-label layout. -/
def flatResolvent (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (p : I → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (x : X) :
    PiLp 2 (fun _ : Slot F p => EuclideanSpace ℂ B) →L[ℂ]
      PiLp 2 (fun _ : Slot F p => EuclideanSpace ℂ B) :=
  (flatten F p).conjStarAlgEquiv
    (MultiWeightedProgramClockBounds.familyResolvent p hF hInv x)

/-- Fixed weighted preparation into flattened clock boundaries. -/
def flatBoundary (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (weights : I → ℝ) (p : I → MultiOracleCircuit.Program F)
    (E : I → P →ₗᵢ[ℂ] EuclideanSpace ℂ B) : P →L[ℂ] PiLp 2 (fun _ : Slot F p => EuclideanSpace ℂ B) :=
  transportBoundary (flatten F p) (MultiWeightedProgramClockBounds.boundary weights p E)

omit [DecidableEq B] [Fintype L] [DecidableEq L] in
/-- All analytic simulation promises for the exact, flattened heterogeneous
native clocks. No inverse, norm, compression, or clock implementation is assumed. -/
theorem family_promises (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (weights : I → ℝ)
    (p : I → MultiOracleCircuit.Program F)
    (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, (MultiQueryClock.slots (p i) : ℝ) ≤ Q)
    (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v)
    (E : I → P →ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    let D := flatFamilyClock F p hF hInv
    let R := flatResolvent F p hF hInv
    let J := flatBoundary F weights p E
    let H := MultiWeightedProgramClockBounds.generator weights p E
    let qbar := MultiWeightedProgramClockBounds.averageLength weights p
    let b := Real.sqrt (qbar / 2)
    (∀ x, (D x)† ∘L D x = 1) ∧ J† ∘L J = 1 ∧
      (∀ x, (1 - D x) ∘L R x = 1) ∧ (∀ x, R x ∘L (1 - D x) = 1) ∧
      (∀ x, ‖R x‖ ≤ Q) ∧
      (∀ x, J† ∘L R x ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H x)) ∧
      (∀ x, star (H x) = H x) ∧ (∀ x, ‖H x‖ ≤ 1) ∧
      (∀ x, ‖R x ∘L J‖ ≤ b) ∧ b ^ 2 ≤ qbar / 2 ∧ qbar ≤ Q := by
  obtain ⟨hD, hJ, hRight, hLeft, hNorm, hBoundary, hSelf, hH, hEnd, hSq, hAverage⟩ :=
    MultiWeightedProgramClockBounds.family_promises weights p hw hsum Q hQ hqQ
      hF hInv E
  dsimp only
  refine ⟨?_, transportBoundary_isometry _ _ hJ, ?_, ?_, ?_, ?_, hSelf, hH, ?_, hSq, hAverage⟩
  · intro x
    exact ((familyClock_unitary F p hF hInv x).transport (flatten F p)).1
  · intro x
    exact (conjugate_inverse (flatten F p) _ _ (hRight x) (hLeft x)).1
  · intro x
    exact (conjugate_inverse (flatten F p) _ _ (hRight x) (hLeft x)).2
  · intro x
    rw [flatResolvent, conjugate_norm]
    exact hNorm x
  · intro x
    rw [flatResolvent, flatBoundary, transportBoundary_compression]
    exact hBoundary x
  · intro x
    rw [flatResolvent, flatBoundary, transportBoundary_endpoint_norm]
    exact hEnd x

end
end SparseHamiltonian.NativeWeightedClockBounds
