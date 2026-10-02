import SparseHamiltonian.PhysicalPhaseSynthesis

/-!
# Counted native-oracle realization of polynomial synthesis

The algebraically synthesized final coordinate phase and global phase are fixed
query-free gates. Adding them to the native phase program preserves every
weighted query count and gives the complete synthesized polynomial column on
all certified invariant planes, with one program uniform over the oracle input.
-/

namespace SparseHamiltonian.NativePolynomialSynthesis

noncomputable section
open Polynomial AmplitudePolynomialSequence PhysicalPhaseSynthesis
open ContinuousLinearMap ComplexAmplitudeRotation OracleCircuit

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- The entire workspace is an orthogonal projection. -/
theorem identity_orthogonal : PhaseSubspaceGates.IsOrthogonalProjection (1 : K →L[ℂ] K) := by
  constructor <;> simp

/-- Add the two fixed output phases required by converse synthesis. -/
def nativePhasedPrepared {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (v u : UnitPhase) (ss : List Phases) :
    MultiOracleCircuit.Program O :=
  .seq (.fixed (PhaseSubspaceGates.phase 1 v)
    (PhaseSubspaceGates.phase_unitary 1 identity_orthogonal v v.property))
    (.seq (.fixed (PhaseSubspaceGates.phase Q u)
      (PhaseSubspaceGates.phase_unitary Q hQ u u.property))
      (InvariantPhaseSequence.nativePrepared p P Q hP hQ ss))

/-- The extra synthesis phases are free for every assignment of oracle-label costs. -/
@[simp] theorem nativePhasedPrepared_cost {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (v u : UnitPhase) (ss : List Phases)
    (w : L → ℕ) :
    (nativePhasedPrepared p P Q hP hQ v u ss).cost w = (2 * ss.length + 1) * p.cost w := by
  simp [nativePhasedPrepared]

/-- In particular, total sparse-oracle calls retain the exact odd-degree factor. -/
@[simp] theorem nativePhasedPrepared_count {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (v u : UnitPhase) (ss : List Phases) :
    (nativePhasedPrepared p P Q hP hQ v u ss).count = (2 * ss.length + 1) * p.count := by
  simp [nativePhasedPrepared]

/-- The entire output column, including its complementary amplitude, is correct. -/
theorem nativePhasedPrepared_column {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (v u : UnitPhase) (ss : List Phases)
    (y : X) (hO : ∀ l y, IsUnitary (O l y)) (x : ℝ) (hx : |x| ≤ 1)
    (V : Qubit →L[ℂ] K)
    (hPV : (p.eval y * P * star (p.eval y)) ∘L V =
      V ∘L (rotation (x : ℂ) * cleanProjection * star (rotation (x : ℂ))))
    (hQV : Q ∘L V = V ∘L cleanProjection)
    (z : K) (hz : p.eval y z = V (rotation (x : ℂ) clean)) :
    (nativePhasedPrepared p P Q hP hQ v u ss).eval y z =
      V (column x (C ((v : ℂ) * (u : ℂ)) * (polynomials ss).1)
        (C (v : ℂ) * (polynomials ss).2)) := by
  have hphase := congrArg
    (fun A : Qubit →L[ℂ] K => A (column x (polynomials ss).1 (polynomials ss).2))
    (InvariantPhaseSequence.phase_intertwines Q cleanProjection V hQV (u : ℂ))
  simp only [comp_apply, ← phase_eq_subspace] at hphase
  simp only [nativePhasedPrepared, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_fixed, mul_apply_eq_comp]
  rw [InvariantPhaseSequence.nativePrepared_column p P Q hP hQ ss y hO x hx V hPV hQV z hz,
    hphase, PhaseSubspaceGates.phase_apply_of_fixed (1 : K →L[ℂ] K) v _ (by simp),
    ← map_smul, phased_column]

/-- Converse polynomial synthesis yields one counted circuit uniform over all
oracle inputs and every compatible (possibly degenerate) invariant plane. -/
theorem native_synthesis {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (hO : ∀ l y, IsUnitary (O l y))
    (m : ℕ) (A B : ℂ[X]) (hA : A.natDegree ≤ 2 * m + 1) (hB : B.natDegree ≤ 2 * m)
    (ha : A.comp (-Polynomial.X) = -A) (hb : B.comp (-Polynomial.X) = B)
    (h : PolynomialUnitarity.IsNormalized A B) :
    ∃ r : MultiOracleCircuit.Program O,
      (∀ w : L → ℕ, r.cost w = (2 * m + 1) * p.cost w) ∧
      ∀ (y : X) (x : ℝ), |x| ≤ 1 → ∀ (V : Qubit →L[ℂ] K),
        (p.eval y * P * star (p.eval y)) ∘L V =
          V ∘L (rotation (x : ℂ) * cleanProjection * star (rotation (x : ℂ))) →
        Q ∘L V = V ∘L cleanProjection → ∀ z : K,
        p.eval y z = V (rotation (x : ℂ) clean) → r.eval y z = V (column x A B) := by
  obtain ⟨v, u, ss, hss, hgood, hbad⟩ := paired_synthesis m A B hA hB ha hb h
  refine ⟨nativePhasedPrepared p P Q hP hQ v u ss, ?_, ?_⟩
  · intro w
    simp only [nativePhasedPrepared_cost, hss]
  · intro y x hx V hPV hQV z hz
    rw [nativePhasedPrepared_column p P Q hP hQ v u ss y hO x hx V hPV hQV z hz,
      ← hgood, ← hbad]

end
end SparseHamiltonian.NativePolynomialSynthesis
