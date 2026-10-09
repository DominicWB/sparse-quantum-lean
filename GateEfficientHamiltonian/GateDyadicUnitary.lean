import GateEfficientHamiltonian.GateDyadicPrefixBridge
/-!
# Unitary validity of the actual dyadic root matrices

The frame correctness results apply to arbitrary coefficient arrays.  Here
we prove that the concrete matrices used in the dyadic Hamiltonian boundary
circuit are unitary on the full qubit, so those algebraic circuits consist
of reversible Boolean gates and genuine one-control quantum rotations.

Compiles with Lean/Mathlib 4.32.1.
-/

namespace SparseHamiltonian.GateDyadicUnitary

noncomputable section

open scoped BigOperators

/-- The real plane rotation as an actual two-by-two complex matrix. -/
def rotationCoefficients (z v : ℝ) : GatePrefixCircuit.Coefficients := fun row col =>
  match row, col with
  | false, false => (z : ℂ)
  | false, true => -(v : ℂ)
  | true, false => (v : ℂ)
  | true, true => (z : ℂ)

/-- Both matrix inverse identities are proved, not assumed as a property of
an abstract rotation gate. -/
theorem rotationCoefficients_unitary (z v : ℝ) (hunit : z ^ 2 + v ^ 2 = 1) :
    (rotationCoefficients z v).IsUnitary := by
  have hu : (z : ℂ) ^ 2 + (v : ℂ) ^ 2 = 1 := by exact_mod_cast hunit
  constructor <;> ext i j <;> cases i <;> cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, rotationCoefficients]
  all_goals first
    | exact hu
    | simpa only [← pow_two, add_comm] using hu
    | ring

theorem input_parameter_unit (z : ℝ) :
    (z / GateDyadicBoundary.rootDenominator z) ^ 2 +
      (1 / GateDyadicBoundary.rootDenominator z) ^ 2 = 1 := by
  have hd := GateDyadicBoundary.rootDenominator_ne_zero z
  have hd2 := GateDyadicBoundary.rootDenominator_sq z
  field_simp [hd]
  nlinarith

theorem output_parameter_unit (z : ℝ) :
    (1 / GateDyadicBoundary.rootDenominator z) ^ 2 +
      (z / GateDyadicBoundary.rootDenominator z) ^ 2 = 1 := by
  simpa only [add_comm] using input_parameter_unit z

theorem inputCoefficients_eq_rotation (z : ℝ) :
    GateDyadicPrefixBridge.inputCoefficients z =
      rotationCoefficients (z / GateDyadicBoundary.rootDenominator z)
        (1 / GateDyadicBoundary.rootDenominator z) := by
  ext i j
  cases i <;> cases j <;>
    simp [GateDyadicPrefixBridge.inputCoefficients, rotationCoefficients, neg_div]

theorem outputCoefficients_eq_rotation (z : ℝ) :
    GateDyadicPrefixBridge.outputCoefficients z =
      rotationCoefficients (1 / GateDyadicBoundary.rootDenominator z)
        (z / GateDyadicBoundary.rootDenominator z) := by
  ext i j
  cases i <;> cases j <;>
    simp [GateDyadicPrefixBridge.outputCoefficients, rotationCoefficients, neg_div]

/-- Every actual input-frame matrix is unitary, with no restriction on its
real argument. -/
theorem inputCoefficients_unitary (z : ℝ) :
    (GateDyadicPrefixBridge.inputCoefficients z).IsUnitary := by
  rw [inputCoefficients_eq_rotation]
  exact rotationCoefficients_unitary _ _ (input_parameter_unit z)

/-- Every actual output-frame matrix is unitary, with no restriction on its
real argument. -/
theorem outputCoefficients_unitary (z : ℝ) :
    (GateDyadicPrefixBridge.outputCoefficients z).IsUnitary := by
  rw [outputCoefficients_eq_rotation]
  exact rotationCoefficients_unitary _ _ (output_parameter_unit z)

/-- The complete explicit input-frame circuit contains only valid elementary
quantum gates, including at depths where the central cosine is zero. -/
theorem input_circuit_valid (c : ℝ) (m : ℕ) :
    ∀ g ∈ GatePrefixCircuit.circuit (fun j : Fin m =>
      GateDyadicPrefixBridge.inputCoefficients (GateDyadicBoundary.centralCosine c j.val)),
        g.Valid := by
  apply GatePrefixCircuit.circuit_valid
  intro j
  exact inputCoefficients_unitary _

/-- The independently constructed output-frame circuit has the same gate
validity guarantee. -/
theorem output_circuit_valid (c : ℝ) (m : ℕ) :
    ∀ g ∈ GatePrefixCircuit.circuit (fun j : Fin m =>
      GateDyadicPrefixBridge.outputCoefficients (GateDyadicBoundary.centralCosine c j.val)),
        g.Valid := by
  apply GatePrefixCircuit.circuit_valid
  intro j
  exact outputCoefficients_unitary _

/-- Reverse the actual input-frame gate list to implement the inverse frame,
returning every prefix flag clean.  The matrix-unitarity premise of the
abstract inverse-circuit lemma is discharged here for the concrete dyadic
coefficients. -/
theorem input_inverse_circuit_correct (c : ℝ) (m : ℕ)
    (u : GateDyadicBoundary.Private m) :
    GatePrefixCircuit.run (GatePrefixInverse.circuit
      (fun j : Fin m => GateDyadicPrefixBridge.inputCoefficients
        (GateDyadicBoundary.centralCosine c j.val)))
      (GatePrefixCircuit.embed 0 (GateDyadicPrefixBridge.amplitudes m u)) =
        GatePrefixCircuit.embed 0 (GateDyadicPrefixBridge.amplitudes m
          (GateDyadicBoundary.inputFrameInverse c m u)) := by
  apply GateDyadicPrefixBridge.input_inverse_circuit_correct_of_unitary
  intro j
  exact inputCoefficients_unitary _

/-- The central doubled-angle rotation is unitary as well. -/
theorem centralCoefficients_unitary (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) :
    (rotationCoefficients (GateDyadicBoundary.centralCosine c m)
      (GateDyadicBoundary.centralSine c σ m)).IsUnitary :=
  rotationCoefficients_unitary _ _ (GateDyadicBoundary.central_unit c σ hunit m)

end
end SparseHamiltonian.GateDyadicUnitary
