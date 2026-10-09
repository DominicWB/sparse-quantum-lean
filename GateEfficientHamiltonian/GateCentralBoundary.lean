import GateEfficientHamiltonian.GateZeroControls
/-!
# The central public/private rotation on the binary clock register

The high bit distinguishes the public and private sectors. The public
amplitude is stored at the zero word of its sector. The central dyadic
rotation therefore acts on the high bit conditioned on all clock bits
being zero. Its actual clean prefix circuit is related below to the
independently defined central operation in the chronological factorisation.

The last count is the sum of the three constructed component lists, not a
gate count for the entire Hamiltonian simulator.  The complete simulator, on
one common workspace with sector controls for both frames, is constructed and
counted in `GateEfficientHamiltonian/Circuit/` (`Circuit/Theorem.lean`).
-/

namespace SparseHamiltonian.GateCentralBoundary

noncomputable section

/-- Zero amplitudes at every position except the distinguished root. -/
def zeroRemainder : (m : ℕ) → GateDyadicBoundary.Remainder m
  | 0 => PUnit.unit
  | m + 1 => (zeroRemainder m, (0, zeroRemainder m))

/-- The high bit is false in the public sector and true in the private one. -/
def clockWords (m : ℕ) (x : GateDyadicBoundary.State m) :
    GateDyadicBoundary.Private (m + 1) :=
  GateDyadicBoundary.joinPrivate (x.1, zeroRemainder m) x.2

/-- Physical binary-word amplitudes before adding the prefix flags. -/
def amplitudes (m : ℕ) (x : GateDyadicBoundary.State m) :
    GatePrefixCircuit.SlotState (m + 1) :=
  GateDyadicPrefixBridge.amplitudes (m + 1) (clockWords m x)

def coefficients (c σ : ℝ) (m : ℕ) : GatePrefixCircuit.Coefficients :=
  GateDyadicUnitary.rotationCoefficients
    (GateDyadicBoundary.centralCosine c m)
    (GateDyadicBoundary.centralSine c σ m)

/-- An actual list of one- and two-control Boolean gates and known
single-controlled one-qubit rotations. No many-control primitive occurs. -/
def circuit (c σ : ℝ) (m : ℕ) : List (GatePrefixCircuit.Gate (m + 1)) :=
  GateZeroControls.circuit m (coefficients c σ m)

theorem topMix_clockWords (c σ : ℝ) (m : ℕ)
    (x : GateDyadicBoundary.State m) :
    GateDyadicPrefixBridge.topMix (coefficients c σ m) (clockWords m x) =
      clockWords m (GateDyadicBoundary.central c σ m x) := by
  rcases x with ⟨p, a, r⟩
  simp only [GateDyadicPrefixBridge.topMix, GateDyadicPrefixBridge.matrixMix,
    coefficients, GateDyadicUnitary.rotationCoefficients, clockWords,
    GateDyadicBoundary.central, GateDyadicBoundary.rotation,
    GateDyadicBoundary.joinPrivate]
  congr 1; ring

/-- Exact central action in the computational basis, including every
unused public word and every occupied private word. -/
theorem ideal_central (c σ : ℝ) (m : ℕ) (x : GateDyadicBoundary.State m) :
    GatePrefixCircuit.idealStep (Fin.last m) (coefficients c σ m)
      (amplitudes m x) = amplitudes m (GateDyadicBoundary.central c σ m x) := by
  unfold amplitudes
  rw [← GateDyadicPrefixBridge.amplitudes_topMix, topMix_clockWords]

/-- The constructed elementary central circuit has the required exact
action and returns all of its prefix flags to zero. -/
theorem circuit_correct (c σ : ℝ) (m : ℕ) (x : GateDyadicBoundary.State m) :
    GatePrefixCircuit.run (circuit c σ m)
      (GatePrefixCircuit.embed 0 (amplitudes m x)) =
        GatePrefixCircuit.embed 0
          (amplitudes m (GateDyadicBoundary.central c σ m x)) := by
  have h := LinearMap.congr_fun
    (GateZeroControls.circuit_correct m (coefficients c σ m)) (amplitudes m x)
  simp only [LinearMap.comp_apply] at h
  change GatePrefixCircuit.run (circuit c σ m)
    (GatePrefixCircuit.embed 0 (amplitudes m x)) =
      GatePrefixCircuit.embed 0
        (GatePrefixCircuit.idealStep (Fin.last m) (coefficients c σ m)
          (amplitudes m x)) at h
  rw [ideal_central] at h
  exact h

theorem circuit_valid (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) :
    ∀ g ∈ circuit c σ m, g.Valid :=
  GateZeroControls.circuit_valid m (coefficients c σ m)
    (GateDyadicUnitary.centralCoefficients_unitary c σ hunit m)

theorem circuit_length (c σ : ℝ) (m : ℕ) :
    (circuit c σ m).length = 3 * (m + 1) :=
  GateZeroControls.circuit_length m (coefficients c σ m)

theorem circuit_positiveCost (c σ : ℝ) (m : ℕ) :
    GatePrefixCircuit.positiveCost (circuit c σ m) = 7 * (m + 1) :=
  GateZeroControls.positive_control_gate_bound m (coefficients c σ m)

/-- The sum of the actual input-inverse, central, and output component
lengths. Additional sector controls for the two frames have not yet been
compiled here; hence this is deliberately a component count. -/
theorem boundary_component_count (c σ : ℝ) (m : ℕ) :
    (GatePrefixInverse.circuit (fun j : Fin m =>
      GateDyadicPrefixBridge.inputCoefficients
        (GateDyadicBoundary.centralCosine c j.val))).length +
    (circuit c σ m).length +
    (GatePrefixCircuit.circuit (fun j : Fin m =>
      GateDyadicPrefixBridge.outputCoefficients
        (GateDyadicBoundary.centralCosine c j.val))).length = 9 * m + 3 := by
  rw [GatePrefixInverse.circuit_length, circuit_length,
    GatePrefixCircuit.circuit_length]
  omega

end
end SparseHamiltonian.GateCentralBoundary
