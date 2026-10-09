import GateEfficientHamiltonian.GateDyadicUnitary
/-!
# Exact all-zero controls from the clean prefix circuit

A rotation on the final bit is enabled precisely when every lower bit is
zero. Its many-bit condition is compiled into the same one- and two-control
Boolean gates as the dyadic frames. In particular, the central public/private
rotation need not be charged as a free multi-controlled operation.
-/

namespace SparseHamiltonian.GateZeroControls

noncomputable section
open GatePrefixCircuit

def identityCoefficients : Coefficients := fun b c => if b = c then 1 else 0

theorem identityCoefficients_unitary : identityCoefficients.IsUnitary := by
  have h : identityCoefficients = (1 : Matrix Bool Bool ℂ) := rfl
  simp [Coefficients.IsUnitary, h]

theorem idealStep_identity {w : ℕ} (j : Fin w) :
    idealStep j identityCoefficients = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x c
  simp only [idealStep, Finsupp.linearCombination_single, LinearMap.id_apply]
  have h : idealBasis j identityCoefficients x = Finsupp.single x 1 := by
    unfold idealBasis
    split
    · simp [identityCoefficients]
    · rfl
  rw [h]
  simp

/-- Identity matrices in the lower levels do not change any slot amplitude. -/
theorem ideal_identity {w : ℕ} (a : Fin w → Coefficients)
    (n : ℕ) (hn : n ≤ w)
    (ha : ∀ j : Fin w, j.val < n → a j = identityCoefficients) :
    ideal a n hn = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [ideal]
      rw [ih (by omega) (fun j hj => ha j (by omega))]
      rw [ha ⟨n, by omega⟩ (by simp), idealStep_identity]
      rfl

/-- There are `w` controls and one final target bit. -/
def coefficients (w : ℕ) (a : Coefficients) : Fin (w + 1) → Coefficients :=
  fun j => if j.val = w then a else identityCoefficients

def circuit (w : ℕ) (a : Coefficients) : List (Gate (w + 1)) :=
  GatePrefixCircuit.circuit (coefficients w a)

/-- The complete ideal sequence is just the intended all-zero-controlled
target operation; no product of `w` nontrivial target operations remains. -/
theorem ideal_eq (w : ℕ) (a : Coefficients) :
    ideal (coefficients w a) (w + 1) le_rfl =
      idealStep (⟨w, Nat.lt_succ_self w⟩ : Fin (w + 1)) a := by
  rw [ideal]
  have hLower : ideal (coefficients w a) w (Nat.le_succ w) = LinearMap.id := by
    apply ideal_identity
    intro j hj
    simp [coefficients, show j.val ≠ w by omega]
  rw [hLower]
  simp [coefficients]

/-- Exact clean-output circuit identity, valid on all superpositions of the
control and target bits. All computed prefix flags are returned to zero. -/
theorem circuit_correct (w : ℕ) (a : Coefficients) :
    (run (circuit w a)).comp (embed 0) =
      (embed 0).comp (idealStep (⟨w, Nat.lt_succ_self w⟩ : Fin (w + 1)) a) := by
  have h := GatePrefixCircuit.circuit_correct (coefficients w a)
  rw [ideal_eq] at h
  exact h

/-- A concrete linear bound in the number of controls, including the clean
flag computation, target rotation, and all uncomputation. -/
theorem circuit_length (w : ℕ) (a : Coefficients) :
    (circuit w a).length = 3 * (w + 1) :=
  GatePrefixCircuit.circuit_length (coefficients w a)

theorem circuit_valid (w : ℕ) (a : Coefficients) (ha : a.IsUnitary) :
    ∀ g ∈ circuit w a, g.Valid := by
  apply GatePrefixCircuit.circuit_valid
  intro j
  unfold coefficients
  split
  · exact ha
  · exact identityCoefficients_unitary

theorem positive_control_gate_bound (w : ℕ) (a : Coefficients) :
    positiveCost (circuit w a) = 7 * (w + 1) :=
  GatePrefixCircuit.positive_control_gate_bound (coefficients w a)

end
end SparseHamiltonian.GateZeroControls
