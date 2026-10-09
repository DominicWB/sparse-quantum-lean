import GateEfficientHamiltonian.GateCentralBoundary
/-!
# Exact external control by controlling the decoded middle operation

All oracle calls below act identically on both values of an external bit.
Only the public decoded middle operation is controlled. The compute and
uncompute cancel exactly on the disabled branch. This is the circuit pattern
used by the locator/value implementation of a private Cayley operation; no
controlled version of an opaque primitive is assumed.
-/

namespace SparseHamiltonian.GatePrivateControl

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {K X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Space (K : Type*) := PiLp 2 (fun _ : Bool => K)

/-- An unknown operation with a spectator bit, not a controlled query. -/
def spectator (U : K →L[ℂ] K) : Space K →L[ℂ] Space K :=
  WeightedClock.diagonal (fun _ : Bool => U)

omit [CompleteSpace K] in
@[simp] theorem spectator_apply (U : K →L[ℂ] K) (v : Space K) (b : Bool) :
    spectator U v b = U (v b) := rfl

theorem spectator_adjoint (U : K →L[ℂ] K) :
    (spectator U)† = spectator (U†) :=
  WeightedClock.diagonal_adjoint _

/-- The external enable controls only a known operation. -/
def middle (R : K →L[ℂ] K) : Space K →L[ℂ] Space K :=
  WeightedClock.diagonal (fun b : Bool => if b then R else 1)

omit [CompleteSpace K] in
@[simp] theorem middle_apply (R : K →L[ℂ] K) (v : Space K) (b : Bool) :
    middle R v b = if b then R (v b) else v b := by
  cases b <;> rfl

theorem middle_unitary (R : K →L[ℂ] K) (hR : IsUnitary R) :
    IsUnitary (middle R) := by
  apply NativeMaskedOracle.diagonal_unitary
  intro b
  cases b
  · exact isUnitary_one
  · exact hR

def oracle (O : L → X → K →L[ℂ] K) (l : L) (x : X) :
    Space K →L[ℂ] Space K := spectator (O l x)

theorem oracle_unitary (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (l : L) (x : X) :
    IsUnitary (oracle O l x) :=
  NativeMaskedOracle.diagonal_unitary _ (fun _ => hO l x)

/-- The locator/locator/value compute sequence uses fixed oracle labels.
The labels need not be distinct; weighted costs remain literal counts. -/
def compute (O : L → X → K →L[ℂ] K) (row col value : L) :
    MultiOracleCircuit.Program (oracle O) :=
  .seq (.query value) (.seq (.query col) (.query row))

def computed (O : L → X → K →L[ℂ] K) (row col value : L) (x : X) :
    K →L[ℂ] K := O value x * (O col x * O row x)

theorem compute_eval (O : L → X → K →L[ℂ] K) (row col value : L) (x : X) :
    (compute O row col value).eval x = spectator (computed O row col value x) := by
  ext v b
  rfl

theorem computed_unitary (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (row col value : L) (x : X) :
    IsUnitary (computed O row col value x) :=
  (hO value x).mul ((hO col x).mul (hO row x))

/-- Execute compute, one controlled known middle operation, and the actual
inverse compute circuit. Oracle calls never consult the enable bit. -/
def program (O : L → X → K →L[ℂ] K) (row col value : L)
    (R : K →L[ℂ] K) (hR : IsUnitary R) :
    MultiOracleCircuit.Program (oracle O) :=
  .seq (compute O row col value).adjoint
    (.seq (.fixed (middle R) (middle_unitary R hR)) (compute O row col value))

/-- Exact native-query count, independent of the control and of all clock
and filter register sizes. Forward and inverse calls both count. -/
theorem program_cost (O : L → X → K →L[ℂ] K) (row col value : L)
    (R : K →L[ℂ] K) (hR : IsUnitary R) (w : L → ℕ) :
    (program O row col value R hR).cost w =
      2 * w row + 2 * w col + 2 * w value := by
  simp only [program, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_adjoint,
    MultiOracleCircuit.Program.cost_fixed, compute,
    MultiOracleCircuit.Program.cost_query]
  omega

theorem program_count (O : L → X → K →L[ℂ] K) (row col value : L)
    (R : K →L[ℂ] K) (hR : IsUnitary R) :
    (program O row col value R hR).count = 6 := by
  have h := program_cost O row col value R hR (fun _ => 1)
  simpa only [MultiOracleCircuit.Program.cost_const, Nat.mul_one] using h

/-- Exact action on a coherent enable bit and arbitrary workspace amplitudes.
No involution property is required of the private operation. -/
theorem program_apply (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (row col value : L)
    (R : K →L[ℂ] K) (hR : IsUnitary R) (x : X) (v : Space K) (b : Bool) :
    (program O row col value R hR).eval x v b =
      if b then
        ((computed O row col value x)†)
          (R (computed O row col value x (v b)))
      else v b := by
  simp only [program, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_adjoint,
    MultiOracleCircuit.Program.eval_fixed, compute_eval, star_eq_adjoint,
    spectator_adjoint, mul_apply_eq_comp, spectator_apply, middle_apply]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact congrArg (fun A : K →L[ℂ] K => A (v false))
      (computed_unitary O hO row col value x).1
  · rfl

theorem program_unitary (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (row col value : L)
    (R : K →L[ℂ] K) (hR : IsUnitary R) (x : X) :
    IsUnitary ((program O row col value R hR).eval x) :=
  (program O row col value R hR).eval_unitary (oracle_unitary O hO) x

/-- The inverse used in subsequent amplification is the adjoint of this
same circuit and has exactly the same primitive cost. -/
theorem adjoint_cost (O : L → X → K →L[ℂ] K) (row col value : L)
    (R : K →L[ℂ] K) (hR : IsUnitary R) (w : L → ℕ) :
    (program O row col value R hR).adjoint.cost w =
      2 * w row + 2 * w col + 2 * w value := by
  rw [MultiOracleCircuit.Program.cost_adjoint, program_cost]

end
end SparseHamiltonian.GatePrivateControl
