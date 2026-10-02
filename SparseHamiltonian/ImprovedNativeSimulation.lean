import SparseHamiltonian.NativeCayleyActive

/-!
# Improved primitive sparse-query simulation for normalized inputs

This joins the actual native Cayley circuit to the sharp filter and the proved
public rescaling optimizer. The primitive active-layer premise is discharged.
The current theorem assumes row and column squared Euclidean norms at most one
and nonnegative time. General eta scaling and signed-time conversion are separate.
-/

namespace SparseHamiltonian.ImprovedNativeSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The chronological slot count is public and is not a query multiplier. -/
def slots (s γ τ ε : ℝ) : ℕ := TimeSchedule.steps (time s τ γ) (ε / 3)

/-- Keep the unreduced chronological budget in the workspace type so it agrees
exactly with the already constructed sharp simulation. -/
def degree (s γ τ ε : ℝ) : ℕ :=
  SharpFilterSchedule.degree (width s γ)
    ((slots s γ τ ε : ℝ) * TimeSchedule.stepSize (time s τ γ) (ε / 3) * moment γ)
    (ε / 3)

abbrev oracle (D : Data X n Z s) (γ τ ε : ℝ) :=
  NativeCayleyActive.oracle D (slots (s : ℝ) γ τ ε) (degree (s : ℝ) γ τ ε)

/-- The physical encoding contains only public schedule and slot data. -/
def embedding (D : Data X n Z s) (γ τ ε : ℝ) :=
  NativeCayleyActive.embedding D (slots (s : ℝ) γ τ ε) (degree (s : ℝ) γ τ ε)

def input (D : Data X n Z s) (γ τ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ]
      NativeCayleyActive.Physical n Z (slots (s : ℝ) γ τ ε)
        (degree (s : ℝ) γ τ ε) :=
  (embedding D γ τ ε).toContinuousLinearMap ∘L
    SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n)
      (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε

def output (D : Data X n Z s) (γ τ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ]
      NativeCayleyActive.Physical n Z (slots (s : ℝ) γ τ ε)
        (degree (s : ℝ) γ τ ε) :=
  (embedding D γ τ ε).toContinuousLinearMap ∘L
    FixedNativeCayleySimulation.output (n := n) (s := s) γ τ ε

/-- Concrete active layers meet the exact dependent workspace interface of the
improved query theorem. Their fixed physical encoding is common to every r. -/
theorem active_implementsOn (D : Data X n Z s) (γ τ ε : ℝ) (r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle D γ τ ε)
      (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
        (P := EuclideanSpace ℂ n) (FixedNativeCayleySimulation.action D x γ)
        (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε r)
      (embedding D γ τ ε).toContinuousLinearMap 54 :=
  NativeCayleyActive.implementsOn D γ (slots (s : ℝ) γ τ ε) (degree (s : ℝ) γ τ ε) r

/-- Uniform normalized-input simulation with an actual primitive oracle program.
No boundary moment, inverse, controlled-oracle, or active-layer implementation
is assumed. The count includes forward and inverse row, column and value calls.
Input and output are fixed isometries; aligning them is a separate free gate. -/
theorem exists_native_simulation (D : Data X n Z s)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := NativeCayleyActive.Physical n Z (slots (s : ℝ) γ τ ε)
            (degree (s : ℝ) γ τ ε)) (oracle D γ τ ε),
        (p.count : ℝ) ≤ 497664 * ImprovedPrecisionBudget.shape
          (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε) ∧
        (input D γ τ ε)† ∘L input D γ τ ε = 1 ∧
        (output D γ τ ε)† ∘L output D γ τ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ τ ε - output D γ τ ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  have hs : (1 : ℝ) ≤ s := by
    have hsNat : 1 ≤ s := D.slots_pos
    exact_mod_cast hsNat
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision (s : ℝ) τ ε hs hτ hε hεOne
  obtain ⟨p, hCount, hIn, hOut, hAction⟩ :=
    FixedNativeCayleyQuery.query_certificate
      (Label := Query)
      (K := NativeCayleyActive.Physical n Z (slots (s : ℝ) γ τ ε)
        (degree (s : ℝ) γ τ ε)) D hH hrow hcol γ τ ε
      hγ hγOne hτ hε hεOne hBudget (oracle D γ τ ε)
      (NativeCayleyActive.oracle_unitary D (slots (s : ℝ) γ τ ε) (degree (s : ℝ) γ τ ε))
      (embedding D γ τ ε).toContinuousLinearMap (embedding D γ τ ε).adjoint_comp_self
      54 (fun r _ => active_implementsOn D γ τ ε r)
  refine ⟨γ, hγ, hγOne, hWidth, p, ?_, hIn, hOut, hAction⟩
  calc
    (p.count : ℝ) ≤ 9216 * (54 : ℝ) * ImprovedPrecisionBudget.shape
        (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε) := hCount
    _ = 497664 * ImprovedPrecisionBudget.shape
        (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε) := by ring

end
end SparseHamiltonian.ImprovedNativeSimulation
