import SparseODE.CoherentQuerySchedule

namespace SparseHamiltonian.ODECoherentCayley

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 12000
set_option maxHeartbeats 2500000

variable {ι X n Z : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Erasing every free gate in the actual native program leaves exactly the
same syntax at all public nodes and all public Cayley angles. Structural
lemmas check each locator, value, masking and flattening compiler separately. -/
theorem program_shape (D : Data X n Z s) (k γ ρ : ℝ) :
    CommonQueryShape.erase (ODENativeCayley.program D k γ ρ) =
      CommonQueryShape.erase (ODENativeCayley.program D 0 0 ρ) := by
  exact ODENativeCircuitShape.cayley_shape D k γ ρ

/-- The finite public branch register does not control the native query label. -/
def schedule (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) :
    CoherentQuerySchedule.Schedule ι Query
      (EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) :=
  CommonQueryShape.schedule
    (CommonQueryShape.erase (ODENativeCayley.program D 0 0 ρ))
    (fun i => ODENativeCayley.program D (k i) (γ i) ρ)
    (fun i => program_shape D (k i) (γ i) ρ)

omit [Fintype ι] in
theorem schedule_branch (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (i : ι) :
    (schedule D k γ ρ).branch (ODENativeCayley.oracle D) i =
      ODENativeCayley.program D (k i) (γ i) ρ :=
  CommonQueryShape.branch_schedule _ _ _ i

omit [Fintype ι] in
@[simp] theorem schedule_count (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) :
    (schedule D k γ ρ).count = 24 := by
  rw [schedule, CommonQueryShape.schedule_count, CommonQueryShape.erase_count,
    ODENativeCayley.program_count]

omit [Fintype ι] in
@[simp] theorem schedule_cost (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (w : Query → ℕ) :
    (schedule D k γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [schedule, CommonQueryShape.schedule_cost, CommonQueryShape.erase_cost,
    ODENativeCayley.program_cost]

/-- Every native query has the entire public index register as a spectator. -/
abbrev oracle (D : Data X n Z s) :=
  CoherentQuerySchedule.oracle (ι := ι) (ODENativeCayley.oracle D)

/-- One actual program, coherently realizing all public Cayley parameters. -/
def program (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) :
    MultiOracleCircuit.Program (oracle (ι := ι) D) :=
  (schedule D k γ ρ).compile (ODENativeCayley.oracle D)

@[simp] theorem program_count (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) :
    (program D k γ ρ).count = 24 := by
  rw [program, CoherentQuerySchedule.Schedule.compile_count, schedule_count]

@[simp] theorem program_cost (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (w : Query → ℕ) :
    (program D k γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [program, CoherentQuerySchedule.Schedule.compile_cost, schedule_cost]

/-- Coherent selection has the exact diagonal semantics on arbitrary inputs. -/
theorem program_eval (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x = WeightedClock.diagonal
      (fun i => (ODENativeCayley.program D (k i) (γ i) ρ).eval x) := by
  rw [program, CoherentQuerySchedule.Schedule.compile_eval]
  simp only [schedule_branch]

theorem program_unitary (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (x : X) :
    IsUnitary ((program D k γ ρ).eval x) :=
  (program D k γ ρ).eval_unitary
    (CoherentQuerySchedule.oracle_unitary (ODENativeCayley.oracle D)
      (ODENativeCayley.oracle_unitary D)) x

/-- One fixed clean encoding is shared by all parameters and all inputs. -/
def clean (D : Data X n Z s) :
    PiLp 2 (fun _ : ι => ODETaggedMoments.PrivateSpace n) →L[ℂ]
      PiLp 2 (fun _ : ι => EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) :=
  CoherentQuerySchedule.rectangular
    (fun _ : ι => (ODENativeCayley.clean D).toContinuousLinearMap)

theorem clean_isometry (D : Data X n Z s) :
    (clean (ι := ι) D)† ∘L clean D = 1 :=
  CoherentQuerySchedule.rectangular_isometry _
    (fun _ : ι => ODENativeCayley.clean_isometry D)

/-- Exact clean action on a superposition of LCHS nodes and source durations;
no cardinality factor is present in either the circuit or its query count. -/
theorem program_intertwines (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x ∘L clean D = clean D ∘L
      WeightedClock.diagonal (fun i => ODEFixedTaggedMoments.action D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (γ i)) := by
  rw [program_eval]
  unfold clean
  exact CoherentQuerySchedule.diagonal_rectangular_intertwines
    (fun i => (ODENativeCayley.program D (k i) (γ i) ρ).eval x)
    (fun _ : ι => (ODENativeCayley.clean D).toContinuousLinearMap)
    (fun i => ODEFixedTaggedMoments.action D x
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (γ i))
    (fun i => ODENativeCayley.program_intertwines D (k i) (γ i) ρ x)

end
end SparseHamiltonian.ODECoherentCayley
