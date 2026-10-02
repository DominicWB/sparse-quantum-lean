import SparseODE.ODECoherentCayley

/-!
# A common native schedule for the active chronological layers

With the slot count, filter degree and reuse index fixed, the actual native
active circuits also have one common query syntax at every LCHS node and
duration. This establishes SELECT for the active layers at cost seventy-two.
The complete sharp-transducer sequence is a separate assembly obligation.
-/

namespace SparseHamiltonian.ODECoherentActive

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 16000
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Each branch has the same active-clock logical workspace. -/
abbrev Logical (n : Type*) [Fintype n] (T d : ℕ) :=
  PiLp 2 (SmoothingLCU.BranchSpace (P := EuclideanSpace ℂ n)
    (V := ChronologicalResolvent.BlockOperator.H T (ODETaggedMoments.PrivateSpace n)) d)

/-- Parameters affect gates, not native query labels or inverse directions. -/
theorem program_shape (D : Data X n Z s) (k γ ρ : ℝ) (T d r : ℕ) :
    CommonQueryShape.erase (ODENativeActive.program D k γ ρ T d r) =
      CommonQueryShape.erase (ODENativeActive.program D 0 0 ρ T d r) := by
  exact ODENativeCircuitShape.active_shape D k γ ρ T d r

def schedule (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (T d r : ℕ) :
    CoherentQuerySchedule.Schedule ι Query (ODENativeActive.Physical n Z T d) :=
  CommonQueryShape.schedule
    (CommonQueryShape.erase (ODENativeActive.program D 0 0 ρ T d r))
    (fun i => ODENativeActive.program D (k i) (γ i) ρ T d r)
    (fun i => program_shape D (k i) (γ i) ρ T d r)

omit [Fintype ι] in
theorem schedule_branch (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (T d r : ℕ) (i : ι) :
    (schedule D k γ ρ T d r).branch (ODENativeActive.oracle D T d) i =
      ODENativeActive.program D (k i) (γ i) ρ T d r :=
  CommonQueryShape.branch_schedule _ _ _ i

/-- The public LCHS/source register is a spectator of every native query. -/
abbrev oracle (D : Data X n Z s) (T d : ℕ) :=
  CoherentQuerySchedule.oracle (ι := ι) (ODENativeActive.oracle D T d)

def program (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle (ι := ι) D T d) :=
  (schedule D k γ ρ T d r).compile (ODENativeActive.oracle D T d)

/-- Coherent node and duration selection introduces no query multiplier. -/
@[simp] theorem program_count (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (T d r : ℕ) : (program D k γ ρ T d r).count = 72 := by
  rw [program, CoherentQuerySchedule.Schedule.compile_count, schedule,
    CommonQueryShape.schedule_count, CommonQueryShape.erase_count,
    ODENativeActive.program_count]

theorem program_cost (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (T d r : ℕ) (w : Query → ℕ) :
    (program D k γ ρ T d r).cost w =
      18 * w .rowLocation + 18 * w .columnLocation + 36 * w .value := by
  rw [program, CoherentQuerySchedule.Schedule.compile_cost, schedule,
    CommonQueryShape.schedule_cost, CommonQueryShape.erase_cost,
    ODENativeActive.program_cost]

theorem program_eval (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (T d r : ℕ) (x : X) :
    (program D k γ ρ T d r).eval x = WeightedClock.diagonal
      (fun i => (ODENativeActive.program D (k i) (γ i) ρ T d r).eval x) := by
  rw [program, CoherentQuerySchedule.Schedule.compile_eval]
  simp only [schedule_branch]

theorem program_unitary (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (T d r : ℕ) (x : X) : IsUnitary ((program D k γ ρ T d r).eval x) :=
  (program D k γ ρ T d r).eval_unitary
    (CoherentQuerySchedule.oracle_unitary (ODENativeActive.oracle D T d)
      (ODENativeActive.oracle_unitary D T d)) x

/-- One fixed clean embedding works for every node, angle and reuse layer. -/
def embedding (D : Data X n Z s) (T d : ℕ) :
    PiLp 2 (fun _ : ι => Logical n T d) →L[ℂ]
      PiLp 2 (fun _ : ι => ODENativeActive.Physical n Z T d) :=
  CoherentQuerySchedule.rectangular
    (fun _ : ι => (ODENativeActive.embedding D T d).toContinuousLinearMap)

theorem embedding_isometry (D : Data X n Z s) (T d : ℕ) :
    (embedding (ι := ι) D T d)† ∘L embedding D T d = 1 :=
  CoherentQuerySchedule.rectangular_isometry _
    (fun _ : ι => (ODENativeActive.embedding D T d).adjoint_comp_self)

/-- Exact action of the shared active-layer circuit on arbitrary coherent
public/private inputs, with all native ancillas restored on every branch. -/
theorem program_intertwines (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ)
    (T d r : ℕ) (x : X) :
    (program D k γ ρ T d r).eval x ∘L embedding D T d =
      embedding D T d ∘L WeightedClock.diagonal
        (fun i => ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
          (ODEFixedTaggedMoments.action D x
            (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (γ i)) T d r) := by
  rw [program_eval]
  unfold embedding
  exact CoherentQuerySchedule.diagonal_rectangular_intertwines
    (fun i => (ODENativeActive.program D (k i) (γ i) ρ T d r).eval x)
    (fun _ : ι => (ODENativeActive.embedding D T d).toContinuousLinearMap)
    (fun i => ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
      (ODEFixedTaggedMoments.action D x
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (γ i)) T d r)
    (fun i => ODENativeActive.program_intertwines D (k i) (γ i) ρ T d r x)

/-- A counted common active implementation, using ordinary native queries
with a spectator branch register and without postulating controlled access. -/
theorem implementsOn (D : Data X n Z s) (k γ : ι → ℝ) (ρ : ℝ) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle (ι := ι) D T d)
      (fun x => WeightedClock.diagonal
        (fun i => ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
          (ODEFixedTaggedMoments.action D x
            (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (γ i)) T d r))
      (embedding D T d) 72 :=
  ⟨program D k γ ρ T d r, program_intertwines D k γ ρ T d r,
    (program_count D k γ ρ T d r).le⟩

end
end SparseHamiltonian.ODECoherentActive
