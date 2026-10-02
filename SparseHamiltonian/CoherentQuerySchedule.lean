import SparseHamiltonian.NativeZeroSimulation

/-!
# Coherent control of a common sparse-query schedule

A schedule has branch-dependent fixed gates and branch-independent query
labels and directions. Compiling it on a finite Hilbert direct sum retains
exactly the query count of one branch. The lifted oracle merely leaves the
branch register untouched: no SELECT among different oracle labels is assumed.

This is a compiler theorem, not a claim that the parameter-dependent
Hamiltonian simulators have already been placed on one such schedule.
-/

namespace SparseHamiltonian.CoherentQuerySchedule

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

variable {ι L X K : Type*} [Fintype ι]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Gates may depend on the known coherent parameter; oracle calls may not. -/
inductive Schedule (ι L K : Type*) [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] where
  | fixed (U : ι → K →L[ℂ] K) (unitary : ∀ i, IsUnitary (U i))
  | query (label : L)
  | queryAdjoint (label : L)
  | seq (p q : Schedule ι L K)

/-- The branch register is a spectator of each original query. -/
def oracle (O : L → X → K →L[ℂ] K) (l : L) (x : X) :
    PiLp 2 (fun _ : ι => K) →L[ℂ] PiLp 2 (fun _ : ι => K) :=
  WeightedClock.diagonal (fun _ => O l x)

/-- A finite diagonal family of fixed unitary gates is unitary. -/
theorem diagonal_unitary (U : ι → K →L[ℂ] K) (hU : ∀ i, IsUnitary (U i)) :
    IsUnitary (WeightedClock.diagonal U) := by
  change (WeightedClock.diagonal U)† ∘L WeightedClock.diagonal U = 1 ∧
    WeightedClock.diagonal U ∘L (WeightedClock.diagonal U)† = 1
  constructor
  · exact WeightedClock.diagonal_isometry U (fun i => (hU i).1)
  · rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    convert (WeightedClock.diagonal_one (V := fun _ : ι => K)) using 1
    congr 1
    funext i
    exact (hU i).2

/-- Adding a spectator preserves unitarity of the original oracle. -/
theorem oracle_unitary (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (l : L) (x : X) :
    IsUnitary (oracle (ι := ι) O l x) :=
  diagonal_unitary _ (fun _ => hO l x)

namespace Schedule

/-- Extract the actual program on one branch. -/
def branch (O : L → X → K →L[ℂ] K) (i : ι) :
    Schedule ι L K → MultiOracleCircuit.Program O
  | .fixed U hU => .fixed (U i) (hU i)
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (p.branch O i) (q.branch O i)

/-- Compile one program acting coherently on all branches. -/
def compile (O : L → X → K →L[ℂ] K) : Schedule ι L K →
    MultiOracleCircuit.Program (oracle (ι := ι) O)
  | .fixed U hU => .fixed (WeightedClock.diagonal U) (diagonal_unitary U hU)
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (p.compile O) (q.compile O)

/-- Query count of the shared syntax, independent of the branch cardinality. -/
def count : Schedule ι L K → ℕ
  | .fixed _ _ => 0
  | .query _ => 1
  | .queryAdjoint _ => 1
  | .seq p q => p.count + q.count

/-- Weighted costs retain the identities of the original oracle labels. -/
def cost (w : L → ℕ) : Schedule ι L K → ℕ
  | .fixed _ _ => 0
  | .query l => w l
  | .queryAdjoint l => w l
  | .seq p q => p.cost w + q.cost w

omit [Fintype ι] in
@[simp] theorem branch_count (O : L → X → K →L[ℂ] K)
    (p : Schedule ι L K) (i : ι) : (p.branch O i).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [branch, MultiOracleCircuit.Program.count_seq, count, hp, hq]

@[simp] theorem compile_count (O : L → X → K →L[ℂ] K)
    (p : Schedule ι L K) : (p.compile O).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [compile, MultiOracleCircuit.Program.count_seq, count, hp, hq]

omit [Fintype ι] in
@[simp] theorem branch_cost (O : L → X → K →L[ℂ] K)
    (p : Schedule ι L K) (i : ι) (w : L → ℕ) :
    (p.branch O i).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [branch, MultiOracleCircuit.Program.cost_seq, cost, hp, hq]

@[simp] theorem compile_cost (O : L → X → K →L[ℂ] K)
    (p : Schedule ι L K) (w : L → ℕ) : (p.compile O).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [compile, MultiOracleCircuit.Program.cost_seq, cost, hp, hq]

/-- The compiled program has the exact diagonal semantics, including inverses. -/
theorem compile_eval (O : L → X → K →L[ℂ] K)
    (p : Schedule ι L K) (x : X) :
    (p.compile O).eval x = WeightedClock.diagonal (fun i => (p.branch O i).eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l =>
    exact WeightedClock.diagonal_adjoint _
  | seq p q hp hq =>
    simp only [compile, branch, MultiOracleCircuit.Program.eval_seq, hp, hq]
    exact WeightedClock.diagonal_comp _ _

/-- An explicit implementation certificate with exactly the single-branch count. -/
theorem implements (O : L → X → K →L[ℂ] K) (p : Schedule ι L K) :
    MultiOracleCircuit.Implements (oracle (ι := ι) O)
      (fun x => WeightedClock.diagonal (fun i => (p.branch O i).eval x)) p.count :=
  ⟨p.compile O, p.compile_eval O, by rw [compile_count]⟩

end Schedule

section Rectangular
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- Rectangular direct sum, used for full input and output isometries. -/
def rectangular (A : ι → P →L[ℂ] K) :
    PiLp 2 (fun _ : ι => P) →L[ℂ] PiLp 2 (fun _ : ι => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => K)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i => (A i).comp (ContinuousLinearMap.proj i))).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => P)).toContinuousLinearMap)

omit [Fintype ι] [CompleteSpace K] in
@[simp] theorem rectangular_apply (A : ι → P →L[ℂ] K)
    (v : PiLp 2 (fun _ : ι => P)) (i : ι) : rectangular A v i = A i (v i) := rfl

omit [CompleteSpace K] in
/-- A uniform branch error is a uniform coherent error, with no sum over nodes. -/
theorem rectangular_norm_le (A : ι → P →L[ℂ] K) (δ : ℝ)
    (hδ : 0 ≤ δ) (hA : ∀ i, ‖A i‖ ≤ δ) : ‖rectangular A‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro v
  have hsq : ‖rectangular A v‖ ^ 2 ≤ (δ * ‖v‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      ∑ i, ‖rectangular A v i‖ ^ 2 ≤ ∑ i, (δ * ‖v i‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        exact ((A i).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hA i) (norm_nonneg _))
      _ = (δ * ‖v‖) ^ 2 := by
        simp_rw [mul_pow]
        rw [← Finset.mul_sum, ← PiLp.norm_sq_eq_of_L2]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp hsq

/-- Full output error, allowing distinct fixed encodings on every branch. -/
theorem compile_output_error (O : L → X → K →L[ℂ] K)
    (p : Schedule ι L K) (E F : ι → P →L[ℂ] K) (U : ι → P →L[ℂ] P)
    (x : X) (δ : ℝ) (hδ : 0 ≤ δ)
    (hError : ∀ i, ‖(p.branch O i).eval x ∘L E i - F i ∘L U i‖ ≤ δ) :
    ‖(p.compile O).eval x ∘L rectangular E -
      rectangular F ∘L WeightedClock.diagonal U‖ ≤ δ := by
  have hEq : (p.compile O).eval x ∘L rectangular E -
      rectangular F ∘L WeightedClock.diagonal U =
      rectangular (fun i => (p.branch O i).eval x ∘L E i - F i ∘L U i) := by
    rw [Schedule.compile_eval]
    ext v i
    rfl
  rw [hEq]
  exact rectangular_norm_le _ δ hδ hError

variable [CompleteSpace P]

/-- Fixed branchwise isometries give a genuine isometry on superpositions. -/
theorem rectangular_isometry (E : ι → P →L[ℂ] K)
    (hE : ∀ i, (E i)† ∘L E i = 1) :
    (rectangular E)† ∘L rectangular E = 1 := by
  apply (rectangular E).norm_map_iff_adjoint_comp_self.mp
  intro v
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [rectangular_apply, (E i).norm_map_iff_adjoint_comp_self.mpr (hE i)]

end Rectangular

end
end SparseHamiltonian.CoherentQuerySchedule
