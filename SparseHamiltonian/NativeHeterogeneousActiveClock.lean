import SparseHamiltonian.NativeMultiActiveClock

/-!
# Heterogeneous native program clocks with one common active implementation

The disjoint union retains every program's own count-plus-two clock length.
All chronological and reuse copies share a single physical native oracle family
and one clean encoding. Each active step costs six calls per primitive label,
independently of the number of branches and their program lengths.
-/
namespace SparseHamiltonian.NativeHeterogeneousActiveClock
noncomputable section
open ContinuousLinearMap OracleCircuit NativeMaskedOracle
open ReuseLayerFactorization
open scoped InnerProduct BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

variable {I B X L : Type*} [Fintype I] [Fintype B] [DecidableEq B]
  [Fintype L] [DecidableEq L]
variable (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)

/-- The genuine unequal clock slots; no padding to the largest query count. -/
abbrev Slot (ps : I → MultiOracleCircuit.Program F) :=
  Sigma (fun i => Fin ((ps i).count + 1 + 1))

/-- The direct sum of each program's actual distributed clock. -/
abbrev Space (ps : I → MultiOracleCircuit.Program F) :=
  PiLp 2 (fun i => ClockOperators.H ((ps i).count + 1) (EuclideanSpace ℂ B))

/-- A fixed regrouping, independent of the unknown oracle input. -/
def flatten (ps : I → MultiOracleCircuit.Program F) :
    Space F ps ≃ₗᵢ[ℂ] Logical (Slot F ps) B :=
  (LinearIsometryEquiv.piLpCurry ℂ 2
    (fun i (_ : Fin ((ps i).count + 1 + 1)) => EuclideanSpace ℂ B)).symm

/-- A cell carries one explicit fixed primitive label or no query. -/
def choice (ps : I → MultiOracleCircuit.Program F) (s : Slot F ps) : Option (L × Bool) :=
  MultiQueryClock.clockChoice (ps s.1) s.2

/-- All program routing gates and phased clock shifts are query-free fixed data. -/
def fixedGate (ps : I → MultiOracleCircuit.Program F) : Space F ps →L[ℂ] Space F ps :=
  WeightedClock.diagonal (fun i => MultiQueryClock.fixedClockGate (ps i))

omit [DecidableEq B] [Fintype L] [DecidableEq L] in
theorem fixedGate_unitary (ps : I → MultiOracleCircuit.Program F) :
    IsUnitary (fixedGate F ps) :=
  HeterogeneousLookupClock.diagonal_unitary _
    (fun i => MultiQueryClock.fixedClockGate_unitary (ps i))

/-- The fixed routing in the common disjoint-slot register. -/
def flatFixed (ps : I → MultiOracleCircuit.Program F) :
    Logical (Slot F ps) B →L[ℂ] Logical (Slot F ps) B :=
  (flatten F ps).conjStarAlgEquiv (fixedGate F ps)

omit [DecidableEq B] [Fintype L] [DecidableEq L] in
theorem flatFixed_unitary (ps : I → MultiOracleCircuit.Program F) :
    IsUnitary (flatFixed F ps) := (fixedGate_unitary F ps).transport (flatten F ps)

/-- The actual family of distributed clocks, with its involution promise. -/
def familyClock (ps : I → MultiOracleCircuit.Program F) (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v) (x : X) :
    Space F ps →L[ℂ] Space F ps :=
  WeightedClock.diagonal (fun i => MultiQueryClock.programClock (ps i) hF (hInv i) x)

omit [DecidableEq B] [Fintype L] [DecidableEq L] in
theorem familyClock_unitary (ps : I → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v) (x : X) :
    IsUnitary (familyClock F ps hF hInv x) :=
  HeterogeneousLookupClock.diagonal_unitary _
    (fun i => MultiQueryClock.programClock_unitary (ps i) hF (hInv i) x)

/-- The family clock in the common flattened coordinate space. -/
def flatFamilyClock (ps : I → MultiOracleCircuit.Program F) (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v) (x : X) :
    Logical (Slot F ps) B →L[ℂ] Logical (Slot F ps) B :=
  (flatten F ps).conjStarAlgEquiv (familyClock F ps hF hInv x)

omit [DecidableEq B] [Fintype L] [DecidableEq L] in
/-- Heterogeneous clocks factor into a fixed gate and exactly the native cell choices. -/
theorem flatFamilyClock_factor (ps : I → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v) (x : X) :
    flatFamilyClock F ps hF hInv x = flatFixed F ps ∘L
      WeightedClock.diagonal (fun c => MultiQueryNormalForm.optionalQuery F (choice F ps c) x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨i,j⟩
  have h := congrArg (fun U : ClockOperators.H ((ps i).count + 1) (EuclideanSpace ℂ B) →L[ℂ]
      ClockOperators.H ((ps i).count + 1) (EuclideanSpace ℂ B) =>
      U ((flatten F ps).symm v i) j)
    (MultiQueryClock.programClock_factor (ps i) hF (hInv i) x)
  exact h

/-- Every active step keeps exactly the original primitive oracle labels. -/
abbrev oracle (ps : I → MultiOracleCircuit.Program F) (T d : ℕ) :=
  NativeMultiActiveClock.oracle (C := Slot F ps) F T d

/-- A literal physical program for every chronological/reuse step. -/
def program (ps : I → MultiOracleCircuit.Program F) (a : B) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle F ps T d) :=
  NativeMultiActiveClock.program F a (flatFixed F ps) (flatFixed_unitary F ps)
    (choice F ps) T d r

@[simp] theorem program_count (ps : I → MultiOracleCircuit.Program F) (a : B) (T d r : ℕ) :
    (program F ps a T d r).count = 6 * Fintype.card L := by simp [program]

@[simp] theorem program_cost (ps : I → MultiOracleCircuit.Program F) (a : B)
    (T d r : ℕ) (w : L → ℕ) :
    (program F ps a T d r).cost w = 6 * ∑ l, w l := by simp [program]

theorem program_unitary (ps : I → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (T d r : ℕ) (x : X) :
    IsUnitary ((program F ps a T d r).eval x) :=
  (program F ps a T d r).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y) x

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- One clean encoding serves all branch lengths and every active-step index. -/
abbrev input (ps : I → MultiOracleCircuit.Program F) (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (a : B) (T d : ℕ) :=
  NativeMultiActiveClock.publicInput (C := Slot F ps) e a T d

omit [CompleteSpace P] in
/-- Actual full-output active-clock semantics, including arbitrary public systems. -/
theorem program_intertwines (ps : I → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v)
    (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (T d r : ℕ) (x : X) :
    (program F ps a T d r).eval x ∘L (input F ps e a T d).toContinuousLinearMap =
      (input F ps e a T d).toContinuousLinearMap ∘L
        activeClock (P := P) (flatFamilyClock F ps hF hInv x) T d r := by
  rw [flatFamilyClock_factor]
  exact NativeMultiActiveClock.program_public_intertwines F hF a image hvalid
    (flatFixed F ps) (flatFixed_unitary F ps) (choice F ps) e T d r x

/-- All implementation premises are discharged simultaneously over one common oracle. -/
theorem all_active_certificate (ps : I → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x))
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v)
    (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (T d : ℕ) :
    (input F ps e a T d).toContinuousLinearMap† ∘L
      (input F ps e a T d).toContinuousLinearMap = 1 ∧
    (∀ l x, IsUnitary (oracle F ps T d l x)) ∧
    ∀ r, (program F ps a T d r).count = 6 * Fintype.card L ∧
      ∀ x, (program F ps a T d r).eval x ∘L (input F ps e a T d).toContinuousLinearMap =
        (input F ps e a T d).toContinuousLinearMap ∘L
          activeClock (P := P) (flatFamilyClock F ps hF hInv x) T d r :=
  ⟨(input F ps e a T d).adjoint_comp_self,
    fun l x => NativeMaskedOracle.oracle_unitary (F l) (hF l) x,
    fun r => ⟨program_count F ps a T d r,
      program_intertwines F ps hF hInv a image hvalid e T d r⟩⟩

end
end SparseHamiltonian.NativeHeterogeneousActiveClock
