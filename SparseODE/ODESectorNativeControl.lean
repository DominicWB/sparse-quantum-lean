import SparseODE.ODEPrimitiveControlBudget

/-!
# Source and matrix sector programs using ordinary native queries

The source interface already supplies its controls.  Matrix sector control is
implemented by the phase-one basis-image construction, with three ordinary
native calls per letter and one fixed common clean encoding.  Neither the
basis-image witnesses nor the unknown input occur in any fixed circuit gate.

-/

namespace SparseHamiltonian.ODESectorNativeControl

noncomputable section
open ContinuousLinearMap OracleCircuit ODESectorTensor
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

variable {A B X L : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]

/-- Source-register coordinates are spectators of all three native queries. -/
def matrixProgram
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (b0 : B) :
    OracleCircuit.Program (NativeMaskedOracle.oracle (ι := A) F) :=
  MaskedProgram.compile (fun _ : A => true) (NativeControlledOracle.program F b0)

omit [DecidableEq A] in
@[simp] theorem matrixProgram_count
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (b0 : B) :
    (matrixProgram (A := A) F b0).count = 3 := by
  rw [matrixProgram, MaskedProgram.compile_count, NativeControlledOracle.program_count]

omit [DecidableEq A] in
theorem matrixProgram_apply
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (b0 : B)
    (x : X) (v : Physical A B) (a : A) :
    (matrixProgram (A := A) F b0).eval x v a =
      (NativeControlledOracle.program F b0).eval x (v a) := by
  simp only [matrixProgram, MaskedProgram.compile_eval, MaskedProgram.masked_apply,
    ↓reduceIte]

/-- Three ordinary calls implement the matrix sector and restore the clean
reference and dummy, including when a source-sector amplitude is present. -/
theorem matrixProgram_intertwines
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a0 : A) (b0 : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image x) 1) (x : X) :
    (matrixProgram (A := A) F b0).eval x ∘L input a0 b0 =
      input a0 b0 ∘L ODESourceTransport.matrixGate (F x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro a
  simp only [comp_apply, matrixProgram_apply, input_apply,
    ODESourceTransport.matrixGate_apply, WithLp.fst, WithLp.snd,
    map_add, map_smul]
  have hfalse : (NativeControlledOracle.program F b0).eval x (sourceSeed b0) =
      sourceSeed b0 :=
    NativeControlledOracle.program_packet_false F hF x b0 (image x) (hvalid x)
      (EuclideanSpace.single b0 1)
  rw [hfalse]
  by_cases ha : a = a0
  · simp only [ha, ↓reduceIte]
    rw [NativeControlledOracle.program_packet_true F hF x b0 (image x) (hvalid x)]
  · simp only [ha, ↓reduceIte, map_zero]

/-- Original native labels and the two supplied source interfaces. -/
def logicalOracle
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :
    L ⊕ Bool → X → Logical A B →L[ℂ] Logical A B :=
  Sum.elim (fun l x => ODESourceTransport.matrixGate (F l x))
    (fun b x => ODESourceTransport.sourceGate (S b x))

/-- Native matrix calls act unconditionally on their payload. Source controls
are exactly the supplied source access, with the remaining registers as spectators. -/
def physicalOracle
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :
    L ⊕ Bool → X → Physical A B →L[ℂ] Physical A B :=
  Sum.elim (fun l => NativeMaskedOracle.oracle (ι := A) (F l))
    (fun b x => sourcePhysical (B := B) (S b x))

omit [DecidableEq A] [DecidableEq B] in
theorem logicalOracle_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ l x, IsUnitary (F l x)) (hS : ∀ b x, IsUnitary (S b x))
    (k : L ⊕ Bool) (x : X) : IsUnitary (logicalOracle F S k x) := by
  cases k with
  | inl l => exact ODESourceTransport.matrixGate_unitary (F l x) (hF l x)
  | inr b => exact ODESourceTransport.sourceGate_unitary (S b x) (hS b x)

omit [DecidableEq A] [DecidableEq B] in
theorem physicalOracle_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ l x, IsUnitary (F l x)) (hS : ∀ b x, IsUnitary (S b x))
    (k : L ⊕ Bool) (x : X) : IsUnitary (physicalOracle F S k x) := by
  cases k with
  | inl l => exact NativeMaskedOracle.oracle_unitary (F l) (hF l) x
  | inr b => exact sourcePhysical_unitary (S b x) (hS b x)

/-- Every matrix letter is expanded into three calls with the same native
label. A supplied controlled source operation is one source call. -/
def letter
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (b0 : B) : L ⊕ Bool → MultiOracleCircuit.Program (physicalOracle F S)
  | .inl l => MultiOracleCircuit.Program.embed (Sum.inl l)
      (matrixProgram (A := A) (F l) b0)
  | .inr b => .query (Sum.inr b)

omit [DecidableEq A] in
@[simp] theorem letter_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (b0 : B) (k : L ⊕ Bool) (w : L ⊕ Bool → ℕ) :
    (letter F S b0 k).cost w =
      Sum.elim (fun l => 3 * w (Sum.inl l)) (fun b => w (Sum.inr b)) k := by
  cases k with
  | inl l =>
      simp only [letter, MultiOracleCircuit.Program.cost_embed, Sum.elim_inl]
      have hCount := matrixProgram_count (A := A) (F l) b0
      dsimp only [physicalOracle, Sum.elim_inl,
        ODESectorTensor.Physical, NativeMaskedOracle.Physical] at hCount ⊢
      exact congrArg (fun q : ℕ => q * w (Sum.inl l)) hCount
  | inr b => rfl

omit [DecidableEq A] in
/-- Matrix costs are multiplied by exactly three, with zero source charge. -/
theorem letter_matrix_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (b0 : B) (w : L → ℕ) (k : L ⊕ Bool) :
    (letter F S b0 k).cost (ODESourceQueryBudget.matrixWeight w) =
      3 * ODESourceQueryBudget.matrixWeight w k := by
  rw [letter_cost]
  cases k <;> simp only [ODESourceQueryBudget.matrixWeight,
    Sum.elim_inl, Sum.elim_inr, Nat.mul_zero]

omit [DecidableEq A] in
/-- Source calls retain their exact per-interface count. -/
theorem letter_source_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (b0 : B) (b : Bool) (k : L ⊕ Bool) :
    (letter F S b0 k).cost (ODESourceQueryBudget.sourceWeight b) =
      ODESourceQueryBudget.sourceWeight b k := by
  rw [letter_cost]
  cases k <;> simp only [ODESourceQueryBudget.sourceWeight,
    Sum.elim_inl, Sum.elim_inr, Nat.mul_zero]

omit [DecidableEq A] in
/-- Native control introduces no additional source calls. -/
theorem letter_source_total_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (b0 : B) (k : L ⊕ Bool) :
    (letter F S b0 k).cost ODESourceQueryBudget.sourceTotalWeight =
      ODESourceQueryBudget.sourceTotalWeight k := by
  rw [letter_cost]
  cases k <;> simp only [ODESourceQueryBudget.sourceTotalWeight,
    Sum.elim_inl, Sum.elim_inr, Nat.mul_zero]

theorem letter_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ l x, IsUnitary (F l x)) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1) (k : L ⊕ Bool) (x : X) :
    (letter F S b0 k).eval x ∘L input a0 b0 =
      input a0 b0 ∘L logicalOracle F S k x := by
  cases k with
  | inl l =>
      simp only [letter, MultiOracleCircuit.Program.eval_embed,
        logicalOracle, Sum.elim_inl]
      have hMatrix :=
        matrixProgram_intertwines (F l) (hF l) a0 b0 (image l) (hvalid l) x
      dsimp only [physicalOracle, Sum.elim_inl,
        ODESectorTensor.Physical, NativeMaskedOracle.Physical] at hMatrix ⊢
      exact hMatrix
  | inr b =>
      exact source_intertwines a0 b0 (S b x)

/-- Fixed logical gates are lifted through the common, oracle-independent
encoding; all primitive letters are substituted with their counted circuits. -/
def compile
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (a0 : A) (b0 : B) (p : MultiOracleCircuit.Program (logicalOracle F S)) :
    MultiOracleCircuit.Program (physicalOracle F S) :=
  EncodedLabeledProgram.compile
    (P := Logical A B) (K := Physical A B)
    (F := physicalOracle F S) (O := logicalOracle F S)
    (input a0 b0) (input_isometry a0 b0) (letter F S b0) p

/-- Exact clean-workspace simulation, including inverse queries and all
unknown source preparations inside amplification and its inverse. -/
theorem compile_eval
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ l x, IsUnitary (F l x)) (hS : ∀ b x, IsUnitary (S b x))
    (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program (logicalOracle F S)) (x : X) :
    (compile F S a0 b0 p).eval x ∘L input a0 b0 =
      input a0 b0 ∘L p.eval x :=
  EncodedLabeledProgram.compile_eval
    (P := Logical A B) (K := Physical A B)
    (F := physicalOracle F S) (O := logicalOracle F S)
    (input a0 b0) (input_isometry a0 b0) (letter F S b0)
    (physicalOracle_unitary F S hF hS) (logicalOracle_unitary F S hF hS)
    (letter_intertwines F S hF a0 b0 image hvalid) p x

/-- The compiled circuit is unitary on the whole physical workspace. -/
theorem compile_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (hF : ∀ l x, IsUnitary (F l x)) (hS : ∀ b x, IsUnitary (S b x))
    (a0 : A) (b0 : B) (p : MultiOracleCircuit.Program (logicalOracle F S)) (x : X) :
    IsUnitary ((compile F S a0 b0 p).eval x) :=
  (compile F S a0 b0 p).eval_unitary (physicalOracle_unitary F S hF hS) x

/-- A single exact weighted identity simultaneously counts all native labels
and both supplied source interfaces. -/
theorem compile_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (a0 : A) (b0 : B) (p : MultiOracleCircuit.Program (logicalOracle F S))
    (w : L ⊕ Bool → ℕ) :
    (compile F S a0 b0 p).cost w =
      p.cost (Sum.elim (fun l => 3 * w (Sum.inl l)) (fun b => w (Sum.inr b))) := by
  simp only [compile, EncodedLabeledProgram.compile_cost, letter_cost]


/-- Exact matrix cost for the entire concrete compiler. -/
theorem compile_matrix_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (a0 : A) (b0 : B) (p : MultiOracleCircuit.Program (logicalOracle F S))
    (w : L → ℕ) :
    (compile F S a0 b0 p).cost (ODESourceQueryBudget.matrixWeight w) =
      3 * p.cost (ODESourceQueryBudget.matrixWeight w) := by
  rw [compile, EncodedLabeledProgram.compile_cost]
  simp only [letter_matrix_cost]
  exact NativeHermitianDilation.cost_scale p _ 3

/-- The entire concrete compiler preserves each source count. -/
theorem compile_source_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (a0 : A) (b0 : B) (p : MultiOracleCircuit.Program (logicalOracle F S)) (b : Bool) :
    (compile F S a0 b0 p).cost (ODESourceQueryBudget.sourceWeight b) =
      p.cost (ODESourceQueryBudget.sourceWeight b) := by
  simp only [compile, EncodedLabeledProgram.compile_cost, letter_source_cost]

/-- The combined source-interface count is also preserved. -/
theorem compile_source_total_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (a0 : A) (b0 : B) (p : MultiOracleCircuit.Program (logicalOracle F S)) :
    (compile F S a0 b0 p).cost ODESourceQueryBudget.sourceTotalWeight =
      p.cost ODESourceQueryBudget.sourceTotalWeight := by
  simp only [compile, EncodedLabeledProgram.compile_cost, letter_source_total_cost]

end
end SparseHamiltonian.ODESectorNativeControl
