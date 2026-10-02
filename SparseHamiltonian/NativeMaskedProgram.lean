import SparseHamiltonian.NativeActiveClock

/-!
# Counted native compilation of changing masks and explicitly routed labels

Every source letter specifies one fixed native label and one fixed branch mask.
All masks share a common clean encoding. The physical program uses the original
native label vocabulary and incurs exactly three times each routed weighted
query cost. In particular no coherent SELECT over native labels is granted.
-/
namespace SparseHamiltonian.NativeMaskedProgram

noncomputable section
open ContinuousLinearMap OracleCircuit NativeMaskedOracle
open scoped InnerProduct
set_option maxHeartbeats 800000

variable {ι B X L M : Type*} [Fintype ι] [Fintype B] [DecidableEq B]

/-- The actual physical oracle family retains the native label vocabulary. -/
abbrev oracle (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    L → X → Physical ι B →L[ℂ] Physical ι B :=
  fun l => NativeMaskedOracle.oracle (F l)

/-- Logical calls to be implemented; each instruction carries one fixed native
label. The branch predicate never controls which native label is queried. -/
abbrev logicalOracle (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (label : M → L) (active : M → ι → Bool) :
    M → X → Logical ι B →L[ℂ] Logical ι B :=
  fun m x => MaskedProgram.masked (active m) (F (label m) x)

/-- A single masked letter implemented with three calls to its routed label. -/
def letter (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool) (m : M) :
    MultiOracleCircuit.Program (oracle (ι := ι) F) :=
  MultiOracleCircuit.Program.embed (label m)
    (NativeMaskedOracle.program (F (label m)) a (active m))

@[simp] theorem letter_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool) (m : M) :
    (letter F a label active m).count = 3 := by
  simp [letter]

@[simp] theorem letter_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool) (m : M) (w : L → ℕ) :
    (letter F a label active m).cost w = 3 * w (label m) := by
  simp [letter]

/-- Implement a logical native masked circuit, including all inverse calls and
all fixed gates, using only ordinary labeled physical native queries. -/
def compile (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (logicalOracle F label active)) :
    MultiOracleCircuit.Program (oracle (ι := ι) F) :=
  EncodedLabeledProgram.compile
    (P := Logical ι B) (K := Physical ι B)
    (F := oracle (ι := ι) F) (O := logicalOracle F label active)
    (NativeMaskedOracle.input (ι := ι) a).toContinuousLinearMap
    (NativeMaskedOracle.input (ι := ι) a).adjoint_comp_self (letter F a label active) p

/-- Exactly three native calls replace each logical masked call. -/
@[simp] theorem compile_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (logicalOracle F label active)) :
    (compile F a label active p).count = p.count * 3 := by
  simp [compile]

/-- The fully routed weighted count; costs of distinct primitives remain visible. -/
@[simp] theorem compile_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (logicalOracle F label active)) (w : L → ℕ) :
    (compile F a label active p).cost w = p.cost (fun m => 3 * w (label m)) := by
  simp [compile]

/-- Count each actual native primitive separately, including inverse calls. -/
@[simp] theorem compile_labelCount [DecidableEq L]
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (logicalOracle F label active)) (l : L) :
    (compile F a label active p).labelCount l =
      p.cost (fun m => if label m = l then 3 else 0) := by
  rw [MultiOracleCircuit.Program.labelCount, compile_cost]
  congr 1
  funext m
  by_cases h : label m = l <;> simp [h]

/-- Uniform full-output semantics under exact native basis-image promises.
The image is only a witness in the proof: it is absent from every fixed gate. -/
theorem compile_eval
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (logicalOracle F label active)) (x : X) :
    (compile F a label active p).eval x ∘L (NativeMaskedOracle.input (ι := ι) a).toContinuousLinearMap =
      (NativeMaskedOracle.input a).toContinuousLinearMap ∘L p.eval x := by
  apply EncodedLabeledProgram.compile_eval
    (P := Logical ι B) (K := Physical ι B)
    (F := oracle (ι := ι) F) (O := logicalOracle F label active)
  · exact fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y
  · exact fun m y => MaskedProgram.masked_unitary (active m) (F (label m) y) (hF _ y)
  · intro m y
    simpa only [letter, MultiOracleCircuit.Program.eval_embed] using
      NativeMaskedOracle.program_intertwines (F (label m)) (hF (label m)) a
        (image (label m)) (hvalid (label m)) (active m) y

/-- The physical program is unitary on the whole workspace, including states
outside the clean encoding. -/
theorem compile_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (label : M → L) (active : M → ι → Bool)
    (p : MultiOracleCircuit.Program (logicalOracle F label active)) (x : X) :
    IsUnitary ((compile F a label active p).eval x) :=
  (compile F a label active p).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y) x

end
end SparseHamiltonian.NativeMaskedProgram
