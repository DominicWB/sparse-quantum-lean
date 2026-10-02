import SparseHamiltonian.NativeMultiSelected

/-!
# Active reuse of explicitly labeled native queries

One fixed native oracle family and one clean encoding serve every chronological
copy and reuse index. Label selection is implemented by the explicitly counted
sequence of masks. Public cells and completed branches bypass every primitive.
-/
namespace SparseHamiltonian.NativeMultiActiveClock
noncomputable section
open ContinuousLinearMap OracleCircuit NativeMaskedOracle ReuseLayerFactorization ActiveClockAlgebra
open ChronologicalResolvent
open scoped InnerProduct BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

variable {C B X L : Type*} [Fintype C] [Fintype B] [DecidableEq B]
  [Fintype L] [DecidableEq L]

/-- Disable all letters on completed private branches and public bypass cells. -/
def activeChoice (choice : C → Option (L × Bool)) (T d r : ℕ) :
    ActiveRegisterLayout.Label C T d → Option (L × Bool)
  | .inl ((i, _), c) => if r < ReuseWeights.length d i then choice c else none
  | .inr _ => none

/-- Original physical native labels, independent of the active-step index. -/
abbrev oracle (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (T d : ℕ) :=
  NativeMaskedProgram.oracle (ι := ActiveRegisterLayout.Label C T d) F

/-- Fixed active-register flattening and fixed clean native-control ancillas. -/
def input (a : B) (T d : ℕ) :
    ActiveRegisterLayout.Space (EuclideanSpace ℂ B) C T d →ₗᵢ[ℂ]
      Physical (ActiveRegisterLayout.Label C T d) B :=
  (NativeMaskedOracle.input a).comp
    (ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d).toLinearIsometry

/-- An actual multi-native circuit; the active mask affects only fixed gates. -/
def optionalProgram
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (choice : C → Option (L × Bool)) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle (C := C) F T d) :=
  NativeMultiSelected.program F a (activeChoice choice T d r)

@[simp] theorem optionalProgram_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (choice : C → Option (L × Bool)) (T d r : ℕ) :
    (optionalProgram F a choice T d r).count = 6 * Fintype.card L := by
  simp [optionalProgram]

@[simp] theorem optionalProgram_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (choice : C → Option (L × Bool)) (T d r : ℕ) (w : L → ℕ) :
    (optionalProgram F a choice T d r).cost w = 6 * ∑ l, w l := by
  simp [optionalProgram]

omit [DecidableEq B] [Fintype L] [DecidableEq L] in
/-- Register flattening exposes the actual simultaneous optional letters. -/
theorem layout_active_optional
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : C → Option (L × Bool)) (T d r : ℕ) (x : X) :
    (ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d).conjStarAlgEquiv
      (activeClock (P := EuclideanSpace ℂ B)
        (WeightedClock.diagonal (fun c => MultiQueryNormalForm.optionalQuery F (choice c) x)) T d r) =
      WeightedClock.diagonal (fun i => MultiQueryNormalForm.optionalQuery F
        (activeChoice choice T d r i) x) := by
  rw [ActiveRegisterLayout.layout_activeClock]
  congr 1
  funext i
  rcases i with ⟨⟨j,t⟩,c⟩ | ⟨j,k⟩
  · by_cases h : r < ReuseWeights.length d j <;>
      simp [ActiveRegisterLayout.mask, activeChoice, h, MultiQueryNormalForm.optionalQuery]
  · simp [ActiveRegisterLayout.mask, activeChoice, MultiQueryNormalForm.optionalQuery]

/-- Every active reuse step has the same physical oracle family and clean encoding. -/
theorem optionalProgram_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (choice : C → Option (L × Bool)) (T d r : ℕ) (x : X) :
    (optionalProgram F a choice T d r).eval x ∘L (input (C := C) a T d).toContinuousLinearMap =
      (input a T d).toContinuousLinearMap ∘L activeClock (P := EuclideanSpace ℂ B)
        (WeightedClock.diagonal (fun c => MultiQueryNormalForm.optionalQuery F (choice c) x)) T d r := by
  have hp := NativeMultiSelected.program_intertwines F hF a image hvalid
    (activeChoice choice T d r) x
  let e := ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d
  let E := (NativeMaskedOracle.input (ι := ActiveRegisterLayout.Label C T d) a).toContinuousLinearMap
  change (NativeMultiSelected.program F a (activeChoice choice T d r)).eval x ∘L
    (E ∘L e.toContinuousLinearMap) = (E ∘L e.toContinuousLinearMap) ∘L _
  rw [← comp_assoc, hp, comp_assoc, comp_assoc]
  congr 1
  rw [← layout_active_optional F choice T d r x]
  apply ContinuousLinearMap.ext
  intro v
  change e (activeClock (P := EuclideanSpace ℂ B)
      (WeightedClock.diagonal (fun c => MultiQueryNormalForm.optionalQuery F (choice c) x)) T d r
      (e.symm (e v))) = e (activeClock (P := EuclideanSpace ℂ B)
        (WeightedClock.diagonal (fun c => MultiQueryNormalForm.optionalQuery F (choice c) x)) T d r v)
  rw [e.symm_apply_apply]

/-- Fixed routing is lifted once to the common physical encoding. -/
def program
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (G : Logical C B →L[ℂ] Logical C B) (hG : IsUnitary G)
    (choice : C → Option (L × Bool)) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle (C := C) F T d) :=
  .seq (.fixed
    (SubspaceOracle.lift (input (C := C) a T d).toContinuousLinearMap
      (activeClock (P := EuclideanSpace ℂ B) G T d r))
    (SubspaceOracle.lift_unitary _ (input (C := C) a T d).adjoint_comp_self _
      (activeClock_unitary G hG T d r)))
    (optionalProgram F a choice T d r)

@[simp] theorem program_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (G : Logical C B →L[ℂ] Logical C B) (hG : IsUnitary G)
    (choice : C → Option (L × Bool)) (T d r : ℕ) :
    (program F a G hG choice T d r).count = 6 * Fintype.card L := by simp [program]

@[simp] theorem program_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (G : Logical C B →L[ℂ] Logical C B) (hG : IsUnitary G)
    (choice : C → Option (L × Bool)) (T d r : ℕ) (w : L → ℕ) :
    (program F a G hG choice T d r).cost w = 6 * ∑ l, w l := by simp [program]

/-- All fixed routing and optional native queries implement the full active clock. -/
theorem program_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (G : Logical C B →L[ℂ] Logical C B) (hG : IsUnitary G)
    (choice : C → Option (L × Bool)) (T d r : ℕ) (x : X) :
    (program F a G hG choice T d r).eval x ∘L (input (C := C) a T d).toContinuousLinearMap =
      (input a T d).toContinuousLinearMap ∘L activeClock (P := EuclideanSpace ℂ B)
        (G ∘L WeightedClock.diagonal (fun c => MultiQueryNormalForm.optionalQuery F (choice c) x)) T d r := by
  simp only [program, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed]
  change (SubspaceOracle.lift (input (C := C) a T d).toContinuousLinearMap
      (activeClock (P := EuclideanSpace ℂ B) G T d r) ∘L
      (optionalProgram F a choice T d r).eval x) ∘L
      (input a T d).toContinuousLinearMap = _
  rw [comp_assoc, optionalProgram_intertwines F hF a image hvalid,
    ← comp_assoc, EncodedOracle.lift_comp _ (input (C := C) a T d).adjoint_comp_self,
    comp_assoc, ← activeClock_comp]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- A smaller public system is encoded only in public reuse cells. -/
def publicInput (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (a : B) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P)
      (V := BlockOperator.H T (Logical C B)) d) →ₗᵢ[ℂ]
        Physical (ActiveRegisterLayout.Label C T d) B :=
  (input (C := C) a T d).comp (PublicRegisterEncoding.workspaceEmbedding e d)

omit [CompleteSpace P] in
/-- Arbitrary fixed public encodings preserve both the common oracle and the count. -/
theorem program_public_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (G : Logical C B →L[ℂ] Logical C B) (hG : IsUnitary G)
    (choice : C → Option (L × Bool)) (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (T d r : ℕ) (x : X) :
    (program F a G hG choice T d r).eval x ∘L (publicInput (C := C) e a T d).toContinuousLinearMap =
      (publicInput e a T d).toContinuousLinearMap ∘L activeClock (P := P)
        (G ∘L WeightedClock.diagonal (fun c => MultiQueryNormalForm.optionalQuery F (choice c) x)) T d r := by
  change (program F a G hG choice T d r).eval x ∘L
      ((input (C := C) a T d).toContinuousLinearMap ∘L PublicRegisterEncoding.embedding e d) =
    ((input a T d).toContinuousLinearMap ∘L PublicRegisterEncoding.embedding e d) ∘L _
  rw [← comp_assoc, program_intertwines F hF a image hvalid, comp_assoc,
    PublicRegisterEncoding.activeClock_intertwines, comp_assoc]

end
end SparseHamiltonian.NativeMultiActiveClock
