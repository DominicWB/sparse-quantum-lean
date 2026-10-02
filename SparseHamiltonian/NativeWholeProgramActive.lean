import SparseHamiltonian.NativeWholeProgramMask

namespace SparseHamiltonian.NativeWholeProgramActive

noncomputable section
open ContinuousLinearMap OracleCircuit ReuseLayerFactorization NativeMaskedOracle
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

variable {C B X L : Type*} [Fintype C] [Fintype B] [DecidableEq B]
  (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)

/-- Only unfinished private cells receive the program. Public slots bypass it. -/
def active (T d r : ℕ) : ActiveRegisterLayout.Label C T d → Bool
  | .inl ((i,_),_) => decide (r < ReuseWeights.length d i)
  | .inr _ => false

/-- The same native oracle family is used at every reuse index. -/
abbrev oracle (T d : ℕ) :=
  NativeMaskedProgram.oracle (ι := ActiveRegisterLayout.Label C T d) F

/-- Fixed flattening and the shared clean native-control workspace. -/
abbrev input (a : B) (T d : ℕ) := NativeActiveClock.input (C := C) a T d

/-- Literal source-program execution, simultaneously on all active cells. -/
def program (a : B) (p : MultiOracleCircuit.Program F) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle (C := C) F T d) :=
  NativeWholeProgramMask.program F a (active (C := C) T d r) p

@[simp] theorem program_count (a : B) (p : MultiOracleCircuit.Program F)
    (T d r : ℕ) : (program (C := C) F a p T d r).count = 3 * p.count := by
  simp [program]

@[simp] theorem program_cost (a : B) (p : MultiOracleCircuit.Program F)
    (T d r : ℕ) (w : L → ℕ) :
    (program (C := C) F a p T d r).cost w = 3 * p.cost w := by
  simp [program]

@[simp] theorem program_labelCount [DecidableEq L] (a : B)
    (p : MultiOracleCircuit.Program F) (T d r : ℕ) (l : L) :
    (program (C := C) F a p T d r).labelCount l = 3 * p.labelCount l :=
  program_cost F a p T d r _

omit [DecidableEq B] in
/-- Flattening turns chronological execution of an arbitrary operator into a
single branch mask. There is no involution or spectral assumption. -/
theorem layout_active (U : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (T d r : ℕ) :
    (ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d).conjStarAlgEquiv
      (activeClock (P := EuclideanSpace ℂ B)
        (WeightedClock.diagonal (fun _ : C => U)) T d r) =
      MaskedProgram.masked (active (C := C) T d r) U := by
  rw [ActiveRegisterLayout.layout_activeClock]
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rcases i with ⟨⟨j,t⟩,c⟩ | ⟨j,k⟩
  · by_cases h : r < ReuseWeights.length d j <;>
      simp [WeightedClock.diagonal_apply, ActiveRegisterLayout.mask,
        MaskedProgram.masked_apply, active, h]
  · simp [WeightedClock.diagonal_apply, ActiveRegisterLayout.mask,
      MaskedProgram.masked_apply, active]

/-- The actual program acts correctly on all reuse branches, time copies and
public bypasses, with a single fixed encoding for every layer. -/
theorem program_intertwines (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (T d r : ℕ) (x : X) :
    (program (C := C) F a p T d r).eval x ∘L
        (input (C := C) a T d).toContinuousLinearMap =
      (input (C := C) a T d).toContinuousLinearMap ∘L
        activeClock (P := EuclideanSpace ℂ B)
          (WeightedClock.diagonal (fun _ : C => p.eval x)) T d r := by
  have hp := NativeWholeProgramMask.program_intertwines F hF a image hvalid
    (active (C := C) T d r) p x
  let e := ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d
  let E := (NativeMaskedOracle.input (ι := ActiveRegisterLayout.Label C T d) a).toContinuousLinearMap
  change (NativeWholeProgramMask.program F a (active (C := C) T d r) p).eval x ∘L
      (E ∘L e.toContinuousLinearMap) = (E ∘L e.toContinuousLinearMap) ∘L _
  rw [← comp_assoc, hp, comp_assoc, comp_assoc]
  congr 1
  rw [← layout_active (C := C) (p.eval x) T d r]
  apply ContinuousLinearMap.ext
  intro v
  change e (activeClock (P := EuclideanSpace ℂ B)
      (WeightedClock.diagonal (fun _ : C => p.eval x)) T d r (e.symm (e v))) =
    e (activeClock (P := EuclideanSpace ℂ B)
      (WeightedClock.diagonal (fun _ : C => p.eval x)) T d r v)
  rw [e.symm_apply_apply]

/-- The source query count, rather than the number of chronological slots,
controls the primitive query count of one whole active layer. -/
theorem all_active_certificate (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (T d : ℕ) :
    (input (C := C) a T d).toContinuousLinearMap† ∘L
      (input (C := C) a T d).toContinuousLinearMap = 1 ∧
    (∀ l x, IsUnitary (oracle (C := C) F T d l x)) ∧
    ∀ r, (program (C := C) F a p T d r).count = 3 * p.count ∧
      ∀ x, (program (C := C) F a p T d r).eval x ∘L
          (input (C := C) a T d).toContinuousLinearMap =
        (input (C := C) a T d).toContinuousLinearMap ∘L
          activeClock (P := EuclideanSpace ℂ B)
            (WeightedClock.diagonal (fun _ : C => p.eval x)) T d r :=
  ⟨(input (C := C) a T d).adjoint_comp_self,
    fun l x => NativeMaskedOracle.oracle_unitary (F l) (hF l) x,
    fun r => ⟨program_count F a p T d r,
      program_intertwines F hF a image hvalid p T d r⟩⟩

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- An arbitrary fixed public embedding can be used alongside the same native
workspace, without changing any native query. -/
def publicInput (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (a : B) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P)
      (V := ChronologicalResolvent.BlockOperator.H T (Logical C B)) d) →ₗᵢ[ℂ]
        Physical (ActiveRegisterLayout.Label C T d) B :=
  (input (C := C) a T d).comp (PublicRegisterEncoding.workspaceEmbedding e d)

omit [CompleteSpace P] in
/-- Complete public-space transfer; it does not require that the public system
have the same dimension as the primitive oracle payload. -/
theorem program_public_intertwines (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (T d r : ℕ) (x : X) :
    (program (C := C) F a p T d r).eval x ∘L
        (publicInput (C := C) e a T d).toContinuousLinearMap =
      (publicInput (C := C) e a T d).toContinuousLinearMap ∘L
        activeClock (P := P)
          (WeightedClock.diagonal (fun _ : C => p.eval x)) T d r := by
  change (program (C := C) F a p T d r).eval x ∘L
      ((input (C := C) a T d).toContinuousLinearMap ∘L PublicRegisterEncoding.embedding e d) =
    ((input (C := C) a T d).toContinuousLinearMap ∘L PublicRegisterEncoding.embedding e d) ∘L _
  rw [← comp_assoc, program_intertwines F hF a image hvalid, comp_assoc,
    PublicRegisterEncoding.activeClock_intertwines, comp_assoc]

end
end SparseHamiltonian.NativeWholeProgramActive
