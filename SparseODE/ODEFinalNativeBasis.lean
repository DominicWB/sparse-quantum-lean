import SparseODE.ODESectorNativeControl

/-!
# Computational-basis access for the complete aligned ODE workspace

The final native simulator contains only fixed spectator registers around
its original sparse primitive. Flattening these registers gives an explicit
Euclidean basis and a common phase-one basis transition for every primitive.
This is the hypothesis needed by the proved dummy-input control compiler;
it is derived from sparse access, rather than assumed for an unknown unitary.
-/

namespace SparseHamiltonian.ODEFinalNativeBasis

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

section AlignedMasked

variable {β B X L : Type*} [Fintype β] [Fintype B] [DecidableEq B]

abbrev AlignedSpace (β B : Type*) [Fintype β] [Fintype B] :=
  CleanOutputAlignment.Double (NativeMaskedOracle.Physical β B)

abbrev AlignedBasis (β B : Type*) := Bool × FlatBranchNativeAccess.Basis β B

/-- Flatten the alignment spectator after flattening the native clock payload. -/
def alignedLayout : AlignedSpace β B ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlignedBasis β B) :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Bool =>
    FlatBranchNativeAccess.layout (ι := β) (B := B))).trans
      (RegisterEquivalences.productFlatten Bool (FlatBranchNativeAccess.Basis β B))

omit [DecidableEq B] in
@[simp] theorem alignedLayout_apply (v : AlignedSpace β B)
    (b : Bool) (i : β) (w : NativeControlledOracle.Workspace B) :
    alignedLayout v (b, (i, w)) = v b i w := rfl

omit [DecidableEq B] in
@[simp] theorem alignedLayout_symm_apply
    (v : EuclideanSpace ℂ (AlignedBasis β B))
    (b : Bool) (i : β) (w : NativeControlledOracle.Workspace B) :
    alignedLayout.symm v b i w = v (b, (i, w)) := rfl

/-- Fixed conjugation of the final aligned native oracle, not a new oracle. -/
abbrev alignedOracle
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (l : L) (x : X) :
    EuclideanSpace ℂ (AlignedBasis β B) →L[ℂ] EuclideanSpace ℂ (AlignedBasis β B) :=
  (alignedLayout (β := β) (B := B)).conjStarAlgEquiv
    (AlignedMultiOracleProgram.oracle (NativeMaskedProgram.oracle (ι := β) F) l x)

omit [DecidableEq B] in
/-- Every displayed extra register is an untouched spectator of one call. -/
theorem alignedOracle_eq_spectator
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (l : L) (x : X) :
    alignedOracle (β := β) F l x = LookupFromBasisOracle.spectator (S := Bool)
      (FlatBranchNativeAccess.flatOracle (ι := β) F l x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨b, i, w⟩
  rfl

omit [DecidableEq B] in
theorem alignedOracle_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (l : L) (x : X) :
    IsUnitary (alignedOracle (β := β) F l x) := by
  rw [alignedOracle_eq_spectator]
  exact LookupFromBasisOracle.spectator_unitary _
    (FlatBranchNativeAccess.flatOracle_unitary (ι := β) F hF l x)

/-- A fixed alignment flag and clock cell suffice for a common dummy input. -/
def alignedClean (i0 : β) (a : B) : AlignedBasis β B :=
  (false, FlatBranchNativeAccess.cleanBasis i0 a)

def alignedImage (i0 : β) (a b : B) : AlignedBasis β B :=
  (false, FlatBranchNativeAccess.imageBasis i0 a b)

/-- The phase-one basis transition survives both fixed spectator layouts. -/
theorem aligned_valid [DecidableEq β]
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (i0 : β) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1) (l : L) (x : X) :
    alignedOracle (β := β) F l x (EuclideanSpace.single (alignedClean i0 a) 1) =
      EuclideanSpace.single (alignedImage i0 a (image l x)) 1 := by
  rw [alignedOracle_eq_spectator]
  exact LookupFromBasisOracle.spectator_single
    (FlatBranchNativeAccess.flatOracle (ι := β) F l x)
    (FlatBranchNativeAccess.cleanBasis i0 a)
    (FlatBranchNativeAccess.imageBasis i0 a (image l x)) 1
    (FlatBranchNativeAccess.valid F i0 a image hvalid l x) false

end AlignedMasked

section Native

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Basis (ι n Z : Type*) (T d : ℕ) :=
  AlignedBasis (ActiveRegisterLayout.Label PUnit.{1} T d) (ODEJointNative.Basis ι n Z)

/-- The complete physical space after output alignment. -/
abbrev Physical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (T d : ℕ) :=
  CleanOutputAlignment.Double (ODEJointNative.Physical ι n Z T d)

def layout (T d : ℕ) :
    Physical ι n Z T d ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Basis ι n Z T d) :=
  alignedLayout (β := ActiveRegisterLayout.Label PUnit.{1} T d)
    (B := ODEJointNative.Basis ι n Z)

abbrev flatOracle (D : Data X n Z s) (T d : ℕ) :=
  alignedOracle (β := ActiveRegisterLayout.Label PUnit.{1} T d)
    (ODEJointNative.cayleyOracle (ι := ι) D)

omit [DecidableEq ι] [DecidableEq Z] in
/-- The actual final native oracle has exactly these fixed coordinates. -/
theorem flatOracle_eq_transport (D : Data X n Z s) (T d : ℕ)
    (l : Query) (x : X) :
    flatOracle (ι := ι) D T d l x =
      (layout (ι := ι) (n := n) (Z := Z) T d).conjStarAlgEquiv
        (AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d) l x) := rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem flatOracle_eq_spectator (D : Data X n Z s) (T d : ℕ)
    (l : Query) (x : X) :
    flatOracle (ι := ι) D T d l x =
      LookupFromBasisOracle.spectator (S := Bool)
        (FlatBranchNativeAccess.flatOracle
          (ι := ActiveRegisterLayout.Label PUnit.{1} T d)
          (ODEJointNative.cayleyOracle (ι := ι) D) l x) :=
  alignedOracle_eq_spectator
    (β := ActiveRegisterLayout.Label PUnit.{1} T d)
    (ODEJointNative.cayleyOracle (ι := ι) D) l x

omit [DecidableEq ι] [DecidableEq Z] in
theorem flatOracle_unitary (D : Data X n Z s) (T d : ℕ) (l : Query) (x : X) :
    IsUnitary (flatOracle (ι := ι) D T d l x) :=
  alignedOracle_unitary
    (β := ActiveRegisterLayout.Label PUnit.{1} T d)
    (ODEJointNative.cayleyOracle (ι := ι) D)
    (ODEJointNative.cayleyOracle_unitary (ι := ι) D) l x

/-- The negative reuse branch at zero has one public slot even when T or d
is zero. This choice requires no positivity or nonemptiness promise. -/
def clockBasis (T d : ℕ) : ActiveRegisterLayout.Label PUnit.{1} T d :=
  .inr ⟨.inr (0 : Fin (d + 1)), ⟨0, by simp [ReuseWeights.length]⟩⟩

def cleanBasis (D : Data X n Z s) (i0 : ι) (T d : ℕ) : Basis ι n Z T d :=
  alignedClean (clockBasis T d) (ODEJointNative.cleanBasis D i0)

def image (D : Data X n Z s) (i0 : ι) (T d : ℕ) (l : Query) (x : X) :
    Basis ι n Z T d :=
  alignedImage (clockBasis T d) (ODEJointNative.cleanBasis D i0)
    (ODEJointNative.image D i0 l x)

/-- Original sparse-data promises prove the common phase-one dummy transition
for every final physical matrix primitive. -/
theorem valid (D : Data X n Z s) (i0 : ι) (T d : ℕ) (l : Query) (x : X) :
    flatOracle (ι := ι) D T d l x (EuclideanSpace.single (cleanBasis D i0 T d) 1) =
      EuclideanSpace.single (image D i0 T d l x) 1 :=
  aligned_valid (β := ActiveRegisterLayout.Label PUnit.{1} T d)
    (ODEJointNative.cayleyOracle (ι := ι) D) (clockBasis T d)
    (ODEJointNative.cleanBasis D i0) (ODEJointNative.image D i0)
    (ODEJointNative.valid D i0) l x

/-- Transport any complete simulator program through the fixed final layout. -/
def transportProgram (D : Data X n Z s) (T d : ℕ)
    (p : MultiOracleCircuit.Program
      (AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d))) :
    MultiOracleCircuit.Program (flatOracle (ι := ι) D T d) := by
  let q := MultiOracleCircuit.Program.transport
    (O := AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d))
    (layout (ι := ι) (n := n) (Z := Z) T d) p
  exact q

omit [DecidableEq ι] [DecidableEq Z] in
theorem transportProgram_eval (D : Data X n Z s) (T d : ℕ)
    (p : MultiOracleCircuit.Program
      (AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d))) (x : X) :
    (transportProgram D T d p).eval x =
      (layout (ι := ι) (n := n) (Z := Z) T d).conjStarAlgEquiv (p.eval x) := by
  exact MultiOracleCircuit.Program.eval_transport
    (O := AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d))
    (layout (ι := ι) (n := n) (Z := Z) T d) p x

omit [DecidableEq ι] [DecidableEq Z] in
theorem transportProgram_count (D : Data X n Z s) (T d : ℕ)
    (p : MultiOracleCircuit.Program
      (AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d))) :
    (transportProgram D T d p).count = p.count := by
  exact MultiOracleCircuit.Program.count_transport
    (O := AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d))
    (layout (ι := ι) (n := n) (Z := Z) T d) p

omit [DecidableEq ι] [DecidableEq Z] in
theorem transportProgram_cost (D : Data X n Z s) (T d : ℕ)
    (p : MultiOracleCircuit.Program
      (AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d)))
    (w : Query → ℕ) : (transportProgram D T d p).cost w = p.cost w := by
  exact MultiOracleCircuit.Program.cost_transport
    (O := AlignedMultiOracleProgram.oracle (ODEJointNative.oracle (ι := ι) D T d))
    (layout (ι := ι) (n := n) (Z := Z) T d) p w

end Native

section SourceCoordinates

variable {σ ι n : Type*} [Fintype σ] [Fintype ι] [Fintype n]

/-- The logical source register also has fixed Cartesian computational coordinates. -/
def sourceLayout : ODEJointLCU.BranchSpace (σ × ι) (EuclideanSpace ℂ n)
    ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((σ × ι) × n) :=
  RegisterEquivalences.productFlatten (σ × ι) n

end SourceCoordinates

end
end SparseHamiltonian.ODEFinalNativeBasis
