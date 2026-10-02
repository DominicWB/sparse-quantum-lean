import SparseHamiltonian.NativeCayleyProgram

/-!
# Primitive implementation of every active Cayley layer

The actual eighteen-query sparse program is executed simultaneously on every
active chronological cell. The native-control compiler supplies one shared
clean workspace, a fixed public embedding, and exactly fifty-four primitive
calls per layer. All oracle basis promises come from the original sparse data.
-/

namespace SparseHamiltonian.NativeCayleyActive

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The public system is placed in the same fixed native payload as the private
system. This preparation contains no oracle-dependent operation. -/
def publicEmbedding (D : Data X n Z s) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ (NativeCayleyProgram.Basis n Z) where
  toLinearMap := (NativeCayleyProgram.clean D).toLinearMap.comp
    (FixedNativeCayleySimulation.boundary D).toLinearMap
  norm_map' := by
    intro v
    change ‖NativeCayleyProgram.clean D (FixedNativeCayleySimulation.boundary D v)‖ = ‖v‖
    rw [(NativeCayleyProgram.clean D).norm_map]
    exact (FixedNativeCayleySimulation.boundary D).norm_map_iff_adjoint_comp_self.mpr
      (FixedNativeCayleySimulation.boundary_isometry D) v

/-- A singleton clock index lets the generic active compiler execute the
actual native program directly, without a distributed involution clock. -/
def privateEmbedding (D : Data X n Z s) :
    SparseEdgeMoments.OrientedSpace n →ₗᵢ[ℂ]
      NativeMaskedOracle.Logical PUnit.{1} (NativeCayleyProgram.Basis n Z) :=
  FlatMaskedAccess.singleton (NativeCayleyProgram.clean D)

/-- Full native workspace, with the active label and all query spectators.
The singleton register lives in `Type 0`, so independently used encodings
cannot acquire unrelated universe parameters. -/
abbrev Physical (n Z : Type*) [Fintype n] [Fintype Z] (T d : ℕ) :=
  NativeMaskedOracle.Physical (ActiveRegisterLayout.Label PUnit.{1} T d)
    (NativeCayleyProgram.Basis n Z)

/-- Every layer uses the same original native labels with spectator registers. -/
abbrev oracle (D : Data X n Z s) (T d : ℕ) :
    Query → X → Physical n Z T d →L[ℂ] Physical n Z T d :=
  NativeWholeProgramActive.oracle (C := PUnit.{1}) (NativeCayleyProgram.oracle D) T d

/-- Fixed logical-to-physical encoding, common to all reuse indices. -/
def embedding (D : Data X n Z s) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := EuclideanSpace ℂ n)
      (V := ChronologicalResolvent.BlockOperator.H T (SparseEdgeMoments.OrientedSpace n)) d)
      →ₗᵢ[ℂ] Physical n Z T d :=
  NativeWholeProgramActive.cleanInput (C := PUnit.{1}) (publicEmbedding D) (privateEmbedding D)
    (NativeCayleyProgram.cleanBasis D) T d

/-- Literal primitive circuit for one active chronological layer. -/
def program (D : Data X n Z s) (γ : ℝ) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle D T d) :=
  NativeWholeProgramActive.program (C := PUnit.{1}) (NativeCayleyProgram.oracle D)
    (NativeCayleyProgram.cleanBasis D) (NativeCayleyProgram.program D γ) T d r

@[simp] theorem program_count (D : Data X n Z s) (γ : ℝ) (T d r : ℕ) :
    (program D γ T d r).count = 54 := by
  rw [program, NativeWholeProgramActive.program_count, NativeCayleyProgram.program_count]

/-- Primitive costs remain separate even after all controls and spectators. -/
theorem program_cost (D : Data X n Z s) (γ : ℝ) (T d r : ℕ) (w : Query → ℕ) :
    (program D γ T d r).cost w =
      18 * w .rowLocation + 18 * w .columnLocation + 18 * w .value := by
  rw [program, NativeWholeProgramActive.program_cost, NativeCayleyProgram.program_cost]
  ring

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (T d : ℕ) (l : Query) (x : X) :
    IsUnitary (oracle D T d l x) :=
  NativeMaskedOracle.oracle_unitary (NativeCayleyProgram.oracle D l)
    (NativeCayleyProgram.oracle_unitary D l) x

/-- Correctness on arbitrary coherent public and private amplitudes, with all
native-control ancillas returned to their common clean state. -/
theorem program_intertwines (D : Data X n Z s) (γ : ℝ) (T d r : ℕ) (x : X) :
    (program D γ T d r).eval x ∘L (embedding D T d).toContinuousLinearMap =
      (embedding D T d).toContinuousLinearMap ∘L
        ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
          (FixedNativeCayleySimulation.action D x γ) T d r := by
  exact NativeWholeProgramActive.program_clean_intertwines
    (C := PUnit.{1}) (B := NativeCayleyProgram.Basis n Z)
    (P := EuclideanSpace ℂ n) (V := SparseEdgeMoments.OrientedSpace n)
    (NativeCayleyProgram.oracle D) (NativeCayleyProgram.oracle_unitary D)
    (NativeCayleyProgram.cleanBasis D) (NativeCayleyProgram.image D)
    (NativeCayleyProgram.valid D) (NativeCayleyProgram.program D γ)
    (publicEmbedding D) (privateEmbedding D)
    (fun x => FixedNativeCayleySimulation.action D x γ)
    (fun x => FlatMaskedAccess.singleton_intertwines
      (V := SparseEdgeMoments.OrientedSpace n) (B := NativeCayleyProgram.Basis n Z)
      ((NativeCayleyProgram.program D γ).eval x)
      (FixedNativeCayleySimulation.action D x γ) (NativeCayleyProgram.clean D)
      (NativeCayleyProgram.program_intertwines D γ x)) T d r x

/-- The formerly conditional active implementation premise is now discharged
at an absolute primitive query cost. No coherent native SELECT is assumed. -/
theorem implementsOn (D : Data X n Z s) (γ : ℝ) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle D T d)
      (fun x => ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
        (FixedNativeCayleySimulation.action D x γ) T d r)
      (embedding D T d).toContinuousLinearMap 54 :=
  ⟨program D γ T d r, program_intertwines D γ T d r, (program_count D γ T d r).le⟩

end
end SparseHamiltonian.NativeCayleyActive
