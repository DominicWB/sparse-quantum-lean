import SparseODE.ODENativeCayley

/-!
# Native active layers for the tagged ODE Hamiltonians

The concrete twenty-four-query Cayley circuit is executed simultaneously in
all active chronological cells. Native basis promises derive its coherent
control without assuming a controlled sparse oracle. Every active layer uses
exactly seventy-two primitive calls, with a fixed embedding independent of
the LCHS node and the Cayley scale parameters.

-/

namespace SparseHamiltonian.ODENativeActive

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
    EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ (ODENativeCayley.Basis n Z) where
  toLinearMap := (ODENativeCayley.clean D).toLinearMap.comp
    (ODEFixedTaggedMoments.boundary D).toLinearMap
  norm_map' := by
    intro v
    change ‖ODENativeCayley.clean D (ODEFixedTaggedMoments.boundary D v)‖ = ‖v‖
    rw [(ODENativeCayley.clean D).norm_map]
    exact (ODEFixedTaggedMoments.boundary D).norm_map_iff_adjoint_comp_self.mpr
      (ODEFixedTaggedMoments.boundary_isometry D) v

/-- A singleton clock index lets the generic active compiler execute the
actual native program directly, without a distributed involution clock. -/
def privateEmbedding (D : Data X n Z s) :
    ODETaggedMoments.PrivateSpace n →ₗᵢ[ℂ]
      NativeMaskedOracle.Logical PUnit.{1} (ODENativeCayley.Basis n Z) :=
  FlatMaskedAccess.singleton (ODENativeCayley.clean D)

/-- Full native workspace, with the active label and all query spectators.
The singleton register lives in `Type 0`, so independently used encodings
cannot acquire unrelated universe parameters. -/
abbrev Physical (n Z : Type*) [Fintype n] [Fintype Z] (T d : ℕ) :=
  NativeMaskedOracle.Physical (ActiveRegisterLayout.Label PUnit.{1} T d)
    (ODENativeCayley.Basis n Z)

/-- Every layer uses the same original native labels with spectator registers. -/
abbrev oracle (D : Data X n Z s) (T d : ℕ) :
    Query → X → Physical n Z T d →L[ℂ] Physical n Z T d :=
  NativeWholeProgramActive.oracle (C := PUnit.{1}) (ODENativeCayley.oracle D) T d

/-- Fixed logical-to-physical encoding, common to all reuse indices. -/
def embedding (D : Data X n Z s) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := EuclideanSpace ℂ n)
      (V := ChronologicalResolvent.BlockOperator.H T (ODETaggedMoments.PrivateSpace n)) d)
      →ₗᵢ[ℂ] Physical n Z T d :=
  NativeWholeProgramActive.cleanInput (C := PUnit.{1}) (publicEmbedding D) (privateEmbedding D)
    (ODENativeCayley.cleanBasis D) T d

/-- Literal primitive circuit for one active chronological layer. -/
def program (D : Data X n Z s) (k γ ρ : ℝ) (T d r : ℕ) :
    MultiOracleCircuit.Program (oracle D T d) :=
  NativeWholeProgramActive.program (C := PUnit.{1}) (ODENativeCayley.oracle D)
    (ODENativeCayley.cleanBasis D) (ODENativeCayley.program D k γ ρ) T d r

@[simp] theorem program_count (D : Data X n Z s) (k γ ρ : ℝ) (T d r : ℕ) :
    (program D k γ ρ T d r).count = 72 := by
  rw [program, NativeWholeProgramActive.program_count, ODENativeCayley.program_count]

/-- Primitive costs remain separate even after all controls and spectators. -/
theorem program_cost (D : Data X n Z s) (k γ ρ : ℝ) (T d r : ℕ) (w : Query → ℕ) :
    (program D k γ ρ T d r).cost w =
      18 * w .rowLocation + 18 * w .columnLocation + 36 * w .value := by
  rw [program, NativeWholeProgramActive.program_cost, ODENativeCayley.program_cost]
  ring

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (T d : ℕ) (l : Query) (x : X) :
    IsUnitary (oracle D T d l x) :=
  NativeMaskedOracle.oracle_unitary (ODENativeCayley.oracle D l)
    (ODENativeCayley.oracle_unitary D l) x

/-- Correctness on arbitrary coherent public and private amplitudes, with all
native-control ancillas returned to their common clean state. -/
theorem program_intertwines (D : Data X n Z s) (k γ ρ : ℝ) (T d r : ℕ) (x : X) :
    (program D k γ ρ T d r).eval x ∘L (embedding D T d).toContinuousLinearMap =
      (embedding D T d).toContinuousLinearMap ∘L
        ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
          (ODEFixedTaggedMoments.action D x
            (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ) T d r := by
  exact NativeWholeProgramActive.program_clean_intertwines
    (C := PUnit.{1}) (B := ODENativeCayley.Basis n Z)
    (P := EuclideanSpace ℂ n) (V := ODETaggedMoments.PrivateSpace n)
    (ODENativeCayley.oracle D) (ODENativeCayley.oracle_unitary D)
    (ODENativeCayley.cleanBasis D) (ODENativeCayley.image D)
    (ODENativeCayley.valid D) (ODENativeCayley.program D k γ ρ)
    (publicEmbedding D) (privateEmbedding D)
    (fun x => ODEFixedTaggedMoments.action D x
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ)
    (fun x => FlatMaskedAccess.singleton_intertwines
      (V := ODETaggedMoments.PrivateSpace n) (B := ODENativeCayley.Basis n Z)
      ((ODENativeCayley.program D k γ ρ).eval x)
      (ODEFixedTaggedMoments.action D x
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ) (ODENativeCayley.clean D)
      (ODENativeCayley.program_intertwines D k γ ρ x)) T d r x

/-- The formerly conditional active implementation premise is now discharged
at an absolute primitive query cost. No coherent native SELECT is assumed. -/
theorem implementsOn (D : Data X n Z s) (k γ ρ : ℝ) (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle D T d)
      (fun x => ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
        (ODEFixedTaggedMoments.action D x
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ) T d r)
      (embedding D T d).toContinuousLinearMap 72 :=
  ⟨program D k γ ρ T d r, program_intertwines D k γ ρ T d r, (program_count D k γ ρ T d r).le⟩

end
end SparseHamiltonian.ODENativeActive
