import ConstantODELowerBound.Oracle

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released constant-coefficient solver's physical oracle in normal form

Manuscript lines 4105-4109 (access "through a reversible value oracle and in-place row/column
locators, their inverses and controls"; known operations free). The released constant-coefficient
solver `SparseHamiltonian.ODECompleteEndpoint.solver` (Theorem `ode:thm:main`) queries the
physical oracle family `ODEFinalNativeSource.physicalOracle D Nm Tsl d J₀ Jb` (with inverse
calls). It does not use the controlled call forms of that family, and they are not treated
here; controlled calls, padding and family forms over this oracle are in the library
`PhysicalODELowerBound`.

**Matrix labels.** Unfolded, a matrix label is one call of the native primitive
`NativeSparseBlockEncoding.oracles D l x` with fixed spectator registers and fixed register
relabellings, and nothing else (there is no time address):

* `ODECoordinateNativeControl.physicalOracle (Sum.inl l)` is the all-active mask over the source
  basis of the clean-control spectator of `matrixLayout.conj (matrixOracle D Nm Tsl d l x)`;
* `ODEFinalNativeSource.matrixOracle = AlignedMultiOracleProgram.oracle`, the constant diagonal
  over the alignment register `Bool`, of `ODEJointNative.oracle D Tsl d =
  NativeWholeProgramActive.oracle`, the all-active mask over the chronological cells of the
  clean-control spectator of `ODEJointNative.cayleyOracle D`;
* `ODEJointNative.cayleyOracle D l x` is the spectator over the coherent branch of
  `ODENativeCayley.oracle D l x` (`ODEJointNative.cayleyOracle_eq_spectator`), and
  `ODENativeCayley.oracle D l x = cayleyWrap n Z (oracles D l x)`
  (`ODELowerBoundExtensions.Release.cayleyOracle_eq_wrap`).

The outer layers are `constWrap` (`physicalOracle_inl_eq`), a spectator wrapper
(`isWrap_constWrap`, the combinators of `ODELowerBoundExtensions.Release.IsWrap`), so every matrix
label is `U⁻¹ (1_Ω ⊗ O_l(x)) U` for one fixed isometric identification `U` and the native
primitive `O = oracles D` (`physicalOracle_normal_form`).

**Source labels.** For public source interfaces the source labels do not depend on the input
(`physicalOracle_inr_const`).

`constWrap` and `physicalOracle_normal_form` are the counterparts, for the oracle
`ODEFinalNativeSource.physicalOracle` of `ODECompleteEndpoint.solver`, of
`ODELowerBoundExtensions.Release.outerWrap` and
`ODELowerBoundExtensions.Release.physicalOracle_normal_form`,
which are stated for the general-mesh oracle `ODELowerBoundExtensions.Release.releaseOracle`.
-/

namespace ConstantODELowerBound.Normal

noncomputable section
open SparseHamiltonian SparseLowerBounds NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Release (SysOp IsWrap)
open ConstantODELowerBound.Oracle (PublicConstSources)

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The fixed outer wrapper of the released constant-coefficient matrix labels** around the
native Cayley oracle: the source-sector mask and clean-control spectator
(`ODECoordinateNativeControl.physicalOracle`), the fixed coordinates
`ODEFinalNativeSource.matrixLayout`, the alignment diagonal `Bool`
(`AlignedMultiOracleProgram.oracle`), the chronological mask and clean-control spectator
(`NativeWholeProgramActive.oracle`) and the coherent-branch spectator
(`ODEJointNative.cayleyOracle`). -/
def constWrap (ι n Z : Type) [Fintype ι] [Fintype n] [Fintype Z] (Nm Tsl d : ℕ)
    (B : EuclideanSpace ℂ (ODENativeCayley.Basis n Z) →L[ℂ]
      EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) :
    ODEFinalNativeSource.Physical ι n Z Nm Tsl d →L[ℂ]
      ODEFinalNativeSource.Physical ι n Z Nm Tsl d :=
  MaskedProgram.masked (fun _ : ODEFinalNativeSource.SourceBasis ι n Nm => true)
    (LookupFromBasisOracle.spectator
      (S := (Bool × ODEFinalNativeSource.MatrixBasis ι n Z Nm Tsl d) ×
        ODEFinalNativeSource.MatrixBasis ι n Z Nm Tsl d)
      ((ODEFinalNativeSource.matrixLayout (ι := ι) (n := n) (Z := Z) Nm Tsl d).conjStarAlgEquiv
        (WeightedClock.diagonal (fun _ : Bool =>
          MaskedProgram.masked (fun _ : ActiveRegisterLayout.Label PUnit.{1} Tsl d => true)
            (LookupFromBasisOracle.spectator
              (S := (Bool × ODEJointNative.Basis (Option (Fin Nm) × ι) n Z) ×
                ODEJointNative.Basis (Option (Fin Nm) × ι) n Z)
              (LookupFromBasisOracle.spectator (S := Option (Fin Nm) × ι) B))))))

/-- `constWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_constWrap (ι n Z : Type) [Fintype ι] [Fintype n] [Fintype Z] (Nm Tsl d : ℕ) :
    IsWrap (constWrap ι n Z Nm Tsl d) :=
  (((((((ODELowerBoundExtensions.Release.isWrap_spectator (Option (Fin Nm) × ι)
    (ODENativeCayley.Basis n Z)).spectator
      (S := (Bool × ODEJointNative.Basis (Option (Fin Nm) × ι) n Z) ×
        ODEJointNative.Basis (Option (Fin Nm) × ι) n Z)).masked
    (ActiveRegisterLayout.Label PUnit.{1} Tsl d)).diagonalConst Bool).conj
      (ODEFinalNativeSource.matrixLayout (ι := ι) (n := n) (Z := Z) Nm Tsl d)).spectator
        (S := (Bool × ODEFinalNativeSource.MatrixBasis ι n Z Nm Tsl d) ×
          ODEFinalNativeSource.MatrixBasis ι n Z Nm Tsl d)).masked
    (ODEFinalNativeSource.SourceBasis ι n Nm))

omit [DecidableEq Z] in
/-- A matrix label of the released constant-coefficient oracle is `constWrap` of the native
Cayley oracle (definitional unfolding). -/
theorem physicalOracle_inl_eq (D : Data X n Z s) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp n) (l : Query) (x : X) :
    ODEFinalNativeSource.physicalOracle (ι := ι) D Nm Tsl d J₀ Jb (Sum.inl l) x =
      constWrap ι n Z Nm Tsl d (ODENativeCayley.oracle D l x) :=
  rfl

omit [DecidableEq Z] in
/-- **Normal form of the matrix labels**: for all native data `D`, every branch register `ι`,
mesh size, slot count, degree and source interfaces, there are a finite spectator register `Ω`
and a fixed isometric identification `U` of the released physical workspace with
`ℂ^Ω ⊗ (ℂ^{N×N} ⊗ ℂ^Z ⊗ flags)` such that every matrix label is `U⁻¹ (1_Ω ⊗ O_l(x)) U` with the
native primitive `O = oracles D`. -/
theorem physicalOracle_normal_form (D : Data X n Z s) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp n) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : ODEFinalNativeSource.Physical ι n Z Nm Tsl d ≃ₗᵢ[ℂ]
        Joint Ω (SparseFlagEmbedding.Space (n × n) Z)),
      ∀ l x, ODEFinalNativeSource.physicalOracle (ι := ι) D Nm Tsl d J₀ Jb (Sum.inl l) x =
        U.symm.conjStarAlgEquiv (Joint.fiber (fun _ : Ω => oracles D l x)) := by
  obtain ⟨Ω, _, U, hU⟩ :=
    (ODELowerBoundExtensions.Release.isWrap_cayleyWrap n Z).comp (isWrap_constWrap ι n Z Nm Tsl d)
  refine ⟨Ω, inferInstance, U, fun l x => ?_⟩
  rw [physicalOracle_inl_eq, ODELowerBoundExtensions.Release.cayleyOracle_eq_wrap]
  exact hU _

omit [DecidableEq Z] in
/-- **Source labels are input-independent** for public source interfaces. -/
theorem physicalOracle_inr_const (D : Data X n Z s) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp n} (hJ : PublicConstSources J₀ Jb) (b : Bool)
    (x x' : X) :
    ODEFinalNativeSource.physicalOracle (ι := ι) D Nm Tsl d J₀ Jb (Sum.inr b) x =
      ODEFinalNativeSource.physicalOracle (ι := ι) D Nm Tsl d J₀ Jb (Sum.inr b) x' := by
  have h0 : J₀ x = J₀ x' := hJ.initial_const x x'
  have hb : Jb x = Jb x' := congrFun (hJ.forcing_const x x') 0
  show ODESectorTensor.sourcePhysical _ = ODESectorTensor.sourcePhysical _
  simp only [ODEPrimitiveSourceJoin.sourceFamily, h0, hb]

end

end ConstantODELowerBound.Normal
