import ODELowerBoundExtensions.Release.Normal
import ODELowerBoundExtensions.Psd.Family
import AdaptiveHamiltonianLowerBound.Cost
import SparseODE.ODECompleteSuccess

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released constant-coefficient ODE solver's oracle on a one-stage family

Manuscript lines 4114-4115 ("The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`") and Theorem `ode:thm:main` (lines 3013-3033). The released constant-coefficient
solver `SparseHamiltonian.ODECompleteEndpoint.solver` takes native sparse data
`Data X N Z s` without a time address (generator `-D.matrix x`,
`ODEPublicSourceMesh.generator`) and runs a four-attempt protocol over the physical oracle family
`ODEFinalNativeSource.physicalOracle (ι := ι) D Nm Tsl d J₀ Jb`, labelled by `Query ⊕ Bool`
(matrix calls and the two source interfaces), with branch register `ι`, mesh size `Nm`, slot
count `Tsl` and degree `d`.

The hard constant-coefficient families of the lower bounds are one-stage families of the ODE
model (`SparseLowerBounds.ODE.Family X N Z 1 s`): the `g = 1` Hamiltonian families
(`hamFamily`, generator `iH`) and the positive semidefinite families (`heatFamily`, generator
`D_X`).

* `constData F`: the stage-`0` data of a one-stage family, the input of the released solver
  (`ODELowerBoundExtensions.Release.reindexData` along `x ↦ (x, 0)`).
* `constOracle F ι Nm Tsl d J₀ Jb`: the released solver's physical oracle on `constData F`.
* `PublicConstSources J₀ Jb`: the source interfaces are unitary and input-independent (lines
  4121-4122, "Initial and source preparation contain no hidden input information"); the predicate
  `ODELowerBoundExtensions.Release.PublicSources` with one forcing piece.
* The native primitives of `constData` of the two kinds of families are those of the underlying
  data (`oracles_constData_ham`, `oracles_constData_heat`), so the access conditions of the
  adaptive Hamiltonian lower bound transfer (`hardAccess_constData_ham`,
  `hardAccess_constData_heat`).
-/

namespace ConstantODELowerBound.Oracle

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open ODELowerBoundExtensions.Release (SysOp reindexData)
open ODELowerBoundExtensions.Psd (heatFamily)
open AdaptiveHamiltonianLowerBound.Access (HardAccess)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192

variable {X N Z : Type} [Fintype N] [DecidableEq N] {s : ℕ}

/-- **The constant-coefficient data of a one-stage family**: the sampled-time data read at the
single stage `0` (same words, decoder and locators). This is the input of the released
constant-coefficient solver. -/
def constData (F : Family X N Z 1 s) : Data X N Z s :=
  reindexData F.data (fun x => (x, 0))

/-- The matrix of `constData F` is the stage-`0` generator matrix. -/
@[simp] theorem constData_matrix (F : Family X N Z 1 s) (x : X) :
    (constData F).matrix x = F.data.matrix (x, 0) := rfl

/-- The native primitives of `constData F` are those of the family's data at stage `0`. -/
theorem oracles_constData [Fintype Z] [AddCommGroup Z] (F : Family X N Z 1 s) (l : Query)
    (x : X) : oracles (constData F) l x = oracles F.data l (x, 0) :=
  ODELowerBoundExtensions.Release.oracles_reindexData _ _ l x

/-- On a `g = 1` family the native primitives of `constData` are those of the Hamiltonian
data. -/
theorem oracles_constData_ham [Fintype Z] [AddCommGroup Z] (D : Data X N Z s) (T : ℝ)
    (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N) (l : Query) (x : X) :
    oracles (constData (hamFamily D T hT x₀)) l x = oracles D l x := by
  cases l <;> rfl

/-- On a heat family the native primitives of `constData` are those of the data. -/
theorem oracles_constData_heat [Fintype Z] [AddCommGroup Z] (D : Data X N Z s) (T : ℝ)
    (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N) (l : Query) (x : X) :
    oracles (constData (heatFamily D T hT x₀)) l x = oracles D l x := by
  cases l <;> rfl

/-- The access conditions of the adaptive Hamiltonian lower bound pass to `constData` of a
`g = 1` family (same words and locators). -/
theorem hardAccess_constData_ham [Fintype Z] [AddCommGroup Z] {n m : ℕ} (D : Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g) (T : ℝ) (hT : 0 ≤ T)
    (x₀ : EuclideanSpace ℂ N) : HardAccess (constData (hamFamily D T hT x₀)) g :=
  ⟨hD.row_const, hD.column_const, hD.table_bit⟩

/-- The access conditions pass to `constData` of a heat family. -/
theorem hardAccess_constData_heat [Fintype Z] [AddCommGroup Z] {n m : ℕ} (D : Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g) (T : ℝ) (hT : 0 ≤ T)
    (x₀ : EuclideanSpace ℂ N) : HardAccess (constData (heatFamily D T hT x₀)) g :=
  ⟨hD.row_const, hD.column_const, hD.table_bit⟩

/-- **Public source interfaces of the constant-coefficient solver**: the initial-state and
forcing preparations are unitary and independent of the hidden input (lines 4121-4122); the
package's `PublicSources` with a single forcing piece. -/
abbrev PublicConstSources (J₀ Jb : X → SysOp N) : Prop :=
  ODELowerBoundExtensions.Release.PublicSources J₀ (fun x (_ : Fin 1) => Jb x)

/-- **The released constant-coefficient solver's physical oracle on a one-stage family**: the
oracle family of `ODECompleteEndpoint.solver` run on `constData F` with branch register `ι`,
mesh size `Nm`, slot count `Tsl`, degree `d` and source interfaces `J₀`, `Jb`. The released
run uses `ι = Fin gridSize ⊕ Bool` and `Nm = meshSize`. -/
abbrev constOracle [Fintype Z] [AddCommGroup Z] [DecidableEq Z] (F : Family X N Z 1 s)
    (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N) :
    Query ⊕ Bool → X → ODEFinalNativeSource.Physical ι N Z Nm Tsl d →L[ℂ]
      ODEFinalNativeSource.Physical ι N Z Nm Tsl d :=
  ODEFinalNativeSource.physicalOracle (ι := ι) (constData F) Nm Tsl d J₀ Jb

/-- Every label of the released oracle is unitary for public source interfaces. -/
theorem constOracle_unitary [Fintype Z] [AddCommGroup Z] [DecidableEq Z] (F : Family X N Z 1 s)
    (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp N}
    (hJ : PublicConstSources J₀ Jb) (l : Query ⊕ Bool) (x : X) :
    IsUnitary (constOracle F ι Nm Tsl d J₀ Jb l x) :=
  ODEFinalNativeSource.physicalOracle_unitary (ι := ι) _ _ _ _ _ _ hJ.initial_unitary
    (fun x => hJ.forcing_unitary x 0) l x

end

end ConstantODELowerBound.Oracle
