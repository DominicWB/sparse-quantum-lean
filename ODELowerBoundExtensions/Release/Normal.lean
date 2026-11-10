import ODELowerBoundExtensions.Release.Refine
import ODELowerBoundExtensions.Release.Registers
import TimeDependentExtensions.ODE.Source

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released ODE solver's physical oracle in normal form

Manuscript: Section `odel:sec:main` ("The value oracle and in-place row and column locators have
the canonical reversible access, including inverses, controls and coherent time addresses where
needed"). The released general-mesh
solver `TimeDependentExtensions.ODE.solver` is a protocol over the physical oracle family
`TimeDependentExtensions.MeshSource.physicalOracle D N d J₀ Jb`, labelled by
`NativeSparseBlockEncoding.Query ⊕ Bool`: matrix labels `Sum.inl l` and the two source interfaces
`Sum.inr false` (initial state `J₀`) and `Sum.inr true` (forcing `J_b`).

**Matrix labels.** Unfolded, a matrix label is one call of the coherent sampled-time native query
with fixed spectator registers and fixed register relabellings, and nothing else:

* `ODESectorNativeControl.physicalOracle (Sum.inl l) = NativeMaskedOracle.oracle (F l)`, the
  all-active mask (`masked_true_eq_fiber`) of `NativeControlledOracle.oracle`, a flattened
  spectator (`spectator_eq_conj_fiber`), of `F l x = eB.conj (MeshSource.matrixOracle D N d l x)`
  (`ODECoordinateNativeControl`, fixed coordinates `matrixLayout`);
* `MeshSource.matrixOracle = AlignedMultiOracleProgram.oracle` (the clean-output alignment
  spectator `Bool`, `diagonal_const_eq_fiber`) of `TimeDependentODE.oracle D N d =
  NativeWholeProgramActive.oracle` = `NativeMaskedProgram.oracle` over the chronological cells, of
  `TimeDependentODE.cayleyOracle D`;
* `cayleyOracle D l x = layout.conj (labelOracle (ODENativeCayley.oracle D) sample l x)`, and
  `ODENativeCayley.oracle D l y` is a fixed conjugated spectator
  (`FlatBranchNativeAccess.flatOracle`, `NativeMaskedProgram.oracle`,
  `NativeSparseMaskedAccess.flatOracle`) of the native primitive `oracles D l y`, the same for
  every `y`.

In Lean the two fixed layers are `cayleyWrap` (around the native primitive) and `outerWrap`
(around the coherent sampled-time query), both spectator wrappers (`IsWrap`, `Release/Registers`).
The time diagonal commutes with the fixed relabellings and spectators (`IsWrap.diagonal`), so
every matrix label is
`U⁻¹ (1_Ω ⊗ A_l(x)) U` for one fixed isometric identification `U` and the sampled-time access
`A = labelOracle (oracles D) sample` with branch register `Label ι M` (for the data of a family
this is `Family.access`) (`physicalOracle_normal_form`, for any data `D`). Boolean certificates
and weight growth of the sampled-time access therefore pass to the release's oracle with the same
per-label costs (`Release/Access`).

**The oracle on a family.** `meshOracle F σ` is the release's oracle on the data
`stageData F.data σ` of any public placement `σ` of mesh pieces into the stages of `F`;
`releaseOracle F R` is the uniform `R`-fold refinement `σ = stageOf K R` used by the released
runs (`Release/Instances`).

**Source labels.** On the hard families the source interfaces are public, input-independent
unitaries (`PublicSources`), so the source labels are input-independent
(`physicalOracle_inr_const`); unitarity of every label is the release's
`MeshSource.physicalOracle_unitary`.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit TimeDependentExtensions
open scoped InnerProduct InnerProductSpace

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- **Public source interfaces**: the initial-state and forcing preparations are unitary and do not
depend on the hidden input (Section `odel:sec:main`: "Initial and source preparations contain no
hidden information"). -/
structure PublicSources {X N : Type*} [Fintype N] {M : ℕ} (J₀ : X → SysOp N)
    (Jb : X → Fin M → SysOp N) : Prop where
  initial_unitary : ∀ x, IsUnitary (J₀ x)
  forcing_unitary : ∀ x r, IsUnitary (Jb x r)
  initial_const : ∀ x x', J₀ x = J₀ x'
  forcing_const : ∀ x x', Jb x = Jb x'

/-- **The release's physical oracle on a family along a placement** `σ : Fin M → Fin K` of `M`
mesh pieces into the stages: the oracle family of `TimeDependentExtensions.ODE.solver` run on
`stageData F.data σ` with `N` slots, degree `d`, spectator index `ι` and source interfaces `J₀`,
`J_b`. -/
abbrev meshOracle {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {K s : ℕ} (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι : Type*) [Fintype ι]
    (Nsl d : ℕ) (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N) :
    Query ⊕ Bool → X → MeshSource.PhysicalSpace ι N Z M Nsl d →L[ℂ]
      MeshSource.PhysicalSpace ι N Z M Nsl d :=
  MeshSource.physicalOracle (ι := ι) (stageData F.data σ) Nsl d J₀ Jb

/-- **The release's physical oracle on the `R`-fold refinement of a family**: `meshOracle` along
the uniform placement `stageOf K R`, i.e. `TimeDependentExtensions.ODE.solver` run on
`refineData F.data R`. -/
abbrev releaseOracle {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {K s : ℕ} (F : Family X N Z K s) (R : ℕ) (ι : Type*) [Fintype ι] (Nsl d : ℕ)
    (J₀ : X → SysOp N) (Jb : X → Fin (K * R) → SysOp N) :
    Query ⊕ Bool → X → MeshSource.PhysicalSpace ι N Z (K * R) Nsl d →L[ℂ]
      MeshSource.PhysicalSpace ι N Z (K * R) Nsl d :=
  meshOracle F (stageOf K R) ι Nsl d J₀ Jb

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M : ℕ}

/-- The fixed wrapper of the released native Cayley oracle around one native primitive:
`FlatBranchNativeAccess.flatOracle` over the branch `ODENativeLayout.Branch Z` (all-active mask,
controlled-call spectators) of `NativeSparseMaskedAccess.flatOracle` (fixed flattening), so that
`ODENativeCayley.oracle D l y = cayleyWrap n Z (oracles D l y)` (`cayleyOracle_eq_wrap`). -/
def cayleyWrap (n Z : Type) [Fintype n] [Fintype Z]
    (A : SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z) :
    EuclideanSpace ℂ (ODENativeCayley.Basis n Z) →L[ℂ]
      EuclideanSpace ℂ (ODENativeCayley.Basis n Z) :=
  (FlatBranchNativeAccess.layout (ι := ODENativeLayout.Branch Z)
      (B := NativeSparseMaskedAccess.Basis n Z)).conjStarAlgEquiv
    (MaskedProgram.masked (fun _ : ODENativeLayout.Branch Z => true)
      (LookupFromBasisOracle.spectator
        (S := (Bool × NativeSparseMaskedAccess.Basis n Z) × NativeSparseMaskedAccess.Basis n Z)
        ((NativeSparseMaskedAccess.layout (n := n) (Z := Z)).conjStarAlgEquiv A)))

/-- `cayleyWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_cayleyWrap (n Z : Type) [Fintype n] [Fintype Z] : IsWrap (cayleyWrap n Z) :=
  (((isWrap_spectator _ _).precomp (NativeSparseMaskedAccess.layout (n := n) (Z := Z))).masked
    (ODENativeLayout.Branch Z)).conj
    (FlatBranchNativeAccess.layout (ι := ODENativeLayout.Branch Z)
      (B := NativeSparseMaskedAccess.Basis n Z))

omit [DecidableEq Z] in
/-- The released native Cayley oracle is `cayleyWrap` of the native primitive. -/
theorem cayleyOracle_eq_wrap {Y : Type} (D : Data Y n Z s) (l : Query) (y : Y) :
    ODENativeCayley.oracle D l y = cayleyWrap n Z (oracles D l y) := rfl

/-- The fixed outer wrapper of the release's matrix labels around the coherent sampled-time
Cayley query: the source-sector spectators (`ODESectorNativeControl.physicalOracle`), the fixed
coordinates `MeshSource.matrixLayout`, the clean-output alignment spectator `Bool`
(`AlignedMultiOracleProgram.oracle`), the chronological cells
(`NativeWholeProgramActive.oracle`) and the layout of `TimeDependentODE.cayleyOracle`. -/
def outerWrap (ι n Z : Type) [Fintype ι] [Fintype n] [Fintype Z] (M N d : ℕ)
    (B : Joint (TimeDependentODE.NativeSource.Label ι M × Fin M)
        (EuclideanSpace ℂ (ODENativeCayley.Basis n Z)) →L[ℂ]
      Joint (TimeDependentODE.NativeSource.Label ι M × Fin M)
        (EuclideanSpace ℂ (ODENativeCayley.Basis n Z))) :
    MeshSource.PhysicalSpace ι n Z M N d →L[ℂ] MeshSource.PhysicalSpace ι n Z M N d :=
  MaskedProgram.masked (fun _ : TimeDependentODE.NativeSource.SourceBasis ι n M => true)
    (LookupFromBasisOracle.spectator
      (S := (Bool × MeshSource.MatrixBasis ι n Z M N d) × MeshSource.MatrixBasis ι n Z M N d)
      ((MeshSource.matrixLayout (ι := ι) (n := n) (Z := Z) M N d).conjStarAlgEquiv
        (WeightedClock.diagonal (fun _ : Bool =>
          MaskedProgram.masked (fun _ : ActiveRegisterLayout.Label PUnit.{1} N d => true)
            (LookupFromBasisOracle.spectator
              (S := (Bool × TimeDependentODE.Basis (TimeDependentODE.NativeSource.Label ι M) n Z M)
                × TimeDependentODE.Basis (TimeDependentODE.NativeSource.Label ι M) n Z M)
              ((TimeDependentODE.layout (ι := TimeDependentODE.NativeSource.Label ι M) (M := M)
                (n := n) (Z := Z)).conjStarAlgEquiv B))))))

/-- `outerWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_outerWrap (ι n Z : Type) [Fintype ι] [Fintype n] [Fintype Z] (M N d : ℕ) :
    IsWrap (outerWrap ι n Z M N d) :=
  ((((((isWrap_spectator _ _).precomp
    (TimeDependentODE.layout (ι := TimeDependentODE.NativeSource.Label ι M) (M := M)
      (n := n) (Z := Z))).masked (ActiveRegisterLayout.Label PUnit.{1} N d)).diagonalConst
        Bool).conj (MeshSource.matrixLayout (ι := ι) (n := n) (Z := Z) M N d)).spectator
          (S := (Bool × MeshSource.MatrixBasis ι n Z M N d) ×
            MeshSource.MatrixBasis ι n Z M N d)).masked
    (TimeDependentODE.NativeSource.SourceBasis ι n M)

omit [DecidableEq Z] in
/-- A matrix label of the release's physical oracle is `outerWrap` of the coherent sampled-time
native Cayley query. -/
theorem physicalOracle_inl_eq (D : Data (X × Fin M) n Z s) (ι : Type) [Fintype ι]
    [DecidableEq ι] (N d : ℕ) (J₀ : X → SysOp n) (Jb : X → Fin M → SysOp n) (l : Query)
    (x : X) :
    MeshSource.physicalOracle (ι := ι) D N d J₀ Jb (Sum.inl l) x =
      outerWrap ι n Z M N d (TimeDependentODE.labelOracle (ODENativeCayley.oracle D)
        (TimeDependentODE.sample (ι := TimeDependentODE.NativeSource.Label ι M) (M := M)) l x) :=
  rfl

omit [DecidableEq Z] in
/-- **Normal form of the matrix labels**: for all sampled-time data `D` with `M` pieces, every
spectator index `ι`, slot count `N`, degree `d` and source interfaces, there are a finite
spectator register `Ω` and a fixed isometric identification `U` of the release's physical
workspace with `ℂ^Ω ⊗ Workspace (Label ι M)` such that every matrix label is
`U⁻¹ (1_Ω ⊗ A_l(x)) U`, where `A = labelOracle (oracles D) sample` is the sampled-time access
with branch register `Label ι M` (`Family.access` when `D` is the data of a family). -/
theorem physicalOracle_normal_form (D : Data (X × Fin M) n Z s) (ι : Type) [Fintype ι]
    [DecidableEq ι] (N d : ℕ) (J₀ : X → SysOp n) (Jb : X → Fin M → SysOp n) :
    ∃ (Ω : Type) (_ : Fintype Ω)
      (U : MeshSource.PhysicalSpace ι n Z M N d ≃ₗᵢ[ℂ]
        Joint Ω (Workspace (TimeDependentODE.NativeSource.Label ι M) n Z M)),
      ∀ l x, MeshSource.physicalOracle (ι := ι) D N d J₀ Jb (Sum.inl l) x =
        U.symm.conjStarAlgEquiv (Joint.fiber (fun _ : Ω =>
          TimeDependentODE.labelOracle (oracles D)
            (TimeDependentODE.sample (ι := TimeDependentODE.NativeSource.Label ι M) (M := M))
            l x)) := by
  obtain ⟨Ω₂, _, U₂, hU₂⟩ :=
    (isWrap_cayleyWrap n Z).diagonal (TimeDependentODE.NativeSource.Label ι M × Fin M)
  obtain ⟨Ω, _, U, hU⟩ := ((isWrap_fiber Ω₂).conj U₂.symm).comp (isWrap_outerWrap ι n Z M N d)
  refine ⟨Ω, inferInstance, U, fun l x => ?_⟩
  have e₂ := hU₂ (fun b => oracles D l
    (TimeDependentODE.sample (ι := TimeDependentODE.NativeSource.Label ι M) (M := M) x b))
  have e₁ := hU (TimeDependentODE.labelOracle (oracles D)
    (TimeDependentODE.sample (ι := TimeDependentODE.NativeSource.Label ι M) (M := M)) l x)
  rw [physicalOracle_inl_eq]
  refine Eq.trans ?_ e₁
  exact congrArg (outerWrap ι n Z M N d) e₂

omit [DecidableEq Z] in
/-- **Source labels are input-independent** for public source interfaces. -/
theorem physicalOracle_inr_const (D : Data (X × Fin M) n Z s) (ι : Type) [Fintype ι]
    [DecidableEq ι] (N d : ℕ) {J₀ : X → SysOp n} {Jb : X → Fin M → SysOp n}
    (hJ : PublicSources J₀ Jb) (b : Bool) (x x' : X) :
    MeshSource.physicalOracle (ι := ι) D N d J₀ Jb (Sum.inr b) x =
      MeshSource.physicalOracle (ι := ι) D N d J₀ Jb (Sum.inr b) x' := by
  show ODESectorTensor.sourcePhysical _ = ODESectorTensor.sourcePhysical _
  simp only [TimeDependentODE.SourceTD.sourceFamily, hJ.initial_const x x',
    hJ.forcing_const x x']

end

end ODELowerBoundExtensions.Release
