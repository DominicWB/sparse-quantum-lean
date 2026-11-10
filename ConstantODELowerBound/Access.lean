import ConstantODELowerBound.Normal
import ODELowerBoundExtensions.Release.Access

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released constant-coefficient oracle on hard data: search-weight growth

Section `odel:sec:main` (access model; public location
lists, public source preparation, all unknown information in exact finite-word entries). For
native data `D` whose locators are input-independent and whose table entries are one-bit
functions of a one-hot input (`AdaptiveHamiltonianLowerBound.Access.HardAccess D g`), the
released constant-coefficient solver's physical oracle on `D` has search-weight growth with the
value-query weight `ODESourceQueryBudget.matrixWeight valueWeight` (`valueWeight` on matrix
labels, `0` on source labels) along `g` (`searchGrowth_const`):

* matrix labels are `U⁻¹ (1_Ω ⊗ O_l(x)) U` with the native primitive `O = oracles D`
  (`Normal.physicalOracle_normal_form`), i.e. the conjugated spectated access
  `specOracles Ω D`, admissible with `valueWeight`
  (`AdaptiveHamiltonianLowerBound.Access.admissible_specOracles`), hence of search-weight growth
  (`AdaptiveHamiltonianLowerBound.searchGrowth_admissible`), and growth passes through fixed
  isometries (`AdaptiveHamiltonianLowerBound.wgrowth_conj`);
* public source labels are input-independent unitaries (`Normal.physicalOracle_inr_const`),
  of growth `1` (`AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq`).

`searchGrowth_const_ham` and `searchGrowth_const_heat` are the instances on `constOracle` of the
`g = 1` families and of the heat families. `searchGrowth_const` is the counterpart, for the oracle
`ODEFinalNativeSource.physicalOracle` of `ODECompleteEndpoint.solver`, of
`ODELowerBoundExtensions.Release.searchGrowth_release_ham`, which is stated for the general-mesh
oracle `ODELowerBoundExtensions.Release.releaseOracle`.
-/

namespace ConstantODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open ODELowerBoundExtensions.Release (SysOp)
open ODELowerBoundExtensions.Psd (heatFamily)
open AdaptiveHamiltonianLowerBound (SearchGrowth)
open AdaptiveHamiltonianLowerBound.Access (HardAccess valueWeight)
open ConstantODELowerBound.Oracle

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

/-- **The released constant-coefficient oracle has search-weight growth** on data with
input-independent locators and one-bit entries along `g`, with the value-query weight
`matrixWeight valueWeight`, for every branch register, mesh size, slot count, degree and public
source interfaces. -/
theorem searchGrowth_const {n m : ℕ} (hm : Even m) {X N Z : Type} [Fintype N] [DecidableEq N]
    [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb) :
    SearchGrowth m
      (fun l j => ODEFinalNativeSource.physicalOracle (ι := ι) D Nm Tsl d J₀ Jb l (g j))
      (ODESourceQueryBudget.matrixWeight valueWeight) := by
  intro a ha l
  rcases l with q | b
  · obtain ⟨Ω, _, U, hU⟩ := Normal.physicalOracle_normal_form D ι Nm Tsl d J₀ Jb
    have hspec : SearchGrowth m (fun (q : Query) j => specOracles Ω D q (g j)) valueWeight :=
      AdaptiveHamiltonianLowerBound.searchGrowth_admissible hm D g hD _ _
        (fun q => AdaptiveHamiltonianLowerBound.Access.admissible_specOracles _ D hD.row_const
          hD.column_const q)
    obtain ⟨h1, h2⟩ := hspec a ha q
    have heq : ∀ j, ODEFinalNativeSource.physicalOracle (ι := ι) D Nm Tsl d J₀ Jb (Sum.inl q)
        (g j) = U.symm.conjStarAlgEquiv (specOracles Ω D q (g j)) := fun j => hU q (g j)
    refine ⟨AdaptiveHamiltonianLowerBound.wgrowth_congr
        (AdaptiveHamiltonianLowerBound.wgrowth_conj _ U.symm _ _ h1) (fun j => (heq j).symm),
      AdaptiveHamiltonianLowerBound.wgrowth_congr
        (AdaptiveHamiltonianLowerBound.wgrowth_conj _ U.symm _ _ h2) (fun j => ?_)⟩
    beta_reduce
    rw [heq j, ← map_star]
  · have hu := ODEFinalNativeSource.physicalOracle_unitary (ι := ι) D Nm Tsl d J₀ Jb
      hJ.initial_unitary (fun x => hJ.forcing_unitary x 0) (Sum.inr b)
    have hc := Normal.physicalOracle_inr_const D ι Nm Tsl d hJ b
    show AdaptiveHamiltonianLowerBound.WGrowth _ _
        ((AdaptiveHamiltonianLowerBound.searchLam m a ^ 2) ^ 0) ∧
      AdaptiveHamiltonianLowerBound.WGrowth _ _
        ((AdaptiveHamiltonianLowerBound.searchLam m a ^ 2) ^ 0)
    rw [pow_zero]
    refine ⟨AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq _ _
        (fun j j' => hc (g j) (g j'))
        (fun j v => LinearSystemLowerBound.isUnitary_norm (hu (g j)) v),
      AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq _ _
        (fun j j' => by beta_reduce; rw [hc (g j) (g j')])
        (fun j v => LinearSystemLowerBound.isUnitary_norm (hu (g j)).adjoint v)⟩

/-- **Search-weight growth on a `g = 1` family**: the released oracle `constOracle` of
`hamFamily D T x₀`, for data `D` with the access conditions along `g`. -/
theorem searchGrowth_const_ham {n m : ℕ} (hm : Even m) {X N Z : Type} [Fintype N]
    [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g) (T : ℝ) (hT : 0 ≤ T)
    (x₀ : EuclideanSpace ℂ N) (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ)
    {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb) :
    SearchGrowth m (fun l j => constOracle (hamFamily D T hT x₀) ι Nm Tsl d J₀ Jb l (g j))
      (ODESourceQueryBudget.matrixWeight valueWeight) :=
  searchGrowth_const hm _ g (hardAccess_constData_ham D g hD T hT x₀) ι Nm Tsl d hJ

/-- **Search-weight growth on a heat family**: the released oracle `constOracle` of
`heatFamily D T x₀`, for data `D` with the access conditions along `g`. -/
theorem searchGrowth_const_heat {n m : ℕ} (hm : Even m) {X N Z : Type} [Fintype N]
    [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X N Z s)
    (g : (Fin n → Fin m) → X) (hD : HardAccess D g) (T : ℝ) (hT : 0 ≤ T)
    (x₀ : EuclideanSpace ℂ N) (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ)
    {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb) :
    SearchGrowth m (fun l j => constOracle (heatFamily D T hT x₀) ι Nm Tsl d J₀ Jb l (g j))
      (ODESourceQueryBudget.matrixWeight valueWeight) :=
  searchGrowth_const hm _ g (hardAccess_constData_heat D g hD T hT x₀) ι Nm Tsl d hJ

end

end ConstantODELowerBound.Access
