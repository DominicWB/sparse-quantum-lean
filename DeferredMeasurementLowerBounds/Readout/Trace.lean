import LinearSystemLowerBound.Weight.PartialTrace
import SparseLowerBounds.Query.Joint

set_option autoImplicit false

/-!
# Partial traces with a classical record register

The accuracy notion of Theorem `qlsl:thm:main` (manuscript eq. `qlsl:eq:target`) identifies the
output space `E` with output register ⊗ finite garbage by an isometric equivalence
`V : E ≃ ℂ^{I × G}` and bounds the trace distance of the partial trace over `G`. For the deferred
output `a : Joint J E` (records `J`), `liftEquiv J V` identifies `Joint J E` with `ℂ^{I × (G × J)}`:
the record register joins the garbage, and the partial trace of the pure deferred output is the
partial trace of the record-discarded mixture (`ptrace_liftEquiv`), with any common normalisation.
-/

namespace DeferredMeasurementLowerBounds.Readout

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian ContinuousLinearMap SparseLowerBounds LinearSystemLowerBound

variable {E J I G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- **The identification of the deferred output space** with output register ⊗ garbage ⊗
records. -/
def liftEquiv (J : Type*) [Fintype J] (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × G)) :
    Joint J E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × (G × J)) :=
  ((LinearIsometryEquiv.piLpCongrRight 2 fun _ : J => V).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : J) (_ : I × G) => ℂ)).symm).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      ((Equiv.sigmaEquivProd J (I × G)).trans
        ((Equiv.prodComm J (I × G)).trans (Equiv.prodAssoc I G J))))

omit [CompleteSpace E] [DecidableEq J] [DecidableEq I] [DecidableEq G] in
/-- Coordinates of the identification. -/
theorem liftEquiv_apply (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × G)) (a : Joint J E) (i : I) (g : G)
    (j : J) : liftEquiv J V a (i, (g, j)) = V (a j) (i, g) := rfl

omit [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] in
/-- An isometric identification carries a pure output to the pure output of the image. -/
theorem conjStarAlgEquiv_pureOperator {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (W : E ≃ₗᵢ[ℂ] K) (a : E) :
    W.conjStarAlgEquiv (ODEMixedOutput.pureOperator a) = ODEMixedOutput.pureOperator (W a) := by
  ext y
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, ODEMixedOutput.pureOperator,
    ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply,
    InnerProductSpace.rankOne_apply, map_smul, ← LinearIsometryEquiv.inner_map_map W a,
    LinearIsometryEquiv.apply_symm_apply]

omit [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] in
/-- Entries of a normalised pure output. -/
theorem entry_smul_pure {K : Type*} [Fintype K] [DecidableEq K] (c : ℂ)
    (y : EuclideanSpace ℂ K) (x z : K) :
    entry (c • ODEMixedOutput.pureOperator y) x z = c * (y x * (starRingEnd ℂ) (y z)) := by
  rw [← entry_pure y x z]
  rfl

omit [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] in
/-- Entries of a normalised mixture of pure outputs. -/
theorem entry_smul_sum_pure {K : Type*} [Fintype K] [DecidableEq K] (c : ℂ)
    (y : J → EuclideanSpace ℂ K) (x z : K) :
    entry (c • ∑ j, ODEMixedOutput.pureOperator (y j)) x z =
      c * ∑ j, y j x * (starRingEnd ℂ) (y j z) := by
  rw [entry, _root_.smul_apply, _root_.sum_apply, PiLp.smul_apply,
    piLp_sum_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => entry_pure (y j) x z

/-- **Discarding the records is a partial trace**: the reduced output of the pure deferred
output equals the reduced output of the record-discarded mixture, with any normalisation. -/
theorem ptrace_liftEquiv [FiniteDimensional ℂ E] (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × G))
    (a : Joint J E) (c : ℂ) :
    ptrace ((liftEquiv J V).conjStarAlgEquiv (c • ODEMixedOutput.pureOperator a)) =
      ptrace (V.conjStarAlgEquiv (c • ∑ j, ODEMixedOutput.pureOperator (a j))) := by
  refine ext_entry fun i i' => ?_
  rw [entry_ptrace, entry_ptrace, map_smul, map_smul, map_sum, conjStarAlgEquiv_pureOperator]
  simp_rw [conjStarAlgEquiv_pureOperator, entry_smul_pure, entry_smul_sum_pure,
    Fintype.sum_prod_type, liftEquiv_apply, Finset.mul_sum]

end

end DeferredMeasurementLowerBounds.Readout
