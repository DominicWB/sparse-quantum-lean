import SparseHamiltonian.UnitaryImplementation
import UnitaryImplementationExtensions.PhaseBridge
import GeneralODE.Block.Registers

set_option autoImplicit false

/-!
# The released entry oracle of one-bit data is a Boolean phase oracle

Corollary `hs:cor:unitary` of the manuscript (line 1837: the entry oracle of
the search family uses one query to the search oracle). The entry oracle of the
unitary-implementation corollary,
`SparseHamiltonian.UnitaryEntryOracle.oracle D γ η t ε x`, is one ordinary
reversible lookup of the table of `D`, put into the simulator's workspace by a
fixed coordinate change (`NativeSparseMaskedAccess.layout`) and the spectator
map `UnitaryEntryOracle.lift`. Both are unital star-algebra homomorphisms of
operator algebras (`layoutHom`, `liftHom`): they only tensor with identities,
take direct sums of copies and conjugate by fixed unitaries; the copies and the
spectator factors are the package's homomorphisms
`SparseHamiltonian.GeneralODE.Registers.diagHom` and
`SparseHamiltonian.GeneralODE.Registers.specHom`. Hence, for one-bit
values (`Z = ZMod 2`), the released entry oracle is the phase oracle of the
image of the XOR family (`entryFamily`), for the Boolean string
`a ↦ (plainTable D x a = 1)` (`oracle_eq_phase`). Lower bounds for Boolean phase
oracles therefore apply to the oracle model of the upper bound itself, with
the same query count. The transport is an exact identity of operators, in the
form of `PhaseBridge.phase_map`; it complements the cost-bounded certificates
`SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess`, which are built for the
release simulator's labelled oracle rather than for `UnitaryEntryOracle.lift`.
-/

namespace UnitaryImplementationExtensions.LiftPhase

noncomputable section
open SparseHamiltonian SparseLowerBounds
open ContinuousLinearMap OracleCircuit UnitaryEntryData
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectator map of the released entry oracle as a composite of unital
star-algebra homomorphisms. -/
def liftStar (γ η t ε : ℝ) :
    (EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2)) →L[ℂ]
      EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2))) →⋆ₐ[ℂ]
    (UnitaryEntryOracle.Physical n (ZMod 2) γ η t ε →L[ℂ]
      UnitaryEntryOracle.Physical n (ZMod 2) γ η t ε) :=
  (GeneralODE.Registers.diagHom Bool _).comp ((GeneralODE.Registers.diagHom Bool _).comp
    ((GeneralODE.Registers.diagHom (ActiveRegisterLayout.Label PUnit.{1}
          (ImprovedNativeSimulation.slots (Fintype.card n : ℝ) γ (η * |t|) ε)
          (ImprovedNativeSimulation.degree (Fintype.card n : ℝ) γ (η * |t|) ε)) _).comp
      ((GeneralODE.Registers.specHom ((Bool × NativeCayleyProgram.Basis (Index n) (ZMod 2)) ×
            NativeCayleyProgram.Basis (Index n) (ZMod 2)) _).comp
        ((NativeDilationLayout.layout
            (B := UnitaryEntryOracle.Base n (ZMod 2))).conjStarAlgEquiv.toStarAlgHom.comp
          ((GeneralODE.Registers.diagHom Bool _).comp
            (GeneralODE.Registers.specHom ((Bool × UnitaryEntryOracle.Base n (ZMod 2)) ×
              UnitaryEntryOracle.Base n (ZMod 2)) _))))))

omit [DecidableEq n] in
/-- `UnitaryEntryOracle.lift` agrees with the composite `liftStar`. -/
theorem lift_eq_liftStar (γ η t ε : ℝ)
    (F : EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2)) →L[ℂ]
      EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2))) :
    UnitaryEntryOracle.lift γ η t ε F = liftStar γ η t ε F :=
  rfl

/-- The spectator map of the released entry oracle, as a unital star-algebra
homomorphism. -/
def liftHom (γ η t ε : ℝ) :
    (EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2)) →L[ℂ]
      EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2))) →⋆ₐ[ℂ]
    (UnitaryEntryOracle.Physical n (ZMod 2) γ η t ε →L[ℂ]
      UnitaryEntryOracle.Physical n (ZMod 2) γ η t ε) where
  toFun := UnitaryEntryOracle.lift γ η t ε
  map_one' := by
    rw [lift_eq_liftStar]
    exact map_one _
  map_mul' := UnitaryEntryOracle.lift_mul γ η t ε
  map_zero' := by
    rw [lift_eq_liftStar]
    exact map_zero _
  map_add' U V := by
    rw [lift_eq_liftStar, lift_eq_liftStar, lift_eq_liftStar]
    exact map_add _ U V
  commutes' c := by
    rw [lift_eq_liftStar]
    exact AlgHomClass.commutes _ c
  map_star' F := by
    rw [lift_eq_liftStar, lift_eq_liftStar]
    exact map_star _ F

omit [DecidableEq n] in
/-- The star-algebra homomorphism `liftHom` evaluates to the released spectator
map `UnitaryEntryOracle.lift`. -/
@[simp] theorem liftHom_apply (γ η t ε : ℝ)
    (F : EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2)) →L[ℂ]
      EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2))) :
    liftHom γ η t ε F = UnitaryEntryOracle.lift γ η t ε F :=
  rfl

/-- The fixed released coordinate change of the entry register. -/
def layoutHom :
    (SparseFlagEmbedding.Space (Index n × Index n) (ZMod 2) →L[ℂ]
      SparseFlagEmbedding.Space (Index n × Index n) (ZMod 2)) →⋆ₐ[ℂ]
    (EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2)) →L[ℂ]
      EuclideanSpace ℂ (UnitaryEntryOracle.Base n (ZMod 2))) :=
  (NativeSparseMaskedAccess.layout (n := Index n) (Z := ZMod 2)).conjStarAlgEquiv.toStarAlgHom

/-- The projection family of the released entry oracle on the simulator's
workspace, indexed by flagged entry addresses. -/
def entryFamily (γ η t ε : ℝ) :
    ProjFamily (UnitaryEntryOracle.Physical n (ZMod 2) γ η t ε) (Index n × Index n) :=
  PhaseBridge.mapFamily ((liftHom γ η t ε).comp layoutHom)
    (PhaseBridge.xorFamily (Index n × Index n) SparseFlagEmbedding.Qutrit)

/-- **The released entry oracle of one-bit data is a phase oracle.** -/
theorem oracle_eq_phase {X : Type*} (D : UnitaryEntryData.Data X n (ZMod 2))
    (γ η t ε : ℝ) (x : X) :
    UnitaryEntryOracle.oracle D γ η t ε x =
      (entryFamily γ η t ε).phase
        (fun a => decide (UnitaryEntryOracle.plainTable D x a = 1)) := by
  change ((liftHom γ η t ε).comp layoutHom) (LookupControlledGate.oracle
    (K := SparseFlagEmbedding.Qutrit) (UnitaryEntryOracle.plainTable D) x) = _
  rw [PhaseBridge.lookup_eq_phase]
  exact PhaseBridge.phase_map
    (K := PiLp 2 (fun _ : (Index n × Index n) × ZMod 2 => SparseFlagEmbedding.Qutrit))
    (K' := UnitaryEntryOracle.Physical n (ZMod 2) γ η t ε)
    ((liftHom γ η t ε).comp layoutHom) _ _

end
end UnitaryImplementationExtensions.LiftPhase
