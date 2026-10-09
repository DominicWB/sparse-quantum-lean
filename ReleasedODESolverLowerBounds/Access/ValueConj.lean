import DeferredMeasurementLowerBounds.Access.TimeAccess

set_option autoImplicit false

/-!
# The inverse value call as a conjugated value call

Manuscript Section `odel:sec:main`, lines 3669-3673 (a reversible value oracle, "their inverses
and controls"). The native value primitive adds the entry word to the value register,
`|a, z⟩ ↦ |a, z + v_a⟩`; its inverse subtracts it, so it is the value call conjugated by the
known negation `z ↦ -z` of the value register.

* `negPrim N Z`: the negation of the value register of one native block, a known unitary
  (`negPrim_unitary`); the package's `DeferredMeasurementLowerBounds.Access.negValue` is its
  spectator lift over the time address (`negValue_eq_fiber`).
* `star_oracles_value`, `primValueConj`: for all native data, the inverse value call is
  `negPrim · value · negPrim†` (the primitive of the constant-coefficient released oracle).
* `star_labelOracle_value`, `labelValueConj`: the same for the one-branch sampled-time access
  of data with `M` pieces (the primitive of the general-mesh released oracle), with
  `negValue`; this is `DeferredMeasurementLowerBounds.Access.star_access_value` for data that
  are not the data of a family.
-/

namespace ReleasedODESolverLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Access (InverseConj negValue negValue_unitary)

variable {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- The negation `z ↦ -z` of the value register of one native block. -/
def negPrim (N Z : Type) [Fintype N] [Fintype Z] [AddCommGroup Z] :
    SparseFlagEmbedding.Space (N × N) Z →L[ℂ] SparseFlagEmbedding.Space (N × N) Z :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ SparseFlagEmbedding.Qutrit
    (Equiv.prodCongr (Equiv.refl (N × N)) (Equiv.neg Z))).toContinuousLinearEquiv.toContinuousLinearMap

omit [DecidableEq N] in
/-- The negation of one native block is unitary. -/
theorem negPrim_unitary : IsUnitary (negPrim N Z) := by
  have hs := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ SparseFlagEmbedding.Qutrit
    (Equiv.prodCongr (Equiv.refl (N × N)) (Equiv.neg Z))).star_eq_symm
  constructor
  · rw [negPrim]
    erw [hs]
    ext v ⟨a, z⟩
    simp
  · rw [negPrim]
    erw [hs]
    ext v ⟨a, z⟩
    simp

omit [DecidableEq N] in
/-- The package's negation of the sampled-time workspace is the spectator lift of `negPrim`. -/
theorem negValue_eq_fiber (Kt : ℕ) :
    negValue (N := N) (Z := Z) (Kt := Kt) = Joint.fiber fun _ => negPrim N Z := rfl

/-- **The inverse native value call is the value call conjugated by the negation.** -/
theorem star_oracles_value {Y : Type*} (D : Data Y N Z s) (y : Y) :
    star (oracles D .value y) = negPrim N Z * oracles D .value y * star (negPrim N Z) := by
  have hs := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ SparseFlagEmbedding.Qutrit
    (Equiv.prodCongr (Equiv.refl (N × N)) (Equiv.neg Z))).star_eq_symm
  rw [negPrim]
  erw [hs]
  ext Ψ ⟨a, z⟩ k
  rw [ContinuousLinearMap.star_eq_adjoint]
  change (ContinuousLinearMap.adjoint
    (LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) D.table y) Ψ) (a, z) k = _
  rw [LookupControlledGate.oracle_adjoint_apply]
  simp
  change _ = ((LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) D.table y)
    _ (a, -z)) k
  rw [LookupControlledGate.oracle_apply]
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, add_comm]

/-- The conjugation data of the native value primitive. -/
def primValueConj {Y : Type*} (D : Data Y N Z s) : InverseConj (oracles D) Query.value :=
  ⟨negPrim N Z, negPrim_unitary, star_oracles_value D⟩

/-- **The inverse value call of the one-branch sampled-time access is the value call conjugated
by the negation**, for data with `M` pieces. -/
theorem star_labelOracle_value {Y : Type*} {M : ℕ} (D : Data (Y × Fin M) N Z s) (y : Y) :
    star (TimeDependentODE.labelOracle (oracles D)
        (TimeDependentODE.sample (ι := Unit) (M := M)) .value y) =
      negValue * TimeDependentODE.labelOracle (oracles D)
        (TimeDependentODE.sample (ι := Unit) (M := M)) .value y * star negValue := by
  have hs := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ SparseFlagEmbedding.Qutrit
    (Equiv.prodCongr (Equiv.refl (N × N)) (Equiv.neg Z))).star_eq_symm
  rw [negValue, Joint.star_fiber]
  erw [hs]
  ext Ψ b ⟨a, z⟩ k
  rw [ContinuousLinearMap.star_eq_adjoint]
  change (ContinuousLinearMap.adjoint (TimeDependentODE.labelOracle (oracles D)
    (TimeDependentODE.sample (ι := Unit) (M := M)) .value y) Ψ) b (a, z) k = _
  rw [TimeDependentODE.labelOracle, WeightedClock.diagonal_adjoint,
    WeightedClock.diagonal_apply]
  change (ContinuousLinearMap.adjoint
    (LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) D.table _)
    (Ψ b)) (a, z) k = _
  rw [LookupControlledGate.oracle_adjoint_apply]
  simp
  change _ = ((LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) D.table
    (TimeDependentODE.sample y b)) _ (a, -z)) k
  rw [LookupControlledGate.oracle_apply]
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, add_comm]

/-- The conjugation data of the value label of the one-branch sampled-time access. -/
def labelValueConj {Y : Type*} {M : ℕ} (D : Data (Y × Fin M) N Z s) :
    InverseConj (TimeDependentODE.labelOracle (oracles D)
      (TimeDependentODE.sample (ι := Unit) (M := M))) Query.value :=
  ⟨negValue, negValue_unitary, star_labelOracle_value D⟩

end

end ReleasedODESolverLowerBounds.Access
