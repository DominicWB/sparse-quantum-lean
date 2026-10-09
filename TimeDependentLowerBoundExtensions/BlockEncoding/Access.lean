import TimeDependentLowerBoundExtensions.BlockEncoding.Hard

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Boolean certificates of the time-indexed block-encoding oracles on the hard instances

Every call of the controlled time-indexed block-encoding oracle
(`TimeDependentExtensions.BlockEncoding.primitive`, `|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`) of the
constant family `beConst D M` is one controlled call of `beOp D x`, the Hermitian dilation
`diag(W, W†) ∘ swap` of the released six-query block encoding `W`: the fixed `swap` and two
masked runs of the six-query program (one forward, one inverse; one row-location, one
column-location and four value calls each). With the Boolean certificate of the native
primitives (`hardCost`: two Boolean queries per value call, none per location call), each
block-encoding call therefore costs at most `16` Boolean queries (`implementsOn_beOp`,
`nonempty_primitiveAccess`), i.e. at most `8` value calls, inverses and controls included.

The released physical families `TimeDependentExtensions.BlockEncoding.oracle` and
`alignedOracle` add untouched spectators only (`beWrap`, `isWrap_beWrap`,
`aligned_eq_beWrap`), so they inherit the certificate (`nonempty_alignedAccess`).
-/

namespace TimeDependentLowerBoundExtensions.BlockEncoding

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open scoped InnerProduct InnerProductSpace

/-! ### Spectator wrapper of the released block-encoding families -/

section Wrap

open TimeDependentExtensions.BlockEncoding (Basis Physical)

variable {B₀ : Type} [Fintype B₀] [DecidableEq B₀] {M : ℕ}

/-- The fixed wrapper of the released aligned block-encoding family around the controlled
time-indexed oracle: the control, dummy and reference spectators of the active layer, the
chronological cells `ActiveRegisterLayout.Label PUnit T d` and the clean-output alignment
spectator `Bool`. -/
def beWrap (B₀ : Type) [Fintype B₀] [DecidableEq B₀] (M T d : ℕ)
    (A : EuclideanSpace ℂ (Basis B₀ M) →L[ℂ] EuclideanSpace ℂ (Basis B₀ M)) :
    CleanOutputAlignment.Double (Physical B₀ M T d) →L[ℂ]
      CleanOutputAlignment.Double (Physical B₀ M T d) :=
  WeightedClock.diagonal (fun _ : Bool =>
    MaskedProgram.masked (fun _ : ActiveRegisterLayout.Label PUnit.{1} T d => true)
      (LookupFromBasisOracle.spectator (S := (Bool × Basis B₀ M) × Basis B₀ M) A))

/-- `beWrap` consists of spectators and fixed relabellings only. -/
theorem isWrap_beWrap (M T d : ℕ) : ODELowerBoundExtensions.Release.IsWrap (beWrap B₀ M T d) :=
  ((ODELowerBoundExtensions.Release.isWrap_spectator _ _).masked
    (ActiveRegisterLayout.Label PUnit.{1} T d)).diagonalConst Bool

/-- The released aligned block-encoding family is `beWrap` of the controlled time-indexed
oracle. -/
theorem aligned_eq_beWrap {X : Type*} (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ]
    EuclideanSpace ℂ B₀) (N : ℕ) (α T ε : ℝ) (l : Unit) (x : X) :
    TimeDependentExtensions.BlockEncoding.alignedOracle O N α T ε l x =
      beWrap B₀ M N (TimeDependentExtensions.BlockEncoding.degree N α T ε)
        (TimeDependentExtensions.BlockEncoding.primitive O l x) :=
  rfl

end Wrap

/-! ### Certificates on the hard instances -/

variable {I : Type*} [Fintype I] {X : Type} {y : X → I → Bool}
variable {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

omit [DecidableEq Z] in
/-- **One block-encoding call costs `16` Boolean queries**: `beOp D x` is implemented on a fixed
isometric encoding by at most `16` queries of the masked Boolean oracle, from any certificate of
the native primitives with weight `hardCost`. -/
theorem implementsOn_beOp (D : Data X N Z s) (A : PhaseAccess I y (oracles D) hardCost) :
    EncodedOracle.ImplementsOn (fun x => (Core.maskedBoolean Bool A.fam).phase (y x))
      (fun x => beOp D x)
      (Core.maskedEncoding Bool A.enc ∘L (beLayout N Z).toLinearIsometry.toContinuousLinearMap)
      16 := by
  have hQ : ∀ x, IsUnitary (A.fam.phase (y x)) := fun x => A.fam.isUnitary_phase (y x)
  have hW : ∀ x, IsUnitary ((program D).eval x) := fun x =>
    (program D).eval_unitary (oracles_unitary D) x
  have h8 : EncodedOracle.ImplementsOn (fun x => A.fam.phase (y x))
      (fun x => (program D).eval x) A.enc 8 :=
    (EncodedMultiOracle.implements_compile A.enc A.enc_isometry hQ (oracles_unitary D)
      (program D) hardCost A.impl).mono (le_of_eq (by rw [program_cost]; rfl))
  have hm := (Core.implementsOn_masked Bool (fun b => !b) A.fam y h8).mul
    (Core.implementsOn_masked Bool (fun b => b) A.fam y (h8.adjoint hQ hW))
  have hs := EncodedOracle.ImplementsOn.fixed
    (O := fun x => (Core.maskedBoolean Bool A.fam).phase (y x))
    (Core.maskedEncoding_isometry Bool A.enc A.enc_isometry) HermitianDilation.swap
    HermitianDilation.swap_unitary
  have hd := (hm.mul hs).congr
    (G := fun x => HermitianDilation.dilation ((program D).eval x)) (fun x => by
      refine ContinuousLinearMap.ext fun v => PiLp.ext fun b => ?_
      cases b <;> simp [MaskedProgram.masked_apply, ContinuousLinearMap.star_eq_adjoint])
  exact SparseLowerBounds.Adaptive.Access.implementsOn_conj (beLayout N Z).symm hd

omit [DecidableEq Z] in
/-- The encoding of `implementsOn_beOp` is isometric. -/
theorem beEncoding_isometry (D : Data X N Z s) (A : PhaseAccess I y (oracles D) hardCost) :
    (Core.maskedEncoding Bool A.enc ∘L (beLayout N Z).toLinearIsometry.toContinuousLinearMap)† ∘L
      (Core.maskedEncoding Bool A.enc ∘L (beLayout N Z).toLinearIsometry.toContinuousLinearMap) =
        1 := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ (Core.maskedEncoding Bool A.enc),
    Core.maskedEncoding_isometry Bool A.enc A.enc_isometry, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]
  exact LinearIsometry.adjoint_comp_self _

/-- The certificate of the one-label family `beOp D`, weight `16`. -/
def beOpAccess (D : Data X N Z s) (A : PhaseAccess I y (oracles D) hardCost) :
    PhaseAccess I y (fun (_ : Unit) (x : X) => beOp D x) (fun _ => 16) :=
  PhaseAccess.ofImplementsOn (Core.maskedBoolean Bool A.fam)
    (Core.maskedEncoding Bool A.enc ∘L (beLayout N Z).toLinearIsometry.toContinuousLinearMap)
    (beEncoding_isometry D A) (fun _ => implementsOn_beOp D A)

/-- The controlled time-indexed oracle of the constant family is the controlled call of
`beOp D x` with the time register as a spectator. -/
theorem primitive_beConst (D : Data X N Z s) (M : ℕ) (l : Unit) (x : X) :
    TimeDependentExtensions.BlockEncoding.primitive (beConst D M) l x =
      (TimeDependentExtensions.BlockEncoding.layout (BEBasis N Z) M).conjStarAlgEquiv
        (MaskedProgram.masked (fun c : Bool × Fin M => c.1) (beOp D x)) :=
  rfl

/-- **The controlled time-indexed oracle of the constant family**: weight `16` per call. -/
theorem nonempty_primitiveAccess (D : Data X N Z s) (A : PhaseAccess I y (oracles D) hardCost)
    (M : ℕ) :
    Nonempty (PhaseAccess I y (TimeDependentExtensions.BlockEncoding.primitive (beConst D M))
      (fun _ => 16)) :=
  ⟨((Core.maskedAccess (beOpAccess D A) (Bool × Fin M) (fun c => c.1)).conj
    (TimeDependentExtensions.BlockEncoding.layout (BEBasis N Z) M)).congr
      (fun l x => (primitive_beConst D M l x).symm)⟩

/-- **The released aligned block-encoding family of the constant family** (any number `M` of
samples, slot count `Nsl` and schedule `α T ε`): weight `16` per call. -/
theorem nonempty_alignedAccess (D : Data X N Z s) (A : PhaseAccess I y (oracles D) hardCost)
    (M Nsl : ℕ) (α T ε : ℝ) :
    Nonempty (PhaseAccess I y
      (TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) Nsl α T ε)
      (fun _ => 16)) := by
  obtain ⟨P⟩ := nonempty_primitiveAccess D A M
  have h : TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) Nsl α T ε =
      fun l x => beWrap (BEBasis N Z) M Nsl
        (TimeDependentExtensions.BlockEncoding.degree Nsl α T ε)
        (TimeDependentExtensions.BlockEncoding.primitive (beConst D M) l x) :=
    funext fun l => funext fun x => aligned_eq_beWrap _ _ _ _ _ _ _
  rw [h]
  exact Core.nonempty_access_of_wrap (isWrap_beWrap _ _ _) P

/-- The released aligned block-encoding family of the constant family is unitary. -/
theorem alignedOracle_beConst_unitary (D : Data X N Z s) (M Nsl : ℕ) (α T ε : ℝ) (l : Unit)
    (x : X) :
    IsUnitary
      (TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) Nsl α T ε l x) :=
  CoherentQuerySchedule.oracle_unitary _ (TimeDependentExtensions.BlockEncoding.oracle_unitary
    (beConst D M) (fun x _ => beOp_unitary D x) Nsl _) l x

end

end TimeDependentLowerBoundExtensions.BlockEncoding
