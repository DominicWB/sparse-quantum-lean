import SparseLinearSystems.Circuit.LogicalWalk

/-!
# An opaque copy of the walk space

`Priv n` is a deeply nested `L²` product.  Generic operator lemmas instantiated
at such a type must reconcile two elaborations of its algebraic structure (the
direct `WithLp` instances and those derived from the normed structure), which
is expensive.  `PrivO n` is the same Hilbert space behind a definition, with its
instances declared once (read off generically, see `ipsOf`); every derived
instance then has a single elaboration.

`toO : Priv n ≃ₗᵢ PrivO n` is the identity, and the walk and its factors are
transported by unitary conjugation (`WwO`, `WwO_factor`).  This changes no
mathematics: it only fixes the representation used by the circuit layer.
-/

namespace SparseLinearSystems.LogicalWalk

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap HilbertAugmentation Augmented SparseBranch
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-! ### Generic accessors

Instances on a concrete `L²` product can be reached along two paths: the direct
`WithLp` seminormed instances and the ones derived from the normed instance.
Reading the structures off generically (`ipsOf`, `IsoN`) pins the second path,
so no comparison between the two is ever needed for the opaque copy. -/

/-- The inner product structure, with the seminormed structure derived from the
normed one. -/
abbrev ipsOf (E : Type*) [NormedAddCommGroup E] [h : InnerProductSpace ℂ E] :
    InnerProductSpace ℂ E := h

theorem completeOf (E : Type*) [NormedAddCommGroup E] [h : CompleteSpace E] : CompleteSpace E := h

theorem findimOf (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [h : FiniteDimensional ℂ E] : FiniteDimensional ℂ E := h

/-- Linear isometric equivalences, with the seminormed structures derived from
the normed ones. -/
abbrev IsoN (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] := E ≃ₗᵢ[ℂ] F

/-- The identity, as an `IsoN`. -/
def isoSelf (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : IsoN E E :=
  LinearIsometryEquiv.refl ℂ E

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- The walk space behind a definition. -/
def PrivO (n : Type*) [Fintype n] : Type _ := Priv n

instance instNormedAddCommGroupPrivO : NormedAddCommGroup (PrivO n) :=
  inferInstanceAs (NormedAddCommGroup (Priv n))
instance instInnerProductSpacePrivO : InnerProductSpace ℂ (PrivO n) := ipsOf (Priv n)
instance instCompleteSpacePrivO : CompleteSpace (PrivO n) := completeOf (Priv n)
instance instFiniteDimensionalPrivO : FiniteDimensional ℂ (PrivO n) := findimOf (Priv n)

/-- The identity isometry onto the opaque copy. -/
def toO : IsoN (Priv n) (PrivO n) := isoSelf (Priv n)

omit [DecidableEq n] in
@[simp] theorem toO_symm_apply_apply (v : Priv n) : (toO (n := n)).symm (toO v) = v := rfl

omit [DecidableEq n] in
@[simp] theorem toO_apply_symm_apply (v : PrivO n) : toO ((toO (n := n)).symm v) = v := rfl

omit [DecidableEq n] in
theorem norm_toO (v : Priv n) : ‖toO v‖ = ‖v‖ := by
  rw [LinearIsometryEquiv.norm_map]

/-- Transport of an operator to the opaque copy. -/
def opO (T : Priv n →L[ℂ] Priv n) : PrivO n →L[ℂ] PrivO n := (toO (n := n)).conjStarAlgEquiv T

omit [DecidableEq n] in
@[simp] theorem opO_apply (T : Priv n →L[ℂ] Priv n) (v : PrivO n) :
    opO T v = toO (T (toO.symm v)) := rfl

omit [DecidableEq n] in
theorem opO_mul (A B : Priv n →L[ℂ] Priv n) : opO (A * B) = opO A * opO B := by
  ext v
  rw [opO_apply, mul_def (opO A), comp_apply, opO_apply, opO_apply, toO_symm_apply_apply,
    mul_def, comp_apply]

omit [DecidableEq n] in
theorem opO_one : opO (1 : Priv n →L[ℂ] Priv n) = 1 := by
  ext v
  rw [opO_apply, one_def, id_apply, one_def, id_apply, toO_apply_symm_apply]

omit [DecidableEq n] in
theorem opO_star (A : Priv n →L[ℂ] Priv n) : opO (star A) = star (opO A) :=
  (toO (n := n)).conjStarAlgEquiv.map_star' A

omit [DecidableEq n] in
theorem opO_adjoint (A : Priv n →L[ℂ] Priv n) : (opO (A†)) = (opO A)† := by
  rw [← star_eq_adjoint, opO_star, star_eq_adjoint]

omit [DecidableEq n] in
theorem opO_unitary (A : Priv n →L[ℂ] Priv n) (hA : OracleCircuit.IsUnitary A) :
    OracleCircuit.IsUnitary (opO A) := by
  constructor
  · rw [← opO_star, ← opO_mul, hA.1, opO_one]
  · rw [← opO_star, ← opO_mul, hA.2, opO_one]

/-! ### Algebra of the transport -/

omit [DecidableEq n] in
theorem opO_add (A B : Priv n →L[ℂ] Priv n) : opO (A + B) = opO A + opO B := by
  ext v
  rw [add_apply, opO_apply, opO_apply, opO_apply,
    add_apply, map_add]

omit [DecidableEq n] in
theorem opO_zero : opO (0 : Priv n →L[ℂ] Priv n) = 0 := by
  ext v
  rw [opO_apply, zero_apply, zero_apply, map_zero]

omit [DecidableEq n] in
theorem opO_smul (c : ℂ) (A : Priv n →L[ℂ] Priv n) : opO (c • A) = c • opO A := by
  ext v
  rw [smul_apply, opO_apply, opO_apply, smul_apply,
    map_smul]

omit [DecidableEq n] in
theorem opO_pow (A : Priv n →L[ℂ] Priv n) (k : ℕ) : opO (A ^ k) = opO A ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, opO_one]
  | succ k ih => rw [pow_succ, pow_succ, opO_mul, ih]

/-- The transport as an additive map. -/
def opOHom : (Priv n →L[ℂ] Priv n) →+ (PrivO n →L[ℂ] PrivO n) where
  toFun := opO
  map_zero' := opO_zero
  map_add' := opO_add

omit [DecidableEq n] in
theorem opO_sum {ι : Type*} (S : Finset ι) (A : ι → Priv n →L[ℂ] Priv n) :
    opO (∑ i ∈ S, A i) = ∑ i ∈ S, opO (A i) :=
  map_sum (opOHom (n := n)) A S

/-- The four-branch boundary in the opaque copy. -/
def JwO [Fintype Z] [AddCommGroup Z] [DecidableEq Z] (D : NativeSparseBlockEncoding.Data X n Z s) :
    Pub V0 →ₗᵢ[ℂ] PrivO n :=
  (toO (n := n)).toLinearIsometry.comp (Jw D)

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The walk in the opaque copy. -/
def WwO (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (σ r : ℝ) (x : X) : PrivO n →L[ℂ] PrivO n :=
  opO (Ww D Ub sv σ r x)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem WwO_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) : OracleCircuit.IsUnitary (WwO D Ub sv σ r x) :=
  opO_unitary _ (Ww_unitary D Ub sv σ r x)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Query factorization in the opaque copy.** -/
theorem WwO_factor (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (σ r : ℝ) (x : X) (hU : OracleCircuit.IsUnitary (Ub x)) :
    WwO D Ub sv σ r x =
      opO (WalkGap.reflection (Jw D).toContinuousLinearMap) *
        (opO (Asp D σ x) * (opO (Fa (s : ℝ) σ) * (opO (Vd (Ub x)) *
          (opO (Fb (s : ℝ) r sv) * opO (Vd ((Ub x)†)))))) := by
  rw [WwO, Ww_factor D Ub sv σ r x hU, opO_mul, opO_mul, opO_mul, opO_mul, opO_mul]

end

end SparseLinearSystems.LogicalWalk
