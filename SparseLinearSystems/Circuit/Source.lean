import SparseLinearSystems.Circuit.CounterFilter
import SparseHamiltonian.NativeWholeProgramMask
import SparseHamiltonian.NativeCayleyProgram

/-!
# The controlled source oracle and its masked use

The native workspace register `B = NativeCayleyProgram.Basis n Z` contains an
`n`-valued sub-register.  A vector of `ℂ^n` is stored there with all other
sub-registers at a fixed public reference value (`nEmb`).

The supplied state-preparation circuit `U_b` acts on that sub-register, with
the remaining registers as spectators (`srcU`).  The physical source primitive
is the *controlled* form `CS`, controlled by the workspace control bit of every
cell (`sourceOracle`); one invocation is one counted state-preparation call, as
in Theorem `qls:thm:main`.  Computing a fixed public mask into the control bit,
one source call and erasing the mask implement `U_b` on exactly the selected
cells (`sourceProgram_intertwines`).
-/

namespace SparseLinearSystems.Source

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit NativeControlledOracle LookupOracle
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [DecidableEq Z]

/-- The native workspace basis. -/
abbrev Bas (n Z : Type*) := NativeCayleyProgram.Basis n Z

/-- The spectator registers of the payload, everything except the `n`-register. -/
abbrev Rest (n Z : Type*) :=
  Bool × (((Bool × NativeSparseMaskedAccess.Basis n Z) × NativeSparseMaskedAccess.Basis n Z) ×
    ((n × Z) × Fin 3))

/-- Separate the source register from its spectators. -/
def regEquiv : Bas n Z ≃ Rest n Z × n where
  toFun b := ((b.1, ((b.2.1.1, b.2.1.2), ((b.2.2.1.1.2, b.2.2.1.2), b.2.2.2))), b.2.2.1.1.1)
  invFun q := (q.1.1, ((q.1.2.1.1, q.1.2.1.2), (((q.2, q.1.2.2.1.1), q.1.2.2.1.2), q.1.2.2.2)))
  left_inv b := by rcases b with ⟨b, ⟨⟨c, d⟩, r⟩, ⟨⟨⟨i, j⟩, z⟩, f⟩⟩; rfl
  right_inv q := by rcases q with ⟨⟨b, ⟨⟨c, d⟩, r⟩, ⟨⟨j, z⟩, f⟩⟩, i⟩; rfl

/-- The flat source layout `E(B) ≃ E(Rest × n)`. -/
def srcLayout : EuclideanSpace ℂ (Bas n Z) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Rest n Z × n) :=
  permutationUnitary (regEquiv (n := n) (Z := Z))

/-- `U` on the source register, all other registers spectators. -/
def srcU (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (Bas n Z) →L[ℂ] EuclideanSpace ℂ (Bas n Z) :=
  (srcLayout (n := n) (Z := Z)).symm.conjStarAlgEquiv
    (LookupFromBasisOracle.spectator (S := Rest n Z) U)

omit [DecidableEq n] [DecidableEq Z] in
theorem srcU_unitary (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hU : IsUnitary U) :
    IsUnitary (srcU (Z := Z) U) :=
  (LookupFromBasisOracle.spectator_unitary U hU).transport _

/-- The fixed spectator value used to store a vector of `ℂ^n`. -/
def rest₀ (a : Bas n Z) : Rest n Z := (regEquiv a).1

/-- Store `v ∈ ℂ^n` in the source register, spectators at `rest₀`. -/
def slice (s₀ : Rest n Z) : EuclideanSpace ℂ n →ₗᵢ[ℂ] PiLp 2 (fun _ : Rest n Z => EuclideanSpace ℂ n) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun s => if s = s₀ then v else 0)
      map_add' := by
        intro v w; apply PiLp.ext; intro s
        by_cases h : s = s₀ <;> simp [h]
      map_smul' := by
        intro c v; apply PiLp.ext; intro s
        by_cases h : s = s₀ <;> simp [h] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    simp only
    rw [Finset.sum_eq_single s₀]
    · simp
    · intro s _ hs; simp [hs]
    · intro h; exact absurd (Finset.mem_univ _) h

@[simp] theorem slice_apply (s₀ : Rest n Z) (v : EuclideanSpace ℂ n) (s : Rest n Z) :
    slice s₀ v s = if s = s₀ then v else 0 := rfl

/-- The `ℂ^n`-cell embedding into the native workspace. -/
def nEmb (a : Bas n Z) : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ (Bas n Z) :=
  (srcLayout (n := n) (Z := Z)).symm.toLinearIsometry.comp
    ((RegisterEquivalences.productFlatten (Rest n Z) n).toLinearIsometry.comp (slice (rest₀ a)))

/-- The source acts on stored vectors exactly as `U`. -/
theorem srcU_nEmb (a : Bas n Z) (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v : EuclideanSpace ℂ n) : srcU U (nEmb a v) = nEmb a (U v) := by
  simp only [srcU, nEmb, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometry.coe_comp, Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    LookupFromBasisOracle.spectator, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  congr 2
  apply PiLp.ext
  intro s
  simp only [WeightedClock.diagonal_apply, slice_apply]
  split_ifs <;> simp

/-! ### The controlled source primitive -/

/-- The controlled source on one native workspace: `U_b` on the payload's
source register when the control bit is set. -/
def controlled (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (Workspace (Bas n Z)) →L[ℂ] EuclideanSpace ℂ (Workspace (Bas n Z)) :=
  (RegisterEquivalences.productFlatten ((Bool × Bas n Z) × Bas n Z) (Bas n Z)).conjStarAlgEquiv
    (WeightedClock.diagonal (fun s : (Bool × Bas n Z) × Bas n Z =>
      if s.1.1 then srcU (Z := Z) U else 1))

omit [DecidableEq n] [DecidableEq Z] in
theorem controlled_unitary (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hU : IsUnitary U) :
    IsUnitary (controlled (Z := Z) U) := by
  apply IsUnitary.transport
  apply NativeMaskedOracle.diagonal_unitary
  intro s
  cases s.1.1
  · exact isUnitary_one
  · exact srcU_unitary U hU

theorem controlled_packet (U : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (c : Bool)
    (d r : Bas n Z) (v : EuclideanSpace ℂ (Bas n Z)) :
    controlled U (packet c d r v) = packet c d r (if c then srcU U v else v) := by
  ext ⟨s, p⟩
  have hs : ((RegisterEquivalences.productFlatten ((Bool × Bas n Z) × Bas n Z) (Bas n Z)).symm
      (packet c d r v)) s = if s = ((c, d), r) then v else 0 := by
    ext q
    by_cases h : s = ((c, d), r) <;> simp [h]
  change (if s.1.1 then srcU (Z := Z) U else 1)
    (((RegisterEquivalences.productFlatten ((Bool × Bas n Z) × Bas n Z) (Bas n Z)).symm
      (packet c d r v)) s) p = _
  rw [hs]
  by_cases h : s = ((c, d), r)
  · subst h
    cases c <;> simp
  · simp [h]

/-- The physical source primitive: one controlled call acting in every cell. -/
def sourceOracle {ι X : Type*} [Fintype ι] (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (x : X) : NativeMaskedOracle.Physical ι (Bas n Z) →L[ℂ] NativeMaskedOracle.Physical ι (Bas n Z) :=
  MaskedProgram.masked (fun _ : ι => true) (controlled (Z := Z) (Ub x))

omit [DecidableEq n] [DecidableEq Z] in
theorem sourceOracle_unitary {ι X : Type*} [Fintype ι]
    (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hUb : ∀ x, IsUnitary (Ub x)) (x : X) :
    IsUnitary (sourceOracle (ι := ι) (Z := Z) Ub x) :=
  MaskedProgram.masked_unitary _ _ (controlled_unitary _ (hUb x))

omit [DecidableEq n] [DecidableEq Z] in
theorem sourceOracle_apply {ι X : Type*} [Fintype ι]
    (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (x : X)
    (w : NativeMaskedOracle.Physical ι (Bas n Z)) (i : ι) :
    sourceOracle (Z := Z) Ub x w i = controlled (Ub x) (w i) := by
  simp [sourceOracle, MaskedProgram.masked_apply]

/-- A single source call under a fixed public cell mask. -/
def sourceProgram {ι X : Type*} [Fintype ι] (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (active : ι → Bool) : OracleCircuit.Program (sourceOracle (ι := ι) (Z := Z) Ub) :=
  .seq (.fixed _ (NativeMaskedOracle.maskGate_unitary active))
    (.seq .query (.fixed _ (NativeMaskedOracle.maskGate_unitary active)))

omit [DecidableEq n] [DecidableEq Z] in
@[simp] theorem sourceProgram_count {ι X : Type*} [Fintype ι]
    (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (active : ι → Bool) :
    (sourceProgram (Z := Z) Ub active).count = 1 := rfl

/-- **Masked source access.**  One controlled source call implements `U_b` on
the selected cells of the clean encoding and the identity elsewhere. -/
theorem sourceProgram_intertwines {ι X : Type*} [Fintype ι]
    (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (a : Bas n Z) (active : ι → Bool)
    (x : X) :
    (sourceProgram (Z := Z) Ub active).eval x ∘L (NativeMaskedOracle.input (ι := ι) a).toContinuousLinearMap =
      (NativeMaskedOracle.input a).toContinuousLinearMap ∘L
        MaskedProgram.masked active (srcU (Z := Z) (Ub x)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  have key : ∀ w : NativeMaskedOracle.Physical ι (Bas n Z),
      NativeMaskedOracle.maskGate active w i =
        permutationUnitary (NativeMaskedOracle.toggle (active i)) (w i) := fun _ => rfl
  change NativeMaskedOracle.maskGate active (sourceOracle Ub x
    (NativeMaskedOracle.maskGate active (NativeMaskedOracle.input a v))) i =
    NativeMaskedOracle.input a (MaskedProgram.masked active (srcU (Ub x)) v) i
  rw [key, sourceOracle_apply, key, NativeMaskedOracle.input_apply, NativeMaskedOracle.input_apply,
    MaskedProgram.masked_apply]
  cases h : active i
  · rw [NativeMaskedOracle.toggle_packet, controlled_packet, NativeMaskedOracle.toggle_packet]
    simp
  · rw [NativeMaskedOracle.toggle_packet, controlled_packet, NativeMaskedOracle.toggle_packet]
    simp

end

end SparseLinearSystems.Source
