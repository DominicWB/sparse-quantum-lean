import PhysicalODELowerBound.Mesh.Transfer
import PhysicalODELowerBound.Families.Joint

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The padded joint families over the general-mesh physical oracle, with controlled calls

Manuscript: the end of the proof of Theorem `odel:thm:joint` (the dense block `2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ`
for maximum sparsity exactly `s`; "Known zero padding permits any sufficiently large qubit
register"), for the padded joint families `ODELowerBoundExtensions.Padding.jointPadFamilyAt` (time
dependent, `n + 2` stages) and adaptive solvers over the physical oracle of the released
general-mesh solver and over its call forms (`MeshForces`).

* `joint_forces_pad_mesh`, `joint_witness_pad_mesh`: `ḡ √s τ / 400` for every dense flag and known
  padding `P`, and maximum sparsity exactly `s` with the dense block, from
  `Families.joint_pad_solver` through `meshForces_of_boolean` with the released certificate
  `ODELowerBoundExtensions.Padding.implementsOn_jointPad`.
* `joint_common_dimension_mesh`, `joint_qubit_register_mesh`: the family padded by
  `PadTo JointIndex Nd` has dimension exactly `Nd` for every `Nd` at least the unpadded
  dimension, in particular `Nd = 2^q` whenever `3 ḡ² s ≤ 2^q`.

Known padding registers range over `Type`, the universe of the families in `MeshForces` and
`ConstForces` and of the released normal-form lemma
`ODELowerBoundExtensions.Release.physicalOracle_normal_form` (the released physical oracles are
universe polymorphic); the sampled-time forms in `AdaptiveODELowerBound` allow any universe.
Nothing is lost: the common-dimension forms use `PadTo S Nd : Type`.
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open LowerBoundRemarks.HamiltonianPadding (PadTo)
open ODELowerBoundExtensions.Padding (jointPadFamilyAt SparsityAttained)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:joint` after known padding over the physical oracle, forcing**: on
`JointRange`, for every dense flag and every known padding `P`, the padded joint family
mesh-forces `ḡ √s τ / 400`. -/
theorem joint_forces_pad_mesh (h : JointRange s τ gbar ε) (dense : Bool) (P : Type) [Fintype P]
    [DecidableEq P] :
    MeshForces (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P) ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  refine meshForces_of_boolean (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P) membership
    (fun ι _ => ⟨_, inferInstance, inferInstance, inferInstance,
      ODELowerBoundExtensions.Padding.stageBoolean ι (jointM gbar) (jointN τ) (jointMu s)
        (ODELowerBoundExtensions.Padding.jointPadBits s dense)
        (LowerBoundRemarks.HamiltonianPadding.padTable
          (ODELowerBoundExtensions.Padding.jointDenseTable (jointM gbar) (jointMu s) s
            (ODELowerBoundExtensions.Padding.jointPadBits s dense) dense) P),
      ancillaEmbed _, ancillaEmbed_isometry,
      ODELowerBoundExtensions.Padding.implementsOn_jointPad ι⟩) ?_
  intro L W Fl E G B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q Enc hEnc O hU w hw A
  exact Families.joint_pad_solver h dense P Q Enc hEnc hU w hw A

/-- **Theorem `odel:thm:joint` after known padding over the general-mesh physical oracle** (proof of
Theorem `odel:thm:joint`): for every finite known register `P`, with or without the dense block, the
padded joint family is in the class and forces `ḡ √s τ / 400` value calls (and as many matrix calls)
on every adaptive solver over the physical oracle or its call forms; with the dense block it has
maximum sparsity exactly `s`. -/
theorem joint_witness_pad_mesh (h : JointRange s τ gbar ε) (dense : Bool) (P : Type) [Fintype P]
    [DecidableEq P] :
    MeshWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P)) := by
  have hW := AdaptiveODELowerBound.Padding.joint_witness_pad_tree h dense P
  exact ⟨⟨hW.1.inClass, hW.1.time_eq, joint_forces_pad_mesh h dense P⟩, hW.2⟩

/-- **Theorem `odel:thm:joint` in any sufficiently large common dimension over the physical oracle**
(proof of Theorem `odel:thm:joint`): for every `Nd` at least the dimension of `jointFamilyAt`, the
joint family padded by `PadTo JointIndex Nd`, with or without the dense block, has dimension exactly
`Nd`, is in the class and mesh-forces `ḡ √s τ / 400`; with the dense block it has maximum sparsity
exactly `s`. -/
theorem joint_common_dimension_mesh (h : JointRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      MeshWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) := by
  exact ⟨LowerBoundRemarks.HamiltonianPadding.card_padTo hJ, joint_witness_pad_mesh h dense _⟩

/-- **Theorem `odel:thm:joint` on any sufficiently large qubit register over the physical oracle**
(proof of Theorem `odel:thm:joint`): for every `q` with `3 ḡ² s ≤ 2^q`, the joint family padded by
`PadTo JointIndex (2^q)`, with or without the dense block, has dimension exactly `2^q`, is in the
class and mesh-forces `ḡ √s τ / 400`; with the dense block it has maximum sparsity exactly `s`. -/
theorem joint_qubit_register_mesh (h : JointRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hq : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      MeshWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) := by
  have hc := (joint_instance_props (s := s) h.s_ge h.gbar_ge).2.2
  have hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ 2 ^ q := by
    have : (Fintype.card (JointIndex (jointM gbar) (jointMu s) s) : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  exact joint_common_dimension_mesh h dense (2 ^ q) hJ

end

end PhysicalODELowerBound.Mesh
