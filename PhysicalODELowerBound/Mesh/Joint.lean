import PhysicalODELowerBound.Mesh.Transfer
import PhysicalODELowerBound.Families.Joint

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:joint` and Remark `odel:rem:homogeneous` over the general-mesh physical oracle

Manuscript lines 4290-4294 (value, inverse and controlled calls cost at most two Boolean
membership queries), 4296-4341 (Theorem `odel:thm:joint`) and 4343-4388 (Remark
`odel:rem:homogeneous`), for adaptive solvers over the physical oracle of the released
general-mesh solver and over its call forms (`MeshForces`). Both families are time dependent
(the homogeneous variant "is homogeneous but still time dependent; it is not a
constant-coefficient reduction", lines 4385-4387), so only the general-mesh oracle applies.

* `joint_forces_mesh`, `joint_witness_mesh` (on `JointRange`): `ḡ √s τ / 400`, from
  `Families.joint_solver` through `meshForces_of_boolean` with the released certificate
  `SparseLowerBounds.ODE.implementsOn_joint`. For the oracle itself (no call forms) the bound is
  the released `AdaptiveODELowerBound.Release.joint_release_tree`.
* `hom_forces_mesh`, `hom_witness_mesh` (on `HomRange`: `s ≥ 4`, `ḡ ≥ 2`, `τ ≥ 20(1 + log ḡ)`,
  `0 < ε ≤ 1/64`): `ḡ √s τ / 500`, from `Families.hom_solver` with
  `ODELowerBoundExtensions.Homogeneous.implementsOn_hom`.
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open ODELowerBoundExtensions.Homogeneous (HomRange homFamilyAt homConst)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:joint` over the physical oracle, forcing**: on `JointRange`, the joint
family mesh-forces `ḡ √s τ / 400` (`c_J = jointConst = 1/400`). -/
theorem joint_forces_mesh (h : JointRange s τ gbar ε) :
    MeshForces (jointFamilyAt s τ gbar h.s_ge h.tau_ge) ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  have hs := h.s_ge
  refine meshForces_of_boolean (jointFamilyAt s τ gbar h.s_ge h.tau_ge) membership
    (fun ι _ => ⟨_, inferInstance, inferInstance, inferInstance,
      jointBoolean ι (jointM gbar) (jointN τ) (jointMu s) s, ancillaEmbed _,
      ancillaEmbed_isometry, implementsOn_joint ι (one_le_jointMu (by omega))
        (two_pow_jointMu_le (by omega)) τ (jointN_time (by linarith [h.tau_ge]))⟩) ?_
  intro L W Fl E G B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P Enc hEnc O hU w hw A
  exact Families.joint_solver h P Enc hEnc hU w hw A

/-- **Theorem `odel:thm:joint` over the general-mesh physical oracle** (lines 4296-4341): for
`s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, the joint family is in the class (`η = 1`, `T = τ`,
`g ≤ ḡ`) and forces `ḡ √s τ / 400` value calls (and as many matrix calls) on every adaptive
solver over the physical oracle or its call forms (controlled and controlled-inverse calls
included). The family has `D = 0` (`SparseLowerBounds.ODE.jointFamily_skew`), `g = √M`
(`SparseLowerBounds.ODE.jointFamilyAt_g`), `ḡ/√2 ≤ √M ≤ ḡ` and dimension at most `3 ḡ² s`
(`SparseLowerBounds.ODE.joint_instance_props`). -/
theorem joint_witness_mesh (h : JointRange s τ gbar ε) :
    MeshWitnesses (jointFamilyAt s τ gbar h.s_ge h.tau_ge) τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  have hW := AdaptiveODELowerBound.Joint.joint_witness_tree h
  exact ⟨hW.inClass, hW.time_eq, joint_forces_mesh h⟩

/-- **Remark `odel:rem:homogeneous` over the physical oracle, forcing**: on `HomRange`, the
homogeneous family mesh-forces `ḡ √s τ / 500` (`c_H = homConst = 1/500`). -/
theorem hom_forces_mesh (h : HomRange s τ gbar ε) :
    MeshForces (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) ε
      (homConst * gbar * Real.sqrt s * τ) := by
  have hs := h.s_ge
  refine meshForces_of_boolean (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) membership
    (fun ι _ => ⟨_, inferInstance, inferInstance, inferInstance,
      ODELowerBoundExtensions.Homogeneous.homBoolean ι (jointM gbar)
        (ODELowerBoundExtensions.Homogeneous.homN τ) (jointMu s) s, ancillaEmbed _,
      ancillaEmbed_isometry, ODELowerBoundExtensions.Homogeneous.implementsOn_hom ι
        (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega)) τ
        (ODELowerBoundExtensions.Homogeneous.homN_time h.gbar_ge h.tau_ge)⟩) ?_
  intro L W Fl E G B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P Enc hEnc O hU w hw A
  exact Families.hom_solver h P Enc hEnc hU w hw A

/-- **Remark `odel:rem:homogeneous` over the general-mesh physical oracle** (lines 4343-4388):
for `s ≥ 4`, `ḡ ≥ 2`, `τ ≥ 20(1 + log ḡ)` and `0 < ε ≤ 1/64`, the homogeneous (`b = 0`)
time-dependent family is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `ḡ √s τ / 500`
value calls (and as many matrix calls) on every adaptive solver over the physical oracle of the
released general-mesh solver or over its call forms (controlled and controlled-inverse calls
included). The family has `(4/√17) √M ≤ g ≤ √M` (`ODELowerBoundExtensions.Homogeneous.homFamily_g`),
`ḡ/√2 ≤ √M ≤ ḡ` and dimension at most `6 ḡ² s`
(`ODELowerBoundExtensions.Homogeneous.hom_instance_props`). -/
theorem hom_witness_mesh (h : HomRange s τ gbar ε) :
    MeshWitnesses (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) τ gbar ε
      (homConst * gbar * Real.sqrt s * τ) := by
  have hW := AdaptiveODELowerBound.Joint.hom_witness_tree h
  exact ⟨hW.inClass, hW.time_eq, hom_forces_mesh h⟩

end

end PhysicalODELowerBound.Mesh
