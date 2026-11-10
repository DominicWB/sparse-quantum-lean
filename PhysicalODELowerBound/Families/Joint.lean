import AdaptiveODELowerBound.Padding.Joint
import AdaptiveODELowerBound.Joint.General

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The time-dependent hard families against adaptive solvers over any Boolean-implemented oracle

Manuscript: Theorem `odel:thm:joint` (with the dense block and zero padding of its proof) and
Proposition `odel:rem:homogeneous`, for one adaptive solver
(`AdaptiveODELowerBound.Model.TreeSolver`) over **any** unitary oracle family `O` each of whose
labels `l` is implemented on an isometric encoding by at most `w l` queries of a Boolean membership
phase oracle (`EncodedOracle.ImplementsOn`, the construction before Theorem `odel:thm:joint`). The
access shape is not fixed here; the general-mesh physical oracle and its call forms qualify
(`PhysicalODELowerBound.Mesh`).

The oracle workspace is finite-dimensional, as the physical workspaces of the released solvers
and their call forms are, so the general forms `AdaptiveODELowerBound.Joint.joint_general_tree`
and `outer_general_tree` apply directly.

The conclusion is the Boolean count `2 b ≤ worstCost w`; with the costs `hardCost` (two per value
call) this is `b` value calls.

* `joint_solver` (on `JointRange`): `2 (ḡ √s τ / 400)`, from
  `AdaptiveODELowerBound.Joint.joint_general_tree` and `SparseLowerBounds.ODE.joint_bound_le`.
* `hom_solver` (on `HomRange`): `2 (ḡ √s τ / 500)`, from
  `AdaptiveODELowerBound.Joint.outer_general_tree` with the homogeneous readout
  (`ODELowerBoundExtensions.Homogeneous.homHalfObs`, `homEnd_ideal_corr`) and `hom_bound_le`.
* `joint_pad_solver` (on `JointRange`, any dense flag and known padding `P`): `2 (ḡ √s τ / 400)`,
  through the padded readout (`AdaptiveODELowerBound.Padding.treeAccurate_of_zeroPad`).
-/

namespace PhysicalODELowerBound.Families

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open ODELowerBoundExtensions.Homogeneous (HomRange homFamilyAt homConst)
open ODELowerBoundExtensions.Padding (jointPadFamilyAt)
open AdaptiveODELowerBound.Model (TreeSolver)
open scoped InnerProduct InnerProductSpace

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {s : ℕ} {τ gbar ε : ℝ}
variable {L W Fl E G B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- **Theorem `odel:thm:joint`, Boolean count** (Theorem `odel:thm:joint`): on `JointRange`, an
adaptive solver of the joint family over a unitary oracle family implemented with costs `w` by
membership programs on an isometric encoding has worst-case cost at least `2 (ḡ √s τ / 400)`. -/
theorem joint_solver (h : JointRange s τ gbar ε)
    (P : ProjFamily B (Fin (jointM gbar) × Fin (jointN τ) × Fin (2 ^ jointMu s)))
    (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Promised (jointM gbar) (jointN τ) (2 ^ jointMu s) → W →L[ℂ] W}
    (hU : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (A : TreeSolver (jointFamilyAt s τ gbar h.s_ge h.tau_ge) O Fl E G ε) :
    2 * (jointConst * gbar * Real.sqrt s * τ) ≤ A.tree.worstCost w := by
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  have hT := jointN_time (by linarith [h.tau_ge] : (1 : ℝ) ≤ τ)
  have hb := AdaptiveODELowerBound.Joint.joint_general_tree (s := s)
    (by omega)
    (even_jointM gbar) (one_le_jointN h.tau_ge) (one_le_jointMu (by omega))
    (by linarith [h.eps_le] : 2 * ε ≤ 1) P Enc hEnc O hU w hw A.tree A.readout A.readout_isometry
    A.success fun x => by
      have hx := A.accurate x _ (jointSol_solves x)
      have hT' : (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T = τ := jointFamily_T
      rwa [hT', unitDirection_jointSol_T hT] at hx
  linarith [joint_bound_le h]

/-- **Proposition `odel:rem:homogeneous`, Boolean count** (Proposition `odel:rem:homogeneous`): on
`HomRange`, an adaptive solver of the homogeneous time-dependent family over a unitary oracle family
implemented with costs `w` by membership programs on an isometric encoding has worst-case cost at
least `2 (ḡ √s τ / 500)`. -/
theorem hom_solver (h : HomRange s τ gbar ε)
    (P : ProjFamily B (Fin (jointM gbar) × Fin (ODELowerBoundExtensions.Homogeneous.homN τ) ×
      Fin (2 ^ jointMu s)))
    (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Promised (jointM gbar) (ODELowerBoundExtensions.Homogeneous.homN τ)
      (2 ^ jointMu s) → W →L[ℂ] W}
    (hU : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (A : TreeSolver (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) O Fl E G ε) :
    2 * (homConst * gbar * Real.sqrt s * τ) ≤ A.tree.worstCost w := by
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  have hτ := ODELowerBoundExtensions.Homogeneous.twenty_le_tau h
  have hT := ODELowerBoundExtensions.Homogeneous.homN_time h.gbar_ge h.tau_ge
  have hideal : ∀ x : Promised (jointM gbar) (ODELowerBoundExtensions.Homogeneous.homN τ)
      (2 ^ jointMu s), 15 / 17 ≤ halfSign (jointM gbar) (oddCand x) *
      (⟪ODEStateNormalization.unitDirection
          (ODELowerBoundExtensions.Homogeneous.homEnd (jointM gbar) (jointMu s) s (oddCand x)),
        ODELowerBoundExtensions.Homogeneous.homHalfObs (jointM gbar) (jointMu s) s
          (ODEStateNormalization.unitDirection
            (ODELowerBoundExtensions.Homogeneous.homEnd (jointM gbar) (jointMu s) s
              (oddCand x)))⟫_ℂ).re :=
    fun x => ODELowerBoundExtensions.Homogeneous.homEnd_ideal_corr (by omega) (oddCand x)
  have hb := AdaptiveODELowerBound.Joint.outer_general_tree
    (S := ODELowerBoundExtensions.Homogeneous.HomIndex (jointM gbar) (jointMu s) s)
    (a := 15 / 17) (by omega) (even_jointM gbar)
    (ODELowerBoundExtensions.Homogeneous.one_le_homN (by linarith))
    (one_le_jointMu (by omega)) (ODELowerBoundExtensions.Homogeneous.two_eps_le h.eps_le)
    P Enc hEnc O hU w hw A.tree A.readout A.readout_isometry A.success
    (fun x => ODEStateNormalization.unitDirection
      (ODELowerBoundExtensions.Homogeneous.homEnd (jointM gbar) (jointMu s) s (oddCand x)))
    (ODELowerBoundExtensions.Homogeneous.homHalfObs (jointM gbar) (jointMu s) s)
    ODELowerBoundExtensions.Homogeneous.homHalfObs_isSelfAdjoint
    ODELowerBoundExtensions.Homogeneous.norm_homHalfObs_le hideal fun x => by
      have hx := A.accurate x _ (ODELowerBoundExtensions.Homogeneous.homSol_solves
        (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega)) hT x)
      have hT' : (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).T = τ :=
        ODELowerBoundExtensions.Homogeneous.homFamily_T
      rwa [hT',
        ODELowerBoundExtensions.Homogeneous.homSol_of_busy_le (by omega) x hT] at hx
  have hc := ODELowerBoundExtensions.Homogeneous.hom_bound_le h
  unfold ODELowerBoundExtensions.Homogeneous.homCorr at hc
  linarith

/-- **Theorem `odel:thm:joint` after known padding, Boolean count** (proof of Theorem
`odel:thm:joint`): on `JointRange`, for any dense flag and any known padding `P'`, an adaptive
solver of the padded joint family over a unitary oracle family implemented with costs `w` by
membership programs on an isometric encoding has worst-case cost at least `2 (ḡ √s τ / 400)`. -/
theorem joint_pad_solver (h : JointRange s τ gbar ε) (dense : Bool) (P' : Type*) [Fintype P']
    [DecidableEq P']
    (P : ProjFamily B (Fin (jointM gbar) × Fin (jointN τ) × Fin (2 ^ jointMu s)))
    (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Promised (jointM gbar) (jointN τ) (2 ^ jointMu s) → W →L[ℂ] W}
    (hU : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (A : TreeSolver (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P') O Fl E G ε) :
    2 * (jointConst * gbar * Real.sqrt s * τ) ≤ A.tree.worstCost w := by
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  have hT := jointN_time (by linarith [h.tau_ge] : (1 : ℝ) ≤ τ)
  let i₀ : JointIndex (jointM gbar) (jointMu s) s := Sum.inr ⟨0, by omega⟩
  have hb := AdaptiveODELowerBound.Joint.joint_general_tree (s := s)
    (G := Joint (Option P') G) (by omega)
    (even_jointM gbar) (one_le_jointN h.tau_ge) (one_le_jointMu (by omega))
    (by linarith [h.eps_le] : 2 * ε ≤ 1) P Enc hEnc O hU w hw A.tree
    (LowerBoundRemarks.HamiltonianPadding.padReadout P' G i₀ ∘L A.readout)
    (LowerBoundRemarks.HamiltonianPadding.padReadout_comp_isometry i₀ A.readout
      A.readout_isometry)
    A.success fun x => by
      have hx := AdaptiveODELowerBound.Padding.treeAccurate_of_zeroPad
        ODELowerBoundExtensions.Padding.jointPadFamily_zeroPad A i₀ x
        (ODELowerBoundExtensions.Padding.jointDenseSol_solves x)
      rwa [ODELowerBoundExtensions.Padding.jointDenseFamily_T, unitDirection_jointSol_T hT] at hx
  linarith [joint_bound_le h]

end

end PhysicalODELowerBound.Families
