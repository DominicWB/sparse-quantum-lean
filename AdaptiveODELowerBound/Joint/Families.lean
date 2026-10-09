import AdaptiveODELowerBound.Joint.General
import AdaptiveODELowerBound.Access.HardCalls
import AdaptiveODELowerBound.Model.Solver
import ODELowerBoundExtensions.Homogeneous.Theorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:joint` and Remark `odel:rem:homogeneous` for adaptive protocols

Manuscript lines 4296-4341 (Theorem `odel:thm:joint`) and 4343-4388 (Remark
`odel:rem:homogeneous`), for adaptive solvers (`Model.TreeSolver`) over the sampled-time access
and over its call forms (inverses, controls and controlled inverses), with the constants of the
released single-program and retry statements.

* `joint_forces_tree` (`joint_forces`, `Release.joint_forces_retry` for trees): the joint family
  tree-forces `β² n √(M 2^μ) / 16` value calls, `β = jointCorr ε`. Route: `Joint.joint_general_tree`
  with the membership certificates `implementsOn_joint` (plain access) and
  `Access.implementsOn_calls_joint` (call forms), Boolean cost `hardCost = 2 · valueWeight`
  (`Model.worstCost_mul_tree`).
* `joint_witness_tree` (`joint_witness`): on `JointRange`, the joint family at the parameters is
  in the class and tree-forces `c_J ḡ √s τ`, `c_J = jointConst = 1/400` (`joint_bound_le`).
* `hom_forces_tree`, `hom_witness_tree` (`Homogeneous.hom_forces`, `hom_witness`): the
  homogeneous family tree-forces `homCorr ε ² n √(M 2^μ) / 16`, and on `HomRange` witnesses
  `c_H ḡ √s τ`, `c_H = homConst = 1/500`; route `Joint.outer_general_tree` with the half
  indicator `homHalfObs` (`homEnd_ideal_corr`).
-/

namespace AdaptiveODELowerBound.Joint

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveODELowerBound.Model
open ODELowerBoundExtensions.Homogeneous
open scoped InnerProduct InnerProductSpace

-- The nested time-addressed workspaces exceed the default instance size (as in `JointTheorem`).
set_option synthInstance.maxSize 1024

/-- **Theorem `odel:thm:joint` for adaptive protocols, native form**: the joint family
tree-forces `β² n √(M 2^μ) / 16` value calls (and as many calls in total), over the sampled-time
access and over its call forms, `β = jointCorr ε`. -/
theorem joint_forces_tree {M n μ s : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n)
    (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {ε : ℝ}
    (hε : 2 * ε ≤ 1) :
    TreeForces (jointFamily M n μ s hμ hμs T hT) ε
      (jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  have hhc : (fun c : Query × Access.CallForm => hardCost c.1) =
      fun c => 2 * AdaptiveHamiltonianLowerBound.Access.valueWeight c.1 := by
    funext c; rcases c with ⟨q, f⟩; cases q <;> rfl
  have hhq : hardCost = fun q => 2 * AdaptiveHamiltonianLowerBound.Access.valueWeight q := by
    funext q; cases q <;> rfl
  refine ⟨fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_, fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_⟩
  · have h := joint_general_tree (s := s) hM hMe hn hμ hε (jointBoolean ι M n μ s)
      (ancillaEmbed _) ancillaEmbed_isometry ((jointFamily M n μ s hμ hμs T hT).access ι)
      (Family.access_unitary ι _) hardCost (implementsOn_joint ι hμ hμs T hT) A.tree A.readout
      A.readout_isometry A.success fun x => by
        have hx := A.accurate x _ (jointSol_solves x)
        rwa [jointFamily_T, unitDirection_jointSol_T hT] at hx
    rw [hhq, worstCost_mul_tree] at h
    have hle : A.tree.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight ≤
        A.tree.worstCost (fun _ => 1) :=
      worstCost_mono_tree _ fun q => by cases q <;> decide
    have hle' : (A.tree.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight : ℝ) ≤
        A.tree.worstCost (fun _ => 1) := by exact_mod_cast hle
    push_cast at h
    constructor <;> linarith
  · have hEnc := Access.callEncoding_isometry
      (ancillaEmbed (Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2)))
      ancillaEmbed_isometry
    have hU := Access.callFamily_unitary
      (Family.access_unitary ι (jointFamily M n μ s hμ hμs T hT))
    have hw := Access.implementsOn_calls_joint (M := M) (n := n) ι hμ hμs T hT
    have h := joint_general_tree (s := s) hM hMe hn hμ hε _ _ hEnc _ hU _ hw A.tree A.readout
      A.readout_isometry A.success fun x => by
        have hx := A.accurate x _ (jointSol_solves x)
        rwa [jointFamily_T, unitDirection_jointSol_T hT] at hx
    rw [hhc, worstCost_mul_tree] at h
    have hle : A.tree.worstCost (fun c => AdaptiveHamiltonianLowerBound.Access.valueWeight c.1) ≤
        A.tree.worstCost (fun _ => 1) :=
      worstCost_mono_tree _ fun c => by cases c.1 <;> decide
    have hle' : (A.tree.worstCost
        (fun c => AdaptiveHamiltonianLowerBound.Access.valueWeight c.1) : ℝ) ≤
        A.tree.worstCost (fun _ => 1) := by exact_mod_cast hle
    push_cast at h
    constructor <;> linarith

/-- **Theorem `odel:thm:joint` for adaptive protocols** (lines 4296-4341): for `s ≥ 4`, `τ ≥ 4`,
`ḡ ≥ 2`, `0 < ε ≤ 1/64`, the joint family at the parameters is in the class (`η = 1`, `T = τ`,
`g ≤ ḡ`) and tree-forces `ḡ √s τ / 400` calls (`c_J = jointConst = 1/400`), for adaptive
solvers over the sampled-time access and over its call forms. The family has `D = 0`
(`SparseLowerBounds.ODE.jointFamily_skew`), `g = √M` (`SparseLowerBounds.ODE.jointFamilyAt_g`),
`ḡ/√2 ≤ √M ≤ ḡ` and dimension at most `3 ḡ² s` (`SparseLowerBounds.ODE.joint_instance_props`). -/
theorem joint_witness_tree {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) :
    TreeWitnesses (jointFamilyAt s τ gbar h.s_ge h.tau_ge) τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  have hb := joint_bound_le h
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  refine ⟨jointFamily_inClass (sqrt_jointM_le (by linarith [h.gbar_ge])), jointFamily_T, ?_⟩
  have hf := joint_forces_tree (s := s) (by omega) (even_jointM gbar)
    (one_le_jointN h.tau_ge) (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega))
    (jointN_time (by linarith [h.tau_ge])) (by linarith [h.eps_le] : 2 * ε ≤ 1)
  exact ⟨fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ⟨hb.trans (hf.1 ι Fl E G A).1,
      hb.trans (hf.1 ι Fl E G A).2⟩,
    fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ⟨hb.trans (hf.2 ι Fl E G A).1,
      hb.trans (hf.2 ι Fl E G A).2⟩⟩

/-- **Remark `odel:rem:homogeneous` for adaptive protocols, native form**: the homogeneous
family tree-forces `β² n √(M 2^μ) / 16` value calls (and as many calls in total),
`β = homCorr ε = (2/3)(15/17 - 2ε)`. -/
theorem hom_forces_tree {M n μ s : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n)
    (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) {T : ℝ} (hT : homBusy M n ≤ T) {ε : ℝ}
    (hε : 2 * ε ≤ 15 / 17) :
    TreeForces (homFamily M n μ s hμ hμs T hT) ε
      (homCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  have hhc : (fun c : Query × Access.CallForm => hardCost c.1) =
      fun c => 2 * AdaptiveHamiltonianLowerBound.Access.valueWeight c.1 := by
    funext c; rcases c with ⟨q, f⟩; cases q <;> rfl
  have hhq : hardCost = fun q => 2 * AdaptiveHamiltonianLowerBound.Access.valueWeight q := by
    funext q; cases q <;> rfl
  have hideal : ∀ x : Promised M n (2 ^ μ), 15 / 17 ≤ halfSign M (oddCand x) *
      (⟪ODEStateNormalization.unitDirection (homEnd M μ s (oddCand x)),
        homHalfObs M μ s (ODEStateNormalization.unitDirection (homEnd M μ s (oddCand x)))⟫_ℂ).re :=
    fun x => homEnd_ideal_corr (by omega) (oddCand x)
  refine ⟨fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_, fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_⟩
  · have h := outer_general_tree (S := HomIndex M μ s) (a := 15 / 17) hM hMe hn hμ hε
      (homBoolean ι M n μ s) (ancillaEmbed _) ancillaEmbed_isometry
      ((homFamily M n μ s hμ hμs T hT).access ι) (Family.access_unitary ι _) hardCost
      (implementsOn_hom ι hμ hμs T hT) A.tree A.readout A.readout_isometry A.success
      (fun x => ODEStateNormalization.unitDirection (homEnd M μ s (oddCand x)))
      (homHalfObs M μ s) homHalfObs_isSelfAdjoint norm_homHalfObs_le hideal fun x => by
        have hx := A.accurate x _ (homSol_solves hμ hμs hT x)
        rwa [homFamily_T, homSol_of_busy_le (by omega) x hT] at hx
    rw [hhq, worstCost_mul_tree] at h
    have hle : A.tree.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight ≤
        A.tree.worstCost (fun _ => 1) :=
      worstCost_mono_tree _ fun q => by cases q <;> decide
    have hle' : (A.tree.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight : ℝ) ≤
        A.tree.worstCost (fun _ => 1) := by exact_mod_cast hle
    push_cast at h
    unfold homCorr
    constructor <;> linarith
  · have hEnc := Access.callEncoding_isometry
      (ancillaEmbed (Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4)))
      ancillaEmbed_isometry
    have hU := Access.callFamily_unitary
      (Family.access_unitary ι (homFamily M n μ s hμ hμs T hT))
    have hw := Access.implementsOn_calls_hom (M := M) (n := n) ι hμ hμs T hT
    have h := outer_general_tree (S := HomIndex M μ s) (a := 15 / 17) hM hMe hn hμ hε
      _ _ hEnc _ hU _ hw A.tree A.readout A.readout_isometry
      A.success (fun x => ODEStateNormalization.unitDirection (homEnd M μ s (oddCand x)))
      (homHalfObs M μ s) homHalfObs_isSelfAdjoint norm_homHalfObs_le hideal fun x => by
        have hx := A.accurate x _ (homSol_solves hμ hμs hT x)
        rwa [homFamily_T, homSol_of_busy_le (by omega) x hT] at hx
    rw [hhc, worstCost_mul_tree] at h
    have hle : A.tree.worstCost (fun c => AdaptiveHamiltonianLowerBound.Access.valueWeight c.1) ≤
        A.tree.worstCost (fun _ => 1) :=
      worstCost_mono_tree _ fun c => by cases c.1 <;> decide
    have hle' : (A.tree.worstCost
        (fun c => AdaptiveHamiltonianLowerBound.Access.valueWeight c.1) : ℝ) ≤
        A.tree.worstCost (fun _ => 1) := by exact_mod_cast hle
    push_cast at h
    unfold homCorr
    constructor <;> linarith

/-- **Remark `odel:rem:homogeneous` for adaptive protocols** (lines 4343-4388): for `s ≥ 4`,
`ḡ ≥ 2`, `τ ≥ 20(1 + log ḡ)` and `0 < ε ≤ 1/64`, the homogeneous (`b = 0`) time-dependent family
is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and tree-forces `ḡ √s τ / 500` calls
(`c_H = homConst = 1/500`). The family has `(4/√17) √M ≤ g ≤ √M`
(`ODELowerBoundExtensions.Homogeneous.homFamily_g`), `ḡ/√2 ≤ √M ≤ ḡ` and dimension at most
`6 ḡ² s` (`ODELowerBoundExtensions.Homogeneous.hom_instance_props`). -/
theorem hom_witness_tree {s : ℕ} {τ gbar ε : ℝ} (h : HomRange s τ gbar ε) :
    TreeWitnesses (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) τ gbar ε
      (homConst * gbar * Real.sqrt s * τ) := by
  have hb := hom_bound_le h
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  have hτ := twenty_le_tau h
  refine ⟨homFamily_inClass (by omega) (sqrt_jointM_le (by linarith [h.gbar_ge])),
    homFamily_T, ?_⟩
  have hf := hom_forces_tree (s := s) (by omega) (even_jointM gbar) (one_le_homN (by linarith))
    (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega)) (homN_time h.gbar_ge h.tau_ge)
    (two_eps_le h.eps_le)
  exact ⟨fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ⟨hb.trans (hf.1 ι Fl E G A).1,
      hb.trans (hf.1 ι Fl E G A).2⟩,
    fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ⟨hb.trans (hf.2 ι Fl E G A).1,
      hb.trans (hf.2 ι Fl E G A).2⟩⟩

end

end AdaptiveODELowerBound.Joint
