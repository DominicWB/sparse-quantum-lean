import AdaptiveODELowerBound.Joint.Families
import AdaptiveODELowerBound.Padding.Readout
import ODELowerBoundExtensions.Padding.JointTheorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The padded joint families against adaptive protocols

Manuscript: the end of the proof of Theorem `odel:thm:joint` (the dense block `2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ`
for maximum sparsity exactly `s`; known zero padding to any sufficiently large register) for the
joint family of Theorem `odel:thm:joint`, for adaptive solvers over the sampled-time access and over
its call forms.

The padded families are the released `ODELowerBoundExtensions.Padding.jointDenseFamily`,
`jointPadFamily`, `jointDenseFamilyAt`, `jointPadFamilyAt`. As in the released library, hardness
is re-derived from the Boolean implementations (`implementsOn_jointDense`,
`implementsOn_jointPad`, with `Access.implementsOn_callFamily` for the call forms) through
`Joint.joint_general_tree`; the padded readout is transferred by `treeAccurate_of_zeroPad`.

* `valueCalls_of_hardCost_tree`: a worst-case Boolean cost (`hardCost`) of at least `2b` gives
  at least `b` value calls and at least `b` calls in total.
* `joint_forces_dense_tree`, `joint_forces_pad_tree`: the native constant `β² n √(M 2^μ) / 16`.
* `joint_witness_dense_tree`, `joint_witness_pad_tree` (on `JointRange`): `ḡ √s τ / 400`, and
  maximum sparsity exactly `s` with the dense block.
* `joint_common_dimension_tree`, `joint_qubit_register_tree`: the family padded by
  `PadTo JointIndex Nd` has dimension exactly `Nd` for every `Nd` at least the unpadded
  dimension, in particular `Nd = 2^q` whenever `3 ḡ² s ≤ 2^q` ("any sufficiently large qubit
  register", proof of Theorem `odel:thm:joint`).
-/

namespace AdaptiveODELowerBound.Padding

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open LowerBoundRemarks.HamiltonianPadding
  (PadTo padTable padReadout padReadout_comp_isometry card_padTo)
open ODELowerBoundExtensions.Padding
open AdaptiveODELowerBound.Model

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

section General

/-- **From the Boolean count to value calls**: if an adaptive protocol whose labels are read as
queries through `v` has worst-case Boolean cost (`hardCost`: two per value call, none per location
call) at least `2b`, then it makes at least `b` value calls and at least `b` calls in total in the
worst case. -/
theorem valueCalls_of_hardCost_tree {W Fl E X L : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {O : L → X → W →L[ℂ] W} (T : SparseLinearSystems.Protocol.Tree O Fl E) (v : L → Query)
    {b : ℝ} (h : 2 * b ≤ T.worstCost (fun l => hardCost (v l))) :
    b ≤ T.worstCost (fun l => AdaptiveHamiltonianLowerBound.Access.valueWeight (v l)) ∧
      b ≤ T.worstCost (fun _ => 1) := by
  have hw : (fun l => hardCost (v l)) =
      fun l => 2 * AdaptiveHamiltonianLowerBound.Access.valueWeight (v l) := by
    funext l
    cases v l <;> rfl
  rw [hw, worstCost_mul_tree] at h
  push_cast at h
  have h1 : b ≤ T.worstCost (fun l => AdaptiveHamiltonianLowerBound.Access.valueWeight (v l)) := by
    linarith
  refine ⟨h1, h1.trans ?_⟩
  exact_mod_cast worstCost_mono_tree T fun l => by
    cases v l <;> simp [AdaptiveHamiltonianLowerBound.Access.valueWeight]

variable {M n μ s B : ℕ} {dense : Bool}

/-- **Theorem `odel:thm:joint` for the dense family, adaptive protocols, native form**: the
densely padded joint family tree-forces `β² n √(M 2^μ) / 16` value calls (and as many calls in
total), `β = jointCorr ε`. -/
theorem joint_forces_dense_tree (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {ε : ℝ}
    (hε : 2 * ε ≤ 1) :
    TreeForces (jointDenseFamily M n μ s B dense hμ hμs hμB T hT) ε
      (jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  refine ⟨fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_, fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_⟩
  · have h := Joint.joint_general_tree (s := s) hM hMe hn hμ hε
      (stageBoolean ι M n μ B (jointDenseTable M μ s B dense)) (ancillaEmbed _)
      ancillaEmbed_isometry ((jointDenseFamily M n μ s B dense hμ hμs hμB T hT).access ι)
      (Family.access_unitary ι _) hardCost (implementsOn_jointDense ι) A.tree A.readout
      A.readout_isometry A.success fun x => by
        have hx := A.accurate x _ (jointDenseSol_solves x)
        rwa [jointDenseFamily_T, unitDirection_jointSol_T hT] at hx
    exact valueCalls_of_hardCost_tree A.tree id
      (by change _ ≤ ((A.tree.worstCost hardCost : ℕ) : ℝ); linarith)
  · have h := Joint.joint_general_tree (s := s) hM hMe hn hμ hε
      (Access.callBoolean (stageBoolean ι M n μ B (jointDenseTable M μ s B dense)))
      (Access.callEncoding
        (ancillaEmbed (Workspace ι (JointIndex M μ s) (Hamiltonian.Word B) (n + 2))))
      (Access.callEncoding_isometry _ ancillaEmbed_isometry)
      (Access.callFamily ((jointDenseFamily M n μ s B dense hμ hμs hμB T hT).access ι))
      (Access.callFamily_unitary (Family.access_unitary ι _)) (fun c => hardCost c.1)
      (Access.implementsOn_callFamily _ membership _ _
        (Family.access_unitary ι _) hardCost (implementsOn_jointDense ι))
      A.tree A.readout A.readout_isometry A.success fun x => by
        have hx := A.accurate x _ (jointDenseSol_solves x)
        rwa [jointDenseFamily_T, unitDirection_jointSol_T hT] at hx
    exact valueCalls_of_hardCost_tree A.tree Prod.fst (by linarith)

/-- **Theorem `odel:thm:joint` for the zero-padded dense family, adaptive protocols, native
form**: for every known padding `P`, the padded joint family tree-forces
`β² n √(M 2^μ) / 16` value calls (and as many calls in total). -/
theorem joint_forces_pad_tree (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {ε : ℝ}
    (hε : 2 * ε ≤ 1) (P : Type*) [Fintype P] [DecidableEq P] :
    TreeForces (jointPadFamily M n μ s B dense P hμ hμs hμB T hT) ε
      (jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  let i₀ : JointIndex M μ s := Sum.inr ⟨0, lt_of_lt_of_le (Nat.two_pow_pos μ) hμs⟩
  refine ⟨fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_, fun ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A => ?_⟩
  · have h := Joint.joint_general_tree (s := s) (G := Joint (Option P) G) hM hMe hn hμ hε
      (stageBoolean ι M n μ B (padTable (jointDenseTable M μ s B dense) P)) (ancillaEmbed _)
      ancillaEmbed_isometry ((jointPadFamily M n μ s B dense P hμ hμs hμB T hT).access ι)
      (Family.access_unitary ι _) hardCost (implementsOn_jointPad ι) A.tree
      (padReadout P G i₀ ∘L A.readout) (padReadout_comp_isometry i₀ A.readout A.readout_isometry)
      A.success fun x => by
        have hx := treeAccurate_of_zeroPad jointPadFamily_zeroPad A i₀ x (jointDenseSol_solves x)
        rwa [jointDenseFamily_T, unitDirection_jointSol_T hT] at hx
    exact valueCalls_of_hardCost_tree A.tree id
      (by change _ ≤ ((A.tree.worstCost hardCost : ℕ) : ℝ); linarith)
  · have h := Joint.joint_general_tree (s := s) (G := Joint (Option P) G) hM hMe hn hμ hε
      (Access.callBoolean (stageBoolean ι M n μ B (padTable (jointDenseTable M μ s B dense) P)))
      (Access.callEncoding
        (ancillaEmbed (Workspace ι (JointIndex M μ s ⊕ P) (Hamiltonian.Word B) (n + 2))))
      (Access.callEncoding_isometry _ ancillaEmbed_isometry)
      (Access.callFamily ((jointPadFamily M n μ s B dense P hμ hμs hμB T hT).access ι))
      (Access.callFamily_unitary (Family.access_unitary ι _)) (fun c => hardCost c.1)
      (Access.implementsOn_callFamily _ membership _ _
        (Family.access_unitary ι _) hardCost (implementsOn_jointPad ι))
      A.tree (padReadout P G i₀ ∘L A.readout)
      (padReadout_comp_isometry i₀ A.readout A.readout_isometry) A.success fun x => by
        have hx := treeAccurate_of_zeroPad jointPadFamily_zeroPad A i₀ x (jointDenseSol_solves x)
        rwa [jointDenseFamily_T, unitDirection_jointSol_T hT] at hx
    exact valueCalls_of_hardCost_tree A.tree Prod.fst (by linarith)

end General

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:joint` with maximum sparsity exactly `s`, adaptive protocols** (Theorem
`odel:thm:joint`): for `s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, the densely padded joint family is
in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and tree-forces `ḡ √s τ / 400` calls. -/
theorem joint_witness_dense_tree (h : JointRange s τ gbar ε) :
    TreeWitnesses (jointDenseFamilyAt s τ gbar h.s_ge h.tau_ge) τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  refine TreeWitnesses.mono ⟨jointDenseFamily_inClass
      (fun _ => (Hamiltonian.le_two_pow_padExp s).trans (Nat.pow_le_pow_left (by norm_num) _))
      (sqrt_jointM_le (by linarith [h.gbar_ge])),
    jointDenseFamily_T, joint_forces_dense_tree (s := s) (by omega) (even_jointM gbar)
      (one_le_jointN h.tau_ge) (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega))
      (jointMu_le_padExp s) (jointN_time (by linarith [h.tau_ge])) (by linarith [h.eps_le])⟩
    (joint_bound_le h)

/-- **Theorem `odel:thm:joint` after known zero padding, adaptive protocols** (proof of Theorem
`odel:thm:joint`): for every finite known register `P`, with or without the dense block, the padded
joint family is in the class and tree-forces `ḡ √s τ / 400` calls; with the dense block it has
maximum sparsity exactly `s`. The padded family keeps `g = √M`, `g = Θ(ḡ)`
(`ODELowerBoundExtensions.Padding.jointPadFamilyAt_g`). -/
theorem joint_witness_pad_tree (h : JointRange s τ gbar ε) (dense : Bool) (P : Type*)
    [Fintype P] [DecidableEq P] :
    TreeWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P)) := by
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  refine ⟨TreeWitnesses.mono ⟨jointPadFamily_inClass
      (fun hd => (le_two_pow_jointPadBits s hd).trans (Nat.pow_le_pow_left (by norm_num) _))
      (sqrt_jointM_le (by linarith [h.gbar_ge])),
    jointPadFamily_T, joint_forces_pad_tree (s := s) (dense := dense) (by omega)
      (even_jointM gbar) (one_le_jointN h.tau_ge) (one_le_jointMu (by omega))
      (two_pow_jointMu_le (by omega)) (jointMu_le_jointPadBits s dense)
      (jointN_time (by linarith [h.tau_ge])) (by linarith [h.eps_le]) P⟩ (joint_bound_le h),
    fun hd => by subst hd; exact jointPadFamily_sparsityAttained rfl⟩

/-- **Theorem `odel:thm:joint` in any sufficiently large common dimension, adaptive protocols**
(as `joint_common_dimension`): for every `Nd` at least the dimension of
`jointFamilyAt`, the joint family padded by `PadTo JointIndex Nd`, with or without the dense block,
has dimension exactly `Nd`, is in the class and tree-forces `ḡ √s τ / 400` calls; with the dense
block it has maximum sparsity exactly `s`. -/
theorem joint_common_dimension_tree (h : JointRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      TreeWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) := by
  exact ⟨card_padTo hJ, joint_witness_pad_tree h dense _⟩

/-- **Theorem `odel:thm:joint` on any sufficiently large qubit register, adaptive protocols**
("Known zero padding permits any sufficiently large qubit register"; as
`joint_qubit_register`): for every `q` with `3 ḡ² s ≤ 2^q`, the joint family padded by
`PadTo JointIndex (2^q)`, with or without the dense block, has dimension exactly `2^q`, is in the
class and tree-forces `ḡ √s τ / 400` calls; with the dense block it has maximum sparsity exactly
`s`. -/
theorem joint_qubit_register_tree (h : JointRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hq : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      TreeWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) := by
  have hc := (joint_instance_props (s := s) h.s_ge h.gbar_ge).2.2
  have hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ 2 ^ q := by
    have : (Fintype.card (JointIndex (jointM gbar) (jointMu s) s) : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  exact joint_common_dimension_tree h dense (2 ^ q) hJ

end

end AdaptiveODELowerBound.Padding
