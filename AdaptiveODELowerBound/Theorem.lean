import AdaptiveODELowerBound.Joint.Families
import AdaptiveODELowerBound.Herald.Transfer
import AdaptiveODELowerBound.Bound

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:combined` for adaptive protocols

Manuscript: Theorem `odel:thm:combined` (eq. `odel:eq:combined`), eq. `odel:eq:hsbound`, Lemma
`odel:lem:herald` and the proof of the theorem (the class
contains the joint family and the `g = 1` families; the maximum of their bounds is a fixed
fraction of their sum), for adaptive solvers (`Model.TreeSolver`: fresh measured runs with
classical branching and a heralded final protocol) over the sampled-time access and over its call
forms (inverses, controls and controlled inverses), with the constants of the released statements.

* `herald_max_tree`, `herald_max_cost_tree`, `herald_witness_tree`,
  `precision_terms_witness_tree`: eq. `odel:eq:hsbound` with `c₀ = log 2/(4096π)`, and the
  fourth sentence of the theorem (the two precision terms are witnessed by homogeneous
  constant-coefficient families with `D = 0`, `g = 1`), on `HSRange` and any `ḡ ≥ 1`.
* `combined_max_tree` (max form over the sampled-time access), `combined_max_cost_tree` (max
  form over realised value counts of either access shape) and `combined_tree` (family form: one of
  the joint, mixed and precision families tree-witnesses `c (ḡ √s τ + √(sτr) + r)`,
  `c = combinedConst = log 2/(8192π)`), under `CombinedRange` (`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`,
  `0 < ε ≤ 1/64`).

Every disjunct of `combined_tree` implies the corresponding disjunct of
`ODELowerBoundExtensions.Release.combined_retry` and of `SparseLowerBounds.ODE.combined`
(`Model.treeWitnesses_retryWitnesses`, `Model.treeWitnesses_witnesses`).
-/

namespace AdaptiveODELowerBound

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Model

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Eq. `odel:eq:hsbound` for adaptive protocols, max form** (Lemma `odel:lem:herald`): for one
adaptive solver of each of the three `g = 1` families (time, mixed, precision) over the
sampled-time access, the largest worst-case value count is at least
`c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. -/
theorem herald_max_tree (h : HSRange τ s ε)
    {ιT ιM ιP FlT FlM FlP ET EM EP GT GM GP : Type} [Fintype ιT] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup FlT] [InnerProductSpace ℂ FlT] [CompleteSpace FlT]
    [NormedAddCommGroup FlM] [InnerProductSpace ℂ FlM] [CompleteSpace FlM]
    [NormedAddCommGroup FlP] [InnerProductSpace ℂ FlP] [CompleteSpace FlP]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : TreeSolver (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
      ((timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).access ιT) FlT ET GT ε)
    (AM : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      ((mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).access ιM) FlM EM GM ε)
    (AP : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      ((precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).access ιP) FlP EP GP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (AT.tree.worstCost valueWeight : ℝ)
        (max (AM.tree.worstCost valueWeight : ℝ) (AP.tree.worstCost valueWeight)) :=
  assembly h ((Herald.time_forces_tree h).1 ιT FlT ET GT AT).1
    (fun hL => ⟨((Herald.precision_forces_tree h hL).1 ιP FlP EP GP AP).1,
      fun hs' => ((Herald.precision_forces_sqrt_tree h hL hs').1 ιP FlP EP GP AP).1⟩)
    (fun hL hs => ((Herald.mixed_forces_tree h hL hs).1 ιM FlM EM GM AM).1)

/-- **Eq. `odel:eq:hsbound` for adaptive protocols, max form over realised counts**: for realised
worst-case value counts `q_T`, `q_M`, `q_P` of adaptive solvers of the time, mixed and precision
families, each over the sampled-time access or over its call forms,
`c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`. -/
theorem herald_max_cost_tree (h : HSRange τ s ε) {qT qM qP : ℝ}
    (hT : TreeCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε qT)
    (hM : TreeCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qM)
    (hP : TreeCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) :=
  assembly h ((Herald.time_forces_tree h).le_cost hT)
    (fun hL => ⟨(Herald.precision_forces_tree h hL).le_cost hP,
      fun hs' => (Herald.precision_forces_sqrt_tree h hL hs').le_cost hP⟩)
    (fun hL hs => (Herald.mixed_forces_tree h hL hs).le_cost hM)

/-- **Eq. `odel:eq:hsbound` for adaptive protocols, family form** (Lemma `odel:lem:herald`): for
`τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64` (`HSRange`) and any `ḡ ≥ 1`, one of the time, mixed and
precision families (homogeneous, constant-coefficient, `D = 0`, `g = 1`) is in the class
(`η = 1`, `T = τ`, `g ≤ ḡ`) and tree-forces `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. -/
theorem herald_witness_tree (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    TreeWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hf := forces_or_of_cost₃
    (P₁ := TreeCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε)
    (P₂ := TreeCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε)
    (P₃ := TreeCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε)
    (fun _ _ _ hT hM hP => herald_max_cost_tree h hT hM hP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨timeFamilyAt_inClass h hg, timeFamilyAt_T h, treeForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass h hg, mixedFamilyAt_T h, treeForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass h hg, precisionFamilyAt_T h,
      treeForces_of_cost hf⟩)

/-- **The precision terms of Theorem `odel:thm:combined` for adaptive protocols are witnessed by
`g = 1` families** (fourth sentence of the theorem, Theorem `odel:thm:combined`): on `HSRange` and
for any `ḡ ≥ 1`, one of the homogeneous constant-coefficient families with `D = 0` and `g = 1`
(time, mixed, precision) tree-witnesses `c₀ (√(sτr) + r)`. -/
theorem precision_terms_witness_tree (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    TreeWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_tree h hg with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

/-- **Theorem `odel:thm:combined` for adaptive protocols, max form** (proof of Theorem
`odel:thm:combined`): for one adaptive solver of each of the three families (joint, mixed,
precision) over the sampled-time access, the largest worst-case value count is at least
`c (ḡ √s τ + √(sτr) + r)`, `c = log 2/(8192π)`. -/
theorem combined_max_tree (h : CombinedRange s τ gbar ε)
    {ιJ ιM ιP FlJ FlM FlP EJ EM EP GJ GM GP : Type} [Fintype ιJ] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup FlJ] [InnerProductSpace ℂ FlJ] [CompleteSpace FlJ]
    [NormedAddCommGroup FlM] [InnerProductSpace ℂ FlM] [CompleteSpace FlM]
    [NormedAddCommGroup FlP] [InnerProductSpace ℂ FlP] [CompleteSpace FlP]
    [NormedAddCommGroup EJ] [InnerProductSpace ℂ EJ] [CompleteSpace EJ] [FiniteDimensional ℂ EJ]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : TreeSolver (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
      ((jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge).access ιJ) FlJ EJ GJ ε)
    (AM : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      ((mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).access ιM) FlM EM GM ε)
    (AP : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      ((precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).access ιP) FlP EP GP ε) :
    combinedBound s τ gbar ε ≤ max (AJ.tree.worstCost valueWeight : ℝ)
      (max (AM.tree.worstCost valueWeight : ℝ) (AP.tree.worstCost valueWeight)) := by
  have hH := h.toHSRange
  exact combinedBound_le_max h
    ((Joint.joint_witness_tree h.toJointRange).forces.1 ιJ FlJ EJ GJ AJ).1
    (fun hL => ⟨((Herald.precision_forces_tree hH hL).1 ιP FlP EP GP AP).1,
      fun hs' => ((Herald.precision_forces_sqrt_tree hH hL hs').1 ιP FlP EP GP AP).1⟩)
    (fun hL hs => ((Herald.mixed_forces_tree hH hL hs).1 ιM FlM EM GM AM).1)

/-- **Theorem `odel:thm:combined` for adaptive protocols, max form over realised counts**: for
realised worst-case value counts of adaptive solvers of the joint, mixed and precision families,
each over the sampled-time access or over its call forms,
`c (ḡ √s τ + √(sτr) + r) ≤ max(q_J, q_M, q_P)`. -/
theorem combined_max_cost_tree (h : CombinedRange s τ gbar ε) {qJ qM qP : ℝ}
    (hJ : TreeCost (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) ε qJ)
    (hM : TreeCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε qM)
    (hP : TreeCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε qP) :
    combinedBound s τ gbar ε ≤ max qJ (max qM qP) := by
  have hH := h.toHSRange
  exact combinedBound_le_max h ((Joint.joint_witness_tree h.toJointRange).forces.le_cost hJ)
    (fun hL => ⟨(Herald.precision_forces_tree hH hL).le_cost hP,
      fun hs' => (Herald.precision_forces_sqrt_tree hH hL hs').le_cost hP⟩)
    (fun hL hs => (Herald.mixed_forces_tree hH hL hs).le_cost hM)

/-- **Theorem `odel:thm:combined` for adaptive protocols** (with its proof):
for `s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, one of the three families — the joint family of
`odel:thm:joint` (inhomogeneous, time-dependent, `D = 0`, `g = Θ(ḡ)`) or the mixed or precision
family of `odel:lem:herald` (homogeneous, constant-coefficient, `D = 0`, `g = 1`) — is in the
class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces every adaptive solver, over the sampled-time access
or over its call forms, to make at least `c (ḡ √s τ + √(sτr) + r)` value calls (and as many
calls in total) in the worst case, `c = combinedConst = log 2/(8192π)`. The instance facts are
those of the released families: for the joint family `g = √M`
(`SparseLowerBounds.ODE.jointFamilyAt_g`), `ḡ/√2 ≤ √M ≤ ḡ` and dimension at most `3 ḡ² s`
(`SparseLowerBounds.ODE.joint_instance_props`), and `D = 0`
(`SparseLowerBounds.ODE.jointFamily_skew`); for the `g = 1` families `D = 0`, `g = 1`
(`SparseLowerBounds.ODE.hamFamily_props`) and dimension at most `4 s (τ + r + 1)`
(`SparseLowerBounds.Hamiltonian.hard_instances`). -/
theorem combined_tree (h : CombinedRange s τ gbar ε) :
    TreeWitnesses (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      TreeWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      TreeWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) := by
  have hH := h.toHSRange
  have hW := Joint.joint_witness_tree h.toJointRange
  have hg1 : 1 ≤ gbar := by linarith [h.gbar_ge]
  have hf := forces_or_of_cost₃
    (P₁ := TreeCost (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) ε)
    (P₂ := TreeCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε)
    (P₃ := TreeCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε)
    (fun _ _ _ hJ hM hP => combined_max_cost_tree h hJ hM hP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hW.inClass, hW.time_eq, treeForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass hH hg1, mixedFamilyAt_T hH,
      treeForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass hH hg1, precisionFamilyAt_T hH,
      treeForces_of_cost hf⟩)

end

end AdaptiveODELowerBound
