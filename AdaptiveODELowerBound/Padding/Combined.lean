import AdaptiveODELowerBound.Padding.Joint
import AdaptiveODELowerBound.Padding.Herald
import AdaptiveODELowerBound.Bound
import ODELowerBoundExtensions.Padding.Combined

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:combined` for padded families and adaptive protocols

Manuscript: the proof of Theorem `odel:thm:combined` ("Pad dimensions to a common known size if
desired") and the end of the proof of Theorem `odel:thm:joint` (maximum sparsity exactly `s`,
any sufficiently large register): Theorem `odel:thm:combined` for
the padded joint, mixed and precision families of `ODELowerBoundExtensions.Padding`, for adaptive
solvers over the sampled-time access and over its call forms, with the constant of
`SparseLowerBounds.ODE.combined`.

* `combined_max_cost_pad_tree` (max form over realised value counts) and `combined_pad_tree`
  (family form) for any known paddings `PJ`, `PM`, `PP`.
* `combined_max_cost_common_dimension_tree` (max form) and `combined_common_dimension_tree`
  (family form): for every `Nd` at least the three dimensions, each family padded by
  `HamiltonianPadding.PadTo S Nd` has dimension exactly `Nd`, the sparsity facts hold (the joint
  family with `dense = true`), and one of them tree-witnesses `c (ḡ √s τ + √(sτr) + r)`.
* `combined_qubit_register_tree`: the case `Nd = 2^q` for every `q` with `3 ḡ² s ≤ 2^q` and
  `4 s (τ + r + 1) ≤ 2^q` (proof of Theorem `odel:thm:joint`, "any sufficiently large qubit
  register"; such `q` exist, `ODELowerBoundExtensions.Padding.exists_qubit_register`).
-/

namespace AdaptiveODELowerBound.Padding

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open LowerBoundRemarks.HamiltonianPadding
open ODELowerBoundExtensions.Padding
open AdaptiveODELowerBound.Model

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:combined` for padded families and adaptive protocols, max form over
realised counts**: for any known paddings and realised worst-case value counts of adaptive
solvers of the padded joint, mixed and precision families (each over the sampled-time access or
over its call forms), `c (ḡ √s τ + √(sτr) + r) ≤ max(q_J, q_M, q_P)`. -/
theorem combined_max_cost_pad_tree (h : CombinedRange s τ gbar ε) (dense : Bool)
    (PJ PM PP : Type*) [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP]
    [DecidableEq PP] {qJ qM qP : ℝ}
    (hJ : TreeCost (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) ε qJ)
    (hM : TreeCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) ε qM)
    (hP : TreeCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) ε qP) :
    combinedBound s τ gbar ε ≤ max qJ (max qM qP) := by
  have hH := h.toHSRange
  exact combinedBound_le_max h
    ((joint_witness_pad_tree h.toJointRange dense PJ).1.forces.le_cost hJ)
    (fun hL => ⟨(precision_forces_pad_tree hH hL PP).le_cost hP,
      fun hs' => (precision_forces_sqrt_pad_tree hH hL hs' PP).le_cost hP⟩)
    (fun hL hs => (mixed_forces_pad_tree hH hL hs PM).le_cost hM)

/-- **Theorem `odel:thm:combined` for padded families and adaptive protocols** (proof of Theorem
`odel:thm:combined`): for `s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64` and any known paddings, one of
the three padded families is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and tree-forces
`c (ḡ √s τ + √(sτr) + r)` calls, `c = log 2/(8192π)`. -/
theorem combined_pad_tree (h : CombinedRange s τ gbar ε) (dense : Bool) (PJ PM PP : Type*)
    [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    TreeWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      TreeWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      TreeWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) τ gbar ε
        (combinedBound s τ gbar ε) := by
  have hW := (joint_witness_pad_tree h.toJointRange dense PJ).1
  -- Only the mixed and precision components are used; the time padding slot is `PEmpty`.
  have hI := herald_instances_pad h.toHSRange (by linarith [h.gbar_ge] : 1 ≤ gbar)
    (PEmpty : Type) PM PP
  have hf := forces_or_of_cost₃
    (P₁ := TreeCost (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) ε)
    (P₂ := TreeCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) ε)
    (P₃ := TreeCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) ε)
    (b := combinedBound s τ gbar ε)
    (fun _ _ _ hJ hM hP => combined_max_cost_pad_tree h dense PJ PM PP hJ hM hP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hW.inClass, hW.time_eq, treeForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨hI.2.1.1, hI.2.1.2.1, treeForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨hI.2.2.1, hI.2.2.2.1, treeForces_of_cost hf⟩)

/-- **Theorem `odel:thm:combined` in one common dimension, adaptive protocols, max form over
realised counts** (as `combined_max_common_dimension`): for every `Nd` at least the three
dimensions, the three families padded by `PadTo S Nd` have dimension exactly `Nd`, and for
realised worst-case value counts of adaptive solvers of each (over the sampled-time access or over
its call forms), `c (ḡ √s τ + √(sτr) + r) ≤ max(q_J, q_M, q_P)`. -/
theorem combined_max_cost_common_dimension_tree (h : CombinedRange s τ gbar ε) (dense : Bool)
    (Nd : ℕ) (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) {qJ qM qP : ℝ}
    (hcJ : TreeCost (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
      (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) ε qJ)
    (hcM : TreeCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
      (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) ε qM)
    (hcP : TreeCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
      (PadTo (ScalarIndex (precN τ ε) s) Nd)) ε qP) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      combinedBound s τ gbar ε ≤ max qJ (max qM qP) := by
  exact ⟨card_padTo hJ, card_padTo hM, card_padTo hP,
    combined_max_cost_pad_tree h dense _ _ _ hcJ hcM hcP⟩

/-- **Theorem `odel:thm:combined` in one common dimension, adaptive protocols** (proof of Theorem
`odel:thm:combined`): for every `Nd` at least the dimensions of the three hard families, the
families padded by `PadTo S Nd` have dimension exactly `Nd`, maximum sparsity exactly `s` (the joint
family with the dense block), and one of them is in the class and tree-forces
`c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_common_dimension_tree (h : CombinedRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      ((dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge
          h.tau_ge (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd))) ∧
      (TreeWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        TreeWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        TreeWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd)) τ gbar ε (combinedBound s τ gbar ε)) := by
  -- Only the mixed and precision components are used; the time padding slot is `PEmpty`.
  have hI := herald_instances_pad h.toHSRange (by linarith [h.gbar_ge] : 1 ≤ gbar)
    (PEmpty : Type) (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)
    (PadTo (ScalarIndex (precN τ ε) s) Nd)
  exact ⟨card_padTo hJ, card_padTo hM, card_padTo hP,
    ⟨(joint_witness_pad_tree h.toJointRange dense _).2, hI.2.1.2.2, hI.2.2.2.2⟩,
    combined_pad_tree h dense _ _ _⟩

/-- **Theorem `odel:thm:combined` on a qubit register, adaptive protocols** (end of the proof of
Theorem `odel:thm:joint`, "Known zero padding permits any sufficiently large qubit register", and
the proof of Theorem `odel:thm:combined`; as `combined_qubit_register`): for every `q` with
`3 ḡ² s ≤ 2^q` and `4 s (τ + r + 1) ≤ 2^q`, the three families padded by `PadTo S (2^q)` have
dimension exactly `2^q` and maximum sparsity exactly `s` (the joint family when `dense = true`), and
one of them is in the class and tree-forces `c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_qubit_register_tree (h : CombinedRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hqJ : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) (hqH : 4 * s * (τ + hsR τ ε + 1) ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕
        PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)) = 2 ^ q ∧
      ((dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge
          h.tau_ge (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)))) ∧
      (TreeWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        TreeWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        TreeWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q))) τ gbar ε (combinedBound s τ gbar ε)) := by
  obtain ⟨hJ, hM, hP⟩ := card_le_of_combinedDim h (Nd := 2 ^ q) (by push_cast; exact hqJ)
    (by push_cast; exact hqH)
  exact combined_common_dimension_tree h dense (2 ^ q) hJ hM hP

end

end AdaptiveODELowerBound.Padding
