import PhysicalODELowerBound.Mesh.Herald
import PhysicalODELowerBound.Mesh.HeraldPad
import PhysicalODELowerBound.Mesh.Joint
import PhysicalODELowerBound.Mesh.JointPad
import AdaptiveODELowerBound.Bound
import ODELowerBoundExtensions.Padding.Combined
import AdaptiveODELowerBound.Release.Bridge

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:combined` over the general-mesh physical oracle: controlled calls, padding

Manuscript lines 4133-4145 (Theorem `odel:thm:combined`) and 4437-4445 (its proof: "Pad
dimensions to a common known size if desired"), with lines 4335-4340 (known zero padding, any
sufficiently large qubit register), for adaptive solvers over the physical oracle of the
released general-mesh solver and over its call forms (`MeshForces`). The constant is
`c = log 2/(8192π)` (`SparseLowerBounds.ODE.combinedBound`), from the per-family bounds by
`AdaptiveODELowerBound.combinedBound_le_max`.

* `combined_max_cost_mesh`, `combined_mesh`: the joint, mixed and precision families. Without call
  forms the max form is the released `AdaptiveODELowerBound.Release.combined_max_release_tree`,
  restated with an identical statement and rederived from `combined_max_cost_mesh` by
  `MeshCost.of_tree` (`combined_max_release_tree_of_mesh`); here the call forms are included
  and the family form is stated.
* `combined_max_cost_pad_mesh`, `combined_pad_mesh`: the padded joint, mixed and precision
  families, for any dense flag and known paddings.
* `combined_common_dimension_mesh`, `combined_qubit_register_mesh`: the three families padded by
  `PadTo S Nd` to one common dimension `Nd`, in particular `Nd = 2^q`.

As in the manuscript, these are worst-case statements over the class: the three terms are
witnessed by different families and are not multiplied (lines 4443-4444).

Known padding registers range over `Type`, the universe of the families in `MeshForces` and
`ConstForces` and of the released normal-form lemma
`ODELowerBoundExtensions.Release.physicalOracle_normal_form` (the released physical oracles are
universe polymorphic); the sampled-time forms in `AdaptiveODELowerBound` allow any universe.
Nothing is lost: the common-dimension forms use `PadTo S Nd : Type`.
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open LowerBoundRemarks.HamiltonianPadding (PadTo)
open ODELowerBoundExtensions.Padding (jointPadFamilyAt mixedPadFamilyAt precisionPadFamilyAt
  SparsityAttained)
open AdaptiveODELowerBound.Model (forces_or_of_cost₃ TreeSolver)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:combined` over the physical oracle, max form over realised counts**: for
realised worst-case value counts of adaptive solvers of the joint, mixed and precision families
over the general-mesh physical oracle or its call forms,
`c (ḡ √s τ + √(sτr) + r) ≤ max(q_J, q_M, q_P)`, `c = log 2/(8192π)`. -/
theorem combined_max_cost_mesh (h : CombinedRange s τ gbar ε) {qJ qM qP : ℝ}
    (hJ : MeshCost (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) ε qJ)
    (hM : MeshCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε qM)
    (hP : MeshCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε qP) :
    combinedBound s τ gbar ε ≤ max qJ (max qM qP) := by
  have hH := h.toHSRange
  exact AdaptiveODELowerBound.combinedBound_le_max h
    ((joint_forces_mesh h.toJointRange).le_cost hJ)
    (fun hL => ⟨(precision_forces_mesh hH hL).le_cost hP,
      fun hs' => (precision_forces_sqrt_mesh hH hL hs').le_cost hP⟩)
    (fun hL hs => (mixed_forces_mesh hH hL hs).le_cost hM)

/-- **Theorem `odel:thm:combined` over the general-mesh physical oracle** (lines 4133-4145): for
`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, one of the joint, mixed and precision families is in
the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `c (ḡ √s τ + √(sτr) + r)` value calls (and as
many matrix calls) on every adaptive solver over the physical oracle or its call forms
(controlled and controlled-inverse calls included), `c = log 2/(8192π)`. The first term is
witnessed by the joint family (inhomogeneous, time-dependent): `g = √M`
(`SparseLowerBounds.ODE.jointFamilyAt_g`), `ḡ/√2 ≤ √M ≤ ḡ` and dimension at most `3 ḡ² s`
(`SparseLowerBounds.ODE.joint_instance_props`), and `D = 0`
(`SparseLowerBounds.ODE.jointFamily_skew`). The last two are witnessed by the mixed and precision
families (homogeneous, constant-coefficient): `D = 0`, `g = 1`
(`SparseLowerBounds.ODE.hamFamily_props`) and dimension at most `4 s (τ + r + 1)`
(`SparseLowerBounds.Hamiltonian.hard_instances`). -/
theorem combined_mesh (h : CombinedRange s τ gbar ε) :
    MeshWitnesses (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeshWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeshWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) := by
  have hH := h.toHSRange
  have hW := joint_witness_mesh h.toJointRange
  have hg1 : 1 ≤ gbar := by linarith [h.gbar_ge]
  have hf := forces_or_of_cost₃
    (P₁ := MeshCost (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) ε)
    (P₂ := MeshCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε)
    (P₃ := MeshCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε)
    (b := combinedBound s τ gbar ε)
    (fun _ _ _ hJ hM hP => combined_max_cost_mesh h hJ hM hP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hW.inClass, hW.time_eq, meshForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass hH hg1, mixedFamilyAt_T hH,
      meshForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass hH hg1, precisionFamilyAt_T hH,
      meshForces_of_cost hf⟩)

/-- **Theorem `odel:thm:combined` for padded families over the physical oracle, max form over
realised counts**: for any dense flag, known paddings and realised worst-case value counts of
adaptive solvers of the padded joint, mixed and precision families over the general-mesh physical
oracle or its call forms, `c (ḡ √s τ + √(sτr) + r) ≤ max(q_J, q_M, q_P)`. -/
theorem combined_max_cost_pad_mesh (h : CombinedRange s τ gbar ε) (dense : Bool)
    (PJ PM PP : Type) [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP]
    [DecidableEq PP] {qJ qM qP : ℝ}
    (hJ : MeshCost (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) ε qJ)
    (hM : MeshCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) ε qM)
    (hP : MeshCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) ε qP) :
    combinedBound s τ gbar ε ≤ max qJ (max qM qP) := by
  have hH := h.toHSRange
  exact AdaptiveODELowerBound.combinedBound_le_max h
    ((joint_forces_pad_mesh h.toJointRange dense PJ).le_cost hJ)
    (fun hL => ⟨(precision_forces_pad_mesh hH hL PP).le_cost hP,
      fun hs' => (precision_forces_sqrt_pad_mesh hH hL hs' PP).le_cost hP⟩)
    (fun hL hs => (mixed_forces_pad_mesh hH hL hs PM).le_cost hM)

/-- **Theorem `odel:thm:combined` for padded families over the general-mesh physical oracle**
(lines 4437-4445): for any dense flag and known paddings, one of the three padded families is in
the class and forces `c (ḡ √s τ + √(sτr) + r)` value calls (and as many matrix calls) on every
adaptive solver over the physical oracle or its call forms. -/
theorem combined_pad_mesh (h : CombinedRange s τ gbar ε) (dense : Bool) (PJ PM PP : Type)
    [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    MeshWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) τ gbar ε
        (combinedBound s τ gbar ε) := by
  have hW := (joint_witness_pad_mesh h.toJointRange dense PJ).1
  -- Only the mixed and precision components are used; the time padding slot is `PEmpty`.
  have hI := ODELowerBoundExtensions.Padding.herald_instances_pad h.toHSRange
    (by linarith [h.gbar_ge] : 1 ≤ gbar) (PEmpty : Type) PM PP
  have hf := forces_or_of_cost₃
    (P₁ := MeshCost (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) ε)
    (P₂ := MeshCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) ε)
    (P₃ := MeshCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) ε)
    (b := combinedBound s τ gbar ε)
    (fun _ _ _ hJ hM hP => combined_max_cost_pad_mesh h dense PJ PM PP hJ hM hP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hW.inClass, hW.time_eq, meshForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨hI.2.1.1, hI.2.1.2.1, meshForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨hI.2.2.1, hI.2.2.2.1, meshForces_of_cost hf⟩)

/-- **Theorem `odel:thm:combined` in one common dimension over the physical oracle** (lines
4437-4445): for every `Nd` at least the dimensions of the three hard families, the families
padded by `PadTo S Nd` have dimension exactly `Nd`, maximum sparsity exactly `s` (the joint
family with the dense block), and one of them is in the class and mesh-forces
`c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_common_dimension_mesh (h : CombinedRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
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
      (MeshWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd)) τ gbar ε (combinedBound s τ gbar ε)) := by
  -- Only the mixed and precision components are used; the time padding slot is `PEmpty`.
  have hI := ODELowerBoundExtensions.Padding.herald_instances_pad h.toHSRange
    (by linarith [h.gbar_ge] : 1 ≤ gbar)
    (PEmpty : Type) (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)
    (PadTo (ScalarIndex (precN τ ε) s) Nd)
  exact ⟨LowerBoundRemarks.HamiltonianPadding.card_padTo hJ,
    LowerBoundRemarks.HamiltonianPadding.card_padTo hM,
    LowerBoundRemarks.HamiltonianPadding.card_padTo hP,
    ⟨(joint_witness_pad_mesh h.toJointRange dense _).2, hI.2.1.2.2, hI.2.2.2.2⟩,
    combined_pad_mesh h dense _ _ _⟩

/-- **Theorem `odel:thm:combined` on a qubit register over the physical oracle** (line 4340 and
lines 4437-4445): for every `q` with `3 ḡ² s ≤ 2^q` and `4 s (τ + r + 1) ≤ 2^q`, the three
families padded by `PadTo S (2^q)` have dimension exactly `2^q` and maximum sparsity exactly `s`
(the joint family when `dense = true`), and one of them is in the class and mesh-forces
`c (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_qubit_register_mesh (h : CombinedRange s τ gbar ε) (dense : Bool) (q : ℕ)
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
      (MeshWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q))) τ gbar ε (combinedBound s τ gbar ε)) := by
  obtain ⟨hJ, hM, hP⟩ := ODELowerBoundExtensions.Padding.card_le_of_combinedDim h
    (Nd := 2 ^ q) (by push_cast; exact hqJ) (by push_cast; exact hqH)
  exact combined_common_dimension_mesh h dense (2 ^ q) hJ hM hP

/-- **Containment of the released max form**: the released
`AdaptiveODELowerBound.Release.combined_max_release_tree` (three adaptive solvers over the
general-mesh physical oracle itself) is `combined_max_cost_mesh` applied to the realised counts
`MeshCost.of_tree`, with the matrix count at least the value count
(`AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree`). -/
theorem combined_max_release_tree_of_mesh {s : ℕ} {τ gbar ε : ℝ} (h : CombinedRange s τ gbar ε)
    {MJ MM MP : ℕ} (σJ : Fin MJ → Fin (jointN τ + 2)) (σM : Fin MM → Fin 1)
    (σP : Fin MP → Fin 1) (ιJ ιM ιP : Type) [Fintype ιJ] [DecidableEq ιJ] [Fintype ιM]
    [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP] (NJ dJ NM dM NP dP : ℕ)
    {J₀J : _ → SysOp _} {JbJ : _ → Fin MJ → SysOp _} (hJJ : PublicSources J₀J JbJ)
    {J₀M : _ → SysOp _} {JbM : _ → Fin MM → SysOp _} (hJM : PublicSources J₀M JbM)
    {J₀P : _ → SysOp _} {JbP : _ → Fin MP → SysOp _} (hJP : PublicSources J₀P JbP)
    {FlJ FlM FlP EJ EM EP GJ GM GP : Type}
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
      (meshOracle (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) σJ ιJ NJ dJ J₀J JbJ)
      FlJ EJ GJ ε)
    (AM : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σM ιM NM dM J₀M JbM)
      FlM EM GM ε)
    (AP : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σP ιP NP dP J₀P
        JbP) FlP EP GP ε) :
    combinedBound s τ gbar ε ≤
        max (AJ.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (max (AM.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
            (AP.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) ∧
      combinedBound s τ gbar ε ≤
        max (AJ.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (max (AM.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
            (AP.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))) := by
  have hv := combined_max_cost_mesh h (MeshCost.of_tree σJ ιJ NJ dJ hJJ AJ)
    (MeshCost.of_tree σM ιM NM dM hJM AM) (MeshCost.of_tree σP ιP NP dP hJP AP)
  exact ⟨hv, hv.trans (max_le_max
    (AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AJ.tree)
    (max_le_max (AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AM.tree)
      (AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AP.tree)))⟩

end

end PhysicalODELowerBound.Mesh
