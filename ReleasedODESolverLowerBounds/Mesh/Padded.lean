import PhysicalODELowerBound.Mesh.Combined
import ReleasedODESolverLowerBounds.Mesh.Corollaries

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Padded forms of the ODE lower bounds for measured solvers over the general-mesh physical oracle

Manuscript Section `odel:sec:main` ("the lower bounds apply to the upper bounds of the preceding
section"), with measurements inside a run (proof of Lemma `hsl:lem:precision`): the padding claims
of the proof of Theorem `odel:thm:joint` (an unoccupied known block gives maximum sparsity exactly
`s`; "Known zero padding permits any sufficiently large qubit register") and of the proof of Theorem
`odel:thm:combined` ("Pad dimensions to a common known size if desired"), over the physical oracle
of the released general-mesh solver of Theorem `ode:thm:time` and over its call forms.

Every statement is the corresponding statement of `PhysicalODELowerBound.Mesh` (`JointPad`,
`HeraldPad`, `Combined`) with `MeasuredMeshWitnesses` in place of `MeshWitnesses`
(`measuredMeshWitnesses_of_meshWitnesses`), or, for the max forms, with realised measured counts
in place of realised adaptive counts (`MeasuredMeshCost.exists_meshCost_le`); the dimension and
sparsity conjuncts are those of the lifted statements, and hypotheses and constants are those of
the lifted statements.
-/

namespace ReleasedODESolverLowerBounds.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open LowerBoundRemarks.HamiltonianPadding (PadTo)
open ODELowerBoundExtensions.Padding (timePadFamilyAt jointPadFamilyAt mixedPadFamilyAt
  precisionPadFamilyAt SparsityAttained)

open PhysicalODELowerBound.Mesh (joint_witness_pad_mesh joint_common_dimension_mesh
  joint_qubit_register_mesh precision_terms_witness_pad_mesh herald_max_cost_pad_mesh
  combined_max_cost_pad_mesh combined_common_dimension_mesh combined_qubit_register_mesh)
open ReleasedODESolverLowerBounds.Mesh renaming measuredMeshWitnesses_of_meshWitnesses → W

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:joint` after known padding for measured solvers over the general-mesh
physical oracle**: for every finite known register `P`, with or without the dense block, the
padded joint family witnesses `ḡ √s τ / 400` on measured solvers; with the dense block it has
maximum sparsity exactly `s`. -/
theorem joint_witness_pad_measured_mesh (h : JointRange s τ gbar ε) (dense : Bool) (P : Type)
    [Fintype P] [DecidableEq P] :
    MeasuredMeshWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge P)) := by
  exact ⟨W (joint_witness_pad_mesh h dense P).1, (joint_witness_pad_mesh h dense P).2⟩

/-- **Theorem `odel:thm:joint` in any sufficiently large common dimension for measured solvers
over the general-mesh physical oracle**: for every `Nd` at least the dimension of the joint
family, the family padded by `PadTo JointIndex Nd` has dimension exactly `Nd` and witnesses
`ḡ √s τ / 400` on measured solvers; with the dense block it has maximum sparsity exactly `s`. -/
theorem joint_common_dimension_measured_mesh (h : JointRange s τ gbar ε) (dense : Bool) (Nd : ℕ)
    (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd) = Nd ∧
      MeasuredMeshWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd))) := by
  obtain ⟨hc, hw, hs⟩ := joint_common_dimension_mesh h dense Nd hJ
  exact ⟨hc, W hw, hs⟩

/-- **Theorem `odel:thm:joint` on any sufficiently large qubit register for measured solvers over
the general-mesh physical oracle**: for every `q` with `3 ḡ² s ≤ 2^q`, the joint family padded by
`PadTo JointIndex (2^q)` has dimension exactly `2^q` and witnesses `ḡ √s τ / 400` on measured
solvers; with the dense block it has maximum sparsity exactly `s`. -/
theorem joint_qubit_register_measured_mesh (h : JointRange s τ gbar ε) (dense : Bool) (q : ℕ)
    (hq : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q) :
    Fintype.card (JointIndex (jointM gbar) (jointMu s) s ⊕
        PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)) = 2 ^ q ∧
      MeasuredMeshWitnesses (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
        (jointConst * gbar * Real.sqrt s * τ) ∧
      (dense = true → SparsityAttained (jointPadFamilyAt s τ gbar dense h.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q)))) := by
  obtain ⟨hc, hw, hs⟩ := joint_qubit_register_mesh h dense q hq
  exact ⟨hc, W hw, hs⟩

/-- **The precision terms of Theorem `odel:thm:combined` for measured solvers with the padded
`g = 1` families**: on `HSRange` with `ḡ ≥ 1` and any known paddings, a padded `g = 1` family
witnesses `c₀ (√(sτr) + r)` on measured solvers. -/
theorem precision_terms_witness_pad_measured_mesh (h : HSRange τ s ε) (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    MeasuredMeshWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ
        gbar ε (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ
        gbar ε (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  exact (precision_terms_witness_pad_mesh h hg PT PM PP).imp
    W (Or.imp W W)

/-- **Eq. `odel:eq:hsbound` for measured solvers with the padded families, max form over realised
counts.** -/
theorem herald_max_pad_measured_mesh (h : HSRange τ s ε) (PT PM PP : Type) [Fintype PT]
    [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] {qT qM qP : ℝ}
    (hT : MeasuredMeshCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε qT)
    (hM : MeasuredMeshCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε qM)
    (hP : MeasuredMeshCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε
      qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  obtain ⟨T', hT', hTle⟩ := MeasuredMeshCost.exists_meshCost_le hT
  obtain ⟨M', hM', hMle⟩ := MeasuredMeshCost.exists_meshCost_le hM
  obtain ⟨P', hP', hPle⟩ := MeasuredMeshCost.exists_meshCost_le hP
  exact (herald_max_cost_pad_mesh h PT PM PP hT' hM' hP').trans
    (max_le_max hTle (max_le_max hMle hPle))

/-- **Theorem `odel:thm:combined` for measured solvers with the padded families, max form over
realised counts.** -/
theorem combined_max_pad_measured_mesh (h : CombinedRange s τ gbar ε) (dense : Bool)
    (PJ PM PP : Type) [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP]
    [DecidableEq PP] {qJ qM qP : ℝ}
    (hJ : MeasuredMeshCost (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) ε qJ)
    (hM : MeasuredMeshCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) ε qM)
    (hP : MeasuredMeshCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) ε qP) :
    combinedBound s τ gbar ε ≤ max qJ (max qM qP) := by
  obtain ⟨J', hJ', hJle⟩ := MeasuredMeshCost.exists_meshCost_le hJ
  obtain ⟨M', hM', hMle⟩ := MeasuredMeshCost.exists_meshCost_le hM
  obtain ⟨P', hP', hPle⟩ := MeasuredMeshCost.exists_meshCost_le hP
  exact (combined_max_cost_pad_mesh h dense PJ PM PP hJ' hM' hP').trans
    (max_le_max hJle (max_le_max hMle hPle))

/-- **Theorem `odel:thm:combined` in one common dimension for measured solvers over the
general-mesh physical oracle**: for every `Nd` at least the dimensions of the three hard
families, the families padded by `PadTo S Nd` have dimension exactly `Nd`, maximum sparsity
exactly `s` (the joint family with the dense block), and one of them witnesses
`c (ḡ √s τ + √(sτr) + r)` on measured solvers. -/
theorem combined_common_dimension_measured_mesh (h : CombinedRange s τ gbar ε) (dense : Bool)
    (Nd : ℕ) (hJ : Fintype.card (JointIndex (jointM gbar) (jointMu s) s) ≤ Nd)
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
      (MeasuredMeshWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeasuredMeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeasuredMeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) Nd)) τ gbar ε (combinedBound s τ gbar ε)) := by
  obtain ⟨h1, h2, h3, h4, hw⟩ := combined_common_dimension_mesh h dense Nd hJ hM hP
  exact ⟨h1, h2, h3, h4, hw.imp W (Or.imp W W)⟩

/-- **Theorem `odel:thm:combined` on a qubit register for measured solvers over the general-mesh
physical oracle**: for every `q` with `3 ḡ² s ≤ 2^q` and `4 s (τ + r + 1) ≤ 2^q`, the three
families padded by `PadTo S (2^q)` have dimension exactly `2^q` and maximum sparsity exactly `s`
(the joint family when `dense = true`), and one of them witnesses `c (ḡ √s τ + √(sτr) + r)` on
measured solvers. -/
theorem combined_qubit_register_measured_mesh (h : CombinedRange s τ gbar ε) (dense : Bool)
    (q : ℕ) (hqJ : 3 * gbar ^ 2 * s ≤ (2 : ℝ) ^ q)
    (hqH : 4 * s * (τ + hsR τ ε + 1) ≤ (2 : ℝ) ^ q) :
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
      (MeasuredMeshWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge
          (PadTo (JointIndex (jointM gbar) (jointMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeasuredMeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) τ gbar ε
          (combinedBound s τ gbar ε) ∨
        MeasuredMeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q))) τ gbar ε (combinedBound s τ gbar ε)) := by
  obtain ⟨h1, h2, h3, h4, hw⟩ := combined_qubit_register_mesh h dense q hqJ hqH
  exact ⟨h1, h2, h3, h4, hw.imp W (Or.imp W W)⟩

end

end ReleasedODESolverLowerBounds.Mesh
