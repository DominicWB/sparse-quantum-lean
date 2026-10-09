import DeferredMeasurementLowerBounds.Corollaries.ODESolver
import AdaptiveODELowerBound.Theorem

set_option autoImplicit false

/-!
# Theorem `odel:thm:combined` for measured algorithms

Manuscript Theorem `odel:thm:combined` (lines 3697-3709, eq. `odel:eq:combined`) and the solver
class of lines 3669-3680, with line 2364 (purification and deferred measurement).

* `combined_measured`: for `s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, one of the joint, mixed
  and precision families is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces every measured
  solver, over the sampled-time access or over its call forms, to make at least
  `c (ḡ √s τ + √(sτr) + r)` value calls (and as many calls in total) in the worst case over all
  transcripts, `c = combinedConst = log 2/(8192π)`, the constant of the adaptive theorem
  `AdaptiveODELowerBound.combined_tree`.
* `combined_max_measured`: the max form for one measured solver of each family over the
  sampled-time access.
* The witnesses of the third and fourth sentences of the theorem (lines 3705-3708):
  `joint_witness_measured` (the first term, by the inhomogeneous time-dependent joint family of
  Theorem `odel:thm:joint`, lines 3860-3868, with `D = 0` and `g = Θ(ḡ)`) and
  `precision_terms_witness_measured` (the last two terms, by one of the homogeneous
  constant-coefficient families of Lemma `odel:lem:herald`, line 3967, with `D = 0` and
  `g = 1`).

The instance facts are those of the released families: for the joint family `g = √M`
(`SparseLowerBounds.ODE.jointFamilyAt_g`), `ḡ/√2 ≤ √M ≤ ḡ` and dimension at most `3 ḡ² s`
(`SparseLowerBounds.ODE.joint_instance_props`), and `D = 0`
(`SparseLowerBounds.ODE.jointFamily_skew`); for the `g = 1` families `D = 0`, `g = 1`
(`SparseLowerBounds.ODE.hamFamily_props`) and dimension at most `4 s (τ + r + 1)`
(`SparseLowerBounds.Hamiltonian.hard_instances`).

Proof: `Corollaries.measuredForces_of_treeForces` and `Corollaries.plainTreeSolver`: the
deferred, compiled protocol is an adaptive solver over the call forms with at most the measured
solver's worst-case value count; the inverse value call is the value call conjugated by the
known negation of the value register (`Access.star_access_value`), so branch-dependent
directions cost no extra call and no constant is lost. Every other statement of the form
`AdaptiveODELowerBound.Model.TreeWitnesses` transfers in the same way by
`Corollaries.measuredWitnesses_of_treeWitnesses`.
-/

namespace DeferredMeasurementLowerBounds.Corollaries

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound AdaptiveODELowerBound.Model

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Theorem `odel:thm:combined` for measured algorithms** (family form): one of the joint,
mixed and precision families witnesses `combinedConst (ḡ √s τ + √(sτr) + r)` on measured
solvers, over the sampled-time access and over its call forms. -/
theorem combined_measured (h : CombinedRange s τ gbar ε) :
    MeasuredWitnesses (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeasuredWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeasuredWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) := by
  rcases combined_tree h with hw | hw | hw
  · exact Or.inl (measuredWitnesses_of_treeWitnesses hw)
  · exact Or.inr (Or.inl (measuredWitnesses_of_treeWitnesses hw))
  · exact Or.inr (Or.inr (measuredWitnesses_of_treeWitnesses hw))

/-- **Theorem `odel:thm:combined` for measured algorithms, max form**: for one measured solver
of each of the three families over the sampled-time access, the largest worst-case value count
is at least `combinedConst (ḡ √s τ + √(sτr) + r)`. -/
theorem combined_max_measured (h : CombinedRange s τ gbar ε)
    {ιJ ιM ιP EJ EM EP GJ GM GP : Type} [Fintype ιJ] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup EJ] [InnerProductSpace ℂ EJ] [CompleteSpace EJ] [FiniteDimensional ℂ EJ]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : MeasuredSolver (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
      ((jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge).access ιJ) EJ GJ ε)
    (AM : MeasuredSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      ((mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).access ιM) EM GM ε)
    (AP : MeasuredSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      ((precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).access ιP) EP GP ε) :
    combinedBound s τ gbar ε ≤ max (AJ.alg.worstCost valueWeight : ℝ)
      (max (AM.alg.worstCost valueWeight : ℝ) (AP.alg.worstCost valueWeight)) := by
  rcases combined_measured h with hw | hw | hw
  · exact le_max_of_le_left (hw.forces.1 ιJ EJ GJ AJ).1
  · exact le_max_of_le_right (le_max_of_le_left (hw.forces.1 ιM EM GM AM).1)
  · exact le_max_of_le_right (le_max_of_le_right (hw.forces.1 ιP EP GP AP).1)

/-- **The first term of Theorem `odel:thm:combined` for measured algorithms** (third sentence of
the theorem, lines 3705-3707; Theorem `odel:thm:joint`): for `s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`,
`0 < ε ≤ 1/64` (`JointRange`), the inhomogeneous time-dependent joint family with `D = 0` and
`g = √M = Θ(ḡ)` is in the class and forces `ḡ √s τ / 400` value calls (and as many calls in
total) on every measured solver, over the sampled-time access and over its call forms. -/
theorem joint_witness_measured (h : JointRange s τ gbar ε) :
    MeasuredWitnesses (jointFamilyAt s τ gbar h.s_ge h.tau_ge) τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) :=
  measuredWitnesses_of_treeWitnesses (Joint.joint_witness_tree h)

/-- **The last two terms of Theorem `odel:thm:combined` for measured algorithms** (fourth
sentence of the theorem, lines 3707-3708): on `HSRange` and for any `ḡ ≥ 1`, one of the
homogeneous constant-coefficient families with `D = 0` and `g = 1` (time, mixed, precision) is
in the class and forces `c₀ (√(sτr) + r)` value calls on every measured solver,
`c₀ = log 2/(4096π)`. -/
theorem precision_terms_witness_measured (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    MeasuredWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  rcases precision_terms_witness_tree h hg with hw | hw | hw
  · exact Or.inl (measuredWitnesses_of_treeWitnesses hw)
  · exact Or.inr (Or.inl (measuredWitnesses_of_treeWitnesses hw))
  · exact Or.inr (Or.inr (measuredWitnesses_of_treeWitnesses hw))

end

end DeferredMeasurementLowerBounds.Corollaries
