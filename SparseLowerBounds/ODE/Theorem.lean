import SparseLowerBounds.ODE.Precision

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Theorem `odel:thm:combined`: the combined worst-case ODE lower bound

Manuscript lines 3697-3709 (statement) and 4001-4009 (proof). For `s ≥ 32`,
`τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64` (`CombinedRange`), every solver for the
time-dependent class (`ODE/Model`, `η = 1`, `T = τ`, `g ≤ ḡ`) has worst-case
matrix-query complexity

  `Q ≥ c (ḡ √s τ + √(sτr) + r)`,  `c = log 2/(8192π)` (`combinedConst`),

with `L = log(1/ε)`, `h = log(e + L/τ)`, `r = L/h` (`Hamiltonian.hsR`).

**Witnesses** (lines 3705-3708). The first term is witnessed by the joint
family of Theorem `odel:thm:joint` (`jointFamilyAt`: inhomogeneous,
time-dependent, `D = 0` by `jointFamily_skew`, `g = √M = Θ(ḡ)`;
`joint_witness`). The last two terms are witnessed, on the whole range, by
the families of the Hamiltonian lower bound read as homogeneous
constant-coefficient ODEs with `D = 0` and `g = 1` (`ODE/Precision`, Lemma
`odel:lem:herald`): `precision_terms_witness` (one of the time, mixed and
precision families), from eq. `odel:eq:hsbound` in the ODE model
(`herald_witness`); its proof uses the mixed and precision bounds for
`L ≥ 64τ` and the time bound alone for `L < 64τ` (line 3996). The headline
`combined` uses the joint, mixed and precision families only, since the time
term `√s τ` of the time family is dominated by the joint term `ḡ √s τ`.

**Direction of the proof.** The quantitative core is the **max form**
`combined_max`: for any three solvers, one for each of the three different
families, the largest of their value-query counts is at least the bound. It
is the assembly of the Hamiltonian lower bound (`Hamiltonian.assembly`,
constant `c₀ = log 2/(4096π)`) with the time term supplied by the joint bound
`Q_J ≥ ḡ √s τ/400 ≥ c_T √s τ`, plus `2 max ≥ Q_J + max`. The headline
**family form** `combined` (one of the three families forces the bound, for
value queries and for all matrix queries) is derived from the max form,
classically: if no family forced it, one cheap
solver per family would contradict `combined_max`.

As in lines 4005-4008, this is a worst-case statement over the class: no
single instance witnesses all terms, and the independent lower bounds are
not multiplied (nor are the two precision terms multiplied by `ḡ`, lines
3715-3719). The initial state and sources are public, and only matrix
queries are counted (lines 3685-3686, 3700). Inverse calls are counted, and
controlled calls are covered by the reduction of `ODE/Model` (**Controlled
calls**) at cost `1` per controlled value call.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open Hamiltonian

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- The parameter range of Theorem `odel:thm:combined` (lines 3697-3699). -/
structure CombinedRange (s : ℕ) (τ gbar ε : ℝ) : Prop where
  s_ge : 32 ≤ s
  tau_ge : 4 ≤ τ
  gbar_ge : 2 ≤ gbar
  eps_pos : 0 < ε
  eps_le : ε ≤ 1 / 64

variable {s : ℕ} {τ gbar ε : ℝ}

/-- The combined range is inside the range of Theorem `odel:thm:joint`. -/
theorem CombinedRange.toJointRange (h : CombinedRange s τ gbar ε) : JointRange s τ gbar ε :=
  ⟨by have := h.s_ge; omega, h.tau_ge, h.gbar_ge, h.eps_pos, h.eps_le⟩

/-- The combined range is inside the range of Theorem `hsl:thm:main`. -/
theorem CombinedRange.toHSRange (h : CombinedRange s τ gbar ε) : HSRange τ s ε :=
  ⟨by linarith [h.tau_ge], h.s_ge, h.eps_pos, h.eps_le⟩

/-- The explicit constant of Theorem `odel:thm:combined`:
`c = log 2/(8192π) = c₀/2`, `c₀` the constant of `hsl:thm:main`. -/
def combinedConst : ℝ := Real.log 2 / (8192 * Real.pi)

/-- The combined bound `c (ḡ √s τ + √(sτr) + r)` (eq. `odel:eq:combined`). -/
def combinedBound (s : ℕ) (τ gbar ε : ℝ) : ℝ :=
  combinedConst * (gbar * Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)

theorem combinedConst_eq : combinedConst = c0 / 2 := by
  unfold combinedConst c0
  ring

theorem combinedConst_pos : 0 < combinedConst := by
  rw [combinedConst_eq]
  linarith [c0_pos]

/-- `c_T = log 2/(192π) ≤ 1/200`. -/
theorem cT_le_inv_200 : cT ≤ 1 / 200 := by
  unfold cT
  rw [div_le_iff₀ (by positivity)]
  linarith [Real.log_two_lt_d9, Real.pi_gt_three]

/-- `c₀ ≤ c_J = 1/400`. -/
theorem c0_le_jointConst : c0 ≤ jointConst := by
  unfold jointConst
  linarith [c0_le, cT_le_inv_32, c0_pos]

/-- **Theorem `odel:thm:combined`, max form** (lines 4001-4009): for one solver
of each of the three families (joint, mixed, precision) at `(s, τ, ḡ, ε)`, the
largest value-query count is at least `c (ḡ √s τ + √(sτr) + r)`.
This is the form from which the family form `combined` is derived. -/
theorem combined_max (h : CombinedRange s τ gbar ε) {ιJ ιM ιP GJ GM GP : Type}
    [Fintype ιJ] [Fintype ιM] [Fintype ιP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : Solver ιJ (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) GJ ε)
    (AM : Solver ιM (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) GM ε)
    (AP : Solver ιP (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) GP ε) :
    combinedBound s τ gbar ε ≤ max (AJ.prog.labelCount .value : ℝ)
      (max (AM.prog.labelCount .value : ℝ) (AP.prog.labelCount .value)) := by
  have hH := h.toHSRange
  have hJ := ((joint_witness h.toJointRange).forces ιJ GJ AJ).1
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) (by linarith [h.tau_ge])
  have hcJ : cT ≤ jointConst * gbar := by
    have := cT_le_inv_200
    unfold jointConst
    linarith [h.gbar_ge]
  have hT : cT * Real.sqrt s * τ ≤ (AJ.prog.labelCount .value : ℝ) := by
    calc cT * Real.sqrt s * τ = cT * (Real.sqrt s * τ) := by ring
      _ ≤ jointConst * gbar * (Real.sqrt s * τ) := mul_le_mul_of_nonneg_right hcJ hS
      _ = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hmax := assembly hH hT
    (fun hL => ⟨(precision_forces hH hL ιP GP AP).1,
      fun hs' => (precision_forces_sqrt hH hL hs' ιP GP AP).1⟩)
    (fun hL hs => (mixed_forces hH hL hs ιM GM AM).1)
  have hg : c0 * gbar * (Real.sqrt s * τ) ≤ jointConst * gbar * (Real.sqrt s * τ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right c0_le_jointConst (by linarith [h.gbar_ge])) hS
  have hle := le_max_left (AJ.prog.labelCount .value : ℝ)
    (max (AM.prog.labelCount .value : ℝ) (AP.prog.labelCount .value))
  have hJ' : jointConst * gbar * (Real.sqrt s * τ) ≤ (AJ.prog.labelCount .value : ℝ) := by
    calc jointConst * gbar * (Real.sqrt s * τ) = jointConst * gbar * Real.sqrt s * τ := by ring
      _ ≤ _ := hJ
  have hsτ : gbar * Real.sqrt s * τ = gbar * (Real.sqrt s * τ) := by ring
  unfold combinedBound
  rw [combinedConst_eq, hsτ]
  linarith [mul_nonneg c0_pos.le hS]

/-- **Theorem `odel:thm:combined`** (lines 3697-3709, proof 4001-4009): for
`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, one of the three families —
the joint family of `odel:thm:joint` (`g = Θ(ḡ)`) or the mixed or precision
family of `odel:lem:herald` (`g = 1`) — is in the class (`η = 1`, `T = τ`,
`g ≤ ḡ`) and forces `c (ḡ √s τ + √(sτr) + r)` value queries (and as many
matrix queries), `c = log 2/(8192π)`.

This headline family form is derived from the max form `combined_max` by
`forces_or_of_max` (if no family forced the bound, one cheap solver per family
would contradict it). It is a worst-case statement over the class: it does not
assert that one instance witnesses all terms, nor that the independent bounds
multiply (lines 4005-4008). Which families witness which terms (third and
fourth sentences of the theorem) is `joint_witness` and `precision_terms_witness`. -/
theorem combined (h : CombinedRange s τ gbar ε) :
    (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge).Witnesses τ gbar ε
        (combinedBound s τ gbar ε) ∨
      (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).Witnesses τ gbar ε
        (combinedBound s τ gbar ε) ∨
      (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])).Witnesses τ gbar ε
        (combinedBound s τ gbar ε) := by
  have hH := h.toHSRange
  have hW := joint_witness h.toJointRange
  have hg1 : 1 ≤ gbar := by linarith [h.gbar_ge]
  have hf := forces_or_of_max (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
    (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
    (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
    (ε := ε) (b := combinedBound s τ gbar ε) (by
      intro ιJ ιM ιP GJ GM GP _ _ _ _ _ _ _ _ _ _ _ _ AJ AM AP
      exact combined_max h AJ AM AP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hW.inClass, hW.time_eq, hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass hH hg1, mixedFamilyAt_T hH, hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass hH hg1, precisionFamilyAt_T hH, hf⟩)

end

end SparseLowerBounds.ODE
end
