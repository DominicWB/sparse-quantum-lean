import MixedOutputODE.Selection
import GeneralODE.Solver.Interface
import GeneralODE.Plan

/-!
# The mixed-output block-input linear-system solver interface

`ode:thm:general` uses a near-optimal block-input linear-system solver (Costa et al.; Dalzell). eq.
`ode:eq:history-solver-tolerance` requests only a *conditional output trace distance* from it, so
that a possibly mixed solver output is admitted. The hypothesis `MixedBlockSolver f q₀` records
this guarantee together with the heralded success floor `q₀` and a solver circuit and decoder fixed
before the instance, which the proof of the manuscript also uses: the solver keeps a finite work
register `W` (its work and measurement records, held coherently), its decoded output `z` on `s × W`
has squared norm at least `q₀`, and the reduced state of `z / ‖z‖` on `s` is within trace distance
`δ` of the normalized solution. It is a hypothesis, never an axiom.

The released pure-output interface `GeneralODE.Solver.BlockSolver` implies `MixedBlockSolver`
with a trivial work register (`mixed_of_block`).

The explicit accuracy requested by the mixed-output construction is
`mixedDelta g ε = ε / (4096 g²)`, as in eq. `ode:eq:history-solver-tolerance`; the selection and
amplification constants are checked in `mixed_select`, `mixed_amplitude` and
`mixed_error`.
-/

namespace SparseHamiltonian.MixedOutputODE

noncomputable section
open ContinuousLinearMap OracleCircuit ODEMixedOutput ODEStateNormalization GeneralODE
  GeneralODE.Solver GeneralODE.Registers
open scoped InnerProduct BigOperators

/-- **Hypothesis.** A block-input quantum linear-system solver with query
complexity `f κ δ`, heralded success probability at least `q₀`, and
conditional output trace distance at most `δ` on the solution register after
the solver's work register `W` is discarded. The circuit, the work register
and the decoder depend only on the registers, `a₀`, `e₀`, `κ` and `δ`. -/
def MixedBlockSolver (f : ℝ → ℝ → ℝ) (q₀ : ℝ) : Prop :=
  ∀ (s a : Type) [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    (a₀ : a) (e₀ : EuclideanSpace ℂ s), ‖e₀‖ = 1 →
  ∀ κ δ : ℝ, 1 ≤ κ → 0 < δ → δ ≤ 1 / 2 →
  ∃ (w : ℕ) (w₀ : Fin w) (ctrl : Fin w → Bool) (W : Type) (_ : Fintype W)
    (_ : DecidableEq W)
    (S : MultiOracleCircuit.Program (solverOracle s a w ctrl))
    (out : EuclideanSpace ℂ (s × W) →L[ℂ] Space s a w),
    out† ∘L out = 1 ∧ (S.count : ℝ) ≤ f κ δ ∧
    ∀ U B : EuclideanSpace ℂ (s × a) →L[ℂ] EuclideanSpace ℂ (s × a),
      IsUnitary U → IsUnitary B →
      ∀ β x : EuclideanSpace ℂ s, ‖β‖ = 1 →
        B (embed a₀ e₀) = embed a₀ β →
        (∀ v, ‖v‖ ≤ κ * ‖block a₀ U v‖) →
        block a₀ U x = β →
        q₀ ≤ ‖(out†) (S.eval (U, B) (initial w₀ (embed a₀ e₀)))‖ ^ 2 ∧
        ∃ h : (ptrace (pureOperator (unitDirection
              ((out†) (S.eval (U, B) (initial w₀ (embed a₀ e₀)))))) -
            pureOperator (unitDirection x)).toLinearMap.IsSymmetric,
          hermitianTraceDistance (ptrace (pureOperator (unitDirection
              ((out†) (S.eval (U, B) (initial w₀ (embed a₀ e₀)))))))
            (pureOperator (unitDirection x)) h ≤ δ

section Unit

variable {s : Type} [Fintype s]

theorem slot_unit_isometry : (slot (n := s) ())† ∘L slot () = 1 := by
  rw [slot_adjoint_comp_slot, if_pos rfl]

theorem slot_comp_adjoint_unit : slot (n := s) () ∘L (slot ())† = 1 := by
  have h := sum_slot_comp_adjoint (n := s) (W := Unit)
  rwa [Fintype.sum_unique] at h

theorem norm_slot_unit (v : EuclideanSpace ℂ s) : ‖slot () v‖ = ‖v‖ :=
  (slot (n := s) ()).norm_map_iff_adjoint_comp_self.mpr slot_unit_isometry v

theorem unitDirection_slot_unit (v : EuclideanSpace ℂ s) :
    unitDirection (slot () v) = slot () (unitDirection v) := by
  rw [unitDirection, unitDirection, norm_slot_unit, ← Complex.coe_smul, ← Complex.coe_smul,
    map_smul]

theorem ptrace_pure_slot_unit (v : EuclideanSpace ℂ s) :
    ptrace (pureOperator (slot (W := Unit) () v)) = pureOperator v := by
  rw [ptrace_pure, Fintype.sum_unique]
  congr 1
  have h := congrArg (fun A => A v) (slot_unit_isometry (s := s))
  simpa using h

end Unit

/-- The released pure-output solver interface implies the mixed-output one, with a trivial work
register. -/
theorem mixed_of_block (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (h : BlockSolver f q₀) :
    MixedBlockSolver f q₀ := by
  intro s a _ _ _ _ a₀ e₀ he κ δ hκ hδ hδ1
  obtain ⟨w, w₀, ctrl, S, out, hout, hcount, hsolve⟩ := h s a a₀ e₀ he κ δ hκ hδ hδ1
  refine ⟨w, w₀, ctrl, Unit, inferInstance, inferInstance, S, out ∘L (slot ())†, ?_, hcount, ?_⟩
  · rw [adjoint_comp, adjoint_adjoint, comp_assoc, ← comp_assoc (out†), hout, one_def, id_comp]
    exact slot_comp_adjoint_unit
  · intro U B hU hB β x hβ hBβ hκU hx
    obtain ⟨hq, ω, hω, hdir⟩ := hsolve U B hU hB β x hβ hBβ hκU hx
    set z := (out†) (S.eval (U, B) (initial w₀ (embed a₀ e₀))) with hzdef
    have hz' : ((out ∘L (slot (n := s) ())†)†) (S.eval (U, B) (initial w₀ (embed a₀ e₀))) =
        slot () z := by
      rw [adjoint_comp, adjoint_adjoint, comp_apply]
    rw [hz', norm_slot_unit, unitDirection_slot_unit, ptrace_pure_slot_unit]
    refine ⟨hq, pure_sub_isSymmetric _ _, ?_⟩
    -- the decoded output is nonzero
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hx
      rw [← hx, norm_zero] at hβ
      norm_num at hβ
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hdir
      simp only [unitDirection, norm_zero, inv_zero, smul_zero, zero_sub, norm_neg] at hdir
      rw [show ‖‖x‖⁻¹ • x‖ = 1 from unitDirection_norm x hx0] at hdir
      linarith
    exact (hermitianTraceDistance_pure_phase_le _ _ (unitDirection_norm z hz0)
      (unitDirection_norm x hx0) ω hω _).trans hdir

/-- Accuracy requested from the mixed-output solver, eq. `ode:eq:history-solver-tolerance`. -/
def mixedDelta (g ε : ℝ) : ℝ := ε / (4096 * g ^ 2)

section Constants

variable {g ε q₀ p : ℝ}

theorem mixedDelta_pos (hg : 1 ≤ g) (hε : 0 < ε) : 0 < mixedDelta g ε := by
  unfold mixedDelta
  have : 0 < g := by linarith
  positivity

theorem mixedDelta_le (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) : mixedDelta g ε ≤ 1 / 2 := by
  unfold mixedDelta
  have hg2 : 1 ≤ g ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The squared extraction ratio. -/
theorem theta_sq_ge (hg : 1 ≤ g) (hε1 : ε ≤ 1 / 2) : 225 / (16384 * g ^ 2) ≤ Plan.theta g ε ^ 2 := by
  unfold Plan.theta
  have hg0 : 0 < g := by linarith
  have h1 : 15 / 16 ≤ 1 - ε / 8 := by linarith
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (15 / 16 : ℝ) ^ 2 ≤ (1 - ε / 8) ^ 2 := pow_le_pow_left₀ (by norm_num) h1 2
  nlinarith

theorem two_mixedDelta_le (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    2 * mixedDelta g ε ≤ 4 / (16384 * g ^ 2) := by
  unfold mixedDelta
  have hg0 : 0 < g := by linarith
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg g]

/-- The ideal selection probability exceeds twice the solver accuracy. -/
theorem mixed_select (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hp : Plan.theta g ε ^ 2 ≤ p) : 2 * mixedDelta g ε < p := by
  have h1 := theta_sq_ge hg hε1
  have h2 := two_mixedDelta_le hg hε hε1
  have hg0 : 0 < g := by linarith
  have h3 : 4 / (16384 * g ^ 2) < 225 / (16384 * g ^ 2) :=
    div_lt_div_of_pos_right (by norm_num) (by positivity)
  linarith

theorem mixed_gap (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hp : Plan.theta g ε ^ 2 ≤ p) :
    221 / (16384 * g ^ 2) ≤ p - 2 * mixedDelta g ε := by
  have h1 := theta_sq_ge hg hε1
  have h2 := two_mixedDelta_le hg hε hε1
  have hg0 : 0 < g := by linarith
  have h3 : 225 / (16384 * g ^ 2) - 4 / (16384 * g ^ 2) = 221 / (16384 * g ^ 2) := by
    field_simp
    norm_num
  linarith

/-- The amplitude handed to the amplification. -/
theorem mixed_amplitude (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hq₀ : 0 < q₀)
    (hp : Plan.theta g ε ^ 2 ≤ p) :
    1 / (2 * Plan.gain g q₀) ≤ Real.sqrt q₀ * Real.sqrt (p - 2 * mixedDelta g ε) := by
  have hg0 : 0 < g := by linarith
  have hgap := mixed_gap hg hε hε1 hp
  have hsq : 0 < Real.sqrt q₀ := Real.sqrt_pos.mpr hq₀
  have hlow : 1 / (10 * g) ≤ Real.sqrt (p - 2 * mixedDelta g ε) := by
    rw [show 1 / (10 * g) = Real.sqrt ((1 / (10 * g)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    calc
      (1 / (10 * g)) ^ 2 = 1 / (100 * g ^ 2) := by field_simp; ring
      _ ≤ 221 / (16384 * g ^ 2) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg g]
      _ ≤ _ := hgap
  unfold Plan.gain
  have heq : 1 / (2 * (5 * g / Real.sqrt q₀)) = Real.sqrt q₀ * (1 / (10 * g)) := by
    field_simp
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left hlow hsq.le

/-- The error allocation: selection plus the history accuracy. -/
theorem mixed_error (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hp : Plan.theta g ε ^ 2 ≤ p) :
    2 * mixedDelta g ε / (p - 2 * mixedDelta g ε) + 2 * (ε / 8) ≤ ε := by
  have hg0 : 0 < g := by linarith
  have hgap := mixed_gap hg hε hε1 hp
  have hpos : 0 < p - 2 * mixedDelta g ε := lt_of_lt_of_le (by positivity) hgap
  have h1 : 2 * mixedDelta g ε / (p - 2 * mixedDelta g ε) ≤
      2 * mixedDelta g ε / (221 / (16384 * g ^ 2)) :=
    div_le_div_of_nonneg_left (by have := mixedDelta_pos hg hε; positivity) (by positivity) hgap
  have h2 : 2 * mixedDelta g ε / (221 / (16384 * g ^ 2)) = 8 * ε / 221 := by
    unfold mixedDelta
    field_simp
    ring
  rw [h2] at h1
  linarith

end Constants

end

end SparseHamiltonian.MixedOutputODE
