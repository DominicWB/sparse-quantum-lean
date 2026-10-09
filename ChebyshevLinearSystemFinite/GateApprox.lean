import SparseHamiltonian.EncodedLabeledProgram
import SparseHamiltonian.OracleStability

set_option autoImplicit false

/-!
# Programs with approximate known gates

The finite-gate allowance of the manuscript (equation `qls:eq:finitedegree` and the allocation
paragraph after equation `qls:eq:bernoulli`) lets every known, input-independent gate of a
circuit be synthesised approximately, while the oracle calls stay exactly the same. For the
released program model (`MultiOracleCircuit.Program`: fixed unitary gates, labelled queries and
inverse queries, sequential composition) this is the relation `GateApprox p q e`:

* every fixed gate `U` of `p` is replaced in `q` by an arbitrary query-free program, that is, a
  finite circuit of known unitary gates, whose unitary is within `e_U` of `U` in operator norm;
* every query and every inverse query of `p` is kept, with the same label, in the same position;
* `e` bounds the sum of the gate errors `e_U`.

Consequences (the norm bound `eval_sub_le` needs unitary oracles):

* `GateApprox.cost_eq`, `GateApprox.count_eq`: `q` makes exactly the oracle calls of `p`, for
  every weighting of the labels;
* `GateApprox.eval_sub_le`: telescoping, `‖q(x) - p(x)‖ ≤ e` for every input `x`;
* `GateApprox.adjoint`: the reversed programs are approximations with the same error;
* `GateApprox.compile`: replacing every logical instruction of a compiled program
  (`EncodedLabeledProgram.compile`) by an approximation within `ρ` gives an approximation of
  the compiled program within (number of logical queries) `· ρ`.

No relation between the approximations of different gates is assumed: an approximate
reflection need not be an involution, and the approximation of a reversed circuit need not be
the adjoint of the approximation of the forward circuit.
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open ContinuousLinearMap SparseHamiltonian OracleCircuit
open scoped InnerProduct

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- **Known-gate approximation.** `GateApprox p q e`: the program `q` makes exactly the oracle
calls of `p` (same labels, directions and order); every fixed gate `U` of `p` is replaced by a
query-free program (a finite circuit of known unitary gates) within operator-norm error `e_U`
of `U`; and `e` bounds the sum of these errors. -/
inductive GateApprox {O : L → X → K →L[ℂ] K} :
    MultiOracleCircuit.Program O → MultiOracleCircuit.Program O → ℝ → Prop
  /-- A fixed gate `U` is replaced by any query-free program `q` (a finite circuit of known
  unitary gates) whose unitary is within `e` of `U` in operator norm. -/
  | fixed {U : K →L[ℂ] K} (hU : IsUnitary U) {q : MultiOracleCircuit.Program O} {e : ℝ}
      (hq : q.count = 0) (he : ∀ x, ‖q.eval x - U‖ ≤ e) : GateApprox (.fixed U hU) q e
  /-- A query is kept unchanged (same label), with any nonnegative error budget. -/
  | query (l : L) {e : ℝ} (he : 0 ≤ e) : GateApprox (.query l) (.query l) e
  /-- An inverse query is kept unchanged (same label), with any nonnegative error budget. -/
  | queryAdjoint (l : L) {e : ℝ} (he : 0 ≤ e) : GateApprox (.queryAdjoint l) (.queryAdjoint l) e
  /-- Sequential composition: the approximations of the two parts are composed in the same
  order and their error budgets add. -/
  | seq {p p' q q' : MultiOracleCircuit.Program O} {e₁ e₂ e : ℝ} (hp : GateApprox p p' e₁)
      (hq : GateApprox q q' e₂) (he : e₁ + e₂ ≤ e) : GateApprox (.seq p q) (.seq p' q') e

namespace GateApprox

variable {O : L → X → K →L[ℂ] K}

/-- Every program is its own approximation with error zero (exact gates). -/
theorem refl : ∀ p : MultiOracleCircuit.Program O, GateApprox p p 0
  | .fixed U hU => .fixed hU rfl (fun _ => by rw [MultiOracleCircuit.Program.eval_fixed, sub_self,
      norm_zero])
  | .query l => .query l le_rfl
  | .queryAdjoint l => .queryAdjoint l le_rfl
  | .seq p q => .seq (refl p) (refl q) (by norm_num)

/-- Enlarging the error budget. -/
theorem mono {p q : MultiOracleCircuit.Program O} {e e' : ℝ} (h : GateApprox p q e)
    (hee : e ≤ e') : GateApprox p q e' := by
  induction h generalizing e' with
  | fixed hU hq he => exact .fixed hU hq (fun x => (he x).trans hee)
  | query l he => exact .query l (he.trans hee)
  | queryAdjoint l he => exact .queryAdjoint l (he.trans hee)
  | seq hp hq he _ _ => exact .seq hp hq (he.trans hee)

/-- A query-free program has weighted cost zero. -/
theorem cost_of_count_zero (p : MultiOracleCircuit.Program O) (h : p.count = 0)
    (w : L → ℕ) : p.cost w = 0 := by
  induction p with
  | fixed U hU => rfl
  | query l => simp at h
  | queryAdjoint l => simp at h
  | seq p q hp hq =>
    have hh : p.count = 0 ∧ q.count = 0 := Nat.add_eq_zero_iff.mp h
    rw [MultiOracleCircuit.Program.cost_seq, hp hh.1, hq hh.2]

/-- **The oracle calls are unchanged**, for every weighting of the labels. -/
theorem cost_eq {p q : MultiOracleCircuit.Program O} {e : ℝ} (h : GateApprox p q e)
    (w : L → ℕ) : q.cost w = p.cost w := by
  induction h with
  | fixed hU hq he => exact cost_of_count_zero _ hq w
  | query l he => rfl
  | queryAdjoint l he => rfl
  | seq hp hq he ihp ihq => simp only [MultiOracleCircuit.Program.cost_seq, ihp, ihq]

/-- The total number of oracle calls is unchanged. -/
theorem count_eq {p q : MultiOracleCircuit.Program O} {e : ℝ} (h : GateApprox p q e) :
    q.count = p.count := by
  have hq := MultiOracleCircuit.Program.cost_const q 1
  have hp := MultiOracleCircuit.Program.cost_const p 1
  rw [mul_one] at hq hp
  rw [← hq, ← hp, h.cost_eq]

/-- **Reversal**: the reversed programs (inverse calls exchanged with forward calls) are
approximations with the same error. -/
theorem adjoint {p q : MultiOracleCircuit.Program O} {e : ℝ} (h : GateApprox p q e) :
    GateApprox p.adjoint q.adjoint e := by
  induction h with
  | fixed hU hq he =>
    refine .fixed hU.adjoint (by rw [MultiOracleCircuit.Program.count_adjoint, hq]) (fun x => ?_)
    rw [MultiOracleCircuit.Program.eval_adjoint, ← star_sub, norm_star]
    exact he x
  | query l he => exact .queryAdjoint l he
  | queryAdjoint l he => exact .query l he
  | seq hp hq he ihp ihq => exact .seq ihq ihp (by linarith)

/-- **Telescoping**: with unitary oracles, a known-gate approximation within `e` changes the
program unitary by at most `e` in operator norm, for every input. -/
theorem eval_sub_le (hO : ∀ l x, IsUnitary (O l x)) {p q : MultiOracleCircuit.Program O}
    {e : ℝ} (h : GateApprox p q e) (x : X) : ‖q.eval x - p.eval x‖ ≤ e := by
  induction h with
  | fixed hU hq he => exact he x
  | query l he => rw [sub_self, norm_zero]; exact he
  | queryAdjoint l he => rw [sub_self, norm_zero]; exact he
  | @seq p p' q q' e₁ e₂ e hp hq he ihp ihq =>
    rw [MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_seq]
    refine (product_error_le _ _ _ _ ((q'.eval_unitary hO x).norm_le_one)
      ((p.eval_unitary hO x).norm_le_one)).trans ?_
    linarith

/-- The vector form of `eval_sub_le`. -/
theorem eval_apply_sub_le (hO : ∀ l x, IsUnitary (O l x)) {p q : MultiOracleCircuit.Program O}
    {e : ℝ} (h : GateApprox p q e) (x : X) (v : K) :
    ‖q.eval x v - p.eval x v‖ ≤ e * ‖v‖ := by
  rw [← sub_apply]
  exact ((q.eval x - p.eval x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (h.eval_sub_le hO x) (norm_nonneg v))

/-- The error bound of an approximation is nonnegative when there is an input. -/
theorem nonneg {p q : MultiOracleCircuit.Program O} {e : ℝ} (h : GateApprox p q e) (x : X) :
    0 ≤ e := by
  induction h with
  | fixed hU hq he => exact (norm_nonneg _).trans (he x)
  | query l he => exact he
  | queryAdjoint l he => exact he
  | seq hp hq he ihp ihq => linarith

end GateApprox

/-! ### Compiled programs -/

section Compile

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable {M : Type*}

/-- **Compiled programs**: if every logical instruction is implemented by an approximation
within `ρ` of its exact implementation, the compiled program is an approximation of the
exactly compiled program within (number of logical queries) `· ρ`. The fixed gates of the
logical program are lifted identically on both sides. -/
theorem GateApprox.compile {F : M → X → K →L[ℂ] K} {O : L → X → P →L[ℂ] P}
    (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (c c' : L → MultiOracleCircuit.Program F) {ρ : ℝ}
    (hc : ∀ l, GateApprox (c l) (c' l) ρ) (p : MultiOracleCircuit.Program O) :
    GateApprox (EncodedLabeledProgram.compile E hE c p) (EncodedLabeledProgram.compile E hE c' p)
      (p.count * ρ) := by
  induction p with
  | fixed U hU =>
    rw [MultiOracleCircuit.Program.count_fixed, Nat.cast_zero, zero_mul]
    exact GateApprox.refl _
  | query l =>
    rw [MultiOracleCircuit.Program.count_query, Nat.cast_one, one_mul]
    exact hc l
  | queryAdjoint l =>
    rw [MultiOracleCircuit.Program.count_queryAdjoint, Nat.cast_one, one_mul]
    exact (hc l).adjoint
  | seq p q hp hq =>
    refine GateApprox.seq hp hq (le_of_eq ?_)
    rw [MultiOracleCircuit.Program.count_seq, Nat.cast_add, add_mul]

end Compile

end

end ChebyshevLinearSystemFinite
