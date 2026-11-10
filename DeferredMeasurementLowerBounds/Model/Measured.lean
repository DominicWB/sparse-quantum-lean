import SparseODE.ODECompleteSuccess

set_option autoImplicit false

/-!
# Measured query algorithms

Manuscript: the end of the proof of Lemma `hsl:lem:precision` ("Purification and deferred
measurement include adaptive and randomised algorithms"), Section `odel:sec:main` (the solver class
of Section `odel:sec:main`: a success flag of probability at least `2/3`, a conditional output, a
worst-case query bound) and the proof of Lemma `qlsl:lem:xor` ("controlled queries and adaptive
algorithms after coherent purification and padding to their worst-case query count").

A **measured algorithm** `Measured O E` acts on one persistent workspace `K` (any complex
Hilbert space) with a labelled oracle family `O : L → X → K →L[ℂ] K`. It is a finite tree of

* `call l inverse next`: one call of the oracle label `l`, forward or inverse;
* `instrument n A next`: an input-independent quantum instrument with finitely many outcomes,
  given by Kraus operators `A j` with `∑ j, A j† A j = 1`, followed by the classically chosen
  continuation `next j` of the observed outcome `j`;
* `output out`: the final herald and output, an isometry `out : E → K`; the success sector is the
  range of `out` and the decoded output is `out† ψ`;
* `reject`: halting without output.

Instruments cover multi-outcome projective measurements in the middle of a run, generalised
measurements with post-measurement states, classical randomness (`A j = n^{-1/2} 1`), known
unitaries (one outcome), resets of a finite-dimensional workspace (`Model.reset`; a reset of an
infinite-dimensional workspace to a fixed vector is not an instrument with finitely many
outcomes), resets of a finite-dimensional register of it (an instrument with Kraus operators
`|ψ⟩⟨b_i| ⊗ 1`) and every classically controlled known operation
(the continuation depends on all earlier outcomes). The workspace can hold any registers: the
model has no fixed register layout.

Semantics on an initial vector `φ` (pure branches, outcomes kept classical): the unnormalised
heralded output `successDensity` is the sum over all transcripts of `|out† ψ⟩⟨out† ψ|`, where `ψ`
is the unnormalised branch vector; `successMass` is the sum of `‖out† ψ‖²`; the conditional
output is `conditionalDensity`. The cost `worstCost w` is the maximum over all transcripts of the
weighted number of calls; inverse calls count as forward calls.
-/

namespace DeferredMeasurementLowerBounds.Model

noncomputable section
open SparseHamiltonian ContinuousLinearMap
open scoped InnerProduct

variable {K E X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- One oracle call: label `l`, forward (`inverse = false`) or inverse (`inverse = true`). -/
def queryOp (O : L → X → K →L[ℂ] K) (l : L) (inverse : Bool) (x : X) : K →L[ℂ] K :=
  if inverse then star (O l x) else O l x

/-- Calls of unitary labels are unitary. -/
theorem queryOp_unitary {O : L → X → K →L[ℂ] K} (hO : ∀ l x, OracleCircuit.IsUnitary (O l x))
    (l : L) (inverse : Bool) (x : X) : OracleCircuit.IsUnitary (queryOp O l inverse x) := by
  cases inverse
  · simpa [queryOp] using hO l x
  · simpa [queryOp] using (hO l x).adjoint

/-- **Measured algorithms**: oracle calls, input-independent finite instruments with classical
continuations, heralded output and rejection, on one persistent workspace. -/
inductive Measured (O : L → X → K →L[ℂ] K) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  /-- Herald the range of the isometry `out` and output `out† ψ`. -/
  | output (out : E →L[ℂ] K) (isometry : out† ∘L out = 1)
  /-- Halt without output. -/
  | reject
  /-- One call of the label `l`, forward or inverse, then continue. -/
  | call (l : L) (inverse : Bool) (next : Measured O E)
  /-- A known instrument with Kraus operators `kraus`, then the continuation of the outcome. -/
  | instrument (n : ℕ) (kraus : Fin n → K →L[ℂ] K)
      (complete : ∑ j, (kraus j)† ∘L kraus j = 1) (next : Fin n → Measured O E)

namespace Measured

variable {O : L → X → K →L[ℂ] K}

/-- Unnormalised heralded output: the sum over transcripts of the decoded branch projectors. -/
def successDensity : Measured O E → X → K → E →L[ℂ] E
  | .output out _, _, φ => ODEMixedOutput.pureOperator ((out†) φ)
  | .reject, _, _ => 0
  | .call l b next, x, φ => successDensity next x (queryOp O l b x φ)
  | .instrument _ A _ next, x, φ => ∑ j, successDensity (next j) x (A j φ)

/-- Probability of a heralded output (Born weights of all successful transcripts). -/
def successMass : Measured O E → X → K → ℝ
  | .output out _, _, φ => ‖(out†) φ‖ ^ 2
  | .reject, _, _ => 0
  | .call l b next, x, φ => successMass next x (queryOp O l b x φ)
  | .instrument _ A _ next, x, φ => ∑ j, successMass (next j) x (A j φ)

/-- The output conditioned on the herald, transcripts discarded. -/
def conditionalDensity (M : Measured O E) (x : X) (φ : K) : E →L[ℂ] E :=
  ((M.successMass x φ)⁻¹ : ℂ) • M.successDensity x φ

/-- Maximum over all transcripts of the weighted number of calls, inverse calls included. -/
def worstCost : Measured O E → (L → ℕ) → ℕ
  | .output _ _, _ => 0
  | .reject, _ => 0
  | .call l _ next, w => w l + worstCost next w
  | .instrument _ _ _ next, w => Finset.univ.sup fun j => worstCost (next j) w

/-- Maximum number of instruments along a transcript. -/
def depth : Measured O E → ℕ
  | .output _ _ => 0
  | .reject => 0
  | .call _ _ next => depth next
  | .instrument _ _ _ next => (Finset.univ.sup fun j => depth (next j)) + 1

/-- Maximum number of outcomes of an instrument. -/
def width : Measured O E → ℕ
  | .output _ _ => 0
  | .reject => 0
  | .call _ _ next => width next
  | .instrument n _ _ next => max n (Finset.univ.sup fun j => width (next j))

/-- The success mass is nonnegative. -/
theorem successMass_nonneg (M : Measured O E) (x : X) (φ : K) : 0 ≤ M.successMass x φ := by
  induction M generalizing φ with
  | output out _ => exact sq_nonneg _
  | reject => exact le_refl _
  | call l b next ih => exact ih _
  | instrument n A _ next ih => exact Finset.sum_nonneg fun j _ => ih j _

/-- The heralded output is quadratic in the initial vector. -/
theorem successDensity_smul (M : Measured O E) (x : X) (c : ℂ) (φ : K) :
    M.successDensity x (c • φ) = ((‖c‖ ^ 2 : ℝ) : ℂ) • M.successDensity x φ := by
  induction M generalizing φ with
  | output out _ =>
    simp only [successDensity, map_smul, ODEMixedOutput.pureOperator_smul]
    push_cast; rfl
  | reject => simp [successDensity]
  | call l b next ih => simp only [successDensity, map_smul, ih]
  | instrument n A _ next ih =>
    simp only [successDensity, map_smul, ih, Finset.smul_sum]

/-- The success mass is quadratic in the initial vector. -/
theorem successMass_smul (M : Measured O E) (x : X) (c : ℂ) (φ : K) :
    M.successMass x (c • φ) = ‖c‖ ^ 2 * M.successMass x φ := by
  induction M generalizing φ with
  | output out _ => simp only [successMass, map_smul, norm_smul, mul_pow]
  | reject => simp [successMass]
  | call l b next ih => simp only [successMass, map_smul, ih]
  | instrument n A _ next ih =>
    simp only [successMass, map_smul, ih, Finset.mul_sum]

/-- The worst-case cost is monotone in the label weights. -/
theorem worstCost_mono (M : Measured O E) {w v : L → ℕ} (h : ∀ l, w l ≤ v l) :
    M.worstCost w ≤ M.worstCost v := by
  induction M with
  | output out _ => exact le_refl _
  | reject => exact le_refl _
  | call l b next ih => exact Nat.add_le_add (h l) ih
  | instrument n A _ next ih => exact Finset.sup_mono_fun fun j _ => ih j

end Measured

/-- The weight counting the calls of the labels in `counted`, each with weight one. -/
def countWeight (counted : L → Prop) [DecidablePred counted] : L → ℕ :=
  fun l => if counted l then 1 else 0

/-- If every counted label has weight at least one, the worst-case number of counted calls is at
most the worst-case weighted cost. -/
theorem worstCost_countWeight_le {O : L → X → K →L[ℂ] K} (M : Measured O E)
    (counted : L → Prop) [DecidablePred counted] {w : L → ℕ} (h : ∀ l, counted l → 1 ≤ w l) :
    M.worstCost (countWeight counted) ≤ M.worstCost w := by
  refine Measured.worstCost_mono M fun l => ?_
  unfold countWeight
  split_ifs with hl
  · exact h l hl
  · exact Nat.zero_le _

end

end DeferredMeasurementLowerBounds.Model
