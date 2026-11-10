import DeferredMeasurementLowerBounds.Model.Embed

set_option autoImplicit false

/-!
# Compiling the calls of a measured algorithm into programs over another family

The manuscript covers randomised and adaptive algorithms by purification and deferred measurement
(proof of Lemma `hsl:lem:precision`, the end of the proof of Lemma `hsl:lem:precision`). For an
oracle family whose calls are not themselves native calls, a measured algorithm is first rewritten
call by call: if every label `l` of a family `O` is computed exactly, on the same workspace, by a
program `P l` over a family `B` (`(P l).eval x = O l x`), then replacing every forward call of `l`
by the chain of `P l`, every inverse call by the chain of the adjoint program, and keeping every
instrument, output and rejection gives a measured algorithm over `B` (`compile`) with the same
heralded output and success mass on every input and initial vector (`successDensity_compile`,
`successMass_compile`, `conditionalDensity_compile`), whose worst-case weighted cost is that of the
original with the weight of `l` replaced by the cost of `P l` (`worstCost_compile`); with programs
of cost at most `c` it is at most `c` times the worst-case number of calls (`worstCost_compile_le`).

`callProgram P l b` is the substitution (`MultiOracleCircuit.Program.substitute`) of the one-call
program of `l` by the programs `P`, and `compile` is its counterpart for measured algorithms.
Compilation happens before deferral: the compiled algorithm is again a measured algorithm, now
over admissible labels, to which `DeferredMeasurementLowerBounds.Corollaries.main_max_measured`
applies directly. This is the reverse order of
`DeferredMeasurementLowerBounds.Access.compiledProgram` (deferral, then compilation of
the record-selected calls), and it needs no program or tree form over the compiled family.
-/

namespace TimeDependentLowerBoundExtensions.Measured

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct

variable {K E X L L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {O : L → X → K →L[ℂ] K} {B : L' → X → K →L[ℂ] K}

/-- The program of one call of `l`: the substitution `MultiOracleCircuit.Program.substitute` of
the one-call program of `l` (forward or inverse) by the programs `P`, that is `P l` for a forward
call and its adjoint program for an inverse call. -/
def callProgram (P : L → MultiOracleCircuit.Program B) (l : L) (inverse : Bool) :
    MultiOracleCircuit.Program B :=
  MultiOracleCircuit.Program.substitute
    (if inverse then
      (.queryAdjoint l : MultiOracleCircuit.Program fun l x => (P l).eval x) else .query l) P

/-- The program of a call evaluates to the call when `P l` computes `O l`. -/
theorem eval_callProgram (P : L → MultiOracleCircuit.Program B)
    (hP : ∀ l x, (P l).eval x = O l x) (l : L) (inverse : Bool) (x : X) :
    (callProgram P l inverse).eval x = queryOp O l inverse x := by
  cases inverse
  · simp [callProgram, MultiOracleCircuit.Program.substitute, queryOp, hP]
  · simp [callProgram, MultiOracleCircuit.Program.substitute, queryOp, hP]

/-- The program of a call costs as much as `P l`, in either direction. -/
theorem cost_callProgram (P : L → MultiOracleCircuit.Program B) (l : L) (inverse : Bool)
    (w : L' → ℕ) : (callProgram P l inverse).cost w = (P l).cost w := by
  cases inverse
  · simp [callProgram, MultiOracleCircuit.Program.substitute]
  · simp [callProgram, MultiOracleCircuit.Program.substitute]

/-- **Call-by-call compilation of a measured algorithm**: every call of `l` (forward or inverse)
becomes the chain of `callProgram P l inverse` (known unitaries as one-outcome instruments, calls
of `B`); instruments, outputs and rejections are kept. -/
def compile (P : L → MultiOracleCircuit.Program B) : Measured O E → Measured B E
  | .output out h => .output out h
  | .reject => .reject
  | .call l b next => ofProgram (callProgram P l b) (compile P next)
  | .instrument n A hA next => .instrument n A hA (fun j => compile P (next j))

/-- **The compiled algorithm has the same heralded output** on every input and initial vector. -/
theorem successDensity_compile (P : L → MultiOracleCircuit.Program B)
    (hP : ∀ l x, (P l).eval x = O l x) (M : Measured O E) (x : X) (φ : K) :
    (compile P M).successDensity x φ = M.successDensity x φ := by
  induction M generalizing φ with
  | output out _ => rfl
  | reject => rfl
  | call l b next ih =>
    rw [compile, successDensity_ofProgram, eval_callProgram P hP, ih]
    rfl
  | instrument n A hA next ih =>
    simp only [compile, Measured.successDensity]
    exact Finset.sum_congr rfl fun j _ => ih j _

/-- **The compiled algorithm has the same success mass** on every input and initial vector. -/
theorem successMass_compile (P : L → MultiOracleCircuit.Program B)
    (hP : ∀ l x, (P l).eval x = O l x) (M : Measured O E) (x : X) (φ : K) :
    (compile P M).successMass x φ = M.successMass x φ := by
  induction M generalizing φ with
  | output out _ => rfl
  | reject => rfl
  | call l b next ih =>
    rw [compile, successMass_ofProgram, eval_callProgram P hP, ih]
    rfl
  | instrument n A hA next ih =>
    simp only [compile, Measured.successMass]
    exact Finset.sum_congr rfl fun j _ => ih j _

/-- **The compiled algorithm has the same conditional output.** -/
theorem conditionalDensity_compile (P : L → MultiOracleCircuit.Program B)
    (hP : ∀ l x, (P l).eval x = O l x) (M : Measured O E) (x : X) (φ : K) :
    (compile P M).conditionalDensity x φ = M.conditionalDensity x φ := by
  simp only [Measured.conditionalDensity, successDensity_compile P hP,
    successMass_compile P hP]

/-- The worst-case cost of the compiled algorithm: the weight of `l` becomes the cost of
`P l`. -/
theorem worstCost_compile (P : L → MultiOracleCircuit.Program B) (M : Measured O E)
    (w : L' → ℕ) : (compile P M).worstCost w = M.worstCost (fun l => (P l).cost w) := by
  induction M with
  | output out _ => rfl
  | reject => rfl
  | call l b next ih =>
    rw [compile, worstCost_ofProgram, cost_callProgram, ih]
    rfl
  | instrument n A hA next ih =>
    simp only [compile, Measured.worstCost, ih]

/-- A constant weight `c` costs at most `c` times the worst-case number of calls (a fact about
measured algorithms over any labels; equality also holds, only the inequality is used). -/
theorem worstCost_const_le (M : Measured O E) (c : ℕ) :
    M.worstCost (fun _ => c) ≤ c * M.worstCost (fun _ => 1) := by
  induction M with
  | output out _ => simp [Measured.worstCost]
  | reject => simp [Measured.worstCost]
  | call l b next ih =>
    simp only [Measured.worstCost]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  | instrument n A hA next ih =>
    simp only [Measured.worstCost]
    exact Finset.sup_le fun j _ => (ih j).trans (Nat.mul_le_mul_left c
      (Finset.le_sup (f := fun j => Measured.worstCost (next j) (fun _ => 1))
        (Finset.mem_univ j)))

/-- **Programs of cost at most `c` per call**: the compiled algorithm costs at most `c` times
the worst-case number of calls of the original. -/
theorem worstCost_compile_le (P : L → MultiOracleCircuit.Program B) (M : Measured O E)
    (w : L' → ℕ) {c : ℕ} (hc : ∀ l, (P l).cost w ≤ c) :
    (compile P M).worstCost w ≤ c * M.worstCost (fun _ => 1) := by
  rw [worstCost_compile]
  exact (Measured.worstCost_mono M hc).trans (worstCost_const_le M c)

end

end TimeDependentLowerBoundExtensions.Measured
