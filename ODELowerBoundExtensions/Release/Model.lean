import SparseLowerBounds.ODE.Theorem
import AdaptiveHamiltonianLowerBound.Readout

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Release-style retry protocols as solvers of the dissipative ODE class

Manuscript: Section `odel:sec:main` (the output model of Theorem `odel:thm:combined`): "A solver
must herald success with probability at least `2/3` on every input. Its conditional output density
operator must be within trace distance `ε` of the normalised solution. [...] the lower bounds apply
to the upper bounds of the preceding section." References to the manuscript use its labels.

The released ODE solvers (`TimeDependentExtensions.ODE.solver`, `ODECompleteTrial.algorithm`)
are not single programs but bounded retry protocols `SparseHamiltonian.ODERepeatProtocol.Protocol`
(`fourTrials`): each attempt draws a uniformly random circuit label, freshly prepares a fixed
unit seed, runs the chosen circuit and measures the clean-output herald; the first success is
decoded, failures are discarded, at most finitely many attempts are made. The solver class of
`SparseLowerBounds.ODE.Solver` (one program with a herald projection) does not contain them.

This module widens the class to exactly these protocols, with the released semantics:

* `RetrySolver F O E G ε`: a protocol `prot : Protocol O E` over any labelled oracle family `O` on
  the inputs of the family `F`, an isometric readout `E → ℂ^N ⊗ G` of the decoded output, success
  mass `prot.successMass x ≥ 2/3` on every input and, for every solution, conditional output
  `prot.conditionalDensity x` within trace distance `ε` of `x(T)/‖x(T)‖` in the observable form
  `AdaptiveHamiltonianLowerBound.DensityAccurate` (Section `odel:sec:main`). The ODE model's own
  access is `O = F.access ι`; the release's physical oracle is another choice (`Release/Bridge`).
* `RetryForces F ε b`: every retry solver over the sampled-time access `F.access ι` (any branch
  register `ι`, output space `E`, garbage `G`) makes at least `b` value queries and `b` queries
  in total, in the worst case over all transcripts (`Protocol.worstCost`, every attempt and every
  failure branch counted).
* `RetryWitnesses F τ ḡ ε b`: the family is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and
  retry-forces `b`; the analogue of `SparseLowerBounds.ODE.Family.Witnesses`.
* Cost monotonicity of protocols (`maxCost_mono`, `worstCost_mono`, `worstCost_mul`).

`Release/Embed` shows that every `Solver` is a one-attempt, one-choice retry solver with the same
counts, so `RetryForces` implies `Forces` and the retry theorems contain the released ones.

**Scope** (`Release/*`).

* The class is the release's retry protocols only. Full adaptive trees and purified protocols
  are not in it for the joint family (a formalization choice, see the statement guide); the
  `g = 1` families get tree bounds also, since their retry bounds come from the adaptive
  Hamiltonian lower bound (`Release/Herald`).
* On the release's physical oracle, the lower bounds and the bracket assume public source
  interfaces (`PublicSources`: unitary and input-independent, Section `odel:sec:main`). The released
  solver itself accepts any unitary `J₀`, `J_b`, possibly input-dependent.
* `ℓ = log(C ḡ/ε)` with `C = 40000`, the released solver's instance of the paper's unspecified
  absolute constant `C > 1` (`Release/Instances`).
* Only the general-mesh solver of `ode:thm:time` is connected; the constant-coefficient released
  solver `SparseHamiltonian.ODECompleteEndpoint.solver` (`ode:thm:main`) is not.
* Padding the three hard families to a common dimension is not formalised here; the lower half of
  the bracket is on the maximum over three runs (`Release/Theta`).
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace

/-- Operators on the system space `ℂ^N` (source and initial-state preparations). -/
abbrev SysOp (N : Type*) [Fintype N] : Type _ := EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N

/-- **A retry-protocol solver for the family `F` at accuracy `ε`** (Section `odel:sec:main`), over a
labelled oracle family `O` on the inputs of `F`: the release's bounded fresh-trial protocol
`prot` (`ODERepeatProtocol.Protocol`: uniformly random circuit label per attempt, fresh unit
seed, clean-output herald, first success decoded, finitely many attempts), an isometric readout
of the decoded output onto system `ℂ^N` ⊗ garbage `G`, success mass at least `2/3` on every
input and, for every solution, conditional output `ε`-close to `x(T)/‖x(T)‖` in trace distance
(observable form, `DensityAccurate`). -/
structure RetrySolver {X N Z : Type*} [Fintype N] [DecidableEq N] {K s : ℕ}
    (F : Family X N Z K s) {L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (O : L → X → W →L[ℂ] W) (E G : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (ε : ℝ) where
  /-- The retry protocol. -/
  prot : ODERepeatProtocol.Protocol O E
  /-- The readout of the decoded output onto system ⊗ garbage. -/
  readout : E →L[ℂ] SysGarb N G
  readout_isometry : readout† ∘L readout = 1
  /-- Success probability at least `2/3` on every input. -/
  success : ∀ x, 2 / 3 ≤ prot.successMass x
  /-- Conditional trace distance at most `ε` from the normalised solution. -/
  accurate : ∀ x sol, F.Solves x sol →
    DensityAccurate readout (prot.conditionalDensity x)
      (ODEStateNormalization.unitDirection (sol F.T)) ε

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- **`F` forces `b` queries on retry protocols at accuracy `ε`**: every retry solver over the
sampled-time access `F.access ι` (any branch register `ι`, output space `E`, garbage `G`) makes
at least `b` value queries and at least `b` queries in total, in the worst case over all
transcripts (`Protocol.worstCost`; inverse calls counted). -/
def RetryForces (F : Family X N Z K s) (ε b : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (A : RetrySolver F (F.access ι) E G ε),
    b ≤ A.prot.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight ∧
      b ≤ A.prot.worstCost (fun _ => 1)

/-- **`F` witnesses the bound `b` on retry protocols** for the parameters `(τ, ḡ, ε)`: `F` is in
the class with `η = 1`, `T = τ` and `g ≤ ḡ`, and retry-forces `b` at accuracy `ε`. -/
structure RetryWitnesses (F : Family X N Z K s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : RetryForces F ε b

/-- A retry witness of `b` witnesses every smaller bound. -/
theorem RetryWitnesses.mono {F : Family X N Z K s} {τ gbar ε b b' : ℝ}
    (hW : RetryWitnesses F τ gbar ε b) (hb : b' ≤ b) : RetryWitnesses F τ gbar ε b' :=
  ⟨hW.inClass, hW.time_eq, fun ι _ E G _ _ _ _ _ _ _ A =>
    ⟨hb.trans (hW.forces ι E G A).1, hb.trans (hW.forces ι E G A).2⟩⟩

/-! ### Worst-case costs of protocols -/

section Cost

variable {E W XX L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {O : L → XX → W →L[ℂ] W}

/-- The per-trial maximum is monotone in the label weights. -/
theorem maxCost_mono (t : ODERepeatProtocol.TrialFamily O E) {w v : L → ℕ}
    (h : ∀ l, w l ≤ v l) : t.maxCost w ≤ t.maxCost v := by
  exact Finset.sup_mono_fun fun j _ => (t.circuit j).cost_mono h

/-- The worst-case cost of a protocol is monotone in the label weights. -/
theorem worstCost_mono (p : ODERepeatProtocol.Protocol O E) {w v : L → ℕ}
    (h : ∀ l, w l ≤ v l) : p.worstCost w ≤ p.worstCost v := by
  induction p with
  | abort => exact le_rfl
  | freshTrial t k ih =>
      exact Nat.add_le_add (maxCost_mono t h) ih

omit [CompleteSpace E] in
/-- Scaling the label weights by `c` scales the weighted cost of a program by `c`. -/
theorem program_cost_mul (p : MultiOracleCircuit.Program O) (c : ℕ) (w : L → ℕ) :
    p.cost (fun l => c * w l) = c * p.cost w := by
  induction p with
  | fixed U hU => simp
  | query l => simp
  | queryAdjoint l => simp
  | seq p q hp hq => simp only [MultiOracleCircuit.Program.cost_seq, hp, hq, Nat.mul_add]

/-- Scaling the label weights by `c` scales the per-trial maximum by `c`. -/
theorem maxCost_mul (t : ODERepeatProtocol.TrialFamily O E) (c : ℕ) (w : L → ℕ) :
    t.maxCost (fun l => c * w l) = c * t.maxCost w := by
  refine le_antisymm (Finset.sup_le fun j _ => ?_) ?_
  · rw [program_cost_mul]
    exact Nat.mul_le_mul_left c (t.cost_le_maxCost w j)
  · have hne : (Finset.univ : Finset (Fin t.choices)).Nonempty :=
      Finset.univ_nonempty_iff.mpr ⟨⟨0, t.choices_pos⟩⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup _ hne
      (fun i : Fin t.choices => (t.circuit i).cost w)
    have hj' : t.maxCost w = (t.circuit j).cost w := hj
    rw [hj', ← program_cost_mul]
    exact t.cost_le_maxCost _ j

/-- Scaling the label weights by `c` scales the worst-case cost by `c`. -/
theorem worstCost_mul (p : ODERepeatProtocol.Protocol O E) (c : ℕ) (w : L → ℕ) :
    p.worstCost (fun l => c * w l) = c * p.worstCost w := by
  induction p with
  | abort => simp [ODERepeatProtocol.Protocol.worstCost]
  | freshTrial t k ih =>
      simp only [ODERepeatProtocol.Protocol.worstCost, maxCost_mul, ih, Nat.mul_add]

end Cost

end

end ODELowerBoundExtensions.Release
