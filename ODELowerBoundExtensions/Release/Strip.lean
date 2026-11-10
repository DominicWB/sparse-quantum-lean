import SparseODE.ODECompleteSuccess
import SparseLowerBounds.Hamiltonian.Accuracy
import AdaptiveHamiltonianLowerBound.Readout

set_option autoImplicit false

/-!
# Released protocols without an idle source vocabulary (`odel:thm:combined`, `odel:lem:dyson`)

The released complete certificate `ODECompleteTrial.Certificate` is stated for programs whose
labels are `L ⊕ Bool` (matrix calls and the two source interfaces, counted separately). Over the
ODE lower-bound access the source vocabulary of the Dyson solver is idle: the oracle family is
`ODESourceQueryBudget.oracle O (fun _ _ => 1)`, whose source calls are identities. The lower-bound
class of retry protocols (`ODELowerBoundExtensions.Release.RetrySolver`) runs over `O` itself.
This module removes the idle vocabulary and reads the released output through a clean readout.

* `stripIdle`: the release's syntactic substitution (`MultiOracleCircuit.Program.substitute`)
  `inl l ↦ query l`, `inr b ↦ identity`; same evaluation (`stripIdle_eval`), cost the matrix cost
  (`stripIdle_cost`).
* `mapTrial`, `mapProtocol`: run every circuit of a released trial family
  (`ODERepeatProtocol.TrialFamily`) or bounded retry protocol (`ODERepeatProtocol.Protocol`)
  through a program map, with the same seed and output. An evaluation-preserving map preserves the
  success mass and the conditional output density (`mapProtocol_successMass`,
  `mapProtocol_conditionalDensity`); a cost-transferring map transfers the worst-case cost
  (`mapProtocol_worstCost`).
* `certificate_densityAccurate`: the released conditional trace distance `≤ ε` gives the
  observable form `AdaptiveHamiltonianLowerBound.DensityAccurate` of the lower-bound class, read by
  the clean readout `SparseLowerBounds.Hamiltonian.endpointReadout 1 i₀` (any `i₀`), for every
  oracle family (`LinearSystemLowerBound.abs_corr_sub_le`).

These lemmas are generic infrastructure of the retry class of this namespace (eqs. `odel:eq:upper`
and `odel:eq:refined` for the released solver, eq. `odel:eq:fixed` for the Dyson solver).
`ReleaseProtocol.accurate` (`Release/Instances`, the released
solver over `releaseOracle`) is the instance of `certificate_densityAccurate`; the Dyson solver
(`Dyson/Family/Retry`) uses `stripIdle`, `mapProtocol` and `certificate_densityAccurate`.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section

open SparseHamiltonian OracleCircuit ContinuousLinearMap
open scoped InnerProduct

section Strip

variable {X L K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- **Remove the idle source vocabulary**: matrix calls are kept, idle source calls become the
identity gate (`MultiOracleCircuit.Program.substitute`). -/
def stripIdle (p : MultiOracleCircuit.Program (ODESourceQueryBudget.oracle O (fun _ _ => 1))) :
    MultiOracleCircuit.Program O :=
  p.substitute (Sum.elim (fun l => (.query l : MultiOracleCircuit.Program O))
    (fun _ => MultiOracleCircuit.Program.identity))

/-- Removing the idle vocabulary does not change the evaluation. -/
theorem stripIdle_eval
    (p : MultiOracleCircuit.Program (ODESourceQueryBudget.oracle O (fun _ _ => 1))) (x : X) :
    (stripIdle p).eval x = p.eval x := by
  refine MultiOracleCircuit.Program.eval_substitute p _ ?_ x
  intro l y
  cases l with
  | inl l => rfl
  | inr b => rfl

/-- After removing the idle vocabulary, every weighted cost is the matrix cost. -/
theorem stripIdle_cost
    (p : MultiOracleCircuit.Program (ODESourceQueryBudget.oracle O (fun _ _ => 1)))
    (w : L → ℕ) : (stripIdle p).cost w = p.cost (ODESourceQueryBudget.matrixWeight w) := by
  rw [stripIdle, MultiOracleCircuit.Program.cost_substitute]
  congr 1
  funext l
  cases l with
  | inl l => rfl
  | inr b => rfl

end Strip

section Map

variable {X L L' K E : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {O : L → X → K →L[ℂ] K} {O' : L' → X → K →L[ℂ] K}

/-- **A released trial family along a program map**: the same labels, seed and output, every
circuit mapped by `f`. -/
def mapTrial (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (t : ODERepeatProtocol.TrialFamily O E) : ODERepeatProtocol.TrialFamily O' E where
  choices := t.choices
  choices_pos := t.choices_pos
  circuit j := f (t.circuit j)
  seed := t.seed
  seed_unit := t.seed_unit
  output := t.output
  output_isometry := t.output_isometry

/-- **A released retry protocol along a program map**: every fresh trial mapped by `mapTrial`. -/
def mapProtocol (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O') :
    ODERepeatProtocol.Protocol O E → ODERepeatProtocol.Protocol O' E
  | .abort => .abort
  | .freshTrial t k => .freshTrial (mapTrial f t) (mapProtocol f k)

/-- An evaluation-preserving program map preserves every decoded trial amplitude. -/
theorem mapTrial_amplitude (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = p.eval x) (t : ODERepeatProtocol.TrialFamily O E) (x : X)
    (j : Fin t.choices) : (mapTrial f t).amplitude x j = t.amplitude x j := by
  change (t.output†) ((f (t.circuit j)).eval x t.seed) = (t.output†) ((t.circuit j).eval x t.seed)
  rw [hf]

/-- An evaluation-preserving program map preserves the mean trial success. -/
theorem mapTrial_meanSuccess (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = p.eval x) (t : ODERepeatProtocol.TrialFamily O E) (x : X) :
    (mapTrial f t).meanSuccess x = t.meanSuccess x := by
  change (∑ j : Fin t.choices, ‖(mapTrial f t).amplitude x j‖ ^ 2) / (t.choices : ℝ) =
    (∑ j : Fin t.choices, ‖t.amplitude x j‖ ^ 2) / (t.choices : ℝ)
  simp only [mapTrial_amplitude f hf]

/-- An evaluation-preserving program map preserves the one-trial successful density. -/
theorem mapTrial_oneTrialDensity
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = p.eval x) (t : ODERepeatProtocol.TrialFamily O E) (x : X) :
    (mapTrial f t).oneTrialDensity x = t.oneTrialDensity x := by
  change ODEMixedOutput.ensemble
      (fun j : Fin t.choices => ‖(mapTrial f t).amplitude x j‖ ^ 2 / (t.choices : ℝ))
      (fun j => ODEStateNormalization.unitDirection ((mapTrial f t).amplitude x j)) =
    ODEMixedOutput.ensemble (fun j : Fin t.choices => ‖t.amplitude x j‖ ^ 2 / (t.choices : ℝ))
      (fun j => ODEStateNormalization.unitDirection (t.amplitude x j))
  simp only [mapTrial_amplitude f hf]

/-- A cost-transferring program map transfers the per-trial maximum cost. -/
theorem mapTrial_maxCost (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (w' : L' → ℕ) (w : L → ℕ) (hf : ∀ p, (f p).cost w' = p.cost w)
    (t : ODERepeatProtocol.TrialFamily O E) : (mapTrial f t).maxCost w' = t.maxCost w := by
  change (Finset.univ.sup fun j : Fin t.choices => (f (t.circuit j)).cost w') =
    Finset.univ.sup fun j : Fin t.choices => (t.circuit j).cost w
  simp only [hf]

/-- An evaluation-preserving program map preserves the failure mass. -/
theorem mapProtocol_failureMass
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = p.eval x) (p : ODERepeatProtocol.Protocol O E) (x : X) :
    (mapProtocol f p).failureMass x = p.failureMass x := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
      change (1 - (mapTrial f t).meanSuccess x) * (mapProtocol f k).failureMass x =
        (1 - t.meanSuccess x) * k.failureMass x
      rw [mapTrial_meanSuccess f hf, ih]

/-- An evaluation-preserving program map preserves the unconditioned successful density. -/
theorem mapProtocol_successDensity
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = p.eval x) (p : ODERepeatProtocol.Protocol O E) (x : X) :
    (mapProtocol f p).successDensity x = p.successDensity x := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
      change (mapTrial f t).oneTrialDensity x +
          ((1 - (mapTrial f t).meanSuccess x : ℝ) : ℂ) • (mapProtocol f k).successDensity x =
        t.oneTrialDensity x + ((1 - t.meanSuccess x : ℝ) : ℂ) • k.successDensity x
      rw [mapTrial_oneTrialDensity f hf, mapTrial_meanSuccess f hf, ih]

/-- An evaluation-preserving program map preserves the success mass. -/
theorem mapProtocol_successMass
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = p.eval x) (p : ODERepeatProtocol.Protocol O E) (x : X) :
    (mapProtocol f p).successMass x = p.successMass x := by
  change 1 - (mapProtocol f p).failureMass x = 1 - p.failureMass x
  rw [mapProtocol_failureMass f hf]

/-- An evaluation-preserving program map preserves the conditional output density. -/
theorem mapProtocol_conditionalDensity
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O')
    (hf : ∀ p x, (f p).eval x = p.eval x) (p : ODERepeatProtocol.Protocol O E) (x : X) :
    (mapProtocol f p).conditionalDensity x = p.conditionalDensity x := by
  unfold ODERepeatProtocol.Protocol.conditionalDensity
  rw [mapProtocol_successMass f hf, mapProtocol_successDensity f hf]

/-- A program map with `cost w' ∘ f = cost w` transfers the worst-case cost. -/
theorem mapProtocol_worstCost
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O') (w' : L' → ℕ)
    (w : L → ℕ) (hf : ∀ p, (f p).cost w' = p.cost w) (p : ODERepeatProtocol.Protocol O E) :
    (mapProtocol f p).worstCost w' = p.worstCost w := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
      change (mapTrial f t).maxCost w' + (mapProtocol f k).worstCost w' =
        t.maxCost w + k.worstCost w
      rw [mapTrial_maxCost f w' w hf, ih]

end Map

/-- **The released accuracy in the observable form of the lower-bound class**: a released
complete certificate (conditional trace distance at most `ε` from `target/‖target‖`) makes the
conditional output of its four-attempt algorithm `ε`-accurate in the sense of
`AdaptiveHamiltonianLowerBound.DensityAccurate`, read by the clean readout `endpointReadout 1 i₀`
(any `i₀`), for every oracle family. `ReleaseProtocol.accurate` is its instance on
`releaseOracle`. -/
theorem certificate_densityAccurate {N R X L : Type*} [Fintype N] [DecidableEq N]
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {O : (L ⊕ Bool) → X → R →L[ℂ] R} {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R}
    {F : EuclideanSpace ℂ N →L[ℂ] R} {x : X} {target : EuclideanSpace ℂ N}
    {s Θ ell g ε : ℝ} (h : ODECompleteTrial.Certificate q M ψ F x target s Θ ell g ε)
    (i₀ : N) :
    AdaptiveHamiltonianLowerBound.DensityAccurate
      (SparseLowerBounds.Hamiltonian.endpointReadout
        (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) i₀)
      ((ODECompleteTrial.algorithm h.trial).conditionalDensity x)
      (ODEStateNormalization.unitDirection target) ε := by
  obtain ⟨hsym, hdist⟩ := h.conditional_error
  intro A _ hA
  have h1 : (SparseLowerBounds.Hamiltonian.endpointReadout
      (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) i₀)† ∘L
      SparseLowerBounds.Hamiltonian.endpointReadout
        (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) i₀ = 1 :=
    SparseLowerBounds.Hamiltonian.endpointReadout_isometry 1 (by ext; simp) i₀
  have hO : ∀ v, ‖SparseLowerBounds.Readout.outObs (SparseLowerBounds.Hamiltonian.endpointReadout
      (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) i₀) A v‖ ≤ ‖v‖ := by
    intro v
    have hn := (SparseLowerBounds.Readout.norm_outObs_le _ h1 A).trans hA
    calc _ ≤ ‖SparseLowerBounds.Readout.outObs (SparseLowerBounds.Hamiltonian.endpointReadout
          (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) i₀) A‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hc := LinearSystemLowerBound.abs_corr_sub_le _ hO _ _ hsym
  rw [LinearSystemLowerBound.corr_pure] at hc
  have hi := SparseLowerBounds.Hamiltonian.inner_outObs_endpointReadout
    (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (by ext; simp) i₀ A
    (ODEStateNormalization.unitDirection target)
  simp only [one_apply_eq_self] at hi
  rw [hi] at hc
  linarith

end

end ODELowerBoundExtensions.Release
