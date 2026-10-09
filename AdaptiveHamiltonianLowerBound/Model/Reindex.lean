import SparseLinearSystems.Protocol.Tree

set_option autoImplicit false

/-!
# Reindexing adaptive protocols along a map of inputs

The released adaptive protocols (`SparseLinearSystems.Protocol.Tree`) are written over an
oracle family `O : L → X → K →L[ℂ] K` indexed by the unknown input `x : X`. Along a map
`f : X' → X` every program, fresh run, trial family, final protocol and tree has the same
syntax over the family `fun l x' => O l (f x')`: only the input at which the oracles are
evaluated changes (`program`, `testRun`, `trial`, `protocol`, `tree`).

The semantics transports pointwise: the reindexed tree at `x'` has the success mass,
heralded output and conditional output of the original tree at `f x'`
(`successMass_tree`, `successDensity_tree`, `conditionalDensity_tree`), and the same
worst-case cost (`worstCost_tree`). The lower bound for the precision family uses this to
read inputs `x : Fin n → Bool` as `j : Fin n → Fin 2`.
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap

namespace Reindex

variable {K F E X X' L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {O : L → X → K →L[ℂ] K} (f : X' → X)

/-! ### Programs -/

/-- A program over `O`, evaluated at the input `f x'`. -/
def program : MultiOracleCircuit.Program O → MultiOracleCircuit.Program (fun l x' => O l (f x'))
  | .fixed U hU => .fixed U hU
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (program p) (program q)

theorem eval_program (p : MultiOracleCircuit.Program O) (x' : X') :
    (program f p).eval x' = p.eval (f x') := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      simp only [program, MultiOracleCircuit.Program.eval_seq, hp, hq]

theorem cost_program (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (program f p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      simp only [program, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-! ### Fresh runs and trial families -/

/-- A fresh measured run, evaluated at `f x'`. -/
def testRun (t : TestRun O F) : TestRun (fun l x' => O l (f x')) F where
  circuit := program f t.circuit
  seed := t.seed
  seed_unit := t.seed_unit
  flag := t.flag
  flag_isometry := t.flag_isometry

theorem probability_testRun (t : TestRun O F) (x' : X') :
    (testRun f t).probability x' = t.probability (f x') := by
  simp only [TestRun.probability, testRun, eval_program]

/-- A trial family, evaluated at `f x'`. -/
def trial (t : ODERepeatProtocol.TrialFamily O E) :
    ODERepeatProtocol.TrialFamily (fun l x' => O l (f x')) E where
  choices := t.choices
  choices_pos := t.choices_pos
  circuit c := program f (t.circuit c)
  seed := t.seed
  seed_unit := t.seed_unit
  output := t.output
  output_isometry := t.output_isometry

theorem amplitude_trial (t : ODERepeatProtocol.TrialFamily O E) (x' : X')
    (c : Fin t.choices) : (trial f t).amplitude x' c = t.amplitude (f x') c := by
  simp only [ODERepeatProtocol.TrialFamily.amplitude, trial, eval_program]

theorem probability_trial (t : ODERepeatProtocol.TrialFamily O E) (x' : X')
    (c : Fin t.choices) : (trial f t).probability x' c = t.probability (f x') c := by
  simp only [ODERepeatProtocol.TrialFamily.probability, amplitude_trial]

theorem meanSuccess_trial (t : ODERepeatProtocol.TrialFamily O E) (x' : X') :
    (trial f t).meanSuccess x' = t.meanSuccess (f x') := by
  simp only [ODERepeatProtocol.TrialFamily.meanSuccess, probability_trial]
  rfl

theorem oneTrialDensity_trial (t : ODERepeatProtocol.TrialFamily O E) (x' : X') :
    (trial f t).oneTrialDensity x' = t.oneTrialDensity (f x') := by
  simp only [ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus, amplitude_trial]
  rfl

theorem maxCost_trial (t : ODERepeatProtocol.TrialFamily O E) (w : L → ℕ) :
    (trial f t).maxCost w = t.maxCost w := by
  simp only [ODERepeatProtocol.TrialFamily.maxCost, trial, cost_program]
  rfl

/-! ### Final protocols -/

/-- A final fresh-trial protocol, evaluated at `f x'`. -/
def protocol : ODERepeatProtocol.Protocol O E →
    ODERepeatProtocol.Protocol (fun l x' => O l (f x')) E
  | .abort => .abort
  | .freshTrial t k => .freshTrial (trial f t) (protocol k)

theorem failureMass_protocol (p : ODERepeatProtocol.Protocol O E) (x' : X') :
    (protocol f p).failureMass x' = p.failureMass (f x') := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
      simp only [protocol, ODERepeatProtocol.Protocol.failureMass, meanSuccess_trial, ih]

theorem successMass_protocol (p : ODERepeatProtocol.Protocol O E) (x' : X') :
    (protocol f p).successMass x' = p.successMass (f x') := by
  simp only [ODERepeatProtocol.Protocol.successMass, failureMass_protocol]

theorem successDensity_protocol (p : ODERepeatProtocol.Protocol O E) (x' : X') :
    (protocol f p).successDensity x' = p.successDensity (f x') := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
      simp only [protocol, ODERepeatProtocol.Protocol.successDensity, oneTrialDensity_trial,
        meanSuccess_trial, ih]

theorem worstCost_protocol (p : ODERepeatProtocol.Protocol O E) (w : L → ℕ) :
    (protocol f p).worstCost w = p.worstCost w := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
      simp only [protocol, ODERepeatProtocol.Protocol.worstCost, maxCost_trial, ih]

/-! ### Adaptive trees -/

/-- An adaptive protocol, evaluated at `f x'`. -/
def tree : Tree O F E → Tree (fun l x' => O l (f x')) F E
  | .final p => .final (protocol f p)
  | .test t s fl => .test (testRun f t) (tree s) (tree fl)

theorem expect_tree (R : Type*) {M : Type*} [CommRing R] [Algebra ℝ R] [AddCommGroup M]
    [Module R M] (g : ODERepeatProtocol.Protocol (fun l x' => O l (f x')) E → M)
    (h : ODERepeatProtocol.Protocol O E → M) (hgh : ∀ p, g (protocol f p) = h p) (x' : X')
    (T : Tree O F E) : (tree f T).expect R g x' = T.expect R h (f x') := by
  induction T with
  | final p => exact hgh p
  | test t s fl ihs ihf =>
      simp only [tree, Tree.expect, probability_testRun, ihs, ihf]

theorem successMass_tree (T : Tree O F E) (x' : X') :
    (tree f T).successMass x' = T.successMass (f x') :=
  expect_tree f ℝ _ _ (fun p => successMass_protocol f p x') x' T

theorem successDensity_tree (T : Tree O F E) (x' : X') :
    (tree f T).successDensity x' = T.successDensity (f x') :=
  expect_tree f ℂ _ _ (fun p => successDensity_protocol f p x') x' T

theorem conditionalDensity_tree (T : Tree O F E) (x' : X') :
    (tree f T).conditionalDensity x' = T.conditionalDensity (f x') := by
  simp only [Tree.conditionalDensity, successMass_tree, successDensity_tree]

theorem worstCost_tree (T : Tree O F E) (w : L → ℕ) :
    (tree f T).worstCost w = T.worstCost w := by
  induction T with
  | final p => exact worstCost_protocol f p w
  | test t s fl ihs ihf =>
      simp only [tree, Tree.worstCost, testRun, cost_program, ihs, ihf]

end Reindex

end

end AdaptiveHamiltonianLowerBound
