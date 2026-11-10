import ODELowerBoundExtensions.Release.Embed
import AdaptiveODELowerBound.Access.Calls

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Adaptive solvers of the dissipative ODE class

Manuscript Section `odel:sec:main` (access with inverses and controls, success
flag of probability at least `2/3` on every input, conditional trace distance `ε` from the
normalised solution, worst-case query bound), and the end of the proof of Lemma `hsl:lem:precision`
("Purification and deferred measurement include adaptive and randomised algorithms").

The algorithm class is the adaptive protocol model of the package,
`SparseLinearSystems.Protocol.Tree O Fl E`: a finite classical decision tree of fresh measured
runs (each a program over the oracle family `O` on a public unit seed, then the two-outcome
measurement of a flag isometry `Fl → W`), branching on the outcomes, with a final fresh-trial
protocol (`ODERepeatProtocol.Protocol`) that heralds the output in `E`. The count is the maximum
over all transcripts of the weighted number of calls (`Tree.worstCost`), every run, every
attempt and every inverse call counted.

* `TreeSolver F O Fl E G ε`: an adaptive protocol over a labelled oracle family `O` on the
  inputs of the family `F`, an isometric readout `E → ℂ^N ⊗ G`, success mass at least `2/3` on
  every input and, for every solution, conditional output within trace distance `ε` of
  `x(T)/‖x(T)‖` (`AdaptiveHamiltonianLowerBound.DensityAccurate`), as `Release.RetrySolver`.
* `TreeForces F ε b`: every adaptive solver over the sampled-time access `F.access ι`, and every
  adaptive solver over its call forms `Access.callFamily (F.access ι)` (inverses, controls,
  controlled inverses), with any branch register `ι`, flag space, output space and garbage, makes
  at least `b` value calls and at least `b` calls in total in the worst case.
* `TreeWitnesses F τ ḡ ε b`: `F` is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and tree-forces `b`.
* `TreeCost F ε q`: `q` is the worst-case value count (`Tree.worstCost valueWeight`) of some
  adaptive solver of `F` in one of the two access shapes; it is bookkeeping over the existing
  `Tree.worstCost`, not a new cost notion. `treeForces_of_cost` and `forces_or_of_cost₂`,
  `forces_or_of_cost₃` turn max forms over realised counts into family forms (with two access
  shapes the family-level `SparseLowerBounds.ODE.forces_or_of_max` does not apply).
* Containment: a retry protocol is the tree `Tree.final` (`retryToTree`, same oracle family,
  labels, output, success mass, conditional output and worst-case cost), so `TreeForces` implies
  `Release.RetryForces` and `SparseLowerBounds.ODE.Family.Forces` (`treeForces_retryForces`,
  `treeForces_forces`, `treeWitnesses_retryWitnesses`, `treeWitnesses_witnesses`).
-/

namespace AdaptiveODELowerBound.Model

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (RetrySolver RetryForces RetryWitnesses)
open scoped InnerProduct InnerProductSpace

/-! ### Worst-case costs of adaptive protocols -/

section Cost

variable {W Fl E X L : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {O : L → X → W →L[ℂ] W}

/-- The worst-case cost of an adaptive protocol is monotone in the label weights. -/
theorem worstCost_mono_tree (T : Tree O Fl E) {w v : L → ℕ} (h : ∀ l, w l ≤ v l) :
    T.worstCost w ≤ T.worstCost v := by
  induction T with
  | final p => exact ODELowerBoundExtensions.Release.worstCost_mono p h
  | test t s f ihs ihf =>
      exact Nat.add_le_add (t.circuit.cost_mono h) (max_le_max ihs ihf)

/-- Scaling the label weights by `c` scales the worst-case cost of an adaptive protocol by
`c`. -/
theorem worstCost_mul_tree (T : Tree O Fl E) (c : ℕ) (w : L → ℕ) :
    T.worstCost (fun l => c * w l) = c * T.worstCost w := by
  induction T with
  | final p => exact ODELowerBoundExtensions.Release.worstCost_mul p c w
  | test t s f ihs ihf =>
      simp only [Tree.worstCost, ODELowerBoundExtensions.Release.program_cost_mul, ihs, ihf,
        Nat.mul_max_mul_left, Nat.mul_add]

end Cost

/-! ### Solvers, forcing and witnessing -/

/-- **An adaptive solver for the family `F` at accuracy `ε`** (Section `odel:sec:main`), over a
labelled oracle family `O` on the inputs of `F`: an adaptive protocol `tree` (fresh measured runs
with classical branching, then a heralded fresh-trial protocol), an isometric readout of its output
onto system `ℂ^N` ⊗ garbage `G`, success mass at least `2/3` on every input and, for every solution,
conditional output `ε`-close to `x(T)/‖x(T)‖` in trace distance (observable form,
`DensityAccurate`). -/
structure TreeSolver {X N Z : Type*} [Fintype N] [DecidableEq N] {K s : ℕ}
    (F : Family X N Z K s) {L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (O : L → X → W →L[ℂ] W) (Fl E G : Type*)
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (ε : ℝ) where
  /-- The adaptive protocol. -/
  tree : Tree O Fl E
  /-- The readout of the heralded output onto system ⊗ garbage. -/
  readout : E →L[ℂ] SysGarb N G
  readout_isometry : readout† ∘L readout = 1
  /-- Success probability at least `2/3` on every input. -/
  success : ∀ x, 2 / 3 ≤ tree.successMass x
  /-- Conditional trace distance at most `ε` from the normalised solution. -/
  accurate : ∀ x sol, F.Solves x sol →
    DensityAccurate readout (tree.conditionalDensity x)
      (ODEStateNormalization.unitDirection (sol F.T)) ε

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- **`F` forces `b` queries on adaptive protocols at accuracy `ε`**: every adaptive solver over
the sampled-time access `F.access ι`, and every adaptive solver over its call forms
`Access.callFamily (F.access ι)` (plain, inverse, controlled and controlled-inverse calls of every
label, on control ⊗ workspace), with any branch register `ι`, flag space `Fl`, output space `E`
and garbage `G`, makes at least `b` value calls and at least `b` calls in total in the worst case
over all transcripts (`Tree.worstCost`; every run, attempt and inverse call counted). -/
def TreeForces (F : Family X N Z K s) (ε b : ℝ) : Prop :=
  (∀ (ι : Type) [Fintype ι] (Fl E G : Type) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver F (F.access ι) Fl E G ε),
    b ≤ A.tree.worstCost valueWeight ∧ b ≤ A.tree.worstCost (fun _ => 1)) ∧
  (∀ (ι : Type) [Fintype ι] (Fl E G : Type) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver F (Access.callFamily (F.access ι)) Fl E G ε),
    b ≤ A.tree.worstCost (fun c => valueWeight c.1) ∧ b ≤ A.tree.worstCost (fun _ => 1))

/-- **`F` witnesses the bound `b` on adaptive protocols** for the parameters `(τ, ḡ, ε)`: `F` is
in the class with `η = 1`, `T = τ` and `g ≤ ḡ`, and tree-forces `b` at accuracy `ε`. -/
structure TreeWitnesses (F : Family X N Z K s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : TreeForces F ε b

/-- A tree witness of `b` witnesses every smaller bound. -/
theorem TreeWitnesses.mono {F : Family X N Z K s} {τ gbar ε b b' : ℝ}
    (hW : TreeWitnesses F τ gbar ε b) (hb : b' ≤ b) : TreeWitnesses F τ gbar ε b' := by
  refine ⟨hW.inClass, hW.time_eq, ⟨?_, ?_⟩⟩
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.1 ι Fl E G A
    exact ⟨hb.trans h1, hb.trans h2⟩
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.2 ι Fl E G A
    exact ⟨hb.trans h1, hb.trans h2⟩

/-- **A realised worst-case value count**: `q` is the worst-case value count of some adaptive
solver of `F` at accuracy `ε`, over the sampled-time access or over its call forms. -/
def TreeCost (F : Family X N Z K s) (ε q : ℝ) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (Fl E G : Type) (_ : NormedAddCommGroup Fl)
      (_ : InnerProductSpace ℂ Fl) (_ : CompleteSpace Fl) (_ : NormedAddCommGroup E)
      (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E) (_ : FiniteDimensional ℂ E)
      (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
      (A : TreeSolver F (F.access ι) Fl E G ε), q = A.tree.worstCost valueWeight) ∨
  (∃ (ι : Type) (_ : Fintype ι) (Fl E G : Type) (_ : NormedAddCommGroup Fl)
      (_ : InnerProductSpace ℂ Fl) (_ : CompleteSpace Fl) (_ : NormedAddCommGroup E)
      (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E) (_ : FiniteDimensional ℂ E)
      (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
      (A : TreeSolver F (Access.callFamily (F.access ι)) Fl E G ε),
      q = A.tree.worstCost (fun c => valueWeight c.1))

/-- Forcing is a lower bound on every realised value count. -/
theorem TreeForces.le_cost {F : Family X N Z K s} {ε b : ℝ} (h : TreeForces F ε b) {q : ℝ}
    (hq : TreeCost F ε q) : b ≤ q := by
  rcases hq with ⟨ι, _, Fl, E, G, _, _, _, _, _, _, _, _, _, _, A, rfl⟩ |
    ⟨ι, _, Fl, E, G, _, _, _, _, _, _, _, _, _, _, A, rfl⟩
  · exact (h.1 ι Fl E G A).1
  · exact (h.2 ι Fl E G A).1

/-- A lower bound on every realised value count is forcing (the total count is at least the
value count). -/
theorem treeForces_of_cost {F : Family X N Z K s} {ε b : ℝ}
    (h : ∀ q, TreeCost F ε q → b ≤ q) : TreeForces F ε b := by
  have hw : ∀ q, valueWeight q ≤ 1 := fun q => by cases q <;> simp [valueWeight]
  refine ⟨?_, ?_⟩
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost valueWeight :=
      h _ (Or.inl ⟨ι, inferInstance, Fl, E, G, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, A, rfl⟩)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast worstCost_mono_tree A.tree hw
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost (fun c => valueWeight c.1) :=
      h _ (Or.inr ⟨ι, inferInstance, Fl, E, G, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, A, rfl⟩)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast worstCost_mono_tree A.tree (fun c => hw c.1)

/-- **From a max form to a family form, two families.** -/
theorem forces_or_of_cost₂ {P₁ P₂ : ℝ → Prop} {b : ℝ}
    (h : ∀ q₁ q₂, P₁ q₁ → P₂ q₂ → b ≤ max q₁ q₂) :
    (∀ q, P₁ q → b ≤ q) ∨ (∀ q, P₂ q → b ≤ q) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨q₁, h₁, hq₁⟩, ⟨q₂, h₂, hq₂⟩⟩ := hc
  exact absurd (h q₁ q₂ h₁ h₂) (not_le.mpr (max_lt hq₁ hq₂))

/-- **From a max form to a family form, three families.** -/
theorem forces_or_of_cost₃ {P₁ P₂ P₃ : ℝ → Prop} {b : ℝ}
    (h : ∀ q₁ q₂ q₃, P₁ q₁ → P₂ q₂ → P₃ q₃ → b ≤ max q₁ (max q₂ q₃)) :
    (∀ q, P₁ q → b ≤ q) ∨ (∀ q, P₂ q → b ≤ q) ∨ (∀ q, P₃ q → b ≤ q) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨q₁, h₁, hq₁⟩, ⟨q₂, h₂, hq₂⟩, ⟨q₃, h₃, hq₃⟩⟩ := hc
  exact absurd (h q₁ q₂ q₃ h₁ h₂ h₃) (not_le.mpr (max_lt hq₁ (max_lt hq₂ hq₃)))

/-! ### Retry protocols and single programs are adaptive protocols -/

/-- **A retry solver is an adaptive solver**: the tree `Tree.final` of its protocol, with any flag
space, over the same oracle family and labels. -/
def retryToTree {F : Family X N Z K s} {L W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {O : L → X → W →L[ℂ] W} {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {ε : ℝ}
    (A : RetrySolver F O E G ε) (Fl : Type*) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] : TreeSolver F O Fl E G ε where
  tree := .final A.prot
  readout := A.readout
  readout_isometry := A.readout_isometry
  success := A.success
  accurate := A.accurate

omit [Fintype Z] [AddCommGroup Z] in
/-- The tree of a retry solver has the worst-case cost of its protocol. -/
@[simp] theorem worstCost_retryToTree {F : Family X N Z K s} {L W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {O : L → X → W →L[ℂ] W} {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {ε : ℝ}
    (A : RetrySolver F O E G ε) (Fl : Type*) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] (w : L → ℕ) :
    (retryToTree A Fl).tree.worstCost w = A.prot.worstCost w :=
  rfl

/-- **Containment of the retry class**: tree-forcing implies retry-forcing. -/
theorem treeForces_retryForces {F : Family X N Z K s} {ε b : ℝ} (h : TreeForces F ε b) :
    RetryForces F ε b := by
  intro ι _ E G _ _ _ _ _ _ _ A
  exact h.1 ι ℂ E G (retryToTree A ℂ)

/-- A tree witness is a retry witness. -/
theorem treeWitnesses_retryWitnesses {F : Family X N Z K s} {τ gbar ε b : ℝ}
    (h : TreeWitnesses F τ gbar ε b) : RetryWitnesses F τ gbar ε b :=
  ⟨h.inClass, h.time_eq, treeForces_retryForces h.forces⟩

section Single

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- Tree-forcing implies the forcing of `SparseLowerBounds.ODE` (single programs with a herald). -/
theorem treeForces_forces {F : Family X N Z K s} {ε b : ℝ} (h : TreeForces F ε b) :
    F.Forces ε b :=
  ODELowerBoundExtensions.Release.retryForces_forces (treeForces_retryForces h)

/-- A tree witness is a witness of `SparseLowerBounds.ODE`. -/
theorem treeWitnesses_witnesses {F : Family X N Z K s} {τ gbar ε b : ℝ}
    (h : TreeWitnesses F τ gbar ε b) : F.Witnesses τ gbar ε b :=
  ⟨h.inClass, h.time_eq, treeForces_forces h.forces⟩

end Single

end

end AdaptiveODELowerBound.Model
