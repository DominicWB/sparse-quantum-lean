import DeferredMeasurementLowerBounds.Access.TimeCircuits
import DeferredMeasurementLowerBounds.Readout.Density
import AdaptiveODELowerBound.Model.Solver
import DeferredMeasurementLowerBounds.Model.Embed

set_option autoImplicit false

/-!
# Measured solvers of the dissipative ODE class

Manuscript Section `odel:sec:main` (access with inverses and controls, success
flag of probability at least `2/3` on every input, conditional trace distance `ε` from the
normalised solution, worst-case query bound) and the end of the proof of Lemma
`hsl:lem:precision` (purification and deferred measurement).

* `MeasuredSolver F O E G ε`: a measured algorithm (`Model.Measured`: mid-run and multi-outcome
  measurements, classical control, randomness and resets of finite-dimensional registers on a
  persistent workspace) over a
  labelled oracle family `O` on the inputs of `F`, a unit initial vector, an isometric readout
  `E → ℂ^N ⊗ G`, success mass at least `2/3` on every input and, for every solution, conditional
  output within trace distance `ε` of `x(T)/‖x(T)‖` (`DensityAccurate`); it mirrors
  `AdaptiveODELowerBound.Model.TreeSolver` field for field (system register `N` in `Type`, as
  for the register exchange of the readout).
* `MeasuredForces F ε b`: every measured solver over the sampled-time access `F.access ι` and
  every measured solver over its call forms `callFamily (F.access ι)`, with any branch register,
  output and garbage spaces (in `Type`), makes at least `b` value calls and at least `b` calls in
  total in the worst case over all transcripts. `MeasuredWitnesses`: in the class and forcing.
* `plainTreeSolver`, `callTreeSolver`: the deferred and compiled protocol of a measured solver is
  an adaptive solver over the call forms of the sampled-time access with the branch register
  `DRec × ι` (respectively `(DRec × Bool) × ι`), the readout `Readout.liftReadout`, and at most
  the measured solver's worst-case number of value calls (`worstCost_plainTreeSolver`,
  `worstCost_callTreeSolver`).
* `measuredForces_of_treeForces`: **tree forcing implies measured forcing with the same bound**
  (the value call's inverse is a conjugated value call, so no factor is lost).
* `MeasuredSolver.ofTreeSolver`, `treeForces_of_measuredForces`: conversely every adaptive
  solver is a measured solver with the same worst-case costs (`Model.ofTree`; the workspaces of
  the sampled-time access are finite-dimensional), so for families with an input measured
  forcing and tree forcing are equivalent.
-/

namespace DeferredMeasurementLowerBounds.Corollaries

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open ContinuousLinearMap OracleCircuit SparseLinearSystems.Protocol
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open DeferredMeasurementLowerBounds.Access DeferredMeasurementLowerBounds.Readout
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily)
open AdaptiveODELowerBound.Model (TreeSolver TreeForces TreeWitnesses)
open scoped InnerProduct InnerProductSpace

/-- **A measured solver for the family `F` at accuracy `ε`** over the labelled oracle family
`O` on the inputs of `F`. -/
structure MeasuredSolver {N : Type} {X Z : Type*} [Fintype N] [DecidableEq N] {Kt s : ℕ}
    (F : Family X N Z Kt s) {L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (O : L → X → W →L[ℂ] W) (E G : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (ε : ℝ) where
  /-- The measured algorithm. -/
  alg : Measured O E
  /-- The input-independent unit initial vector. -/
  seed : W
  seed_unit : ‖seed‖ = 1
  /-- The readout of the heralded output onto system ⊗ garbage. -/
  readout : E →L[ℂ] SysGarb N G
  readout_isometry : readout† ∘L readout = 1
  /-- Success probability at least `2/3` on every input. -/
  success : ∀ x, 2 / 3 ≤ alg.successMass x seed
  /-- Conditional trace distance at most `ε` from the normalised solution. -/
  accurate : ∀ x sol, F.Solves x sol →
    DensityAccurate readout (alg.conditionalDensity x seed)
      (ODEStateNormalization.unitDirection (sol F.T)) ε

variable {N : Type} {X Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
  {Kt s : ℕ}

/-- **`F` forces `b` queries on measured algorithms at accuracy `ε`**, over the sampled-time
access and over its call forms, value calls and all calls counted in the worst case. -/
def MeasuredForces (F : Family X N Z Kt s) (ε b : ℝ) : Prop :=
  (∀ (ι : Type) [Fintype ι] (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (A : MeasuredSolver F (F.access ι) E G ε),
    b ≤ A.alg.worstCost valueWeight ∧ b ≤ A.alg.worstCost (fun _ => 1)) ∧
  (∀ (ι : Type) [Fintype ι] (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (A : MeasuredSolver F (callFamily (F.access ι)) E G ε),
    b ≤ A.alg.worstCost (fun c => valueWeight c.1) ∧ b ≤ A.alg.worstCost (fun _ => 1))

/-- **`F` witnesses the bound `b` on measured algorithms** for the parameters `(τ, ḡ, ε)`. -/
structure MeasuredWitnesses (F : Family X N Z Kt s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : MeasuredForces F ε b

variable {F : Family X N Z Kt s} {ε : ℝ} {ι : Type} [Fintype ι]
  {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The deferred plain-shape solver** as an adaptive solver over the call forms. -/
def plainTreeSolver (A : MeasuredSolver F (F.access ι) E G ε) :
    TreeSolver F (callFamily (F.access (DRec A.alg × ι))) (EuclideanSpace ℂ (Fin 1))
      (Joint (DOut A.alg) E) (Joint (DOut A.alg) G) ε where
  tree := compiledTree plainCounted (EuclideanSpace ℂ (Fin 1)) A.alg A.seed A.seed_unit
    (plainEnc (DRec A.alg) ι) plainEnc_isometry (plainCircuit F)
  readout := liftReadout (DOut A.alg) A.readout
  readout_isometry := liftReadout_isometry A.readout_isometry
  success := fun x => by
    rw [successMass_compiledTree (fun q x => F.access_unitary ι q x)
      (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (fun q x => F.access_unitary _ q x) c x)
      A.alg A.seed_unit _ plainEnc_isometry _ (fun c x => plainCircuit_eval F c x) x]
    exact A.success x
  accurate := fun x sol hsol => by
    rw [conditionalDensity_compiledTree (fun q x => F.access_unitary ι q x)
      (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (fun q x => F.access_unitary _ q x) c x)
      A.alg A.seed_unit _ plainEnc_isometry _ (fun c x => plainCircuit_eval F c x) x]
    apply densityAccurate_liftReadout
    have h := A.accurate x sol hsol
    unfold Measured.conditionalDensity at h
    rwa [← sum_pure_amplitude (counted := plainCounted) A.alg x A.seed] at h

/-- The deferred plain-shape solver makes at most the measured solver's worst-case number of
value calls. -/
theorem worstCost_plainTreeSolver (A : MeasuredSolver F (F.access ι) E G ε) :
    (plainTreeSolver A).tree.worstCost (fun c => valueWeight c.1) ≤
      A.alg.worstCost valueWeight := by
  have hw : countWeight plainCounted = valueWeight := by
    funext q
    cases q <;> simp [countWeight, plainCounted, valueWeight]
  have h := worstCost_compiledTree (F := EuclideanSpace ℂ (Fin 1)) A.alg A.seed_unit
    (plainEnc (DRec A.alg) ι) plainEnc_isometry (plainCircuit F) _ (plainCircuit_cost F)
  rw [hw] at h
  exact h

/-- **The deferred call-shape solver** as an adaptive solver over the call forms. -/
def callTreeSolver (A : MeasuredSolver F (callFamily (F.access ι)) E G ε) :
    TreeSolver F (callFamily (F.access ((DRec A.alg × Bool) × ι))) (EuclideanSpace ℂ (Fin 1))
      (Joint (DOut A.alg) E) (Joint (DOut A.alg) G) ε where
  tree := compiledTree callCounted (EuclideanSpace ℂ (Fin 1)) A.alg A.seed A.seed_unit
    (callEnc (DRec A.alg) ι) callEnc_isometry (callCircuit F)
  readout := liftReadout (DOut A.alg) A.readout
  readout_isometry := liftReadout_isometry A.readout_isometry
  success := fun x => by
    rw [successMass_compiledTree (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (fun q x => F.access_unitary ι q x) c x)
      (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (fun q x => F.access_unitary _ q x) c x)
      A.alg A.seed_unit _ callEnc_isometry _ (fun c x => callCircuit_eval F c x) x]
    exact A.success x
  accurate := fun x sol hsol => by
    rw [conditionalDensity_compiledTree (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (fun q x => F.access_unitary ι q x) c x)
      (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (fun q x => F.access_unitary _ q x) c x)
      A.alg A.seed_unit _ callEnc_isometry _ (fun c x => callCircuit_eval F c x) x]
    apply densityAccurate_liftReadout
    have h := A.accurate x sol hsol
    unfold Measured.conditionalDensity at h
    rwa [← sum_pure_amplitude (counted := callCounted) A.alg x A.seed] at h

/-- The deferred call-shape solver makes at most the measured solver's worst-case number of
value calls. -/
theorem worstCost_callTreeSolver (A : MeasuredSolver F (callFamily (F.access ι)) E G ε) :
    (callTreeSolver A).tree.worstCost (fun c => valueWeight c.1) ≤
      A.alg.worstCost (fun c => valueWeight c.1) := by
  have hw : countWeight callCounted = fun c => valueWeight c.1 := by
    funext c
    obtain ⟨q, f⟩ := c
    cases q <;> simp [countWeight, callCounted, valueWeight]
  have h := worstCost_compiledTree (F := EuclideanSpace ℂ (Fin 1)) A.alg A.seed_unit
    (callEnc (DRec A.alg) ι) callEnc_isometry (callCircuit F) _ (callCircuit_cost F)
  rw [hw] at h
  exact h

variable (F) in
/-- **Tree forcing implies measured forcing with the same bound** (the solver class of Section
`odel:sec:main` with measurements inside a run; purification and deferred measurement). -/
theorem measuredForces_of_treeForces {b : ℝ} (h : TreeForces F ε b) : MeasuredForces F ε b := by
  have hw : ∀ q, valueWeight q ≤ 1 := fun q => by cases q <;> simp [valueWeight]
  constructor
  · intro ι _ E G _ _ _ _ _ _ _ A
    have hb := (h.2 (DRec A.alg × ι) (EuclideanSpace ℂ (Fin 1)) (Joint (DOut A.alg) E)
      (Joint (DOut A.alg) G) (plainTreeSolver A)).1
    have hv : b ≤ A.alg.worstCost valueWeight :=
      hb.trans (by exact_mod_cast worstCost_plainTreeSolver A)
    exact ⟨hv, hv.trans (by exact_mod_cast A.alg.worstCost_mono hw)⟩
  · intro ι _ E G _ _ _ _ _ _ _ A
    have hb := (h.2 ((DRec A.alg × Bool) × ι) (EuclideanSpace ℂ (Fin 1)) (Joint (DOut A.alg) E)
      (Joint (DOut A.alg) G) (callTreeSolver A)).1
    have hv : b ≤ A.alg.worstCost (fun c => valueWeight c.1) :=
      hb.trans (by exact_mod_cast worstCost_callTreeSolver A)
    exact ⟨hv, hv.trans (by exact_mod_cast A.alg.worstCost_mono (fun c => hw c.1))⟩

/-- **Tree witnesses are measured witnesses of the same bound.** -/
theorem measuredWitnesses_of_treeWitnesses {τ gbar b : ℝ} (h : TreeWitnesses F τ gbar ε b) :
    MeasuredWitnesses F τ gbar ε b :=
  ⟨h.inClass, h.time_eq, measuredForces_of_treeForces F h.forces⟩

/-! ### Adaptive solvers are measured solvers -/

/-- **An adaptive solver as a measured solver** (`Model.ofTree`), for unitary labels on a
finite-dimensional workspace, from any unit initial vector. -/
def MeasuredSolver.ofTreeSolver {L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] [FiniteDimensional ℂ W] {O : L → X → W →L[ℂ] W}
    (hO : ∀ l x, IsUnitary (O l x)) {Fl : Type*} [NormedAddCommGroup Fl]
    [InnerProductSpace ℂ Fl] [CompleteSpace Fl] (A : TreeSolver F O Fl E G ε) (φ : W)
    (hφ : ‖φ‖ = 1) : MeasuredSolver F O E G ε where
  alg := ofTree A.tree
  seed := φ
  seed_unit := hφ
  readout := A.readout
  readout_isometry := A.readout_isometry
  success := fun x => by
    rw [successMass_ofTree hO A.tree x hφ]
    exact A.success x
  accurate := fun x sol hsol => by
    rw [conditionalDensity_ofTree hO A.tree x hφ]
    exact A.accurate x sol hsol

variable (F) in
/-- **Measured forcing implies tree forcing with the same bound** (Section `odel:sec:main`), for a
family with an input. -/
theorem treeForces_of_measuredForces [Nonempty X] {b : ℝ} (h : MeasuredForces F ε b) :
    TreeForces F ε b := by
  obtain ⟨x⟩ := ‹Nonempty X›
  constructor
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨φ, hφ⟩ := exists_unit_of_successMass_pos A.tree x (by linarith [A.success x])
    have hA := h.1 ι E G (MeasuredSolver.ofTreeSolver (fun q x => F.access_unitary ι q x) A φ hφ)
    simpa only [MeasuredSolver.ofTreeSolver, worstCost_ofTree] using hA
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨φ, hφ⟩ := exists_unit_of_successMass_pos A.tree x (by linarith [A.success x])
    have hA := h.2 ι E G (MeasuredSolver.ofTreeSolver
      (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (fun q x => F.access_unitary ι q x) c x) A φ hφ)
    simpa only [MeasuredSolver.ofTreeSolver, worstCost_ofTree] using hA

end

end DeferredMeasurementLowerBounds.Corollaries
