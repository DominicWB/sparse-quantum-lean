import ReleasedODESolverLowerBounds.Transport.Encode
import DeferredMeasurementLowerBounds.Access.ControlTree
import DeferredMeasurementLowerBounds.Corollaries.ODESolver

set_option autoImplicit false

/-!
# Measured solvers over a physical oracle: the plain shape

Manuscript Section `odel:sec:main` (access with inverses and controls, success flag of probability
at least `2/3`, conditional trace distance `ε`, worst-case query bound; "the lower bounds apply to
the upper bounds of the preceding section"), proof of Lemma `hsl:lem:precision` ("Purification and
deferred measurement include adaptive and randomised algorithms") and Section `odel:sec:main`
(source preparation contains no hidden input information).

A measured solver (`DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver`) over a labelled
oracle family `B : L ⊕ Bool → X → W →L[ℂ] W` (matrix labels and two input-independent source
labels) is deferred (`DeferredMeasurementLowerBounds.Deferral.deferral`), its record-selected
calls are compiled into controlled calls of the spectator lift `1_{DRec} ⊗ B`
(`DeferredMeasurementLowerBounds.Access.ctrlCircuits`), and the spectator lift is absorbed into a
larger oracle `B'` (`Absorbs`, `Absorbs.compileProg`). The result is an adaptive solver
(`AdaptiveODELowerBound.Model.TreeSolver`) over the call forms `callFamily B'` (`exists_treeSolver_plain`).

* `singleConj Nc`: the conjugation data that uses `Nc` for one label and none for the others.
* `plainEncOf`, `plainCircuitsOf`: the encoding `ℂ^{DRec} ⊗ W → Joint Bool W'` and the circuits
  of the deferred labels; they act on the encoding as the deferred labels
  (`plainCircuitsOf_eval`) and cost at most one call of `l₀` per counted pattern and none per
  other pattern when the inverse of `l₀` is a conjugation (`plainCircuitsOf_cost`).
* `exists_treeSolver_plain`: **every measured solver over `B` gives an adaptive solver over the
  call forms of `B'`** with the same success and accuracy and at most the measured solver's
  worst-case number of calls of `l₀`. No constant is lost.

`plainEncOf` and `plainCircuitsOf` are label-generic counterparts of
`DeferredMeasurementLowerBounds.Access.plainEnc` and `plainCircuit`. Those are fixed to the
sampled-time access `F.access`, whose spectator register is identified by `targetEquiv`; the
physical oracle needs an absorbing isometry (`Absorbs`) and has the source labels `Sum.inr`.
-/

namespace ReleasedODESolverLowerBounds.Transport

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model (Measured countWeight)
open DeferredMeasurementLowerBounds.Deferral (DRec DOut SelLabel selFamily selWeight)
open DeferredMeasurementLowerBounds.Access (InverseConj ctrlTarget ctrlCircuits)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)
open AdaptiveODELowerBound.Model (TreeSolver)
open AdaptiveODELowerBound.Access (CallForm callFamily activeEmbed)
open scoped InnerProduct

variable {X : Type*} {L : Type} [Fintype L] [DecidableEq L] {W W' : Type} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
  [CompleteSpace W'] {B : L ⊕ Bool → X → W →L[ℂ] W} {B' : L ⊕ Bool → X → W' →L[ℂ] W'}

/-- The conjugation data that uses `Nc` for the label `l₀` and none for the other labels. -/
def singleConj {l₀ : L ⊕ Bool} (Nc : InverseConj B l₀) :
    (l : L ⊕ Bool) → Option (InverseConj B l) :=
  fun l => if h : l = l₀ then some (h ▸ Nc) else none

omit [Fintype L] in
/-- The single conjugation is present at its label. -/
theorem singleConj_isSome {l₀ : L ⊕ Bool} (Nc : InverseConj B l₀) : (singleConj Nc l₀).isSome := by
  simp [singleConj]

/-- The encoding of the plain shape: active control sector, then the absorbing isometry. -/
def plainEncOf {J : Type} [Fintype J] (h : Absorbs B B' J) : Joint J W →L[ℂ] Joint Bool W' :=
  h.enc ∘L activeEmbed (Joint J W)

omit [Fintype L] [DecidableEq L] in
/-- The plain encoding is an isometry. -/
theorem plainEncOf_isometry {J : Type} [Fintype J] (h : Absorbs B B' J) :
    (plainEncOf h)† ∘L plainEncOf h = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [plainEncOf, adjoint_comp, comp_apply]
  rw [← comp_apply (h.enc†) h.enc, h.enc_isometry, one_apply_eq_self,
    ← comp_apply ((activeEmbed (Joint J W))†) (activeEmbed (Joint J W)),
    AdaptiveODELowerBound.Access.activeEmbed_isometry, one_apply_eq_self]

/-- **The circuits of the deferred labels of the plain shape** over the call forms of `B'`. -/
def plainCircuitsOf {R : Type} [Fintype R] (h : Absorbs B B' R) (hB : ∀ l x, IsUnitary (B l x))
    (x₀ : X) (Nc : (l : L ⊕ Bool) → Option (InverseConj B l)) (counted : L ⊕ Bool → Prop)
    [DecidablePred counted] (c : SelLabel counted R) :
    MultiOracleCircuit.Program (callFamily B') :=
  h.compileProg hB x₀ (ctrlCircuits B Nc counted R c)

/-- The plain circuits act on the encoding as the deferred labels. -/
theorem plainCircuitsOf_eval {R : Type} [Fintype R] (h : Absorbs B B' R)
    (hB : ∀ l x, IsUnitary (B l x)) (hB' : ∀ l x, IsUnitary (B' l x))
    (hsrc : ∀ b x x', B (Sum.inr b) x = B (Sum.inr b) x') (x₀ : X)
    (Nc : (l : L ⊕ Bool) → Option (InverseConj B l)) (counted : L ⊕ Bool → Prop)
    [DecidablePred counted] (c : SelLabel counted R) (x : X) :
    (plainCircuitsOf h hB x₀ Nc counted c).eval x ∘L plainEncOf h =
      plainEncOf h ∘L selFamily B counted R c x := by
  rw [plainCircuitsOf, plainEncOf, ← comp_assoc, h.compileProg_eval hB hB' hsrc x₀, comp_assoc,
    DeferredMeasurementLowerBounds.Access.ctrlCircuits_eval, comp_assoc]

/-- **A counted plain pattern costs at most one call of `l₀`, an uncounted one none**, when the
inverse of `l₀` is a conjugation. -/
theorem plainCircuitsOf_cost {R : Type} [Fintype R] (h : Absorbs B B' R)
    (hB : ∀ l x, IsUnitary (B l x)) (x₀ : X) {l₀ : L} (Nc : InverseConj B (Sum.inl l₀))
    (c : SelLabel (· = Sum.inl l₀) R) :
    (plainCircuitsOf h hB x₀ (singleConj Nc) (· = Sum.inl l₀) c).cost
        (fun c' => countWeight (· = Sum.inl l₀) c'.1) ≤ selWeight c := by
  rw [plainCircuitsOf, h.compileProg_cost hB x₀ (countWeight (· = Sum.inl l₀))
    (fun b => by simp [countWeight])]
  exact DeferredMeasurementLowerBounds.Access.ctrlCircuits_cost_conj B (singleConj Nc) (Sum.inl l₀)
    (singleConj_isSome Nc) R c

variable {N : Type} {Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
  {K s : ℕ} {F : Family X N Z K s} {ε : ℝ}
  {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [Fintype Z] [AddCommGroup Z] in
/-- **Measured solvers over `B` are adaptive solvers over the call forms of `B'`** (plain
shape): for unitary families, input-independent source labels, an inverse of the matrix label
`l₀` by conjugation and an absorption of the record register of the deferral, there is an
adaptive solver over `callFamily B'` with the success and the accuracy of the measured solver
and at most its worst-case number of calls of `l₀`. -/
theorem exists_treeSolver_plain (hB : ∀ l x, IsUnitary (B l x))
    (hB' : ∀ l x, IsUnitary (B' l x)) (hsrc : ∀ b x x', B (Sum.inr b) x = B (Sum.inr b) x')
    {l₀ : L} (Nc : InverseConj B (Sum.inl l₀)) (A : MeasuredSolver F B E G ε)
    (h : Absorbs B B' (DRec A.alg)) :
    ∃ T : TreeSolver F (callFamily B') (EuclideanSpace ℂ (Fin 1)) (Joint (DOut A.alg) E)
        (Joint (DOut A.alg) G) ε,
      T.tree.worstCost (fun c => countWeight (· = Sum.inl l₀) c.1) ≤
        A.alg.worstCost (countWeight (· = Sum.inl l₀)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨{ tree := DeferredMeasurementLowerBounds.Access.compiledTree (· = Sum.inl l₀)
                (EuclideanSpace ℂ (Fin 1)) A.alg A.seed A.seed_unit (plainEncOf h)
                (plainEncOf_isometry h) (fun _ => MultiOracleCircuit.Program.identity)
              readout := DeferredMeasurementLowerBounds.Readout.liftReadout (DOut A.alg) A.readout
              readout_isometry :=
                DeferredMeasurementLowerBounds.Readout.liftReadout_isometry A.readout_isometry
              success := fun x => isEmptyElim x
              accurate := fun x => isEmptyElim x }, ?_⟩
    exact DeferredMeasurementLowerBounds.Access.worstCost_compiledTree A.alg A.seed_unit _
      (plainEncOf_isometry h) _ _ (fun _ => Nat.zero_le _)
  · have x₀ : X := Classical.arbitrary X
    have hcirc := fun c x => plainCircuitsOf_eval h hB hB' hsrc x₀ (singleConj Nc)
      (· = Sum.inl l₀) c x
    have hB'c := fun c x => AdaptiveODELowerBound.Access.callFamily_unitary hB' c x
    refine ⟨{ tree := DeferredMeasurementLowerBounds.Access.compiledTree (· = Sum.inl l₀)
                (EuclideanSpace ℂ (Fin 1)) A.alg A.seed A.seed_unit (plainEncOf h)
                (plainEncOf_isometry h) (plainCircuitsOf h hB x₀ (singleConj Nc) (· = Sum.inl l₀))
              readout := DeferredMeasurementLowerBounds.Readout.liftReadout (DOut A.alg) A.readout
              readout_isometry :=
                DeferredMeasurementLowerBounds.Readout.liftReadout_isometry A.readout_isometry
              success := fun x => by
                rw [DeferredMeasurementLowerBounds.Access.successMass_compiledTree hB hB'c A.alg
                  A.seed_unit _ (plainEncOf_isometry h) _ hcirc x]
                exact A.success x
              accurate := fun x sol hsol => by
                rw [DeferredMeasurementLowerBounds.Access.conditionalDensity_compiledTree hB hB'c
                  A.alg A.seed_unit _ (plainEncOf_isometry h) _ hcirc x]
                apply DeferredMeasurementLowerBounds.Readout.densityAccurate_liftReadout
                have h := A.accurate x sol hsol
                unfold DeferredMeasurementLowerBounds.Model.Measured.conditionalDensity at h
                rwa [← DeferredMeasurementLowerBounds.Deferral.sum_pure_amplitude
                  (counted := (· = Sum.inl l₀)) A.alg x A.seed] at h }, ?_⟩
    exact DeferredMeasurementLowerBounds.Access.worstCost_compiledTree A.alg A.seed_unit _
      (plainEncOf_isometry h) _ _ (fun c => plainCircuitsOf_cost h hB x₀ Nc c)

end

end ReleasedODESolverLowerBounds.Transport
