import ReleasedODESolverLowerBounds.Transport.Plain
import ReleasedODESolverLowerBounds.Transport.Calls

set_option autoImplicit false

/-!
# Measured solvers over the call forms of a physical oracle

Manuscript Section `odel:sec:main`, lines 3669-3681 (value oracle and locators, "their inverses
and controls"; the lower bounds apply to Theorems `ode:thm:main` and `ode:thm:time`) and line
2364 (deferred measurement).

A measured solver over the call forms `callFamily B` (plain, inverse, controlled and
controlled-inverse calls of every label on control ⊗ workspace) is deferred with every call form
of the matrix label `l₀` counted (`callCountedOf l₀`). After flattening the records and the
control bit (`Transport.callFlat`), a deferred label is a record-selected call of `B` itself on
`R × Bool` (`callPatOf`, `Transport.patOp_callFlat`), so it is compiled by the controlled-call
circuit `DeferredMeasurementLowerBounds.Access.selCircuit` over the spectator lift
`1_{R × Bool} ⊗ B` and absorbed into `B'` (`Absorbs.compileProg`).

* `callEncOf`, `callCircuitsOf`: the encoding and the circuits; they act on the encoding as the
  deferred labels (`callCircuitsOf_eval`) and cost at most one call of `l₀` per counted pattern
  and none per other pattern when the inverse of `l₀` is a conjugation (`callCircuitsOf_cost`).
* `exists_treeSolver_call`: **every measured solver over the call forms of `B` gives an
  adaptive solver over the call forms of `B'`** with the same success and accuracy and at most
  the measured solver's worst-case number of calls of `l₀` in any form.

`callCountedOf`, `callPatOf`, `callEncOf` and `callCircuitsOf` are label-generic counterparts of
`DeferredMeasurementLowerBounds.Access.callCounted`, `callPat`, `callEnc` and `callCircuit`.
Those are fixed to the sampled-time access `F.access`, whose spectator register is identified by
`targetEquiv`; the physical oracle needs an absorbing isometry (`Absorbs`) and has the source
labels `Sum.inr`.
-/

namespace ReleasedODESolverLowerBounds.Transport

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model (Measured countWeight)
open DeferredMeasurementLowerBounds.Deferral (DRec DOut Pat SelLabel selFamily selWeight)
open DeferredMeasurementLowerBounds.Access (InverseConj ctrlTarget selCircuit)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)
open AdaptiveODELowerBound.Model (TreeSolver)
open AdaptiveODELowerBound.Access (CallForm callFamily activeEmbed)
open scoped InnerProduct

variable {X : Type*} {L : Type} [Fintype L] [DecidableEq L] {W W' : Type} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W']
  [CompleteSpace W'] {B : L ⊕ Bool → X → W →L[ℂ] W} {B' : L ⊕ Bool → X → W' →L[ℂ] W'}

/-- The counted labels of the call shape: every call form of the matrix label `l₀`. -/
def callCountedOf (l₀ : L) : (L ⊕ Bool) × CallForm → Prop := fun c => c.1 = Sum.inl l₀

/-- Whether a call form is counted is decidable. -/
instance (l₀ : L) : DecidablePred (callCountedOf l₀) := fun c => by
  unfold callCountedOf; infer_instance

/-- The pattern of a deferred label of the call shape, on the records and the control bit. -/
def callPatOf {R : Type} {counted : (L ⊕ Bool) × CallForm → Prop} (c : SelLabel counted R) :
    Pat (L ⊕ Bool) (R × Bool) :=
  match c with
  | .inl π => fun rd => formSelOf ((π rd.1).map fun lb => (lb.1.1, lb.2)) rd.2
  | .inr π => fun rd => formSelOf ((π rd.1).map fun lb => (lb.1.1, lb.2)) rd.2

/-- The encoding of the call shape: flattening, active control sector, absorbing isometry. -/
def callEncOf {R : Type} [Fintype R] (h : Absorbs B B' (R × Bool)) :
    Joint R (Joint Bool W) →L[ℂ] Joint Bool W' :=
  h.enc ∘L activeEmbed (Joint (R × Bool) W) ∘L
    (callFlat R W).toContinuousLinearEquiv.toContinuousLinearMap

omit [Fintype L] [DecidableEq L] in
/-- The call encoding is an isometry. -/
theorem callEncOf_isometry {R : Type} [Fintype R] (h : Absorbs B B' (R × Bool)) :
    (callEncOf h)† ∘L callEncOf h = 1 :=
  DeferredMeasurementLowerBounds.Access.comp_three_isometry _ _ _ h.enc_isometry
    AdaptiveODELowerBound.Access.activeEmbed_isometry
    (DeferredMeasurementLowerBounds.Access.isoEquiv_isometry _)

/-- **The circuits of the deferred labels of the call shape** over the call forms of `B'`. -/
def callCircuitsOf {R : Type} [Fintype R] (h : Absorbs B B' (R × Bool))
    (hB : ∀ l x, IsUnitary (B l x)) (x₀ : X) (Nc : (l : L ⊕ Bool) → Option (InverseConj B l))
    {counted : (L ⊕ Bool) × CallForm → Prop} [DecidablePred counted] (c : SelLabel counted R) :
    MultiOracleCircuit.Program (callFamily B') :=
  h.compileProg hB x₀ (selCircuit B Nc (callPatOf c))

omit [Fintype L] [DecidableEq L] in
/-- A deferred label of the call shape, flattened, is the record-selected call of its pattern
`callPatOf`. -/
theorem callFlat_selFamily {R : Type} [Fintype R] {counted : (L ⊕ Bool) × CallForm → Prop}
    (c : SelLabel counted R) (x : X) :
    (callFlat R W).conjStarAlgEquiv (selFamily (callFamily B) counted R c x) =
      DeferredMeasurementLowerBounds.Deferral.patOp B (callPatOf c) x := by
  rcases c with π | π
  · exact (congrArg _ (DeferredMeasurementLowerBounds.Access.patOp_subtype _ _ π x)).trans
      (patOp_callFlat B _ x)
  · exact (congrArg _ (DeferredMeasurementLowerBounds.Access.patOp_subtype _ _ π x)).trans
      (patOp_callFlat B _ x)

/-- The call circuits act on the encoding as the deferred labels. -/
theorem callCircuitsOf_eval {R : Type} [Fintype R] (h : Absorbs B B' (R × Bool))
    (hB : ∀ l x, IsUnitary (B l x)) (hB' : ∀ l x, IsUnitary (B' l x))
    (hsrc : ∀ b x x', B (Sum.inr b) x = B (Sum.inr b) x') (x₀ : X)
    (Nc : (l : L ⊕ Bool) → Option (InverseConj B l)) {counted : (L ⊕ Bool) × CallForm → Prop}
    [DecidablePred counted] (c : SelLabel counted R) (x : X) :
    (callCircuitsOf h hB x₀ Nc c).eval x ∘L callEncOf h =
      callEncOf h ∘L selFamily (callFamily B) counted R c x := by
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := DFunLike.congr_fun
    (h.compileProg_eval hB hB' hsrc x₀ (selCircuit B Nc (callPatOf c)) x)
    (activeEmbed _ (callFlat R W v))
  have h3 := DFunLike.congr_fun
    (DeferredMeasurementLowerBounds.Access.selCircuit_eval Nc (callPatOf c) x) (callFlat R W v)
  have h2 := DFunLike.congr_fun (callFlat_selFamily (B := B) c x) (callFlat R W v)
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] at h2
  simp only [comp_apply] at h1 h3
  change (callCircuitsOf h hB x₀ Nc c).eval x
      (h.enc (activeEmbed _ (callFlat R W v))) =
    h.enc (activeEmbed _ (callFlat R W (selFamily (callFamily B) counted R c x v)))
  rw [callCircuitsOf, h1, h3, h2]

/-- **A counted call-shape pattern costs at most one call of `l₀`, an uncounted one none**, when
the inverse of `l₀` is a conjugation. -/
theorem callCircuitsOf_cost {R : Type} [Fintype R] (h : Absorbs B B' (R × Bool))
    (hB : ∀ l x, IsUnitary (B l x)) (x₀ : X) {l₀ : L} (Nc : InverseConj B (Sum.inl l₀))
    (c : SelLabel (callCountedOf l₀) R) :
    (callCircuitsOf h hB x₀ (singleConj Nc) c).cost
        (fun c' => countWeight (· = Sum.inl l₀) c'.1) ≤ selWeight c := by
  rw [callCircuitsOf, h.compileProg_cost hB x₀ (countWeight (· = Sum.inl l₀))
    (fun b => by simp [countWeight])]
  refine (DeferredMeasurementLowerBounds.Access.selCircuit_cost B (singleConj Nc) (callPatOf c)
    (countWeight (· = Sum.inl l₀))).trans ?_
  rw [Fintype.sum_eq_single (Sum.inl l₀) (fun l hl => by simp [countWeight, hl]),
    countWeight, if_pos rfl, one_mul]
  rcases c with π | π
  · exact DeferredMeasurementLowerBounds.Access.dirCount_le_one _ _ _ (singleConj_isSome Nc)
  · refine (DeferredMeasurementLowerBounds.Access.dirCount_eq_zero _ _ _
      fun rd b hrd => ?_).le
    dsimp only [callPatOf] at hrd
    obtain ⟨f, b', he⟩ := formSelOf_eq_some hrd
    obtain ⟨⟨⟨l, hl⟩, b''⟩, -, he'⟩ := Option.map_eq_some_iff.mp he
    exact hl (congrArg (fun p : ((L ⊕ Bool) × CallForm) × Bool => p.1.1) he')

variable {N : Type} {Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
  {K s : ℕ} {F : Family X N Z K s} {ε : ℝ}
  {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [Fintype Z] [AddCommGroup Z] in
/-- **Measured solvers over the call forms of `B` are adaptive solvers over the call forms of
`B'`**: for unitary families, input-independent source labels, an inverse of the matrix label
`l₀` by conjugation and an absorption of the records and the control bit of the deferral, there
is an adaptive solver over `callFamily B'` with the success and the accuracy of the measured
solver and at most its worst-case number of calls of `l₀` in any form. -/
theorem exists_treeSolver_call (hB : ∀ l x, IsUnitary (B l x))
    (hB' : ∀ l x, IsUnitary (B' l x)) (hsrc : ∀ b x x', B (Sum.inr b) x = B (Sum.inr b) x')
    {l₀ : L} (Nc : InverseConj B (Sum.inl l₀)) (A : MeasuredSolver F (callFamily B) E G ε)
    (h : Absorbs B B' (DRec A.alg × Bool)) :
    ∃ T : TreeSolver F (callFamily B') (EuclideanSpace ℂ (Fin 1)) (Joint (DOut A.alg) E)
        (Joint (DOut A.alg) G) ε,
      T.tree.worstCost (fun c => countWeight (· = Sum.inl l₀) c.1) ≤
        A.alg.worstCost (fun c => countWeight (· = Sum.inl l₀) c.1) := by
  have hw : countWeight (callCountedOf l₀) = fun c => countWeight (· = Sum.inl l₀) c.1 := by
    funext c
    simp [countWeight, callCountedOf]
  rw [← hw]
  rcases isEmpty_or_nonempty X with hX | hX
  · refine ⟨{ tree := DeferredMeasurementLowerBounds.Access.compiledTree (callCountedOf l₀)
                (EuclideanSpace ℂ (Fin 1)) A.alg A.seed A.seed_unit (callEncOf h)
                (callEncOf_isometry h) (fun _ => MultiOracleCircuit.Program.identity)
              readout := DeferredMeasurementLowerBounds.Readout.liftReadout (DOut A.alg) A.readout
              readout_isometry :=
                DeferredMeasurementLowerBounds.Readout.liftReadout_isometry A.readout_isometry
              success := fun x => isEmptyElim x
              accurate := fun x => isEmptyElim x }, ?_⟩
    exact DeferredMeasurementLowerBounds.Access.worstCost_compiledTree A.alg A.seed_unit _
      (callEncOf_isometry h) _ _ (fun _ => Nat.zero_le _)
  · have x₀ : X := Classical.arbitrary X
    have hcirc := fun c x => callCircuitsOf_eval h hB hB' hsrc x₀ (singleConj Nc)
      (counted := callCountedOf l₀) c x
    have hBc := fun c x => AdaptiveODELowerBound.Access.callFamily_unitary hB c x
    have hB'c := fun c x => AdaptiveODELowerBound.Access.callFamily_unitary hB' c x
    refine ⟨{ tree := DeferredMeasurementLowerBounds.Access.compiledTree (callCountedOf l₀)
                (EuclideanSpace ℂ (Fin 1)) A.alg A.seed A.seed_unit (callEncOf h)
                (callEncOf_isometry h) (callCircuitsOf h hB x₀ (singleConj Nc))
              readout := DeferredMeasurementLowerBounds.Readout.liftReadout (DOut A.alg) A.readout
              readout_isometry :=
                DeferredMeasurementLowerBounds.Readout.liftReadout_isometry A.readout_isometry
              success := fun x => by
                rw [DeferredMeasurementLowerBounds.Access.successMass_compiledTree hBc hB'c A.alg
                  A.seed_unit _ (callEncOf_isometry h) _ hcirc x]
                exact A.success x
              accurate := fun x sol hsol => by
                rw [DeferredMeasurementLowerBounds.Access.conditionalDensity_compiledTree hBc hB'c
                  A.alg A.seed_unit _ (callEncOf_isometry h) _ hcirc x]
                apply DeferredMeasurementLowerBounds.Readout.densityAccurate_liftReadout
                have h := A.accurate x sol hsol
                unfold DeferredMeasurementLowerBounds.Model.Measured.conditionalDensity at h
                rwa [← DeferredMeasurementLowerBounds.Deferral.sum_pure_amplitude
                  (counted := callCountedOf l₀) A.alg x A.seed] at h }, ?_⟩
    exact DeferredMeasurementLowerBounds.Access.worstCost_compiledTree A.alg A.seed_unit _
      (callEncOf_isometry h) _ _ (fun c => callCircuitsOf_cost h hB x₀ Nc c)

end

end ReleasedODESolverLowerBounds.Transport
