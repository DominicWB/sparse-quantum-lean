import DeferredMeasurementLowerBounds.Access.TimeAccess

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# Circuits over the call forms of the sampled-time ODE access

Manuscript Section `odel:sec:main`, lines 3669-3673 (a reversible value oracle and in-place
locators, "their inverses and controls, with a coherent time address").

`plainCircuit`, `callCircuit`: the deferred selection labels of a measured algorithm over the
sampled-time access `F.access ι` (plain shape) or over its call forms `callFamily (F.access ι)`
(call shape) as programs over the call forms `callFamily (F.access J)` of the sampled-time access
with the branch register `J = (R × ι)`, respectively `((R × Bool) × ι)`, on the encodings
`plainEnc`, `callEnc`. They are the controlled-call circuits of `Access.selCircuit` moved along
the flattening of the branch register (`MultiOracleCircuit.Program.transport`) and relabelled by
`MultiOracleCircuit.Program.substitute`, and they act on the encodings as the deferred labels
(`plainCircuit_eval`, `callCircuit_eval`). The inverse value call is a conjugated value call
(`Access.valueConj`), so a counted (value) pattern costs at most one value call and a locator
pattern none (`plainCircuit_cost`, `callCircuit_cost`): **no constant is lost**.
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open AdaptiveODELowerBound.Access (CallForm callFamily formOp ctrlOp activeEmbed)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open scoped InnerProduct

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {Kt s : ℕ}
  (F : Family X N Z Kt s)

variable {R : Type} [Fintype R] {ι : Type} [Fintype ι]

/-- The control ⊗ workspace of the call forms with branch register `J`, flattened. -/
def targetEquiv (J : Type) [Fintype J] :
    Joint Bool (Workspace J N Z Kt) ≃ₗᵢ[ℂ] Joint Bool (Joint J (Workspace Unit N Z Kt)) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun _ : Bool => accessEquiv J

omit [DecidableEq N] [AddCommGroup Z] in
/-- Coordinates of the flattened target register. -/
theorem targetEquiv_apply (J : Type) [Fintype J] (Φ : Joint Bool (Workspace J N Z Kt)) (d : Bool)
    (j : J) : targetEquiv J Φ d j = accessEquiv J (Φ d) j := rfl

/-- The call forms of the sampled-time access are those of the spectator lift. -/
theorem ctrlTarget_eq_conj (J : Type) [Fintype J] (c : Query × CallForm) (x : X) :
    ctrlTarget (F.access Unit) J c x =
      (targetEquiv J).conjStarAlgEquiv (callFamily (F.access J) c x) := by
  obtain ⟨q, f⟩ := c
  refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun d => PiLp.ext fun j => ?_
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, targetEquiv_apply]
  change callOpt (callFamily fun l x => Joint.fiber fun _ : J => F.access Unit l x)
      (some ((q, f), false)) x Ψ d j =
    accessEquiv J (callOpt (callFamily (F.access J)) (some ((q, f), false)) x
      ((targetEquiv J).symm Ψ) d) j
  rw [callOpt_callFamily_apply, callOpt_callFamily_apply, callOpt_fiber_apply,
    callOpt_access_apply, ← targetEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The counted labels of the plain shape: the value label. -/
def plainCounted : Query → Prop := fun q => q = .value

/-- The counted labels of the call shape: the call forms of the value label. -/
def callCounted : Query × CallForm → Prop := fun c => c.1 = .value

/-- Whether a label is counted in the plain shape is decidable. -/
instance : DecidablePred plainCounted := fun q => by unfold plainCounted; infer_instance

/-- Whether a call form is counted in the call shape is decidable. -/
instance : DecidablePred callCounted := fun c => by unfold callCounted; infer_instance

/-- The pattern of a deferred label of the plain shape, on `R × ι`. -/
def plainPat (c : SelLabel plainCounted R) : Pat Query (R × ι) :=
  match c with
  | .inl π => fun ri => (π ri.1).map fun lb => (lb.1.1, lb.2)
  | .inr π => fun ri => (π ri.1).map fun lb => (lb.1.1, lb.2)

/-- The pattern of a deferred label of the call shape, on `(R × Bool) × ι`. -/
def callPat (c : SelLabel callCounted R) : Pat Query ((R × Bool) × ι) :=
  match c with
  | .inl π => fun rdi => formSel ((π rdi.1.1).map fun lb => (lb.1.1, lb.2)) rdi.1.2
  | .inr π => fun rdi => formSel ((π rdi.1.1).map fun lb => (lb.1.1, lb.2)) rdi.1.2

/-- The encoding of the plain shape's deferred workspace. -/
def plainEnc (R ι : Type) [Fintype R] [Fintype ι] :
    Joint R (Workspace ι N Z Kt) →L[ℂ] Joint Bool (Workspace (R × ι) N Z Kt) :=
  (targetEquiv (R × ι)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    activeEmbed _ ∘L (plainEquiv R ι).toContinuousLinearEquiv.toContinuousLinearMap

/-- The encoding of the call shape's deferred workspace. -/
def callEnc (R ι : Type) [Fintype R] [Fintype ι] :
    Joint R (Joint Bool (Workspace ι N Z Kt)) →L[ℂ]
      Joint Bool (Workspace ((R × Bool) × ι) N Z Kt) :=
  (targetEquiv ((R × Bool) × ι)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    activeEmbed _ ∘L (callEquiv R ι).toContinuousLinearEquiv.toContinuousLinearMap

omit [DecidableEq N] [AddCommGroup Z] in
/-- The plain encoding is an isometry. -/
theorem plainEnc_isometry : (plainEnc (N := N) (Z := Z) (Kt := Kt) R ι)† ∘L plainEnc R ι = 1 :=
  comp_three_isometry _ _ _ (isoEquiv_isometry _)
    AdaptiveODELowerBound.Access.activeEmbed_isometry (isoEquiv_isometry _)

omit [DecidableEq N] [AddCommGroup Z] in
/-- The call encoding is an isometry. -/
theorem callEnc_isometry : (callEnc (N := N) (Z := Z) (Kt := Kt) R ι)† ∘L callEnc R ι = 1 :=
  comp_three_isometry _ _ _ (isoEquiv_isometry _)
    AdaptiveODELowerBound.Access.activeEmbed_isometry (isoEquiv_isometry _)

/-- A deferred label of the plain shape is a pattern of the one-branch access. -/
theorem plain_selFamily (c : SelLabel plainCounted R) (x : X) :
    (plainEquiv R ι).conjStarAlgEquiv (selFamily (F.access ι) plainCounted R c x) =
      patOp (F.access Unit) (plainPat (ι := ι) c) x := by
  rcases c with π | π
  · exact (congrArg _ (patOp_subtype _ _ π x)).trans (patOp_plain F _ x)
  · exact (congrArg _ (patOp_subtype _ _ π x)).trans (patOp_plain F _ x)

/-- A deferred label of the call shape is a pattern of the one-branch access. -/
theorem call_selFamily (c : SelLabel callCounted R) (x : X) :
    (callEquiv R ι).conjStarAlgEquiv (selFamily (callFamily (F.access ι)) callCounted R c x) =
      patOp (F.access Unit) (callPat (ι := ι) c) x := by
  rcases c with π | π
  · exact (congrArg _ (patOp_subtype _ _ π x)).trans (patOp_call F _ x)
  · exact (congrArg _ (patOp_subtype _ _ π x)).trans (patOp_call F _ x)

/-- The calls of the sampled-time access are the transported calls of the spectator lift. -/
theorem eval_query_target (J : Type) [Fintype J] (l : Query × CallForm) (x : X) :
    (MultiOracleCircuit.Program.query l :
        MultiOracleCircuit.Program (callFamily (F.access J))).eval x =
      (targetEquiv J).symm.conjStarAlgEquiv (ctrlTarget (F.access Unit) J l x) := by
  rw [MultiOracleCircuit.Program.eval_query, ctrlTarget_eq_conj,
    ← LinearIsometryEquiv.symm_conjStarAlgEquiv, StarAlgEquiv.symm_apply_apply]

/-- **The circuit of a deferred label of the plain shape** over the call forms of the
sampled-time access with branch register `R × ι`. -/
def plainCircuit (c : SelLabel plainCounted R) :
    MultiOracleCircuit.Program (callFamily (F.access (R × ι))) :=
  ((selCircuit (F.access Unit) (valueConj F) (plainPat (ι := ι) c)).transport
    (targetEquiv (R × ι)).symm).substitute fun l => .query l

/-- **The circuit of a deferred label of the call shape.** -/
def callCircuit (c : SelLabel callCounted R) :
    MultiOracleCircuit.Program (callFamily (F.access ((R × Bool) × ι))) :=
  ((selCircuit (F.access Unit) (valueConj F) (callPat (ι := ι) c)).transport
    (targetEquiv ((R × Bool) × ι)).symm).substitute fun l => .query l

/-- The plain circuits act on the encoding as the deferred labels. -/
theorem plainCircuit_eval (c : SelLabel plainCounted R) (x : X) :
    (plainCircuit F (ι := ι) c).eval x ∘L plainEnc R ι =
      plainEnc R ι ∘L selFamily (F.access ι) plainCounted R c x := by
  rw [plainCircuit, MultiOracleCircuit.Program.eval_substitute _ _ (eval_query_target F _),
    MultiOracleCircuit.Program.eval_transport]
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 := DFunLike.congr_fun (plain_selFamily F c x) (plainEquiv R ι v)
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] at h2
  have h1 := DFunLike.congr_fun (selCircuit_eval (valueConj F) (plainPat (ι := ι) c) x)
    (plainEquiv R ι v)
  rw [comp_apply, comp_apply] at h1
  change (targetEquiv (R × ι)).symm ((selCircuit (F.access Unit) (valueConj F)
      (plainPat (ι := ι) c)).eval x ((targetEquiv (R × ι)).symm.symm ((targetEquiv (R × ι)).symm
        (activeEmbed _ (plainEquiv R ι v))))) =
    (targetEquiv (R × ι)).symm (activeEmbed _
      (plainEquiv R ι (selFamily (F.access ι) plainCounted R c x v)))
  rw [LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply, h1, h2]

set_option maxRecDepth 4096 in
/-- The call circuits act on the encoding as the deferred labels. -/
theorem callCircuit_eval (c : SelLabel callCounted R) (x : X) :
    (callCircuit F (ι := ι) c).eval x ∘L callEnc R ι =
      callEnc R ι ∘L selFamily (callFamily (F.access ι)) callCounted R c x := by
  rw [callCircuit, MultiOracleCircuit.Program.eval_substitute _ _ (eval_query_target F _),
    MultiOracleCircuit.Program.eval_transport]
  refine ContinuousLinearMap.ext fun v => ?_
  have h2 := DFunLike.congr_fun (call_selFamily F c x) (callEquiv R ι v)
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply] at h2
  have h1 := DFunLike.congr_fun (selCircuit_eval (valueConj F) (callPat (ι := ι) c) x)
    (callEquiv R ι v)
  rw [comp_apply, comp_apply] at h1
  change (targetEquiv ((R × Bool) × ι)).symm ((selCircuit (F.access Unit) (valueConj F)
      (callPat (ι := ι) c)).eval x ((targetEquiv ((R × Bool) × ι)).symm.symm
        ((targetEquiv ((R × Bool) × ι)).symm (activeEmbed _ (callEquiv R ι v))))) =
    (targetEquiv ((R × Bool) × ι)).symm (activeEmbed _
      (callEquiv R ι (selFamily (callFamily (F.access ι)) callCounted R c x v)))
  rw [LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply, h1, h2]

/-- A call of `formSel` names the label of its call form. -/
theorem formSel_eq_some {c : Option ((Query × CallForm) × Bool)} {d : Bool} {q : Query}
    {b : Bool} (h : formSel c d = some (q, b)) : ∃ f b', c = some ((q, f), b') := by
  rcases c with _ | ⟨⟨q', f⟩, b'⟩
  · simp [formSel] at h
  · refine ⟨f, b', ?_⟩
    have hq : q' = q := by
      cases f <;> cases d <;> simp [formSel] at h <;> exact h.1
    rw [hq]

/-- The weighted value count of a pattern circuit is its value `dirCount`. -/
theorem selCircuit_cost_value {J' : Type} [Fintype J'] (σ : Pat Query J') :
    (selCircuit (F.access Unit) (valueConj F) σ).cost (fun c => valueWeight c.1) ≤
      dirCount (valueConj F) σ .value := by
  refine (selCircuit_cost (F.access Unit) (valueConj F) σ valueWeight).trans ?_
  rw [Fintype.sum_eq_single Query.value (fun q hq => by cases q <;> simp_all [valueWeight])]
  simp [valueWeight]

/-- **A counted plain pattern costs at most one value call, an uncounted one none.** -/
theorem plainCircuit_cost (c : SelLabel plainCounted R) :
    (plainCircuit F (ι := ι) c).cost (fun c' => valueWeight c'.1) ≤ selWeight c := by
  rw [plainCircuit, MultiOracleCircuit.Program.cost_substitute,
    MultiOracleCircuit.Program.cost_transport]
  refine (selCircuit_cost_value F (plainPat (ι := ι) c)).trans ?_
  rcases c with π | π
  · exact dirCount_le_one (valueConj F) _ Query.value rfl
  · refine (dirCount_eq_zero (valueConj F) _ Query.value fun j b h => ?_).le
    obtain ⟨⟨⟨l, hl⟩, b'⟩, -, he⟩ := Option.map_eq_some_iff.mp h
    exact hl (congrArg Prod.fst he)

/-- **A counted call-shape pattern costs at most one value call, an uncounted one none.** -/
theorem callCircuit_cost (c : SelLabel callCounted R) :
    (callCircuit F (ι := ι) c).cost (fun c' => valueWeight c'.1) ≤ selWeight c := by
  rw [callCircuit, MultiOracleCircuit.Program.cost_substitute,
    MultiOracleCircuit.Program.cost_transport]
  refine (selCircuit_cost_value F (callPat (ι := ι) c)).trans ?_
  rcases c with π | π
  · exact dirCount_le_one (valueConj F) _ Query.value rfl
  · refine (dirCount_eq_zero (valueConj F) _ Query.value fun j b h => ?_).le
    obtain ⟨f, b', he⟩ := formSel_eq_some h
    obtain ⟨⟨⟨l, hl⟩, b''⟩, -, he'⟩ := Option.map_eq_some_iff.mp he
    exact hl (congrArg (fun p : (Query × CallForm) × Bool => p.1.1) he')

end

end DeferredMeasurementLowerBounds.Access
