import GateEfficientODE.Circuit.Counts

/-!
# The trial circuits and the actual Grover trials

On configurations with clean work wires the preparation circuit agrees with

`Wideal = SP† LP† PH SEL LD LP SP`,

where `SP` is the exact source-label rotation tree, `LP` the ideal LCHS
label tree, `PH` the ideal coefficient phases, `LD` the two source calls and
`SEL` the embedded released simulator (`prepC_agrees`).  The reflections
agree with the ideal reflections about the clean outputs and about the seed
state, so one step agrees with the released signed Grover step
`ODEGroverProgram.operator` of the *actual* preparation unitary
(`stepC_agrees`).  Consequently the actual trial with `j` steps applied to
the seed state is exactly the released actual Grover trial
`ODEGroverActual.trial` of the actual preparation (`trialC_seed`), and its
clean decoded vector is `outMap† (SEL (inMap v))` (`decoded_prepC`).
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective simCircuit)
open scoped InnerProduct BigOperators

/-! ### Generic facts -/

section Generic

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

theorem pres2_treeFrom {q : ℕ} (S : Cfg W → Prop) (ts : Fin q → W)
    (M : Fin q → Cfg W → Matrix Bool Bool ℂ) (hS : ∀ x i b, S x → S (Function.update x (ts i) b))
    (k : ℕ) (hk : k ≤ q) : Pres2 S (treeFrom (Q := Q) ts M k hk) := by
  induction k with
  | zero => exact pres2_one S
  | succ k ih =>
      rw [treeFrom]
      exact (ih (by omega)).comp (pres2_condOp S _ _ (fun x b hx => hS x _ b hx))

theorem treeFrom_isUnitary {q : ℕ} (ts : Fin q → W) (M : Fin q → Cfg W → Matrix Bool Bool ℂ)
    (hM : ∀ s x, UnitaryMat (M s x)) (k : ℕ) (hk : k ≤ q) :
    IsUnitary (treeFrom (Q := Q) ts M k hk) := by
  induction k with
  | zero => exact isUnitary_one
  | succ k ih =>
      rw [treeFrom]
      exact isUnitary_comp (ih (by omega)) (condOp_isUnitary _ _ (fun x => hM _ x))

theorem gateOp_neg_one (t : W) : gateOp (Q := Q) [] t (-1) = -1 := by
  ext ψ x
  rw [gateOp_apply [] t (-1) (by simp) ψ x, if_pos (ctrlOK_nil x)]
  rw [Finset.sum_eq_single (x t)]
  · simp
  · intro b _ hb
    simp [Matrix.neg_apply, Ne.symm hb]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
/-- Agreement through a change of the clean predicate. -/
theorem Agrees.comp' {S₁ S₂ : Cfg W → Prop} {C₁ C₂ O₁ O₂ : Reg W Q →L[ℂ] Reg W Q}
    (h₁ : Agrees S₁ C₁ O₁) (hO₁ : ∀ ψ, Supp S₁ ψ → Supp S₂ (O₁ ψ)) (h₂ : Agrees S₂ C₂ O₂) :
    Agrees S₁ (C₂ ∘L C₁) (O₂ ∘L O₁) := by
  intro ψ hψ
  rw [comp_apply, comp_apply, h₁ ψ hψ, h₂ _ (hO₁ ψ hψ)]

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
/-- An operator agreeing with an invariant one is invariant. -/
theorem Preserves.of_agrees {S : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q}
    (h : Agrees S C O) (hO : Preserves S O) : Preserves S C := by
  intro ψ hψ
  rw [h ψ hψ]
  exact hO ψ hψ

theorem projector_map (U : Reg W Q →L[ℂ] Reg W Q) (ψ : Reg W Q) :
    ODEGroverRay.projector (U ψ) = U * ODEGroverRay.projector ψ * star U := by
  ext φ
  rw [ODEGroverRay.projector_apply, mul_apply_eq_comp, mul_apply_eq_comp, ODEGroverRay.projector_apply,
    map_smul, star_eq_adjoint, adjoint_inner_right]

end Generic

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Clean configurations of the solver -/

section Clean

variable {a m r K k l f : ℕ}

theorem workClean_update_inl (x : Cfg (AW a m r K k l f)) (s : Wire a m r K) (b : Bool)
    (hx : WorkClean x) : WorkClean (Function.update x (Sum.inl s) b) := by
  intro o ho
  rw [Function.update_of_ne (by simp)]
  exact hx o ho

theorem workClean_update_inr (x : Cfg (AW a m r K k l f)) (o : OWire k l f) (ho : o.isWork = false)
    (b : Bool) (hx : WorkClean x) : WorkClean (Function.update x (Sum.inr o) b) := by
  intro o' ho'
  rw [Function.update_of_ne]
  · exact hx o' ho'
  · intro h
    cases h
    rw [ho] at ho'
    cases ho'

theorem workClean_overwrite_inl (y : Cfg (AW a m r K k l f)) (b : Cfg (Wire a m r K))
    (hy : WorkClean y) : WorkClean (overwrite Sum.inl y b) := by
  intro o ho
  rw [overwrite_apply_out Sum.inl y b _ (fun s h => by cases h)]
  exact hy o ho

theorem pres2_localOp_inl (F : Cfg (AW a m r K k l f) → (Reg (Wire a m r K) P →L[ℂ]
    Reg (Wire a m r K) P)) :
    Pres2 WorkClean (localOp Sum.inl Sum.inl_injective F) :=
  pres2_localOp WorkClean Sum.inl Sum.inl_injective F
    (fun y b hy => workClean_overwrite_inl y b hy)

/-- Every simulator instruction keeps the work wires of the solver clean. -/
theorem pres2_run_select {Λ : Type*} (ω : Wiring (Wire a m r K) (OWire k l f) a Λ P)
    (σ : Oracles a Λ P) (gs : List (Instr (Wire a m r K))) :
    Pres2 WorkClean (run ω σ (gs.map (embI (O := OWire k l f)))) := by
  rw [run_map_embI]
  exact pres2_localOp_inl _

theorem srcTS_stable (x : Cfg (AW a m r K k l f)) (i : Fin (k + 1)) (b : Bool)
    (hx : WorkClean x) : WorkClean (Function.update x (srcTS i) b) := by
  cases i using Fin.cases with
  | zero => exact workClean_update_inr x _ rfl b hx
  | succ i => exact workClean_update_inr x _ rfl b hx

theorem lchTS_stable (x : Cfg (AW a m r K k l f)) (i : Fin l) (b : Bool) (hx : WorkClean x) :
    WorkClean (Function.update x (lchTS i) b) :=
  workClean_update_inr x _ rfl b hx

end Clean

namespace Params

variable (p : Params)

/-! ### The ideal operators -/

/-- The exact source-label rotations. -/
def SP : Reg p.W P →L[ℂ] Reg p.W P := treeFrom srcTS (fun s _ => p.srcMat s) (p.k + 1) le_rfl

/-- The ideal LCHS label tree. -/
def LP : Reg p.W P →L[ℂ] Reg p.W P := treeOp lchTS (treeSel lchTS p.lchAmp)

/-- The ideal coefficient phases. -/
def PH : Reg p.W P →L[ℂ] Reg p.W P :=
  phaseOp lchTS p.l_pos (fun w => ODECoherentLCU.coefficientPhase (p.coeffW w))

/-- The actual preparation, written with the ideal label operations. -/
def Wideal (v : P) (σ : Oracles p.a (Label p.k p.l) P) : Reg p.W P →L[ℂ] Reg p.W P :=
  p.SP† ∘L p.LP† ∘L p.PH ∘L run (wiring v) σ p.select ∘L run (wiring v) σ p.load ∘L p.LP ∘L p.SP

theorem run_srcPrep (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    run (wiring v) σ (ofGates p.srcPrep) = p.SP := by
  rw [run_ofGates]
  exact gRun_constT _ _ _ le_rfl

theorem pres2_SP : Pres2 WorkClean (p.SP (P := P)) :=
  pres2_treeFrom WorkClean srcTS _ srcTS_stable _ _

theorem pres2_LP : Pres2 WorkClean (p.LP (P := P)) :=
  pres2_treeFrom WorkClean lchTS _ lchTS_stable _ _

theorem pres2_PH : Pres2 WorkClean (p.PH (P := P)) := by
  unfold PH phaseOp
  exact pres2_condOp WorkClean _ _ (fun x b hx => lchTS_stable x _ b hx)

theorem SP_isUnitary (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B) :
    IsUnitary (p.SP (P := P)) :=
  treeFrom_isUnitary _ _ (fun s _ => p.srcMat_unitary hr₀ hrb hT hB s) _ _

theorem LP_isUnitary : IsUnitary (p.LP (P := P)) :=
  treeFrom_isUnitary _ _ (fun s _ => treeMat_unitary _ s _) _ _

theorem PH_isUnitary : IsUnitary (p.PH (P := P)) := by
  unfold PH phaseOp
  exact condOp_isUnitary _ _ (fun x => phaseMat_unitary p.l_pos _
    (fun w => ODECoherentLCU.norm_coefficientPhase _) _)

theorem pres2_load (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Pres2 WorkClean (run (wiring v) σ p.load) := by
  rw [load, run_cons, run_singleton, OInstr.eval_src, OInstr.eval_src]
  exact (pres2_pctl _ _ _).comp (pres2_pctl _ _ _)

theorem lchPrep_agrees (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Agrees WorkClean (run (wiring v) σ (ofGates p.lchPrep)) (p.LP (P := P)) := by
  rw [run_ofGates]
  exact prepT_agrees _ WorkClean (lchTree_ok p.l_le_pool) _ _ le_rfl

theorem lchPhase_agrees (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Agrees WorkClean (run (wiring v) σ (ofGates p.lchPhase)) (p.PH (P := P)) := by
  rw [run_ofGates]
  unfold lchPhase PH
  exact phaseT_agrees lchTree WorkClean (lchTree_ok p.l_le_pool) p.l_pos _

/-- **The preparation agrees with its ideal form on clean work wires.** -/
theorem prepC_agrees (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Agrees WorkClean (run (wiring v) σ p.prepC) (p.Wideal v σ) := by
  have hLPu : IsUnitary (run (wiring v) σ (ofGates p.lchPrep)) := by
    rw [run_ofGates]
    exact gRun_isUnitary _ (fun g hg => (prepT_ok _ lchTS_injective poolList_nodup
      (lchTree_ok p.l_le_pool).disj _ _ g hg).2.2)
  have hA1 : Agrees WorkClean (run (wiring v) σ (ofGates p.srcPrep)) p.SP := by
    rw [p.run_srcPrep v σ]; exact Agrees.refl _ _
  have hA2 := p.lchPrep_agrees v σ
  have hA5 := p.lchPhase_agrees v σ
  have hA6 : Agrees WorkClean (run (wiring v) σ (invList (ofGates p.lchPrep))) (p.LP†) := by
    rw [run_invList]
    exact hA2.adjoint hLPu p.LP_isUnitary p.pres2_LP.2
  have hA7 : Agrees WorkClean (run (wiring v) σ (invList (ofGates p.srcPrep))) (p.SP†) := by
    rw [run_invList, p.run_srcPrep v σ]; exact Agrees.refl _ _
  have pSP : Preserves WorkClean (p.SP (P := P)) := p.pres2_SP.1
  have pLP : Preserves WorkClean (p.LP (P := P)) := p.pres2_LP.1
  have pLD : Preserves WorkClean (run (wiring v) σ p.load) := (p.pres2_load v σ).1
  have pSEL : Preserves WorkClean (run (wiring v) σ p.select) :=
    (pres2_run_select (wiring v) σ (simCircuit p.a p.tau p.Q p.qbar p.nu)).1
  have pPH : Preserves WorkClean (p.PH (P := P)) := p.pres2_PH.1
  have pLPa : Preserves WorkClean ((p.LP (P := P))†) := p.pres2_LP.2
  have c2 := pSP.comp pLP
  have c3 := c2.comp pLD
  have c4 := c3.comp pSEL
  have c5 := c4.comp pPH
  have c6 := c5.comp pLPa
  have h12 := hA1.comp pSP hA2
  have h123 := h12.comp c2 (Agrees.refl WorkClean (run (wiring v) σ p.load))
  have h1234 := h123.comp c3 (Agrees.refl WorkClean (run (wiring v) σ p.select))
  have h5 := h1234.comp c4 hA5
  have h6 := h5.comp c5 hA6
  have h7 := h6.comp c6 hA7
  have e : run (wiring v) σ p.prepC =
      run (wiring v) σ (invList (ofGates p.srcPrep)) ∘L
        (run (wiring v) σ (invList (ofGates p.lchPrep)) ∘L
        (run (wiring v) σ (ofGates p.lchPhase) ∘L (run (wiring v) σ p.select ∘L
        (run (wiring v) σ p.load ∘L (run (wiring v) σ (ofGates p.lchPrep) ∘L
        run (wiring v) σ (ofGates p.srcPrep)))))) := by
    unfold prepC
    simp only [run_append, comp_assoc]
  rw [e]
  exact h7

theorem pres2_Wideal (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Pres2 WorkClean (p.Wideal v σ) := by
  unfold Wideal
  exact p.pres2_SP.adj.comp (p.pres2_LP.adj.comp (p.pres2_PH.comp
    ((pres2_run_select (wiring v) σ _).comp ((p.pres2_load v σ).comp (p.pres2_LP.comp p.pres2_SP)))))

/-- The hypotheses making every supplied operation unitary. -/
structure Unitaries (v : P) (σ : Oracles p.a (Label p.k p.l) P) : Prop where
  seed : ‖v‖ = 1
  uj : IsUnitary σ.UJ
  priv : ∀ z, IsUnitary (σ.D z)
  src : ∀ b, IsUnitary (σ.J b)

theorem prepC_isUnitary (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (v : P) (σ : Oracles p.a (Label p.k p.l) P)
    (hU : p.Unitaries v σ) : IsUnitary (run (wiring v) σ p.prepC) :=
  run_isUnitary _ _ hU.uj hU.priv hU.src hU.seed _ (p.prepC_valid hτ hν hr₀ hrb hT hB)

theorem Wideal_isUnitary (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (v : P) (σ : Oracles p.a (Label p.k p.l) P)
    (hU : p.Unitaries v σ) : IsUnitary (p.Wideal v σ) := by
  have hsel : IsUnitary (run (wiring v) σ p.select) :=
    run_isUnitary _ _ hU.uj hU.priv hU.src hU.seed _ (fun g hg =>
      p.prepC_valid hτ hν hr₀ hrb hT hB g (by simp [prepC, hg]))
  have hload : IsUnitary (run (wiring v) σ p.load) :=
    run_isUnitary _ _ hU.uj hU.priv hU.src hU.seed _ (fun g hg =>
      p.prepC_valid hτ hν hr₀ hrb hT hB g (by simp [prepC, hg]))
  have hSP := p.SP_isUnitary (P := P) hr₀ hrb hT hB
  unfold Wideal
  exact isUnitary_comp (isUnitary_adj hSP) (isUnitary_comp (isUnitary_adj p.LP_isUnitary)
    (isUnitary_comp p.PH_isUnitary (isUnitary_comp hsel (isUnitary_comp hload
      (isUnitary_comp p.LP_isUnitary hSP)))))

theorem pres2_prepC (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (v : P) (σ : Oracles p.a (Label p.k p.l) P)
    (hU : p.Unitaries v σ) : Pres2 WorkClean (run (wiring v) σ p.prepC) := by
  have h := p.prepC_agrees v σ
  have hW := p.pres2_Wideal v σ
  refine ⟨Preserves.of_agrees h hW.1, ?_⟩
  exact Preserves.of_agrees (h.adjoint (p.prepC_isUnitary hτ hν hr₀ hrb hT hB v σ hU)
    (p.Wideal_isUnitary hτ hν hr₀ hrb hT hB v σ hU) hW.2) hW.2

/-! ### One step and the trials -/

/-- The released signed Grover step of the actual preparation. -/
def groverStep (v : P) (σ : Oracles p.a (Label p.k p.l) P) : Reg p.W P →L[ℂ] Reg p.W P :=
  ODEGroverProgram.operator (run (wiring v) σ p.prepC) (ODEGroverRay.projector (seedState v))
    (ODEHeraldedSuccess.successProjector goodF)

theorem stepC_agrees (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (v : P) (σ : Oracles p.a (Label p.k p.l) P)
    (hU : p.Unitaries v σ) :
    Agrees WorkClean (run (wiring v) σ p.stepC) (p.groverStep v σ) := by
  have hW := p.pres2_prepC hτ hν hr₀ hrb hT hB v σ hU
  have hg : Agrees WorkClean (run (wiring v) σ (ofGates (S := Wire p.a p.m p.r p.K)
      (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f))))
      rgoodI := by
    rw [run_ofGates]; exact rgood_agrees p.zero_test_le
  have hs := rseed_agrees (a := p.a) (m := p.m) (r := p.r) (K := p.K) p.zero_test_le v σ
  unfold stepC groverStep ODEGroverProgram.operator
  simp only [run_append, run_invList, run_singleton, OInstr.eval_gate, negGate,
    gateOp_neg_one]
  have h1 := hg.comp pres2_rgoodI.1 (Agrees.refl WorkClean ((run (wiring v) σ p.prepC)†))
  have h2 := h1.comp (pres2_rgoodI.1.comp hW.2) hs
  have h3 := h2.comp (((pres2_rgoodI.1).comp hW.2).comp (pres2_rseedI v).1)
    (Agrees.refl WorkClean (run (wiring v) σ p.prepC))
  have h4 := h3.comp ((((pres2_rgoodI.1).comp hW.2).comp (pres2_rseedI v).1).comp hW.1)
    (Agrees.refl WorkClean (-1))
  intro ψ hψ
  rw [h4 ψ hψ]
  simp only [comp_apply, neg_apply, one_apply_eq_self, mul_apply_eq_comp, rgoodI, rseedI,
    star_eq_adjoint]

theorem pres_groverStep (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (v : P) (σ : Oracles p.a (Label p.k p.l) P)
    (hU : p.Unitaries v σ) : Preserves WorkClean (p.groverStep v σ) := by
  have hW := p.pres2_prepC hτ hν hr₀ hrb hT hB v σ hU
  have hpre : Preserves WorkClean (-(run (wiring v) σ p.prepC ∘L rseedI v ∘L
      (run (wiring v) σ p.prepC)† ∘L rgoodI)) :=
    preserves_neg ((((pres2_rgoodI.1).comp hW.2).comp (pres2_rseedI v).1).comp hW.1)
  intro ψ hψ
  have e : p.groverStep v σ ψ = (-(run (wiring v) σ p.prepC ∘L rseedI v ∘L
      (run (wiring v) σ p.prepC)† ∘L rgoodI)) ψ := by
    simp only [groverStep, ODEGroverProgram.operator, neg_apply, mul_apply_eq_comp, comp_apply, rgoodI,
      rseedI, star_eq_adjoint]
  rw [e]
  exact hpre ψ hψ

theorem steps_agree (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (v : P) (σ : Oracles p.a (Label p.k p.l) P)
    (hU : p.Unitaries v σ) (j : ℕ) (φ : Reg p.W P) (hφ : Supp WorkClean φ) :
    run (wiring v) σ (List.replicate j p.stepC).flatten φ = (p.groverStep v σ ^ j) φ := by
  induction j generalizing φ with
  | zero => rfl
  | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, run_append, comp_apply,
        p.stepC_agrees hτ hν hr₀ hrb hT hB v σ hU φ hφ,
        ih _ (p.pres_groverStep hτ hν hr₀ hrb hT hB v σ hU φ hφ), pow_succ, mul_apply_eq_comp]

/-- **The actual trial is the released actual Grover trial of the actual
preparation unitary.** -/
theorem trialC_seed (hτ : 0 ≤ p.tau) (hν : 0 < p.nu) (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb)
    (hT : 0 ≤ p.T) (hB : 0 < p.B) (v : P) (σ : Oracles p.a (Label p.k p.l) P)
    (hU : p.Unitaries v σ) (j : ℕ) :
    run (wiring v) σ (p.trialC j) (seedState v) =
      ODEGroverActual.trial goodF (run (wiring v) σ p.prepC) (seedState v) j := by
  have hW := p.pres2_prepC hτ hν hr₀ hrb hT hB v σ hU
  have hseed : Supp WorkClean (seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k)
      (l := p.l) (f := p.f) v) := supp_bas _ workClean_zero _
  rw [trialC, run_append, comp_apply,
    p.steps_agree hτ hν hr₀ hrb hT hB v σ hU j _ (hW.1 _ hseed)]
  unfold ODEGroverActual.trial ODEGroverActual.actualG
  congr 2
  rw [groverStep, ODEGroverProgram.operator_eq_grover _ _ _
    (p.prepC_isUnitary hτ hν hr₀ hrb hT hB v σ hU), ← projector_map]

/-! ### The decoded vector -/

/-- The ideal input map: source and LCHS label preparation and loading. -/
def inMap (v : P) (σ : Oracles p.a (Label p.k p.l) P) : P →L[ℂ] Reg p.W P :=
  run (wiring v) σ p.load ∘L p.LP ∘L p.SP ∘L goodF

/-- The ideal output map: label preparation with conjugate phases. -/
def outMap : P →L[ℂ] Reg p.W P := p.PH† ∘L p.LP ∘L p.SP ∘L goodF

/-- **The clean decoded vector of the actual preparation.** -/
theorem decoded_prepC (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    ODEHeraldedSuccess.decoded goodF (run (wiring v) σ p.prepC) (seedState v) =
      (p.outMap†) (run (wiring v) σ p.select (p.inMap v σ v)) := by
  have hseed : Supp WorkClean (seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k)
      (l := p.l) (f := p.f) v) := supp_bas _ workClean_zero _
  rw [ODEHeraldedSuccess.decoded, p.prepC_agrees v σ _ hseed]
  have hs : seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l)
      (f := p.f) v = goodF v := by
    rw [seedState, goodF, basL_apply]
  rw [hs]
  simp only [Wideal, outMap, inMap, comp_apply, adjoint_comp, adjoint_adjoint]

end Params

end

end SparseHamiltonian.GateODE
