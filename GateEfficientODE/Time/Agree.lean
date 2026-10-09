import GateEfficientODE.Time.Counts
import GateEfficientODE.Circuit.Agree

/-!
# The time-dependent trial circuits and the actual Grover trials

On configurations with clean work wires the preparation circuit agrees with

`Wideal = WP† LP† PH SEL LD LP WP`,

where `WP` is the supplied weight preparation, `LP` the ideal LCHS label tree,
`PH` the ideal coefficient phases, `LD` the coherent source loading and
`SEL` the embedded slot-selected simulator (`prepC_agrees`).  The
reflections are those of the constant-coefficient solver (`trun_eq_run`), so
one step agrees with the released signed Grover step of the *actual*
preparation unitary (`stepC_agrees`), the actual trial with `j` steps applied
to the seed state is the released actual Grover trial (`trialC_seed`), and
its clean decoded vector is `outMap† (SEL (inMap v))` (`decoded_prepC`).
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Clean configurations -/

section Clean

variable {a m r K k l f : ℕ}

theorem workClean_overwrite_src (y : Cfg (AW a m r K k l f)) (b : Cfg (Fin (k + 1)))
    (hy : WorkClean y) : WorkClean (overwrite srcTS y b) := by
  intro o ho
  rw [overwrite_apply_out srcTS y b _ (fun i h => by
    cases i using Fin.cases <;> cases o <;> simp_all [srcTS, OWire.isWork])]
  exact hy o ho

theorem pres2_wprep (σ : TOracles a k l P) (adj : Bool) :
    Pres2 WorkClean (wprep (m := m) (r := r) (K := K) (f := f) σ adj) :=
  pres2_localOp WorkClean srcTS srcTS_injective _
    (fun y b hy => workClean_overwrite_src y b hy)

/-- Every embedded simulator instruction keeps the work wires clean. -/
theorem pres2_trun_select (v : P) (σ : TOracles a k l P) (gs : List (Instr (Wire a m r K))) :
    Pres2 WorkClean (trun v σ (gs.map (embI (O := OWire k l f)))) := by
  rw [trun_map_embI]
  exact pres2_localOp_inl _

/-- Some constant-coefficient oracles, used to transfer the reflections. -/
def oracles₁ (σ : TOracles a k l P) : Oracles a (Label k l) P := ⟨σ.UJ, fun _ => 1, fun _ => 1⟩

theorem rseedT_agrees (hf : Fintype.card (Wire a m r K) + k + l ≤ f) (v : P)
    (σ : TOracles a k l P) :
    Agrees WorkClean (trun v σ (rseedC (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
      (f := f))) (rseedI v) := by
  rw [trun_eq_run v σ (oracles₁ σ)]
  · exact rseed_agrees hf v (oracles₁ σ)
  · intro g hg
    simp only [rseedC, ofGates, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    rcases hg with (⟨g', _, rfl⟩ | rfl) | ⟨g', _, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

end Clean

namespace TParams

variable (p : TParams)

/-! ### The ideal operators -/

/-- The ideal LCHS label tree. -/
def LP : Reg p.W P →L[ℂ] Reg p.W P := treeOp lchTS (treeSel lchTS p.lchAmp)

/-- The ideal coefficient phases. -/
def PH : Reg p.W P →L[ℂ] Reg p.W P :=
  phaseOp lchTS p.l_pos (fun w => ODECoherentLCU.coefficientPhase (p.coeffW w))

/-- The supplied weight preparation on the source label. -/
def WP (σ : TOracles p.a p.m p.l P) : Reg p.W P →L[ℂ] Reg p.W P := wprep σ false

/-- The actual preparation, written with the ideal label operations. -/
def Wideal (v : P) (σ : TOracles p.a p.m p.l P) : Reg p.W P →L[ℂ] Reg p.W P :=
  (p.WP σ)† ∘L p.LP† ∘L p.PH ∘L trun v σ p.select ∘L trun v σ p.load ∘L p.LP ∘L p.WP σ

theorem pres2_LP : Pres2 WorkClean (p.LP (P := P)) :=
  pres2_treeFrom WorkClean lchTS _ lchTS_stable _ _

theorem pres2_PH : Pres2 WorkClean (p.PH (P := P)) := by
  unfold PH phaseOp
  exact pres2_condOp WorkClean _ _ (fun x b hx => lchTS_stable x _ b hx)

theorem LP_isUnitary : IsUnitary (p.LP (P := P)) :=
  treeFrom_isUnitary _ _ (fun s _ => treeMat_unitary _ s _) _ _

theorem PH_isUnitary : IsUnitary (p.PH (P := P)) := by
  unfold PH phaseOp
  exact condOp_isUnitary _ _ (fun x => phaseMat_unitary p.l_pos _
    (fun w => ODECoherentLCU.norm_coefficientPhase _) _)

theorem pres2_load (v : P) (σ : TOracles p.a p.m p.l P) :
    Pres2 WorkClean (trun v σ p.load) := by
  rw [load, trun_singleton, teval_load]
  exact pres2_psel _ _

theorem run_wprepC (v : P) (σ : TOracles p.a p.m p.l P) : trun v σ p.wprepC = p.WP σ := by
  rw [wprepC, trun_singleton, teval_wprep]
  rfl

theorem lchPrep_agrees (v : P) (σ : TOracles p.a p.m p.l P) :
    Agrees WorkClean (trun v σ (ofGates p.lchPrep)) (p.LP (P := P)) := by
  rw [trun_ofGates]
  exact prepT_agrees _ WorkClean (lchTree_ok p.l_le_pool) _ _ le_rfl

theorem lchPhase_agrees (v : P) (σ : TOracles p.a p.m p.l P) :
    Agrees WorkClean (trun v σ (ofGates p.lchPhase)) (p.PH (P := P)) := by
  rw [trun_ofGates]
  unfold lchPhase PH
  exact phaseT_agrees lchTree WorkClean (lchTree_ok p.l_le_pool) p.l_pos _

/-- **The preparation agrees with its ideal form on clean work wires.** -/
theorem prepC_agrees (v : P) (σ : TOracles p.a p.m p.l P) :
    Agrees WorkClean (trun v σ p.prepC) (p.Wideal v σ) := by
  have hLPu : IsUnitary (trun v σ (ofGates p.lchPrep)) := by
    rw [trun_ofGates]
    exact gRun_isUnitary _ (fun g hg => (prepT_ok _ lchTS_injective poolList_nodup
      (lchTree_ok p.l_le_pool).disj _ _ g hg).2.2)
  have hA1 : Agrees WorkClean (trun v σ p.wprepC) (p.WP σ) := by
    rw [p.run_wprepC v σ]; exact Agrees.refl _ _
  have hA2 := p.lchPrep_agrees v σ
  have hA5 := p.lchPhase_agrees v σ
  have hA6 : Agrees WorkClean (trun v σ (invList (ofGates p.lchPrep))) (p.LP†) := by
    rw [trun_invList]
    exact hA2.adjoint hLPu p.LP_isUnitary p.pres2_LP.2
  have hA7 : Agrees WorkClean (trun v σ (invList p.wprepC)) ((p.WP σ)†) := by
    rw [trun_invList, p.run_wprepC v σ]; exact Agrees.refl _ _
  have pWP : Preserves WorkClean (p.WP σ) := (pres2_wprep σ false).1
  have pLP : Preserves WorkClean (p.LP (P := P)) := p.pres2_LP.1
  have pLD : Preserves WorkClean (trun v σ p.load) := (p.pres2_load v σ).1
  have pSEL : Preserves WorkClean (trun v σ p.select) :=
    (pres2_trun_select v σ (SlotSim.simCircuitT p.a p.tau p.Q p.qbar p.nu p.m)).1
  have pPH : Preserves WorkClean (p.PH (P := P)) := p.pres2_PH.1
  have pLPa : Preserves WorkClean ((p.LP (P := P))†) := p.pres2_LP.2
  have c2 := pWP.comp pLP
  have c3 := c2.comp pLD
  have c4 := c3.comp pSEL
  have c5 := c4.comp pPH
  have c6 := c5.comp pLPa
  have h12 := hA1.comp pWP hA2
  have h123 := h12.comp c2 (Agrees.refl WorkClean (trun v σ p.load))
  have h1234 := h123.comp c3 (Agrees.refl WorkClean (trun v σ p.select))
  have h5 := h1234.comp c4 hA5
  have h6 := h5.comp c5 hA6
  have h7 := h6.comp c6 hA7
  have e : trun v σ p.prepC =
      trun v σ (invList p.wprepC) ∘L
        (trun v σ (invList (ofGates p.lchPrep)) ∘L
        (trun v σ (ofGates p.lchPhase) ∘L (trun v σ p.select ∘L
        (trun v σ p.load ∘L (trun v σ (ofGates p.lchPrep) ∘L
        trun v σ p.wprepC))))) := by
    unfold prepC
    simp only [trun_append, comp_assoc]
  rw [e]
  exact h7

theorem pres2_Wideal (v : P) (σ : TOracles p.a p.m p.l P) :
    Pres2 WorkClean (p.Wideal v σ) := by
  unfold Wideal
  exact (pres2_wprep σ false).adj.comp (p.pres2_LP.adj.comp (p.pres2_PH.comp
    ((pres2_trun_select v σ _).comp ((p.pres2_load v σ).comp (p.pres2_LP.comp
      (pres2_wprep σ false))))))

theorem prepC_isUnitary (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (hσ : σ.Unitary p.m) : IsUnitary (trun v σ p.prepC) :=
  trun_isUnitary v σ hσ hv _ (p.prepC_valid hτ hν hm)

theorem Wideal_isUnitary (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (hσ : σ.Unitary p.m) : IsUnitary (p.Wideal v σ) := by
  have hsel : IsUnitary (trun v σ p.select) :=
    trun_isUnitary v σ hσ hv _ (fun g hg => p.prepC_valid hτ hν hm g (by simp [prepC, hg]))
  have hload : IsUnitary (trun v σ p.load) :=
    trun_isUnitary v σ hσ hv _ (fun g hg => p.prepC_valid hτ hν hm g (by simp [prepC, hg]))
  have hWP : IsUnitary (p.WP σ) := wprep_isUnitary σ hσ false
  unfold Wideal
  exact isUnitary_comp (isUnitary_adj hWP) (isUnitary_comp (isUnitary_adj p.LP_isUnitary)
    (isUnitary_comp p.PH_isUnitary (isUnitary_comp hsel (isUnitary_comp hload
      (isUnitary_comp p.LP_isUnitary hWP)))))

theorem pres2_prepC (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (hσ : σ.Unitary p.m) : Pres2 WorkClean (trun v σ p.prepC) := by
  have h := p.prepC_agrees v σ
  have hW := p.pres2_Wideal v σ
  refine ⟨Preserves.of_agrees h hW.1, ?_⟩
  exact Preserves.of_agrees (h.adjoint (p.prepC_isUnitary hτ hν hm v hv σ hσ)
    (p.Wideal_isUnitary hτ hν hm v hv σ hσ) hW.2) hW.2

/-! ### One step and the trials -/

/-- The released signed Grover step of the actual preparation. -/
def groverStep (v : P) (σ : TOracles p.a p.m p.l P) : Reg p.W P →L[ℂ] Reg p.W P :=
  ODEGroverProgram.operator (trun v σ p.prepC) (ODEGroverRay.projector (seedState v))
    (ODEHeraldedSuccess.successProjector goodF)

theorem stepC_agrees (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (hσ : σ.Unitary p.m) :
    Agrees WorkClean (trun v σ p.stepC) (p.groverStep v σ) := by
  have hW := p.pres2_prepC hτ hν hm v hv σ hσ
  have hg : Agrees WorkClean (trun v σ (ofGates (S := Wire p.a p.m p.r p.K)
      (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f))))
      rgoodI := by
    rw [trun_ofGates]; exact rgood_agrees p.zero_test_le
  have hs := rseedT_agrees (a := p.a) (m := p.m) (r := p.r) (K := p.K) p.zero_test_le v σ
  unfold stepC groverStep ODEGroverProgram.operator
  simp only [trun_append, trun_invList, trun_singleton, teval_gate, negGate, gateOp_neg_one]
  have h1 := hg.comp pres2_rgoodI.1 (Agrees.refl WorkClean ((trun v σ p.prepC)†))
  have h2 := h1.comp (pres2_rgoodI.1.comp hW.2) hs
  have h3 := h2.comp (((pres2_rgoodI.1).comp hW.2).comp (pres2_rseedI v).1)
    (Agrees.refl WorkClean (trun v σ p.prepC))
  have h4 := h3.comp ((((pres2_rgoodI.1).comp hW.2).comp (pres2_rseedI v).1).comp hW.1)
    (Agrees.refl WorkClean (-1))
  intro ψ hψ
  rw [h4 ψ hψ]
  simp only [comp_apply, neg_apply, one_apply_eq_self, mul_apply_eq_comp, rgoodI, rseedI,
    star_eq_adjoint]

theorem pres_groverStep (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (hσ : σ.Unitary p.m) :
    Preserves WorkClean (p.groverStep v σ) := by
  have hW := p.pres2_prepC hτ hν hm v hv σ hσ
  have hpre : Preserves WorkClean (-(trun v σ p.prepC ∘L rseedI v ∘L
      (trun v σ p.prepC)† ∘L rgoodI)) :=
    preserves_neg ((((pres2_rgoodI.1).comp hW.2).comp (pres2_rseedI v).1).comp hW.1)
  intro ψ hψ
  have e : p.groverStep v σ ψ = (-(trun v σ p.prepC ∘L rseedI v ∘L
      (trun v σ p.prepC)† ∘L rgoodI)) ψ := by
    simp only [groverStep, ODEGroverProgram.operator, neg_apply, mul_apply_eq_comp, comp_apply,
      rgoodI, rseedI, star_eq_adjoint]
  rw [e]
  exact hpre ψ hψ

theorem steps_agree (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (hσ : σ.Unitary p.m) (j : ℕ) (φ : Reg p.W P)
    (hφ : Supp WorkClean φ) :
    trun v σ (List.replicate j p.stepC).flatten φ = (p.groverStep v σ ^ j) φ := by
  induction j generalizing φ with
  | zero => rfl
  | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, trun_append, comp_apply,
        p.stepC_agrees hτ hν hm v hv σ hσ φ hφ,
        ih _ (p.pres_groverStep hτ hν hm v hv σ hσ φ hφ), pow_succ, mul_apply_eq_comp]

/-- **The actual trial is the released actual Grover trial of the actual
preparation unitary.** -/
theorem trialC_seed (hτ : 0 ≤ p.tau) (hν : 0 < p.nu)
    (hm : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m) (v : P) (hv : ‖v‖ = 1)
    (σ : TOracles p.a p.m p.l P) (hσ : σ.Unitary p.m) (j : ℕ) :
    trun v σ (p.trialC j) (seedState v) =
      ODEGroverActual.trial goodF (trun v σ p.prepC) (seedState v) j := by
  have hW := p.pres2_prepC hτ hν hm v hv σ hσ
  have hseed : Supp WorkClean (seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
      (l := p.l) (f := p.f) v) := supp_bas _ workClean_zero _
  rw [trialC, trun_append, comp_apply,
    p.steps_agree hτ hν hm v hv σ hσ j _ (hW.1 _ hseed)]
  unfold ODEGroverActual.trial ODEGroverActual.actualG
  congr 2
  rw [groverStep, ODEGroverProgram.operator_eq_grover _ _ _
    (p.prepC_isUnitary hτ hν hm v hv σ hσ), ← projector_map]

/-! ### The decoded vector -/

/-- The ideal input map: weight and LCHS label preparation and loading. -/
def inMap (v : P) (σ : TOracles p.a p.m p.l P) : P →L[ℂ] Reg p.W P :=
  trun v σ p.load ∘L p.LP ∘L p.WP σ ∘L goodF

/-- The ideal output map: label preparation with conjugate phases. -/
def outMap (σ : TOracles p.a p.m p.l P) : P →L[ℂ] Reg p.W P :=
  p.PH† ∘L p.LP ∘L p.WP σ ∘L goodF

/-- **The clean decoded vector of the actual preparation.** -/
theorem decoded_prepC (v : P) (σ : TOracles p.a p.m p.l P) :
    ODEHeraldedSuccess.decoded goodF (trun v σ p.prepC) (seedState v) =
      ((p.outMap σ)†) (trun v σ p.select (p.inMap v σ v)) := by
  have hseed : Supp WorkClean (seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m)
      (l := p.l) (f := p.f) v) := supp_bas _ workClean_zero _
  rw [ODEHeraldedSuccess.decoded, p.prepC_agrees v σ _ hseed]
  have hs : seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l)
      (f := p.f) v = goodF v := by
    rw [seedState, goodF, basL_apply]
  rw [hs]
  simp only [Wideal, outMap, inMap, comp_apply, adjoint_comp, adjoint_adjoint]

end TParams

end

end SparseHamiltonian.GateODE.Time
