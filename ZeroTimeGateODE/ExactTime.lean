import ZeroTimeGateODE.Exact
import ZeroTimeGateODE.TimeCombined

/-!
# Zero time or a known zero generator with exact gates, time-dependent coefficients

The exact-gate form of the remark of Theorem `ode:thm:gates` for time-dependent coefficients
(`GateODE.Time.solver`).  The zero-case preparation is the released-model counterpart
`tzprepE p = tzrelC` of the direct source assembly (the supplied weight preparation `Wp`, the
loading `J` and `Wp†`), with the released reflections and sign:

* `tztrialE_counts`: no private call, no `U_J` call, `2j + 1` loading calls, `2 (2j + 1)`
  weight-preparation calls, `j` seed reflections and at most `j · reflGates` gates;
* `tztrialE_seed`: on the seed the trial is the released actual Grover trial of the zero-case
  preparation unitary;
* `tzprotocol`: the released bounded four-attempt wrapper with the released ratio `2g`;
  `tzprotocol_worst`: at most `40 g · reflGates` gates, no private and no `U_J` call, at most
  `80 g` loading calls, `160 g` weight-preparation calls and `40 g` seed reflections;
* `tzoutcome`, `exact_ode_time_solver_zero`: the guarantees `TZOutcome` (the fields of the
  released `GateODE.Time.TParams.Outcome`) against `x(T)` under `TZInstanceOK`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire zMat zMat_unitary negOne_unitary)
open GateODE (OInstr OWire AW Label invList rgoodG rgoodI rseedC rseedI flagG seedState
  seedState_norm goodF goodF_isometry WorkClean nGates nPriv nUJ nSrc nSeed)
open GateODE.Time (TParams TOracles trun teval)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The circuits, counts and validity -/

section Circuits

variable (p : TParams)

/-- **The exact-gate time-dependent zero-case preparation**: the weight preparation, the
loading and the inverse weight preparation (`tzrelC`) on the released wires. -/
def tzprepE : List p.Ins := tzrelC

/-- One amplification step around the time-dependent zero-case preparation. -/
def tzstepE : List p.Ins :=
  GateODE.ofGates rgoodG ++ invList (tzprepE p) ++ rseedC ++ tzprepE p ++ [.gate p.negGate]

/-- The time-dependent zero-case trial with `j` amplification steps. -/
def tztrialE (j : ℕ) : List p.Ins := tzprepE p ++ (List.replicate j (tzstepE p)).flatten

theorem tzprepE_counts :
    nPriv (tzprepE p) = 0 ∧ nUJ (tzprepE p) = 0 ∧ nSrc false (tzprepE p) = 1 ∧
      nSrc true (tzprepE p) = 2 ∧ nSeed (tzprepE p) = 0 ∧ nGates (tzprepE p) = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem tzstepE_counts :
    nPriv (tzstepE p) = 0 ∧ nUJ (tzstepE p) = 0 ∧ nSrc false (tzstepE p) = 2 ∧
      nSrc true (tzstepE p) = 4 ∧ nSeed (tzstepE p) = 1 ∧ nGates (tzstepE p) ≤ p.reflGates := by
  obtain ⟨wP, wU, wL, wW, wE, wG⟩ := tzprepE_counts p
  obtain ⟨rP, rU, rS, rE, rG⟩ := p.rseedC_counts
  obtain ⟨gU, gP, gS, gE⟩ := GateODE.ofGates_counts (S := Wire p.a p.m p.r p.K)
    (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f))
  have hg := p.rgoodG_length
  unfold tzstepE
  simp only [GateODE.nPriv_append, GateODE.nUJ_append, GateODE.nSrc_append,
    GateODE.nSeed_append, GateODE.nGates_append, GateODE.nPriv_invList, GateODE.nUJ_invList,
    GateODE.nSrc_invList, GateODE.nSeed_invList, GateODE.nGates_invList]
  have eN : nGates [OInstr.gate p.negGate] = 1 := rfl
  have eP : nPriv [OInstr.gate p.negGate] = 0 := rfl
  have eU : nUJ [OInstr.gate p.negGate] = 0 := rfl
  have eS : ∀ b, nSrc b [OInstr.gate p.negGate] = 0 := fun _ => rfl
  have eE : nSeed [OInstr.gate p.negGate] = 0 := rfl
  have hgl : nGates (GateODE.ofGates (S := Wire p.a p.m p.r p.K) (rgoodG (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f))) ≤ 2 * p.nz + 1 := by
    rw [GateODE.nGates_ofGates]
    exact hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [gP, wP, rP, eP]
  · rw [gU, wU, rU, eU]
  · rw [gS false, wL, rS false, eS false]
  · rw [gS true, wW, rS true, eS true]
  · rw [gE, wE, rE, eE]
  · rw [eN, wG]
    unfold GateODE.Time.TParams.reflGates
    omega

/-- **Exact counts of the time-dependent zero-case trial with `j` steps.** -/
theorem tztrialE_counts (j : ℕ) :
    nPriv (tztrialE p j) = 0 ∧ nUJ (tztrialE p j) = 0 ∧ nSrc false (tztrialE p j) = 2 * j + 1 ∧
      nSrc true (tztrialE p j) = 2 * (2 * j + 1) ∧ nSeed (tztrialE p j) = j ∧
      nGates (tztrialE p j) ≤ j * p.reflGates := by
  obtain ⟨wP, wU, wL, wW, wE, wG⟩ := tzprepE_counts p
  obtain ⟨sP, sU, sL, sW, sE, sG⟩ := tzstepE_counts p
  unfold tztrialE
  simp only [GateODE.nPriv_append, GateODE.nUJ_append, GateODE.nSrc_append,
    GateODE.nSeed_append, GateODE.nGates_append]
  have rP : nPriv (List.replicate j (tzstepE p)).flatten = j * nPriv (tzstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  have rU : nUJ (List.replicate j (tzstepE p)).flatten = j * nUJ (tzstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  have rS : ∀ b, nSrc b (List.replicate j (tzstepE p)).flatten = j * nSrc b (tzstepE p) :=
    fun b => GateODE.countP_replicate_flatten _ j _
  have rE : nSeed (List.replicate j (tzstepE p)).flatten = j * nSeed (tzstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  have rG : nGates (List.replicate j (tzstepE p)).flatten = j * nGates (tzstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rP, wP, sP]
    simp
  · rw [rU, wU, sU]
    simp
  · rw [rS false, wL, sL]
    ring
  · rw [rS true, wW, sW]
    ring
  · rw [rE, wE, sE]
    ring
  · rw [rG, wG, zero_add]
    exact Nat.mul_le_mul_left _ sG

theorem tzprepE_valid : ∀ g ∈ tzprepE p, g.Valid Wire.anc := by
  intro g hg
  simp only [tzprepE, tzrelC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> trivial

theorem tzstepE_valid : ∀ g ∈ tzstepE p, g.Valid Wire.anc := by
  have hW := tzprepE_valid p
  have hmc : ∀ u, UnitaryMat u → ∀ g ∈ mcGate (GateODE.zeroLits (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f)) GateODE.poolList
      (Sum.inr OWire.flg) u, GateOK 2 g :=
    fun u hu => mcGate_valid _ _ _ _ hu GateODE.poolList_nodup GateODE.zeroLits_ne_flg
      (fun w hw => by obtain ⟨i, rfl⟩ := (GateODE.mem_poolList w).mp hw; simp)
      GateODE.zeroLits_ne_pool
  have hgood : ∀ g ∈ GateODE.ofGates (S := Wire p.a p.m p.r p.K) (rgoodG (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
    GateODE.valid_ofGates _ _ (fun g hg => (hmc zMat zMat_unitary g hg).mono (by norm_num))
  have hflag : ∀ g ∈ GateODE.ofGates (S := Wire p.a p.m p.r p.K) (flagG (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
    GateODE.valid_ofGates _ _ (fun g hg => (hmc pauliX pauliX_unitary g hg).mono (by norm_num))
  intro g hg
  simp only [tzstepE, rseedC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (((h | h) | ((h | h) | h)) | h) | h
  · exact hgood g h
  · exact GateODE.valid_invList _ _ hW g h
  · exact hflag g h
  · subst h
    show [(Sum.inr OWire.flg, true)].length ≤ 1
    simp
  · exact hflag g h
  · exact hW g h
  · subst h
    exact ⟨by simp [GateODE.Time.TParams.negGate], by simp [GateODE.Time.TParams.negGate],
      negOne_unitary⟩

/-- Every instruction of every time-dependent zero-case trial is a valid elementary
instruction. -/
theorem tztrialE_valid (j : ℕ) : ∀ g ∈ tztrialE p j, g.Valid Wire.anc := by
  intro g hg
  simp only [tztrialE, List.mem_append, List.mem_flatten, List.mem_replicate] at hg
  rcases hg with h | ⟨l', ⟨_, rfl⟩, h⟩
  · exact tzprepE_valid p g h
  · exact tzstepE_valid p g h

end Circuits

/-! ### Independence of `U_J` and the private operations -/

section Oracles

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **A circuit without `U_J` and private instructions does not depend on `U_J` and the private
operations** (time-dependent semantics). -/
theorem trun_eq_srcOracles {a m r K k l f : ℕ} (v : P) (σ : TOracles a k l P)
    (gs : List (OInstr (Wire a m r K) (OWire k l f))) (hU : nUJ gs = 0) (hD : nPriv gs = 0) :
    trun v σ gs = trun v ⟨1, fun _ _ => 1, σ.J, σ.Wp⟩ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      have hU' : nUJ gs = 0 :=
        Nat.eq_zero_of_le_zero (hU ▸ (List.sublist_cons_self g gs).countP_le)
      have hD' : nPriv gs = 0 :=
        Nat.eq_zero_of_le_zero (hD ▸ (List.sublist_cons_self g gs).countP_le)
      have he : teval v σ g = teval v ⟨1, fun _ _ => 1, σ.J, σ.Wp⟩ g := by
        cases g with
        | gate g => rfl
        | uj cs adj => simp [GateODE.nUJ, OInstr.isUJ] at hU
        | priv cs adj => simp [GateODE.nPriv, OInstr.isPriv] at hD
        | src b adj => rfl
        | seed cs => rfl
      rw [GateODE.Time.trun_cons, GateODE.Time.trun_cons, ih hU' hD', he]

end Oracles

/-! ### The trials are Grover trials of the preparation -/

section Agree

variable (p : TParams)
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

theorem tztrialE_isUnitary (v : P) (hv : ‖v‖ = 1) (σ : TOracles p.a p.m p.l P)
    (hJ : ∀ s, IsUnitary (σ.J s)) (hWl : σ.Wp.conjTranspose * σ.Wp = 1)
    (hWr : σ.Wp * σ.Wp.conjTranspose = 1) (j : ℕ) : IsUnitary (trun v σ (tztrialE p j)) := by
  obtain ⟨hD, hU, -, -, -, -⟩ := tztrialE_counts p j
  rw [trun_eq_srcOracles v σ (tztrialE p j) hU hD]
  have h1 : IsUnitary (1 : GateCircuit.Anc p.a P →L[ℂ] GateCircuit.Anc p.a P) := isUnitary_one
  have hσ : (⟨1, fun _ _ => 1, σ.J, σ.Wp⟩ : TOracles p.a p.m p.l P).Unitary p.m :=
    ⟨h1, fun _ _ _ => h1, hJ, hWl, hWr⟩
  exact GateODE.Time.trun_isUnitary v _ hσ hv _ (tztrialE_valid p j)

theorem tzprepE_isUnitary (v : P) (hv : ‖v‖ = 1) (σ : TOracles p.a p.m p.l P)
    (hJ : ∀ s, IsUnitary (σ.J s)) (hWl : σ.Wp.conjTranspose * σ.Wp = 1)
    (hWr : σ.Wp * σ.Wp.conjTranspose = 1) : IsUnitary (trun v σ (tzprepE p)) := by
  have h := tztrialE_isUnitary p v hv σ hJ hWl hWr 0
  simpa [tztrialE] using h

/-- The time-dependent zero-case preparation and its adjoint keep the work wires clean. -/
theorem pres2_tzprepE (v : P) (σ : TOracles p.a p.m p.l P) :
    Pres2 WorkClean (trun v σ (tzprepE p)) := by
  rw [tzprepE, tzrelC, GateODE.Time.trun_cons, GateODE.Time.trun_cons,
    GateODE.Time.trun_singleton, GateODE.Time.teval_wprep, GateODE.Time.teval_load,
    GateODE.Time.teval_wprep]
  exact ((GateODE.Time.pres2_wprep σ true).comp (GateODE.Time.pres2_psel _ _)).comp
    (GateODE.Time.pres2_wprep σ false)

/-- The released signed Grover step of the time-dependent zero-case preparation. -/
def tzgroverStep (v : P) (σ : TOracles p.a p.m p.l P) : Reg p.W P →L[ℂ] Reg p.W P :=
  ODEGroverProgram.operator (trun v σ (tzprepE p)) (ODEGroverRay.projector (seedState v))
    (ODEHeraldedSuccess.successProjector goodF)

theorem tzstepE_agrees (v : P) (σ : TOracles p.a p.m p.l P) :
    Agrees WorkClean (trun v σ (tzstepE p)) (tzgroverStep p v σ) := by
  have hW := pres2_tzprepE p v σ
  have hg : Agrees WorkClean (trun v σ (GateODE.ofGates (S := Wire p.a p.m p.r p.K)
      (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.m) (l := p.l) (f := p.f))))
      rgoodI := by
    rw [GateODE.Time.trun_ofGates]
    exact GateODE.rgood_agrees p.zero_test_le
  have hs := GateODE.Time.rseedT_agrees (a := p.a) (m := p.m) (r := p.r) (K := p.K)
    p.zero_test_le v σ
  unfold tzstepE tzgroverStep ODEGroverProgram.operator
  simp only [GateODE.Time.trun_append, GateODE.Time.trun_invList, GateODE.Time.trun_singleton,
    GateODE.Time.teval_gate, GateODE.Time.TParams.negGate, GateODE.gateOp_neg_one]
  have h1 := hg.comp GateODE.pres2_rgoodI.1 (Agrees.refl WorkClean ((trun v σ (tzprepE p))†))
  have h2 := h1.comp (GateODE.pres2_rgoodI.1.comp hW.2) hs
  have h3 := h2.comp ((GateODE.pres2_rgoodI.1.comp hW.2).comp (GateODE.pres2_rseedI v).1)
    (Agrees.refl WorkClean (trun v σ (tzprepE p)))
  have h4 := h3.comp
    (((GateODE.pres2_rgoodI.1.comp hW.2).comp (GateODE.pres2_rseedI v).1).comp hW.1)
    (Agrees.refl WorkClean (-1))
  intro ψ hψ
  rw [h4 ψ hψ]
  simp only [comp_apply, neg_apply, one_apply_eq_self, mul_apply_eq_comp, GateODE.rgoodI,
    GateODE.rseedI, star_eq_adjoint]

theorem pres_tzgroverStep (v : P) (σ : TOracles p.a p.m p.l P) :
    Preserves WorkClean (tzgroverStep p v σ) := by
  have hW := pres2_tzprepE p v σ
  have hpre : Preserves WorkClean (-(trun v σ (tzprepE p) ∘L rseedI v ∘L
      (trun v σ (tzprepE p))† ∘L rgoodI)) :=
    preserves_neg (((GateODE.pres2_rgoodI.1.comp hW.2).comp (GateODE.pres2_rseedI v).1).comp
      hW.1)
  intro ψ hψ
  have e : tzgroverStep p v σ ψ = (-(trun v σ (tzprepE p) ∘L rseedI v ∘L
      (trun v σ (tzprepE p))† ∘L rgoodI)) ψ := by
    simp only [tzgroverStep, ODEGroverProgram.operator, neg_apply, mul_apply_eq_comp,
      comp_apply, GateODE.rgoodI, GateODE.rseedI, star_eq_adjoint]
  rw [e]
  exact hpre ψ hψ

theorem tzsteps_agree (v : P) (σ : TOracles p.a p.m p.l P) (j : ℕ) (φ : Reg p.W P)
    (hφ : Supp WorkClean φ) :
    trun v σ (List.replicate j (tzstepE p)).flatten φ = (tzgroverStep p v σ ^ j) φ := by
  induction j generalizing φ with
  | zero => rfl
  | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, GateODE.Time.trun_append, comp_apply,
        tzstepE_agrees p v σ φ hφ, ih _ (pres_tzgroverStep p v σ φ hφ), pow_succ,
        mul_apply_eq_comp]

/-- **The time-dependent zero-case trial is the released actual Grover trial of the zero-case
preparation unitary.** -/
theorem tztrialE_seed (v : P) (hv : ‖v‖ = 1) (σ : TOracles p.a p.m p.l P)
    (hJ : ∀ s, IsUnitary (σ.J s)) (hWl : σ.Wp.conjTranspose * σ.Wp = 1)
    (hWr : σ.Wp * σ.Wp.conjTranspose = 1) (j : ℕ) :
    trun v σ (tztrialE p j) (seedState v) =
      ODEGroverActual.trial goodF (trun v σ (tzprepE p)) (seedState v) j := by
  have hW := pres2_tzprepE p v σ
  have hseed : Supp WorkClean (seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K)
      (k := p.m) (l := p.l) (f := p.f) v) := supp_bas _ GateODE.workClean_zero _
  rw [tztrialE, GateODE.Time.trun_append, comp_apply, tzsteps_agree p v σ j _ (hW.1 _ hseed)]
  unfold ODEGroverActual.trial ODEGroverActual.actualG
  congr 2
  rw [tzgroverStep, ODEGroverProgram.operator_eq_grover _ _ _
    (tzprepE_isUnitary p v hv σ hJ hWl hWr), ← GateODE.projector_map]

end Agree

/-! ### The protocol -/

section Protocol

variable (p : TParams)
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The time-dependent zero-case trial with `j` steps as a released multi-oracle program. -/
def tzprogram (v : P) (j : ℕ) :
    MultiOracleCircuit.Program (GateODE.Time.tfamily (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.m) (l := p.l) (f := p.f) v) :=
  GateODE.Time.ttoProgram v (tztrialE p j)

theorem tzprogram_eval (v : P) (σ : TOracles p.a p.m p.l P) (j : ℕ) :
    (tzprogram p v j).eval σ = trun v σ (tztrialE p j) :=
  GateODE.Time.ttoProgram_eval _ _ _

theorem tzprogram_cost (v : P) (j : ℕ) :
    (tzprogram p v j).cost p.wGate = nGates (tztrialE p j) ∧
    (tzprogram p v j).cost p.wPriv = nPriv (tztrialE p j) ∧
    (tzprogram p v j).cost p.wUJ = nUJ (tztrialE p j) ∧
    (tzprogram p v j).cost p.wLoad = nSrc false (tztrialE p j) ∧
    (tzprogram p v j).cost p.wPrep = nSrc true (tztrialE p j) ∧
    (tzprogram p v j).cost p.wSeed = nSeed (tztrialE p j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [tzprogram, GateODE.Time.ttoProgram_cost]
    exact GateODE.sum_map_indicator _ _

/-- **The time-dependent zero-case protocol**: the released bounded four-attempt wrapper with
the released ratio `2g`. -/
def tzprotocol (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.Protocol (GateODE.Time.tfamily (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.m) (l := p.l) (f := p.f) v) P :=
  ODERepeatProtocol.fourTrials (tzprogram p v) (ODEGroverAverage.chosenIterations p.ratio)
    (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hg)).1 (seedState v)
    (seedState_norm v hv) goodF goodF_isometry

/-- The public trial family of the time-dependent zero case. -/
def tztrials (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    ODERepeatProtocol.TrialFamily (GateODE.Time.tfamily (a := p.a) (m := p.m) (r := p.r)
      (K := p.K) (k := p.m) (l := p.l) (f := p.f) v) P :=
  ODERepeatProtocol.ofCircuits (tzprogram p v) (ODEGroverAverage.chosenIterations p.ratio)
    (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hg)).1 (seedState v)
    (seedState_norm v hv) goodF goodF_isometry

theorem tzprotocol_eq (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    tzprotocol p v hv hg = ODERepeatProtocol.Protocol.repeatTrials (tztrials p v hv hg) 4 := rfl

theorem tztrials_eval (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : TOracles p.a p.m p.l P)
    (j : Fin (tztrials p v hv hg).choices) :
    ((tztrials p v hv hg).circuit j).eval σ = trun v σ (tztrialE p j.val) :=
  tzprogram_eval p v σ j.val

theorem tztrials_output (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    (tztrials p v hv hg).output = goodF := rfl

theorem tztrials_seed (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) :
    (tztrials p v hv hg).seed = seedState v := rfl

theorem tztrials_amplitude (v : P) (hv : ‖v‖ = 1) (hg : 1 ≤ p.g) (σ : TOracles p.a p.m p.l P)
    (j : Fin (tztrials p v hv hg).choices) :
    (tztrials p v hv hg).amplitude σ j = (goodF†) (trun v σ (tztrialE p j.val) (seedState v)) := by
  rw [ODERepeatProtocol.TrialFamily.amplitude, tztrials_eval p v hv hg σ j,
    tztrials_output p v hv hg, tztrials_seed p v hv hg]

theorem tztrial_cost_bound (hg : 1 ≤ p.g) (v : P) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations p.ratio) :
    ((tzprogram p v j).cost p.wGate : ℝ) ≤ 10 * p.g * p.reflGates ∧
    (tzprogram p v j).cost p.wPriv = 0 ∧
    (tzprogram p v j).cost p.wUJ = 0 ∧
    ((tzprogram p v j).cost p.wLoad : ℝ) ≤ 20 * p.g ∧
    ((tzprogram p v j).cost p.wPrep : ℝ) ≤ 40 * p.g ∧
    ((tzprogram p v j).cost p.wSeed : ℝ) ≤ 10 * p.g := by
  obtain ⟨cG, cP, cU, cL, cW, cE⟩ := tzprogram_cost p v j
  obtain ⟨tP, tU, tL, tW, tE, tG⟩ := tztrialE_counts p j
  have hM := (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hg)).2.2
  have hjM : (j : ℝ) + 1 ≤ ODEGroverAverage.chosenIterations p.ratio := by exact_mod_cast hj
  have hr : p.ratio = 2 * p.g := rfl
  rw [hr] at hM
  have hj1 : (2 * (j : ℝ) + 1) ≤ 20 * p.g := by linarith
  have hj2 : (j : ℝ) ≤ 10 * p.g := by linarith
  rw [cG, cP, cU, cL, cW, cE, tP, tU, tL, tW, tE]
  refine ⟨?_, rfl, rfl, ?_, ?_, hj2⟩
  · generalize p.reflGates = Rg at tG ⊢
    have h : (nGates (tztrialE p j) : ℝ) ≤ j * Rg := by exact_mod_cast tG
    have h2 : (j : ℝ) * Rg ≤ 10 * p.g * Rg := mul_le_mul_of_nonneg_right hj2 (Nat.cast_nonneg _)
    linarith
  · push_cast
    linarith
  · push_cast
    linarith

/-- **Worst-case counts of the time-dependent zero-case protocol**, over every history: at most
`40 g · reflGates` elementary gates, no private call and no `U_J` call, at most `80 g` loading
calls, `160 g` weight-preparation calls and `40 g` seed reflections. -/
theorem tzprotocol_worst (hg : 1 ≤ p.g) (v : P) (hv : ‖v‖ = 1) :
    ((tzprotocol p v hv hg).worstCost p.wGate : ℝ) ≤ 40 * p.g * p.reflGates ∧
    (tzprotocol p v hv hg).worstCost p.wPriv = 0 ∧
    (tzprotocol p v hv hg).worstCost p.wUJ = 0 ∧
    ((tzprotocol p v hv hg).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((tzprotocol p v hv hg).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((tzprotocol p v hv hg).worstCost p.wSeed : ℝ) ≤ 40 * p.g := by
  have hW := fun w B (h : ∀ j, j < ODEGroverAverage.chosenIterations p.ratio →
      ((tzprogram p v j).cost w : ℝ) ≤ B) =>
    ODERepeatProtocol.fourTrials_worstCost_le (tzprogram p v)
      (ODEGroverAverage.chosenIterations p.ratio)
      (ODEGroverAverage.chosenIterations_bounds p.ratio (p.ratio_ge hg)).1 (seedState v)
      (seedState_norm v hv) goodF goodF_isometry w B h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hW p.wGate _ (fun j hj => (tztrial_cost_bound p hg v j hj).1)
    unfold tzprotocol
    linarith
  · have h := hW p.wPriv 0 (fun j hj => by
      rw [(tztrial_cost_bound p hg v j hj).2.1]
      norm_num)
    have h0 : ((tzprotocol p v hv hg).worstCost p.wPriv : ℝ) ≤ 0 := by
      unfold tzprotocol
      linarith
    exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
  · have h := hW p.wUJ 0 (fun j hj => by
      rw [(tztrial_cost_bound p hg v j hj).2.2.1]
      norm_num)
    have h0 : ((tzprotocol p v hv hg).worstCost p.wUJ : ℝ) ≤ 0 := by
      unfold tzprotocol
      linarith
    exact_mod_cast le_antisymm h0 (Nat.cast_nonneg _)
  · have h := hW p.wLoad _ (fun j hj => (tztrial_cost_bound p hg v j hj).2.2.2.1)
    unfold tzprotocol
    linarith
  · have h := hW p.wPrep _ (fun j hj => (tztrial_cost_bound p hg v j hj).2.2.2.2.1)
    unfold tzprotocol
    linarith
  · have h := hW p.wSeed _ (fun j hj => (tztrial_cost_bound p hg v j hj).2.2.2.2.2)
    unfold tzprotocol
    linarith

end Protocol

end

end SparseHamiltonian.ZeroTimeGateODE
