import ZeroTimeGateODE.Constant
import GateEfficientODE.Theorem

/-!
# Zero time or a known zero generator with exact gates: the trial circuits

The exact-gate model of Theorem `ode:thm:gates` (`GateODE.solver`) runs instruction lists
`GateODE.OInstr` on the released wires `GateODE.Params.W` with supplied unitaries: `U_J`, the
private Cayley operations and the two source interfaces (`GateODE.Oracles`).  Its trial with `j`
amplification steps is the released preparation followed by `j` steps
`R_good · prep⁻¹ · R_seed · prep · (-1)`.  Here the preparation is the direct source assembly
`zprepE p = zrelC (srcRot T r₀ r_b)` (the gate `R` on `ini`, the two source calls, `R†` on
`ini`), with the released reflections and sign:

* `zstepE`, `ztrialE`: one step and the trial with `j` steps;
* `ztrialE_counts`: no private call, no `U_J` call, `2j + 1` calls of each source interface,
  `j` seed reflections and at most `2 (2j + 1) + j · reflGates` gates; `ztrialE_valid`;
* `run_eq_srcOracles`: a circuit without `U_J` and private instructions does not depend on
  `U_J` and the private operations, so the trials are unitary for unitary source interfaces and
  a unit seed (`ztrialE_isUnitary`);
* `ztrialE_seed`: on the seed the trial is the released actual Grover trial
  `ODEGroverActual.trial` of the zero-case preparation unitary (the released agreement
  argument of `GateODE.Params.trialC_seed`, with `pres2_zprepE` for the preparation);
* `zprepE_decoded`: the decoded prepared vector is `(x₀ + T b) / B` under the released source
  promises.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire zMat zMat_unitary negOne_unitary)
open GateODE (Params OInstr OWire AW Label Oracles wiring run invList rgoodG rgoodI
  rseedC rseedI flagG seedState goodF WorkClean nGates nPriv nUJ nSrc nSeed)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The circuits -/

section Circuits

variable (p : Params)

/-- **The exact-gate zero-case preparation**: the released-model direct source assembly
`zrelC (srcRot T r₀ r_b)` on the released wires. -/
def zprepE : List p.Ins := zrelC (srcRot p.T p.r₀ p.rb)

/-- One amplification step around the zero-case preparation: the released good-subspace
reflection, the inverse preparation, the released seed reflection, the preparation and the
sign `-1`. -/
def zstepE : List p.Ins :=
  GateODE.ofGates rgoodG ++ invList (zprepE p) ++ rseedC ++ zprepE p ++ [.gate p.negGate]

/-- The zero-case trial with `j` amplification steps. -/
def ztrialE (j : ℕ) : List p.Ins := zprepE p ++ (List.replicate j (zstepE p)).flatten

end Circuits

/-! ### Counts and validity -/

section Counts

variable (p : Params)

theorem zprepE_counts :
    nPriv (zprepE p) = 0 ∧ nUJ (zprepE p) = 0 ∧ (∀ b, nSrc b (zprepE p) = 1) ∧
      nSeed (zprepE p) = 0 ∧ nGates (zprepE p) = 2 := by
  refine ⟨rfl, rfl, fun b => ?_, rfl, rfl⟩
  cases b <;> rfl

theorem zstepE_counts :
    nPriv (zstepE p) = 0 ∧ nUJ (zstepE p) = 0 ∧ (∀ b, nSrc b (zstepE p) = 2) ∧
      nSeed (zstepE p) = 1 ∧ nGates (zstepE p) ≤ 2 * 2 + p.reflGates := by
  obtain ⟨wP, wU, wS, wE, wG⟩ := zprepE_counts p
  obtain ⟨rP, rU, rS, rE, rG⟩ := p.rseedC_counts
  obtain ⟨gU, gP, gS, gE⟩ := GateODE.ofGates_counts (S := Wire p.a p.m p.r p.K)
    (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f))
  have hg := p.rgoodG_length
  unfold zstepE
  simp only [GateODE.nPriv_append, GateODE.nUJ_append, GateODE.nSrc_append,
    GateODE.nSeed_append, GateODE.nGates_append, GateODE.nPriv_invList, GateODE.nUJ_invList,
    GateODE.nSrc_invList, GateODE.nSeed_invList, GateODE.nGates_invList, GateODE.nGates_ofGates]
  have eN : nGates [OInstr.gate p.negGate] = 1 := rfl
  have eP : nPriv [OInstr.gate p.negGate] = 0 := rfl
  have eU : nUJ [OInstr.gate p.negGate] = 0 := rfl
  have eS : ∀ b, nSrc b [OInstr.gate p.negGate] = 0 := fun _ => rfl
  have eE : nSeed [OInstr.gate p.negGate] = 0 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [gP, wP, rP, eP]
  · rw [gU, wU, rU, eU]
  · intro b
    rw [gS b, wS b, rS b, eS b]
  · rw [gE, wE, rE, eE]
  · rw [eN, wG]
    unfold GateODE.Params.reflGates
    omega

/-- **Exact counts of the zero-case trial with `j` amplification steps**: no private call, no
`U_J` call, `2j + 1` calls of each source interface, `j` seed reflections, and at most
`2 (2j + 1) + j · reflGates` elementary gates. -/
theorem ztrialE_counts (j : ℕ) :
    nPriv (ztrialE p j) = 0 ∧ nUJ (ztrialE p j) = 0 ∧ (∀ b, nSrc b (ztrialE p j) = 2 * j + 1) ∧
      nSeed (ztrialE p j) = j ∧ nGates (ztrialE p j) ≤ (2 * j + 1) * 2 + j * p.reflGates := by
  obtain ⟨wP, wU, wS, wE, wG⟩ := zprepE_counts p
  obtain ⟨sP, sU, sS, sE, sG⟩ := zstepE_counts p
  unfold ztrialE
  simp only [GateODE.nPriv_append, GateODE.nUJ_append, GateODE.nSrc_append,
    GateODE.nSeed_append, GateODE.nGates_append]
  have rP : nPriv (List.replicate j (zstepE p)).flatten = j * nPriv (zstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  have rU : nUJ (List.replicate j (zstepE p)).flatten = j * nUJ (zstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  have rS : ∀ b, nSrc b (List.replicate j (zstepE p)).flatten = j * nSrc b (zstepE p) :=
    fun b => GateODE.countP_replicate_flatten _ j _
  have rE : nSeed (List.replicate j (zstepE p)).flatten = j * nSeed (zstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  have rG : nGates (List.replicate j (zstepE p)).flatten = j * nGates (zstepE p) :=
    GateODE.countP_replicate_flatten _ j _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [rP, wP, sP]
    simp
  · rw [rU, wU, sU]
    simp
  · intro b
    rw [rS b, wS b, sS b]
    ring
  · rw [rE, wE, sE]
    ring
  · rw [rG, wG]
    calc 2 + j * nGates (zstepE p) ≤ 2 + j * (2 * 2 + p.reflGates) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ sG) _
      _ = (2 * j + 1) * 2 + j * p.reflGates := by ring

theorem zprepE_valid (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B) :
    ∀ g ∈ zprepE p, g.Valid Wire.anc := by
  have hu := srcRot_unitary p.T p.r₀ p.rb hT hr₀ hrb hB
  intro g hg
  simp only [zprepE, zrelC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨by simp, by simp, hu⟩
  · trivial
  · trivial
  · exact ⟨by simp, by simp, unitaryMat_conjTranspose hu⟩

theorem zstepE_valid (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B) :
    ∀ g ∈ zstepE p, g.Valid Wire.anc := by
  have hW := zprepE_valid p hr₀ hrb hT hB
  have hmc : ∀ u, UnitaryMat u → ∀ g ∈ mcGate (GateODE.zeroLits (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f)) GateODE.poolList
      (Sum.inr OWire.flg) u, GateOK 2 g :=
    fun u hu => mcGate_valid _ _ _ _ hu GateODE.poolList_nodup GateODE.zeroLits_ne_flg
      (fun w hw => by obtain ⟨i, rfl⟩ := (GateODE.mem_poolList w).mp hw; simp)
      GateODE.zeroLits_ne_pool
  have hgood : ∀ g ∈ GateODE.ofGates (S := Wire p.a p.m p.r p.K) (rgoodG (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
    GateODE.valid_ofGates _ _ (fun g hg => (hmc zMat zMat_unitary g hg).mono (by norm_num))
  have hflag : ∀ g ∈ GateODE.ofGates (S := Wire p.a p.m p.r p.K) (flagG (a := p.a) (m := p.m)
      (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f)), g.Valid Wire.anc :=
    GateODE.valid_ofGates _ _ (fun g hg => (hmc pauliX pauliX_unitary g hg).mono (by norm_num))
  intro g hg
  simp only [zstepE, rseedC, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
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
    exact ⟨by simp [GateODE.Params.negGate], by simp [GateODE.Params.negGate], negOne_unitary⟩

/-- Every instruction of every zero-case trial is a valid elementary instruction. -/
theorem ztrialE_valid (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B)
    (j : ℕ) : ∀ g ∈ ztrialE p j, g.Valid Wire.anc := by
  intro g hg
  simp only [ztrialE, List.mem_append, List.mem_flatten, List.mem_replicate] at hg
  rcases hg with h | ⟨l', ⟨_, rfl⟩, h⟩
  · exact zprepE_valid p hr₀ hrb hT hB g h
  · exact zstepE_valid p hr₀ hrb hT hB g h

end Counts

/-! ### Independence of `U_J` and the private operations -/

section Oracles

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **A circuit without `U_J` and private instructions does not depend on `U_J` and the private
operations**: it runs as with the trivial ones. -/
theorem run_eq_srcOracles {S O : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]
    {a : ℕ} {Λ : Type*} (ω : GateODE.Wiring S O a Λ P) (σ : Oracles a Λ P)
    (gs : List (OInstr S O)) (hU : nUJ gs = 0) (hD : nPriv gs = 0) :
    run ω σ gs = run ω ⟨1, fun _ => 1, σ.J⟩ gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      have hU' : nUJ gs = 0 :=
        Nat.eq_zero_of_le_zero (hU ▸ (List.sublist_cons_self g gs).countP_le)
      have hD' : nPriv gs = 0 :=
        Nat.eq_zero_of_le_zero (hD ▸ (List.sublist_cons_self g gs).countP_le)
      have he : g.eval ω σ = g.eval ω ⟨1, fun _ => 1, σ.J⟩ := by
        cases g with
        | gate g => rfl
        | uj cs adj => simp [GateODE.nUJ, OInstr.isUJ] at hU
        | priv cs adj => simp [GateODE.nPriv, OInstr.isPriv] at hD
        | src b adj => rfl
        | seed cs => rfl
      rw [GateODE.run_cons, GateODE.run_cons, ih hU' hD', he]

end Oracles

/-! ### The trials are Grover trials of the preparation -/

section Agree

variable (p : Params)
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

theorem ztrialE_isUnitary (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B)
    (v : P) (hv : ‖v‖ = 1) (σ : Oracles p.a (Label p.k p.l) P) (hJ : ∀ b, IsUnitary (σ.J b))
    (j : ℕ) : IsUnitary (run (wiring v) σ (ztrialE p j)) := by
  obtain ⟨hD, hU, -, -, -⟩ := ztrialE_counts p j
  rw [run_eq_srcOracles (wiring v) σ (ztrialE p j) hU hD]
  have h1 : IsUnitary (1 : GateCircuit.Anc p.a P →L[ℂ] GateCircuit.Anc p.a P) := isUnitary_one
  exact GateODE.run_isUnitary (wiring v) (⟨1, fun _ => 1, σ.J⟩ : Oracles p.a (Label p.k p.l) P)
    h1 (fun _ => h1) hJ hv _ (ztrialE_valid p hr₀ hrb hT hB j)

theorem zprepE_isUnitary (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B)
    (v : P) (hv : ‖v‖ = 1) (σ : Oracles p.a (Label p.k p.l) P) (hJ : ∀ b, IsUnitary (σ.J b)) :
    IsUnitary (run (wiring v) σ (zprepE p)) := by
  have h := ztrialE_isUnitary p hr₀ hrb hT hB v hv σ hJ 0
  simpa [ztrialE] using h

/-- The zero-case preparation and its adjoint keep the work wires clean. -/
theorem pres2_zprepE (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Pres2 WorkClean (run (wiring v) σ (zprepE p)) := by
  have hg : ∀ u : Matrix Bool Bool ℂ, Pres2 WorkClean
      (gateOp (Q := P) [] (Sum.inr OWire.ini : p.W) u) :=
    fun u => pres2_gateOp WorkClean [] _ u
      (fun x b hx => GateODE.workClean_update_inr x _ rfl b hx)
  rw [zprepE, zrelC, GateODE.run_cons, GateODE.run_cons, GateODE.run_cons,
    GateODE.run_singleton, OInstr.eval_gate, OInstr.eval_src, OInstr.eval_src, OInstr.eval_gate]
  exact (((hg _).comp (GateODE.pres2_pctl _ _ _)).comp (GateODE.pres2_pctl _ _ _)).comp (hg _)

/-- The released signed Grover step of the zero-case preparation. -/
def zgroverStep (v : P) (σ : Oracles p.a (Label p.k p.l) P) : Reg p.W P →L[ℂ] Reg p.W P :=
  ODEGroverProgram.operator (run (wiring v) σ (zprepE p)) (ODEGroverRay.projector (seedState v))
    (ODEHeraldedSuccess.successProjector goodF)

theorem zstepE_agrees (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Agrees WorkClean (run (wiring v) σ (zstepE p)) (zgroverStep p v σ) := by
  have hW := pres2_zprepE p v σ
  have hg : Agrees WorkClean (run (wiring v) σ (GateODE.ofGates (S := Wire p.a p.m p.r p.K)
      (rgoodG (a := p.a) (m := p.m) (r := p.r) (K := p.K) (k := p.k) (l := p.l) (f := p.f))))
      rgoodI := by
    rw [GateODE.run_ofGates]
    exact GateODE.rgood_agrees p.zero_test_le
  have hs := GateODE.rseed_agrees (a := p.a) (m := p.m) (r := p.r) (K := p.K) p.zero_test_le v σ
  unfold zstepE zgroverStep ODEGroverProgram.operator
  simp only [GateODE.run_append, GateODE.run_invList, GateODE.run_singleton, OInstr.eval_gate,
    GateODE.Params.negGate, GateODE.gateOp_neg_one]
  have h1 := hg.comp GateODE.pres2_rgoodI.1
    (Agrees.refl WorkClean ((run (wiring v) σ (zprepE p))†))
  have h2 := h1.comp (GateODE.pres2_rgoodI.1.comp hW.2) hs
  have h3 := h2.comp ((GateODE.pres2_rgoodI.1.comp hW.2).comp (GateODE.pres2_rseedI v).1)
    (Agrees.refl WorkClean (run (wiring v) σ (zprepE p)))
  have h4 := h3.comp
    (((GateODE.pres2_rgoodI.1.comp hW.2).comp (GateODE.pres2_rseedI v).1).comp hW.1)
    (Agrees.refl WorkClean (-1))
  intro ψ hψ
  rw [h4 ψ hψ]
  simp only [comp_apply, neg_apply, one_apply_eq_self, mul_apply_eq_comp, GateODE.rgoodI,
    GateODE.rseedI, star_eq_adjoint]

theorem pres_zgroverStep (v : P) (σ : Oracles p.a (Label p.k p.l) P) :
    Preserves WorkClean (zgroverStep p v σ) := by
  have hW := pres2_zprepE p v σ
  have hpre : Preserves WorkClean (-(run (wiring v) σ (zprepE p) ∘L rseedI v ∘L
      (run (wiring v) σ (zprepE p))† ∘L rgoodI)) :=
    preserves_neg (((GateODE.pres2_rgoodI.1.comp hW.2).comp (GateODE.pres2_rseedI v).1).comp
      hW.1)
  intro ψ hψ
  have e : zgroverStep p v σ ψ = (-(run (wiring v) σ (zprepE p) ∘L rseedI v ∘L
      (run (wiring v) σ (zprepE p))† ∘L rgoodI)) ψ := by
    simp only [zgroverStep, ODEGroverProgram.operator, neg_apply, mul_apply_eq_comp, comp_apply,
      GateODE.rgoodI, GateODE.rseedI, star_eq_adjoint]
  rw [e]
  exact hpre ψ hψ

theorem zsteps_agree (v : P) (σ : Oracles p.a (Label p.k p.l) P) (j : ℕ) (φ : Reg p.W P)
    (hφ : Supp WorkClean φ) :
    run (wiring v) σ (List.replicate j (zstepE p)).flatten φ = (zgroverStep p v σ ^ j) φ := by
  induction j generalizing φ with
  | zero => rfl
  | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, GateODE.run_append, comp_apply,
        zstepE_agrees p v σ φ hφ, ih _ (pres_zgroverStep p v σ φ hφ), pow_succ,
        mul_apply_eq_comp]

/-- **The zero-case trial is the released actual Grover trial of the zero-case preparation
unitary.** -/
theorem ztrialE_seed (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B)
    (v : P) (hv : ‖v‖ = 1) (σ : Oracles p.a (Label p.k p.l) P) (hJ : ∀ b, IsUnitary (σ.J b))
    (j : ℕ) :
    run (wiring v) σ (ztrialE p j) (seedState v) =
      ODEGroverActual.trial goodF (run (wiring v) σ (zprepE p)) (seedState v) j := by
  have hW := pres2_zprepE p v σ
  have hseed : Supp WorkClean (seedState (a := p.a) (m := p.m) (r := p.r) (K := p.K)
      (k := p.k) (l := p.l) (f := p.f) v) := supp_bas _ GateODE.workClean_zero _
  rw [ztrialE, GateODE.run_append, comp_apply, zsteps_agree p v σ j _ (hW.1 _ hseed)]
  unfold ODEGroverActual.trial ODEGroverActual.actualG
  congr 2
  rw [zgroverStep, ODEGroverProgram.operator_eq_grover _ _ _
    (zprepE_isUnitary p hr₀ hrb hT hB v hv σ hJ), ← GateODE.projector_map]

/-- **The decoded prepared vector of the zero case**: `B · goodF† (prep seed) = x₀ + T b` under
the public norms and the released source promises. -/
theorem zprepE_decoded (hr₀ : 0 ≤ p.r₀) (hrb : 0 ≤ p.rb) (hT : 0 ≤ p.T) (hB : 0 < p.B)
    (v : P) (σ : Oracles p.a (Label p.k p.l) P) (x0 b : P) (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb)
    (hJ0 : x0 ≠ 0 → σ.J false v = unitDirection x0)
    (hJb : b ≠ 0 → σ.J true v = unitDirection b) :
    p.B • (goodF†) (run (wiring v) σ (zprepE p) (seedState v)) = x0 + p.T • b :=
  srcRot_decoded p.T p.r₀ p.rb hT hr₀ hrb hB v σ x0 b h₀ hb hJ0 hJb

end Agree

end

end SparseHamiltonian.ZeroTimeGateODE
