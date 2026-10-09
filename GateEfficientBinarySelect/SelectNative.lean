import GateEfficientBinarySelect.Certified
import GateEfficientNative.Hamiltonian.Theorem

/-!
# Lemma `ode:lem:gate-select` with native private calls

The label-selected simulator of Lemma `ode:lem:gate-select` (`GateSelect.runS`, on the simulator
wires and the label wires `SW a m r K L`) with every instruction replaced by its native macro
(`GateNative.hcirc`): `U_J` by its elementary gates and every label- and slot-selected private
Cayley call by one native compute circuit `V`, the reversible angle arithmetic and the
bit-controlled rotations, `V† R V`, as in the released native simulators of `GateEfficientNative`.
The selection wires of the native private operation are the label wires and the slot wires of
the simulator (`selSW`); the native identity `NativeOK` of the label- and slot-selected family
`selFam D` is a hypothesis here and is proved for binary data in `SelectBinary`.

* `selRel`, `selSW`, `embW`, `selFam`: the released register of the label-selected simulator,
  its selection wires, the instruction embedding and the selected family;
* `prodOps_evalSel_embW`: the selected native semantics of the embedded simulator is the
  label-selected simulator `runS`;
* `hcirc_error_gen`: the full-output error of a native circuit on any clean released embedding;
* `native_gate_select`: **Lemma `ode:lem:gate-select` with native private calls**: validity,
  exactly `12 d` calls of the compute circuit, at most
  `200 (d+1)(a+m+r+1) + 84 d C_J + 6 d (2 |V| + 2 |arith| + 2 bP + bT + 1)` elementary gates, the
  register `|S| + (2a + 3m + 6r + 3 + |L|) + (|Z| + bT + bP + A + 3)` and full-output error at most
  `ε` against the controlled direct sum of the branch propagators on the clean-input space,
  under the integrated sample-error certificate and the arithmetic budget `48 d ζ ≤ ε`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire Vsp io anc_injective simR fDeg card_wire)
open GateSelect (branchPath runS evalS selE selE_isometry SW labelOf evalS_gate)
open GatePointerEncoding (wordEquivFin)
open scoped InnerProduct BigOperators

/-! ### The register -/

section Register

variable {a m r K : ℕ} {L : Type*}

/-- The released register of the label-selected simulator: the ancilla and sector wires of the
simulator. -/
def selRel (a m r K : ℕ) (L : Type*) : RelW (SW a m r K L) a :=
  ⟨fun i => Sum.inl (Wire.anc i), fun _ _ h => anc_injective (Sum.inl_injective h),
    Sum.inl Wire.sec, fun _ h => by cases h⟩

/-- The selection wires of the private calls: the label wires and the slot wires. -/
def selWFun : L ⊕ Fin m → SW a m r K L
  | Sum.inl l => Sum.inr l
  | Sum.inr i => Sum.inl (Wire.slot i)

theorem selWFun_injective :
    Function.Injective (selWFun (a := a) (m := m) (r := r) (K := K) (L := L)) := by
  intro x y h
  rcases x with l | i <;> rcases y with l' | i' <;> simp_all [selWFun]

/-- **The label and slot wires as selection wires** of the private calls. -/
def selSW : SelWires (selRel a m r K L) (L ⊕ Fin m) :=
  ⟨⟨selWFun, selWFun_injective⟩,
    fun s => by rcases s with l | i <;> simp [selWFun, selRel],
    fun s i => by rcases s with l | i' <;> simp [selWFun, selRel]⟩

/-- **The simulator instructions on the label-selected register.** -/
def embW : Instr (Wire a m r K) → Instr (SW a m r K L)
  | .gate g => .gate (GateODE.Gate.map Sum.inl g)
  | .uj cs adj => .uj (cs.map (fun c => (Sum.inl c.1, c.2))) adj
  | .priv cs adj => .priv (cs.map (fun c => (Sum.inl c.1, c.2))) adj

theorem isGate_embW (i : Instr (Wire a m r K)) : (embW (L := L) i).isGate = i.isGate := by
  cases i <;> rfl

theorem isUJ_embW (i : Instr (Wire a m r K)) : (embW (L := L) i).isUJ = i.isUJ := by
  cases i <;> rfl

theorem isPriv_embW (i : Instr (Wire a m r K)) : (embW (L := L) i).isPriv = i.isPriv := by
  cases i <;> rfl

theorem nGates_embW (l : List (Instr (Wire a m r K))) :
    nGates (l.map (embW (L := L))) = nGates l := by
  unfold nGates
  rw [List.countP_map]
  congr 1
  funext i
  exact isGate_embW i

theorem nUJ_embW (l : List (Instr (Wire a m r K))) :
    nUJ (l.map (embW (L := L))) = nUJ l := by
  unfold nUJ
  rw [List.countP_map]
  congr 1
  funext i
  exact isUJ_embW i

theorem nPriv_embW (l : List (Instr (Wire a m r K))) :
    nPriv (l.map (embW (L := L))) = nPriv l := by
  unfold nPriv
  rw [List.countP_map]
  congr 1
  funext i
  exact isPriv_embW i

/-- The embedded instructions are valid on the label-selected register. -/
theorem valid_embW (i : Instr (Wire a m r K)) (hi : i.Valid Wire.anc) :
    (embW (L := L) i).Valid (selRel a m r K L).anc := by
  cases i with
  | gate g =>
      obtain ⟨h1, h2, h3⟩ := hi
      refine ⟨by simpa [GateODE.Gate.map] using h1, ?_, h3⟩
      intro c hc
      simp only [GateODE.Gate.map, List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      intro h
      exact h2 c' hc' (Sum.inl_injective h)
  | uj cs adj =>
      obtain ⟨h1, h2⟩ := hi
      refine ⟨by simpa using h1, ?_⟩
      intro c hc i
      simp only [List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      intro h
      exact h2 c' hc' i (Sum.inl_injective h)
  | priv cs adj =>
      obtain ⟨h1, h2⟩ := hi
      refine ⟨by simpa using h1, ?_⟩
      intro c hc i
      simp only [List.mem_map] at hc
      obtain ⟨c', hc', rfl⟩ := hc
      intro h
      exact h2 c' hc' i (Sum.inl_injective h)

end Register

/-! ### The selected semantics -/

section Semantics

variable {a m r K : ℕ} {L : Type*} [Fintype L] [DecidableEq L] {S : Type*} [Fintype S]
  [DecidableEq S]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The label- and slot-selected private family**: at the label `z` on the label wires and the
slot word `w` on the slot wires, the private operation `D z w` (or its adjoint). -/
def selFam (D : Cfg L → ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :
    Bool → Cfg (L ⊕ Fin m) → (Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :=
  fun adj y =>
    SlotSim.adjT adj (D (fun l => y (Sum.inl l)) (wordEquivFin m (fun i => y (Sum.inr i))))

omit [Fintype L] [DecidableEq L] [Fintype S] [DecidableEq S] [CompleteSpace R] in
theorem ctrlOK_sec' (x : Cfg (Wire a m r K)) : ctrlOK [(Wire.sec, true)] x = x Wire.sec := by
  simp [ctrlOK]

/-- **One embedded instruction in selected form**: for a sector-controlled oracle call, the
selected native semantics of the embedded instruction is the label-selected instruction. -/
theorem evalSel_embW (UJg : List (Gate (Fin a ⊕ S)))
    (D : Cfg L → ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (i : Instr (Wire a m r K))
    (hi : SecOK (wireRel a m r K) i) :
    evalSel (selRel a m r K L) UJg selSW (selFam D) (embW i) =
      evalS (P := Reg S R) (UJop (R := R) UJg) D i := by
  cases i with
  | gate g => exact (evalS_gate _ _ g).symm
  | uj cs adj =>
      simp only [SecOK, GateNative.wireRel_sec] at hi
      subst hi
      simp only [embW, List.map_cons, List.map_nil, evalSel, selOracle, evalS, SlotSim.evalT,
        oracleOp]
      rw [GateODE.localOp_localOp' Sum.inl_injective anc_injective (selRel a m r K L).anc
        (selRel a m r K L).anc_inj (fun _ => rfl)]
      apply localOp_congr
      intro z
      set z' := clearCfg (selRel a m r K L).anc z
      have h1 : clearCfg Wire.anc (fun w => z' (Sum.inl w)) Wire.sec = z' (Sum.inl Wire.sec) :=
        clearCfg_apply_out _ _ Wire.sec (fun i h => by cases h)
      simp only [ctrlOK_sec', h1]
      rfl
  | priv cs adj =>
      simp only [SecOK, GateNative.wireRel_sec] at hi
      subst hi
      simp only [embW, List.map_cons, List.map_nil, evalSel, selOracle, evalS, SlotSim.evalT,
        SlotSim.slotOracle]
      rw [GateODE.localOp_localOp' Sum.inl_injective anc_injective (selRel a m r K L).anc
        (selRel a m r K L).anc_inj (fun _ => rfl)]
      apply localOp_congr
      intro z
      set z' := clearCfg (selRel a m r K L).anc z
      have h1 : clearCfg Wire.anc (fun w => z' (Sum.inl w)) Wire.sec = z' (Sum.inl Wire.sec) :=
        clearCfg_apply_out _ _ Wire.sec (fun i h => by cases h)
      have h2 : labelOf (clearCfg (Sum.inl : Wire a m r K → SW a m r K L) z') =
          fun l => z' (Sum.inr l) :=
        funext (fun l => clearCfg_apply_out _ _ _ (fun w h => by cases h))
      have h3 : GateCircuit.Sim.slotIdx (clearCfg Wire.anc (fun w => z' (Sum.inl w))) =
          wordEquivFin m (fun i => z' (Sum.inl (Wire.slot i))) := by
        unfold GateCircuit.Sim.slotIdx GateCircuit.Sim.slotOf
        congr 1
        funext i
        exact clearCfg_apply_out _ _ _ (fun j h => by cases h)
      simp only [ctrlOK_sec', h1, h2, h3]
      rfl

/-- **The selected native semantics of the embedded simulator is the label-selected
simulator.** -/
theorem prodOps_evalSel_embW (UJg : List (Gate (Fin a ⊕ S)))
    (D : Cfg L → ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (l : List (Instr (Wire a m r K)))
    (hl : ∀ i ∈ l, SecOK (wireRel a m r K) i) :
    prodOps (V := SW a m r K L) (R := Reg S R)
      (evalSel (selRel a m r K L) UJg selSW (selFam D)) (l.map embW) =
      runS (P := Reg S R) (UJop (R := R) UJg) D l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [List.map_cons, prodOps, ih (fun j hj => hl j (List.mem_cons_of_mem i hj)),
        evalSel_embW UJg D i (hl i List.mem_cons_self)]
      rfl

end Semantics

/-! ### The full-output error on a clean released embedding -/

section Error

variable {V S X' Z Sel Y J : Type*} [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S]
  [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Sel] [DecidableEq Sel]
  [Fintype Y] [DecidableEq Y] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {B : Type*} [Fintype B]

/-- **The full-output error of a native circuit on a clean released embedding** of a direct sum
`E = ⊕_B (Reg S R)` of payload copies (the released `GateNative.hcirc_error` for one copy): if
the released circuit, with `U_J` from its gates and the selected private operation, is within
`ε₀` of `U` on an isometric released embedding `ι`, the native circuit is within
`ε₀ + 4 ζ nPriv l` of `U` on `ι` with every added work wire clean. -/
theorem hcirc_error_gen (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (hnd : nd.Public) (ar : Arith (NB Sel (Fin a ⊕ S) Z))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hDu : ∀ w, IsUnitary (Dfam false w)) (hDadj : ∀ w, Dfam true w = (Dfam false w)†)
    (hN : NativeOK prim nd (selOp (Dfam false)))
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc)
    (ι : ODEJointLCU.BranchSpace B (Reg S R) →L[ℂ] Reg V (Reg S R)) (hι : ∀ ψ, ‖ι ψ‖ = ‖ψ‖)
    (U : ODEJointLCU.BranchSpace B (Reg S R) →L[ℂ] ODEJointLCU.BranchSpace B (Reg S R))
    (Orel : Reg V (Reg S R) →L[ℂ] Reg V (Reg S R))
    (hO : prodOps (V := V) (R := Reg S R) (evalSel ρ UJg sw Dfam) l = Orel) {ε₀ : ℝ}
    (hrel : ‖Orel ∘L ι - ι ∘L U‖ ≤ ε₀) :
    ‖nrun prim (hcirc (X' := X') ρ sw UJg nd ar l) ∘L
        ((cleanEmb : Reg (V ⊕ S) R →L[ℂ] Reg ((V ⊕ S) ⊕ (XW Z ar.bT ar.bP ar.A ⊕ X')) R) ∘L
          fl ∘L ι) -
      ((cleanEmb : Reg (V ⊕ S) R →L[ℂ] Reg ((V ⊕ S) ⊕ (XW Z ar.bT ar.bP ar.A ⊕ X')) R) ∘L
          fl ∘L ι) ∘L U‖ ≤ ε₀ + (nPriv l : ℝ) * (4 * ζ) := by
  have hA := hcirc_approx (X' := X') prim hprim ρ sw UJg hUJ nd hnd ar hζ har Dfam hDu hDadj hN
    l hv
  rw [hO] at hA
  have hε₀ : 0 ≤ ε₀ := le_trans (norm_nonneg (Orel ∘L ι - ι ∘L U)) hrel
  have hδ : 0 ≤ (nPriv l : ℝ) * (4 * ζ) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro ψ
  set C := nrun prim (hcirc (X' := X') ρ sw UJg nd ar l) with hC
  set φ : Reg (V ⊕ S) R := fl (ι ψ) with hφ
  have e1 : (C ∘L ((cleanEmb : Reg (V ⊕ S) R →L[ℂ] Reg ((V ⊕ S) ⊕
        (XW Z ar.bT ar.bP ar.A ⊕ X')) R) ∘L fl ∘L ι) -
      ((cleanEmb : Reg (V ⊕ S) R →L[ℂ] Reg ((V ⊕ S) ⊕ (XW Z ar.bT ar.bP ar.A ⊕ X')) R) ∘L
        fl ∘L ι) ∘L U) ψ =
      (C (cleanEmb φ) - liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ)) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L U) ψ)) := by
    have h1 : liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ) =
        cleanEmb (conj Orel φ) := by
      rw [← comp_apply, liftB_cleanEmb, comp_apply]
    rw [h1, hφ, conj_fl]
    simp only [sub_apply, comp_apply, map_sub]
    abel
  have hφn : ‖φ‖ = ‖ψ‖ := by rw [hφ, norm_fl, hι]
  rw [e1]
  calc ‖C (cleanEmb φ) - liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L U) ψ))‖
      ≤ ‖C (cleanEmb φ) - liftB (X := XW Z ar.bT ar.bP ar.A ⊕ X') (conj Orel) (cleanEmb φ)‖ +
        ‖cleanEmb (X := XW Z ar.bT ar.bP ar.A ⊕ X') (fl ((Orel ∘L ι - ι ∘L U) ψ))‖ :=
        norm_add_le _ _
    _ ≤ (nPriv l : ℝ) * (4 * ζ) * ‖ψ‖ + ε₀ * ‖ψ‖ := by
        gcongr
        · have := hA _ (supp_cleanEmb φ)
          rwa [norm_cleanEmb, hφn] at this
        · rw [norm_cleanEmb, norm_fl]
          exact ((Orel ∘L ι - ι ∘L U).le_opNorm ψ).trans
            (mul_le_mul_of_nonneg_right hrel (norm_nonneg _))
    _ = (ε₀ + (nPriv l : ℝ) * (4 * ζ)) * ‖ψ‖ := by ring

end Error

/-! ### The native circuit and the lemma -/

section Lemma

variable {L : Type*} [Fintype L] [DecidableEq L]
variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native label-selected circuit** for target accuracy `ε`: the released slot-selected
simulator for the common time `τ` and accuracy `ε/4`, embedded on the label-selected register,
with every instruction replaced by its native macro (`U_J` from `UJg`, the private calls by the
compute circuit and the arithmetic of `nd`, `ar`, selected by the label and slot wires). -/
def nativeSel (a m : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp (L ⊕ Fin m) (Fin a ⊕ S) Z Y J) (ar : Arith (NB (L ⊕ Fin m) (Fin a ⊕ S) Z)) :
    List (NInstr (HW (SW a m (simR Q τ qbar (ε / 4)) (a + m + 2 * simR Q τ qbar (ε / 4)) L) S
      Empty Z ar.bT ar.bP ar.A) Y J) :=
  hcirc (selRel _ _ _ _ L) selSW UJg nd ar ((SlotSim.simCircuitT a τ Q qbar (ε / 4) m).map embW)

/-- **The clean-input space of the native register**: a label and a payload vector, every
simulator wire and every added work wire clear. -/
def selN (a m r K : ℕ) (bT bP A : ℕ) :
    ODEJointLCU.BranchSpace (Cfg L) (Reg S R) →L[ℂ]
      Reg ((SW a m r K L ⊕ S) ⊕ (XW Z bT bP A ⊕ Empty)) R :=
  (cleanEmb : Reg (SW a m r K L ⊕ S) R →L[ℂ] Reg ((SW a m r K L ⊕ S) ⊕ (XW Z bT bP A ⊕ Empty)) R)
    ∘L fl ∘L selE

/-- The clean-input space is isometric. -/
theorem norm_selN (a m r K : ℕ) (bT bP A : ℕ)
    (φ : ODEJointLCU.BranchSpace (Cfg L) (Reg S R)) :
    ‖selN (L := L) (S := S) (Z := Z) (R := R) a m r K bT bP A φ‖ = ‖φ‖ := by
  rw [selN, comp_apply, comp_apply, norm_cleanEmb, norm_fl]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr selE_isometry φ

/-- **Lemma `ode:lem:gate-select` with native private calls** (the native circuit of the
lemma, before finite-set synthesis).

The circuit `nativeSel a m τ Q qbar ε UJg nd ar` (`τ = α T`) depends only on the public numbers,
the gates of `U_J` and the native data `nd`, `ar`. Let the label- and slot-selected private
operations `D z j` be given natively by the compute circuit `V` of `nd` on the label wires, the
slot wires, the private register and scratch (`NativeOK` for `selFam D`), with arithmetic
accuracy `ζ` (`ArithOK`). Under the hypotheses of `gate_select_certified` at accuracy `ε/2`
(the clock promises, the subdivision `steps τ (ε/12) ≤ 2^m`, the freezing condition
`16 (βH + R βD) T² ≤ ε 2^m` and the integrated sample-error certificate `sampleErr z ≤ ε/32`) and
the arithmetic budget `48 d ζ ≤ ε`, the native circuit consists of valid instructions, makes
exactly `12 d` times the primitive calls of `V`, uses at most
`200 (d+1)(a+m+r+1) + 84 d C_J + 6 d (2 |V| + 2 |arith| + 2 bP + bT + 1)` elementary gates
(`C_J = |UJg|`, `d` the filter degree for the common time `τ = α T`), has
`|S| + (2a + 3m + 6r + 3 + |L|) + (|Z| + bT + bP + A + 3)` qubits, and for every family of
propagators `U z` of the branch paths its full output on the clean-input space `selN` is within
`ε` of the controlled direct sum `∑_z |z⟩⟨z| ⊗ U z (T - v z)`. No count depends on the labels;
the work wires `|Z| + bT + bP + A + 3` added to the released register do not depend on `d`. -/
theorem native_gate_select (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (L ⊕ Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (L ⊕ Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D : Cfg L → ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (selFam D false)))
    (Hp Dp : ℝ → Reg S R →L[ℂ] Reg S R) (k v : Cfg L → ℝ)
    (X : Cfg L → ℕ → Reg S R →L[ℂ] Reg S R) (T α τ Rk βH βD Q qbar ε : ℝ) (hT : 0 < T)
    (hα : 0 < α) (hτ : α * T = τ) (hβH : 0 ≤ βH) (hβD : 0 ≤ βD) (hQ : 1 ≤ Q) (hqQ : qbar ≤ Q)
    (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps τ (ε / 12) ≤ 2 ^ m)
    (hFreeze : 16 * (βH + Rk * βD) * T ^ 2 ≤ ε * 2 ^ m)
    (hk : ∀ z, |k z| ≤ Rk) (hv0 : ∀ z, 0 ≤ v z) (hvT : ∀ z, v z ≤ T)
    (hD : ∀ z, ∀ j < 2 ^ m, IsUnitary (D z j))
    (hClock : ∀ z, ∀ j < 2 ^ m, GateODE.ClockPromise (P := Reg S R) (a := a) (UJop (R := R) UJg)
      (D z j)
      ((((T - v z) / τ : ℝ) : ℂ) • X z j) Q qbar)
    (hX : ∀ z, ∀ j < 2 ^ m, star (X z j) = X z j) (hXn : ∀ z, ∀ j < 2 ^ m, ‖X z j‖ ≤ α)
    (hHp : ∀ t ∈ Set.Icc 0 T, star (Hp t) = Hp t) (hDp : ∀ t ∈ Set.Icc 0 T, star (Dp t) = Dp t)
    (hLipH : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Hp t - Hp t'‖ ≤ βH * |t - t'|)
    (hLipD : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ‖Dp t - Dp t'‖ ≤ βD * |t - t'|)
    (hCert : ∀ z, sampleErr Hp Dp k v X T m z ≤ ε / 32)
    (hζε : 48 * (fDeg Q τ qbar (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeSel (L := L) a m τ Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ c : J → Bool, nCallsN c (nativeSel (L := L) a m τ Q qbar ε UJg nd ar) =
      12 * fDeg Q τ qbar (ε / 4) * nCallsN c nd.V) ∧
    nGatesN (nativeSel (L := L) a m τ Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q τ qbar (ε / 4) + 1) * (a + m + simR Q τ qbar (ε / 4) + 1) +
        84 * fDeg Q τ qbar (ε / 4) * UJg.length +
        6 * fDeg Q τ qbar (ε / 4) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (SW a m (simR Q τ qbar (ε / 4))
        (a + m + 2 * simR Q τ qbar (ε / 4)) L) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q τ qbar (ε / 4) + 3 + Fintype.card L) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    (fDeg Q τ qbar (ε / 4) : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (12 / ε))) ∧
    2 * fDeg Q τ qbar (ε / 4) + 2 ≤ 2 ^ simR Q τ qbar (ε / 4) ∧
    2 ^ simR Q τ qbar (ε / 4) ≤ 4 * (fDeg Q τ qbar (ε / 4) + 1) ∧
    (∀ z, ∃ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 ∧
      TimeDependent.SolvesOn (branchPath Hp Dp k v z) U 0 (T - v z)) ∧
    ∀ U : Cfg L → ℝ → Reg S R →L[ℂ] Reg S R, (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath Hp Dp k v z) (U z) 0 (T - v z)) →
      ‖nrun prim (nativeSel (L := L) a m τ Q qbar ε UJg nd ar) ∘L
          selN (L := L) (S := S) (Z := Z) (R := R) a m (simR Q τ qbar (ε / 4))
            (a + m + 2 * simR Q τ qbar (ε / 4)) ar.bT ar.bP ar.A -
        selN (L := L) (S := S) (Z := Z) (R := R) a m (simR Q τ qbar (ε / 4))
            (a + m + 2 * simR Q τ qbar (ε / 4)) ar.bT ar.bP ar.A ∘L
          WeightedClock.diagonal (fun z => U z (T - v z))‖ ≤ ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  have hC' : TimeSchedule.steps τ (ε / 2 / 6) ≤ 2 ^ m := by
    rw [show ε / 2 / 6 = ε / 12 by ring]
    exact hCayley
  have hF' : 8 * (βH + Rk * βD) * T ^ 2 ≤ ε / 2 * 2 ^ m := by linarith
  have hCert' : ∀ z, sampleErr Hp Dp k v X T m z ≤ ε / 2 / 16 := by
    intro z
    rw [show ε / 2 / 16 = ε / 32 by ring]
    exact hCert z
  obtain ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, hex, herr⟩ :=
    gate_select_certified (P := Reg S R) a m (UJop (R := R) UJg) D Hp Dp k v X T α τ Rk βH βD Q
      qbar (ε / 2) hT hα hτ hβH hβD hQ hqQ hε2 hε21 hC' hF' hk hv0 hvT hUJu hD hClock hX hXn hHp
      hDp hLipH hLipD hCert'
  have e4 : ε / 2 / 2 = ε / 4 := by ring
  have hlog : (6 : ℝ) / (ε / 2) = 12 / ε := by
    field_simp
    ring
  rw [e4] at hvalid hP hJ hG hW hdeg hr1 hr2 herr
  rw [hlog] at hdeg
  have hsec : ∀ i ∈ SlotSim.simCircuitT a τ Q qbar (ε / 4) m,
      SecOK (wireRel a m (simR Q τ qbar (ε / 4))
        (a + m + 2 * simR Q τ qbar (ε / 4))) i := by
    unfold SlotSim.simCircuitT
    exact secOK_ampI _ _ _ _ _ _
  have hv : ∀ i ∈ (SlotSim.simCircuitT a τ Q qbar (ε / 4) m).map (embW (L := L)),
      i.Valid (selRel a m (simR Q τ qbar (ε / 4))
        (a + m + 2 * simR Q τ qbar (ε / 4)) L).anc := by
    intro i hi
    simp only [List.mem_map] at hi
    obtain ⟨i', hi', rfl⟩ := hi
    exact valid_embW i' (hvalid i' hi')
  have hDu : ∀ w, IsUnitary (selFam (m := m) (S := S) (R := R) D false w) := by
    intro w
    exact hD _ _ (wordEquivFin m (fun i => w (Sum.inr i))).isLt
  have hDadj : ∀ w, selFam (m := m) (S := S) (R := R) D true w =
      (selFam (m := m) (S := S) (R := R) D false w)† := fun _ => rfl
  refine ⟨hcirc_valid _ _ UJg hUJg nd hnd ar har.elem har.classical _ hv, fun c => ?_, ?_, ?_,
    hdeg, hr1, hr2, hex, fun U hU0 hU => ?_⟩
  · rw [nativeSel, hcirc_nCalls, nPriv_embW, hP]
    ring
  · refine (hcirc_nGates _ _ UJg hUJg nd ar _).trans ?_
    rw [nGates_embW, nUJ_embW, nPriv_embW, hP, hJ, mul_one]
    have h84 : 12 * fDeg Q τ qbar (ε / 4) * (7 * UJg.length) =
        84 * fDeg Q τ qbar (ε / 4) * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right (Nat.add_le_add_right hG _) _
  · rw [card_HW, GateSelect.card_SW, card_wire]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have herr' := herr U hU0 hU
    have hO : prodOps (V := SW a m (simR Q τ qbar (ε / 4))
        (a + m + 2 * simR Q τ qbar (ε / 4)) L) (R := Reg S R)
        (evalSel (selRel a m (simR Q τ qbar (ε / 4))
          (a + m + 2 * simR Q τ qbar (ε / 4)) L) UJg selSW (selFam (m := m) D))
        ((SlotSim.simCircuitT a τ Q qbar (ε / 4) m).map embW) =
        runS (P := Reg S R) (UJop (R := R) UJg) D (SlotSim.simCircuitT a τ Q qbar (ε / 4) m) :=
      prodOps_evalSel_embW UJg D _ hsec
    have hι : ∀ φ : ODEJointLCU.BranchSpace (Cfg L) (Reg S R),
        ‖(selE (a := a) (m := m) (r := simR Q τ qbar (ε / 4))
          (K := a + m + 2 * simR Q τ qbar (ε / 4)) (L := L) (P := Reg S R)) φ‖ = ‖φ‖ :=
      fun φ => (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr selE_isometry φ
    have h := hcirc_error_gen (X' := Empty) (B := Cfg L)
      prim hprim (selRel a m (simR Q τ qbar (ε / 4))
        (a + m + 2 * simR Q τ qbar (ε / 4)) L) selSW UJg hUJg nd hnd ar hζ har
      (selFam (m := m) D) hDu hDadj hN _ hv _ hι (WeightedClock.diagonal (fun z => U z (T - v z)))
      _ hO (ε₀ := ε / 2) ?hrel
    case hrel => convert herr' using 1
    rw [nPriv_embW, hP] at h
    have hb : (ε / 2) + ((6 * fDeg Q τ qbar (ε / 4) : ℕ) : ℝ) * (4 * ζ) ≤ ε := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
      linarith
    rw [nativeSel, selN]
    convert h.trans hb using 1

/-- **The inverse of the native selection circuit** (the last sentence of Lemma
`ode:lem:gate-select`): the literal inverse instruction list `ninv (nativeSel …)` (the adjoint of
every gate and the call of the inverse oracle for every primitive call, in reverse order) runs
as the adjoint of the circuit and has the same validity, the same number of elementary gates and
the same number of primitive calls of every kind. Validity of `nativeSel` is the first conclusion
of `native_gate_select`. -/
theorem native_gate_select_inverse (prim : J → Reg Y R →L[ℂ] Reg Y R) (a m : ℕ)
    (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S))) (nd : NativeOp (L ⊕ Fin m) (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB (L ⊕ Fin m) (Fin a ⊕ S) Z))
    (hC : ∀ i ∈ nativeSel (L := L) a m τ Q qbar ε UJg nd ar, i.Valid) :
    nrun prim (ninv (nativeSel (L := L) a m τ Q qbar ε UJg nd ar)) =
      (nrun prim (nativeSel (L := L) a m τ Q qbar ε UJg nd ar))† ∧
    (∀ i ∈ ninv (nativeSel (L := L) a m τ Q qbar ε UJg nd ar), i.Valid) ∧
    nGatesN (ninv (nativeSel (L := L) a m τ Q qbar ε UJg nd ar)) =
      nGatesN (nativeSel (L := L) a m τ Q qbar ε UJg nd ar) ∧
    ∀ c : J → Bool, nCallsN c (ninv (nativeSel (L := L) a m τ Q qbar ε UJg nd ar)) =
      nCallsN c (nativeSel (L := L) a m τ Q qbar ε UJg nd ar) :=
  ⟨nrun_ninv prim _, valid_ninv _ hC, nGatesN_ninv _, fun c => nCallsN_ninv c _⟩

end Lemma

end

end SparseHamiltonian.GateBinarySelect
