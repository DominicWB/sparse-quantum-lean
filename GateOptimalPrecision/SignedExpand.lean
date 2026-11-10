import GateOptimalPrecision.SignedLayout

/-!
# Expanding the private calls of the signed-factor circuit

The private operation of the signed factor is `P = U_B† G U_B` (`gate:eq:factor-private`), where the
known phase `G` multiplies the success states with sign `±` by `ζ_± = (±q + i)/(±q - i)` and the
failure states by `-1`. Section `gate:sec:signed`: "Only the three known middle phases need an
external control. On an inactive branch the unconditional factor and inverse cancel. The adjoint
reverses the middle phase; no controlled opaque `U_B` is needed."

On the attenuated gate register (`attKnown`):

* `attPhaseD`, `attKnown_phase`: `G` is the diagonal operator with these entries, so
  `attKnown_priv`: `P = (liftA U_B)† ∘ dg(attPhaseD) ∘ liftA U_B`;
* `phaseGates`, `gRun_phaseGates`: the sector-controlled `G` is three elementary gates (diagonal
  one-qubit matrices with at most three controls);
* `privExpand`, `run_privExpand`: an unconditional factor call, the three gates (or their literal
  inverses for `P†`) and an unconditional inverse factor call implement the sector-controlled `P`
  (or `P†`) exactly, on every input;
* `ujExpand`, `run_ujExpand`: the sector-controlled attenuated boundary `U_J ∘ R_κ` is the
  sector-controlled flag rotation followed by a sector-controlled call of `U_J`;
* `expandI`, `run_expand`, `expand_counts`, `expand_valid`: the expansion of a released circuit
  whose oracle calls are sector-controlled.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open SignedFactorSimulation (Known)
open SignedFactorSimulation.Known (zetaP zetaM norm_zetaP norm_zetaM)
open scoped InnerProduct InnerProductSpace BigOperators

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The diagonal private phase -/

/-- The entries of the private phase `G` of the attenuated factor. -/
def attPhaseD (f z : Fin a) (q : ℝ) : Cfg (Fin (a + 1)) → ℂ := fun x =>
  if x 0 = false ∧ x f.succ = true then (if x z.succ then zetaM q else zetaP q) else -1

theorem attKnown_phase (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (f z : Fin a)
    {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (q : ℝ) :
    (attKnown UJ hUJ f z h0 h1).phase q = dg (attPhaseD f z q) := by
  ext ψ x
  simp only [Known.phase, Known.spec, Known.plus, Known.minus, attKnown, add_apply, sub_apply,
    smul_apply, one_apply_eq_self, mul_apply_eq_comp, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, dg_apply]
  unfold attProjD attSignD attPhaseD
  by_cases h1 : x 0 = false ∧ x f.succ = true
  · by_cases h2 : x z.succ = true
    · simp only [if_pos h1, if_pos h2]; module
    · simp only [if_pos h1, if_neg h2]; module
  · simp only [if_neg h1]; module

/-- The private operation of the attenuated factor. -/
theorem attKnown_priv (UJ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (f z : Fin a)
    {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1) (q : ℝ) (U : Anc a P →L[ℂ] Anc a P) :
    (attKnown UJ hUJ f z h0 h1).priv q (liftA U) =
      (liftA U)† ∘L dg (attPhaseD f z q) ∘L liftA U := by
  rw [Known.priv, attKnown_phase, mul_def, mul_def]
  exact comp_assoc _ _ _

/-! ### Diagonal gates on basis vectors -/

/-- A diagonal one-qubit matrix `diag(α, β)`. -/
def dmat (α β : ℂ) : Matrix Bool Bool ℂ := fun i j => if i = j then (if i then β else α) else 0

theorem dmat_unitary {α β : ℂ} (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) : UnitaryMat (dmat α β) := by
  have hα' : (starRingEnd ℂ) α * α = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hα]; norm_num
  have hβ' : (starRingEnd ℂ) β * β = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hβ]; norm_num
  constructor
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.one_apply,
      dmat]
    cases i <;> cases j <;> simp [hα', hβ']
  · funext i j
    simp only [Matrix.mul_apply, Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.one_apply,
      dmat]
    have hα'' : α * (starRingEnd ℂ) α = 1 := by rw [mul_comm]; exact hα'
    have hβ'' : β * (starRingEnd ℂ) β = 1 := by rw [mul_comm]; exact hβ'
    cases i <;> cases j <;> simp [hα'', hβ'']

theorem dmat_conjTranspose (α β : ℂ) :
    (dmat α β).conjTranspose = dmat ((starRingEnd ℂ) α) ((starRingEnd ℂ) β) := by
  funext i j
  simp only [Matrix.conjTranspose_apply, dmat]
  cases i <;> cases j <;> simp

theorem gateOp_dmat_bas {W : Type*} [Fintype W] [DecidableEq W] (cs : List (W × Bool)) (t : W)
    (ht : ∀ c ∈ cs, c.1 ≠ t) (α β : ℂ) (y : Cfg W) (q : P) :
    gateOp cs t (dmat α β) (bas y q) =
      (if ctrlOK cs y then (if y t then β else α) else 1) • bas y q := by
  rw [gateOp_bas cs t _ ht]
  by_cases hc : ctrlOK cs y = true
  · rw [if_pos hc, if_pos hc, Fintype.sum_bool]
    cases h : y t
    · rw [show Function.update y t false = y by rw [← h, Function.update_eq_self]]
      simp [dmat]
    · rw [show Function.update y t true = y by rw [← h, Function.update_eq_self]]
      simp [dmat]
  · rw [if_neg hc, if_neg hc, one_smul]

/-! ### Oracle calls on basis vectors -/

omit [CompleteSpace P] in
theorem put_smul {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (c : ℂ) (φ : Reg A P) :
    GateODE.put ι hι x (c • φ) = c • GateODE.put ι hι x φ := by
  simp only [GateODE.put, Pi.single_smul, WithLp.toLp_smul, map_smul]

omit [CompleteSpace P] in
theorem put_add {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
    {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (φ φ' : Reg A P) :
    GateODE.put ι hι x (φ + φ') = GateODE.put ι hι x φ + GateODE.put ι hι x φ' := by
  simp only [GateODE.put, Pi.single_add, WithLp.toLp_add, map_add]

theorem ctrlOK_sec' (y : Cfg (Wire (a + 1) m r K)) :
    ctrlOK [(Wire.sec, true)] y = y Wire.sec := by
  simp [ctrlOK]

theorem clearCfg_anc_sec (y : Cfg (Wire (a + 1) m r K)) :
    clearCfg (Wire.anc (a := a + 1) (m := m) (r := r) (K := K)) y Wire.sec = y Wire.sec :=
  GateODE.overwrite_apply_out _ y _ Wire.sec (fun _ h => by cases h)

theorem overwrite_anc_self (y : Cfg (Wire (a + 1) m r K)) :
    overwrite (Wire.anc (a := a + 1) (m := m) (r := r) (K := K)) y (fun i => y (Wire.anc i)) = y :=
  joinCfg_self anc_injective y

theorem oracleOp_sec_bas (O : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) (y : Cfg (Wire (a + 1) m r K))
    (q : P) :
    oracleOp Wire.anc anc_injective [(Wire.sec, true)] O (bas y q) =
      if y Wire.sec then GateODE.put Wire.anc anc_injective y (O (bas (fun i => y (Wire.anc i)) q))
      else bas y q := by
  rw [oracleOp, GateNative.localOp_bas, ctrlOK_sec', clearCfg_anc_sec]
  split_ifs
  · rfl
  · rw [one_apply_eq_self, GateNative.put_bas, overwrite_anc_self]

theorem oracleOp_dg_bas (d : Cfg (Fin (a + 1)) → ℂ) (y : Cfg (Wire (a + 1) m r K)) (q : P) :
    oracleOp Wire.anc anc_injective [(Wire.sec, true)] (dg d) (bas y q) =
      (if y Wire.sec then d (fun i => y (Wire.anc i)) else 1) • bas y q := by
  rw [oracleOp_sec_bas]
  split_ifs
  · rw [dg_bas, put_smul, GateNative.put_bas, overwrite_anc_self]
  · rw [one_smul]

/-! ### The phase gates -/

/-- **The three phase gates**: `ζ_±` on success (`wire 0 = 0`, `wire f+1 = 1`) by the sign
`wire z+1`, and `-1` on the two failure cases, all controlled by the sector wire. -/
def phaseGates (f z : Fin a) (q : ℝ) : List (Gate (Wire (a + 1) m r K)) :=
  [⟨[(Wire.sec, true), (Wire.anc 0, false), (Wire.anc f.succ, true)], Wire.anc z.succ,
      dmat (zetaP q) (zetaM q)⟩,
    ⟨[(Wire.sec, true)], Wire.anc 0, dmat 1 (-1)⟩,
    ⟨[(Wire.sec, true), (Wire.anc 0, false)], Wire.anc f.succ, dmat (-1) 1⟩]

theorem phaseGates_length (f z : Fin a) (q : ℝ) :
    (phaseGates (m := m) (r := r) (K := K) f z q).length = 3 := rfl

theorem phaseGates_ok {f z : Fin a} (hfz : f ≠ z) (q : ℝ) :
    ∀ g ∈ phaseGates (m := m) (r := r) (K := K) f z q, GateOK 3 g := by
  intro g hg
  simp only [phaseGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · refine ⟨by simp, ?_, dmat_unitary (norm_zetaP q)
      (norm_zetaM q)⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp
    · simp only [ne_eq, Wire.anc.injEq]; exact (Fin.succ_ne_zero z).symm
    · simp only [ne_eq, Wire.anc.injEq, Fin.succ_inj]; exact hfz
  · refine ⟨by simp, ?_, dmat_unitary (by simp) (by simp)⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    simp
  · refine ⟨by simp, ?_, dmat_unitary (by simp) (by simp)⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp
    · simp only [ne_eq, Wire.anc.injEq]; exact (Fin.succ_ne_zero f).symm

/-- **The sector-controlled private phase is three gates.** -/
theorem gRun_phaseGates {f z : Fin a} (hfz : f ≠ z) (q : ℝ) :
    gRun (Q := P) (phaseGates (m := m) (r := r) (K := K) f z q) =
      oracleOp Wire.anc anc_injective [(Wire.sec, true)] (dg (attPhaseD f z q)) := by
  have ht1 : ∀ c ∈ [(Wire.sec, true), (Wire.anc 0, false), (Wire.anc f.succ, true)],
      c.1 ≠ (Wire.anc z.succ : Wire (a + 1) m r K) := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp
    · simp only [ne_eq, Wire.anc.injEq]; exact (Fin.succ_ne_zero z).symm
    · simp only [ne_eq, Wire.anc.injEq, Fin.succ_inj]; exact hfz
  have ht2 : ∀ c ∈ [((Wire.sec : Wire (a + 1) m r K), true)], c.1 ≠ Wire.anc 0 := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl
    simp
  have ht3 : ∀ c ∈ [((Wire.sec : Wire (a + 1) m r K), true), (Wire.anc 0, false)],
      c.1 ≠ Wire.anc f.succ := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · simp
    · simp only [ne_eq, Wire.anc.injEq]; exact (Fin.succ_ne_zero f).symm
  apply ext_bas_clm
  intro y p
  rw [oracleOp_dg_bas]
  simp only [phaseGates, gRun_cons, gRun_nil, comp_apply, one_apply_eq_self, Gate.op]
  simp only [gateOp_dmat_bas _ _ ht1, gateOp_dmat_bas _ _ ht2, gateOp_dmat_bas _ _ ht3, map_smul,
    smul_smul]
  congr 1
  simp only [ctrlOK_cons, ctrlOK_nil, Bool.and_true, beq_iff_eq]
  unfold attPhaseD
  cases hs : y Wire.sec <;> cases h0 : y (Wire.anc 0) <;> cases hf : y (Wire.anc f.succ) <;>
    cases hz : y (Wire.anc z.succ) <;> simp [h0, hf, hz]

/-! ### The expanded private call -/

/-- **The expanded private call**: an unconditional factor call, the three phase gates (or their
literal inverses), and an unconditional inverse factor call. -/
def privExpand (f z : Fin a) (q : ℝ) (adj : Bool) : List (Instr (Wire (a + 1) m r K)) :=
  Instr.priv [] false :: (ofGates (if adj then gInv (phaseGates f z q) else phaseGates f z q) ++
    [Instr.priv [] true])

theorem oracleOp_nil (O : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) :
    oracleOp (Wire.anc (a := a + 1) (m := m) (r := r) (K := K)) anc_injective [] O =
      localOp Wire.anc anc_injective (fun _ => O) := by
  unfold oracleOp
  simp only [ctrlOK_nil, if_true]

theorem oracleOp_conj (U G : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) (hU : IsUnitary U) :
    localOp (Wire.anc (a := a + 1) (m := m) (r := r) (K := K)) anc_injective (fun _ => U†) ∘L
        oracleOp Wire.anc anc_injective [(Wire.sec, true)] G ∘L
        localOp Wire.anc anc_injective (fun _ => U) =
      oracleOp Wire.anc anc_injective [(Wire.sec, true)] (U† ∘L G ∘L U) := by
  unfold oracleOp
  rw [localOp_comp, localOp_comp]
  congr 1
  funext x
  split_ifs
  · rfl
  · rw [one_comp', unitary_adj_comp hU]

/-- **The expanded private call is exact.** -/
theorem run_privExpand (UJ U : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) (hU : IsUnitary U)
    {f z : Fin a} (hfz : f ≠ z) (q : ℝ) (adj : Bool) :
    run (simSem (m := m) (r := r) (K := K) UJ U) (privExpand f z q adj) =
      oracleOp Wire.anc anc_injective [(Wire.sec, true)]
        (if adj then (U† ∘L dg (attPhaseD f z q) ∘L U)† else U† ∘L dg (attPhaseD f z q) ∘L U) := by
  rw [privExpand, run_cons, run_append, run_ofGates, run_singleton]
  have e1 : (Instr.priv [] false).eval (simSem (m := m) (r := r) (K := K) UJ U) =
      localOp Wire.anc anc_injective (fun _ => U) := by
    change oracleOp Wire.anc anc_injective [] (if false then U† else U) = _
    rw [if_neg Bool.false_ne_true, oracleOp_nil]
  have e2 : (Instr.priv [] true).eval (simSem (m := m) (r := r) (K := K) UJ U) =
      localOp Wire.anc anc_injective (fun _ => U†) := by
    change oracleOp Wire.anc anc_injective [] (if true then U† else U) = _
    rw [if_pos rfl, oracleOp_nil]
  rw [e1, e2]
  cases adj
  · simp only [Bool.false_eq_true, if_false]
    rw [gRun_phaseGates hfz q, comp_assoc, oracleOp_conj U _ hU]
  · simp only [if_true]
    rw [gRun_gInv, gRun_phaseGates hfz q, oracleOp_adjoint, comp_assoc, oracleOp_conj U _ hU]
    congr 1
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, comp_assoc]

/-! ### The expanded boundary call -/

/-- The sector-controlled flag rotation (or its inverse). -/
def rotGate (κ : ℝ) (adj : Bool) : Gate (Wire (a + 1) m r K) :=
  ⟨[(Wire.sec, true)], Wire.anc 0, if adj then (rotMat κ).conjTranspose else rotMat κ⟩

/-- The expanded attenuated boundary call: the flag rotation and a call of `U_J`. -/
def ujExpand (κ : ℝ) (adj : Bool) : List (Instr (Wire (a + 1) m r K)) :=
  if adj then [Instr.uj [(Wire.sec, true)] true, Instr.gate (rotGate κ true)]
  else [Instr.gate (rotGate κ false), Instr.uj [(Wire.sec, true)] false]

theorem overwrite_anc_update (y : Cfg (Wire (a + 1) m r K)) (b : Bool) :
    overwrite Wire.anc y (Function.update (fun i => y (Wire.anc i)) 0 b) =
      Function.update y (Wire.anc (a := a + 1) (m := m) (r := r) (K := K) 0) b := by
  funext w
  by_cases hw : ∃ i, Wire.anc i = w
  · obtain ⟨i, rfl⟩ := hw
    rw [GateODE.overwrite_apply_ι anc_injective]
    by_cases hi : i = 0
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne (fun h => hi (anc_injective h))]
  · push Not at hw
    rw [GateODE.overwrite_apply_out _ _ _ _ hw, Function.update_of_ne (fun h => hw 0 h.symm)]

theorem oracleOp_gate0 (u : Matrix Bool Bool ℂ) :
    oracleOp (Wire.anc (a := a + 1) (m := m) (r := r) (K := K)) anc_injective [(Wire.sec, true)]
        (gateOp (Q := P) [] 0 u) =
      gateOp [(Wire.sec, true)] (Wire.anc 0) u := by
  apply ext_bas_clm
  intro y p
  rw [oracleOp_sec_bas, gateOp_bas [(Wire.sec, true)] (Wire.anc 0) u (by simp) y p, ctrlOK_sec']
  split_ifs with hs
  · rw [gateOp_bas [] (0 : Fin (a + 1)) u (by simp), ctrlOK_nil, if_pos rfl, Fintype.sum_bool,
      Fintype.sum_bool, put_add, put_smul, put_smul, GateNative.put_bas, GateNative.put_bas,
      overwrite_anc_update, overwrite_anc_update]
  · rfl

theorem eval_gate {D₁ D₂ : Anc (a + 1) P →L[ℂ] Anc (a + 1) P} (g : Gate (Wire (a + 1) m r K)) :
    (Instr.gate g).eval (simSem D₁ D₂) = gateOp g.cs g.t g.u := rfl

theorem eval_uj_sec (D₁ D₂ : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) (adj : Bool) :
    (Instr.uj [(Wire.sec, true)] adj : Instr (Wire (a + 1) m r K)).eval (simSem D₁ D₂) =
      oracleOp Wire.anc anc_injective [(Wire.sec, true)] (if adj then D₁† else D₁) := rfl

theorem eval_priv_sec (D₁ D₂ : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) (adj : Bool) :
    (Instr.priv [(Wire.sec, true)] adj : Instr (Wire (a + 1) m r K)).eval (simSem D₁ D₂) =
      oracleOp Wire.anc anc_injective [(Wire.sec, true)] (if adj then D₂† else D₂) := rfl

theorem oracleOp_sec_comp (A B : Anc (a + 1) P →L[ℂ] Anc (a + 1) P) :
    oracleOp (Wire.anc (a := a + 1) (m := m) (r := r) (K := K)) anc_injective
      [(Wire.sec, true)] (A ∘L B) =
      oracleOp Wire.anc anc_injective [(Wire.sec, true)] A ∘L
        oracleOp Wire.anc anc_injective [(Wire.sec, true)] B := by
  unfold oracleOp
  rw [localOp_comp]
  congr 1
  funext x
  split_ifs
  · rfl
  · rw [one_comp']

/-- **The expanded attenuated boundary call is exact.** -/
theorem run_ujExpand (UJ : Anc a P →L[ℂ] Anc a P) (V : Anc (a + 1) P →L[ℂ] Anc (a + 1) P)
    (κ : ℝ) (adj : Bool) :
    run (simSem (m := m) (r := r) (K := K) (liftA UJ) V) (ujExpand κ adj) =
      oracleOp Wire.anc anc_injective [(Wire.sec, true)]
        (if adj then (attUJ UJ κ)† else attUJ UJ κ) := by
  cases adj
  · simp only [ujExpand, Bool.false_eq_true, if_false]
    rw [run_cons, run_singleton, eval_gate, eval_uj_sec, attUJ, oracleOp_sec_comp, flagRot,
      oracleOp_gate0]
    simp only [rotGate, Bool.false_eq_true, if_false]
  · simp only [ujExpand, if_true]
    rw [run_cons, run_singleton, eval_gate, eval_uj_sec, attUJ, adjoint_comp, oracleOp_sec_comp,
      flagRot, gateOp_adjoint, oracleOp_gate0, liftA_adjoint]
    simp only [rotGate, if_true]

/-! ### The expanded circuit -/

/-- The expansion of one released instruction. -/
def expandI (f z : Fin a) (q κ : ℝ) : Instr (Wire (a + 1) m r K) → List (Instr (Wire (a + 1) m r K))
  | .gate g => [.gate g]
  | .uj _ adj => ujExpand κ adj
  | .priv _ adj => privExpand f z q adj

/-- **The expanded circuit is exact**: run with `U_J` and `U_B` on the last `a` ancilla wires, it is
the released circuit run with the attenuated boundary `U_J ∘ R_κ` and the private operation
`U_B† G U_B`. -/
theorem run_expand (UJ U : Anc a P →L[ℂ] Anc a P) (hU : IsUnitary U) {f z : Fin a} (hfz : f ≠ z)
    (q κ : ℝ) (l : List (Instr (Wire (a + 1) m r K)))
    (hl : ∀ i ∈ l, GateNative.SecOK (GateNative.wireRel (a + 1) m r K) i) :
    run (simSem (liftA UJ) (liftA U)) (l.flatMap (expandI f z q κ)) =
      run (simSem (attUJ UJ κ) ((liftA U)† ∘L dg (attPhaseD f z q) ∘L liftA U)) l := by
  induction l with
  | nil => exact run_nil _
  | cons i l ih =>
      rw [List.flatMap_cons, run_append, run_cons,
        ih (fun j hj => hl j (List.mem_cons_of_mem i hj))]
      have hi := hl i List.mem_cons_self
      have key : run (simSem (liftA UJ) (liftA U)) (expandI f z q κ i) =
          i.eval (simSem (attUJ UJ κ) ((liftA U)† ∘L dg (attPhaseD f z q) ∘L liftA U)) := by
        cases i with
        | gate g =>
            change run (simSem (liftA UJ) (liftA U)) [Instr.gate g] = _
            rw [run_singleton, eval_gate, eval_gate]
        | uj cs adj =>
            change cs = [(Wire.sec, true)] at hi
            subst hi
            change run (simSem (liftA UJ) (liftA U)) (ujExpand κ adj) = _
            rw [run_ujExpand, eval_uj_sec]
        | priv cs adj =>
            change cs = [(Wire.sec, true)] at hi
            subst hi
            change run (simSem (liftA UJ) (liftA U)) (privExpand f z q adj) = _
            rw [run_privExpand _ _ (liftA_isUnitary hU) hfz, eval_priv_sec]
      rw [key]

theorem expandI_counts (f z : Fin a) (q κ : ℝ) (i : Instr (Wire (a + 1) m r K)) :
    nPriv (expandI f z q κ i) = 2 * nPriv [i] ∧ nUJ (expandI f z q κ i) = nUJ [i] ∧
      nGates (expandI f z q κ i) = nGates [i] + nUJ [i] + 3 * nPriv [i] := by
  cases i with
  | gate g => exact ⟨rfl, rfl, rfl⟩
  | uj cs adj => cases adj <;> exact ⟨rfl, rfl, rfl⟩
  | priv cs adj => cases adj <;> exact ⟨rfl, rfl, rfl⟩

theorem cons_counts (i : Instr (Wire (a + 1) m r K)) (l : List (Instr (Wire (a + 1) m r K))) :
    nPriv (i :: l) = nPriv [i] + nPriv l ∧ nUJ (i :: l) = nUJ [i] + nUJ l ∧
      nGates (i :: l) = nGates [i] + nGates l :=
  ⟨nPriv_append [i] l, nUJ_append [i] l, nGates_append [i] l⟩

/-- The counts of the expanded circuit: `2 nPriv` factor calls, `nUJ` boundary calls and
`nGates + nUJ + 3 nPriv` elementary gates. -/
theorem expand_counts (f z : Fin a) (q κ : ℝ) (l : List (Instr (Wire (a + 1) m r K))) :
    nPriv (l.flatMap (expandI f z q κ)) = 2 * nPriv l ∧
      nUJ (l.flatMap (expandI f z q κ)) = nUJ l ∧
      nGates (l.flatMap (expandI f z q κ)) = nGates l + nUJ l + 3 * nPriv l := by
  induction l with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i l ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨e1, e2, e3⟩ := expandI_counts f z q κ i
      obtain ⟨c1, c2, c3⟩ := cons_counts i l
      rw [List.flatMap_cons, nPriv_append, nUJ_append, nGates_append, h1, h2, h3, e1, e2, e3,
        c1, c2, c3]
      refine ⟨by ring, rfl, by ring⟩

theorem expand_valid {f z : Fin a} (hfz : f ≠ z) (q : ℝ) {κ : ℝ} (h0 : 0 ≤ κ) (h1 : κ ≤ 1)
    (l : List (Instr (Wire (a + 1) m r K))) (hl : ∀ i ∈ l, i.Valid Wire.anc) :
    ∀ i ∈ l.flatMap (expandI f z q κ), i.Valid Wire.anc := by
  intro i hi
  rw [List.mem_flatMap] at hi
  obtain ⟨j, hj, hij⟩ := hi
  have hjv := hl j hj
  have hpriv : (Instr.priv [] false : Instr (Wire (a + 1) m r K)).Valid Wire.anc ∧
      (Instr.priv [] true : Instr (Wire (a + 1) m r K)).Valid Wire.anc :=
    ⟨⟨by simp, by simp⟩, ⟨by simp, by simp⟩⟩
  have hrot : ∀ adj, (Instr.gate (rotGate (a := a) (m := m) (r := r) (K := K) κ adj)).Valid
      Wire.anc := by
    intro adj
    refine ⟨by simp [rotGate], by simp [rotGate], ?_⟩
    cases adj
    · exact rotMat_unitary h0 h1
    · simp only [rotGate, if_true]
      exact ⟨by rw [Matrix.conjTranspose_conjTranspose]; exact (rotMat_unitary h0 h1).2,
        by rw [Matrix.conjTranspose_conjTranspose]; exact (rotMat_unitary h0 h1).1⟩
  have huj : ∀ adj, (Instr.uj [(Wire.sec, true)] adj : Instr (Wire (a + 1) m r K)).Valid
      Wire.anc := fun adj => ⟨by simp, by simp⟩
  cases j with
  | gate g =>
      change i ∈ [Instr.gate g] at hij
      rw [List.mem_singleton] at hij
      subst hij; exact hjv
  | uj cs adj =>
      change i ∈ ujExpand κ adj at hij
      cases adj
      · change i ∈ [Instr.gate (rotGate κ false), Instr.uj [(Wire.sec, true)] false] at hij
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hij
        rcases hij with rfl | rfl
        · exact hrot false
        · exact huj false
      · change i ∈ [Instr.uj [(Wire.sec, true)] true, Instr.gate (rotGate κ true)] at hij
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hij
        rcases hij with rfl | rfl
        · exact huj true
        · exact hrot true
  | priv cs adj =>
      change i ∈ privExpand f z q adj at hij
      simp only [privExpand, List.mem_cons, List.mem_append] at hij
      rcases hij with rfl | hij | hij
      · exact hpriv.1
      · cases adj
        · exact ofGates_valid _ (phaseGates_ok hfz q) le_rfl i hij
        · simp only [if_true] at hij
          simp only [ofGates, List.mem_map] at hij
          obtain ⟨g, hg, rfl⟩ := hij
          obtain ⟨g', hg', rfl⟩ := mem_gInv _ g hg
          obtain ⟨c1, c2, c3⟩ := phaseGates_ok hfz q g' hg'
          exact ⟨c1, c2, ⟨by rw [Matrix.conjTranspose_conjTranspose]; exact c3.2,
            by rw [Matrix.conjTranspose_conjTranspose]; exact c3.1⟩⟩
      · simp only [List.not_mem_nil, or_false] at hij
        subst hij; exact hpriv.2

end

end GateOptimalPrecision
