import GateEfficientHamiltonian.Circuit.GPrep

/-!
# The complete gate-level circuit

Instructions: elementary gates, the sector-controlled `U_J` (or `U_J†`) and the
sector-controlled private Cayley operation.  The reuse step at pointer word
`j` is `D`, the boundary network (`U_J†`, gates, `U_J`) and the ripple
increment; the LCU circuit prepares the label table and pointer states, runs
`N` reuse steps and unprepares; one amplification round uses the LCU circuit,
the clean reflection, the literal inverse of the LCU circuit, the reflection,
the LCU circuit again and a global phase.

`amp_agrees` proves that the circuit agrees with the ideal amplified circuit
on clean inputs; the instruction counts are exact for the oracles
(`ampI_nPriv`, `ampI_nUJ`) and bounded for the elementary gates
(`ampI_nGates`).
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)
open GateDyadicBoundary (centralCosine centralSine)

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Semantics and oracle instructions -/

/-- The semantics: ancilla wires and the two supplied unitaries. -/
def simSem (UJ D : Vsp a P →L[ℂ] Vsp a P) : Sem (Wire a m r K) a P :=
  ⟨Wire.anc, anc_injective, UJ, D⟩

/-- The sector-controlled `U_J` (`adj = false`) or `U_J†` (`adj = true`). -/
def ujI (adj : Bool) : Instr (Wire a m r K) := Instr.uj [(Wire.sec, true)] adj

/-- The sector-controlled private Cayley operation. -/
def privI : Instr (Wire a m r K) := Instr.priv [(Wire.sec, true)] false

theorem run_ujI_true (UJ D : Vsp a P →L[ℂ] Vsp a P) :
    run (simSem (m := m) (r := r) (K := K) UJ D) [ujI true] = secOracle (UJ†) := by
  rw [run_singleton]; rfl

theorem run_ujI_false (UJ D : Vsp a P →L[ℂ] Vsp a P) :
    run (simSem (m := m) (r := r) (K := K) UJ D) [ujI false] = secOracle UJ := by
  rw [run_singleton]; rfl

theorem run_privI (UJ D : Vsp a P →L[ℂ] Vsp a P) :
    run (simSem (m := m) (r := r) (K := K) UJ D) [privI] = secOracle D := by
  rw [run_singleton]; rfl

/-! ### Reuse steps -/

/-- The boundary network conjugated by the sector-controlled `U_J`. -/
def bnetI (j : Fin (cap r + 1)) (c σ : ℝ) : List (Instr (Wire a m r K)) :=
  [ujI true] ++ ofGates (netGates j c σ) ++ [ujI false]

/-- One reuse step at pointer word `j`. -/
def stepI (j : Fin (cap r + 1)) (c σ : ℝ) : List (Instr (Wire a m r K)) :=
  [privI] ++ bnetI j c σ ++ ofGates incGates

/-- The SELECT circuit with `n` reuse steps. -/
def selectI (c σ : ℝ) : ℕ → List (Instr (Wire a m r K))
  | 0 => []
  | n + 1 => selectI c σ n ++ (if h : n < cap r + 1 then stepI ⟨n, h⟩ c σ else [])

theorem bnet_agrees (UJ D : Vsp a P →L[ℂ] Vsp a P) (j : Fin (cap r + 1)) (c σ : ℝ)
    (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (run (simSem UJ D) (bnetI (a := a) (m := m) (K := K) j c σ)) (BNET j c σ UJ) := by
  rw [bnetI, run_append, run_append, run_ujI_true, run_ujI_false, run_ofGates, BNET]
  exact ((Agrees.refl _ _).comp (pres2_secOracle _).1 (net_agrees j c σ hK)).comp
    ((pres2_NET _ _ _).comp (pres2_secOracle _)).1 (Agrees.refl _ _)

theorem step_agrees (UJ D : Vsp a P →L[ℂ] Vsp a P) (j : Fin (cap r + 1)) (c σ : ℝ)
    (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (run (simSem UJ D) (stepI (a := a) (m := m) (K := K) j c σ)) (STEP j c σ UJ D) := by
  rw [stepI, run_append, run_append, run_privI, run_ofGates, STEP]
  exact ((Agrees.refl _ _).comp (pres2_secOracle _).1 (bnet_agrees UJ D j c σ hK)).comp
    ((pres2_BNET _ _ _ _).comp (pres2_secOracle _)).1 inc_agrees

theorem select_agrees (UJ D : Vsp a P →L[ℂ] Vsp a P) (c σ : ℝ) (hK : a + m + 2 * r ≤ K) (n : ℕ) :
    Agrees Clean (run (simSem UJ D) (selectI (a := a) (m := m) (r := r) (K := K) c σ n))
      (selectN c σ UJ D n) := by
  induction n with
  | zero => exact Agrees.refl _ _
  | succ n ih =>
      rw [selectI, run_append, selectN]
      split_ifs with h
      · exact ih.comp (pres2_selectN _ _ _ _ _).1 (step_agrees UJ D _ c σ hK)
      · have h0 : run (simSem (m := m) (r := r) (K := K) UJ D) ([] : List (Instr (Wire a m r K))) = 1 :=
          rfl
        rw [h0, one_comp']
        exact ih

/-! ### The LCU circuit -/

variable {L : ℕ}

/-- The LCU circuit. -/
def lcuI (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ) :
    List (Instr (Wire a m r K)) :=
  ofGates (prepG (fIn wt)) ++ ofGates (rangeG hL nOf) ++ selectI c σ N ++
    ofGates (gInv (rangeG hL nOf)) ++ ofGates (gInv (prepG (fOut wt)))

theorem allUnitary_of_ok {k : ℕ} (gs : List (Gate (Wire a m r K))) (h : ∀ g ∈ gs, GateOK k g) :
    AllUnitary gs := fun g hg => (h g hg).2.2

theorem gInv_agrees (gs : List (Gate (Wire a m r K)) ) (O : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P)
    {k : ℕ} (hgs : ∀ g ∈ gs, GateOK k g) (h : Agrees Clean (gRun gs) O) (hO : IsUnitary O)
    (hOs : Preserves Clean (O†)) : Agrees Clean (gRun (gInv gs)) (O†) := by
  rw [gRun_gInv]
  exact h.adjoint (gRun_isUnitary gs (allUnitary_of_ok gs hgs)) hO hOs

theorem prepG_ok (f : Word r → ℝ) : ∀ g ∈ (prepG (a := a) (m := m) (K := K) f), GateOK 2 g :=
  prepCore_ok f r

theorem rangeG_ok (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) :
    ∀ g ∈ (rangeG (a := a) (m := m) (K := K) hL nOf), GateOK 2 g :=
  rangeLG_ok hL nOf _

theorem lcu_agrees (UJ D : Vsp a P →L[ℂ] Vsp a P) (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ)
    (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ) (hn : ∀ ℓ, nOf ℓ < 2 ^ r) (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (run (simSem UJ D) (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N))
      (LCU hL nOf wt c σ UJ D N) := by
  have hKr : r ≤ K + 1 := by omega
  rw [lcuI, run_append, run_append, run_append, run_append, run_ofGates, run_ofGates, run_ofGates,
    run_ofGates, LCU]
  have h1 := prep_agrees (P := P) (a := a) (m := m) (K := K) (fIn wt) hKr
  have h2 := range_agrees (P := P) (a := a) (m := m) (K := K) hL nOf hn hKr
  have h3 := select_agrees (r := r) UJ D c σ hK N
  have h4 := gInv_agrees _ _ (rangeG_ok hL nOf) h2 (RANGE_isUnitary _ _) (pres2_RANGE _ _).2
  have h5 := gInv_agrees _ _ (prepG_ok (fOut wt)) (prep_agrees (P := P) (a := a) (m := m) (K := K)
    (fOut wt) hKr) (PREP_isUnitary _) (pres2_PREP _).2
  exact (((h1.comp (pres2_PREP _).1 h2).comp ((pres2_RANGE _ _).comp (pres2_PREP _)).1 h3).comp
    ((pres2_selectN _ _ _ _ _).comp ((pres2_RANGE _ _).comp (pres2_PREP _))).1 h4).comp
    ((pres2_RANGE _ _).adj.comp ((pres2_selectN _ _ _ _ _).comp
      ((pres2_RANGE _ _).comp (pres2_PREP _)))).1 h5

/-! ### One amplification round -/

/-- The global phase `-1`. -/
def phaseG : Gate (Wire a m r K) := ⟨[], Wire.sec, -1⟩

theorem phaseG_op : (phaseG (a := a) (m := m) (r := r) (K := K)).op (Q := P) = -1 := by
  apply ext_bas_clm
  intro x q
  change gateOp [] Wire.sec (-1 : Matrix Bool Bool ℂ) (bas x q) = _
  rw [phase_bas]
  rfl

/-- The amplified circuit. -/
def ampI (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ) :
    List (Instr (Wire a m r K)) :=
  lcuI hL nOf wt c σ N ++ ofGates zrG ++ invList (lcuI hL nOf wt c σ N) ++ ofGates zrG ++
    lcuI hL nOf wt c σ N ++ ofGates [phaseG]

/-! ### Validity -/

theorem gate_valid_of_ok {k : ℕ} (g : Gate (Wire a m r K)) (hg : GateOK k g) (hk : k ≤ 3) :
    (Instr.gate g).Valid (Wire.anc (a := a) (m := m) (r := r) (K := K)) :=
  ⟨hg.1.trans hk, hg.2.1, hg.2.2⟩

theorem ofGates_valid {k : ℕ} (gs : List (Gate (Wire a m r K))) (h : ∀ g ∈ gs, GateOK k g)
    (hk : k ≤ 3) : ∀ i ∈ ofGates gs, i.Valid (Wire.anc (a := a) (m := m) (r := r) (K := K)) := by
  intro i hi
  simp only [ofGates, List.mem_map] at hi
  obtain ⟨g, hg, rfl⟩ := hi
  exact gate_valid_of_ok g (h g hg) hk

theorem ujI_valid (adj : Bool) : (ujI (a := a) (m := m) (r := r) (K := K) adj).Valid Wire.anc := by
  refine ⟨by simp, ?_⟩
  intro c hc i
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  simp

theorem privI_valid : (privI (a := a) (m := m) (r := r) (K := K)).Valid Wire.anc := by
  refine ⟨by simp, ?_⟩
  intro c hc i
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  simp

theorem compL_ok (n : ℕ) : ∀ g ∈ (compL (a := a) (m := m) (r := r) (K := K) n), GateOK 3 g := by
  intro g hg
  cases n with
  | zero => simp [compL] at hg
  | succ k =>
      simp only [compL] at hg
      split_ifs at hg with h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        subst hg
        exact (compG_ok k h).mono (by norm_num)
      · simp at hg

theorem rotL_ok (R : ℕ → Matrix Bool Bool ℂ) (hR : ∀ k, UnitaryMat (R k)) (n : ℕ) :
    ∀ g ∈ (rotL (a := a) (m := m) (r := r) (K := K) R n), GateOK 3 g := by
  intro g hg
  simp only [rotL] at hg
  split_ifs at hg with h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    exact rotG_ok _ (hR n) n h
  · simp at hg

theorem ascFull_ok (R : ℕ → Matrix Bool Bool ℂ) (hR : ∀ k, UnitaryMat (R k)) :
    ∀ g ∈ (ascFull (a := a) (m := m) (r := r) (K := K) R), GateOK 3 g := by
  have hc : ∀ n, ∀ g ∈ (ascCore (a := a) (m := m) (r := r) (K := K) R n), GateOK 3 g := by
    intro n
    induction n with
    | zero => intro g hg; simp [ascCore] at hg
    | succ n ih =>
        intro g hg
        rw [ascCore, List.mem_append, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · exact ih g hg
        · exact compL_ok n g hg
        · exact rotL_ok R hR n g hg
  have hd : ∀ n, ∀ g ∈ (chainDown (a := a) (m := m) (r := r) (K := K) n), GateOK 3 g := by
    intro n
    induction n with
    | zero => intro g hg; simp [chainDown] at hg
    | succ n ih =>
        intro g hg
        rw [chainDown, List.mem_append] at hg
        rcases hg with hg | hg
        · exact compL_ok _ g hg
        · exact ih g hg
  intro g hg
  rw [ascFull, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hc m g hg
  · exact hd _ g hg

theorem descFull_ok (R : ℕ → Matrix Bool Bool ℂ) (hR : ∀ k, UnitaryMat (R k)) :
    ∀ g ∈ (descFull (a := a) (m := m) (r := r) (K := K) R), GateOK 3 g := by
  have hc : ∀ n, ∀ g ∈ (descCore (a := a) (m := m) (r := r) (K := K) R n), GateOK 3 g := by
    intro n
    induction n with
    | zero => intro g hg; simp [descCore] at hg
    | succ n ih =>
        intro g hg
        rw [descCore, List.mem_append, List.mem_append] at hg
        rcases hg with (hg | hg) | hg
        · exact rotL_ok R hR n g hg
        · exact compL_ok n g hg
        · exact ih g hg
  have hu : ∀ n, ∀ g ∈ (chainUp (a := a) (m := m) (r := r) (K := K) n), GateOK 3 g := by
    intro n
    induction n with
    | zero => intro g hg; simp [chainUp] at hg
    | succ n ih =>
        intro g hg
        rw [chainUp, List.mem_append] at hg
        rcases hg with hg | hg
        · exact ih g hg
        · exact compL_ok _ g hg
  intro g hg
  rw [descFull, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hu _ g hg
  · exact hc m g hg

theorem hfC_ok (j : Fin (cap r + 1)) : ∀ g ∈ (hfC (a := a) (m := m) (K := K) j), GateOK 2 g :=
  mcGate_valid _ _ _ _ pauliX_unitary wkList_nodup (hfLits_ne_hf j)
    (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp) (hfLits_ne_wk j)

theorem cenG_ok (zz vv : ℝ) (h : zz ^ 2 + vv ^ 2 = 1) :
    ∀ g ∈ (cenG (a := a) (m := m) (r := r) (K := K) zz vv), GateOK 2 g := by
  have hlt : ∀ l ∈ (cenLits (a := a) (m := m) (r := r) (K := K)), l.1 ≠ Wire.sec := by
    intro l hl
    rcases mem_cenLits l hl with h | ⟨i, h⟩ <;> rw [h] <;> simp
  exact mcGate_valid _ _ _ _ (rotMat_unitary zz vv h) wkList_nodup hlt
    (fun f hf => by obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf; simp)
    (fun l hl f hf => by
      obtain ⟨i, rfl⟩ := (mem_wkList f).mp hf
      rcases mem_cenLits l hl with h | ⟨k, h⟩ <;> rw [h] <;> simp)

theorem netGates_ok (j : Fin (cap r + 1)) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) :
    ∀ g ∈ (netGates (a := a) (m := m) (K := K) j c σ), GateOK 3 g := by
  intro g hg
  simp only [netGates, List.mem_append] at hg
  rcases hg with (((hg | hg) | hg) | hg) | hg
  · exact (hfC_ok j g hg).mono (by norm_num)
  · exact ascFull_ok _ (fun _ => unMat_unitary _) g hg
  · exact (cenG_ok _ _ (GateDyadicBoundary.central_unit c σ hunit m) g hg).mono (by norm_num)
  · exact descFull_ok _ (fun _ => outMat_unitary _) g hg
  · exact (hfC_ok j g hg).mono (by norm_num)

theorem selectI_valid (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (n : ℕ) :
    ∀ i ∈ (selectI (a := a) (m := m) (r := r) (K := K) c σ n), i.Valid Wire.anc := by
  induction n with
  | zero => intro i hi; simp [selectI] at hi
  | succ n ih =>
      intro i hi
      rw [selectI, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih i hi
      · split_ifs at hi with h
        · simp only [stepI, bnetI, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with ((rfl | (rfl | hi) | rfl) | hi)
          · exact privI_valid
          · exact ujI_valid true
          · exact ofGates_valid _ (netGates_ok _ c σ hunit) le_rfl i hi
          · exact ujI_valid false
          · exact ofGates_valid _ (fun g hg => (incGates_ok g hg).1) (by norm_num) i hi
        · simp at hi

theorem lcuI_valid (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (N : ℕ) :
    ∀ i ∈ (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N), i.Valid Wire.anc := by
  intro i hi
  simp only [lcuI, List.mem_append] at hi
  rcases hi with (((hi | hi) | hi) | hi) | hi
  · exact ofGates_valid _ (prepG_ok _) (by norm_num) i hi
  · exact ofGates_valid _ (rangeG_ok hL nOf) (by norm_num) i hi
  · exact selectI_valid c σ hunit N i hi
  · exact ofGates_valid _ (gInv_ok _ (rangeG_ok hL nOf)) (by norm_num) i hi
  · exact ofGates_valid _ (gInv_ok _ (prepG_ok _)) (by norm_num) i hi

theorem invList_valid (gs : List (Instr (Wire a m r K)))
    (h : ∀ i ∈ gs, i.Valid (Wire.anc (a := a) (m := m) (r := r) (K := K))) :
    ∀ i ∈ invList gs, i.Valid Wire.anc := by
  intro i hi
  simp only [invList, List.mem_reverse, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact Instr.valid_inv _ j (h j hj)

theorem ampI_valid (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (N : ℕ) :
    ∀ i ∈ (ampI (a := a) (m := m) (K := K) hL nOf wt c σ N), i.Valid Wire.anc := by
  intro i hi
  simp only [ampI, List.mem_append] at hi
  rcases hi with ((((hi | hi) | hi) | hi) | hi) | hi
  · exact lcuI_valid hL nOf wt c σ hunit N i hi
  · exact ofGates_valid _ zrG_ok (by norm_num) i hi
  · exact invList_valid _ (lcuI_valid hL nOf wt c σ hunit N) i hi
  · exact ofGates_valid _ zrG_ok (by norm_num) i hi
  · exact lcuI_valid hL nOf wt c σ hunit N i hi
  · exact ofGates_valid (k := 0) _ (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      exact ⟨by simp [phaseG], by simp [phaseG], negOne_unitary⟩) (by norm_num) i hi

/-! ### Agreement of the amplified circuit -/

theorem amp_agrees (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (N : ℕ) (hn : ∀ ℓ, nOf ℓ < 2 ^ r) (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (run (simSem UJ D) (ampI (a := a) (m := m) (K := K) hL nOf wt c σ N))
      (AMP hL nOf wt c σ UJ D N) := by
  have hl := lcu_agrees (P := P) (a := a) (m := m) (K := K) UJ D hL nOf wt c σ N hn hK
  have hlu := LCU_isUnitary (K := K) (m := m) hL nOf wt c σ hunit UJ D hUJ hD N
  have hrunU : IsUnitary (run (simSem (m := m) (r := r) (K := K) UJ D)
      (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N)) :=
    run_isUnitary (simSem UJ D) hUJ hD _ (lcuI_valid hL nOf wt c σ hunit N)
  have hinv : Agrees Clean (run (simSem UJ D) (invList (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N)))
      ((LCU (K := K) (m := m) hL nOf wt c σ UJ D N)†) := by
    rw [run_invList]
    exact hl.adjoint hrunU hlu (pres2_LCU _ _ _ _ _ _ _ _).2
  have hz := zr_agrees (P := P) (a := a) (m := m) (r := r) (K := K) (by omega)
  have hp : Agrees Clean (gRun (Q := P) [phaseG (a := a) (m := m) (r := r) (K := K)])
      (-1 : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) := by
    rw [gRun_singleton, phaseG_op]
    exact Agrees.refl _ _
  rw [ampI, run_append, run_append, run_append, run_append, run_append, run_ofGates, run_ofGates]
  have hLp := pres2_LCU (K := K) (m := m) (P := P) hL nOf wt c σ UJ D N
  have e1 := hl.comp hLp.1 hz
  have e2 := e1.comp (pres2_ZR.comp hLp).1 hinv
  have e3 := e2.comp (hLp.adj.comp (pres2_ZR.comp hLp)).1 hz
  have e4 := e3.comp (pres2_ZR.comp (hLp.adj.comp (pres2_ZR.comp hLp))).1 hl
  have e5 := e4.comp (hLp.comp (pres2_ZR.comp (hLp.adj.comp (pres2_ZR.comp hLp)))).1 hp
  convert e5 using 1
  ext v
  simp [AMP]

end

end SparseHamiltonian.GateCircuit.Sim
