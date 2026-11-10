import GeneralSparseODE.Time
import GeneralSparseODE.ConstantBudget
import GateEfficientRemarks.ODE.ZeroReleasedTime

/-!
# The budget of the time-dependent general solver in `𝔟`

For the public data `q : GPubT` of the time-dependent general solver, the released time-dependent
solver works internally with the ratio `2g` and the accuracy `ε/2`. Put
`q*' = qOf s' T η_H η_D (2g) (ε/2)` (`s'` the padded slot count `2^⌈log₂ s⌉`), `𝔴` the register
words of the padded problem (`GateODEBudget.wordsT q.pub`), `ℓ' = log(1/ν)` and
`𝔟' = bitB b_data (2^{k+1}) (2^m) (2^m) q*' g ε`. The protocol `nprotocol (q.prep N z₀ loadC wpC)
(2g)` has the bounds of the released solver on the padded problem with the same constants
(`general_time_budget`):

* valid trials;
* at most `2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]` elementary gates in every history
  (`G_src = |loadC| + 2 |wpC|`): the implementations of the padded calls add at most
  `12 implG k b ≤ 408 𝔴` gates to each private call, within the slack of the released per-call bound
  `65536 (𝔴+1)³`, and their ancillas `12 k + 12 + 4 b` qubits;
* at most `3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits (`card_reg_le`: `10016 (𝔴+1)³ + 2 |Zs|`);
* at most `23592960 g q*'` supplied calls of each kind of matrix oracle (none in the zero case),
  three times the released count, besides `80 g` times the calls of `loadC` and twice those of
  `wpC`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open GateBinaryODE (SZ4 card_SZ4 hadUJ4_ok)
open GateBinaryODETime (PubT)
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase tzprepC btpublicOK_of btparams_ok0
  btzeroCase_params)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf wordsT gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Query)

namespace GPubT

variable (q : GPubT)

/-! ### The register -/

theorem card_Zg :
    Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) = 12 * q.k + 12 + 6 * q.b := by
  rw [Fintype.card_sum, card_SZ4, card_AWg]
  ring

/-- **The register of the time-dependent general solver**: the released register of the padded
problem with the ancillas of the implementations in the private scratch. -/
abbrev reg (Zs : Type*) [Fintype Zs] :=
  TNW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
    q.ar.bT q.ar.bP q.ar.A

/-- **The register of the time-dependent general solver** has `12 k + 12 + 4 b` more qubits than
the released register of the padded problem. -/
theorem card_reg (Zs : Type*) [Fintype Zs] :
    Fintype.card (q.reg Zs) =
      Fintype.card (TNW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
        q.pub.ar.bP q.pub.ar.A) + (12 * q.k + 12 + 4 * q.b) := by
  have h1 := ZeroTimeGateODE.card_ZNW (S := Fin (q.k + 1)) (Zs := Zs)
    (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.pub.params.a q.pub.params.m
    q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP
    q.ar.A
  have h2 := ZeroTimeGateODE.card_ZNW (S := Fin q.pub.kx) (Zs := Zs) (Z := SZ4 q.pub.kx q.pub.b)
    q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l
    q.pub.params.f q.pub.ar.bT q.pub.ar.bP q.pub.ar.A
  have e1 : Fintype.card (q.reg Zs) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a
      q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f
      (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
      q.ar.A) := rfl
  have e2 : Fintype.card (TNW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
      q.pub.ar.bP q.pub.ar.A) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a q.pub.params.m
      q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f (Fin q.pub.kx)
      Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT q.pub.ar.bP q.pub.ar.A) := rfl
  rw [e1, e2, h1, h2, card_Zg, card_SZ4, Fintype.card_fin, Fintype.card_fin]
  have hb : q.ar.bT = q.pub.ar.bT := rfl
  have hp : q.ar.bP = q.pub.ar.bP := rfl
  have ha : q.ar.A = q.pub.ar.A := rfl
  have hk : q.pub.kx = q.k + 1 := rfl
  have hbb : q.pub.b = q.b := rfl
  omega

/-- **The register of the time-dependent general solver in the words**: at most
`10016 (𝔴+1)³ + 2 |Zs|` qubits. -/
theorem card_reg_le (Zs : Type*) [Fintype Zs] :
    Fintype.card (q.reg Zs) ≤ 10016 * (wordsT q.pub + 1) ^ 3 + 2 * Fintype.card Zs := by
  rw [card_reg]
  have h1 := GateRemarks.ODE.card_TNW_le q.pub (Zs := Zs)
  have hk : q.k + 1 ≤ wordsT q.pub := by
    show q.pub.kx ≤ wordsT q.pub
    unfold wordsT
    omega
  have hb : q.b ≤ wordsT q.pub := by
    show q.pub.b ≤ wordsT q.pub
    unfold wordsT
    omega
  have hp1 : wordsT q.pub + 1 ≤ (wordsT q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  omega

/-- **The per-call cost of the time-dependent general operation in the words**: at most
`65944 (𝔴+1)³`. -/
theorem privGates_le (N : ℕ) (z₀ : Cfg (VW q.b)) :
    privGates (q.nd N z₀) q.ar ≤ 65944 * (wordsT q.pub + 1) ^ 3 := by
  have hV := q.nd_nGates N z₀
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_time_arith_words q.pub
  have hk : q.k + 1 ≤ wordsT q.pub := by
    show q.pub.kx ≤ wordsT q.pub
    unfold wordsT
    omega
  have hb : q.b ≤ wordsT q.pub := by
    show q.pub.b ≤ wordsT q.pub
    unfold wordsT
    omega
  have hp1 : wordsT q.pub + 1 ≤ (wordsT q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hl : q.ar.circ.length = q.pub.ar.circ.length := liftA_circ_length _
  have hb2 : q.ar.bP = q.pub.ar.bP := rfl
  have hb3 : q.ar.bT = q.pub.ar.bT := rfl
  have hkx : q.pub.kx = q.k + 1 := rfl
  unfold privGates
  rw [hl, hb2, hb3]
  unfold implG at hV
  omega

/-- **The arithmetic and scratch wires of the time-dependent general operation in the words**:
at most `4200 (𝔴+1)³`. -/
theorem wires_le :
    ((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A ≤
      4200 * ((wordsT q.pub : ℝ) + 1) ^ 3 := by
  obtain ⟨-, hA, hT, hP⟩ := GateODEBudget.binary_time_arith_words q.pub
  have hk : q.k + 1 ≤ wordsT q.pub := by
    show q.pub.kx ≤ wordsT q.pub
    unfold wordsT
    omega
  have hb : q.b ≤ wordsT q.pub := by
    show q.pub.b ≤ wordsT q.pub
    unfold wordsT
    omega
  have hp1 : wordsT q.pub + 1 ≤ (wordsT q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have h : (q.k + 1) + (12 * q.k + 12 + 6 * q.b) + q.ar.bT + q.ar.bP + q.ar.A ≤
      4200 * (wordsT q.pub + 1) ^ 3 := by
    have e1 : q.ar.bT = q.pub.ar.bT := rfl
    have e2 : q.ar.bP = q.pub.ar.bP := rfl
    have e3 : q.ar.A = q.pub.ar.A := rfl
    rw [e1, e2, e3]
    omega
  exact_mod_cast h

end GPubT

/-! ### The budget -/

section Budget

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 8000000 in
/-- **The budget of the time-dependent general solver in `𝔟`** (every `T ≥ 0`; equations
`ode:eq:gate-main` and `ode:eq:gate-space` for time-indexed sparse access of general size). For
public data with `BTPublicOK0 q.pub`, a rescaling of bit length `b_data` in the zero case and the
public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)` otherwise, an arithmetic accuracy
`ζ ≥ ν/(196608 q*')`, stored bits `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` of bit length `b_data`,
and valid loading and weight-preparation circuits, put
`𝔟' = bitB b_data (2^{k+1}) (2^m) (2^m) q*' g ε`. The protocol
`nprotocol (q.prep N z₀ loadC wpC) (2g)` has valid trials, at most
`2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]` elementary gates in every history, at most
`3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits, and at most
`(if BTZeroCase then 0 else 23592960 g q*' ([row] + [col] + [value])) +
80 g (calls_c(loadC) + 2 calls_c(wpC))` calls of every kind `c` of the supplied oracles. -/
theorem general_time_budget (bd : ℕ) (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : if BTZeroCase q.pub then HasBits bd q.γ
      else q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) (z₀ : Cfg (VW q.b))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prep N z₀ loadC wpC) j, i.Valid) ∧
    ((nprotocol (q.prep N z₀ loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
            (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (q.reg Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
          (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs ∧
    (∀ c : Query → Bool, ((nprotocol (q.prep N z₀ loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      (if BTZeroCase q.pub then 0 else
        23592960 * q.g * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hε0 : (0 : ℝ) < q.ε := hq.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hq.ε_half
  have hg1 : (1 : ℝ) ≤ q.g := hq.g_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith
  have hε2' : q.ε / 2 ≤ 1 := by linarith
  have hQ1 : 1 ≤ qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hg2 hε2 hε2'
  have hℓ1 : 1 ≤ logBudget (2 * q.g) (q.ε / 2) :=
    ImprovedODEQueryBudget.logBudget_ge_one (2 * q.g) (q.ε / 2) hg2 hε2 hε2'
  have hQg : 0 ≤ qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g := by positivity
  have hB0 : 0 ≤ bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
      (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg bd _ _ _ hQg hq.ε_pos hε1
  -- the words in `𝔟'`
  have hw : (wordsT q.pub : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
        (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by
    by_cases hz : BTZeroCase q.pub
    · rw [if_pos hz] at hγ
      exact GateRemarks.ODE.zero_wordsT_le bd q.pub hq hz hγ hζ hb hc0 hH hD
    · rw [if_neg hz] at hγ
      exact GateBitBudget.wordsT_le bd q.pub (btpublicOK_of hq hz) hγ hζ hb hc0 hT hH hD
  generalize hBdef : bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
    (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε = B at hB0 hw ⊢
  have hwr0 : (0 : ℝ) ≤ wordsT q.pub := Nat.cast_nonneg _
  have hY1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
  -- the register
  have hspace : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (B + 1) ^ 3 +
      2 * Fintype.card Zs := by
    have h1 : (Fintype.card (q.reg Zs) : ℝ) ≤ 10016 * ((wordsT q.pub : ℝ) + 1) ^ 3 +
        2 * Fintype.card Zs := by exact_mod_cast q.card_reg_le Zs
    have hcube := GateBitBudget.cube_le hwr0 hB0 (c := 300) (by linarith)
    have : (10016 : ℝ) * ((wordsT q.pub : ℝ) + 1) ^ 3 ≤ 10016 * ((300 + 1) ^ 3 * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    linarith
  have hloadV' : ∀ i ∈ liftC loadC, i.Valid := valid_liftC _ hloadV
  have hGl : nGatesN (liftC loadC) = nGatesN loadC := nGatesN_liftC _
  have hCl : ∀ p : Query → Bool, nCallsN p (liftC loadC) = nCallsN p loadC :=
    fun p => nCallsN_liftC p _
  have hr : q.pub.params.ratio = 2 * q.g := rfl
  by_cases hz : BTZeroCase q.pub
  · -- the direct source assembly
    have hp := btparams_ok0 hq
    obtain ⟨hV, -, -, hWG, hWC, -, hcardZ, -⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
      (S := Fin (q.k + 1)) (Zs := Zs) (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Y := Fin q.m ⊕ PY q.k q.b) (J := Query) q.pub.params q.pub.params.a q.pub.params.m
      q.pub.params.r q.pub.params.K q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
      (btzeroCase_params hq hz) (liftC loadC) hloadV' wpC hwpV
    have hpr : q.prep N z₀ loadC wpC = tzprepC (liftC loadC) wpC := by
      rw [GPubT.prep, if_pos hz]
      rfl
    have htest : Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
        Fintype.card (q.reg Zs) := by
      have h1 := (hcardZ : Fintype.card (q.reg Zs) = _)
      have h2 : Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT
          q.ar.bP q.ar.A) = Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) +
            q.ar.bT + q.ar.bP + q.ar.A + 3 := by
        simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [h1, h2]
      omega
    have htest' : (Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f) : ℝ) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
        Fintype.card (q.reg Zs) := by
      exact_mod_cast htest
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hpr]
      exact hV
    · -- gates
      rw [hpr]
      have hWG' : ((nprotocol (tzprepC (liftC loadC) wpC : List (NInstr (q.reg Zs)
          (Fin q.m ⊕ PY q.k q.b) Query)) q.pub.params.ratio
          (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
          40 * q.pub.params.ratio * ((nGatesN (liftC loadC) + 2 * nGatesN wpC : ℕ) : ℝ) +
            20 * q.pub.params.ratio * (4 * ((Fintype.card (GateODE.AW q.pub.params.a
              q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l
              q.pub.params.f) : ℝ) +
              Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT
                q.ar.bP q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1))) + 3) := hWG
      rw [hGl] at hWG'
      push_cast at hWG'
      refine hWG'.trans ?_
      rw [hr]
      have h1 := mul_le_mul_of_nonneg_left htest' hg0
      have h2 : q.g * (Fintype.card (q.reg Zs) : ℝ) ≤
          q.g * (3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs) :=
        mul_le_mul_of_nonneg_left hspace hg0
      have h3 : q.g * (B + 1) ^ 3 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
      have h4 : q.g * 1 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
      have h5 : 0 ≤ q.g * ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := mul_nonneg hg0 hG0
      have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
      nlinarith
    · -- calls
      intro c
      rw [hpr, if_pos hz, zero_add]
      have hW : ((nprotocol (tzprepC (liftC loadC) wpC : List (NInstr (q.reg Zs)
          (Fin q.m ⊕ PY q.k q.b) Query)) q.pub.params.ratio
          (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
          40 * q.pub.params.ratio * ((nCallsN c (liftC loadC) + 2 * nCallsN c wpC : ℕ) : ℝ) :=
        hWC c
      rw [hCl] at hW
      refine hW.trans (le_of_eq ?_)
      rw [hr]
      push_cast
      ring
  · -- the native preparation
    have hP := btpublicOK_of hq hz
    rw [if_neg hz] at hγ
    obtain ⟨-, hd, -, -, hJ, -⟩ := GateODEBudget.binary_ode_time_sizes q.pub hP hγ
    have hd' : (q.pub.params.d : ℝ) ≤
        4096 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := hd
    have hJ' : (q.pub.params.J : ℝ) ≤ 60 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        logBudget (2 * q.g) (q.ε / 2) := hJ
    have hpr : q.prep N z₀ loadC wpC =
        tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC := by
      rw [GPubT.prep, if_neg hz]
    obtain ⟨hV, -, hC, -, hWC, -, -⟩ := native_ode_time_solver q.pub.params (q.pub.params_ok hP)
      q.pub.UJg (hadUJ4_ok q.pub.σ q.pub.hσ) (q.nd N z₀) (q.nd_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (liftC loadC) hloadV' wpC hwpV
    have hgc := native_ode_time_gate_count q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.nd N z₀) (q.nd_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (liftC loadC) hloadV' wpC hwpV
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hpr]
      exact hV
    · -- gates
      rw [hpr]
      have hUJl : q.pub.UJg.length = q.pub.σ + 3 := GateBinaryODE.hadUJ4_length q.pub.σ q.pub.hσ
      have hPG := q.privGates_le N z₀
      have hAp := q.wires_le
      have hcZ := q.card_Zg
      have hgc' : ((nprotocol (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC)
          q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
          18000 * q.pub.params.g * (((q.pub.params.d : ℝ) + 1) * ((q.pub.params.a : ℝ) +
            q.pub.params.m + q.pub.params.r + 1 + ((q.pub.UJg.length : ℕ) : ℝ) +
            ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ)) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN (liftC loadC) : ℝ) + 2 * nGatesN wpC) +
            ((Fintype.card (Fin (q.k + 1)) : ℝ) + Fintype.card Zs +
              Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) + q.ar.bT +
              q.ar.bP + q.ar.A)) := hgc
      rw [hUJl, hGl, Fintype.card_fin, hcZ] at hgc'
      have hgg : q.pub.params.g = q.g := rfl
      rw [hgg] at hgc'
      have hSm : (q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r ≤
          2 * (wordsT q.pub : ℝ) := by
        have hσ := q.pub.hσ
        have : q.pub.kx + q.pub.σ + q.pub.params.m + q.pub.params.r ≤ 2 * wordsT q.pub := by
          unfold wordsT
          omega
        exact_mod_cast this
      have hl : (q.pub.params.l : ℝ) ≤ wordsT q.pub := by
        have : q.pub.params.l ≤ wordsT q.pub := by
          unfold wordsT
          omega
        exact_mod_cast this
      have hPG' : ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ) ≤
          65944 * ((wordsT q.pub : ℝ) + 1) ^ 3 := by
        exact_mod_cast hPG
      have hcube := GateBitBudget.cube_le (add_nonneg hwr0 (by linarith)) hB0 (c := 300) hw
      have e1 : ((q.pub.params.a : ℕ) : ℝ) = (q.k : ℝ) + 4 := by
        show ((q.k + 1 + 3 : ℕ) : ℝ) = _
        push_cast
        ring
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q
        at hQ1 hd' hJ' ⊢
      have hXs0 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ (q.pub.params.m : ℝ) := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ (q.pub.params.r : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ ((q.pub.σ + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have hAw0 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs +
          ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A := by
        have h1 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ (q.ar.bT : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ (q.ar.bP : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ (q.ar.A : ℝ) := Nat.cast_nonneg _
        linarith
      have key1 := GateODEBudget.gate_budget_arith' 18000 q.g Q
        (logBudget (2 * q.g) (q.ε / 2)) (q.pub.params.d : ℝ) (q.pub.params.J : ℝ)
        (q.pub.params.l : ℝ)
        (((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ))
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT +
          q.ar.bP + q.ar.A)
        (by norm_num) hg0 hQ1 hℓ1 hd' hJ' (Nat.cast_nonneg _) hXs0 hG0 hAw0
      have key2 := words_gate_arith_g 73746000 (6 * 10 ^ 12) q.g Q (logBudget (2 * q.g) (q.ε / 2))
        (wordsT q.pub : ℝ) ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ)
        ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r)
        (q.pub.params.l : ℝ) ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (Fintype.card Zs : ℝ)
        (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A)
        (by norm_num) (by norm_num) hg0 hQ1 hℓ1 hwr0 hPG' hSm (Nat.cast_nonneg _) hl hAp hG0 hZ0
      have key3 := GateBitBudget.budget_mono (c := 6 * 10 ^ 12) (C := 2 * 10 ^ 20)
        (k := (300 + 1) ^ 3) (g := q.g) (Q := Q)
        (a := ((wordsT q.pub : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3)
        (b := (B + 1) ^ 3) (S₁ := (nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (S₂ := (Fintype.card Zs : ℝ)) (by norm_num) hg0 (by linarith) (by positivity) hG0 hZ0
        (by norm_num) hcube (by norm_num)
      have e2 : 4097 * 18000 * q.g * (Q * ((((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) +
            ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ)) + 1 +
            logBudget (2 * q.g) (q.ε / 2) * ((q.pub.params.l : ℝ) + 1)) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A)) =
          73746000 * q.g * (Q * (((privGates (q.nd N z₀) q.ar : ℕ) : ℝ) +
            ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r) +
            logBudget (2 * q.g) (q.ε / 2) * ((q.pub.params.l : ℝ) + 1) + 8) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            ((Fintype.card Zs : ℝ) + (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A))) := by
        rw [e1]
        push_cast
        ring
      have hgc'' : ((nprotocol (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC)
          q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
          18000 * q.g * (((q.pub.params.d : ℝ) + 1) * (((q.pub.params.a : ℕ) : ℝ) +
            q.pub.params.m + q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) +
            ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ)) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A)) := by
        refine hgc'.trans (le_of_eq ?_)
        push_cast
        ring
      exact hgc''.trans (key1.trans (le_of_eq e2 |>.trans (key2.trans key3)))
    · -- calls
      intro c
      rw [hpr, if_neg hz]
      have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
        split_ifs <;> norm_num
      have hcV := q.nd_nCalls N z₀ c
      have hcP : (nCallsN c (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC) :
          ℝ) ≤ 12 * (q.pub.params.d : ℝ) * (6 *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0))) +
          ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by
        have h1 : nCallsN c (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC) ≤
            12 * q.pub.params.d * nCallsN c (q.nd N z₀).V + nCallsN c (liftC loadC) +
              2 * nCallsN c wpC := hC c
        rw [hCl] at h1
        have h2 : nCallsN c (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC) ≤
            12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c loadC + 2 * nCallsN c wpC :=
          h1.trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ hcV) _) _)
        have h3 : ((nCallsN c (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC) :
            ℕ) : ℝ) ≤ ((12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c loadC + 2 * nCallsN c wpC : ℕ) :
                  ℝ) := by
          exact_mod_cast h2
        refine h3.trans (le_of_eq ?_)
        push_cast
        split_ifs <;> ring
      have hW : ((nprotocol (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC)
          q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
          40 * q.pub.params.ratio * (nCallsN c (tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
            (liftC loadC) wpC) : ℝ) := hWC c
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q at hd' ⊢
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hcP ⊢
      have h4 := mul_le_mul_of_nonneg_left hd' (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤
        80 * 72) hg0) hI0)
      have h5 := mul_le_mul_of_nonneg_left hcP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) hg0)
      have e6 : 80 * q.g * (12 * (q.pub.params.d : ℝ) * (6 * I) + ((nCallsN c loadC : ℝ) +
          2 * nCallsN c wpC)) = 80 * 72 * q.g * I * (q.pub.params.d : ℝ) +
          80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by ring
      have e7 : 80 * 72 * q.g * I * (4096 * Q) = 23592960 * q.g * Q * I := by ring
      have e8 : 40 * q.pub.params.ratio * (nCallsN c (tnprepC q.pub.params q.pub.UJg (q.nd N z₀)
          q.ar (liftC loadC) wpC) : ℝ) = 80 * q.g * (nCallsN c (tnprepC q.pub.params q.pub.UJg
            (q.nd N z₀) q.ar (liftC loadC) wpC) : ℝ) := by
        rw [hr]
        ring
      rw [e6] at h5
      rw [e7] at h4
      rw [e8] at hW
      exact hW.trans (h5.trans (add_le_add h4 le_rfl))

end Budget

end

end SparseHamiltonian.GeneralSparseODE
