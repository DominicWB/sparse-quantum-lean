import GeneralSparseODE.Constant
import GateEfficientRemarks.ODE.ZeroReleased

/-!
# The budget of the constant-coefficient general solver in `𝔟`

For the public data `q : GPub` of the general solver, put `q* = qOf s' T η_H η_D g ε` (`s'` the
padded slot count `2^⌈log₂ s⌉`), `𝔴` the register words of the padded problem
(`GateODEBudget.words q.pub`), `ℓ = log(1/ν)` and `𝔟₀ = bitB b_data (2^{k+1}) 0 0 q* g ε`. The
protocol `nprotocol (q.prep N z₀ srcC) g` has the bounds of the released solver on the padded
problem with the same constants (`general_ode_budget`):

* valid trials;
* at most `10²⁰ g [q* (𝔟₀+1)³ + G_src + |Zs|]` elementary gates in every history: the
  implementations of the padded calls add at most `12 implG k b ≤ 408 𝔴` gates to each private
  call, within the slack of the released per-call bound `65536 (𝔴+1)³`, and their ancillas at most
  `12 k + 12 + 4 b` qubits;
* at most `3·10¹¹ (𝔟₀+1)³ + 2 |Zs|` qubits (`card_reg_le`: `10016 (𝔴+1)³ + 2 |Zs|`);
* at most `11796480 g q*` supplied calls of each kind of matrix oracle (none in the zero case),
  three times the released count, besides `40 g` times the calls of the source circuits.
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
open GateBinaryODE (Pub SZ4 card_SZ4 hadUJ4_ok)
open ZeroTimeGateODE (BPublicOK0 BZeroCase zprepC srcRot bpublicOK_of)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf words gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Query)

/-! ### Arithmetic -/

/-- The arithmetic of the gate budget in the words with the implementation gates: as
`GateODEBudget.words_gate_arith`, for `G_C ≤ 65944 (𝔴+1)³` and `A ≤ 4200 (𝔴+1)³`. -/
theorem words_gate_arith_g (c C g Q ℓ w GC Sm l Gs Zs Ap : ℝ) (hcC : 70155 * c ≤ C) (hc : 0 ≤ c)
    (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hℓ : 1 ≤ ℓ) (hw : 0 ≤ w) (hGC : GC ≤ 65944 * (w + 1) ^ 3)
    (hSm : Sm ≤ 2 * w) (hl0 : 0 ≤ l) (hl : l ≤ w) (hAp : Ap ≤ 4200 * (w + 1) ^ 3)
    (hGs : 0 ≤ Gs) (hZs : 0 ≤ Zs) :
    c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap)) ≤
      C * g * (Q * (w + ℓ + 1) ^ 3 + Gs + Zs) := by
  have hy1 : 1 ≤ w + ℓ + 1 := by linarith
  have hy3 : w + ℓ + 1 ≤ (w + ℓ + 1) ^ 3 := le_self_pow₀ hy1 (by norm_num)
  have h13 : 1 ≤ (w + ℓ + 1) ^ 3 := one_le_pow₀ hy1
  have hwy : (w + 1) ^ 3 ≤ (w + ℓ + 1) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hsq : (w + ℓ + 1) * (w + ℓ + 1) ≤ (w + ℓ + 1) ^ 3 := by
    have e : (w + ℓ + 1) ^ 3 = (w + ℓ + 1) * (w + ℓ + 1) * (w + ℓ + 1) := by ring
    rw [e]
    exact le_mul_of_one_le_right (by positivity) hy1
  have hℓl : ℓ * (l + 1) ≤ (w + ℓ + 1) * (w + ℓ + 1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  generalize (w + ℓ + 1) ^ 3 = Y at hy3 h13 hwy hsq ⊢
  have hS : GC + Sm + ℓ * (l + 1) + 8 ≤ 65955 * Y := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hQY : Y ≤ Q * Y := le_mul_of_one_le_left hY0 hQ
  have h1 := mul_le_mul_of_nonneg_left hS hQ0
  have hin : Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap) ≤ 70155 * (Q * Y + Gs + Zs) := by
    linarith
  have hpos : 0 ≤ Q * Y + Gs + Zs := by positivity
  calc c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap))
      ≤ c * g * (70155 * (Q * Y + Gs + Zs)) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hc hg)
    _ = 70155 * c * g * (Q * Y + Gs + Zs) := by ring
    _ ≤ C * g * (Q * Y + Gs + Zs) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hg) hpos

theorem card_AWg (k b : ℕ) : Fintype.card (GeneralSparseAccess.AW k b) = 6 * k + 6 + 2 * b := by
  simp only [GeneralSparseAccess.AW, EW, VW, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

namespace GPub

variable (q : GPub)

/-! ### The register -/

theorem card_Zg :
    Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) = 12 * q.k + 12 + 6 * q.b := by
  rw [Fintype.card_sum, card_SZ4, card_AWg]
  ring

/-- **The register of the general solver**: the released register of the padded problem with the
ancillas of the implementations in the private scratch. -/
abbrev reg (Zs : Type*) [Fintype Zs] :=
  NW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
    q.ar.bT q.ar.bP q.ar.A

/-- **The register of the general solver** has `12 k + 12 + 4 b` more qubits than the released
register of the padded problem. -/
theorem card_reg (Zs : Type*) [Fintype Zs] :
    Fintype.card (q.reg Zs) =
      Fintype.card (NW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
        q.pub.ar.bP q.pub.ar.A) + (12 * q.k + 12 + 4 * q.b) := by
  have h1 := ZeroTimeGateODE.card_ZNW (S := Fin (q.k + 1)) (Zs := Zs)
    (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.pub.params.a q.pub.params.m
    q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP
    q.ar.A
  have h2 := ZeroTimeGateODE.card_ZNW (S := Fin q.pub.kx) (Zs := Zs) (Z := SZ4 q.pub.kx q.pub.b)
    q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l
    q.pub.params.f q.pub.ar.bT q.pub.ar.bP q.pub.ar.A
  have e1 : Fintype.card (q.reg Zs) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a
      q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f
      (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
      q.ar.A) := rfl
  have e2 : Fintype.card (NW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
      q.pub.ar.bP q.pub.ar.A) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a q.pub.params.m
      q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f (Fin q.pub.kx) Zs
      (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT q.pub.ar.bP q.pub.ar.A) := rfl
  rw [e1, e2, h1, h2, card_Zg, card_SZ4, Fintype.card_fin, Fintype.card_fin]
  have hb : q.ar.bT = q.pub.ar.bT := rfl
  have hp : q.ar.bP = q.pub.ar.bP := rfl
  have ha : q.ar.A = q.pub.ar.A := rfl
  have hk : q.pub.kx = q.k + 1 := rfl
  have hbb : q.pub.b = q.b := rfl
  omega

/-- **The register of the general solver in the words**: at most `10016 (𝔴+1)³ + 2 |Zs|` qubits. -/
theorem card_reg_le (Zs : Type*) [Fintype Zs] :
    Fintype.card (q.reg Zs) ≤ 10016 * (words q.pub + 1) ^ 3 + 2 * Fintype.card Zs := by
  rw [card_reg]
  have h1 := GateRemarks.ODE.card_NW_le q.pub (Zs := Zs)
  have hk : q.k + 1 ≤ words q.pub := by
    show q.pub.kx ≤ words q.pub
    unfold words
    omega
  have hb : q.b ≤ words q.pub := by
    show q.pub.b ≤ words q.pub
    unfold words
    omega
  have hp1 : words q.pub + 1 ≤ (words q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  omega

/-- **The per-call cost of the general operation in the words**: at most `65944 (𝔴+1)³`. -/
theorem privGates_le (N : ℕ) (z₀ : Cfg (VW q.b)) :
    privGates (q.nd N z₀) q.ar ≤ 65944 * (words q.pub + 1) ^ 3 := by
  have hV := q.nd_nGates N z₀
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_arith_words q.pub
  have hk : q.k + 1 ≤ words q.pub := by
    show q.pub.kx ≤ words q.pub
    unfold words
    omega
  have hb : q.b ≤ words q.pub := by
    show q.pub.b ≤ words q.pub
    unfold words
    omega
  have hp1 : words q.pub + 1 ≤ (words q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hl : q.ar.circ.length = q.pub.ar.circ.length := liftA_circ_length _
  have hb2 : q.ar.bP = q.pub.ar.bP := rfl
  have hb3 : q.ar.bT = q.pub.ar.bT := rfl
  have hkx : q.pub.kx = q.k + 1 := rfl
  unfold privGates
  rw [hl, hb2, hb3]
  unfold implG at hV
  omega

/-- **The arithmetic and scratch wires of the general operation in the words**: at most
`4200 (𝔴+1)³`. -/
theorem wires_le :
    ((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A ≤
      4200 * ((words q.pub : ℝ) + 1) ^ 3 := by
  obtain ⟨-, hA, hT, hP⟩ := GateODEBudget.binary_arith_words q.pub
  have hk : q.k + 1 ≤ words q.pub := by
    show q.pub.kx ≤ words q.pub
    unfold words
    omega
  have hb : q.b ≤ words q.pub := by
    show q.pub.b ≤ words q.pub
    unfold words
    omega
  have hp1 : words q.pub + 1 ≤ (words q.pub + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have h : (q.k + 1) + (12 * q.k + 12 + 6 * q.b) + q.ar.bT + q.ar.bP + q.ar.A ≤
      4200 * (words q.pub + 1) ^ 3 := by
    have e1 : q.ar.bT = q.pub.ar.bT := rfl
    have e2 : q.ar.bP = q.pub.ar.bP := rfl
    have e3 : q.ar.A = q.pub.ar.A := rfl
    rw [e1, e2, e3]
    omega
  exact_mod_cast h

end GPub

/-! ### The budget -/

section Budget

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 8000000 in
/-- **The budget of the general solver in `𝔟`** (constant coefficients, every `T ≥ 0`; equations
`ode:eq:gate-main` and `ode:eq:gate-space` for sparse access of general size). For public data
with `BPublicOK0 q.pub`, a rescaling of bit length `b_data` in the zero case and the public
rescaling otherwise, an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data` and `c₀`,
`T`, `η_H`, `η_D` of bit length `b_data`, and valid source circuits, put
`𝔟₀ = bitB b_data (2^{k+1}) 0 0 q* g ε`. The protocol `nprotocol (q.prep N z₀ srcC) g` has valid
trials, at most `10²⁰ g [q* (𝔟₀+1)³ + G_src + |Zs|]` elementary gates in every history, at most
`3·10¹¹ (𝔟₀+1)³ + 2 |Zs|` qubits, and at most
`(if BZeroCase then 0 else 11796480 g q* ([row] + [col] + [value])) + 40 g (calls_c(srcC 0) +
calls_c(srcC 1))` calls of every kind `c` of the supplied oracles. -/
theorem general_ode_budget (bd : ℕ) (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : if BZeroCase q.pub then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) (z₀ : Cfg (VW q.b))
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prep N z₀ srcC) j, i.Valid) ∧
    ((nprotocol (q.prep N z₀ srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (q.reg Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 2 * Fintype.card Zs ∧
    (∀ c : Query → Bool, ((nprotocol (q.prep N z₀ srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      (if BZeroCase q.pub then 0 else 11796480 * q.g * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.pub.s q.T q.etaH q.etaD q.g q.ε :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hℓ1 : 1 ≤ logBudget q.g q.ε := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge
    hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hB0 : 0 ≤ bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    bitB_nonneg bd _ 0 0 hQg hq.ε_pos hε1
  -- the words in `𝔟₀`
  have hw : (words q.pub : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
    by_cases hz : BZeroCase q.pub
    · rw [if_pos hz] at hγ
      exact GateRemarks.ODE.zero_words_le bd q.pub hq hz hγ hζ hb hc0 hH hD
    · rw [if_neg hz] at hγ
      exact GateBitBudget.words_le bd q.pub (bpublicOK_of hq hz) hγ hζ hb hc0 hT hH hD
  generalize hBdef : bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε =
    B at hB0 hw ⊢
  have hwr0 : (0 : ℝ) ≤ words q.pub := Nat.cast_nonneg _
  have hY1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
  -- the register
  have hspace : (Fintype.card (q.reg Zs) : ℝ) ≤ 3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs := by
    have h1 : (Fintype.card (q.reg Zs) : ℝ) ≤ 10016 * ((words q.pub : ℝ) + 1) ^ 3 +
        2 * Fintype.card Zs := by exact_mod_cast q.card_reg_le Zs
    have hcube := GateBitBudget.cube_le hwr0 hB0 (c := 300) (by linarith)
    have : (10016 : ℝ) * ((words q.pub : ℝ) + 1) ^ 3 ≤ 10016 * ((300 + 1) ^ 3 * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    linarith
  have hsrcV' : ∀ c, ∀ i ∈ liftC (srcC c), i.Valid := fun c => valid_liftC _ (hsrcV c)
  have hGs : ∀ c, nGatesN (liftC (srcC c)) = nGatesN (srcC c) := fun c => nGatesN_liftC _
  have hCs : ∀ (p : Query → Bool) c, nCallsN p (liftC (srcC c)) = nCallsN p (srcC c) :=
    fun p c => nCallsN_liftC p _
  by_cases hz : BZeroCase q.pub
  · -- the direct source assembly
    obtain ⟨hV, -, -, hWG, hWC, -, hcardZ, -⟩ := ZeroTimeGateODE.native_ode_solver_zero
      (S := Fin (q.k + 1)) (Zs := Zs) (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Y := PY q.k q.b) (J := Query) q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.k q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A q.T q.g q.ε q.r₀ q.rb
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos
      (fun c => liftC (srcC c)) hsrcV'
    have hp : q.prep N z₀ srcC = zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) := by
      rw [GPub.prep, if_pos hz]
    have htest : Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤ Fintype.card (q.reg Zs) := by
      have h1 := (hcardZ : Fintype.card (q.reg Zs) = _)
      have h2 : Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT
          q.ar.bP q.ar.A) = Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) +
            q.ar.bT + q.ar.bP + q.ar.A + 3 := by
        simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [h1, h2]
      omega
    have htest' : (Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) : ℝ) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
          q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤ Fintype.card (q.reg Zs) := by
      exact_mod_cast htest
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hp]
      exact hV
    · -- gates
      rw [hp]
      have hWG' : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) :
          List (NInstr (q.reg Zs) (PY q.k q.b) Query)) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
          40 * q.g * ((nGatesN (liftC (srcC false)) + nGatesN (liftC (srcC true)) + 2 : ℕ) : ℝ) +
            20 * q.g * (4 * ((Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
              q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) : ℝ) +
              Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP
                q.ar.A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1))) + 3) := hWG
      rw [hGs, hGs] at hWG'
      push_cast at hWG'
      refine hWG'.trans ?_
      have h1 := mul_le_mul_of_nonneg_left htest' hg0
      have h2 : q.g * (Fintype.card (q.reg Zs) : ℝ) ≤
          q.g * (3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs) :=
        mul_le_mul_of_nonneg_left hspace hg0
      have h3 : q.g * (B + 1) ^ 3 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
      have h4 : q.g * 1 ≤ q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
      have h5 : 0 ≤ q.g * ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := mul_nonneg hg0 hG0
      have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
      nlinarith
    · -- calls
      intro c
      rw [hp, if_pos hz, zero_add]
      have hW : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) :
          List (NInstr (q.reg Zs) (PY q.k q.b) Query)) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
          40 * q.g * ((nCallsN c (liftC (srcC false)) + nCallsN c (liftC (srcC true)) : ℕ) : ℝ) :=
        hWC c
      rw [hCs, hCs] at hW
      push_cast at hW
      exact hW
  · -- the native preparation
    have hP := bpublicOK_of hq hz
    rw [if_neg hz] at hγ
    obtain ⟨-, hd, -, -, hJ, -, -⟩ := GateODEBudget.binary_ode_sizes q.pub hP hγ
    have hd' : (q.pub.params.d : ℝ) ≤ 4096 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε := hd
    have hJ' : (q.pub.params.J : ℝ) ≤ 60 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
        logBudget q.g q.ε := hJ
    have hp : q.prep N z₀ srcC =
        nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (fun c => liftC (srcC c)) := by
      rw [GPub.prep, if_neg hz]
    obtain ⟨hV, -, hC, -, hWC, -, -⟩ := native_ode_solver q.pub.params (q.pub.params_ok hP)
      q.pub.UJg (hadUJ4_ok q.pub.σ q.pub.hσ) (q.nd N z₀) (q.nd_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (fun c => liftC (srcC c)) hsrcV'
    have hgc := native_ode_gate_count q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.nd N z₀) (q.nd_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (fun c => liftC (srcC c)) hsrcV'
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hp]
      exact hV
    · -- gates
      rw [hp]
      have hUJl : q.pub.UJg.length = q.pub.σ + 3 := GateBinaryODE.hadUJ4_length q.pub.σ q.pub.hσ
      have hPG := q.privGates_le N z₀
      have hAp := q.wires_le
      have hcZ := q.card_Zg
      have hgc' : ((nprotocol (nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
          (fun c => liftC (srcC c))) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
          9000 * q.g * (((q.pub.params.d : ℝ) + 1) * ((q.pub.params.a : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.UJg.length : ℕ) : ℝ) +
            ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ)) + ((q.pub.params.k : ℝ) + 1) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN (liftC (srcC false)) : ℝ) + nGatesN (liftC (srcC true))) +
            ((Fintype.card (Fin (q.k + 1)) : ℝ) + Fintype.card Zs +
              Fintype.card (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) + q.ar.bT +
              q.ar.bP + q.ar.A)) := hgc
      rw [hUJl, hGs, hGs, Fintype.card_fin, hcZ] at hgc'
      have hSm : (q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k ≤
          2 * (words q.pub : ℝ) := by
        have hσ := q.pub.hσ
        have : q.pub.kx + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k ≤
            2 * words q.pub := by
          unfold words
          omega
        exact_mod_cast this
      have hl : (q.pub.params.l : ℝ) ≤ words q.pub := by
        have : q.pub.params.l ≤ words q.pub := by
          unfold words
          omega
        exact_mod_cast this
      have hPG' : ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ) ≤ 65944 * ((words q.pub : ℝ) + 1) ^ 3 := by
        exact_mod_cast hPG
      have hcube := GateBitBudget.cube_le (add_nonneg hwr0 (by linarith)) hB0 (c := 300) hw
      have e1 : ((q.pub.params.a : ℕ) : ℝ) = (q.k : ℝ) + 4 := by
        show ((q.k + 1 + 3 : ℕ) : ℝ) = _
        push_cast
        ring
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hd' hJ' ⊢
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
      have key1 := GateODEBudget.gate_budget_arith 9000 q.g Q
        (logBudget q.g q.ε) (q.pub.params.d : ℝ) (q.pub.params.J : ℝ) (q.pub.params.k : ℝ)
        (q.pub.params.l : ℝ)
        (((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ))
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT +
          q.ar.bP + q.ar.A)
        (by norm_num) hg0 hQ1 hℓ1 hd' hJ' (Nat.cast_nonneg _) (Nat.cast_nonneg _) hXs0 hG0 hAw0
      have key2 := words_gate_arith_g 36873000 (3 * 10 ^ 12) q.g Q (logBudget q.g q.ε)
        (words q.pub : ℝ) ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ)
        ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k)
        (q.pub.params.l : ℝ) ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (Fintype.card Zs : ℝ)
        (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP + q.ar.A)
        (by norm_num) (by norm_num) hg0 hQ1 hℓ1 hwr0 hPG' hSm (Nat.cast_nonneg _) hl hAp hG0 hZ0
      have key3 := GateBitBudget.budget_mono (c := 3 * 10 ^ 12) (C := 10 ^ 20) (k := (300 + 1) ^ 3)
        (g := q.g) (Q := Q) (a := ((words q.pub : ℝ) + logBudget q.g q.ε + 1) ^ 3)
        (b := (B + 1) ^ 3) (S₁ := (nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (S₂ := (Fintype.card Zs : ℝ)) (by norm_num) hg0 (by linarith) (by positivity) hG0 hZ0
        (by norm_num) hcube (by norm_num)
      have e2 : 4097 * 9000 * q.g * (Q * ((((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (q.nd N z₀) q.ar : ℕ) : ℝ)) +
            q.pub.params.k + 1 + logBudget q.g q.ε * ((q.pub.params.l : ℝ) + 1)) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) + q.ar.bT +
              q.ar.bP + q.ar.A)) =
          36873000 * q.g * (Q * (((privGates (q.nd N z₀) q.ar : ℕ) : ℝ) +
            ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k) +
            logBudget q.g q.ε * ((q.pub.params.l : ℝ) + 1) + 8) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
            ((Fintype.card Zs : ℝ) + (((q.k + 1 : ℕ) : ℝ) + ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) +
              q.ar.bT + q.ar.bP + q.ar.A))) := by
        rw [e1]
        push_cast
        ring
      exact hgc'.trans (key1.trans (le_of_eq e2 |>.trans (key2.trans key3)))
    · -- calls
      intro c
      rw [hp, if_neg hz]
      have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
        split_ifs <;> norm_num
      have hcV := q.nd_nCalls N z₀ c
      have hcP : (nCallsN c (nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
          (fun c => liftC (srcC c))) : ℝ) ≤ 12 * (q.pub.params.d : ℝ) * (6 *
            ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
              (if c Query.value then 1 else 0))) +
          ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := by
        have h1 : nCallsN c (nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
            (fun c => liftC (srcC c))) ≤ 12 * q.pub.params.d * nCallsN c (q.nd N z₀).V +
              nCallsN c (liftC (srcC false)) + nCallsN c (liftC (srcC true)) := hC c
        rw [hCs, hCs] at h1
        have h2 : nCallsN c (nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
            (fun c => liftC (srcC c))) ≤ 12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c (srcC false) +
              nCallsN c (srcC true) :=
          h1.trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ hcV) _) _)
        have h3 : ((nCallsN c (nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
            (fun c => liftC (srcC c))) : ℕ) : ℝ) ≤ ((12 * q.pub.params.d * (6 *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) + nCallsN c (srcC false) +
              nCallsN c (srcC true) : ℕ) : ℝ) := by exact_mod_cast h2
        refine h3.trans (le_of_eq ?_)
        push_cast
        split_ifs <;> ring
      have hW : ((nprotocol (nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
          (fun c => liftC (srcC c))) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
          40 * q.g * (nCallsN c (nprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar
            (fun c => liftC (srcC c))) : ℝ) := hWC c
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD q.g q.ε = Q at hd' ⊢
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hcP ⊢
      have h4 := mul_le_mul_of_nonneg_left hd' (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤
        40 * 72) hg0) hI0)
      have h5 := mul_le_mul_of_nonneg_left hcP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) hg0)
      have e6 : 40 * q.g * (12 * (q.pub.params.d : ℝ) * (6 * I) + ((nCallsN c (srcC false) : ℝ) +
          nCallsN c (srcC true))) = 40 * 72 * q.g * I * (q.pub.params.d : ℝ) +
          40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := by ring
      have e7 : 40 * 72 * q.g * I * (4096 * Q) = 11796480 * q.g * Q * I := by ring
      rw [e6] at h5
      rw [e7] at h4
      exact hW.trans (h5.trans (add_le_add h4 le_rfl))

end Budget

end

end SparseHamiltonian.GeneralSparseODE
