import GeneralDecoderODE.SolverTime
import GeneralDecoderODE.SolverBudget
import GeneralSparseODE.TimeBudget

/-!
# The budget of the time-dependent general solver through any implementation

For the public data `q : GPubT`, an implementation `impl` of the padded oracles with at most `G`
gates per call and at most `c` calls per call, all of the kind of the call (`KindOK impl id c`), on
the ancillas `Xa`, put `q*' = qOf s' T η_H η_D (2g) (ε/2)`, `𝔴` the register words of the padded
problem and `𝔟' = bitB b_data (2^{k+1}) (2^m) (2^m) q*' g ε`
(`GeneralSparseODE.general_time_budget`). The protocol `nprotocol (prepTI q impl loadC wpC) (2g)`
has (`general_time_budgetI`)

* valid trials;
* at most `1.8·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|] + 6·10¹² g (q*' G + |Xa|)` elementary gates in
  every history (`G_src = |loadC| + 2 |wpC|`): each private call costs at most
  `65536 (𝔴+1)³ + 12 G` gates;
* at most `2.8·10¹¹ (𝔟'+1)³ + 2 |Zs| + 2 |Xa|` qubits;
* at most `7864320 c g q*'` supplied calls of each kind of matrix oracle (none in the zero case),
  besides `80 g` times the calls of `loadC` and twice those of `wpC`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoderODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE
open SparseHamiltonian.OracleCircuit
open GateBinaryODE (SZ4 card_SZ4 hadUJ4_ok)
open GateBinaryODETime (PubT)
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase tzprepC btpublicOK_of btparams_ok0
  btzeroCase_params)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf wordsT gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Query)

/-- The passage from the words to `𝔟` with the implementation terms kept apart, for the constants
`c` and `C` with `301³ c ≤ C`. -/
theorem budget_mono_c (c C g Q a B Gs Zs G X : ℝ) (hc : 0 ≤ c) (hcC : c * (300 + 1) ^ 3 ≤ C)
    (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hB : 0 ≤ B) (ha : a ≤ (300 + 1) ^ 3 * (B + 1) ^ 3)
    (hGs : 0 ≤ Gs) (hZs : 0 ≤ Zs) :
    c * g * (Q * (a + G) + Gs + Zs + X) ≤
      C * g * (Q * (B + 1) ^ 3 + Gs + Zs) + c * g * (Q * G + X) := by
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : Q * a ≤ Q * ((300 + 1) ^ 3 * (B + 1) ^ 3) := mul_le_mul_of_nonneg_left ha hQ0
  have hY : 0 ≤ Q * (B + 1) ^ 3 := by positivity
  have hcg : 0 ≤ c * g := mul_nonneg hc hg
  have h2 : c * g * (Q * a) ≤ c * g * ((300 + 1) ^ 3 * (Q * (B + 1) ^ 3)) := by
    have := mul_le_mul_of_nonneg_left h1 hcg
    have e : Q * ((300 + 1) ^ 3 * (B + 1) ^ 3) = (300 + 1) ^ 3 * (Q * (B + 1) ^ 3) := by ring
    rw [e] at this
    exact this
  have h3 : c * g * ((300 + 1) ^ 3 * (Q * (B + 1) ^ 3)) ≤ C * g * (Q * (B + 1) ^ 3) := by
    have e : c * g * ((300 + 1) ^ 3 * (Q * (B + 1) ^ 3)) =
        (c * (300 + 1) ^ 3) * (g * (Q * (B + 1) ^ 3)) := by ring
    have e' : C * g * (Q * (B + 1) ^ 3) = C * (g * (Q * (B + 1) ^ 3)) := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_right hcC (mul_nonneg hg hY)
  have hcC' : c ≤ C := by nlinarith
  have h4 : c * g * (Gs + Zs) ≤ C * g * (Gs + Zs) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC' hg) (by positivity)
  nlinarith

namespace GPubTI

variable (q : GPubT)

/-! ### The register -/

theorem card_ZgTI (Xa : Type*) [Fintype Xa] :
    Fintype.card (SZ4 (q.k + 1) q.b ⊕ Xa) = 6 * q.k + 6 + 4 * q.b + Fintype.card Xa := by
  rw [Fintype.card_sum, card_SZ4]
  ring

/-- **The register of the time-dependent general solver through an implementation**: the released
register of the padded problem with the ancillas of the implementation in the private scratch. -/
abbrev regTI (Xa Zs : Type*) [Fintype Xa] [Fintype Zs] :=
  TNW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa) (arTI q Xa).bT (arTI q Xa).bP
    (arTI q Xa).A

/-- **The register of the time-dependent general solver through an implementation** has `2 |Xa|`
more qubits than the released register of the padded problem. -/
theorem card_regTI (Xa Zs : Type*) [Fintype Xa] [Fintype Zs] :
    Fintype.card (regTI q Xa Zs) =
      Fintype.card (TNW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
        q.pub.ar.bP q.pub.ar.A) + 2 * Fintype.card Xa := by
  have h1 := ZeroTimeGateODE.card_ZNW (S := Fin (q.k + 1)) (Zs := Zs)
    (Z := SZ4 (q.k + 1) q.b ⊕ Xa) q.pub.params.a q.pub.params.m
    q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f (arTI q Xa).bT
    (arTI q Xa).bP (arTI q Xa).A
  have h2 := ZeroTimeGateODE.card_ZNW (S := Fin q.pub.kx) (Zs := Zs) (Z := SZ4 q.pub.kx q.pub.b)
    q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l
    q.pub.params.f q.pub.ar.bT q.pub.ar.bP q.pub.ar.A
  have e1 : Fintype.card (regTI q Xa Zs) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a
      q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f
      (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa) (arTI q Xa).bT (arTI q Xa).bP
      (arTI q Xa).A) := rfl
  have e2 : Fintype.card (TNW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
      q.pub.ar.bP q.pub.ar.A) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a q.pub.params.m
      q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f (Fin q.pub.kx)
      Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT q.pub.ar.bP q.pub.ar.A) := rfl
  rw [e1, e2, h1, h2, card_ZgTI, card_SZ4, Fintype.card_fin, Fintype.card_fin]
  have hb : (arTI q Xa).bT = q.pub.ar.bT := rfl
  have hp : (arTI q Xa).bP = q.pub.ar.bP := rfl
  have ha : (arTI q Xa).A = q.pub.ar.A := rfl
  have hk : q.pub.kx = q.k + 1 := rfl
  have hbb : q.pub.b = q.b := rfl
  omega

/-- **The register in the words**: at most `10000 (𝔴+1)³ + 2 |Zs| + 2 |Xa|` qubits. -/
theorem card_regTI_le (Xa Zs : Type*) [Fintype Xa] [Fintype Zs] :
    Fintype.card (regTI q Xa Zs) ≤
      10000 * (wordsT q.pub + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Xa := by
  rw [card_regTI]
  have h1 := GateRemarks.ODE.card_TNW_le q.pub (Zs := Zs)
  omega

/-- **The per-call cost of the operation in the words**: at most `65536 (𝔴+1)³ + 12 G` for `G`
gates per call of the implementation. -/
theorem privGatesTI_le {Y Xa : Type*}
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query)) (G : ℕ)
    (hG : ∀ j, nGatesN (impl j) ≤ G) :
    privGates (ndTI q impl) (arTI q Xa) ≤ 65536 * (wordsT q.pub + 1) ^ 3 + 12 * G := by
  have hV := ndTI_nGates q impl G hG
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_time_arith_words q.pub
  have hl : (arTI q Xa).circ.length = q.pub.ar.circ.length := liftA_circ_length _
  have hb2 : (arTI q Xa).bP = q.pub.ar.bP := rfl
  have hb3 : (arTI q Xa).bT = q.pub.ar.bT := rfl
  have hkx : q.pub.kx = q.k + 1 := rfl
  unfold privGates
  rw [hl, hb2, hb3]
  omega

/-- **The arithmetic and scratch wires of the operation in the words**, without the ancillas of
the implementation: at most `4200 (𝔴+1)³`. -/
theorem wiresTI_le (Xa : Type*) :
    ((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) + (arTI q Xa).bT + (arTI q Xa).bP +
      (arTI q Xa).A ≤ 4200 * ((wordsT q.pub : ℝ) + 1) ^ 3 := by
  have h := q.wires_le
  have e1 : ((arTI q Xa).bT : ℝ) = (q.ar.bT : ℝ) := rfl
  have e2 : ((arTI q Xa).bP : ℝ) = (q.ar.bP : ℝ) := rfl
  have e3 : ((arTI q Xa).A : ℝ) = (q.ar.A : ℝ) := rfl
  have h2 : ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) ≤ ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega)
  rw [e1, e2, e3]
  linarith

end GPubTI

/-! ### The budget -/

section Budget

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

set_option maxHeartbeats 8000000 in
/-- **The budget of the time-dependent general solver through any implementation in `𝔟`** (every
`T ≥ 0`). For the hypotheses of `GeneralSparseODE.general_time_budget` and a valid implementation
`impl` of the padded oracles with at most `G` gates and at most `c` calls per call, all of the kind
of the call, put `𝔟' = bitB b_data (2^{k+1}) (2^m) (2^m) q*' g ε`. The protocol
`nprotocol (prepTI q impl loadC wpC) (2g)` has valid trials, at most
`1.8·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|] + 6·10¹² g (q*' G + |Xa|)` elementary gates in every
history, at most `2.8·10¹¹ (𝔟'+1)³ + 2 |Zs| + 2 |Xa|` qubits, and at most
`(if BTZeroCase then 0 else 7864320 c g q*' ([row] + [col] + [value])) +
80 g (calls_p(loadC) + 2 calls_p(wpC))` calls of every kind `p` of the primitives. -/
theorem general_time_budgetI (bd : ℕ) (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : if BTZeroCase q.pub then HasBits bd q.γ
      else q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (hv : ∀ j, ∀ i ∈ impl j, i.Valid) (G c : ℕ) (hG : ∀ j, nGatesN (impl j) ≤ G)
    (hK : KindOK impl id c)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepTI q impl loadC wpC) j, i.Valid) ∧
    ((nprotocol (prepTI q impl loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      18 * 10 ^ 19 * q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
            (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) +
      6 * 10 ^ 12 * q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * G +
        Fintype.card Xa) ∧
    (Fintype.card (GPubTI.regTI q Xa Zs) : ℝ) ≤
      28 * 10 ^ 10 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
          (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    (∀ p : Query → Bool, ((nprotocol (prepTI q impl loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN p) : ℝ) ≤
      (if BTZeroCase q.pub then 0 else
        7864320 * c * q.g * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0))) +
        80 * q.g * ((nCallsN p loadC : ℝ) + 2 * nCallsN p wpC)) := by
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
  have hX0 : (0 : ℝ) ≤ Fintype.card Xa := Nat.cast_nonneg _
  have hGr0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
  -- the register
  have hspace : (Fintype.card (GPubTI.regTI q Xa Zs) : ℝ) ≤ 28 * 10 ^ 10 * (B + 1) ^ 3 +
      2 * Fintype.card Zs + 2 * Fintype.card Xa := by
    have h1 : (Fintype.card (GPubTI.regTI q Xa Zs) : ℝ) ≤ 10000 * ((wordsT q.pub : ℝ) + 1) ^ 3 +
        2 * Fintype.card Zs + 2 * Fintype.card Xa := by
      exact_mod_cast GPubTI.card_regTI_le q Xa Zs
    have hcube := GateBitBudget.cube_le hwr0 hB0 (c := 300) (by linarith)
    have : (10000 : ℝ) * ((wordsT q.pub : ℝ) + 1) ^ 3 ≤ 10000 * ((300 + 1) ^ 3 * (B + 1) ^ 3) :=
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
      (S := Fin (q.k + 1)) (Zs := Zs) (Z := SZ4 (q.k + 1) q.b ⊕ Xa)
      (Y := Fin q.m ⊕ Y) (J := Query) q.pub.params q.pub.params.a q.pub.params.m
      q.pub.params.r q.pub.params.K q.pub.params.l q.pub.params.f (arTI q Xa).bT (arTI q Xa).bP
      (arTI q Xa).A
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
      (btzeroCase_params hq hz) (liftC loadC) hloadV' wpC hwpV
    have hpr : prepTI q impl loadC wpC = tzprepC (liftC loadC) wpC := by
      rw [prepTI, if_pos hz]
      rfl
    have htest : Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arTI q Xa).bT (arTI q Xa).bP
          (arTI q Xa).A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
        Fintype.card (GPubTI.regTI q Xa Zs) := by
      have h1 := (hcardZ : Fintype.card (GPubTI.regTI q Xa Zs) = _)
      have h2 : Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arTI q Xa).bT
          (arTI q Xa).bP (arTI q Xa).A) = Fintype.card (SZ4 (q.k + 1) q.b ⊕ Xa) +
            (arTI q Xa).bT + (arTI q Xa).bP + (arTI q Xa).A + 3 := by
        simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [h1, h2]
      omega
    have htest' : (Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.m q.pub.params.l q.pub.params.f) : ℝ) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arTI q Xa).bT (arTI q Xa).bP
          (arTI q Xa).A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
        Fintype.card (GPubTI.regTI q Xa Zs) := by
      exact_mod_cast htest
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hpr]
      exact hV
    · -- gates
      rw [hpr]
      have hWG' : ((nprotocol (tzprepC (liftC loadC) wpC : List (NInstr (GPubTI.regTI q Xa Zs)
          (Fin q.m ⊕ Y) Query)) q.pub.params.ratio
          (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
          40 * q.pub.params.ratio * ((nGatesN (liftC loadC) + 2 * nGatesN wpC : ℕ) : ℝ) +
            20 * q.pub.params.ratio * (4 * ((Fintype.card (GateODE.AW q.pub.params.a
              q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.m q.pub.params.l
              q.pub.params.f) : ℝ) +
              Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arTI q Xa).bT
                (arTI q Xa).bP (arTI q Xa).A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1))) +
              3) := hWG
      rw [hGl] at hWG'
      push_cast at hWG'
      refine hWG'.trans ?_
      rw [hr]
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q at hQ1 ⊢
      have h1 := mul_le_mul_of_nonneg_left htest' hg0
      have h2 : q.g * (Fintype.card (GPubTI.regTI q Xa Zs) : ℝ) ≤
          q.g * (28 * 10 ^ 10 * (B + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Xa) :=
        mul_le_mul_of_nonneg_left hspace hg0
      have h3 : q.g * (B + 1) ^ 3 ≤ q.g * (Q * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
      have h4 : q.g * 1 ≤ q.g * (Q * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
      have h5 : 0 ≤ q.g * ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := mul_nonneg hg0 hG0
      have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
      have h7 : 0 ≤ q.g * (Fintype.card Xa : ℝ) := mul_nonneg hg0 hX0
      have h8 : 0 ≤ q.g * (Q * (G : ℝ)) := mul_nonneg hg0 (mul_nonneg (by linarith) hGr0)
      linarith
    · -- calls
      intro p
      rw [hpr, if_pos hz, zero_add]
      have hW : ((nprotocol (tzprepC (liftC loadC) wpC : List (NInstr (GPubTI.regTI q Xa Zs)
          (Fin q.m ⊕ Y) Query)) q.pub.params.ratio
          (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN p) : ℝ) ≤
          40 * q.pub.params.ratio * ((nCallsN p (liftC loadC) + 2 * nCallsN p wpC : ℕ) : ℝ) :=
        hWC p
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
    have hpr : prepTI q impl loadC wpC =
        tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa) (liftC loadC) wpC := by
      rw [prepTI, if_neg hz]
    obtain ⟨hV, -, hC, -, hWC, -, -⟩ := native_ode_time_solver q.pub.params (q.pub.params_ok hP)
      q.pub.UJg (hadUJ4_ok q.pub.σ q.pub.hσ) (ndTI q impl) (ndTI_public q hv) (arTI q Xa) q.ζ
      hP.ζ_pos.le (arTI_ok q hP impl) (liftC loadC) hloadV' wpC hwpV
    have hgc := native_ode_time_gate_count q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (ndTI q impl) (ndTI_public q hv) (arTI q Xa) q.ζ hP.ζ_pos.le
      (arTI_ok q hP impl) (liftC loadC) hloadV' wpC hwpV
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hpr]
      exact hV
    · -- gates
      rw [hpr]
      have hUJl : q.pub.UJg.length = q.pub.σ + 3 := GateBinaryODE.hadUJ4_length q.pub.σ q.pub.hσ
      have hPG := GPubTI.privGatesTI_le q impl G hG
      have hAp := GPubTI.wiresTI_le q Xa
      have hcZ := GPubTI.card_ZgTI q Xa
      have hgc' : ((nprotocol (tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa)
          (liftC loadC) wpC) q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost
            wGateN : ℝ) ≤
          18000 * q.pub.params.g * (((q.pub.params.d : ℝ) + 1) * ((q.pub.params.a : ℝ) +
            q.pub.params.m + q.pub.params.r + 1 + ((q.pub.UJg.length : ℕ) : ℝ) +
            ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ)) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN (liftC loadC) : ℝ) + 2 * nGatesN wpC) +
            ((Fintype.card (Fin (q.k + 1)) : ℝ) + Fintype.card Zs +
              Fintype.card (SZ4 (q.k + 1) q.b ⊕ Xa) + (arTI q Xa).bT +
              (arTI q Xa).bP + (arTI q Xa).A)) := hgc
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
      have hPG' : ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ) ≤
          65536 * ((wordsT q.pub : ℝ) + 1) ^ 3 + 12 * (G : ℝ) := by
        exact_mod_cast hPG
      have hcube := GateBitBudget.cube_le (add_nonneg hwr0 (by linarith)) hB0 (c := 300) hw
      have e1 : ((q.pub.params.a : ℕ) : ℝ) = (q.k : ℝ) + 4 := by
        show ((q.k + 1 + 3 : ℕ) : ℝ) = _
        push_cast
        ring
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q
        at hQ1 hd' hJ' ⊢
      have hXs0 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ (q.pub.params.m : ℝ) := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ (q.pub.params.r : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ ((q.pub.σ + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have hAw0 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs +
          ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) + (arTI q Xa).bT + (arTI q Xa).bP +
          (arTI q Xa).A := by
        have h1 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ ((arTI q Xa).bT : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ ((arTI q Xa).bP : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ ((arTI q Xa).A : ℝ) := Nat.cast_nonneg _
        linarith
      have key1 := GateODEBudget.gate_budget_arith' 18000 q.g Q
        (logBudget (2 * q.g) (q.ε / 2)) (q.pub.params.d : ℝ) (q.pub.params.J : ℝ)
        (q.pub.params.l : ℝ)
        (((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ))
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) +
          (arTI q Xa).bT + (arTI q Xa).bP + (arTI q Xa).A)
        (by norm_num) hg0 hQ1 hℓ1 hd' hJ' (Nat.cast_nonneg _) hXs0 hG0 hAw0
      have hAp' : ((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) + (arTI q Xa).bT +
          (arTI q Xa).bP + (arTI q Xa).A + Fintype.card Xa ≤
          4200 * ((wordsT q.pub : ℝ) + 1) ^ 3 + Fintype.card Xa := by linarith
      have key2 := words_gate_arith_i 73746000 (6 * 10 ^ 12) q.g Q (logBudget (2 * q.g) (q.ε / 2))
        (wordsT q.pub : ℝ) ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ)
        ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r)
        (q.pub.params.l : ℝ) ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
        (Fintype.card Zs : ℝ)
        (((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) + (arTI q Xa).bT +
          (arTI q Xa).bP + (arTI q Xa).A + Fintype.card Xa) (G : ℝ) (Fintype.card Xa : ℝ)
        (by norm_num) (by norm_num) hg0 hQ1 hℓ1 hwr0 hPG' hSm (Nat.cast_nonneg _) hl hAp' hG0 hZ0
        hGr0 hX0
      have key3 := budget_mono_c (6 * 10 ^ 12) (18 * 10 ^ 19) q.g Q
        (((wordsT q.pub : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3) B
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) (Fintype.card Zs : ℝ) (G : ℝ)
        (Fintype.card Xa : ℝ) (by norm_num) (by norm_num) hg0 hQ1 hB0 hcube hG0 hZ0
      have e2 : 4097 * 18000 * q.g * (Q * ((((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) +
            ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ)) + 1 +
            logBudget (2 * q.g) (q.ε / 2) * ((q.pub.params.l : ℝ) + 1)) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs +
              ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) +
              (arTI q Xa).bT + (arTI q Xa).bP + (arTI q Xa).A)) =
          73746000 * q.g * (Q * (((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ) +
            ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r) +
            logBudget (2 * q.g) (q.ε / 2) * ((q.pub.params.l : ℝ) + 1) + 8) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            ((Fintype.card Zs : ℝ) + (((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) +
              (arTI q Xa).bT + (arTI q Xa).bP + (arTI q Xa).A + Fintype.card Xa))) := by
        rw [e1]
        push_cast
        ring
      have hgc'' : ((nprotocol (tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa)
          (liftC loadC) wpC) q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost
            wGateN : ℝ) ≤
          18000 * q.g * (((q.pub.params.d : ℝ) + 1) * (((q.pub.params.a : ℕ) : ℝ) +
            q.pub.params.m + q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) +
            ((privGates (ndTI q impl) (arTI q Xa) : ℕ) : ℝ)) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs +
              ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) +
              (arTI q Xa).bT + (arTI q Xa).bP + (arTI q Xa).A)) := by
        refine hgc'.trans (le_of_eq ?_)
        push_cast
        ring
      exact hgc''.trans (key1.trans (le_of_eq e2 |>.trans (key2.trans key3)))
    · -- calls
      intro p
      rw [hpr, if_neg hz]
      have hI0 : (0 : ℝ) ≤ (if p Query.rowLocation then 1 else 0) +
          (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) := by
        split_ifs <;> norm_num
      have hcV := ndTI_nCalls q hK p
      have hcP : (nCallsN p (tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa)
          (liftC loadC) wpC) : ℝ) ≤ 12 * (q.pub.params.d : ℝ) * (2 * c *
            ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) +
          ((nCallsN p loadC : ℝ) + 2 * nCallsN p wpC) := by
        have h1 : nCallsN p (tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa)
            (liftC loadC) wpC) ≤
            12 * q.pub.params.d * nCallsN p (ndTI q impl).V + nCallsN p (liftC loadC) +
              2 * nCallsN p wpC := hC p
        rw [hCl] at h1
        have h2 : nCallsN p (tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa)
            (liftC loadC) wpC) ≤
            12 * q.pub.params.d * (2 * c *
              ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) + nCallsN p loadC + 2 * nCallsN p wpC :=
          h1.trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ hcV) _) _)
        have h3 : ((nCallsN p (tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa)
            (liftC loadC) wpC) : ℕ) : ℝ) ≤ ((12 * q.pub.params.d * (2 * c *
              ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) + nCallsN p loadC + 2 * nCallsN p wpC : ℕ) :
                  ℝ) := by
          exact_mod_cast h2
        refine h3.trans (le_of_eq ?_)
        push_cast
        split_ifs <;> ring
      have hW : ((nprotocol (tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa)
          (liftC loadC) wpC) q.pub.params.ratio (q.pub.params.ratio_ge hq.g_ge)).worstCost
            (wCallN p) : ℝ) ≤
          40 * q.pub.params.ratio * (nCallsN p (tnprepC q.pub.params q.pub.UJg (ndTI q impl)
            (arTI q Xa) (liftC loadC) wpC) : ℝ) := hWC p
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q at hd' ⊢
      generalize hId : ((if p Query.rowLocation then 1 else 0) +
          (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) : ℝ) = I
        at hI0 hcP ⊢
      have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
      have h4 := mul_le_mul_of_nonneg_left hd' (mul_nonneg (mul_nonneg (mul_nonneg
        (by norm_num : (0 : ℝ) ≤ 80 * 24) hc0) hg0) hI0)
      have h5 := mul_le_mul_of_nonneg_left hcP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) hg0)
      have e6 : 80 * q.g * (12 * (q.pub.params.d : ℝ) * (2 * c * I) + ((nCallsN p loadC : ℝ) +
          2 * nCallsN p wpC)) = 80 * 24 * c * q.g * I * (q.pub.params.d : ℝ) +
          80 * q.g * ((nCallsN p loadC : ℝ) + 2 * nCallsN p wpC) := by ring
      have e7 : 80 * 24 * c * q.g * I * (4096 * Q) = 7864320 * c * q.g * Q * I := by ring
      have e8 : 40 * q.pub.params.ratio * (nCallsN p (tnprepC q.pub.params q.pub.UJg (ndTI q impl)
          (arTI q Xa) (liftC loadC) wpC) : ℝ) = 80 * q.g * (nCallsN p (tnprepC q.pub.params
            q.pub.UJg (ndTI q impl) (arTI q Xa) (liftC loadC) wpC) : ℝ) := by
        rw [hr]
        ring
      rw [e6] at h5
      rw [e7] at h4
      rw [e8] at hW
      exact hW.trans (h5.trans (add_le_add h4 le_rfl))

end Budget

end

end SparseHamiltonian.GeneralDecoderODE
