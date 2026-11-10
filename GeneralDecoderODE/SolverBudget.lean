import GeneralDecoderODE.Solver
import GeneralSparseODE.ConstantBudget

/-!
# The budget of the constant-coefficient general solver through any implementation

For the public data `q : GPub`, an implementation `impl` of the padded oracles with at most `G`
gates per call and at most `c` calls per call, all of the kind of the call (`KindOK impl id c`), on
the ancillas `Xa`, put `q* = qOf s' T η_H η_D g ε`, `𝔴` the register words of the padded problem
and `𝔟₀ = bitB b_data (2^{k+1}) 0 0 q* g ε` (`GeneralSparseODE.general_ode_budget`). The protocol
`nprotocol (prepI q impl srcC) g` has (`general_ode_budgetI`)

* valid trials;
* at most `9·10¹⁹ g [q* (𝔟₀+1)³ + G_src + |Zs|] + 3·10¹² g (q* G + |Xa|)` elementary gates in every
  history: each private call costs at most `65536 (𝔴+1)³ + 12 G` gates (`privGatesI_le`);
* at most `2.8·10¹¹ (𝔟₀+1)³ + 2 |Zs| + 2 |Xa|` qubits (`card_regI`: the released register of the
  padded problem with the ancillas in both copies of the private scratch);

the constants `9·10¹⁹` and `2.8·10¹¹` leave room below the constants `10²⁰` and `3·10¹¹` of the
released bounds for the words of the implementation.
* at most `3932160 c g q*` supplied calls of each kind of matrix oracle (none in the zero case),
  `c` times the released count, besides `40 g` times the calls of the source circuits.
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
open GateBinaryODE (Pub SZ4 card_SZ4 hadUJ4_ok)
open ZeroTimeGateODE (BPublicOK0 BZeroCase zprepC srcRot bpublicOK_of)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf words gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Query)

/-! ### Arithmetic -/

/-- The arithmetic of the gate budget in the words with implementation gates `G` and ancillas
`X`: as `GeneralSparseODE.words_gate_arith_g`, for `G_C ≤ 65536 (𝔴+1)³ + 12 G` and
`A ≤ 4200 (𝔴+1)³ + X`. -/
theorem words_gate_arith_i (c C g Q ℓ w GC Sm l Gs Zs Ap G X : ℝ) (hcC : 69747 * c ≤ C)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hℓ : 1 ≤ ℓ) (hw : 0 ≤ w)
    (hGC : GC ≤ 65536 * (w + 1) ^ 3 + 12 * G) (hSm : Sm ≤ 2 * w) (hl0 : 0 ≤ l) (hl : l ≤ w)
    (hAp : Ap ≤ 4200 * (w + 1) ^ 3 + X) (hGs : 0 ≤ Gs) (hZs : 0 ≤ Zs) (hG : 0 ≤ G)
    (hX : 0 ≤ X) :
    c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap)) ≤
      C * g * (Q * ((w + ℓ + 1) ^ 3 + G) + Gs + Zs + X) := by
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
  have hS : GC + Sm + ℓ * (l + 1) + 8 ≤ 65547 * Y + 12 * G := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have hQY : Y ≤ Q * Y := le_mul_of_one_le_left hY0 hQ
  have hQG : 0 ≤ Q * G := mul_nonneg hQ0 hG
  have h1 := mul_le_mul_of_nonneg_left hS hQ0
  have hin : Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap) ≤
      69747 * (Q * (Y + G) + Gs + Zs + X) := by
    linarith
  have hpos : 0 ≤ Q * (Y + G) + Gs + Zs + X := by positivity
  calc c * g * (Q * (GC + Sm + ℓ * (l + 1) + 8) + Gs + (Zs + Ap))
      ≤ c * g * (69747 * (Q * (Y + G) + Gs + Zs + X)) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg hc hg)
    _ = 69747 * c * g * (Q * (Y + G) + Gs + Zs + X) := by ring
    _ ≤ C * g * (Q * (Y + G) + Gs + Zs + X) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hg) hpos

/-- The passage from the words to `𝔟₀` with the implementation terms kept apart. -/
theorem budget_mono_i (g Q a B Gs Zs G X : ℝ) (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hB : 0 ≤ B)
    (ha : a ≤ (300 + 1) ^ 3 * (B + 1) ^ 3) (hGs : 0 ≤ Gs) (hZs : 0 ≤ Zs) :
    3 * 10 ^ 12 * g * (Q * (a + G) + Gs + Zs + X) ≤
      9 * 10 ^ 19 * g * (Q * (B + 1) ^ 3 + Gs + Zs) + 3 * 10 ^ 12 * g * (Q * G + X) := by
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : Q * a ≤ Q * ((300 + 1) ^ 3 * (B + 1) ^ 3) := mul_le_mul_of_nonneg_left ha hQ0
  have hY : 0 ≤ Q * (B + 1) ^ 3 := by positivity
  have h2 : 3 * 10 ^ 12 * (Q * a) ≤ 9 * 10 ^ 19 * (Q * (B + 1) ^ 3) := by nlinarith
  have h3 : 3 * 10 ^ 12 * g * (Q * a) ≤ 9 * 10 ^ 19 * g * (Q * (B + 1) ^ 3) := by
    have := mul_le_mul_of_nonneg_left h2 hg
    linarith
  have h4 : 3 * 10 ^ 12 * g * (Gs + Zs) ≤ 9 * 10 ^ 19 * g * (Gs + Zs) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg) (by positivity)
  nlinarith

namespace GPubI

variable (q : GPub)

/-! ### The register -/

theorem card_ZgI (Xa : Type*) [Fintype Xa] :
    Fintype.card (SZ4 (q.k + 1) q.b ⊕ Xa) = 6 * q.k + 6 + 4 * q.b + Fintype.card Xa := by
  rw [Fintype.card_sum, card_SZ4]
  ring

/-- **The register of the general solver through an implementation**: the released register of
the padded problem with the ancillas of the implementation in the private scratch. -/
abbrev regI (Xa Zs : Type*) [Fintype Xa] [Fintype Zs] :=
  NW q.pub.params (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa) (arI q Xa).bT (arI q Xa).bP
    (arI q Xa).A

/-- **The register of the general solver through an implementation** has `2 |Xa|` more qubits than
the released register of the padded problem (the ancillas in both copies of the private
scratch). -/
theorem card_regI (Xa Zs : Type*) [Fintype Xa] [Fintype Zs] :
    Fintype.card (regI q Xa Zs) =
      Fintype.card (NW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
        q.pub.ar.bP q.pub.ar.A) + 2 * Fintype.card Xa := by
  have h1 := ZeroTimeGateODE.card_ZNW (S := Fin (q.k + 1)) (Zs := Zs)
    (Z := SZ4 (q.k + 1) q.b ⊕ Xa) q.pub.params.a q.pub.params.m
    q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f (arI q Xa).bT
    (arI q Xa).bP (arI q Xa).A
  have h2 := ZeroTimeGateODE.card_ZNW (S := Fin q.pub.kx) (Zs := Zs) (Z := SZ4 q.pub.kx q.pub.b)
    q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l
    q.pub.params.f q.pub.ar.bT q.pub.ar.bP q.pub.ar.A
  have e1 : Fintype.card (regI q Xa Zs) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a
      q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f
      (Fin (q.k + 1)) Zs (SZ4 (q.k + 1) q.b ⊕ Xa) (arI q Xa).bT (arI q Xa).bP
      (arI q Xa).A) := rfl
  have e2 : Fintype.card (NW q.pub.params (Fin q.pub.kx) Zs (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT
      q.pub.ar.bP q.pub.ar.A) = Fintype.card (ZeroTimeGateODE.ZNW q.pub.params.a q.pub.params.m
      q.pub.params.r q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f (Fin q.pub.kx) Zs
      (SZ4 q.pub.kx q.pub.b) q.pub.ar.bT q.pub.ar.bP q.pub.ar.A) := rfl
  rw [e1, e2, h1, h2, card_ZgI, card_SZ4, Fintype.card_fin, Fintype.card_fin]
  have hb : (arI q Xa).bT = q.pub.ar.bT := rfl
  have hp : (arI q Xa).bP = q.pub.ar.bP := rfl
  have ha : (arI q Xa).A = q.pub.ar.A := rfl
  have hk : q.pub.kx = q.k + 1 := rfl
  have hbb : q.pub.b = q.b := rfl
  omega

/-- **The register in the words**: at most `10000 (𝔴+1)³ + 2 |Zs| + 2 |Xa|` qubits. -/
theorem card_regI_le (Xa Zs : Type*) [Fintype Xa] [Fintype Zs] :
    Fintype.card (regI q Xa Zs) ≤
      10000 * (words q.pub + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Xa := by
  rw [card_regI]
  have h1 := GateRemarks.ODE.card_NW_le q.pub (Zs := Zs)
  omega

/-- **The per-call cost of the operation in the words**: at most `65536 (𝔴+1)³ + 12 G` for `G`
gates per call of the implementation. -/
theorem privGatesI_le {Y Xa : Type*} (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (G : ℕ) (hG : ∀ j, nGatesN (impl j) ≤ G) :
    privGates (ndI q impl) (arI q Xa) ≤ 65536 * (words q.pub + 1) ^ 3 + 12 * G := by
  have hV := ndI_nGates q impl G hG
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_arith_words q.pub
  have hl : (arI q Xa).circ.length = q.pub.ar.circ.length := liftA_circ_length _
  have hb2 : (arI q Xa).bP = q.pub.ar.bP := rfl
  have hb3 : (arI q Xa).bT = q.pub.ar.bT := rfl
  have hkx : q.pub.kx = q.k + 1 := rfl
  unfold privGates
  rw [hl, hb2, hb3]
  omega

/-- **The arithmetic and scratch wires of the operation in the words**, without the ancillas of
the implementation: at most `4200 (𝔴+1)³`. -/
theorem wiresI_le (Xa : Type*) :
    ((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) + (arI q Xa).bT + (arI q Xa).bP +
      (arI q Xa).A ≤ 4200 * ((words q.pub : ℝ) + 1) ^ 3 := by
  have h := q.wires_le
  have e1 : ((arI q Xa).bT : ℝ) = (q.ar.bT : ℝ) := rfl
  have e2 : ((arI q Xa).bP : ℝ) = (q.ar.bP : ℝ) := rfl
  have e3 : ((arI q Xa).A : ℝ) = (q.ar.A : ℝ) := rfl
  have h2 : ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) ≤ ((12 * q.k + 12 + 6 * q.b : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega)
  rw [e1, e2, e3]
  linarith

end GPubI

/-! ### The budget -/

section Budget

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

set_option maxHeartbeats 8000000 in
/-- **The budget of the general solver through any implementation in `𝔟`** (constant
coefficients, every `T ≥ 0`). For the hypotheses of `GeneralSparseODE.general_ode_budget` and a
valid implementation `impl` of the padded oracles with at most `G` gates and at most `c` calls per
call, all of the kind of the call, put `𝔟₀ = bitB b_data (2^{k+1}) 0 0 q* g ε`. The protocol
`nprotocol (prepI q impl srcC) g` has valid trials, at most
`9·10¹⁹ g [q* (𝔟₀+1)³ + G_src + |Zs|] + 3·10¹² g (q* G + |Xa|)` elementary gates in every history,
at most `2.8·10¹¹ (𝔟₀+1)³ + 2 |Zs| + 2 |Xa|` qubits, and at most
`(if BZeroCase then 0 else 3932160 c g q* ([row] + [col] + [value])) + 40 g (calls_p(srcC 0) +
calls_p(srcC 1))` calls of every kind `p` of the primitives. -/
theorem general_ode_budgetI (bd : ℕ) (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : if BZeroCase q.pub then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (hv : ∀ j, ∀ i ∈ impl j, i.Valid) (G c : ℕ) (hG : ∀ j, nGatesN (impl j) ≤ G)
    (hK : KindOK impl id c)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) Y Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepI q impl srcC) j, i.Valid) ∧
    ((nprotocol (prepI q impl srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      9 * 10 ^ 19 * q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) +
      3 * 10 ^ 12 * q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * G + Fintype.card Xa) ∧
    (Fintype.card (GPubI.regI q Xa Zs) : ℝ) ≤
      28 * 10 ^ 10 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    (∀ p : Query → Bool, ((nprotocol (prepI q impl srcC) q.g hq.g_ge).worstCost (wCallN p) : ℝ) ≤
      (if BZeroCase q.pub then 0 else 3932160 * c * q.g * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0))) +
        40 * q.g * ((nCallsN p (srcC false) : ℝ) + nCallsN p (srcC true))) := by
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
  have hX0 : (0 : ℝ) ≤ Fintype.card Xa := Nat.cast_nonneg _
  have hGr0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
  -- the register
  have hspace : (Fintype.card (GPubI.regI q Xa Zs) : ℝ) ≤
      28 * 10 ^ 10 * (B + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Xa := by
    have h1 : (Fintype.card (GPubI.regI q Xa Zs) : ℝ) ≤ 10000 * ((words q.pub : ℝ) + 1) ^ 3 +
        2 * Fintype.card Zs + 2 * Fintype.card Xa := by
      exact_mod_cast GPubI.card_regI_le q Xa Zs
    have hcube := GateBitBudget.cube_le hwr0 hB0 (c := 300) (by linarith)
    have : (10000 : ℝ) * ((words q.pub : ℝ) + 1) ^ 3 ≤ 10000 * ((300 + 1) ^ 3 * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    linarith
  have hsrcV' : ∀ c, ∀ i ∈ liftC (srcC c), i.Valid := fun c => valid_liftC _ (hsrcV c)
  have hGs : ∀ c, nGatesN (liftC (srcC c)) = nGatesN (srcC c) := fun c => nGatesN_liftC _
  have hCs : ∀ (p : Query → Bool) c, nCallsN p (liftC (srcC c)) = nCallsN p (srcC c) :=
    fun p c => nCallsN_liftC p _
  by_cases hz : BZeroCase q.pub
  · -- the direct source assembly
    obtain ⟨hV, -, -, hWG, hWC, -, hcardZ, -⟩ := ZeroTimeGateODE.native_ode_solver_zero
      (S := Fin (q.k + 1)) (Zs := Zs) (Z := SZ4 (q.k + 1) q.b ⊕ Xa)
      (Y := Y) (J := Query) q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.k q.pub.params.l q.pub.params.f (arI q Xa).bT (arI q Xa).bP (arI q Xa).A q.T
      q.g q.ε q.r₀ q.rb
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos
      (fun c => liftC (srcC c)) hsrcV'
    have hp : prepI q impl srcC = zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) := by
      rw [prepI, if_pos hz]
    have htest : Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arI q Xa).bT (arI q Xa).bP
          (arI q Xa).A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
          Fintype.card (GPubI.regI q Xa Zs) := by
      have h1 := (hcardZ : Fintype.card (GPubI.regI q Xa Zs) = _)
      have h2 : Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arI q Xa).bT
          (arI q Xa).bP (arI q Xa).A) = Fintype.card (SZ4 (q.k + 1) q.b ⊕ Xa) +
            (arI q Xa).bT + (arI q Xa).bP + (arI q Xa).A + 3 := by
        simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
        ring
      rw [h1, h2]
      omega
    have htest' : (Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
        q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) : ℝ) +
        Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arI q Xa).bT (arI q Xa).bP
          (arI q Xa).A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1)) ≤
          Fintype.card (GPubI.regI q Xa Zs) := by
      exact_mod_cast htest
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hp]
      exact hV
    · -- gates
      rw [hp]
      have hWG' : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) :
          List (NInstr (GPubI.regI q Xa Zs) Y Query)) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
          40 * q.g * ((nGatesN (liftC (srcC false)) + nGatesN (liftC (srcC true)) + 2 : ℕ) : ℝ) +
            20 * q.g * (4 * ((Fintype.card (GateODE.AW q.pub.params.a q.pub.params.m q.pub.params.r
              q.pub.params.K q.pub.params.k q.pub.params.l q.pub.params.f) : ℝ) +
              Fintype.card (XW (SZ4 (q.k + 1) q.b ⊕ Xa) (arI q Xa).bT (arI q Xa).bP
                (arI q Xa).A) + Fintype.card Zs + Fintype.card (Fin (q.k + 1))) + 3) := hWG
      rw [hGs, hGs] at hWG'
      push_cast at hWG'
      refine hWG'.trans ?_
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD q.g q.ε = Q at hQ1 ⊢
      have h1 := mul_le_mul_of_nonneg_left htest' hg0
      have h2 : q.g * (Fintype.card (GPubI.regI q Xa Zs) : ℝ) ≤
          q.g * (28 * 10 ^ 10 * (B + 1) ^ 3 + 2 * Fintype.card Zs + 2 * Fintype.card Xa) :=
        mul_le_mul_of_nonneg_left hspace hg0
      have h3 : q.g * (B + 1) ^ 3 ≤ q.g * (Q * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
      have h4 : q.g * 1 ≤ q.g * (Q * (B + 1) ^ 3) :=
        mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
      have h5 : 0 ≤ q.g * ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := mul_nonneg hg0 hG0
      have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
      have h7 : 0 ≤ q.g * (Fintype.card Xa : ℝ) := mul_nonneg hg0 hX0
      have h8 : 0 ≤ q.g * (Q * (G : ℝ)) := mul_nonneg hg0 (mul_nonneg (by linarith) hGr0)
      linarith
    · -- calls
      intro p
      rw [hp, if_pos hz, zero_add]
      have hW : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) (fun c => liftC (srcC c)) :
          List (NInstr (GPubI.regI q Xa Zs) Y Query)) q.g hq.g_ge).worstCost (wCallN p) : ℝ) ≤
          40 * q.g * ((nCallsN p (liftC (srcC false)) + nCallsN p (liftC (srcC true)) : ℕ) : ℝ) :=
        hWC p
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
    have hp : prepI q impl srcC =
        nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa) (fun c => liftC (srcC c)) := by
      rw [prepI, if_neg hz]
    obtain ⟨hV, -, hC, -, hWC, -, -⟩ := native_ode_solver q.pub.params (q.pub.params_ok hP)
      q.pub.UJg (hadUJ4_ok q.pub.σ q.pub.hσ) (ndI q impl) (ndI_public q hv) (arI q Xa) q.ζ
      hP.ζ_pos.le (arI_ok q hP impl) (fun c => liftC (srcC c)) hsrcV'
    have hgc := native_ode_gate_count q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (ndI q impl) (ndI_public q hv) (arI q Xa) q.ζ hP.ζ_pos.le
      (arI_ok q hP impl) (fun c => liftC (srcC c)) hsrcV'
    refine ⟨?_, ?_, hspace, ?_⟩
    · rw [hp]
      exact hV
    · -- gates
      rw [hp]
      have hUJl : q.pub.UJg.length = q.pub.σ + 3 := GateBinaryODE.hadUJ4_length q.pub.σ q.pub.hσ
      have hPG := GPubI.privGatesI_le q impl G hG
      have hAp := GPubI.wiresI_le q Xa
      have hcZ := GPubI.card_ZgI q Xa
      have hgc' : ((nprotocol (nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa)
          (fun c => liftC (srcC c))) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
          9000 * q.g * (((q.pub.params.d : ℝ) + 1) * ((q.pub.params.a : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.UJg.length : ℕ) : ℝ) +
            ((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ)) + ((q.pub.params.k : ℝ) + 1) +
            ((q.pub.params.J : ℝ) + 2) * ((q.pub.params.l : ℝ) + 1) +
            ((nGatesN (liftC (srcC false)) : ℝ) + nGatesN (liftC (srcC true))) +
            ((Fintype.card (Fin (q.k + 1)) : ℝ) + Fintype.card Zs +
              Fintype.card (SZ4 (q.k + 1) q.b ⊕ Xa) + (arI q Xa).bT +
              (arI q Xa).bP + (arI q Xa).A)) := hgc
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
      have hPG' : ((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ) ≤
          65536 * ((words q.pub : ℝ) + 1) ^ 3 + 12 * (G : ℝ) := by
        exact_mod_cast hPG
      have hcube := GateBitBudget.cube_le (add_nonneg hwr0 (by linarith)) hB0 (c := 300) hw
      have e1 : ((q.pub.params.a : ℕ) : ℝ) = (q.k : ℝ) + 4 := by
        show ((q.k + 1 + 3 : ℕ) : ℝ) = _
        push_cast
        ring
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hd' hJ' ⊢
      have hXs0 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ) := by
        have h1 : (0 : ℝ) ≤ ((q.pub.params.a : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ (q.pub.params.m : ℝ) := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ (q.pub.params.r : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ ((q.pub.σ + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ ((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have hAw0 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs +
          ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) + (arI q Xa).bT + (arI q Xa).bP +
          (arI q Xa).A := by
        have h1 : (0 : ℝ) ≤ ((q.k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ ((arI q Xa).bT : ℝ) := Nat.cast_nonneg _
        have h4 : (0 : ℝ) ≤ ((arI q Xa).bP : ℝ) := Nat.cast_nonneg _
        have h5 : (0 : ℝ) ≤ ((arI q Xa).A : ℝ) := Nat.cast_nonneg _
        linarith
      have key1 := GateODEBudget.gate_budget_arith 9000 q.g Q
        (logBudget q.g q.ε) (q.pub.params.d : ℝ) (q.pub.params.J : ℝ) (q.pub.params.k : ℝ)
        (q.pub.params.l : ℝ)
        (((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m + q.pub.params.r + 1 +
          ((q.pub.σ + 3 : ℕ) : ℝ) + ((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ))
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs + ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) +
          (arI q Xa).bT + (arI q Xa).bP + (arI q Xa).A)
        (by norm_num) hg0 hQ1 hℓ1 hd' hJ' (Nat.cast_nonneg _) (Nat.cast_nonneg _) hXs0 hG0 hAw0
      have hAp' : ((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) + (arI q Xa).bT +
          (arI q Xa).bP + (arI q Xa).A + Fintype.card Xa ≤
          4200 * ((words q.pub : ℝ) + 1) ^ 3 + Fintype.card Xa := by linarith
      have key2 := words_gate_arith_i 36873000 (3 * 10 ^ 12) q.g Q (logBudget q.g q.ε)
        (words q.pub : ℝ) ((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ)
        ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k)
        (q.pub.params.l : ℝ) ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
        (Fintype.card Zs : ℝ)
        (((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) + (arI q Xa).bT +
          (arI q Xa).bP + (arI q Xa).A + Fintype.card Xa) (G : ℝ) (Fintype.card Xa : ℝ)
        (by norm_num) (by norm_num) hg0 hQ1 hℓ1 hwr0 hPG' hSm (Nat.cast_nonneg _) hl hAp' hG0 hZ0
        hGr0 hX0
      have key3 := budget_mono_i q.g Q (((words q.pub : ℝ) + logBudget q.g q.ε + 1) ^ 3) B
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) (Fintype.card Zs : ℝ) (G : ℝ)
        (Fintype.card Xa : ℝ) hg0 hQ1 hB0 hcube hG0 hZ0
      have e2 : 4097 * 9000 * q.g * (Q * ((((q.pub.params.a : ℕ) : ℝ) + q.pub.params.m +
            q.pub.params.r + 1 + ((q.pub.σ + 3 : ℕ) : ℝ) +
            ((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ)) +
            q.pub.params.k + 1 + logBudget q.g q.ε * ((q.pub.params.l : ℝ) + 1)) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
            (((q.k + 1 : ℕ) : ℝ) + Fintype.card Zs +
              ((6 * q.k + 6 + 4 * q.b + Fintype.card Xa : ℕ) : ℝ) + (arI q Xa).bT +
              (arI q Xa).bP + (arI q Xa).A)) =
          36873000 * q.g * (Q * (((privGates (ndI q impl) (arI q Xa) : ℕ) : ℝ) +
            ((q.k + 1 : ℝ) + q.pub.σ + q.pub.params.m + q.pub.params.r + q.pub.params.k) +
            logBudget q.g q.ε * ((q.pub.params.l : ℝ) + 1) + 8) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
            ((Fintype.card Zs : ℝ) + (((q.k + 1 : ℕ) : ℝ) + ((6 * q.k + 6 + 4 * q.b : ℕ) : ℝ) +
              (arI q Xa).bT + (arI q Xa).bP + (arI q Xa).A + Fintype.card Xa))) := by
        rw [e1]
        push_cast
        ring
      exact hgc'.trans (key1.trans (le_of_eq e2 |>.trans (key2.trans key3)))
    · -- calls
      intro p
      rw [hp, if_neg hz]
      have hI0 : (0 : ℝ) ≤ (if p Query.rowLocation then 1 else 0) +
          (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) := by
        split_ifs <;> norm_num
      have hcV := ndI_nCalls q hK p
      have hcP : (nCallsN p (nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa)
          (fun c => liftC (srcC c))) : ℝ) ≤ 12 * (q.pub.params.d : ℝ) * (2 * c *
            ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) +
          ((nCallsN p (srcC false) : ℝ) + nCallsN p (srcC true)) := by
        have h1 : nCallsN p (nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa)
            (fun c => liftC (srcC c))) ≤ 12 * q.pub.params.d * nCallsN p (ndI q impl).V +
              nCallsN p (liftC (srcC false)) + nCallsN p (liftC (srcC true)) := hC p
        rw [hCs, hCs] at h1
        have h2 : nCallsN p (nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa)
            (fun c => liftC (srcC c))) ≤ 12 * q.pub.params.d * (2 * c *
              ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) + nCallsN p (srcC false) +
              nCallsN p (srcC true) :=
          h1.trans (Nat.add_le_add_right (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ hcV) _) _)
        have h3 : ((nCallsN p (nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa)
            (fun c => liftC (srcC c))) : ℕ) : ℝ) ≤ ((12 * q.pub.params.d * (2 * c *
              ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) + nCallsN p (srcC false) +
              nCallsN p (srcC true) : ℕ) : ℝ) := by exact_mod_cast h2
        refine h3.trans (le_of_eq ?_)
        push_cast
        split_ifs <;> ring
      have hW : ((nprotocol (nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa)
          (fun c => liftC (srcC c))) q.g hq.g_ge).worstCost (wCallN p) : ℝ) ≤
          40 * q.g * (nCallsN p (nprepC q.pub.params q.pub.UJg (ndI q impl) (arI q Xa)
            (fun c => liftC (srcC c))) : ℝ) := hWC p
      generalize hQd : qOf (q.pub.s : ℝ) q.T q.etaH q.etaD q.g q.ε = Q at hd' ⊢
      generalize hId : ((if p Query.rowLocation then 1 else 0) +
          (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) : ℝ) = I
        at hI0 hcP ⊢
      have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
      have h4 := mul_le_mul_of_nonneg_left hd' (mul_nonneg (mul_nonneg (mul_nonneg
        (by norm_num : (0 : ℝ) ≤ 40 * 24) hc0) hg0) hI0)
      have h5 := mul_le_mul_of_nonneg_left hcP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40) hg0)
      have e6 : 40 * q.g * (12 * (q.pub.params.d : ℝ) * (2 * c * I) +
          ((nCallsN p (srcC false) : ℝ) + nCallsN p (srcC true))) =
          40 * 24 * c * q.g * I * (q.pub.params.d : ℝ) +
          40 * q.g * ((nCallsN p (srcC false) : ℝ) + nCallsN p (srcC true)) := by ring
      have e7 : 40 * 24 * c * q.g * I * (4096 * Q) = 3932160 * c * q.g * Q * I := by ring
      rw [e6] at h5
      rw [e7] at h4
      exact hW.trans (h5.trans (add_le_add h4 le_rfl))

end Budget

end

end SparseHamiltonian.GeneralDecoderODE
