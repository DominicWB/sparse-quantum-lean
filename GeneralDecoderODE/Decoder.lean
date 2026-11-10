import GeneralDecoderODE.ImplDec
import GeneralDecoderODE.Compose
import GeneralDecoderODE.SolverBudget
import GeneralDecoderODE.SolverTimeBudget

/-!
# The gate-level dissipative solvers for sparse access with a binary entry decoding

Theorem `ode:thm:gates` assumes sparse access with a public decoder `val` of the stored words
(Section `hs:sec:control`) and "efficient binary entry decoding". For sparse access
`D : GeneralSparseAccess.QData X N s k b` of general size with a decoder `val` that has an exact
binary entry decoding `dc : BinDecode b b' A` (`val w = c₀ (X + iY)` for the decoded word
`dc.dw w`, `Decode`; the values of `val` lie on the grid `c₀ (ℤ + iℤ)`), the solvers of
`GeneralSparseODE` run on the decoded data `D.decData dc c₀ …` (the same matrix and locators, the
stored words replaced by the decoded words read by `c₀(X + iY)`), calling the supplied oracles of
`D` through

* `implDP N s z₀ dc`: the implementation `GeneralSparseAccess.implP` of the padded oracles of the
  decoded data from the decoded oracles, every decoded call replaced by its implementation
  `implDec dc` from the supplied oracles (`implComp`); on clean ancillas it acts as the padded
  oracles of the decoded data (`implOK_implDP`), with at most `6` supplied calls of the kind of the
  call (`kindOK_implDP`) and at most `implG k b' + 3 (2 |dc| + 2b')` gates per call
  (`nGatesN_implDP_le`);
* `prepD q N dc srcC`, `prepTD q N dc loadC wpC`: the preparations of the constant-coefficient and
  the time-dependent solver through `implDP N s 0 dc`.

The theorems:

* `decoder_ode_outcome`, `decoder_time_outcome`: the guarantees of `general_ode_outcome` and
  `general_time_outcome` for the supplied oracles of `D` (for the time-dependent solver the
  coherent sampled-time supplied oracles `primsTG D x`), against the marker embedding of the
  solution for the matrix of `D` extended by zero;
* `decoder_ode_budget`, `decoder_time_budget`: the bounds of `general_ode_budget` and
  `general_time_budget` with the decoding cost `cost dc = |dc| + 2b + 2b' + A` and its wires
  `wires dc = 2b + 2b' + A`: at most `10²⁰ g [q* ((𝔟₀+1)³ + cost dc) + G_src + |Zs|]`
  (time-dependent: `2·10²⁰ g [q*' ((𝔟'+1)³ + cost dc) + G_src + |Zs|]`) gates, at most
  `3·10¹¹ (𝔟₀+1)³ + 2 |Zs| + 2 wires dc` (time-dependent: `(𝔟'+1)³`) qubits and at most
  `23592960 g q*` (time-dependent: `47185920 g q*'`) supplied calls of each kind of matrix oracle
  besides those of the source circuits, for decoded words of `b' ≤ b_data` bits.
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
open GateBinaryODE (Pub SZ4)
open GateBinaryODETime (PubT)
open ZeroTimeGateODE (BPublicOK0 BZeroCase BTPublicOK0 BTZeroCase bpublicOK_of btpublicOK_of)
open SourceAccuracyODE (WOutcome)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf words wordsT gammaOf)
open ImprovedODEQueryBudget (logBudget)
open GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct

/-! ### The implementation through the decoding circuit -/

section Impl

variable {k b b' A : ℕ}

/-- **The padded oracles of the decoded data from the supplied oracles**: the implementation
`implP` of the padded oracles of the decoded data with every decoded call replaced by its
implementation `implDec dc` through the decoding circuit. -/
def implDP (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) :
    Query → List (NInstr (PY (k + 1) b' ⊕ (GeneralSparseAccess.AW k b' ⊕ DW b b' A))
      (PY k b) Query) :=
  implComp (implP (k := k) (b := b') N s z₀) (implDec (k := k) dc)

/-- **The gates of one padded call through the decoding circuit**: the gates of `implP` and the
decoding gates of its at most three decoded calls. -/
def implDG (k b' : ℕ) (dc : BinDecode b b' A) : ℕ :=
  implG k b' + (2 * dc.circ.length + 2 * b') * 3

theorem valid_implDP (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) :
    ∀ j, ∀ i ∈ implDP (k := k) N s z₀ dc j, i.Valid := by
  intro j i hi
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact NInstr.valid_map assocE i'
    (valid_subst (valid_implDec dc) _ (valid_implP N s z₀ j) i' hi')

/-- **At most `implG k b' + 3 (2 |dc| + 2b')` gates per padded call.** -/
theorem nGatesN_implDP_le (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) (j : Query) :
    nGatesN (implDP (k := k) N s z₀ dc j) ≤ implDG k b' dc :=
  nGatesN_implComp_le _ _ (implG k b') (2 * dc.circ.length + 2 * b') 3
    (nGatesN_implP_le N s z₀) (nGatesN_implDec_le dc) (kindOK_implP N s z₀) j

/-- **At most six supplied calls per padded call, all of its kind.** -/
theorem kindOK_implDP (N s : ℕ) (z₀ : Cfg (VW b')) (dc : BinDecode b b' A) :
    KindOK (implDP (k := k) N s z₀ dc) id 6 :=
  kindOK_comp_id (kindOK_implP N s z₀) (kindOK_implDec dc)

variable {X : Type*} {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The padded oracles of the decoded data from the supplied oracles**: on clean ancillas,
`implDP N s z₀ dc` acts as the padded oracles of the decoded data. -/
theorem implOK_implDP {N s : ℕ} (D : QData X N s k b) (dc : BinDecode b b' A) (c₀ : ℝ)
    (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (z₀ : Cfg (VW b'))
    (hz₀ : (D.decData dc c₀ hc₀ hdc).val z₀ = 0) (x : X) :
    ImplOK (D.prims (R := R) x)
      (GateBinary.prims (R := R) ((D.decData dc c₀ hc₀ hdc).padData z₀ hz₀) (Equiv.refl _) x)
      (implDP N s z₀ dc) :=
  implOK_comp (D.prims x) ((D.decData dc c₀ hc₀ hdc).prims x)
    (GateBinary.prims ((D.decData dc c₀ hc₀ hdc).padData z₀ hz₀) (Equiv.refl _) x)
    (D.prims_isUnitary x) ((D.decData dc c₀ hc₀ hdc).prims_isUnitary x)
    (implDec_ok D dc c₀ hc₀ hdc x) (implOK (D.decData dc c₀ hc₀ hdc) z₀ hz₀ x)

/-- The lift of the matrix extended by zero of the decoded data is that of `D`. -/
theorem padLift_decData {N s : ℕ} (D : QData X N s k b) (dc : BinDecode b b' A) (c₀ : ℝ)
    (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀) (x : X) :
    padLift (D.decData dc c₀ hc₀ hdc) x = padLift D x := rfl

end Impl

/-! ### The arithmetic of the decoding cost -/

section Arith

theorem card_DW (b b' A : ℕ) : Fintype.card (DW b b' A) = 2 * b + 2 * b' + A := by
  simp only [DW, AWr, VW, Fintype.card_sum, Fintype.card_fin]
  ring

/-- **The decoding terms of the gate budget**: with `G ≤ 40 𝔴 + 6 cost` gates per call and
`X ≤ 8 𝔴 + cost` ancillas, `𝔴 ≤ 300 (𝔟+1)`, the slack below the released constant absorbs the
words and leaves the decoding cost. -/
theorem decoder_gate_arith (c₁ c₂ C g Q B Gs Zs X1 X2 W Cst : ℝ)
    (hc₂ : 0 ≤ c₂) (hC : c₁ + 14400 * c₂ ≤ C) (hC' : 7 * c₂ ≤ C)
    (hg : 0 ≤ g) (hQ : 1 ≤ Q) (hB : 0 ≤ B) (hW0 : 0 ≤ W) (hW : W ≤ 300 * (B + 1))
    (hCst : 0 ≤ Cst) (h1 : X1 ≤ 40 * W + 6 * Cst) (h2 : X2 ≤ 8 * W + Cst) (hGs : 0 ≤ Gs)
    (hZs : 0 ≤ Zs) :
    c₁ * g * (Q * (B + 1) ^ 3 + Gs + Zs) + c₂ * g * (Q * X1 + X2) ≤
      C * g * (Q * ((B + 1) ^ 3 + Cst) + Gs + Zs) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hB1 : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have hY0 : 0 ≤ (B + 1) ^ 3 := by positivity
  have hW' : W ≤ 300 * (B + 1) ^ 3 := by linarith
  have hX2 : X2 ≤ Q * (8 * W + Cst) := by
    have : 8 * W + Cst ≤ Q * (8 * W + Cst) := le_mul_of_one_le_left (by positivity) hQ
    linarith
  have hQX1 : Q * X1 ≤ Q * (40 * W + 6 * Cst) := mul_le_mul_of_nonneg_left h1 hQ0
  have hS : Q * X1 + X2 ≤ 14400 * (Q * (B + 1) ^ 3) + 7 * (Q * Cst) := by
    have h3 : Q * (48 * W) ≤ Q * (14400 * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hQ0
    linarith
  have hQY : 0 ≤ Q * (B + 1) ^ 3 := mul_nonneg hQ0 hY0
  have hQC : 0 ≤ Q * Cst := mul_nonneg hQ0 hCst
  have hcg : 0 ≤ c₂ * g := mul_nonneg hc₂ hg
  have h4 : c₂ * g * (Q * X1 + X2) ≤ c₂ * g * (14400 * (Q * (B + 1) ^ 3) + 7 * (Q * Cst)) :=
    mul_le_mul_of_nonneg_left hS hcg
  have h5 : (c₁ + 14400 * c₂) * (g * (Q * (B + 1) ^ 3)) ≤ C * (g * (Q * (B + 1) ^ 3)) :=
    mul_le_mul_of_nonneg_right hC (mul_nonneg hg hQY)
  have h6 : 7 * c₂ * (g * (Q * Cst)) ≤ C * (g * (Q * Cst)) :=
    mul_le_mul_of_nonneg_right hC' (mul_nonneg hg hQC)
  have h7 : c₁ * (g * (Gs + Zs)) ≤ C * (g * (Gs + Zs)) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hg (by positivity))
  linarith

/-- **The decoding terms of the register**: `2 X ≤ 16 𝔴 + 2 wires` and `𝔴 ≤ 300 (𝔟+1)`. -/
theorem decoder_space_arith (B Zs X2 W Wr : ℝ) (hB : 0 ≤ B) (hW : W ≤ 300 * (B + 1))
    (h2 : X2 ≤ 8 * W + Wr) :
    28 * 10 ^ 10 * (B + 1) ^ 3 + 2 * Zs + 2 * X2 ≤ 3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Zs + 2 * Wr := by
  have hB1 : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  linarith

end Arith

/-! ### The constant-coefficient solver -/

section Constant

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The preparation of the constant-coefficient decoder solver**: `prepI` through the
implementation `implDP N s 0 dc` of the padded oracles of the decoded data. -/
def prepD (q : GPub) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k b) Query)) :
    List (NInstr (GPubI.regI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs) (PY q.k b)
      Query) :=
  prepI q (implDP (k := q.k) N q.s (fun _ => false) dc) srcC

set_option maxHeartbeats 1600000 in
/-- **The outcome of the decoder solver** (constant coefficients, every `T ≥ 0`): for public data
with `BPublicOK0 q.pub` and the public rescaling outside the zero case, sparse access `D` of
general size with a decoder `val` that has an exact binary entry decoding `dc` of its stored
words into `q.b`-bit components (`val w = c₀ (X + iY)` of `dc.dw w`, `c₀ = q.c0`), and every input
as in `GeneralSparseODE.general_ode_outcome` for the matrix of `D` and source circuits calling the
supplied oracles, the protocol `nprotocol (prepD q N dc srcC) g` has the guarantees
`WOutcome … (ε / 250)` for the supplied oracles `D.prims x`, against the marker embedding of the
solution of `x' = -A x + b`, `A = padLift D x`. -/
theorem decoder_ode_outcome (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : ¬ BZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε)
    {b A : ℕ} (D : QData X N q.s q.k b) (dc : BinDecode b q.b A) (hdc : dc.Exact D.val q.c0)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (x : X)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ w : EuclideanSpace ℂ (Fin N), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (Jsrc : Bool → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (x0 v : Reg (Fin q.k) ℂ) (ζs : ℝ)
    (hJ : ∀ c, IsUnitary (Jsrc c)) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun (D.prims (R := ℂ) x) (srcC c))
      (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤
      4 * q.pub.params.nu)
    (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.k)) = unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.k)) = unitDirection v)
    (hne : ODEConstantForcing.solution (-padLift D x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-padLift D x) x0 v q.T‖) :
    WOutcome (prepD q N dc srcC) q.g (q.ε / 250) hq.g_ge (D.prims (R := ℂ) x)
      (markEmb q.k (ODEConstantForcing.solution (-padLift D x) x0 v q.T)) := by
  have hc₀ : 0 < q.c0 := hq.c0_pos
  have h := general_ode_outcomeI q hq hγ (D.decData dc q.c0 hc₀ hdc) (fun _ => false)
    (QData.decData_val_zero D dc q.c0 hc₀ hdc) (fun z => rfl) x (D.prims (R := ℂ) x)
    (D.prims_isUnitary x) (implDP (k := q.k) N q.s (fun _ => false) dc)
    (implOK_implDP D dc q.c0 hc₀ hdc (fun _ => false) (QData.decData_val_zero D dc q.c0 hc₀ hdc) x)
    srcC hsrcV hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv
    (by rw [padLift_decData]; exact hne) (by rw [padLift_decData]; exact hB)
  rw [padLift_decData] at h
  exact h

set_option maxHeartbeats 8000000 in
/-- **The budget of the decoder solver in `𝔟`** (constant coefficients, every `T ≥ 0`). For the
hypotheses of `GeneralSparseODE.general_ode_budget` with decoded words of `q.b ≤ b_data` bits and
any decoding `dc` of stored words of `2b` bits, put `𝔟₀ = bitB b_data (2^{k+1}) 0 0 q* g ε`. The
protocol `nprotocol (prepD q N dc srcC) g` has valid trials, at most
`10²⁰ g [q* ((𝔟₀+1)³ + cost dc) + G_src + |Zs|]` elementary gates in every history, at most
`3·10¹¹ (𝔟₀+1)³ + 2 |Zs| + 2 wires dc` qubits, and at most
`(if BZeroCase then 0 else 23592960 g q* ([row] + [col] + [value])) + 40 g (calls_p(srcC 0) +
calls_p(srcC 1))` calls of every kind `p` of the supplied oracles. -/
theorem decoder_ode_budget (bd : ℕ) (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : if BZeroCase q.pub then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepD q N dc srcC) j, i.Valid) ∧
    ((nprotocol (prepD q N dc srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          ((bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
            dc.cost) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (GPubI.regI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 2 * Fintype.card Zs + 2 * dc.wires ∧
    (∀ p : Query → Bool, ((nprotocol (prepD q N dc srcC) q.g hq.g_ge).worstCost (wCallN p) : ℝ) ≤
      (if BZeroCase q.pub then 0 else 23592960 * q.g * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0))) +
        40 * q.g * ((nCallsN p (srcC false) : ℝ) + nCallsN p (srcC true))) := by
  obtain ⟨hV, hG, hS, hC⟩ := general_ode_budgetI bd q hq hγ hζ hb hc0 hT hH hD
    (implDP (k := q.k) N q.s (fun _ => false) dc) (valid_implDP N q.s _ dc) (implDG q.k q.b dc) 6
    (nGatesN_implDP_le N q.s _ dc) (kindOK_implDP N q.s _ dc) srcC hsrcV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.pub.s q.T q.etaH q.etaD q.g q.ε :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hℓ1 : 1 ≤ logBudget q.g q.ε := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge
    hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hB0 : 0 ≤ bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    bitB_nonneg bd _ 0 0 hQg hq.ε_pos hε1
  have hw : (words q.pub : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
    by_cases hz : BZeroCase q.pub
    · rw [if_pos hz] at hγ
      exact GateRemarks.ODE.zero_words_le bd q.pub hq hz hγ hζ hb hc0 hH hD
    · rw [if_neg hz] at hγ
      exact GateBitBudget.words_le bd q.pub (bpublicOK_of hq hz) hγ hζ hb hc0 hT hH hD
  -- the decoding terms in the words
  have hk : q.k + 1 ≤ words q.pub := by
    show q.pub.kx ≤ words q.pub
    unfold words
    omega
  have hbw : q.b ≤ words q.pub := by
    show q.pub.b ≤ words q.pub
    unfold words
    omega
  have hX1 : ((implDG q.k q.b dc : ℕ) : ℝ) ≤ 40 * (words q.pub : ℝ) + 6 * (dc.cost : ℝ) := by
    have : implDG q.k q.b dc ≤ 40 * words q.pub + 6 * dc.cost := by
      unfold implDG implG BinDecode.cost
      omega
    exact_mod_cast this
  have hX2w : (Fintype.card (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) : ℝ) ≤
      8 * (words q.pub : ℝ) + (dc.wires : ℝ) := by
    have : Fintype.card (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) ≤
        8 * words q.pub + dc.wires := by
      rw [Fintype.card_sum, card_AWg, card_DW]
      unfold BinDecode.wires
      omega
    exact_mod_cast this
  have hX2 : (Fintype.card (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) : ℝ) ≤
      8 * (words q.pub : ℝ) + (dc.cost : ℝ) := by
    have : (dc.wires : ℝ) ≤ (dc.cost : ℝ) := by exact_mod_cast dc.wires_le_cost
    linarith
  have hW : (words q.pub : ℝ) ≤
      300 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
    linarith
  refine ⟨hV, ?_, ?_, ?_⟩
  · refine hG.trans ?_
    exact decoder_gate_arith (9 * 10 ^ 19) (3 * 10 ^ 12) (10 ^ 20) q.g _ _ _ _ _ _ _ _
      (by norm_num) (by norm_num) (by norm_num) hg0 hQ1 hB0 (Nat.cast_nonneg _) hW
      (Nat.cast_nonneg _) hX1 hX2 (by positivity) (Nat.cast_nonneg _)
  · exact hS.trans (decoder_space_arith _ _ _ _ _ hB0 hW hX2w)
  · intro p
    refine (hC p).trans (le_of_eq ?_)
    split_ifs <;> push_cast <;> ring

end Constant

/-! ### The time-dependent solver -/

section Time

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The instance conditions for the decoded data**: the conditions `RobustRestG` depend on the
sparse access only through the lifts of its matrix, which the decoded data share. -/
theorem robustRestG_decData {q : GPubT} {b A : ℕ} {D : QData (X × Fin (2 ^ q.m)) N q.s q.k b}
    {x : X} {Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ}
    {Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ}
    {G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ} {bf xs : ℝ → Reg (Fin q.k) ℂ}
    {bs : ℕ → Reg (Fin q.k) ℂ} {βG δG βb δb bmax : ℝ} (dc : BinDecode b q.b A) (c₀ : ℝ)
    (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀)
    (hR : RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax) :
    RobustRestG q (D.decData dc c₀ hc₀ hdc) x Jl Wp G bf xs bs βG δG βb δb bmax :=
  ⟨hR.load_unitary, hR.prep_left, hR.prep_right, hR.prep, hR.init_load, hR.forcing_load,
    hR.solves, hR.accretive, hR.lipG, hR.sampleG, hR.lipb, hR.sampleb, hR.boundb, hR.βG_nonneg,
    hR.βb_nonneg, hR.target_ne, hR.budget, hR.disc, hR.branch⟩

/-- **The preparation of the time-dependent decoder solver**: `prepTI` through the implementation
`implDP N s 0 dc` of the padded oracles of the decoded data. -/
def prepTD (q : GPubT) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query)) :
    List (NInstr (GPubTI.regTI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs)
      (Fin q.m ⊕ PY q.k b) Query) :=
  prepTI q (implDP (k := q.k) N q.s (fun _ => false) dc) loadC wpC

set_option maxHeartbeats 1600000 in
/-- **The outcome of the time-dependent decoder solver** (every `T ≥ 0`, represented samples of
any sign): for public data with `BTPublicOK0 q.pub` and the public rescaling outside the zero case,
time-indexed sparse access `D` of general size with a decoder that has an exact binary entry
decoding `dc` of its stored words into `q.b`-bit components (`c₀ = q.c0`), and every input as in
`GeneralSparseODE.general_time_outcome` for the samples of `D` and loading and weight-preparation
circuits calling the coherent sampled-time supplied oracles, the protocol
`nprotocol (prepTD q N dc loadC wpC) (2g)` has the guarantees `WOutcome … (ε / 100)` for the
coherent sampled-time supplied oracles `primsTG D x`, against the marker embedding of `x(T)`. -/
theorem decoder_time_outcome (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    {b A : ℕ} (D : QData (X × Fin (2 ^ q.m)) N q.s q.k b) (dc : BinDecode b q.b A)
    (hdc : dc.Exact D.val q.c0)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (bf xs : ℝ → Reg (Fin q.k) ℂ)
    (bs : ℕ → Reg (Fin q.k) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 13 * q.pub.params.nu)
    (hR : RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax) :
    WOutcome (prepTD q N dc loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (primsTG D x) (markEmb q.k (xs q.T)) := by
  have hc₀ : 0 < q.c0 := hq.c0_pos
  exact general_time_outcomeI q hq hγ (D.decData dc q.c0 hc₀ hdc) (fun _ => false)
    (QData.decData_val_zero D dc q.c0 hc₀ hdc) (fun z => rfl) x
    (fun w => D.prims (R := ℂ) (x, wordEquivFin q.m w))
    (fun w j => D.prims_isUnitary (x, wordEquivFin q.m w) j)
    (implDP (k := q.k) N q.s (fun _ => false) dc)
    (fun w => implOK_implDP D dc q.c0 hc₀ hdc (fun _ => false)
      (QData.decData_val_zero D dc q.c0 hc₀ hdc) (x, wordEquivFin q.m w))
    loadC hloadV wpC hwpV hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud
    (robustRestG_decData dc q.c0 hc₀ hdc hR)

set_option maxHeartbeats 8000000 in
/-- **The budget of the time-dependent decoder solver in `𝔟`** (every `T ≥ 0`). For the hypotheses
of `GeneralSparseODE.general_time_budget` with decoded words of `q.b ≤ b_data` bits and any decoding
`dc` of stored words of `2b` bits, put `𝔟' = bitB b_data (2^{k+1}) (2^m) (2^m) q*' g ε`. The
protocol `nprotocol (prepTD q N dc loadC wpC) (2g)` has valid trials, at most
`2·10²⁰ g [q*' ((𝔟'+1)³ + cost dc) + G_src + |Zs|]` elementary gates in every history
(`G_src = |loadC| + 2 |wpC|`), at most `3·10¹¹ (𝔟'+1)³ + 2 |Zs| + 2 wires dc` qubits, and at most
`(if BTZeroCase then 0 else 47185920 g q*' ([row] + [col] + [value])) +
80 g (calls_p(loadC) + 2 calls_p(wpC))` calls of every kind `p` of the supplied oracles. -/
theorem decoder_time_budget (bd : ℕ) (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : if BTZeroCase q.pub then HasBits bd q.γ
      else q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepTD q N dc loadC wpC) j, i.Valid) ∧
    ((nprotocol (prepTD q N dc loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
            (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 + dc.cost) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (GPubTI.regTI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
          (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + 2 * dc.wires ∧
    (∀ p : Query → Bool, ((nprotocol (prepTD q N dc loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN p) : ℝ) ≤
      (if BTZeroCase q.pub then 0 else
        47185920 * q.g * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0))) +
        80 * q.g * ((nCallsN p loadC : ℝ) + 2 * nCallsN p wpC)) := by
  obtain ⟨hV, hG, hS, hC⟩ := general_time_budgetI bd q hq hγ hζ hb hc0 hT hH hD
    (implDP (k := q.k) N q.s (fun _ => false) dc) (valid_implDP N q.s _ dc) (implDG q.k q.b dc) 6
    (nGatesN_implDP_le N q.s _ dc) (kindOK_implDP N q.s _ dc) loadC hloadV wpC hwpV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hg1 : (1 : ℝ) ≤ q.g := hq.g_ge
  have hε0 : (0 : ℝ) < q.ε := hq.ε_pos
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
  have hw : (wordsT q.pub : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
        (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by
    by_cases hz : BTZeroCase q.pub
    · rw [if_pos hz] at hγ
      exact GateRemarks.ODE.zero_wordsT_le bd q.pub hq hz hγ hζ hb hc0 hH hD
    · rw [if_neg hz] at hγ
      exact GateBitBudget.wordsT_le bd q.pub (btpublicOK_of hq hz) hγ hζ hb hc0 hT hH hD
  -- the decoding terms in the words
  have hk : q.k + 1 ≤ wordsT q.pub := by
    show q.pub.kx ≤ wordsT q.pub
    unfold wordsT
    omega
  have hbw : q.b ≤ wordsT q.pub := by
    show q.pub.b ≤ wordsT q.pub
    unfold wordsT
    omega
  have hX1 : ((implDG q.k q.b dc : ℕ) : ℝ) ≤ 40 * (wordsT q.pub : ℝ) + 6 * (dc.cost : ℝ) := by
    have : implDG q.k q.b dc ≤ 40 * wordsT q.pub + 6 * dc.cost := by
      unfold implDG implG BinDecode.cost
      omega
    exact_mod_cast this
  have hX2w : (Fintype.card (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) : ℝ) ≤
      8 * (wordsT q.pub : ℝ) + (dc.wires : ℝ) := by
    have : Fintype.card (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) ≤
        8 * wordsT q.pub + dc.wires := by
      rw [Fintype.card_sum, card_AWg, card_DW]
      unfold BinDecode.wires
      omega
    exact_mod_cast this
  have hX2 : (Fintype.card (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) : ℝ) ≤
      8 * (wordsT q.pub : ℝ) + (dc.cost : ℝ) := by
    have : (dc.wires : ℝ) ≤ (dc.cost : ℝ) := by exact_mod_cast dc.wires_le_cost
    linarith
  have hW : (wordsT q.pub : ℝ) ≤
      300 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
        (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) := by
    linarith
  refine ⟨hV, ?_, ?_, ?_⟩
  · refine hG.trans ?_
    exact decoder_gate_arith (18 * 10 ^ 19) (6 * 10 ^ 12) (2 * 10 ^ 20) q.g _ _ _ _ _ _ _ _
      (by norm_num) (by norm_num) (by norm_num) hg0 hQ1 hB0 (Nat.cast_nonneg _) hW
      (Nat.cast_nonneg _) hX1 hX2 (by positivity) (Nat.cast_nonneg _)
  · exact hS.trans (decoder_space_arith _ _ _ _ _ hB0 hW hX2w)
  · intro p
    refine (hC p).trans (le_of_eq ?_)
    split_ifs <;> push_cast <;> ring

end Time

end

end SparseHamiltonian.GeneralDecoderODE
