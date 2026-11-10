import ManuscriptConformance.WriterDecoderAccess
import ManuscriptConformance.WriterODETimeGates
import ManuscriptConformance.GateODEDecoder

/-!
# Conformance: Theorem `ode:thm:gates` with binary entry decoding and a writer

Theorem `ode:thm:gates` for sparse access of general size with an exact binary entry decoding
(`ode_thm_gates_decoder`, `ode_thm_gates_time_decoder`, `GateODEDecoder`), with the value oracle
given by a reversible writer of the stored words specified on the clean inputs of the valid index
pairs only (`GeneralSparseAccess.QData.Writer`, handover item B4).

The released decoder solvers call the padded oracles of the decoded data through the composite
`GeneralDecoderODE.implDP` (`implP` of the decoded data, every decoded call through the decoding
circuit `implDec`). Their writer forms call them through `implDPW` (the inverse writer in the place
of the second supplied value call of every decoded value call), which acts on clean ancillas as the
padded oracles of the decoded data for every writer (`implOK_implDPW`, `WriterDecoderAccess`) with
the gates and the kinds of calls of `implDP`:

* `GeneralDecoderODE.prepDW`, `prepTDW`: the preparations through `implDPW N s 0 dc`;
* `decoder_ode_outcome_writer`, `decoder_ode_budget_writer`, `decoder_time_outcome_writer`,
  `decoder_time_budget_writer`: the outcomes and the budgets of `decoder_ode_outcome`,
  `decoder_ode_budget`, `decoder_time_outcome`, `decoder_time_budget` (the released proofs, with
  `implOK_implDPW` in place of `implOK_implDP`) for the primitives `Wr.prims x` and the coherent
  sampled-time primitives `primsTGW Wr x` of the writer model;
* `ode_thm_gates_decoder_writer`, `ode_thm_gates_time_decoder_writer`: the endpoints, with the
  hypotheses, constants, resource bounds and guarantees of `ode_thm_gates_decoder` and
  `ode_thm_gates_time_decoder`. The protocols are fixed before the writer and the instance.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

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

/-! ### The constant-coefficient solver from a writer -/

section Constant

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The preparation of the constant-coefficient decoder solver from a writer**: `prepI` through
the implementation `implDPW N s 0 dc` of the padded oracles of the decoded data. -/
def prepDW (q : GPub) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k b) Query)) :
    List (NInstr (GPubI.regI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs) (PY q.k b)
      Query) :=
  prepI q (implDPW (k := q.k) N q.s (fun _ => false) dc) srcC

set_option maxHeartbeats 1600000 in
/-- **The outcome of the decoder solver from a writer** (constant coefficients, every `T ≥ 0`): the
guarantees of `decoder_ode_outcome` for the protocol `nprotocol (prepDW q N dc srcC) g` and the
primitives `Wr.prims x` of a writer `Wr` of the stored words of `D` (the source circuits calling
them), for every unitary action of the writer outside its valid clean inputs. -/
theorem decoder_ode_outcome_writer (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : ¬ BZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε)
    {b A : ℕ} (D : QData X N q.s q.k b) (Wr : D.Writer) (dc : BinDecode b q.b A)
    (hdc : dc.Exact D.val q.c0)
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
    (hsrc : ∀ c, ApproxOn CleanX (nrun (Wr.prims (R := ℂ) x) (srcC c))
      (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤
      4 * q.pub.params.nu)
    (hx0 : ‖x0‖ = q.r₀) (hv : ‖v‖ = q.rb)
    (hpx : x0 ≠ 0 → Jsrc false (seedV (S := Fin q.k)) = unitDirection x0)
    (hpv : v ≠ 0 → Jsrc true (seedV (S := Fin q.k)) = unitDirection v)
    (hne : ODEConstantForcing.solution (-padLift D x) x0 v q.T ≠ 0)
    (hB : q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-padLift D x) x0 v q.T‖) :
    WOutcome (prepDW q N dc srcC) q.g (q.ε / 250) hq.g_ge (Wr.prims (R := ℂ) x)
      (markEmb q.k (ODEConstantForcing.solution (-padLift D x) x0 v q.T)) := by
  have hc₀ : 0 < q.c0 := hq.c0_pos
  have h := general_ode_outcomeI q hq hγ (D.decData dc q.c0 hc₀ hdc) (fun _ => false)
    (QData.decData_val_zero D dc q.c0 hc₀ hdc) (fun z => rfl) x (Wr.prims (R := ℂ) x)
    (Wr.prims_isUnitary x) (implDPW (k := q.k) N q.s (fun _ => false) dc)
    (implOK_implDPW dc Wr q.c0 hc₀ hdc (fun _ => false)
      (QData.decData_val_zero D dc q.c0 hc₀ hdc) x)
    srcC hsrcV hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv
    (by rw [padLift_decData]; exact hne) (by rw [padLift_decData]; exact hB)
  rw [padLift_decData] at h
  exact h

set_option maxHeartbeats 8000000 in
/-- **The budget of the decoder solver from a writer** (constant coefficients, every `T ≥ 0`): the
bounds of `decoder_ode_budget` for `prepDW`, whose implementation `implDPW` has the gates and the
kinds of calls of `implDP` (`nGatesN_implDPW_le`, `kindOK_implDPW`). -/
theorem decoder_ode_budget_writer (bd : ℕ) (q : GPub) (hq : BPublicOK0 q.pub)
    (hγ : if BZeroCase q.pub then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.k) ⊕ Zs) (PY q.k b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepDW q N dc srcC) j, i.Valid) ∧
    ((nprotocol (prepDW q N dc srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          ((bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
            dc.cost) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (GPubI.regI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) 0 0 (qOf q.pub.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 2 * Fintype.card Zs + 2 * dc.wires ∧
    (∀ p : Query → Bool, ((nprotocol (prepDW q N dc srcC) q.g hq.g_ge).worstCost (wCallN p) : ℝ) ≤
      (if BZeroCase q.pub then 0 else 23592960 * q.g * qOf q.pub.s q.T q.etaH q.etaD q.g q.ε *
          ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0))) +
        40 * q.g * ((nCallsN p (srcC false) : ℝ) + nCallsN p (srcC true))) := by
  obtain ⟨hV, hG, hS, hC⟩ := general_ode_budgetI bd q hq hγ hζ hb hc0 hT hH hD
    (implDPW (k := q.k) N q.s (fun _ => false) dc) (valid_implDPW N q.s _ dc) (implDG q.k q.b dc) 6
    (nGatesN_implDPW_le N q.s _ dc) (kindOK_implDPW N q.s _ dc) srcC hsrcV
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

/-! ### The time-dependent solver from a writer -/

section Time

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The preparation of the time-dependent decoder solver from a writer**: `prepTI` through the
implementation `implDPW N s 0 dc` of the padded oracles of the decoded data. -/
def prepTDW (q : GPubT) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query)) :
    List (NInstr (GPubTI.regTI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs)
      (Fin q.m ⊕ PY q.k b) Query) :=
  prepTI q (implDPW (k := q.k) N q.s (fun _ => false) dc) loadC wpC

set_option maxHeartbeats 1600000 in
/-- **The outcome of the time-dependent decoder solver from a writer** (every `T ≥ 0`): the
guarantees of `decoder_time_outcome` for the protocol `nprotocol (prepTDW q N dc loadC wpC) (2g)`
and the coherent sampled-time primitives `primsTGW Wr x` of a writer `Wr` of the stored words of
every sample (the loading and weight-preparation circuits calling them). -/
theorem decoder_time_outcome_writer (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    {b A : ℕ} (D : QData (X × Fin (2 ^ q.m)) N q.s q.k b) (Wr : D.Writer) (dc : BinDecode b q.b A)
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
    (hload : ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 13 * q.pub.params.nu)
    (hR : RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax) :
    WOutcome (prepTDW q N dc loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (primsTGW Wr x) (markEmb q.k (xs q.T)) := by
  have hc₀ : 0 < q.c0 := hq.c0_pos
  exact general_time_outcomeI q hq hγ (D.decData dc q.c0 hc₀ hdc) (fun _ => false)
    (QData.decData_val_zero D dc q.c0 hc₀ hdc) (fun z => rfl) x
    (fun w => Wr.prims (R := ℂ) (x, wordEquivFin q.m w))
    (fun w j => Wr.prims_isUnitary (x, wordEquivFin q.m w) j)
    (implDPW (k := q.k) N q.s (fun _ => false) dc)
    (fun w => implOK_implDPW dc Wr q.c0 hc₀ hdc (fun _ => false)
      (QData.decData_val_zero D dc q.c0 hc₀ hdc) (x, wordEquivFin q.m w))
    loadC hloadV wpC hwpV hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud
    (robustRestG_decData dc q.c0 hc₀ hdc hR)

set_option maxHeartbeats 8000000 in
/-- **The budget of the time-dependent decoder solver from a writer** (every `T ≥ 0`): the bounds
of `decoder_time_budget` for `prepTDW`. -/
theorem decoder_time_budget_writer (bd : ℕ) (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : if BTZeroCase q.pub then HasBits bd q.γ
      else q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.pub.params.nu ≤ 196608 * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) (N : ℕ) {b A : ℕ} (dc : BinDecode b q.b A)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (prepTDW q N dc loadC wpC) j, i.Valid) ∧
    ((nprotocol (prepTDW q N dc loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
            (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 + dc.cost) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (GPubTI.regTI q (GeneralSparseAccess.AW q.k q.b ⊕ DW b q.b A) Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ (q.k + 1)) (2 ^ q.m) (2 ^ q.m)
          (qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + 2 * dc.wires ∧
    (∀ p : Query → Bool, ((nprotocol (prepTDW q N dc loadC wpC) q.pub.params.ratio
        (q.pub.params.ratio_ge hq.g_ge)).worstCost (wCallN p) : ℝ) ≤
      (if BTZeroCase q.pub then 0 else
        47185920 * q.g * qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if p Query.rowLocation then 1 else 0) + (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0))) +
        80 * q.g * ((nCallsN p loadC : ℝ) + 2 * nCallsN p wpC)) := by
  obtain ⟨hV, hG, hS, hC⟩ := general_time_budgetI bd q hq hγ hζ hb hc0 hT hH hD
    (implDPW (k := q.k) N q.s (fun _ => false) dc) (valid_implDPW N q.s _ dc) (implDG q.k q.b dc) 6
    (nGatesN_implDPW_le N q.s _ dc) (kindOK_implDPW N q.s _ dc) loadC hloadV wpC hwpV
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

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPub GPubT markEmb padLift primsTG primsTGW)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepDW prepTDW)
open SparseHamiltonian.ZeroTimeGateODE (BPublicOK0 BZeroCase BTPublicOK0 BTZeroCase)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` with binary entry decoding and a writer, constant coefficients**
(handover item B4). The statement of `ode_thm_gates_decoder`, with the constant `C = 10²³`, for
the protocol `nprotocol (prepDW (odePubG …) N dc srcC) ḡ` (fixed before the writer and the
instance) and the primitives `Wr.prims x` of every writer `Wr` of the stored words specified on
the clean inputs of the valid pairs only (`GeneralSparseAccess.QData.Writer`): the supplied
locators and the writer, an inverse call its adjoint. The source circuits call these primitives;
writer and inverse-writer calls are counted as value calls. -/
theorem ode_thm_gates_decoder_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (D : GeneralSparseAccess.QData X N s k b)
        (dc : BinDecode b b' A) (bd : ℕ) (c0 etaH etaD T gbar ε r₀ rb : ℝ),
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hnd : formal_nondegenerate gbar (r₀ + T * rb))
        {Zs : Type} [Fintype Zs] [DecidableEq Zs]
        (srcC : Bool → List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) (PY k b) Query)),
        (∀ c, ∀ i ∈ srcC c, i.Valid) →
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 → 0 ≤ r₀ → 0 ≤ rb →
        (∀ j, ∀ i ∈ trialN (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc
          srcC) j, i.Valid) ∧
        ((nprotocol (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC)
            gbar hnd.1).worstCost wGateN : ℝ) ≤
          C * gbar * (odeShape s T etaH etaD gbar ε *
              ((bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 + dc.cost) +
            ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
        (odeQubitsD (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) dc Zs : ℝ) ≤
          C * (bitB bd N 0 0 (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
            C * Fintype.card Zs + C * dc.wires ∧
        (∀ c : Query → Bool,
          ((nprotocol (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC)
            gbar hnd.1).worstCost (wCallN c) : ℝ) ≤
          (if T = 0 ∨ etaH + etaD = 0 then 0 else
            C * gbar * odeShape s T etaH etaD gbar ε *
              ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
                (if c Query.value then 1 else 0))) +
          C * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
        ∀ (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
          (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
          (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
          (∀ w : EuclideanSpace ℂ (Fin N), 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
          ∀ (Jsrc : Bool → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (x0 v : Reg (Fin k) ℂ) (ζs : ℝ),
          (∀ c, OracleCircuit.IsUnitary (Jsrc c)) → 0 ≤ ζs →
          (∀ c, ApproxOn CleanX (nrun (Wr.prims (R := ℂ) x) (srcC c))
            (liftB (srcIdeal c (Jsrc c))) ζs) →
          ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
          ‖x0‖ = r₀ → ‖v‖ = rb →
          (x0 ≠ 0 → Jsrc false (seedV (S := Fin k)) = ODEStateNormalization.unitDirection x0) →
          (v ≠ 0 → Jsrc true (seedV (S := Fin k)) = ODEStateNormalization.unitDirection v) →
          ODEConstantForcing.solution (-padLift D x) x0 v T ≠ 0 →
          r₀ + T * rb ≤ gbar * ‖ODEConstantForcing.solution (-padLift D x) x0 v T‖ →
          HeraldedOutput (nprotocol (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb)
              N dc srcC) gbar hnd.1) (Wr.prims (R := ℂ) x)
            (ODEStateNormalization.unitDirection
              (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                (ODEConstantForcing.solution (-padLift D x) x0 v T))) ε ∧
          ∀ j : ℕ, ((goodN (S := Fin (k + 1)))†) (nrun (Wr.prims (R := ℂ) x)
              (trialN (prepDW (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) N dc srcC) j)
              sN) ≠ 0 →
            ∃ ω : ℂ, ‖ω‖ = 1 ∧
              ‖ω • ODEStateNormalization.unitDirection (((goodN (S := Fin (k + 1)))†)
                  (nrun (Wr.prims (R := ℂ) x) (trialN (prepDW (odePubG k s D.s_le_pow b' c0 etaH
                    etaD T gbar ε r₀ rb) N dc srcC) j) sN)) -
                ODEStateNormalization.unitDirection
                  (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
                    (ODEConstantForcing.solution (-padLift D x) x0 v T))‖ ≤ ε := by
  refine ⟨10 ^ 23, by norm_num, ?_⟩
  intro X N s k b b' A D dc bd c0 etaH etaD T gbar ε r₀ rb hk hF hbits hnd Zs _ _ srcC hsrcV hH hD
    hT hε hε2 hr0 hrb
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg := hnd.1
  have hB := hnd.2
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb with hqdef
  have hqp : q.pub = odePub (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b' c0
      etaH etaD T gbar ε r₀ rb := rfl
  have hq : BPublicOK0 q.pub := by
    rw [hqp]
    exact odePub_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hr0 hrb hB
  have hγ := odePub_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePub_zeta hqp hH hD hT hg hε hε1
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralDecoderODE.decoder_ode_budget_writer bd q hq hγ hζ hbd
    hc0b hTb hHb hDb N dc srcC hsrcV
  have hWg : ((nprotocol (prepDW q N dc srcC) gbar hnd.1).worstCost wGateN : ℝ) ≤
      10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
        ((bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar
          ε + 1) ^ 3 + dc.cost) + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
          Fintype.card Zs) := hWg0
  have hWq : (odeQubitsD q dc Zs : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) 0 0
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs + 2 * dc.wires := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (prepDW q N dc srcC) gbar
      hnd.1).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        23592960 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hB0 : 0 ≤ bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε := bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_pad_le (bd := bd) hk (by linarith) hQQ (by linarith) hg0 hε
  have hcube := cube_pad_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by
    positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) 0 0 (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε)
      gbar ε + 1) ^ 3 := by positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ dc.cost := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) 0 0 Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N 0 0 Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    generalize (dc.cost : ℝ) = Cst at hC0 ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
    have h1 : Q' * (Y' + Cst) ≤ 128 * (Q * (Y + Cst)) := by
      have h2 : Q' * (Y' + Cst) ≤ (2 * Q) * (Y' + Cst) :=
        mul_le_mul_of_nonneg_right hQQ (by linarith)
      have h3 : (2 * Q) * (Y' + Cst) ≤ (2 * Q) * (64 * Y + 64 * Cst) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * (Y + Cst) := mul_nonneg (by linarith) (by linarith)
    have h4 : (10 : ℝ) ^ 20 * gbar * (Q' * (Y' + Cst) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ≤
        10 ^ 20 * gbar * (128 * (Q * (Y + Cst)) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (10 : ℝ) ^ 20 * gbar * (128 * (Q * (Y + Cst)) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * gbar * (Q * (Y + Cst) +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
      have h6 : (10 : ℝ) ^ 20 * (128 * (Q * (Y + Cst)) + ((nGatesN (srcC false) : ℝ) +
          nGatesN (srcC true)) + Fintype.card Zs) ≤ 10 ^ 23 * (Q * (Y + Cst) +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    linarith
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 23 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h2' : (2 : ℝ) * dc.wires ≤ 10 ^ 23 * dc.wires :=
      mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    have h3 : (3 * 10 ^ 11 : ℝ) * (64 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3) ≤ 10 ^ 23 * (bitB bd N 0 0 (GateODEBudget.qOf s T etaH etaD gbar ε)
        gbar ε + 1) ^ 3 := by nlinarith
    linarith
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true) := by positivity
    have hS : 40 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) ≤
        10 ^ 23 * gbar * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      linarith
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε = Q' at hQQ hW
      have h1 : 23592960 * gbar * Q' * I ≤ 10 ^ 23 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (2 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 23592960 * (Q' * I) ≤ 10 ^ 23 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      linarith
  · -- the guarantees
    intro Wr x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc hacc hx0 hv hpx hpv hne hBud
    have hγ' : ¬ BZeroCase q.pub → q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD q.g q.ε := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralDecoderODE.decoder_ode_outcome_writer
      (odePubG k s D.s_le_pow b' c0 etaH etaD T gbar ε r₀ rb) hq hγ' D Wr dc hF.exact srcC hsrcV x
      hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs0 hsrc (hζs ζs hacc) hx0 hv hpx hpv hne
      hBud).mono (β' := ε) (by
        show ε / 250 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` with binary entry decoding and a writer, time-dependent
coefficients** (handover item B4; special case under the package's uniform-mesh conditions). The
statement of `ode_thm_gates_time_decoder`, with the constant `C = 10²⁴`, for the protocol
`nprotocol (prepTDW (odePubTG …) N dc loadC wpC) (2ḡ)` (fixed before the writer and the instance)
and the coherent sampled-time primitives `primsTGW Wr x` of every writer `Wr` of the stored words
of every sample specified on the clean inputs of the valid pairs only. The loading and
weight-preparation circuits call these primitives. -/
theorem ode_thm_gates_time_decoder_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T gbar ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc
            loadC wpC) j, i.Valid) ∧
          ((nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC wpC)
              (2 * gbar) (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) dc Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs + C * dc.wires ∧
          (∀ c : Query → Bool,
            ((nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
              wpC) (2 * gbar) (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) (bf xs : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (βG δG βb δb bmax ζs : ℝ),
            0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            formal_uniformMeshG (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) D x Jl Wp G
              bf xs bs βG δG βb δb bmax →
            HeraldedOutput (nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m)
                N dc loadC wpC) (2 * gbar) (one_le_two_mul hg))
              (primsTGW Wr x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
                (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) N dc loadC
                  wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTGW Wr x) (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD
                      T gbar ε m) N dc loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (xs T))‖ ≤ ε := by
  refine ⟨10 ^ 24, by norm_num, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨hbd, hc0b, hTb, hHb, hDb⟩ := hbits
  have hg1 : 1 ≤ gbar := hg
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  set q := odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m with hqdef
  have hqp : q.pub = odePubT (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b' c0
      etaH etaD T gbar ε m := rfl
  have hq : BTPublicOK0 q.pub := by
    rw [hqp]
    exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg hε hε2 hm
  have hγ := odePubT_gamma hqp hF.hb hbd
  obtain ⟨hζ, hζs⟩ := odePubT_zeta hqp hH hD hT hg hε hε2
  obtain ⟨hV, hWg0, hWq0, hWc0⟩ := GeneralDecoderODE.decoder_time_budget_writer bd q hq hγ hζ hbd
    hc0b hTb hHb hDb N dc loadC hloadV wpC hwpV
  have hWg : ((nprotocol (prepTDW q N dc loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * gbar * (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
        ((bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
          (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
            dc.cost) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := hWg0
  have hWq : (odeQubitsTD q dc Zs : ℝ) ≤ 3 * 10 ^ 11 * (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 +
      2 * Fintype.card Zs + 2 * dc.wires := hWq0
  have hWc : ∀ c : Query → Bool, ((nprotocol (prepTDW q N dc loadC wpC) (2 * gbar)
      (one_le_two_mul hg)).worstCost (wCallN c) : ℝ) ≤ (if T = 0 ∨ etaH + etaD = 0 then 0 else
        47185920 * gbar * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := hWc0
  -- the query shapes and the word budgets
  have hsP : (((sP s : ℕ) : ℝ)) ≤ 2 * (s : ℝ) := by
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hQQ1 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε ≤
      2 * GateODEBudget.qOf s T etaH etaD gbar ε :=
    qOf_le_of_le (Nat.cast_nonneg _) hsP hT hH hD hg hε hε1
  have hQQ2 : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      3 * GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD gbar ε :=
    qOf_two_le0 (Nat.cast_nonneg _) hT hH hD hg hε hε1
  have hQQ : GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) ≤
      6 * GateODEBudget.qOf s T etaH etaD gbar ε := by linarith
  have hQ1 : 1 ≤ GateODEBudget.qOf s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf hT hH hD hg hε hε1
  have hQ1' : 1 ≤ GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) :=
    GateRemarks.ODE.one_le_qOf hT hH hD (by linarith) (by linarith) (by linarith)
  have hB0 : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hB0' : 0 ≤ bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hBB := bitB_padT_le (bd := bd) (M := 2 ^ m) hk (by linarith) hQQ (by linarith) hg0 hε hε1
  have hcube := cube_padT_le hB0 hB0' hBB
  have hY : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 :=
    by positivity
  have hY' : 0 ≤ (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m)
      (GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2)) gbar ε + 1) ^ 3 := by
    positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ dc.cost := Nat.cast_nonneg _
  rw [odeShape_eq]
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    refine hWg.trans ?_
    generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q'
      at hQQ hQ1' hcube hY' ⊢
    generalize GateODEBudget.qOf s T etaH etaD gbar ε = Q at hQQ hQ1 hcube hB0 hY ⊢
    generalize (bitB bd (2 ^ (k + 1)) (2 ^ m) (2 ^ m) Q' gbar ε + 1) ^ 3 = Y' at hcube hY' ⊢
    generalize (bitB bd N (2 ^ m) (2 ^ m) Q gbar ε + 1) ^ 3 = Y at hcube hY ⊢
    generalize (dc.cost : ℝ) = Cst at hC0 ⊢
    have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
    have h1 : Q' * (Y' + Cst) ≤ 1296 * (Q * (Y + Cst)) := by
      have h2 : Q' * (Y' + Cst) ≤ (6 * Q) * (Y' + Cst) :=
        mul_le_mul_of_nonneg_right hQQ (by linarith)
      have h3 : (6 * Q) * (Y' + Cst) ≤ (6 * Q) * (216 * Y + 216 * Cst) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      nlinarith
    have hQY : 0 ≤ Q * (Y + Cst) := mul_nonneg (by linarith) (by linarith)
    have h4 : (2 * 10 ^ 20 : ℝ) * gbar * (Q' * (Y' + Cst) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ≤
        2 * 10 ^ 20 * gbar * (1296 * (Q * (Y + Cst)) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : (2 * 10 ^ 20 : ℝ) * gbar * (1296 * (Q * (Y + Cst)) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * gbar * (Q * (Y + Cst) +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
      have h6 : (2 * 10 ^ 20 : ℝ) * (1296 * (Q * (Y + Cst)) + ((nGatesN loadC : ℝ) +
          2 * nGatesN wpC) + Fintype.card Zs) ≤ 10 ^ 24 * (Q * (Y + Cst) +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) := by
        nlinarith
      have := mul_le_mul_of_nonneg_left h6 hg0
      linarith
    exact h4.trans h5
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 11)
    have h2 : (2 : ℝ) * Fintype.card Zs ≤ 10 ^ 24 * Fintype.card Zs :=
      mul_le_mul_of_nonneg_right (by norm_num) hZ0
    have h2' : (2 : ℝ) * dc.wires ≤ 10 ^ 24 * dc.wires :=
      mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg _)
    have h3 : (3 * 10 ^ 11 : ℝ) * (216 * (bitB bd N (2 ^ m) (2 ^ m)
        (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3) ≤ 10 ^ 24 * (bitB bd N (2 ^ m)
          (2 ^ m) (GateODEBudget.qOf s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by nlinarith
    linarith
  · -- calls
    intro c
    have hW := hWc c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hS0 : (0 : ℝ) ≤ (nCallsN c loadC : ℝ) + 2 * nCallsN c wpC := by positivity
    have hS : 80 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) ≤
        10 ^ 24 * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg0) hS0
    by_cases hz : T = 0 ∨ etaH + etaD = 0
    · rw [if_pos hz] at hW
      rw [if_pos hz]
      exact hW.trans (add_le_add le_rfl hS)
    · rw [if_neg hz] at hW
      rw [if_neg hz]
      generalize hId : ((if c Query.rowLocation then 1 else 0) +
          (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) : ℝ) = I
        at hI0 hW ⊢
      generalize GateODEBudget.qOf ((sP s : ℕ) : ℝ) T etaH etaD (2 * gbar) (ε / 2) = Q' at hQQ hW
      have h1 : 47185920 * gbar * Q' * I ≤ 10 ^ 24 * gbar * GateODEBudget.qOf s T etaH etaD gbar ε *
          I := by
        have h2 : Q' * I ≤ (6 * GateODEBudget.qOf s T etaH etaD gbar ε) * I :=
          mul_le_mul_of_nonneg_right hQQ hI0
        have h3 : 0 ≤ GateODEBudget.qOf s T etaH etaD gbar ε * I :=
          mul_nonneg (by linarith) hI0
        have h4 : 47185920 * (Q' * I) ≤ 10 ^ 24 * (GateODEBudget.qOf s T etaH etaD gbar ε * I) := by
          nlinarith
        have h5 := mul_le_mul_of_nonneg_left h4 hg0
        nlinarith
      exact hW.trans (add_le_add h1 hS)
  · -- the guarantees
    intro Wr x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp hacc hR
    have hγ' : ¬ BTZeroCase q.pub →
        q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (GeneralDecoderODE.decoder_time_outcome_writer
      (odePubTG k s D.s_le_pow b' c0 etaH etaD T gbar ε m) hq hγ' D Wr dc hF.exact loadC hloadV wpC
      hwpV x hrH hcH hrD hcD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs0 hload hwp
      (hζs ζs hacc) hR).mono (β' := ε) (by
        show ε / 100 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

end

end ManuscriptConformance
