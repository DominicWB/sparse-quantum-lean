import ManuscriptConformance.WriterDecoderODE
import ManuscriptConformance.GateODETimeCertValid

/-!
# Conformance: the certificate forms of `ode:thm:gates` with binary entry decoding and a writer

The certificate forms of Theorem `ode:thm:gates` for time-indexed sparse access of general size
with an exact binary entry decoding (`ode_thm_gates_time_decoder_cert`,
`ode_thm_gates_time_decoder_cert_valid`) with the value oracle given by a reversible writer of the
stored words of every sample specified on the clean inputs of the valid index pairs only
(`GeneralSparseAccess.QData.Writer`, handover item B4).

* `MeshCertificateODE.decoder_time_cert_outcome_writer`: the released outcome through any
  implementation (`general_time_cert_outcomeI`) at the implementation
  `GeneralDecoderODE.implDPW` of the padded oracles of the decoded data from the writer, with
  `implOK_implDPW`, for the coherent sampled-time primitives `primsTGW Wr x`; its protocol is
  `GeneralDecoderODE.prepTDW`.
* `ode_thm_gates_time_decoder_cert_writer`, `ode_thm_gates_time_decoder_cert_valid_writer`: the
  endpoints, with the hypotheses, constants, resource bounds and guarantees of the released forms
  (the resource bounds from `ode_thm_gates_time_decoder_writer`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb primsTG primsTGW)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTDW implDPW implOK_implDPW)
open SparseHamiltonian.OracleCircuit
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open SourceAccuracyODE (WOutcome)
open GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Query)

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the time-dependent decoder solver under the manuscript's certificates from a
writer**: the guarantees of `decoder_time_cert_outcome` for the protocol
`nprotocol (prepTDW q N dc loadC wpC) (2g)` and the coherent sampled-time primitives
`primsTGW Wr x` of a writer `Wr` of the stored words of every sample (the loading and
weight-preparation circuits calling them), for every unitary action of the writer outside its
valid clean inputs. -/
theorem decoder_time_cert_outcome_writer (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    {b A : ℕ} (D : QData (X × Fin (2 ^ q.m)) N q.s q.k b) (Wr : D.Writer)
    (dc : BinDecode b q.b A)
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
    (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ) (sol : ℝ → Reg (Fin q.k) ℂ)
    (U : ℝ → Reg (Fin q.k) ℂ → ℝ → Reg (Fin q.k) ℂ) (bs : ℕ → Reg (Fin q.k) ℂ)
    (gb cq ζ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 25 * q.pub.params.nu)
    (hR : CertRestG q D x Jl Wp G bf sol U bs gb cq ζ) :
    WOutcome (prepTDW q N dc loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (primsTGW Wr x) (markEmb q.k (sol q.T)) := by
  have hc₀ : 0 < q.c0 := hq.c0_pos
  exact general_time_cert_outcomeI q hq hγ (D.decData dc q.c0 hc₀ hdc) (fun _ => false)
    (QData.decData_val_zero D dc q.c0 hc₀ hdc) (fun z => rfl) x
    (fun w => Wr.prims (R := ℂ) (x, wordEquivFin q.m w))
    (fun w j => Wr.prims_isUnitary (x, wordEquivFin q.m w) j)
    (implDPW (k := q.k) N q.s (fun _ => false) dc)
    (fun w => implOK_implDPW dc Wr q.c0 hc₀ hdc (fun _ => false)
      (QData.decData_val_zero D dc q.c0 hc₀ hdc) (x, wordEquivFin q.m w))
    loadC hloadV wpC hwpV hrH hcH hrD hcD Jl Wp G bf sol U bs gb cq ζ ζs hζs hload hwp hbud
    (certRestG_decData dc q.c0 hc₀ hdc hR)

end

end SparseHamiltonian.MeshCertificateODE

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb padLift primsTG primsTGW validEmb validLift
  norm_validEmb accretive_validLift)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTDW)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open SparseHamiltonian.MeshCertificateODE (umesh quadSum quadAmp quadMass sampleErr dissErr liftV)
open SparseHamiltonian.GeneralSourceExtensions (Mesh.meshScale)
open GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` with binary entry decoding and a writer, time-dependent
coefficients, with the manuscript's certificates** (handover item B4). The statement of
`ode_thm_gates_time_decoder_cert`, with its constant, for the protocol
`nprotocol (prepTDW (odePubTG … (2ḡ) …) N dc loadC wpC) (4ḡ)` (fixed before the writer and the
instance) and the coherent sampled-time primitives `primsTGW Wr x` of every writer `Wr` of the
stored words of every sample specified on the clean inputs of the valid pairs only. -/
theorem ode_thm_gates_time_decoder_cert_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N
            dc loadC wpC) j, i.Valid) ∧
          ((nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) dc Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs + C * dc.wires ∧
          (∀ c : Query → Bool,
            ((nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                (wCallN c) : ℝ) ≤
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
              (G : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (bf : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ) (sol : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (ζ ζs : ℝ),
            0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            (∀ c, OracleCircuit.IsUnitary (Jl c)) → Wp.conjTranspose * Wp = 1 →
            Wp * Wp.conjTranspose = 1 →
            (∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
              ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)) →
            (sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (sol 0)) →
            (∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (bs (wordValue w))) →
            (∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
              TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G →
            RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U →
            formal_classicalPropagator G (umesh T (2 ^ m)) T U →
            sol T ≠ 0 →
            Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖ →
            quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤ ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ζ + 2 * (sampleErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) +
              2 * dissErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r))) ≤
              ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (2 * gbar) ε *
                dissErr (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) ≤
              TimeDependentODE.precision (2 * gbar) ε →
            HeraldedOutput (nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
                ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
              (primsTGW Wr x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
                (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
                  loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTGW Wr x) (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD
                      T (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))‖ ≤ ε := by
  obtain ⟨C₀, hC₀, h⟩ := ode_thm_gates_time_decoder_writer.{u}
  refine ⟨108 * C₀, by positivity, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  have hg1 : 1 ≤ gbar := hg
  have hg2 : formal_gbarOne (2 * gbar) := one_le_two_mul hg
  have hε1 : ε ≤ 1 := by linarith
  have hg0 : 0 ≤ gbar := by linarith
  obtain ⟨hV, hG0, hQ0, hC0, -⟩ := h bd c0 etaH etaD T (2 * gbar) ε m D dc hm hk hF hbits hg2
    loadC wpC hloadV hwpV hH hD hT hε hε2
  -- the comparisons of the shapes and the word budgets
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hQ2 := odeShape_two_le hs0 hT hH hD hg1 hε hε1
  have hQ1 : 1 ≤ odeShape s T etaH etaD gbar ε :=
    GateRemarks.ODE.one_le_qOf (s := (s : ℝ)) hT hH hD hg1 hε hε1
  have hB0 : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) hg0) hε hε1
  have hQ1' : 1 ≤ odeShape s T etaH etaD (2 * gbar) ε :=
    GateRemarks.ODE.one_le_qOf (s := (s : ℝ)) hT hH hD (by linarith) hε hε1
  have hB0' : 0 ≤ bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD (2 * gbar) ε) (2 * gbar) ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith)) hε hε1
  have hBB := bitB_two_le (bd := bd) (N := N) (M := 2 ^ m) (M' := 2 ^ m) (by linarith) hQ2
    (by linarith) hg0 hε hε1
  have hY := cube_two_le hB0 hB0' hBB
  have hY0 : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 := by
    positivity
  have hY0' : 0 ≤ (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD (2 * gbar) ε) (2 * gbar) ε +
      1) ^ 3 := by positivity
  have hZ : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hCst : (0 : ℝ) ≤ dc.cost := Nat.cast_nonneg _
  have hWr : (0 : ℝ) ≤ dc.wires := Nat.cast_nonneg _
  refine ⟨hV, ?_, ?_, ?_, ?_⟩
  · -- gates
    exact hG0.trans (gates_two_le hC₀.le hg0 (by linarith) hQ2 (by positivity)
      (by linarith) (by positivity) hZ)
  · -- qubits
    have h1 := mul_le_mul_of_nonneg_left hY hC₀.le
    have h2 := mul_nonneg hC₀.le hZ
    have h3 := mul_nonneg hC₀.le hY0
    have h4 := mul_nonneg hC₀.le hWr
    linarith
  · -- calls
    intro c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    exact calls_two_le hC₀.le hg0 (by linarith) hQ2 hI0 (by positivity) (hC0 c)
  · -- the guarantees
    intro Wr x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs0 hload hwp hacc hJl hWl hWr' hWp hinit
      hforce hacc' hreg hmild hprop hne hscale hmass hsrc hbud hbranch
    obtain ⟨hbd, -, -, -, -⟩ := hbits
    set q := odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m with hqdef
    have hqp : q.pub = odePubT (k + 1) (sbP s) ((sbP_le D.s_le_pow).trans (Nat.le_succ k)) b' c0
        etaH etaD T (2 * gbar) ε m := rfl
    have hq : BTPublicOK0 q.pub := by
      rw [hqp]
      exact odePubT_ok _ hF.hb hF.hc0 hH hD hT hg2 hε hε2 hm
    have hγ := odePubT_gamma hqp hF.hb hbd
    have hζs := odePubT_zeta2 hqp hH hD hT hg1 hε hε2
    have hγ' : ¬ BTZeroCase q.pub →
        q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by
      intro hz
      have h := hγ
      rw [if_neg hz] at h
      exact h
    have hR : MeshCertificateODE.CertRestG q D x Jl Wp G bf sol U bs gbar 2 ζ :=
      { load_unitary := hJl
        prep_left := hWl
        prep_right := hWr'
        prep := fun w => by
          rw [MeshCertificateODE.srcAmp_eq_quadAmp q.pub.params hT]
          exact hWp w
        init_load := hinit
        forcing_load := hforce
        accretive := hacc'
        regular := hreg
        mild := hmild
        propagator := hprop
        target_ne := hne
        gb_pos := by linarith
        cq_nonneg := by norm_num
        scale := hscale
        mass := by
          rw [MeshCertificateODE.mass_eq_quadMass q.pub.params hT]
          exact hmass
        ratio := le_rfl
        source := hsrc
        budget := hbud
        branch := hbranch }
    -- the public data is passed literally (not as the local definition `q`), so that the
    -- outcome has the types of the statement and the final unification is syntactic
    have o := (MeshCertificateODE.decoder_time_cert_outcome_writer
      (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) hq hγ' D Wr dc hF.exact loadC
      hloadV wpC hwpV x hrH hcH hrD hcD Jl Wp G bf sol U bs gbar 2 ζ ζs hζs0 hload hwp
      (hζs ζs hacc) hR).mono (β' := ε) (by
        show ε / 100 ≤ ε
        linarith)
    rw [markEmb_eq_cleanAlong] at o
    exact ⟨⟨o.success_two_thirds, o.output_density, o.conditional_error⟩, o.trial_direction⟩

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` with binary entry decoding and a writer, time-dependent, with the
manuscript's certificates, for a problem on `ℂ^N`**: the guarantees of
`ode_thm_gates_time_decoder_cert_valid` for the protocol of `ode_thm_gates_time_decoder_cert_writer`
and the coherent sampled-time primitives `primsTGW Wr x` of every writer `Wr` of the stored words
of every sample on valid clean inputs. -/
theorem ode_thm_gates_time_decoder_cert_valid_writer {X : Type u} {N s k b b' A : ℕ} (bd : ℕ)
    (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b)
    (dc : BinDecode b b' A) (hm : odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m)
    (hk : 2 ^ k < 2 * N) (hF : BinaryEntryDecoding D dc c0)
    (hbits : comp_bits b' bd [c0, T, etaH, etaD]) (hg : formal_gbarOne gbar) {Zs : Type}
    [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (Wr : GeneralSparseAccess.QData.Writer D) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
    (G : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (bf : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N)) (sol : ℝ → EuclideanSpace ℂ (Fin N))
    (bs : ℕ → EuclideanSpace ℂ (Fin N))
    (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)) (ζ ζs : ℝ) (hζs0 : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs)
    (hacc : ζs ≤ ImprovedODEQueryBudget.precision gbar ε)
    (hJl : ∀ c, OracleCircuit.IsUnitary (Jl c)) (hWl : Wp.conjTranspose * Wp = 1)
    (hWr : Wp * Wp.conjTranspose = 1)
    (hWp : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ))
    (hinit : sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)))
    (hforce : ∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))))
    (hacc' : ∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
      TimeDependentODE.Accretive (G r u))
    (hreg : RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G)
    (hmild : RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U)
    (hprop : formal_classicalPropagator G (umesh T (2 ^ m)) T U) (hne : sol T ≠ 0)
    (hscale : Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖)
    (hmass : quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (hsrc : ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤
      ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (hbud : ζ + 2 * (sampleErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) +
      2 * dissErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r)))) ≤ ε / (2000 * gbar))
    (hbranch : 6 * TimeDependentODE.radius (2 * gbar) ε * dissErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    HeraldedOutput (nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
        ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
      (primsTGW Wr x) (ODEStateNormalization.unitDirection
        (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))) ε ∧
    ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
        (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
          loadC wpC) j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
            (nrun (primsTGW Wr x) (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T
              (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
          ODEStateNormalization.unitDirection
            (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))‖ ≤ ε := by
  obtain ⟨C, -, h⟩ := ode_thm_gates_time_decoder_cert_writer.{u}
  have hN : N ≤ 2 ^ k := D.hN
  have hg1 : 1 ≤ gbar := hg
  have hε1 : ε ≤ 1 := by linarith
  have hmesh := MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)
  have hS := MeshCertificateODE.sampleErr_padLift_le D x hmesh G hreg
  have hDS := MeshCertificateODE.dissErr_padLift_le D x hmesh G hreg
  have hR0 : 0 ≤ TimeDependentODE.radius (2 * gbar) ε :=
    ImprovedODEQueryBudget.radius_nonneg (2 * (2 * gbar)) (ε / 2) (by linarith) (by linarith)
      (by linarith)
  have hWp' : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (validEmb N k (sol 0)) (fun r => validEmb N k (bs r)) (w 0, Fin.tail w) :
        ℝ) : ℂ) := fun w => by
    rw [MeshCertificateODE.quadAmp_validEmb hN]
    exact hWp w
  have hinit' : validEmb N k (sol 0) ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)) :=
    fun h0 => hinit fun h1 => h0 (by rw [h1, map_zero])
  have hforce' : ∀ w : Fin m → Bool, validEmb N k (bs (wordValue w)) ≠ 0 →
      Jl (true, w) (seedV (S := Fin k)) =
        ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))) :=
    fun w hw => hforce w fun h1 => hw (by rw [h1, map_zero])
  have hacc'' : ∀ r : Fin (2 ^ m),
      ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
        TimeDependentODE.Accretive (validLift N k (G r u)) :=
    fun r u hu => accretive_validLift hN (hacc' r u hu)
  have hscale' : Mesh.meshScale (fun u => validEmb N k (sol u)) (fun r u => validEmb N k (bf r u))
      (umesh T (2 ^ m)) ≤ gbar * ‖validEmb N k (sol T)‖ := by
    rw [MeshCertificateODE.meshScale_validEmb hN, norm_validEmb hN]
    exact hscale
  have hmass' : quadMass T m (validEmb N k (sol 0)) (fun r => validEmb N k (bs r)) ≤
      2 * Mesh.meshScale (fun u => validEmb N k (sol u)) (fun r u => validEmb N k (bf r u))
        (umesh T (2 ^ m)) := by
    rw [MeshCertificateODE.quadMass_validEmb hN, MeshCertificateODE.meshScale_validEmb hN]
    exact hmass
  have hsrc' : ‖validEmb N k (sol T) - quadSum T (2 ^ m) (liftV N k U) (validEmb N k (sol 0))
      (fun r => validEmb N k (bs r))‖ ≤ ζ * Mesh.meshScale (fun u => validEmb N k (sol u))
        (fun r u => validEmb N k (bf r u)) (umesh T (2 ^ m)) := by
    rw [MeshCertificateODE.quadSum_liftV hN, ← map_sub, norm_validEmb hN,
      MeshCertificateODE.meshScale_validEmb hN]
    exact hsrc
  have hbud' : ζ + 2 * (sampleErr (umesh T (2 ^ m)) (fun r u => validLift N k (G r u))
      (fun r => padLift D (x, r)) + 2 * dissErr (umesh T (2 ^ m))
        (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r))) ≤ ε / (2000 * gbar) := by
    linarith
  have hbranch' : 6 * TimeDependentODE.radius (2 * gbar) ε * dissErr (umesh T (2 ^ m))
      (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r)) ≤
        TimeDependentODE.precision (2 * gbar) ε := by
    have := mul_le_mul_of_nonneg_left hDS
      (by linarith : (0 : ℝ) ≤ 6 * TimeDependentODE.radius (2 * gbar) ε)
    linarith
  exact (h bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg loadC wpC hloadV hwpV hH hD hT hε
    hε2).2.2.2.2 Wr x hrH hcH hrD hcD Jl Wp (fun r u => validLift N k (G r u))
    (fun r u => validEmb N k (bf r u)) (fun u => validEmb N k (sol u))
    (fun r => validEmb N k (bs r)) (liftV N k U) ζ ζs hζs0 hload hwp hacc hJl hWl hWr hWp' hinit'
    hforce' hacc'' (MeshCertificateODE.regular_validLift hreg)
    (MeshCertificateODE.mild_liftV hN hmild) (MeshCertificateODE.isMeshPropagator_liftV hN hprop)
    (MeshCertificateODE.validEmb_ne_zero hN hne) hscale' hmass' hsrc' hbud' hbranch'

end

end ManuscriptConformance
