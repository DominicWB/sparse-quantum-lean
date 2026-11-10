import GateEfficientSelective.ODESolver
import GateEfficientBitBudget.Synth

/-!
# Equations `ode:eq:gate-main` and `ode:eq:gate-space` with retained source circuits

Theorem `ode:thm:gates` of the accompanying paper bounds the gates of the solver (here over the
finite gate set, a partial formalisation, under this package's format hypotheses, of its finite-set
statement: the manuscript states Theorem `ode:thm:gates` over a finite gate set; the conformance
endpoints count native gates) by
`C ḡ [q P(𝔟) + G_src(ν) + A_src(ν)]` and its qubits by `P(𝔟) + C A_src(ν)`, where `G_src` counts the
supplied source and weight-preparation circuits over the gate set and `P` does not depend on them.
The released finite-gate-set budgets (`GateBitBudget.binary_ode_budget_trials_bits` and its
time-dependent analogue) synthesise the source circuits with the rest of the
preparation, so their gate bound contains `G_src · log(G_src + 1)`. Here the preparation is
compiled selectively (`selPrep`): with source circuits over `𝒢` (and `𝒢` adjoint-closed), the
synthesised gate occurrences are bounded by the native preparation bound with empty source
circuits, `R = prepBound q ∅ ≤ 2·10¹⁸ q* (𝔟+1)³`, and

* `binary_ode_budget_sel` (constant coefficients): in every history at most
  `40 g (G_src + 2·10¹⁸ q* (𝔟+1)³ (64 c₁ (𝔟+1) + c₀ + 1)) + 20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)`
  gates of `𝒢`, `G_src = |srcC 0| + |srcC 1|`;
* `binary_ode_time_budget_sel` (time-dependent coefficients, common mesh): the same with `80 g`,
  `40 g` and `G_src = |loadC| + 2 |wpC|`.

`G_src` enters linearly, outside every logarithm, and the polynomial in `𝔟` does not depend on the
source circuits; `A_src = |Zs|` enters through the zero tests (`2 |Zs|`) and the register
(`4 |Zs|`). The calls, the register and the guarantees `NOutcome` are those of the released
budgets (with the selective preparation).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open GateBinary GateBinaryODE GateBinaryODETime
open GateODEBudget (gammaOf qOf prepBound prepBoundT binary_ode_sizes binary_ode_time_sizes
  call_budget_arith card_SX card_XW_SZ4 pub_shapeOK pubT_shapeOK)
open GateBitBudget (bitB HasBits binary_ode_budget_trials_bits binary_ode_time_budget_trials_bits
  log_factor_le log_factorT_le tested_le testedT_le)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-- The monotonicity of the separated closed form. -/
theorem sep_mono {c d g G R R' L Λ c₀ c₁ n n' : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hg : 0 ≤ g)
    (hR0 : 0 ≤ R) (hR : R ≤ R') (hL : L ≤ Λ) (hΛ : 0 ≤ Λ) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hn : n ≤ n') :
    c * g * (G + R * (c₁ * L + c₀ + 1)) + d * g * (4 * n + 3) ≤
      c * g * (G + R' * (c₁ * Λ + c₀ + 1)) + d * g * (4 * n' + 3) := by
  have h1 : R * (c₁ * L + c₀ + 1) ≤ R * (c₁ * Λ + c₀ + 1) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hR0
  have h2 : R * (c₁ * Λ + c₀ + 1) ≤ R' * (c₁ * Λ + c₀ + 1) :=
    mul_le_mul_of_nonneg_right hR (by positivity)
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) (mul_nonneg hc hg)
  have h4 : d * g * (4 * n + 3) ≤ d * g * (4 * n' + 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hd hg)
  nlinarith

/-- The empty circuit has no gate. -/
theorem nGatesN_empty {V Y J : Type*} : nGatesN ([] : List (NInstr V Y J)) = 0 := rfl

section Constant

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

omit [Fintype Zs] [DecidableEq Zs] in
/-- The gate bound of one native preparation splits into the bound with empty source circuits
and the gates of the source circuits. -/
theorem prepBound_split (q : Pub)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    prepBound q srcC = prepBound (Zs := Zs) q (fun _ => []) +
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := by
  simp only [prepBound, nGatesN_empty, Nat.cast_zero, add_zero]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` with retained source circuits,
constant coefficients** (partial formalisation, under this package's format hypotheses, of the
finite-set statement of Theorem `ode:thm:gates`, constant coefficients). Under
the hypotheses of `GateBitBudget.binary_ode_budget_trials_bits` (`Synthesis 𝒢 Xa len` with
`len ζ ≤ c₁ log(1/ζ) + c₀`, `AdjClosed 𝒢`, `zeroTestKinds ⊆ 𝒢`, the public rescaling,
`ζ ≥ ν/(196608 q*)` and the bit lengths) and source circuits over `𝒢`, with
`𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε` and `G_src = |srcC 0| + |srcC 1|`, the selective
protocol `nprotocol (selPrep hS (ν/3) (q.prep srcC)) g`: (1) has valid trials whose gates are
gates of `𝒢`; (2) synthesises at most `R = prepBound q ∅ ≤ 2·10¹⁸ q* (𝔟+1)³` gate occurrences
per preparation, a bound that does not depend on the source circuits; (3) uses in every history
at most
`40 g (G_src + 2·10¹⁸ q* (𝔟+1)³ (64 c₁ (𝔟+1) + c₀ + 1)) + 20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)`
gates; (4) makes at most `3932160 g q*` calls of each matrix oracle besides `40 g` times the calls
of the source circuits; (5) has at most `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; and (6) has the
guarantees `NOutcome` for every input and instance as in `GateBinaryODE.binary_ode_solver` with
`98304 q* ζ + 2 ζs ≤ ν`. -/
theorem binary_ode_budget_sel (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : Pub) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid)
    (hsrcG : ∀ c, ∀ g, NInstr.gate g ∈ srcC c → GateOf 𝒢 g) :
    (∀ j, (∀ i ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep srcC)) j →
        GateOf 𝒢 g) ∧
    (nSynN 𝒢 (q.prep srcC) : ℝ) ≤ prepBound (Zs := Zs) q (fun _ => []) ∧
    prepBound (Zs := Zs) q (fun _ => []) ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 ∧
    ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * (((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 *
          (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1)) + c₀ + 1)) +
      20 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs +
        Fintype.card Xa) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤
      3932160 * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    (Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 4 * Fintype.card Zs +
        2 * Fintype.card Xa ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (selPrep hS (q.params.nu / 3) (q.prep srcC)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  have hsh := pub_shapeOK q hq
  obtain ⟨-, hd, -, -, -, -, -⟩ := binary_ode_sizes q hq hγ
  obtain ⟨hV0, -, hC, -, -, -⟩ := GateBinaryODE.binary_ode_counts q hq srcC hsrcV
  have hprepV : ∀ i ∈ q.prep srcC, i.Valid := fun i hi => hV0 0 i (List.mem_append_left _ hi)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hout⟩ :=
    native_ode_solver_sel hS hadj hzt q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd
      q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) srcC hsrcV hsrcG
  -- the released bit budgets, for the source circuits and for empty ones
  obtain ⟨-, -, hqub, -, hNS, -⟩ := binary_ode_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen bd q hq
    hγ hζ hb hc0 hT hH hD D en hrange hdec srcC hsrcV
  obtain ⟨hBp0, -, -, -, hN0, -⟩ := binary_ode_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen bd q hq
    hγ hζ hb hc0 hT hH hD D en hrange hdec (Zs := Zs) (fun _ => []) (fun _ i hi => by simp at hi)
  have hE0 : ((nGatesN ([] : List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) : ℝ) +
      nGatesN ([] : List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))) = 0 := by
    simp [nGatesN]
  rw [hE0, add_zero] at hBp0
  have hR0 : 0 ≤ prepBound (Zs := Zs) q (fun _ => []) := le_trans (Nat.cast_nonneg _) hN0
  have hsyn : (nSynN 𝒢 (q.prep srcC) : ℝ) ≤ prepBound (Zs := Zs) q (fun _ => []) := by
    have h1 := nSynN_nprepC_le 𝒢 hadj q.params q.UJg q.nd q.ar srcC hsrcG
    have h2 : ((nSynN 𝒢 (q.prep srcC) : ℕ) : ℝ) ≤
        ((nGatesN (q.prep (Zs := Zs) (fun _ => [])) : ℕ) : ℝ) := by exact_mod_cast h1
    exact h2.trans hN0
  have hlog := log_factor_le bd q hq hγ hζ hb hc0 hT hH hD (Zs := Zs) (fun _ => []) hR0
  rw [hE0, zero_add, Real.log_one, add_zero] at hlog
  have hn := tested_le bd q hq hγ hζ hb hc0 hT hH hD
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge
      (hq.ε_half.trans (by norm_num))
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε :=
    GateBitBudget.bitB_nonneg bd _ _ _ (mul_nonneg (le_trans zero_le_one hsh.one_le_q) hg0)
      hq.ε_pos (hq.ε_half.trans (by norm_num))
  obtain ⟨hWC, -⟩ := sel_protocol_worst hS hη _ hprepV q.g hq.g_ge
  refine ⟨fun j => ⟨trialSel_valid hS hη _ hprepV j, trialSel_gateOf hS hadj hzt hη _ hprepV j⟩,
    hsyn, hBp0, ?_, ?_, hqub, ?_⟩
  · -- gates
    have hW := sel_protocol_worst_log hS hη hη1 _ hprepV q.g hq.g_ge hc₀ hc₁ hlen _ hsyn
    have hnc : Fintype.card q.params.W + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
          Xa) + Fintype.card (Fin q.kx) =
        (22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
          8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47) + 2 * Fintype.card Zs +
          Fintype.card Xa := by
      have ha : q.params.a = q.kx + 3 := rfl
      rw [card_SX, nPool, card_XW_SZ4, q.params.card_W, Fintype.card_fin]
      omega
    have hnc' : ((Fintype.card q.params.W : ℕ) : ℝ) +
        (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
        (Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
          Xa) : ℕ) + (Fintype.card (Fin q.kx) : ℕ) ≤
        3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs +
          Fintype.card Xa := by
      have e : ((Fintype.card q.params.W : ℕ) : ℝ) +
          (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
          (Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) : ℕ) + (Fintype.card (Fin q.kx) : ℕ) =
          ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
            8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 : ℕ) : ℝ) +
            2 * Fintype.card Zs + Fintype.card Xa := by
        rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, hnc]
        push_cast
        ring
      rw [e]
      linarith
    have hNk : (nKeepN 𝒢 (q.prep srcC) : ℝ) ≤
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
          prepBound (Zs := Zs) q (fun _ => []) := by
      have h1 : ((nKeepN 𝒢 (q.prep srcC) : ℕ) : ℝ) ≤ (nGatesN (q.prep srcC) : ℝ) := by
        exact_mod_cast nKeepN_le 𝒢 (q.prep srcC)
      rw [prepBound_split q srcC] at hNS
      linarith
    have hS1 := sep_arith (c := 40) (c₀ := c₀) (c₁ := c₁)
      (lam := Real.log ((prepBound (Zs := Zs) q (fun _ => []) + 1) / (q.params.nu / 3)))
      (by norm_num) hg0 hNk
      (T := ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) - 20 * q.g * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + Fintype.card (Fin q.kx)) + 3))
      (by linarith)
    have hS2 := sep_mono (c := 40) (d := 20) (g := q.g)
      (G := (nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) (c₀ := c₀) (c₁ := c₁)
      (by norm_num) (by norm_num) hg0 hR0 hBp0 hlog (by positivity) hc₀ hc₁ hnc'
    linarith
  · -- calls
    intro c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hc : (nCallsN c (q.prep srcC) : ℝ) ≤ 12 * (q.params.d : ℝ) *
        (2 * ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0)
          + (if c Query.value then 1 else 0))) +
        ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true)) := by
      have h1 : (nCallsN c (q.prep srcC) : ℝ) ≤ ((12 * q.params.d *
          (2 * (if c Query.rowLocation then 1 else 0) +
            2 * (if c Query.columnLocation then 1 else 0) +
            2 * (if c Query.value then 1 else 0)) +
          nCallsN c (srcC false) + nCallsN c (srcC true) : ℕ) : ℝ) := by
        exact_mod_cast hC c
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    refine (hWC c).trans ((call_budget_arith 40 q.g _ _ _ _ _ (by norm_num) hg0 hI0 hd hc).trans
      (le_of_eq ?_))
    ring
  · -- guarantees
    intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
    have hbud' : 24 * (q.params.d : ℝ) * q.ζ + 2 * ζs ≤ q.params.nu := by
      have hζ0 := hq.ζ_pos.le
      have := mul_le_mul_of_nonneg_right hd hζ0
      linarith
    have h := hout (prims (R := ℂ) D en x) (privFam q.params D en x q.rho q.γ) Jsrc
      (hLift D en x) (lLift D en x) x0 v ζs (prims_isUnitary D en x)
      (q.nativeOK hq D en hrange hdec x) hζs hsrc hbud'
      (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jsrc x0 v hJ hx0 hv hpx hpv hne hB)
    rw [target_lift] at h
    exact h

end Constant

section Time

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

omit [Fintype Zs] [DecidableEq Zs] in
/-- The gate bound of one native preparation (time-dependent coefficients) splits into the bound
with empty loading and weight-preparation circuits and `|loadC| + 2 |wpC|`. -/
theorem prepBoundT_split (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    prepBoundT q loadC wpC = prepBoundT (Zs := Zs) q [] [] +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
  simp only [prepBoundT, nGatesN_empty, Nat.cast_zero, mul_zero, add_zero]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` with retained source circuits,
time-dependent coefficients** (partial formalisation, under this package's format hypotheses, of
the finite-set statement of Theorem `ode:thm:gates`, time-dependent part,
common mesh). Under the hypotheses of `GateBitBudget.binary_ode_time_budget_trials_bits` and loading
and weight-preparation circuits over `𝒢`, with `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`
(`q* = qOf s T η_H η_D (2g) (ε/2)`) and `G_src = |loadC| + 2 |wpC|`: the selective protocol
(ratio `2g`) has valid trials over `𝒢`; it synthesises at most
`R = prepBoundT q ∅ ∅ ≤ 2·10¹⁸ q* (𝔟+1)³` gate occurrences per preparation; it uses in every
history at most
`80 g (G_src + 2·10¹⁸ q* (𝔟+1)³ (64 c₁ (𝔟+1) + c₀ + 1)) + 40 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)`
gates; at most `7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times the
calls of `loadC` and twice those of `wpC`; at most `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; and
the guarantees `NOutcome` for every input and instance as in
`GateBinaryODETime.binary_ode_time_solver` with `98304 q* ζ + 3 ζs ≤ ν`. -/
theorem binary_ode_time_budget_sel (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid) (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    (∀ j, (∀ i ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nSynN 𝒢 (q.prep loadC wpC) : ℝ) ≤ prepBoundT (Zs := Zs) q [] [] ∧
    prepBoundT (Zs := Zs) q [] [] ≤
      2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 ∧
    ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 *
          (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1)) + c₀ + 1)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
        (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax →
      NOutcome (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  have hsh := pubT_shapeOK q hq
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  obtain ⟨hV0, -, hC, -, -, -⟩ :=
    GateBinaryODETime.binary_ode_time_counts q hq loadC hloadV wpC hwpV
  have hprepV : ∀ i ∈ q.prep loadC wpC, i.Valid :=
    fun i hi => hV0 0 i (List.mem_append_left _ hi)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hout⟩ :=
    native_ode_time_solver_sel hS hadj hzt q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
      q.nd q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV hloadG wpC hwpV hwpG
  obtain ⟨-, -, hqub, -, hNS, -⟩ := binary_ode_time_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen bd
    q hq hγ hζ hb hc0 hT hH hD D en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨hBp0, -, -, -, hN0, -⟩ := binary_ode_time_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen bd
    q hq hγ hζ hb hc0 hT hH hD D en hrange hdec (Zs := Zs) [] (by simp) [] (by simp)
  have hE0 : ((nGatesN ([] : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs)
      (Fin q.m ⊕ PY q.kx q.b) Query)) : ℝ) +
      2 * nGatesN ([] : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
        Query))) = 0 := by
    simp [nGatesN]
  rw [hE0, add_zero] at hBp0
  have hR0 : 0 ≤ prepBoundT (Zs := Zs) q [] [] := le_trans (Nat.cast_nonneg _) hN0
  have hsyn : (nSynN 𝒢 (q.prep loadC wpC) : ℝ) ≤ prepBoundT (Zs := Zs) q [] [] := by
    have h1 := nSynN_tnprepC_le 𝒢 hadj q.params q.UJg q.nd q.ar loadC hloadG wpC hwpG
    have h2 : ((nSynN 𝒢 (q.prep loadC wpC) : ℕ) : ℝ) ≤
        ((nGatesN (q.prep (Zs := Zs) [] []) : ℕ) : ℝ) := by exact_mod_cast h1
    exact h2.trans hN0
  have hlog := log_factorT_le bd q hq hγ hζ hb hc0 hT hH hD (Zs := Zs) [] [] hR0
  rw [hE0, zero_add, Real.log_one, add_zero] at hlog
  have hn := testedT_le bd q hq hγ hζ hb hc0 hT hH hD
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
      (by linarith [hq.g_ge]) (by linarith [hq.ε_half])
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  have hr2 : q.params.ratio = 2 * q.g := rfl
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    GateBitBudget.bitB_nonneg bd _ _ _ (mul_nonneg (le_trans zero_le_one hsh.one_le_q) hg0)
      hq.ε_pos (hq.ε_half.trans (by norm_num))
  obtain ⟨hWC, -⟩ := sel_protocol_worst hS hη _ hprepV q.params.ratio (q.params.ratio_ge hq.g_ge)
  refine ⟨fun j => ⟨trialSel_valid hS hη _ hprepV j, trialSel_gateOf hS hadj hzt hη _ hprepV j⟩,
    hsyn, hBp0, ?_, ?_, hqub, ?_⟩
  · -- gates
    have hW := sel_protocol_worst_log hS hη hη1 _ hprepV q.params.ratio
      (q.params.ratio_ge hq.g_ge) hc₀ hc₁ hlen _ hsyn
    have hnc : Fintype.card q.params.W + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
          q.ar.A) Xa) + Fintype.card (Fin q.kx) =
        (22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47) + 2 * Fintype.card Zs + Fintype.card Xa := by
      have ha : q.params.a = q.kx + 3 := rfl
      rw [card_SX, tnPool, card_XW_SZ4, q.params.card_W, Fintype.card_fin]
      omega
    have hnc' : ((Fintype.card q.params.W : ℕ) : ℝ) +
        (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
        (Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
          q.ar.A) Xa) : ℕ) + (Fintype.card (Fin q.kx) : ℕ) ≤
        3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
          2 * Fintype.card Zs + Fintype.card Xa := by
      have e : ((Fintype.card q.params.W : ℕ) : ℝ) +
          (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
          (Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) : ℕ) + (Fintype.card (Fin q.kx) : ℕ) =
          ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
            2 * (q.ar.bT + q.ar.bP + q.ar.A) + 47 : ℕ) : ℝ) +
            2 * Fintype.card Zs + Fintype.card Xa := by
        rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add, hnc]
        push_cast
        ring
      rw [e]
      linarith
    have hNk : (nKeepN 𝒢 (q.prep loadC wpC) : ℝ) ≤
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + prepBoundT (Zs := Zs) q [] [] := by
      have h1 : ((nKeepN 𝒢 (q.prep loadC wpC) : ℕ) : ℝ) ≤ (nGatesN (q.prep loadC wpC) : ℝ) := by
        exact_mod_cast nKeepN_le 𝒢 (q.prep loadC wpC)
      rw [prepBoundT_split q loadC wpC] at hNS
      linarith
    generalize ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
      (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) = W at hW ⊢
    rw [hr2] at hW
    have hS1 := sep_arith (c := 80) (c₀ := c₀) (c₁ := c₁)
      (lam := Real.log ((prepBoundT (Zs := Zs) q [] [] + 1) / (q.params.nu / 3)))
      (by norm_num) hg0 hNk
      (T := W - 40 * q.g *
          (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + Fintype.card (Fin q.kx)) + 3))
      (by linarith)
    have hS2 := sep_mono (c := 80) (d := 40) (g := q.g)
      (G := (nGatesN loadC : ℝ) + 2 * nGatesN wpC) (c₀ := c₀) (c₁ := c₁)
      (by norm_num) (by norm_num) hg0 hR0 hBp0 hlog (by positivity) hc₀ hc₁ hnc'
    linarith
  · -- calls
    intro c
    have hI0 : (0 : ℝ) ≤ (if c Query.rowLocation then 1 else 0) +
        (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    have hc : (nCallsN c (q.prep loadC wpC) : ℝ) ≤ 12 * (q.params.d : ℝ) *
        (2 * ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0)
          + (if c Query.value then 1 else 0))) +
        ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by
      have h1 : (nCallsN c (q.prep loadC wpC) : ℝ) ≤ ((12 * q.params.d *
          (2 * (if c Query.rowLocation then 1 else 0) +
            2 * (if c Query.columnLocation then 1 else 0) +
            2 * (if c Query.value then 1 else 0)) +
          nCallsN c loadC + 2 * nCallsN c wpC : ℕ) : ℝ) := by
        exact_mod_cast hC c
      refine h1.trans (le_of_eq ?_)
      push_cast
      ring
    have h := (hWC c).trans ((call_budget_arith 40 q.params.ratio _ _ _ _ _ (by norm_num)
      (le_trans zero_le_one (q.params.ratio_ge hq.g_ge)) hI0 hd hc))
    refine h.trans (le_of_eq ?_)
    rw [hr2]
    ring
  · -- guarantees
    intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    have hbud' : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu := by
      have hζ0 := hq.ζ_pos.le
      have := mul_le_mul_of_nonneg_right hd hζ0
      linarith
    exact hout (primsT (R := ℂ) D en x) (privFamT q.params D en x q.rho q.γ) Jl Wp (HsT D en x)
      (LsT D en x) G bf xs bs βG δG βb δb bmax ζs (primsT_isUnitary D en x)
      (q.nativeOK hq D en hrange hdec x) hζs hload hwp hbud'
      (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax hR)

end Time

end

end SparseHamiltonian.GateSelective
