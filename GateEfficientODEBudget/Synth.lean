import GateEfficientODEBudget.Time
import GateEfficientSynthesisTrials.Binary

/-!
# The budget over a finite gate set

Equation `ode:eq:gate-main` counts the non-matrix-oracle gates of the complete solver over a
finite gate set. The solvers of `GateEfficientSynthesisTrials` synthesise one native preparation
over `𝒢` (synthesis budget `ν/3`) and keep the zero tests, the sign and the inverse preparation
exact; with the public rescaling `γ = gammaOf …` of `GateEfficientODEBudget.Constant` and
`GateEfficientODEBudget.Time`:

* `prepBound`, `prepBoundT`: the bound
  `B = 819400 q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src` (respectively without `k`,
  with `q*` and `ℓ` for `(2g, ε/2)`); `prep_budget_arith`, `prep_budget_arith'`: one native
  preparation has at most `B` elementary gates;
* `binary_ode_budget_trials` (constant coefficients) and `binary_ode_time_budget_trials`
  (time-dependent coefficients): every trial of the synthesised protocol consists of valid gates
  of `𝒢` and primitive calls; if `len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, in every history the
  synthesised protocol uses at most
  `40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n + 3)` gates of `𝒢` (respectively `2g` in place
  of `g`), where `n = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| +
  |Xa| + 47` (respectively `16 m` and no `k`) counts the tested wires: the native register and the
  synthesis ancillas; it makes `O(g q*)` matrix-oracle calls; its register has
  `44 k_x + 24 m + 48 r + 8 k + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95` qubits
  (respectively `32 m` and no `k`); and with the arithmetic budget `98304 q* ζ + 2 ζs ≤ ν`
  (respectively `3 ζs`) it has the guarantees `NOutcome`, every successful trial included.

This is equation `ode:eq:gate-main` over a finite gate set in the form
`G ≤ C g [(q* (G_C + polylog) + G_src) · log((q* (G_C + polylog) + G_src)/ν) + A]`, and
`ode:eq:gate-space` with `A_src = |Zs|` and the synthesis ancillas `|Xa|`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateODEBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateSynth SparseHamiltonian.GateSynthTrials
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### Arithmetic -/

/-- **The gates of one native preparation**, from the released counts and `d ≤ 4096 q*`,
`2^l < 2 (J + 2)`, `J ≤ 60 q* ℓ`. -/
theorem prep_budget_arith (Q ℓ d J P k l kx m r σ GC Gs c N : ℝ) (hQ : 1 ≤ Q) (hℓ : 1 ≤ ℓ)
    (hd : d ≤ 4096 * Q) (hJ : J ≤ 60 * Q * ℓ) (hP : P ≤ 2 * (J + 2))
    (hP0 : 0 ≤ P) (hc : c ≤ 1) (hk : 0 ≤ k) (hl : 0 ≤ l) (hkx : 0 ≤ kx)
    (hm : 0 ≤ m) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hGC : 0 ≤ GC)
    (hN : N ≤ 200 * (d + 1) * (kx + 3 + m + r + 1) + 2 * c * (k + 1) + 3 * (P * (2 * l + 1)) +
      84 * d * (σ + 3) + 6 * d * GC + Gs) :
    N ≤ 819400 * Q * (GC + kx + σ + m + r + k + ℓ * (l + 1) + 8) + Gs := by
  have hQℓ : 1 ≤ Q * ℓ := by nlinarith
  have h1 : 200 * (d + 1) * (kx + 3 + m + r + 1) ≤ 819400 * Q * (kx + m + r + 4) := by
    have : d + 1 ≤ 4097 * Q := by linarith
    have h0 : 0 ≤ kx + m + r + 4 := by linarith
    nlinarith
  have h2 : 2 * c * (k + 1) ≤ 819400 * Q * (k + 1) := by nlinarith
  have h3 : 3 * (P * (2 * l + 1)) ≤ 819400 * Q * (ℓ * (l + 1)) := by
    have hP' : P ≤ 124 * (Q * ℓ) := by linarith
    have hl1 : 0 ≤ 2 * l + 1 := by linarith
    have : P * (2 * l + 1) ≤ 124 * (Q * ℓ) * (2 * (l + 1)) :=
      mul_le_mul hP' (by linarith) hl1 (by positivity)
    nlinarith
  have h4 : 84 * d * (σ + 3) ≤ 819400 * Q * (σ + 3) := by nlinarith
  have h5 : 6 * d * GC ≤ 819400 * Q * GC := by nlinarith
  nlinarith

/-- **The gates of one native preparation without the quadrature register** (time-dependent
coefficients). -/
theorem prep_budget_arith' (Q ℓ d J P l kx m r σ GC Gs N : ℝ) (hQ : 1 ≤ Q) (hℓ : 1 ≤ ℓ)
    (hd : d ≤ 4096 * Q) (hJ : J ≤ 60 * Q * ℓ) (hP : P ≤ 2 * (J + 2)) (hP0 : 0 ≤ P)
    (hl : 0 ≤ l) (hkx : 0 ≤ kx) (hm : 0 ≤ m) (hr : 0 ≤ r) (hσ : 0 ≤ σ) (hGC : 0 ≤ GC)
    (hN : N ≤ 200 * (d + 1) * (kx + 3 + m + r + 1) + 3 * (P * (2 * l + 1)) +
      84 * d * (σ + 3) + 6 * d * GC + Gs) :
    N ≤ 819400 * Q * (GC + kx + σ + m + r + ℓ * (l + 1) + 8) + Gs := by
  have h := prep_budget_arith Q ℓ d J P 0 l kx m r σ GC Gs 0 N hQ hℓ hd hJ hP hP0
    (by norm_num) le_rfl hl hkx hm hr hσ hGC (by linarith)
  linarith

/-! ### The gate bound of one native preparation -/

/-- **The gate bound of one native preparation**, constant coefficients:
`B = 819400 q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src`, with `q* = qOf s T η_H η_D g ε`,
`ℓ = log(1/ν)`, `G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private call
and `G_src = |srcC 0| + |srcC 1|` the gates of the source circuits. -/
def prepBound {Zs : Type*} (q : Pub)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) : ℝ :=
  819400 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
      (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
        q.kx + q.σ + q.params.m + q.params.r + q.params.k +
        logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) +
    ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))

/-- **The gate bound of one native preparation**, time-dependent coefficients:
`B = 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src`, with `q*` and `ℓ` for `(2g, ε/2)`
(the internal ratio and accuracy of the released time-dependent solver), `G_C` as for constant
coefficients and `G_src = |loadC| + 2 |wpC|`. -/
def prepBoundT {Zs : Type*} (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) : ℝ :=
  819400 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
        q.kx + q.σ + q.params.m + q.params.r +
        logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
    ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- The added work wires of the binary solvers (the scratch wires `SZ4 k_x b`, the arithmetic
wires and three further wires): `6 k_x + 4 b + bT + bP + A + 3`. -/
theorem card_XW_SZ4 (kx b bT bP A : ℕ) :
    Fintype.card (XW (SZ4 kx b) bT bP A) = 6 * kx + 4 * b + bT + bP + A + 3 := by
  simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
  ring

omit [DecidableEq Zs] [DecidableEq Xa] in
/-- The scratch slot of the trial register (native scratch, flag and pool, synthesis ancillas):
`|Zs| + 1 + nP + |Xa|`. -/
theorem card_SX (nP : ℕ) :
    Fintype.card (SX Zs nP Xa) = Fintype.card Zs + 1 + nP + Fintype.card Xa := by
  simp only [SX, OX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  ring

/-- **The gate, call and qubit budget over a finite gate set, constant coefficients**
(Theorem `ode:thm:gates`, equations `ode:eq:gate-main` and `ode:eq:gate-space` over a finite
gate set). Under `Synthesis 𝒢 Xa len` with `len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`,
`AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, for the public data `q` with `γ = gammaOf T η_H η_D g ε`,
`q* = qOf s T η_H η_D g ε`, `ℓ = log(1/ν)` and the binary data and source circuits of
`binary_ode_solver`, with `B = prepBound q srcC`
`= 819400 q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src`: every instruction of every
trial of the synthesised protocol `nprotocol (synthPrep hS (ν/3) (q.prep srcC)) g` is valid and
every gate is a gate of `𝒢`; one native preparation has at most `B` gates; in every history the
synthesised protocol uses at most `40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n + 3)` gates of
`𝒢`, with `n = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`,
and at most `3932160 g q*` calls of each matrix oracle besides `40 g` times the calls of the
source circuits; its register has
`44 k_x + 24 m + 48 r + 8 k + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95` qubits;
and for every input and instance as in `binary_ode_solver` with `98304 q* ζ + 2 ζs ≤ ν` it has
the guarantees `NOutcome`, in particular every successful trial is within `ε/500` of the
normalised solution up to a global phase. -/
theorem binary_ode_budget_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (q : Pub) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (q.prep srcC) : ℝ) ≤ prepBound q srcC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * (prepBound q srcC *
        (c₁ * Real.log ((prepBound q srcC + 1) / (q.params.nu / 3)) + c₀)) +
      20 * q.g * (4 * ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k +
        4 * q.params.l + 8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤
      3932160 * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 24 * q.params.m + 48 * q.params.r + 8 * q.params.k + 8 * q.params.l +
        16 * q.b + 4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs +
        2 * Fintype.card Xa + 95 ∧
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
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  have h := pub_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -, -⟩ := binary_ode_sizes q hq hγ
  obtain ⟨hV, hG, hC, hSG, -, hWC, hWG, -, hcard, hout⟩ :=
    binary_ode_solver_trials hS hadj hzt q hq D en hrange hdec srcC hsrcV
  have hq1 := h.one_le_q
  have hℓ := h.ell_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge
      (hq.ε_half.trans (by norm_num))
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  have ha : q.params.a = q.kx + 3 := rfl
  -- one native preparation
  have hN : (nGatesN (q.prep srcC) : ℝ) ≤ prepBound q srcC := by
    unfold prepBound
    have h1 : (nGatesN (q.prep srcC) : ℝ) ≤ ((q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
        6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
          (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN (srcC false) + nGatesN (srcC true) : ℕ) : ℝ) := by
      exact_mod_cast hG
    have hP : ((2 ^ q.params.l : ℕ) : ℝ) ≤ 2 * ((q.params.J : ℝ) + 2) := by
      exact_mod_cast q.params.l_bounds.2.le
    have ha' : ((q.params.a : ℕ) : ℝ) = (q.kx : ℝ) + 3 := by rw [ha]; push_cast; ring
    rw [q.params.prepGates_eq] at h1
    generalize q.params.d = d at h1 hd
    generalize 2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) = GC
      at h1 ⊢
    push_cast at h1 hP
    rw [ha'] at h1
    exact prep_budget_arith _ _ _ _ _ _ _ _ _ _ _ _ _ 1 _ hq1 hℓ hd hJ hP (by positivity) le_rfl
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)
  refine ⟨hV, hN, ?_, ?_, ?_, ?_⟩
  · -- gates
    have hNS := (Nat.cast_le.mpr hSG).trans (gates_log_le hc₀ hc₁ hlen hη hη1 _ _ hN)
    have hn : Fintype.card q.params.W + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
          Xa) + q.kx =
        22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
          8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + Fintype.card Xa +
          47 := by
      rw [card_SX, nPool, card_XW_SZ4, q.params.card_W, Fintype.card_fin]
      omega
    have hn' : ((Fintype.card q.params.W : ℕ) : ℝ) +
        (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
        (Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
          Xa) : ℕ) + (q.kx : ℝ) =
        ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
          8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + Fintype.card Xa +
          47 : ℕ) : ℝ) := by
      rw [← hn]
      push_cast
      ring
    rw [hn'] at hWG
    have h40 := mul_le_mul_of_nonneg_left hNS (by positivity : (0 : ℝ) ≤ 40 * q.g)
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
  · -- qubits
    rw [hcard, nPool, card_XW_SZ4, q.params.card_W, Fintype.card_fin]
    omega
  · -- guarantees
    intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJs hζs hsrc hbud hx0 hv hpx hpv hne hB
    refine hout x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJs hζs hsrc ?_ hx0 hv hpx hpv hne hB
    have hζ := hq.ζ_pos.le
    have := mul_le_mul_of_nonneg_right hd hζ
    linarith

/-- **The gate, call and qubit budget over a finite gate set, time-dependent coefficients**
(Theorem `ode:thm:gates`, time-dependent part, equations `ode:eq:gate-main` and
`ode:eq:gate-space` over a finite gate set). Under `Synthesis 𝒢 Xa len` with
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, for the public
data `q` with `γ = gammaOf T η_H η_D (2g) (ε/2)`, `q* = qOf s T η_H η_D (2g) (ε/2)`,
`ℓ = log(1/ν)` and the time-indexed binary data and the valid circuits `loadC`, `wpC` of
`binary_ode_time_solver`, with `B = prepBoundT q loadC wpC`
`= 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src`, `G_src = |loadC| + 2 |wpC|`: every
instruction of every trial of the synthesised protocol
`nprotocol (synthPrep hS (ν/3) (q.prep loadC wpC)) (2g)` is valid and every gate is a gate of
`𝒢`; one native preparation has at most `B` gates; in every history the synthesised protocol
uses at most `80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` gates of `𝒢`, with
`n = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`, and at most
`7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times the calls of
`loadC` and twice those of `wpC`; its register has
`44 k_x + 32 m + 48 r + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95` qubits; and
for every input and instance as in `binary_ode_time_solver` with `98304 q* ζ + 3 ζs ≤ ν` it
has the guarantees `NOutcome`, in particular every successful trial is within `ε/500` of
`x(T)/‖x(T)‖` up to a global phase. -/
theorem binary_ode_time_budget_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (q.prep loadC wpC) : ℝ) ≤ prepBoundT q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundT q loadC wpC *
        (c₁ * Real.log ((prepBoundT q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 95 ∧
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
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  have h := pubT_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -⟩ := binary_ode_time_sizes q hq hγ
  obtain ⟨hV, hG, hC, hSG, -, hWC, hWG, -, hcard, hout⟩ :=
    binary_ode_time_solver_trials hS hadj hzt q hq D en hrange hdec loadC hloadV wpC hwpV
  have hq1 := h.one_le_q
  have hℓ := h.ell_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  have hν1 : q.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
      (by linarith [hq.g_ge]) (by linarith [hq.ε_half])
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  have ha : q.params.a = q.kx + 3 := rfl
  have hr2 : q.params.ratio = 2 * q.g := rfl
  -- one native preparation
  have hN : (nGatesN (q.prep loadC wpC) : ℝ) ≤ prepBoundT q loadC wpC := by
    unfold prepBoundT
    have h1 : (nGatesN (q.prep loadC wpC) : ℝ) ≤ ((q.params.prepGates +
        84 * q.params.d * (q.σ + 3) + 6 * q.params.d * (2 * (28 * q.kx + 2) +
          2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC +
          2 * nGatesN wpC : ℕ) : ℝ) := by
      exact_mod_cast hG
    have hP : ((2 ^ q.params.l : ℕ) : ℝ) ≤ 2 * ((q.params.J : ℝ) + 2) := by
      exact_mod_cast q.params.l_bounds.2.le
    have ha' : ((q.params.a : ℕ) : ℝ) = (q.kx : ℝ) + 3 := by rw [ha]; push_cast; ring
    rw [q.params.prepGates_eq] at h1
    generalize q.params.d = d at h1 hd
    generalize 2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) = GC
      at h1 ⊢
    push_cast at h1 hP
    rw [ha'] at h1
    exact prep_budget_arith' _ _ _ _ _ _ _ _ _ _ _ _ _ hq1 hℓ hd hJ hP (by positivity)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)
  refine ⟨hV, hN, ?_, ?_, ?_, ?_⟩
  · -- gates
    have hNS := (Nat.cast_le.mpr hSG).trans (gates_log_le hc₀ hc₁ hlen hη hη1 _ _ hN)
    have hn : Fintype.card q.params.W + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
          q.ar.A) Xa) + q.kx =
        22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + Fintype.card Xa + 47 := by
      rw [card_SX, tnPool, card_XW_SZ4, q.params.card_W, Fintype.card_fin]
      omega
    have hn' : ((Fintype.card q.params.W : ℕ) : ℝ) +
        (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
        (Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
          q.ar.A) Xa) : ℕ) + (q.kx : ℝ) =
        ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + Fintype.card Xa +
          47 : ℕ) : ℝ) := by
      rw [← hn]
      push_cast
      ring
    rw [hn'] at hWG
    have e1 : (40 : ℝ) * q.params.ratio = 80 * q.g := by rw [hr2]; ring
    have e2 : (20 : ℝ) * q.params.ratio = 40 * q.g := by rw [hr2]; ring
    rw [e1, e2] at hWG
    have h80 := mul_le_mul_of_nonneg_left hNS (by positivity : (0 : ℝ) ≤ 80 * q.g)
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
    have hr0 : 0 ≤ q.params.ratio := by
      rw [hr2]
      linarith
    refine (hWC c).trans ((call_budget_arith 40 q.params.ratio _ _ _ _ _ (by norm_num) hr0 hI0
      hd hc).trans (le_of_eq ?_))
    rw [hr2]
    ring
  · -- qubits
    rw [hcard, tnPool, card_XW_SZ4, q.params.card_W, Fintype.card_fin]
    omega
  · -- guarantees
    intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    refine hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp ?_ hR
    have hζ := hq.ζ_pos.le
    have := mul_le_mul_of_nonneg_right hd hζ
    linarith

end Budget

end

end SparseHamiltonian.GateODEBudget
