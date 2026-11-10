import GateEfficientBinarySelect.BudgetBits
import GateEfficientODEBudget.Synth
import GateEfficientBitBudget.Synth

/-!
# The finite-gate-set budget on branch-dependent meshes

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

Equations `ode:eq:gate-main` and `ode:eq:gate-space` over a finite gate set, with the per-trial
claim of Theorem `ode:thm:gates`, for the solver on branch-dependent meshes from time-indexed
binary data (`binary_select_solver_trials`): the synthesised protocol
`nprotocol (synthPrep hS (ν/3) (prepQ q loadC wpC)) (2g)`, with the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)`.

* `prepBoundB`: the gate bound of one native preparation,
  `B = 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src`, with the per-call gates
  `G_C = 2 (|apG| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` (address program and compute circuit).
* `binary_select_budget_trials`: in `q*` and `B`: at most
  `80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` gates of `𝒢` in every history
  (`n` the tested wires), the calls, the register, and the guarantees `NOutcome` (every successful
  trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase).
* `prepBoundB_le`, `log_factorB_le`, `testedB_le`: `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`,
  `log((B+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src+1)` and the tested register at most `3·10¹¹ (𝔟+1)³`.
* `binary_select_budget_trials_bits`: the finite-gate-set budget in `𝔟`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT gridP)
open SparseHamiltonian.GateSynth SparseHamiltonian.GateSynthTrials
open SparseHamiltonian.GateBitBudget
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes pubT_shapeOK
  gammaOf_le_one prep_budget_arith' call_budget_arith card_SX)
open ImprovedODEQueryBudget (precision logBudget radius)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-- The added work wires of the solver on branch-dependent meshes (the address registers, the
scratch wires `SZ4 k_x b`, the arithmetic wires and three further wires). -/
theorem card_XW_ZB (m kx b bT bP A : ℕ) :
    Fintype.card (XW (ZA m ⊕ SZ4 kx b) bT bP A) =
      (1 + 2 * (2 * m + 14) + (4 * m + 62) * (2 * m + 14)) + (6 * kx + 4 * b) + bT + bP + A +
        3 := by
  simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin, card_ZA]
  ring

/-- **The gate bound of one native preparation on branch-dependent meshes**:
`B = 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src`, with `q*` and `ℓ` for `(2g, ε/2)`,
`G_C = 2 (|apG| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private call and
`G_src = |loadC| + 2 |wpC|`. -/
def prepBoundB {Zs : Type*} (q : PubT)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query)) : ℝ :=
  819400 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (((2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) + 2 * (arQ q).circ.length +
        (2 * (arQ q).bP + (arQ q).bT + 1) : ℕ) : ℝ) +
        q.kx + q.σ + q.params.m + q.params.r +
        logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
    ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The gate, call and qubit budget over a finite gate set, branch-dependent meshes**
(partial formalisation, under this package's format hypotheses, of the finite-set statement of
Theorem `ode:thm:gates`, time-dependent part, equations `ode:eq:gate-main` and
`ode:eq:gate-space` over a finite gate set). Under `Synthesis 𝒢 Xa len` with
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, for the public
data `q` with `γ = gammaOf T η_H η_D (2g) (ε/2)`, `q* = qOf s T η_H η_D (2g) (ε/2)`,
`ℓ = log(1/ν)` and the time-indexed binary data and the valid circuits `loadC`, `wpC` of
`binary_select_solver`, with `B = prepBoundB q loadC wpC`
`= 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src`, `G_src = |loadC| + 2 |wpC|`: every
instruction of every trial of the synthesised protocol
`nprotocol (synthPrep hS (ν/3) (prepQ q loadC wpC)) (2g)` is valid and every gate is a gate of
`𝒢`; one native preparation has at most `B` gates; in every history the synthesised protocol
uses at most `80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` gates of `𝒢`, with
`n = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (|ZA| + bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`, and
at most
`7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times the calls of
`loadC` and twice those of `wpC`; its register has
`44 k_x + 32 m + 48 r + 8 l + 16 b + 4 (|ZA| + bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95`
qubits (`|ZA| = 1 + 2 (2m + 14) + (4m + 62)(2m + 14)` the address registers); and
for every input and instance as in `binary_select_solver` with `98304 q* ζ + 3 ζs ≤ ν` it
has the guarantees `NOutcome`, in particular every successful trial is within `ε/500` of
`x(T)/‖x(T)‖` up to a global phase. -/
theorem binary_select_budget_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (prepQ q loadC wpC) : ℝ) ≤ prepBoundB q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundB q loadC wpC *
        (c₁ * Real.log ((prepBoundB q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 95 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
        (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
        (βG δG κ ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ →
      NOutcome (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  have h := pubT_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -⟩ := binary_ode_time_sizes q hq hγ
  obtain ⟨hV, hG, hC, hSG, -, hWC, hWG, -, hcard, hout⟩ :=
    binary_select_solver_trials hS hadj hzt q hq D en hrange hdec loadC hloadV wpC hwpV
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
  have hN : (nGatesN (prepQ q loadC wpC) : ℝ) ≤ prepBoundB q loadC wpC := by
    unfold prepBoundB
    have h1 : (nGatesN (prepQ q loadC wpC) : ℝ) ≤ ((q.params.prepGates +
        84 * q.params.d * (q.σ + 3) + 6 * q.params.d *
          (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
          2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) + nGatesN loadC +
          2 * nGatesN wpC : ℕ) : ℝ) := by
      exact_mod_cast hG
    have hP : ((2 ^ q.params.l : ℕ) : ℝ) ≤ 2 * ((q.params.J : ℝ) + 2) := by
      exact_mod_cast q.params.l_bounds.2.le
    have ha' : ((q.params.a : ℕ) : ℝ) = (q.kx : ℝ) + 3 := by rw [ha]; push_cast; ring
    rw [q.params.prepGates_eq] at h1
    generalize q.params.d = d at h1 hd
    generalize 2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) = GC at h1 ⊢
    push_cast at h1 hP
    rw [ha'] at h1
    exact prep_budget_arith' _ _ _ _ _ _ _ _ _ _ _ _ _ hq1 hℓ hd hJ hP (by positivity)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith)
  refine ⟨hV, hN, ?_, ?_, ?_, ?_⟩
  · -- gates
    have hNS := (Nat.cast_le.mpr hSG).trans (gates_log_le hc₀ hc₁ hlen hη hη1 _ _ hN)
    have hn : Fintype.card q.params.W +
        Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) +
        Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
          (arQ q).bP (arQ q).A) Xa) + q.kx =
        22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 2 * Fintype.card Zs + Fintype.card Xa + 47 := by
      rw [card_SX, tnPool, card_XW_ZB, q.params.card_W, Fintype.card_fin]
      generalize 1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14) = Z
      omega
    have hn' : ((Fintype.card q.params.W : ℕ) : ℝ) +
        (Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) : ℕ) +
        (Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
          (arQ q).bP (arQ q).A) Xa) : ℕ) + (q.kx : ℝ) =
        ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
          2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 2 * Fintype.card Zs + Fintype.card Xa +
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
    have hc : (nCallsN c (prepQ q loadC wpC) : ℝ) ≤ 12 * (q.params.d : ℝ) *
        (2 * ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0)
          + (if c Query.value then 1 else 0))) +
        ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC) := by
      have h1 : (nCallsN c (prepQ q loadC wpC) : ℝ) ≤ ((12 * q.params.d *
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
    rw [hcard, tnPool, card_XW_ZB, q.params.card_W, Fintype.card_fin]
    generalize 1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14) = Z
    omega
  · -- guarantees
    intro x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp hbud hR
    refine hout x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp ?_ hR
    have hζ := hq.ζ_pos.le
    have := mul_le_mul_of_nonneg_right hd hζ
    linarith

end Budget

section Words

/-- **The preparation bound in `𝔟`** (time-dependent coefficients): under the hypotheses of
`binary_select_budget_bits`, `prepBoundB q loadC wpC ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`,
`G_src = |loadC| + 2 |wpC|`. -/
theorem prepBoundB_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) {Zs : Type*}
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query)) :
    prepBoundB q loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
  have h := pubT_shapeOK q hq
  have hw := wordsB_le bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨hGC, -, -, -⟩ := binary_select_arith_words q
  have hℓ := h.ell_ge
  have hQ1 := h.one_le_q
  have hσ := q.hσ
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith [hq.g_ge])) hq.ε_pos hε1
  have hw0 : (0 : ℝ) ≤ wordsB q := Nat.cast_nonneg _
  have hGC' : (((2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) :
      ℕ) : ℝ)) ≤ 65536 * ((wordsB q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
  have hS : (q.kx : ℝ) + q.σ + q.params.m + q.params.r ≤ 2 * (wordsB q : ℝ) := by
    have : q.kx + q.σ + q.params.m + q.params.r ≤ 2 * wordsB q := by
      unfold wordsB
      omega
    exact_mod_cast this
  have hl : (q.params.l : ℝ) ≤ wordsB q := by
    have : q.params.l ≤ wordsB q := by
      unfold wordsB
      omega
    exact_mod_cast this
  have hin := inner_le hw0 hℓ hGC' hS (Nat.cast_nonneg _) hl
  have hcube := cube_le (by linarith) hB0 hw
  have hY := one_le_pow₀
    (by linarith : (1 : ℝ) ≤ (wordsB q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) (n := 3)
  unfold prepBoundB
  have hQ0 : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := by linarith
  have h1 : (((2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) : ℕ) :
      ℝ) + q.kx + q.σ + q.params.m + q.params.r +
      logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) ≤
      65547 * ((300 + 1) ^ 3 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 819400 *
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
  have hY2 : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
  linarith

/-- **The synthesis factor in `𝔟`** (time-dependent coefficients): under the hypotheses of
`binary_select_budget_bits`, `log((B+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src+1)` for
`B = prepBoundB q loadC wpC`. -/
theorem log_factorB_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) {Zs : Type*}
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hB0 : 0 ≤ prepBoundB q loadC wpC) :
    Real.log ((prepBoundB q loadC wpC + 1) / (q.params.nu / 3)) ≤
      64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) +
      Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1) := by
  have h := pubT_shapeOK q hq
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 := h.one_le_q
  have hX := shape_one_le_X h
  have hQX := shape_q_le_X h
  have hνX : 1 / q.params.nu ≤ 10000 *
      ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * (2 * q.g) + 1) / (q.ε / 2)) :=
    shape_inv_precision_le h
  have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
  have hB0' : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith) (by linarith [hq.g_ge])) hq.ε_pos hε1
  have hP : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 :=
    one_le_mul_of_one_le_of_one_le hQ1 (one_le_pow₀ (by linarith))
  have hBp := prepBoundB_le bd q hq hγ hζ hb hc0 hT hH hD loadC wpC
  have hBp' : prepBoundB q loadC wpC ≤ 2 * 10 ^ 18 *
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3) +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) :=
    hBp.trans (le_of_eq (by ring))
  have h1 := log_prep_le hB0 hBp' hP (by positivity) hν
  have h2 := log_q_cube_le (by linarith) hQX hX hB0'
  have h3 := log_three_div_le hν hX hνX
  have hLL := logb_X_two_le (Q := qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) (g := q.g)
    (by linarith) (by linarith [hq.g_ge]) hq.ε_pos hε1
  have hL : Real.logb 2 ((qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g + 1) / q.ε) ≤
      bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε := by
    have h4 := logb_succ_nonneg (2 ^ q.kx)
    have h5 := logb_succ_nonneg (2 ^ q.m)
    have h7 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    unfold bitB
    linarith
  linarith

/-- **The tested register in `𝔟`** (branch-dependent meshes): under the hypotheses of
`binary_select_budget_bits`, the native part `22 k_x + 16 m + 24 r + 4 l + 8 b +
2 (|ZA| + bT + bP + A_arith) + 47` of the register tested by the zero tests is at most
`3·10¹¹ (𝔟+1)³`. -/
theorem testedB_le (bd : ℕ) (q : PubT) (hq : q.OK)
    (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD) :
    ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 47 : ℕ) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by
  have h := pubT_shapeOK q hq
  have hw := wordsB_le bd q hq hγ hζ hb hc0 hT hH hD
  obtain ⟨-, hA, hT', hP'⟩ := binary_select_arith_words q
  have hσ := q.hσ
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hℓ := h.ell_ge
  have hB0 : 0 ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε :=
    bitB_nonneg _ _ _ _ (mul_nonneg (by linarith [h.one_le_q]) (by linarith [hq.g_ge]))
      hq.ε_pos hε1
  have h24 : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b ≤
      24 * wordsB q := by
    unfold wordsB
    omega
  have hp1 : wordsB q + 1 ≤ (wordsB q + 1) ^ 3 := le_self_pow₀ (by omega) (by norm_num)
  have hn : 22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
      2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 47 ≤ 8283 * (wordsB q + 1) ^ 3 := by
    generalize (wordsB q + 1) ^ 3 = W at hA hp1 ⊢
    generalize 1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14) = Z at hA ⊢
    omega
  have hn' : ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
      2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 47 : ℕ) : ℝ) ≤ 8283 * ((wordsB q : ℝ) + 1) ^ 3 := by
    exact_mod_cast hn
  have hcube := cube_le (Nat.cast_nonneg (wordsB q)) hB0 (c := 300) (by linarith)
  have hY : 0 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
  linarith

end Words

section BudgetBits

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set,
branch-dependent meshes** (partial formalisation, under this package's format hypotheses, of the
finite-set statement of Theorem `ode:thm:gates`, time-dependent part, with
the branch-dependent meshes of Lemma `ode:lem:gate-select`). Under the synthesis hypotheses of
`GateBitBudget.binary_ode_time_budget_trials_bits` (`c₀, c₁ ≥ 0` the synthesis constants, not
the decoder scale `c₀`) and the hypotheses of `binary_select_budget_bits`, with
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` (`q* = qOf s T η_H η_D (2g) (ε/2)`) and
`G_src = |loadC| + 2 |wpC|`: the native preparation bound is
`B = prepBoundB q loadC wpC ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`; in every history the synthesised
protocol (ratio `2g`) uses at most
`80 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
40 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; its register has at most
`7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; and every conclusion of
`binary_select_budget_trials` holds (with `98304 q* ζ + 3 ζs ≤ ν` for the
guarantees `NOutcome`). -/
theorem binary_select_budget_trials_bits (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    prepBoundB q loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)) *
        (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) +
          Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1)) + c₀)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (prepQ q loadC wpC) : ℝ) ≤ prepBoundB q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundB q loadC wpC *
        (c₁ * Real.log ((prepBoundB q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (arQ q).bT +
          (arQ q).bP + (arQ q).A) + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 95 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
        (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
        (βG δG κ ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ →
      NOutcome (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨hV, hN, hWG, hC, hcard, hout⟩ :=
    binary_select_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq hγ D en hrange hdec loadC hloadV
      wpC hwpV
  have hBp := prepBoundB_le bd q hq hγ hζ hb hc0 hT hH hD loadC wpC
  have hB0 : 0 ≤ prepBoundB q loadC wpC := le_trans (Nat.cast_nonneg _) hN
  have hlog := log_factorB_le bd q hq hγ hζ hb hc0 hT hH hD loadC wpC hB0
  have hn := testedB_le bd q hq hγ hζ hb hc0 hT hH hD
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hY : 1 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by
    have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
    have := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (mul_nonneg (le_trans zero_le_one (GateODEBudget.pubT_shapeOK q hq).one_le_q) hg0)
      hq.ε_pos hε1
    exact one_le_pow₀ (by linarith)
  refine ⟨hBp, ?_, ?_, hV, hN, hWG, hC, hcard, hout⟩
  · refine hWG.trans (synth_arith (by norm_num) (by norm_num) hg0 hB0 hBp ?_ hlog hc₀ hc₁ ?_)
    · apply Real.log_nonneg
      have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
      have hν1 : q.params.nu ≤ 1 :=
        (ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
          (by linarith [hq.g_ge]) (by linarith [hq.ε_half])).trans (by norm_num)
      rw [le_div_iff₀ (by positivity)]
      linarith
    · push_cast at hn ⊢
      linarith
  · rw [hcard]
    push_cast at hn hY ⊢
    linarith

end BudgetBits

end

end SparseHamiltonian.GateBinarySelect
