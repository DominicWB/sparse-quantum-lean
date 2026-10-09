import GateEfficientODEBudget.Shape
import GateEfficientBinaryODE.Solver

/-!
# The budget of the dissipative solver from binary data, constant coefficients

For the public data `q : GateBinaryODE.Pub` of the solver from binary sparse data, put
`ℓ = log(10000 g/ε) = log(1/ν)`, `Θ = T η_H + T η_D ℓ` and `q* = √s Θ + √(s Θ ℓ) + ℓ`
(`qOf`, equation `ode:eq:gate-q`). The public rescaling is `γ = gammaOf T η_H η_D g ε =
min(1, √(Θ/ℓ))`, a function of `T`, `η_H`, `η_D`, `g` and `ε` alone, chosen before the binary
data, the input, the source circuits and the instance.

* `binary_ode_sizes`: with this `γ`, the released public sizes satisfy `τ ≤ 16 q*`,
  `d ≤ 4096 q*`, `2^m < 2 (2 + 64 q* + √(12288 q*³/ν))`, `2^r ≤ 4 (4096 q* + 1)`,
  `J ≤ 60 q* ℓ`, `2^l < 2 (60 q* ℓ + 2)` and `2^k < 2 (2 q*/ν + 2)` (`k` the quadrature bits):
  the degree is `O(q*)` and the register words are logarithmic.
* `binary_ode_budget`: for valid source circuits, in every history the native protocol uses at
  most `36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` elementary gates
  (`G_C` the gates of one private call, `G_src` the gates of the source circuits, `A` the
  system, source-scratch, private-scratch and arithmetic wires), at most `3932160 g q*` calls of
  each matrix oracle besides `40 g` times the calls of the source circuits, its register has
  `22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47` qubits, and with
  the arithmetic budget `98304 q* ζ + 2 ζs ≤ ν` (in place of `24 d ζ + 2 ζs ≤ ν`) it has the
  guarantees of `GateBinaryODE.binary_ode_solver`.

This is equation `ode:eq:gate-main` before finite-gate-set synthesis, with `C = 36873000`, the
per-call cost `G_C` and the logarithmic register words explicit, and equation `ode:eq:gate-space`
with `C = 2`, `A_src = |Zs|`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateODEBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open ImprovedODEQueryBudget (precision logBudget radius)
open CayleyClockInterface (width moment)
open GateCircuit.Sim (simM_spec simR_spec)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-- The public conditions of the solver from binary data give those of the size bounds. -/
theorem pub_shapeOK (q : Pub) (hq : q.OK) :
    ShapeOK (q.s : ℝ) q.T q.etaH q.etaD q.g q.ε where
  s_ge := by exact_mod_cast Nat.one_le_two_pow
  T_pos := hq.T_pos
  etaH_nonneg := hq.etaH_nonneg
  etaD_nonneg := hq.etaD_nonneg
  eta_pos := hq.eta_pos
  g_ge := hq.g_ge
  ε_pos := hq.ε_pos
  ε_le := hq.ε_half.trans (by norm_num)

/-- **The public sizes of the solver from binary data with the public rescaling**
(Theorem `ode:thm:gates`, the sizes behind equation `ode:eq:gate-main`). For the public data
`q` with `γ = gammaOf T η_H η_D g ε` and `q* = qOf s T η_H η_D g ε`, `ℓ = log(1/ν)`: the common
simulation time is `τ ≤ 16 q*`, the filter degree `d ≤ 4096 q*`, the simulator words satisfy
`2^m < 2 (2 + 64 q* + √(12288 q*³/ν))` and `2^r ≤ 4 (4096 q* + 1)`, the LCHS grid has
`J ≤ 60 q* ℓ` labels on `l` wires with `2^l < 2 (60 q* ℓ + 2)`, and the quadrature register has
`2^k < 2 (2 q*/ν + 2)`. -/
theorem binary_ode_sizes (q : Pub) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε) :
    q.params.tau ≤ 16 * qOf q.s q.T q.etaH q.etaD q.g q.ε ∧
    (q.params.d : ℝ) ≤ 4096 * qOf q.s q.T q.etaH q.etaD q.g q.ε ∧
    ((2 ^ q.params.m : ℕ) : ℝ) < 2 * (2 + 64 * qOf q.s q.T q.etaH q.etaD q.g q.ε +
      Real.sqrt (12288 * qOf q.s q.T q.etaH q.etaD q.g q.ε ^ 3 / q.params.nu)) ∧
    ((2 ^ q.params.r : ℕ) : ℝ) ≤ 4 * (4096 * qOf q.s q.T q.etaH q.etaD q.g q.ε + 1) ∧
    (q.params.J : ℝ) ≤ 60 * qOf q.s q.T q.etaH q.etaD q.g q.ε * logBudget q.g q.ε ∧
    ((2 ^ q.params.l : ℕ) : ℝ) <
      2 * (60 * qOf q.s q.T q.etaH q.etaD q.g q.ε * logBudget q.g q.ε + 2) ∧
    ((2 ^ q.params.k : ℕ) : ℝ) < 2 * (2 * qOf q.s q.T q.etaH q.etaD q.g q.ε / q.params.nu + 2) := by
  have h := pub_shapeOK q hq
  have hp := q.params_ok hq
  have hν := hp.nu_pos
  -- the common simulation time
  have hτ : q.params.tau ≤ 16 * qOf q.s q.T q.etaH q.etaD q.g q.ε := by
    have e : q.params.tau = q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ +
        radius q.g q.ε * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ)) := rfl
    rw [e, hγ]
    exact h.tau_le
  have hτ0 : 0 ≤ q.params.tau := hp.tau_pos.le
  -- the degree
  have hd : (q.params.d : ℝ) ≤ 4096 * qOf q.s q.T q.etaH q.etaD q.g q.ε := by
    have hdeg := q.params.degree_bound hp
    change (q.params.d : ℝ) ≤ 128 * (q.params.tau * moment q.γ +
      width (4 * (q.s : ℝ)) q.γ * (1 + Real.log (3 / precision q.g q.ε))) at hdeg
    rw [hγ] at hdeg
    exact hdeg.trans (h.degree_shape_le _ hτ0 hτ)
  obtain ⟨-, hm, -, hr⟩ := q.params.sim_sizes
  refine ⟨hτ, hd, ?_, ?_, ?_, ?_, ?_⟩
  · -- the time word
    have hm' : ((2 ^ q.params.m : ℕ) : ℝ) < 2 * (TimeSchedule.steps q.params.tau
        (q.params.nu / 3) : ℝ) := by exact_mod_cast hm
    have hs := steps_le q.params.tau _ q.params.nu hτ0 hτ hν
    linarith
  · -- the reuse word
    have hr' : ((2 ^ q.params.r : ℕ) : ℝ) ≤ 4 * ((q.params.d : ℝ) + 1) := by exact_mod_cast hr
    linarith
  · -- the LCHS grid
    have hJ := q.params.J_le hp
    change (q.params.J : ℝ) ≤ radius q.g q.ε * (q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) +
      2 * Real.log (512 / precision q.g q.ε)) / Real.pi + 3 at hJ
    rw [hγ] at hJ
    exact hJ.trans h.grid_le
  · -- the LCHS word
    have hJ := q.params.J_le hp
    change (q.params.J : ℝ) ≤ radius q.g q.ε * (q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) +
      2 * Real.log (512 / precision q.g q.ε)) / Real.pi + 3 at hJ
    rw [hγ] at hJ
    have hl : ((2 ^ q.params.l : ℕ) : ℝ) < 2 * ((q.params.J : ℝ) + 2) := by
      exact_mod_cast q.params.l_bounds.2
    linarith [h.grid_le]
  · -- the quadrature word
    obtain ⟨-, hk⟩ := q.params.k_bounds hν
    have hk' : ((2 ^ q.params.k : ℕ) : ℝ) <
        2 * ((⌈q.params.T * (q.params.lamH + q.params.lamD) / q.params.nu⌉₊ : ℕ) + 1 : ℝ) := by
      exact_mod_cast hk
    have hlam : q.params.T * (q.params.lamH + q.params.lamD) ≤
        2 * qOf q.s q.T q.etaH q.etaD q.g q.ε := by
      have e : q.params.T * (q.params.lamH + q.params.lamD) =
          q.T * (Real.sqrt (4 * (q.s : ℝ)) * q.etaH / q.γ +
            Real.sqrt (4 * (q.s : ℝ)) * q.etaD / q.γ) := rfl
      rw [e, hγ]
      exact h.lam_le
    have hx0 : 0 ≤ q.params.T * (q.params.lamH + q.params.lamD) / q.params.nu :=
      div_nonneg (mul_nonneg hp.T_pos.le (add_nonneg hp.lamH_nonneg hp.lamD_nonneg)) hν.le
    have hc := Nat.ceil_lt_add_one hx0
    have hdiv : q.params.T * (q.params.lamH + q.params.lamD) / q.params.nu ≤
        2 * qOf q.s q.T q.etaH q.etaD q.g q.ε / q.params.nu :=
      div_le_div_of_nonneg_right hlam hν.le
    linarith

/-! ### Arithmetic of the budget -/

/-- The arithmetic of the gate budget: `d ≤ 4096 q*`, `J ≤ 60 q* ℓ`. -/
theorem gate_budget_arith (c g Q ℓ d J k l Xs Gs Aw : ℝ) (hc : 0 ≤ c) (hg : 0 ≤ g) (hQ : 1 ≤ Q)
    (hℓ : 1 ≤ ℓ) (hd : d ≤ 4096 * Q) (hJ : J ≤ 60 * Q * ℓ) (hk : 0 ≤ k) (hl : 0 ≤ l)
    (hXs : 0 ≤ Xs) (hGs : 0 ≤ Gs) (hAw : 0 ≤ Aw) :
    c * g * ((d + 1) * Xs + (k + 1) + (J + 2) * (l + 1) + Gs + Aw) ≤
      4097 * c * g * (Q * (Xs + k + 1 + ℓ * (l + 1)) + Gs + Aw) := by
  have h1 : (d + 1) * Xs ≤ 4097 * Q * Xs := mul_le_mul_of_nonneg_right (by linarith) hXs
  have hQℓ : 1 ≤ Q * ℓ := by nlinarith
  have h2 : (J + 2) * (l + 1) ≤ 4097 * Q * ℓ * (l + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h3 : k + 1 ≤ 4097 * Q * (k + 1) := by nlinarith
  have hB : (d + 1) * Xs + (k + 1) + (J + 2) * (l + 1) + Gs + Aw ≤
      4097 * (Q * (Xs + k + 1 + ℓ * (l + 1)) + Gs + Aw) := by
    nlinarith
  calc c * g * ((d + 1) * Xs + (k + 1) + (J + 2) * (l + 1) + Gs + Aw)
      ≤ c * g * (4097 * (Q * (Xs + k + 1 + ℓ * (l + 1)) + Gs + Aw)) :=
        mul_le_mul_of_nonneg_left hB (mul_nonneg hc hg)
    _ = 4097 * c * g * (Q * (Xs + k + 1 + ℓ * (l + 1)) + Gs + Aw) := by ring

/-- The arithmetic of the gate budget without the quadrature register. -/
theorem gate_budget_arith' (c g Q ℓ d J l Xs Gs Aw : ℝ) (hc : 0 ≤ c) (hg : 0 ≤ g) (hQ : 1 ≤ Q)
    (hℓ : 1 ≤ ℓ) (hd : d ≤ 4096 * Q) (hJ : J ≤ 60 * Q * ℓ) (hl : 0 ≤ l)
    (hXs : 0 ≤ Xs) (hGs : 0 ≤ Gs) (hAw : 0 ≤ Aw) :
    c * g * ((d + 1) * Xs + (J + 2) * (l + 1) + Gs + Aw) ≤
      4097 * c * g * (Q * (Xs + 1 + ℓ * (l + 1)) + Gs + Aw) := by
  have h := gate_budget_arith c g Q ℓ d J 0 l Xs Gs Aw hc hg hQ hℓ hd hJ le_rfl hl hXs hGs hAw
  have hcg : 0 ≤ c * g := mul_nonneg hc hg
  have h1 : c * g * ((d + 1) * Xs + (J + 2) * (l + 1) + Gs + Aw) ≤
      c * g * ((d + 1) * Xs + (0 + 1) + (J + 2) * (l + 1) + Gs + Aw) :=
    mul_le_mul_of_nonneg_left (by linarith) hcg
  have e : 4097 * c * g * (Q * (Xs + 0 + 1 + ℓ * (l + 1)) + Gs + Aw) =
      4097 * c * g * (Q * (Xs + 1 + ℓ * (l + 1)) + Gs + Aw) := by ring
  linarith

/-- The arithmetic of the call budget: `d ≤ 4096 q*`. -/
theorem call_budget_arith (c g Q d I S N : ℝ) (hc : 0 ≤ c) (hg : 0 ≤ g) (hI : 0 ≤ I)
    (hd : d ≤ 4096 * Q) (hN : N ≤ 12 * d * (2 * I) + S) :
    c * g * N ≤ 98304 * c * g * Q * I + c * g * S := by
  have h1 := mul_le_mul_of_nonneg_left hd (mul_nonneg (mul_nonneg hc hg) hI)
  have h2 := mul_le_mul_of_nonneg_left hN (mul_nonneg hc hg)
  nlinarith

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The gate, call and qubit budget of the solver from binary data with the public rescaling**
(Theorem `ode:thm:gates`, constant coefficients, equations `ode:eq:gate-main` and
`ode:eq:gate-space` before finite-gate-set synthesis). Let the public data `q` have
`γ = gammaOf T η_H η_D g ε`, and put `q* = qOf s T η_H η_D g ε`, `ℓ = log(1/ν)`. For the binary
data and the valid source circuits `srcC` of `binary_ode_solver`, in every history the native
protocol `nprotocol (q.prep srcC) g`

* uses at most `36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` elementary
  gates, `G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private call,
  `G_src = |srcC 0| + |srcC 1|` and `A = k_x + |Zs| + (6 k_x + 4 b) + bT + bP + A_arith`;
* makes at most `3932160 g q*` calls of each matrix oracle besides `40 g` times the calls of the
  source circuits;

its register has `22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`
qubits; and for every input and instance as in `binary_ode_solver`, with the arithmetic budget
`98304 q* ζ + 2 ζs ≤ ν`, it has the guarantees `NOutcome`. The words `m`, `r`, `l`, `k` and the
degree are bounded in `binary_ode_sizes`. -/
theorem binary_ode_budget (q : Pub) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      36873000 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r + q.params.k +
            logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) ∧
    (∀ c : Query → Bool, ((nprotocol (q.prep srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      3932160 * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 ∧
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
      NOutcome (q.prep srcC) q.g q.ε hq.g_ge (prims (R := ℂ) D en x)
        (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  have h := pub_shapeOK q hq
  obtain ⟨-, hd, -, -, hJ, -, -⟩ := binary_ode_sizes q hq hγ
  have hq1 := h.one_le_q
  have hℓ := h.ell_ge
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- gates
    refine (binary_ode_gate_count q hq srcC hsrcV).trans
      ((gate_budget_arith 9000 q.g _ _ _ _ _ _ _ _ _ (by norm_num) hg0 hq1 hℓ hd hJ
        (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by positivity) (by positivity)
        (by positivity)).trans (le_of_eq ?_))
    push_cast
    ring
  · -- calls
    intro c
    obtain ⟨-, -, hC, -, hWC, -⟩ := binary_ode_counts q hq srcC hsrcV
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
    obtain ⟨-, -, -, -, -, hcard⟩ := binary_ode_counts q hq srcC hsrcV
    rw [hcard, q.params.card_W]
    show q.kx + 2 * (4 * (q.kx + 3) + 6 * q.params.m + 12 * q.params.r + 2 * q.params.k +
      2 * q.params.l + 8 + (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) +
      Fintype.card Zs) + q.kx + 1 = _
    ring
  · -- guarantees
    obtain ⟨-, -, -, -, -, -, hout⟩ := binary_ode_solver q hq D en hrange hdec srcC hsrcV
    intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJs hζs hsrc hbud hx0 hv hpx hpv hne hB
    refine hout x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJs hζs hsrc ?_ hx0 hv hpx hpv hne hB
    have hζ := hq.ζ_pos.le
    have := mul_le_mul_of_nonneg_right hd hζ
    linarith

end Budget

end

end SparseHamiltonian.GateODEBudget
