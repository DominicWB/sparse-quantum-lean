import GateEfficientRemarks.ODE.MinRegister
import ZeroTimeGateODE.Binary

/-!
# Zero time or a known zero generator: equations `ode:eq:gate-main`, `ode:eq:gate-space` in `𝔟`

The released library `GateEfficientBitBudget` proves equations `ode:eq:gate-main` and
`ode:eq:gate-space` of Theorem `ode:thm:gates` in the word budget
`𝔟 = b_data + log₂(N+1) + log₂(M+1) + log₂(m_src+1) + log₂((q* g + 1)/ε)` of
`ode:eq:gate-word-budget` for the solvers from binary data, under the released public conditions,
which exclude zero time and a known zero generator; the released library `ZeroTimeGateODE` proves
the remark of `ode:thm:gates` for this zero case with explicit worst-case counts. These are the
absolute-constant forms for the zero case: the direct source assembly on the minimal register
`MinW k k_x Zs` (no simulator, LCHS, private-operation or arithmetic wires), with `𝔟` the `bitB`
of the same public data and `q* = qOf …` (which is `ℓ = log(10⁴ g/ε)` in the zero case,
`qOf_zero`):

* `binary_ode_budget_bits_zero` (constant coefficients, `BZeroCase`: `T = 0 ∨ η_H + η_D = 0`):
  the protocol `nprotocol (zprepC (srcRot T r₀ r_b) srcC) g` on `MinW 0 k_x Zs` uses at most
  `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` gates and has at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits
  (the constants of `GateBitBudget.binary_ode_budget_bits`), for `𝔟` with every time mesh `M` and
  number `m_src` of source nodes (in particular the released `M = 2^m`, `m_src = 2^k` of the
  public data); in fact at most `780 g [q* (𝔟+1) + G_src + |Zs|]` gates and `17 (𝔟+1) + 2 |Zs|`
  qubits, from the explicit counts `40 g (G_src + 2) + 20 g (4 (k_x + |Zs| + 8) + 3)` and
  `2 k_x + 2 |Zs| + 17`; no call of a kind that the source circuits do not call; and the
  guarantee `GateNative.NOutcome` against the solution `x(T)` of `x' = -M̂ x + b` under the
  zero-case conditions.
* `binary_ode_time_budget_bits_zero` (in `ZeroBudgetTime`; time-indexed binary data, `BTZeroCase`):
  the protocol `nprotocol (tzprepC loadC wpC) (2g)` on `MinW m k_x Zs` (`m` the mesh bits) uses at
  most `2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]` gates on at most `3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits
  (internal `q*'` of `(2g, ε/2)`, `GateBitBudget.binary_ode_time_budget_bits`) and at most
  `2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]` gates on at most `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits (the `q*`
  of `(g, ε)`, `GateBitBudget.binary_ode_time_budget_bits_user`); in fact at most
  `1400 g [q* (𝔟+1) + G_src + |Zs|]` gates and `17 (𝔟+1) + 2 |Zs|` qubits; the calls and `NOutcome`
  against `x(T)` as in the zero case of `ZeroTimeGateODE`.

`lin_le_cube`, `lin_le_cube_space` turn the linear bounds into the cubic ones.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open ZeroTimeGateODE (zprepC srcRot BPublicOK0 BZeroCase)
open GateBinaryODE (Pub mLift)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg)
open GateODEBudget (qOf)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### From linear to cubic bounds -/

/-- A gate bound linear in `𝔟 + 1` gives the cubic form of `ode:eq:gate-main`:
`W ≤ c g (Q (B+1) + G + Z)` implies `W ≤ C g (Q (B+1)³ + G + Z)` for `0 ≤ c ≤ C` and nonnegative
data. -/
theorem lin_le_cube {W g Q B G Z c C : ℝ} (hg : 0 ≤ g) (hQ : 0 ≤ Q) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hZ : 0 ≤ Z) (hc : 0 ≤ c) (hcC : c ≤ C) (hW : W ≤ c * g * (Q * (B + 1) + G + Z)) :
    W ≤ C * g * (Q * (B + 1) ^ 3 + G + Z) := by
  have h1 : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have h2 : Q * (B + 1) ≤ Q * (B + 1) ^ 3 := mul_le_mul_of_nonneg_left h1 hQ
  have h3 : c * g * (Q * (B + 1) + G + Z) ≤ c * g * (Q * (B + 1) ^ 3 + G + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hc hg)
  have h4 : 0 ≤ Q * (B + 1) ^ 3 + G + Z := by positivity
  have h5 : c * g * (Q * (B + 1) ^ 3 + G + Z) ≤ C * g * (Q * (B + 1) ^ 3 + G + Z) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcC hg) h4
  linarith

/-- A qubit bound linear in `𝔟 + 1` gives the cubic form of `ode:eq:gate-space`:
`A ≤ c (B+1) + 2 Z` implies `A ≤ C (B+1)³ + 2 Z` for `0 ≤ c ≤ C` and `B ≥ 0`. -/
theorem lin_le_cube_space {A B Z c C : ℝ} (hB : 0 ≤ B) (hc : 0 ≤ c) (hcC : c ≤ C)
    (hA : A ≤ c * (B + 1) + 2 * Z) : A ≤ C * (B + 1) ^ 3 + 2 * Z := by
  have h1 : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  have h2 : c * (B + 1) ≤ c * (B + 1) ^ 3 := mul_le_mul_of_nonneg_left h1 hc
  have h3 : c * (B + 1) ^ 3 ≤ C * (B + 1) ^ 3 :=
    mul_le_mul_of_nonneg_right hcC (by positivity)
  linarith

/-! ### Constant coefficients -/

section Constant

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` for zero time or a known zero
generator, constant coefficients** (Theorem `ode:thm:gates` with its remark: direct source
assembly, no matrix calls).

For binary public data with `BPublicOK0 q` in the zero case `T = 0 ∨ η_H + η_D = 0`, valid source
circuits `srcC`, any `b_data` and any `M`, `m_src`, put `q* = qOf s T η_H η_D g ε` (`= ℓ`) and
`𝔟 = bitB b_data (2^k_x) M m_src q* g ε`. The protocol `nprotocol (zprepC (srcRot T r₀ r_b) srcC) g`
on the minimal register `MinW 0 k_x Zs`: uses at most `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]`
elementary gates in every history (`G_src = |srcC 0| + |srcC 1|`) and has at most
`3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits (the bounds of `GateBitBudget.binary_ode_budget_bits` with the
same constants); in fact at most `780 g [q* (𝔟+1) + G_src + |Zs|]` gates and `17 (𝔟+1) + 2 |Zs|`
qubits; `q* = ℓ = log(10⁴ g/ε)`; the explicit counts are at most
`40 g (G_src + 2) + 20 g (4 (k_x + |Zs| + 8) + 3)` gates and exactly `2 k_x + 2 |Zs| + 17` qubits;
the trials are valid; every history makes at most `40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls
of every kind `c` of the binary sparse oracles, so none of a kind that the source circuits do not
call; and for every input with the row energy promises, unitary source interfaces approximated
by the source circuits within `ζs`, `2 ζs ≤ ν`, the public norms, the seed promises, `x(T) ≠ 0`
and `r₀ + T r_b ≤ g ‖x(T)‖`, the protocol has the guarantee `NOutcome` against the solution
`x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_budget_bits_zero (bd : ℕ) (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (M msrc : ℕ) :
    ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (MinW 0 q.kx Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      780 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) + Fintype.card Zs) ∧
    (Fintype.card (MinW 0 q.kx Zs) : ℝ) ≤
      17 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) +
        2 * Fintype.card Zs ∧
    qOf q.s q.T q.etaH q.etaD q.g q.ε = ImprovedODEQueryBudget.logBudget q.g q.ε ∧
    ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * (nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) +
        20 * q.g * (4 * (q.kx + Fintype.card Zs + 8 : ℕ) + 3) ∧
    Fintype.card (MinW 0 q.kx Zs) = 2 * q.kx + 2 * Fintype.card Zs + 17 ∧
    (∀ j, ∀ i ∈ trialN (zprepC (srcRot q.T q.r₀ q.rb) srcC :
      List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) j, i.Valid) ∧
    (∀ c : Query → Bool, ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.g * (nCallsN c (srcC false) + nCallsN c (srcC true) : ℕ)) ∧
    (∀ c : Query → Bool, nCallsN c (srcC false) = 0 → nCallsN c (srcC true) = 0 →
      (nprotocol (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g hq.g_ge).worstCost
        (wCallN c) = 0) ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, -, -, hWG, hWC, hno, -, hout⟩ := ZeroTimeGateODE.native_ode_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := Empty) (Y := PY q.kx q.b) (J := Query) 0 0 0 0 0 0 0 0 0 0
    q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg
    hq.B_pos srcC hsrcV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hkx := kx_le_bitB bd q.kx M msrc hQg hq.ε_pos hε1
  have hB0 := bitB_nonneg bd (2 ^ q.kx) M msrc hQg hq.ε_pos hε1
  have hcard : Fintype.card (MinW 0 q.kx Zs) = 2 * q.kx + 2 * Fintype.card Zs + 17 := by
    rw [card_MinW]
    ring
  have hWG' : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * (nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) +
        20 * q.g * (4 * (q.kx + Fintype.card Zs + 8 : ℕ) + 3) := by
    refine hWG.trans (le_of_eq ?_)
    rw [card_AW_min, card_XW_min, Fintype.card_fin]
    push_cast
    ring
  generalize hB : bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε = B
    at hkx hB0
  generalize hQ : qOf q.s q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hQg
  have hlin : ((nprotocol (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      780 * q.g * (Q * (B + 1) + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        Fintype.card Zs) := by
    refine hWG'.trans ?_
    push_cast
    have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
    have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
    have h1 : B + 1 ≤ Q * (B + 1) := le_mul_of_one_le_left (by linarith) hQ1
    have h2 : q.g * (B + 1) ≤ q.g * (Q * (B + 1)) := mul_le_mul_of_nonneg_left h1 hg0
    have h3 : q.g * (q.kx : ℝ) ≤ q.g * B := mul_le_mul_of_nonneg_left hkx hg0
    have h4 : 0 ≤ q.g * B := mul_nonneg hg0 hB0
    have h5 : 0 ≤ q.g * ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) :=
      mul_nonneg hg0 hG0
    have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
    nlinarith
  have hspace : (Fintype.card (MinW 0 q.kx Zs) : ℝ) ≤ 17 * (B + 1) + 2 * Fintype.card Zs := by
    rw [hcard]
    push_cast
    linarith
  refine ⟨lin_le_cube hg0 (by linarith) hB0 (by positivity) (Nat.cast_nonneg _) (by norm_num)
      (by norm_num) hlin,
    lin_le_cube_space hB0 (by norm_num) (by norm_num) hspace, hlin, hspace,
    hQ ▸ qOf_zero hq.etaH_nonneg hq.etaD_nonneg hz, hWG', hcard, hV, hWC, hno, ?_⟩
  intro x hrH hrD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hBud
  have ht := ZeroTimeGateODE.binary_target_zero q hq hz D en x hrH hrD x0 v
  rw [ht] at hne hBud ⊢
  have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
  rw [hnu] at hbud
  exact hout (prims (R := ℂ) D en x) Jsrc x0 v ζs (prims_isUnitary D en x) hJ hζs hsrc hbud hx0
    hv hpx hpv hne hBud

end Constant

end

end SparseHamiltonian.GateRemarks.ODE
