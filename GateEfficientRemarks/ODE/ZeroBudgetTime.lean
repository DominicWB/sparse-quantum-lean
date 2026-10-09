import GateEfficientRemarks.ODE.ZeroBudget
import ZeroTimeGateODE.BinaryTime

/-!
# Zero time or a known zero generator, time-dependent coefficients: the budgets in `𝔟`

The time-dependent form of `binary_ode_budget_bits_zero` (equations `ode:eq:gate-main` and
`ode:eq:gate-space` of Theorem `ode:thm:gates`, time-dependent part, with its remark on zero time
and a known zero generator): for time-indexed binary data in the zero case
(`ZeroTimeGateODE.BTZeroCase`: `T = 0 ∨ η_H + η_D = 0`), the direct source assembly
`tzprepC loadC wpC` (the weight preparation, the loading circuit and the inverse weight preparation)
on the minimal register `MinW m k_x Zs` (the `m` mesh bits form the source-label word), with the
released ratio `2g`, meets the bounds of `GateBitBudget.binary_ode_time_budget_bits` (`2·10²⁰`,
`3·10¹¹`, internal `q*'` of `(2g, ε/2)`) and of `GateBitBudget.binary_ode_time_budget_bits_user`
(`2·10²²`, `9·10¹²`, the `q*` of `(g, ε)`), both with `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`;
in fact at most `1400 g [q* (𝔟+1) + G_src + |Zs|]` gates (`G_src = |loadC| + 2 |wpC|`) and
`17 (𝔟+1) + 2 |Zs|` qubits, from the explicit counts
`80 g G_src + 40 g (4 (m + k_x + |Zs| + 8) + 3)` and `2 k_x + 2 m + 2 |Zs| + 17`. It makes no call
of a kind that the supplied circuits do not call, and it has the guarantee `GateNative.NOutcome`
against `x(T)` under the zero-case conditions (the energy and accretivity promises of every sample,
circuits within `ζs`, `3 ζs ≤ ν` and the released remaining conditions `PubT.Rest`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open ZeroTimeGateODE (tzprepC BTPublicOK0 BTZeroCase)
open GateBinaryODETime (PubT HsT LsT)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg)
open GateODEBudget (qOf)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct BigOperators

section Time

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` for zero time or a known zero
generator, time-dependent coefficients** (Theorem `ode:thm:gates`, time-dependent part, with its
remark: direct source assembly, no matrix calls).

For time-indexed binary public data with `BTPublicOK0 q` in the zero case, valid loading and
weight-preparation circuits and any `b_data`, the protocol `nprotocol (tzprepC loadC wpC) (2g)` on
the minimal register `MinW m k_x Zs` (`m` the mesh bits): with the internal
`q*' = qOf s T η_H η_D (2g) (ε/2)` and `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`, at most
`2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]` gates and `3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits; with the
`q* = qOf s T η_H η_D g ε` of `(g, ε)` and its `𝔟`, at most `2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]`
gates and `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits, and in fact at most `1400 g [q* (𝔟+1) + G_src + |Zs|]`
gates and `17 (𝔟+1) + 2 |Zs|` qubits (`G_src = |loadC| + 2 |wpC|`); `q* = ℓ = log(10⁴ g/ε)`; the
explicit counts are at most `80 g G_src + 40 g (4 (m + k_x + |Zs| + 8) + 3)` gates and exactly
`2 k_x + 2 m + 2 |Zs| + 17` qubits; the trials are valid; every history makes at most
`80 g (calls_c(loadC) + 2 calls_c(wpC))` calls of every kind `c`, so none of a kind that the
supplied circuits do not call; and for every input with the energy and accretivity promises of
every sample, circuits within `ζs`, `3 ζs ≤ ν` and `PubT.Rest`, the protocol has the guarantee
`NOutcome` against `x(T)`. -/
theorem binary_ode_time_budget_bits_zero (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q)
    (hz : BTZeroCase q) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (MinW q.params.m q.kx Zs) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs ∧
    ((nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      2 * 10 ^ 22 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
            1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (MinW q.params.m q.kx Zs) : ℝ) ≤
      9 * 10 ^ 12 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      1400 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
            1) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (MinW q.params.m q.kx Zs) : ℝ) ≤
      17 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) + 2 * Fintype.card Zs ∧
    qOf q.s q.T q.etaH q.etaD q.g q.ε = ImprovedODEQueryBudget.logBudget q.g q.ε ∧
    ((nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (nGatesN loadC + 2 * nGatesN wpC : ℕ) +
        40 * q.g * (4 * (q.m + q.kx + Fintype.card Zs + 8 : ℕ) + 3) ∧
    Fintype.card (MinW q.params.m q.kx Zs) = 2 * q.kx + 2 * q.m + 2 * Fintype.card Zs + 17 ∧
    (∀ j, ∀ i ∈ trialN (tzprepC loadC wpC :
      List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) j, i.Valid) ∧
    (∀ c : Query → Bool, ((nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      80 * q.g * (nCallsN c loadC + 2 * nCallsN c wpC : ℕ)) ∧
    (∀ c : Query → Bool, nCallsN c loadC = 0 → nCallsN c wpC = 0 →
      (nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) = 0) ∧
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
      3 * ζs ≤ q.params.nu →
      q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax →
      NOutcome (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  have hp := ZeroTimeGateODE.btparams_ok0 hq
  obtain ⟨hV, -, -, hWG, hWC, hno, -, hout⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := Empty) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) q.params
    0 0 0 0 0 0 0 0 0 hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
    (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
  have hr : q.params.ratio = 2 * q.g := rfl
  have hm : q.params.m = q.m := rfl
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hcard : Fintype.card (MinW q.params.m q.kx Zs) =
      2 * q.kx + 2 * q.m + 2 * Fintype.card Zs + 17 := by
    rw [card_MinW, hm]
  have hWG' : ((nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (nGatesN loadC + 2 * nGatesN wpC : ℕ) +
        40 * q.g * (4 * (q.m + q.kx + Fintype.card Zs + 8 : ℕ) + 3) := by
    refine hWG.trans (le_of_eq ?_)
    have hm' : ((q.params.m : ℕ) : ℝ) = q.m := rfl
    rw [card_AW_min, card_XW_min, Fintype.card_fin, hr]
    push_cast
    rw [hm']
    ring
  have hGs0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  -- the linear bounds for every query shape `Q ≥ 1` and word budget `B ≥ k_x + m`
  have hlin : ∀ Q B : ℝ, 1 ≤ Q → (q.kx : ℝ) + q.m ≤ B →
      ((nprotocol (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        1400 * q.g * (Q * (B + 1) + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
          Fintype.card Zs) := by
    intro Q B hQ hB
    refine hWG'.trans ?_
    push_cast
    have hB0 : 0 ≤ B := le_trans (by positivity) hB
    have h1 : B + 1 ≤ Q * (B + 1) := le_mul_of_one_le_left (by linarith) hQ
    have h2 : q.g * (B + 1) ≤ q.g * (Q * (B + 1)) := mul_le_mul_of_nonneg_left h1 hg0
    have h3 : q.g * ((q.kx : ℝ) + q.m) ≤ q.g * B := mul_le_mul_of_nonneg_left hB hg0
    have h4 : 0 ≤ q.g * B := mul_nonneg hg0 hB0
    have h5 : 0 ≤ q.g * ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := mul_nonneg hg0 hGs0
    have h6 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
    nlinarith
  have hspace : ∀ B : ℝ, (q.kx : ℝ) + q.m ≤ B →
      (Fintype.card (MinW q.params.m q.kx Zs) : ℝ) ≤ 17 * (B + 1) + 2 * Fintype.card Zs := by
    intro B hB
    have hB0 : 0 ≤ B := le_trans (by positivity) hB
    rw [hcard]
    push_cast
    linarith
  -- the internal query shape of `(2g, ε/2)`
  have hQ1' : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
      (by linarith [hq.ε_pos]) (by linarith)
  have hQg' : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g := by positivity
  have hw' := kx_add_le_bitB bd q.kx q.m (2 ^ q.m) hQg' hq.ε_pos hε1
  have hB0' := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) hQg' hq.ε_pos hε1
  -- the query shape of `(g, ε)`
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hw := kx_add_le_bitB bd q.kx q.m (2 ^ q.m) hQg hq.ε_pos hε1
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) hQg hq.ε_pos hε1
  refine ⟨lin_le_cube hg0 (by linarith) hB0' hGs0 hZ0 (by norm_num) (by norm_num)
      (hlin _ _ hQ1' hw'),
    lin_le_cube_space hB0' (by norm_num) (by norm_num) (hspace _ hw'),
    lin_le_cube hg0 (by linarith) hB0 hGs0 hZ0 (by norm_num) (by norm_num) (hlin _ _ hQ1 hw),
    lin_le_cube_space hB0 (by norm_num) (by norm_num) (hspace _ hw), hlin _ _ hQ1 hw,
    hspace _ hw, qOf_zero hq.etaH_nonneg hq.etaD_nonneg hz, hWG', hcard, hV, ?_, hno, ?_⟩
  · intro c
    refine (hWC c).trans (le_of_eq ?_)
    rw [hr]
    push_cast
    ring
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    have hI := ZeroTimeGateODE.binary_tzInstanceOK q hq D en x hrH hcH hrD hcD hPSD Jl Wp G bf
      xs bs βG δG βb δb bmax hR
    exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb
      bmax ζs (primsT_isUnitary D en x) hζs hload hwp hbud hI

end Time

end

end SparseHamiltonian.GateRemarks.ODE
