import GateEfficientNative.Hamiltonian.Theorem
import GateEfficientNative.ODE.Time

/-!
# Explicit and polynomial gate counts

* `simCircuit_counts`, `nativeSim_counts`: the counts of the released and of
  the native constant-Hamiltonian circuits depend only on the public data.
* `native_sparse_counts` (equation `hs:eq:gate-binary`): for sparsity `s`,
  norm bound `η`, time `t` and `q = √s ηt + √(s ηt log(1/ε)) + log(1/ε)`, the
  released precision budget chooses the clock parameters so that the filter
  degree is at most `4608 q`; the native circuit then makes at most `55296 q`
  times the primitive calls of `V` and uses at most
  `200 (4608 q + 1) (G_C + C_J + a + m + r + 1)` elementary gates, where the
  simulator words satisfy `2^m < 2 (2 + 4τ + √(6τ³/ε))` with `τ ≤ √s q` and
  `2^r ≤ 4 (4608 q + 1)`. With per-call costs `G_C + C_J + a` polynomial in
  the data bit length, `log (N+1)` and `log (1/ζ)`, this is the paper's
  `Q_base · poly(b_data, log (N+1), log ((Q_base+1)/ε))` with `Q_base = q` (using
  `s ≤ N` and `ζ = ε/(48d)`).
* `native_ode_gate_count`, `native_ode_time_gate_count` (the explicit counts
  underlying equation `ode:eq:gate-main`): the worst-case gate counts of the
  native ODE protocols are at most
  `C g [(d+1)(a+m+r+1+C_J+G_C) + (k+1) + (J+2)(l+1) + G_src + A]`
  with `C = 9000` (constant coefficients) and `C = 18000` (time-dependent),
  where `G_C` is the gate count of one native private call, `G_src` the gate
  count of the source circuits, and `A` the system, source-scratch, private
  scratch and arithmetic wires; the public sizes `d`, `m`, `r`, `l` and `J` are
  bounded by the released size lemmas (for example
  `GateODE.Params.degree_bound`, `GateODE.Params.sim_sizes`,
  `GateODE.Params.l_bounds`, `GateODE.Params.J_le_log`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct BigOperators

/-! ### Hamiltonian simulation -/

section Hamiltonian

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]

/-- The counts of the released circuit, from the public data alone. -/
theorem simCircuit_counts (a : ℕ) (τ Q qbar ε : ℝ) :
    nPriv (simCircuit a τ Q qbar ε) = 6 * fDeg Q τ qbar ε ∧
    nUJ (simCircuit a τ Q qbar ε) = 12 * fDeg Q τ qbar ε ∧
    nGates (simCircuit a τ Q qbar ε) ≤
      200 * (fDeg Q τ qbar ε + 1) * (a + simM τ ε + simR Q τ qbar ε + 1) := by
  obtain ⟨hr1, _, hr2⟩ := simR_spec Q τ qbar ε
  have hN : 2 * fDeg Q τ qbar ε ≤ cap (simR Q τ qbar ε) + 1 := by
    have := cap_succ (simR Q τ qbar ε)
    omega
  obtain ⟨hc1, hc2, hc3⟩ := ampI_counts (a := a) (m := simM τ ε) (K := simK a Q τ qbar ε)
    (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ (simM τ ε)))
    (CayleyTransfer.sigma (stepW τ (simM τ ε))) (2 * fDeg Q τ qbar ε) hN
  have hgb := gate_bound a (simM τ ε) (simR Q τ qbar ε) (fDeg Q τ qbar ε) (2 ^ simR Q τ qbar ε) hr2
  refine ⟨?_, ?_, ?_⟩
  · unfold simCircuit; rw [hc1]; ring
  · unfold simCircuit; rw [hc2]; ring
  · unfold simCircuit
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- **The counts of the native circuit**, from the public data alone: exactly
`12 d` times the primitive calls of `V`, and at most
`200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C` elementary gates. -/
theorem nativeSim_counts (a : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (hUJg : ∀ g ∈ UJg, GateOK 3 g) (nd : NativeOp Empty (Fin a ⊕ S) Z Y J)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) :
    (∀ p : J → Bool, nCallsN p (nativeSim a τ Q qbar ε UJg nd ar) =
      12 * fDeg Q τ qbar (ε / 2) * nCallsN p nd.V) ∧
    nGatesN (nativeSim a τ Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
        84 * fDeg Q τ qbar (ε / 2) * UJg.length + 6 * fDeg Q τ qbar (ε / 2) * privGates nd ar := by
  obtain ⟨hP, hJ, hG⟩ := simCircuit_counts a τ Q qbar (ε / 2)
  refine ⟨fun p => ?_, ?_⟩
  · rw [nativeSim, hcirc_nCalls, hP]
    ring
  · refine (hcirc_nGates (wireRel _ _ _ _) (noSel _) UJg hUJg nd ar _).trans ?_
    rw [hP, hJ, mul_one]
    have h84 : 12 * fDeg Q τ qbar (ε / 2) * (7 * UJg.length) =
        84 * fDeg Q τ qbar (ε / 2) * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right (Nat.add_le_add_right hG _) _

/-- The simulator word `m` is logarithmic: `2^m < 2 (2 + 4τ + √(6τ³/ε))`. -/
theorem pow_simM_lt (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ((2 ^ simM τ (ε / 2) : ℕ) : ℝ) < 2 * (2 + 4 * τ + Real.sqrt (6 * τ ^ 3 / ε)) := by
  have h1 : ((2 ^ simM τ (ε / 2) : ℕ) : ℝ) < 2 * (TimeSchedule.steps τ (ε / 2 / 3) : ℝ) := by
    exact_mod_cast (simM_spec τ (ε / 2)).2
  have hth0 : 0 ≤ TimeSchedule.threshold τ (ε / 2 / 3) :=
    (by positivity : (0 : ℝ) ≤ 4 * τ).trans (le_max_left _ _)
  have e : τ ^ 3 / (ε / 2 / 3) = 6 * τ ^ 3 / ε := by
    field_simp
    ring
  have hmax : TimeSchedule.threshold τ (ε / 2 / 3) ≤ 4 * τ + Real.sqrt (6 * τ ^ 3 / ε) := by
    unfold TimeSchedule.threshold
    rw [e]
    exact max_le (le_add_of_nonneg_right (Real.sqrt_nonneg _))
      (le_add_of_nonneg_left (by positivity))
  have hc := Nat.ceil_lt_add_one hth0
  have hsteps : (TimeSchedule.steps τ (ε / 2 / 3) : ℝ) ≤ 2 + 4 * τ + Real.sqrt (6 * τ ^ 3 / ε) := by
    unfold TimeSchedule.steps
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  linarith

omit [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
/-- **The sparse form of the gate count** (equation `hs:eq:gate-binary`). For
sparsity `s ≥ 1`, row and column norm bound `η ≥ 0`, time `t ≥ 0` and
`0 < ε ≤ 1/2`, put `q = √s ηt + √(s ηt log(1/ε)) + log(1/ε)`
(`ImprovedPrecisionBudget.shape`). The released precision budget chooses
`γ ∈ (0, 1]` with `γ √s ≥ 1` such that, for the clock parameters
`Q = ⌈max(1, γ√s)⌉`, `qbar = (1+γ²)/2` (with `Q ≥ 1` and `qbar ≤ Q`) and the
rescaled time `τ = η √s t / γ`:

* `τ ≤ √s q`, and the filter degree is `d ≤ 4608 q`;
* the simulator words satisfy `2^m < 2 (2 + 4τ + √(6τ³/ε))` and
  `2^r ≤ 4 (4608 q + 1)`;
* for all native data (`U_J` by valid gates `UJg`, compute circuit, decoder and
  arithmetic), the native circuit for accuracy `ε` makes at most `55296 q`
  times the primitive calls of `V` and uses at most
  `200 (4608 q + 1) (G_C + C_J + a + m + r + 1)` elementary gates, where
  `G_C = privGates nd ar` and `C_J = |UJg|`.

So the gate count is `q` times the per-call cost plus logarithmic terms; with
per-call costs polynomial in the data bit length, `log (N+1)` and `log (1/ζ)`
this is the paper's `Q_base · poly(b_data, log (N+1), log ((Q_base+1)/ε))` with
`Q_base = q` (using `s ≤ N` and `ζ = ε/(48d)`). -/
theorem native_sparse_counts (a : ℕ) (s η t ε : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η) (ht : 0 ≤ t)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      1 ≤ CayleyClockInterface.width s γ ∧
      CayleyClockInterface.moment γ ≤ CayleyClockInterface.width s γ ∧
      η * Real.sqrt s / γ * t ≤
        Real.sqrt s * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) ∧
      (fDeg (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
          (CayleyClockInterface.moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) ∧
      ((2 ^ simM (η * Real.sqrt s / γ * t) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * (η * Real.sqrt s / γ * t) +
          Real.sqrt (6 * (η * Real.sqrt s / γ * t) ^ 3 / ε)) ∧
      ((2 ^ simR (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
          (CayleyClockInterface.moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) + 1) ∧
      ∀ (UJg : List (Gate (Fin a ⊕ S))), (∀ g ∈ UJg, GateOK 3 g) →
        ∀ (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (ar : Arith (NB Empty (Fin a ⊕ S) Z)),
        (∀ p : J → Bool, (nCallsN p (nativeSim a (η * Real.sqrt s / γ * t)
            (CayleyClockInterface.width s γ) (CayleyClockInterface.moment γ) ε UJg nd ar) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) *
            nCallsN p nd.V) ∧
        (nGatesN (nativeSim a (η * Real.sqrt s / γ * t) (CayleyClockInterface.width s γ)
            (CayleyClockInterface.moment γ) ε UJg nd ar) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) + 1) *
            ((privGates nd ar : ℝ) + UJg.length + a + simM (η * Real.sqrt s / γ * t) (ε / 2) +
              simR (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
                (CayleyClockInterface.moment γ) (ε / 2) + 1) := by
  obtain ⟨γ, hγ, hγ1, hγs, hW1, hmom, hdeg, -⟩ :=
    SlotSim.sparse_counts a s η t ε hs hη ht hε hεHalf
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hℓ : 0 ≤ Real.log (1 / ε) :=
    Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
  have hηt : 0 ≤ η * t := mul_nonneg hη ht
  have hq0 : 0 ≤ ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) := by
    unfold ImprovedPrecisionBudget.shape
    have := Real.sqrt_nonneg (s * (η * t) * Real.log (1 / ε))
    positivity
  have hτ0 : 0 ≤ η * Real.sqrt s / γ * t := by positivity
  refine ⟨γ, hγ, hγ1, hγs, hW1, hmom, ?_, hdeg, pow_simM_lt _ ε hτ0 hε, ?_, ?_⟩
  · -- `τ ≤ √s q`
    have hq : Real.sqrt s * (η * t) ≤
        ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) := by
      unfold ImprovedPrecisionBudget.shape
      have := Real.sqrt_nonneg (s * (η * t) * Real.log (1 / ε))
      linarith
    have hinv : η * Real.sqrt s / γ * t ≤ Real.sqrt s * (Real.sqrt s * (η * t)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hγ]
      have h0 : 0 ≤ η * Real.sqrt s * t := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hγs h0]
    exact hinv.trans (mul_le_mul_of_nonneg_left hq hsq)
  · -- `2^r ≤ 4 (4608 q + 1)`
    have h := (simR_spec (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
      (CayleyClockInterface.moment γ) (ε / 2)).2.2
    generalize fDeg (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
      (CayleyClockInterface.moment γ) (ε / 2) = d at h hdeg
    have h' : ((2 ^ simR (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
        (CayleyClockInterface.moment γ) (ε / 2) : ℕ) : ℝ) ≤ 4 * ((d : ℝ) + 1) := by
      exact_mod_cast h
    linarith
  · intro UJg hUJg nd ar
    obtain ⟨hC, hG⟩ := nativeSim_counts a (η * Real.sqrt s / γ * t)
      (CayleyClockInterface.width s γ) (CayleyClockInterface.moment γ) ε UJg hUJg nd ar
    generalize ImprovedPrecisionBudget.shape s (η * t) (Real.log (1 / ε)) = q at hdeg hq0 ⊢
    generalize fDeg (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
      (CayleyClockInterface.moment γ) (ε / 2) = d at hC hG hdeg
    refine ⟨fun p => ?_, ?_⟩
    · rw [hC p]
      have hc : (0 : ℝ) ≤ nCallsN p nd.V := Nat.cast_nonneg _
      have e : ((12 * d * nCallsN p nd.V : ℕ) : ℝ) = 12 * (d : ℝ) * nCallsN p nd.V := by
        push_cast
        ring
      rw [e]
      linarith only [mul_le_mul_of_nonneg_right hdeg hc]
    · generalize privGates nd ar = PG at hG ⊢
      generalize nGatesN (nativeSim a (η * Real.sqrt s / γ * t) (CayleyClockInterface.width s γ)
        (CayleyClockInterface.moment γ) ε UJg nd ar) = NG at hG ⊢
      generalize simM (η * Real.sqrt s / γ * t) (ε / 2) = M at hG ⊢
      generalize simR (CayleyClockInterface.width s γ) (η * Real.sqrt s / γ * t)
        (CayleyClockInterface.moment γ) (ε / 2) = Rr at hG ⊢
      generalize UJg.length = nJ at hG ⊢
      have hG' : (NG : ℝ) ≤ 200 * ((d : ℝ) + 1) * ((a : ℝ) + M + Rr + 1) + 84 * (d : ℝ) * nJ +
          6 * (d : ℝ) * PG := by
        exact_mod_cast hG
      have hJ : (0 : ℝ) ≤ nJ := Nat.cast_nonneg _
      have hP : (0 : ℝ) ≤ PG := Nat.cast_nonneg _
      have hw : (0 : ℝ) ≤ (a : ℝ) + M + Rr + 1 := by positivity
      have h1 : ((d : ℝ) + 1) * ((a : ℝ) + M + Rr + 1) ≤ (4608 * q + 1) * ((a : ℝ) + M + Rr + 1) :=
        mul_le_mul_of_nonneg_right (by linarith) hw
      linarith only [hG', h1, mul_le_mul_of_nonneg_right hdeg hJ,
        mul_le_mul_of_nonneg_right hdeg hP, mul_nonneg hq0 hJ, mul_nonneg hq0 hP, hJ, hP]

end Hamiltonian

/-! ### Dissipative ODEs -/

section ODE

/-- The arithmetic of the constant-coefficient count. -/
theorem ode_gate_arith (W N g D A M R K L J T C G S0 X : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hK : 0 ≤ K) (hL : 0 ≤ L) (hJ : 0 ≤ J) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hS : 0 ≤ S0) (hX : 0 ≤ X) (hg : 1 ≤ g) (hT : T ≤ 2 * (J + 2))
    (hN : N ≤ 200 * (D + 1) * (A + M + R + 1) + 2 * (K + 1) + 3 * (T * (2 * L + 1)) +
      84 * D * C + 6 * D * G + S0)
    (hW : W ≤ 40 * g * N + 20 * g * (4 * (4 * A + 6 * M + 12 * R + 2 * K + 2 * L + 11 + X) + 3)) :
    W ≤ 9000 * g * ((D + 1) * (A + M + R + 1 + C + G) + (K + 1) + (J + 2) * (L + 1) + S0 + X) := by
  have h1 : T * (2 * L + 1) ≤ 2 * (J + 2) * (2 * L + 1) :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  have h2 : 0 ≤ D * (A + M + R + 1) := by positivity
  have h3 : 0 ≤ D * C := mul_nonneg hD hC
  have h4 : 0 ≤ D * G := mul_nonneg hD hG
  have h5 : 0 ≤ J * L := mul_nonneg hJ hL
  have hin : 40 * N + 20 * (4 * (4 * A + 6 * M + 12 * R + 2 * K + 2 * L + 11 + X) + 3) ≤
      9000 * ((D + 1) * (A + M + R + 1 + C + G) + (K + 1) + (J + 2) * (L + 1) + S0 + X) := by
    nlinarith
  calc W ≤ g * (40 * N + 20 * (4 * (4 * A + 6 * M + 12 * R + 2 * K + 2 * L + 11 + X) + 3)) := by
        linarith
    _ ≤ g * (9000 * ((D + 1) * (A + M + R + 1 + C + G) + (K + 1) + (J + 2) * (L + 1) + S0 + X)) :=
        mul_le_mul_of_nonneg_left hin (by linarith)
    _ = _ := by ring

/-- The arithmetic of the time-dependent count. -/
theorem ode_time_gate_arith (W N g D A M R L J T C G S0 X : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hL : 0 ≤ L) (hJ : 0 ≤ J) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (hS : 0 ≤ S0) (hX : 0 ≤ X) (hg : 1 ≤ g) (hT : T ≤ 2 * (J + 2))
    (hN : N ≤ 200 * (D + 1) * (A + M + R + 1) + 3 * (T * (2 * L + 1)) +
      84 * D * C + 6 * D * G + S0)
    (hW : W ≤ 40 * (2 * g) * N +
      20 * (2 * g) * (4 * (4 * A + 8 * M + 12 * R + 2 * L + 11 + X) + 3)) :
    W ≤ 18000 * g * ((D + 1) * (A + M + R + 1 + C + G) + (J + 2) * (L + 1) + S0 + X) := by
  have h1 : T * (2 * L + 1) ≤ 2 * (J + 2) * (2 * L + 1) :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  have h2 : 0 ≤ D * (A + M + R + 1) := by positivity
  have h3 : 0 ≤ D * C := mul_nonneg hD hC
  have h4 : 0 ≤ D * G := mul_nonneg hD hG
  have h5 : 0 ≤ J * L := mul_nonneg hJ hL
  have hin : 80 * N + 40 * (4 * (4 * A + 8 * M + 12 * R + 2 * L + 11 + X) + 3) ≤
      18000 * ((D + 1) * (A + M + R + 1 + C + G) + (J + 2) * (L + 1) + S0 + X) := by
    nlinarith
  calc W ≤ g * (80 * N + 40 * (4 * (4 * A + 8 * M + 12 * R + 2 * L + 11 + X) + 3)) := by
        linarith
    _ ≤ g * (18000 * ((D + 1) * (A + M + R + 1 + C + G) + (J + 2) * (L + 1) + S0 + X)) :=
        mul_le_mul_of_nonneg_left hin (by linarith)
    _ = _ := by ring

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The worst-case gate count of the native constant-coefficient solver**
(the explicit count underlying equation `ode:eq:gate-main`): in every history
the native protocol uses at most
`9000 g [(d+1)(a+m+r+1+C_J+G_C) + (k+1) + (J+2)(l+1) + G_src + A]`
elementary gates, where `C_J` is the number of gates of `U_J`, `G_C` that of
one native private call, `G_src = |srcC 0| + |srcC 1|` and `A` counts the
system, source-scratch, private-scratch and arithmetic wires. -/
theorem native_ode_gate_count (p : GateODE.Params) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) :
    ((nprotocol (nprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost wGateN : ℝ) ≤
      9000 * p.g * (((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1 + UJg.length + privGates nd ar) +
        ((p.k : ℝ) + 1) + ((p.J : ℝ) + 2) * ((p.l : ℝ) + 1) +
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
        ((Fintype.card S : ℝ) + Fintype.card Zs + Fintype.card Z + ar.bT + ar.bP + ar.A)) := by
  obtain ⟨-, hG, -, hW, -⟩ := native_ode_solver p hp UJg hUJg nd hnd ar ζ hζ har srcC hsrcV
  have hcX : Fintype.card (XW Z ar.bT ar.bP ar.A) = Fintype.card Z + ar.bT + ar.bP + ar.A + 3 := by
    simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [p.card_W, hcX] at hW
  rw [p.prepGates_eq] at hG
  have hl : ((2 : ℝ) ^ p.l) ≤ 2 * ((p.J : ℝ) + 2) := by exact_mod_cast p.l_bounds.2.le
  generalize privGates nd ar = PG at hG ⊢
  generalize nGatesN (nprepC p UJg nd ar srcC) = NG at hG hW
  generalize ((nprotocol (nprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost wGateN : ℝ) = WC at hW ⊢
  have hN : (NG : ℝ) ≤ 200 * ((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1) + 2 * ((p.k : ℝ) + 1) +
      3 * ((2 : ℝ) ^ p.l * (2 * (p.l : ℝ) + 1)) + 84 * (p.d : ℝ) * UJg.length +
      6 * (p.d : ℝ) * PG + (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by
    exact_mod_cast hG
  have hW' : WC ≤ 40 * p.g * NG + 20 * p.g * (4 * (4 * (p.a : ℝ) + 6 * p.m + 12 * p.r +
      2 * p.k + 2 * p.l + 11 + ((Fintype.card S : ℝ) + Fintype.card Zs + Fintype.card Z + ar.bT +
      ar.bP + ar.A)) + 3) := by
    refine hW.trans (le_of_eq ?_)
    push_cast
    ring
  exact ode_gate_arith WC NG p.g p.d p.a p.m p.r p.k p.l p.J ((2 : ℝ) ^ p.l) UJg.length PG
    ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))
    ((Fintype.card S : ℝ) + Fintype.card Zs + Fintype.card Z + ar.bT + ar.bP + ar.A)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (by positivity) (by positivity) hp.g_ge hl (by linarith only [hN]) hW'

/-- **The worst-case gate count of the native time-dependent solver** (the
explicit count underlying equation `ode:eq:gate-main`): in every history the
native protocol uses at most
`18000 g [(d+1)(a+m+r+1+C_J+G_C) + (J+2)(l+1) + G_src + A]` elementary gates,
where `G_src = |loadC| + 2 |wpC|` and `A` counts the system, source-scratch,
private-scratch and arithmetic wires. -/
theorem native_ode_time_gate_count (p : GateODE.Time.TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        wGateN : ℝ) ≤
      18000 * p.g * (((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1 + UJg.length + privGates nd ar) +
        ((p.J : ℝ) + 2) * ((p.l : ℝ) + 1) + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((Fintype.card S : ℝ) + Fintype.card Zs + Fintype.card Z + ar.bT + ar.bP + ar.A)) := by
  obtain ⟨-, hG, -, hW, -⟩ :=
    native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  have hcX : Fintype.card (XW Z ar.bT ar.bP ar.A) = Fintype.card Z + ar.bT + ar.bP + ar.A + 3 := by
    simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [p.card_W, hcX] at hW
  rw [p.prepGates_eq] at hG
  have hl : ((2 : ℝ) ^ p.l) ≤ 2 * ((p.J : ℝ) + 2) := by exact_mod_cast p.l_bounds.2.le
  generalize privGates nd ar = PG at hG ⊢
  generalize nGatesN (tnprepC p UJg nd ar loadC wpC) = NG at hG hW
  generalize ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
    wGateN : ℝ) = WC at hW ⊢
  have hN : (NG : ℝ) ≤ 200 * ((p.d : ℝ) + 1) * ((p.a : ℝ) + p.m + p.r + 1) +
      3 * ((2 : ℝ) ^ p.l * (2 * (p.l : ℝ) + 1)) + 84 * (p.d : ℝ) * UJg.length +
      6 * (p.d : ℝ) * PG + (nGatesN loadC : ℝ) + 2 * (nGatesN wpC : ℝ) := by
    exact_mod_cast hG
  have hW' : WC ≤ 40 * (2 * p.g) * NG + 20 * (2 * p.g) * (4 * (4 * (p.a : ℝ) + 8 * p.m +
      12 * p.r + 2 * p.l + 11 + ((Fintype.card S : ℝ) + Fintype.card Zs + Fintype.card Z + ar.bT +
      ar.bP + ar.A)) + 3) := by
    refine hW.trans (le_of_eq ?_)
    rw [show p.ratio = 2 * p.g from rfl]
    push_cast
    ring
  exact ode_time_gate_arith WC NG p.g p.d p.a p.m p.r p.l p.J ((2 : ℝ) ^ p.l) UJg.length PG
    ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)
    ((Fintype.card S : ℝ) + Fintype.card Zs + Fintype.card Z + ar.bT + ar.bP + ar.A)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) (by positivity) hp.g_ge hl (by linarith only [hN]) hW'

end ODE

end

end SparseHamiltonian.GateNative
