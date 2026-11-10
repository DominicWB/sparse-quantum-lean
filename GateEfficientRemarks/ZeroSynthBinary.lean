import GateEfficientRemarks.ZeroBinary
import GateEfficientRemarks.ZeroSynth
import GateEfficientSynthesis.Binary

/-!
# Theorem `hs:thm:gates` at zero time over a finite gate set: binary sparse data

The finite-gate-set forms of the binary-data endpoints of Theorem `hs:thm:gates` (library
`GateEfficientSynthesis`: `GateSynth.binary_simulation_synth`,
`GateSynth.binary_time_simulation_synth`, `GateSynth.binary_simulation_budget_synth`,
`GateSynth.binary_time_simulation_budget_synth`) synthesise the binary-data circuits with the budget
`ε'`. With the combined circuits `binaryCircuit` and `binaryTimeCircuit` (the empty circuit at zero
time, the released circuit otherwise) and `synthBudget_nil`, this file states the remark "at `t = 0`
the identity suffices" (Theorem `hs:thm:gates`) for them:

* `binary_simulation_synth_nonneg`, `binary_time_simulation_synth_nonneg`;
* `binary_simulation_budget_synth_nonneg`, `binary_time_simulation_budget_synth_nonneg` (the
  rescaling `γ` chosen from `s`, the time and `ε` before the gate set, the synthesis budget and the
  data, as in the released budgets).

Each keeps every conclusion of the released theorem, with the synthesised counts `0` at zero time
and the released counts otherwise, and the full-output error exactly `0` at zero time.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary GateSynth
open GateCircuit.Sim (fDeg simM simR SimWire Wire io io_apply)
open CayleyClockInterface
open ZeroTimeRemarks.Gates (exp_zero_time identity_comp_error_eq_zero identity_comp_error_le)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w x

section Endpoints

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:gates` from binary sparse data over a finite gate set for every `τ ≥ 0`,
with the identity circuit at `τ = 0`.** Under the hypotheses of the released
`GateSynth.binary_simulation_synth`, the synthesis `synthBudget hS ε' (binaryCircuit …)` consists
of valid gates of `𝒢` and primitive calls, makes `0` calls if `τ = 0` and exactly `12 d` times `2`
row, `2` column and `1` value calls otherwise, uses `0` gates if `τ = 0` and at most
`N L(ε'/(N+1))` gates otherwise (`N` the gate count of the released `binarySim`, bounded as in the
released theorem), has the released qubit count (`|Xa|` synthesis ancillas included), and its
full output is within `ε + ε'` of `exp(-iτĤ)`; at `τ = 0` the error is exactly `0`. -/
theorem binary_simulation_synth_nonneg (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
    (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ τ ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) =
      (if τ = 0 then 0 else
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0)))) ∧
    nGatesN (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) ≤
      (if τ = 0 then 0 else
        nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) *
          L (ε' / (nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) + 1))) ∧
    nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) *
          (k + 1 + simM (time (s : ℝ) τ γ) (ε / 2) +
            simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
          (2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2))
        (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A ⊕
        Xa) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
    ‖nrun (prims (R := R) D en x) (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) ∘L
        (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε + ε' ∧
    (τ = 0 →
      ‖nrun (prims (R := R) D en x) (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) ∘L
        (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) := by
  obtain ⟨hv, hk, hcalls, hg, hgates, hcard, herr⟩ := binary_simulation_synth (R := R) hS ε' hε'
    D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol γ τ ε ζ hγ hγ1 hτ hε hε1 hζ hζ1 hζε
  by_cases hτ0 : τ = 0
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = [] := if_pos hτ0
    rw [hc, synthBudget_nil, if_pos hτ0, nrun_nil, exp_zero_time τ hτ0]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, le_rfl, hgates, hcard, identity_comp_error_le _ _ hε0,
      fun _ => identity_comp_error_eq_zero _⟩
    rw [if_pos hτ0]
    rfl
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = binarySim k b σ hσ s γ c0 τ ε ζ :=
      if_neg hτ0
    rw [hc, if_neg hτ0]
    refine ⟨hv, hk, fun p => ?_, hg, hgates, hcard, ?_, fun h => absurd h hτ0⟩
    · rw [if_neg hτ0]
      exact hcalls p
    · convert herr using 1

/-- **The time-dependent gate-level simulation (Theorem `hs:thm:time` with the circuit of
`hs:thm:gates`) from time-indexed binary sparse data over a finite gate set for every `t ≥ 0`, with
the identity circuit at `t = 0`.** Under the hypotheses of the released
`GateSynth.binary_time_simulation_synth`, the synthesis `synthBudget hS ε' (binaryTimeCircuit …)`
consists of valid gates of `𝒢` and primitive calls, makes `0` calls and uses `0` gates if `t = 0`,
has the released counts otherwise, has the released qubit count, the propagator of the lifted path
exists, and for every propagator `U` its full output is within `ε + ε'` of `U(t)`; at `t = 0` the
error is exactly `0`. -/
theorem binary_time_simulation_synth_nonneg (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
    (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    (hrow : ∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (hcol : ∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (H : ℝ → Matrix n n ℂ) (t β δ γ ε ζ : ℝ) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hPath : ∀ u ∈ Set.Icc 0 t, (H u).IsHermitian)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t,
      ‖SparseStateOverlap.matrixOperator (H u) - SparseStateOverlap.matrixOperator (H v)‖ ≤
        β * |u - v|)
    (hVal : ∀ r : Fin (2 ^ m),
      ‖SparseStateOverlap.matrixOperator (H (((r : ℕ) : ℝ) * t / 2 ^ m)) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ)
    (hValBudget : 8 * t * δ ≤ ε)
    (hCayley : TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m)
    (hFreeze : 8 * β * t ^ 2 ≤ ε * 2 ^ m)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool,
      nCallsN p (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) =
        (if t = 0 then 0 else
          12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0)))) ∧
    nGatesN (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) ≤
      (if t = 0 then 0 else
        nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) *
          L (ε' / (nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) + 1))) ∧
    nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) *
          (k + 1 + m + simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
          (2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
              (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (Wire (k + 1) m
        (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
        (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
        (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) =
      k + (2 * (k + 1) + 3 * m +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 3) +
        (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
    (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
    (∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
      ‖nrun (primsT (R := R) D en x)
            (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) ∘L
          (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε') ∧
    (t = 0 → ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
      ‖nrun (primsT (R := R) D en x)
            (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) ∘L
          (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ = 0) := by
  obtain ⟨hv, hk, hcalls, hg, hgates, hcard, hex, herr⟩ := binary_time_simulation_synth (R := R)
    hS ε' hε' D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H t β δ γ ε ζ ht hβ hγ hγ1 hε
    hε1 hζ hζ1 hPath hLip hVal hValBudget hCayley hFreeze hζε
  by_cases ht0 : t = 0
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, synthBudget_nil, if_pos ht0, nrun_nil]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, le_rfl, hgates, hcard, hex, fun U hU0 _ => ?_, fun _ U hU0 _ => ?_⟩
    · rw [if_pos ht0]
      rfl
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_le _ _ hε0
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_eq_zero _
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ =
        binaryTimeSim k b m σ hσ s γ c0 t ε ζ := if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hv, hk, fun p => ?_, hg, hgates, hcard, hex, fun U hU0 hU => ?_,
      fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · convert herr U hU0 hU using 1

end Endpoints

/-! ### Budgets with a logarithmic synthesis length -/

section Budgets

set_option maxHeartbeats 1000000 in
/-- **The gate budget from binary sparse oracles over a finite gate set for every `τ ≥ 0`, with the
identity circuit at `τ = 0`** (equation `hs:eq:gate-total`). There is a rescaling `γ`, chosen from
`s`, `τ` and `ε` before the gate set, the synthesis budget and the data, with every bound that the
released `GateSynth.binary_simulation_budget_synth` states, such that: for every gate set with
`L ζ ≤ c₁ log(1/ζ) + c₀`, every `0 < ε' ≤ 1` and all data as in the released budget, the synthesis
of `binaryCircuit` consists of valid gates of `𝒢` and primitive calls, makes `0` calls if `τ = 0`
and at most `55296 q` times `2` row, `2` column and `1` value calls otherwise, uses `0` gates if
`τ = 0` and at most `G (c₁ log((G+1)/ε') + c₀)` otherwise, with the released pre-synthesis budget
`G`, and has full-output error at most `ε + ε'`, exactly `0` at `τ = 0`. -/
theorem binary_simulation_budget_synth_nonneg (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      time (s : ℝ) τ γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) τ γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) τ γ + Real.sqrt (6 * time (s : ℝ) τ γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) ∧
      ∀ {Xa : Type x} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}
        (hS : Synthesis 𝒢 Xa L) {c₀ c₁ : ℝ}, 0 ≤ c₀ → 0 ≤ c₁ →
        (∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) →
        ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b : ℕ} {R : Type w}
        [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k),
        s = 2 ^ σ →
        (∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) →
        0 < b → ∀ c0 : ℝ, 0 < c0 → (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) →
        ∀ x : X, (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ ≤ ε →
        (∀ i ∈ synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) : ℝ) ≤
            (if τ = 0 then 0 else
              55296 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
                (2 * (if p Query.rowLocation then 1 else 0) +
                  2 * (if p Query.columnLocation then 1 else 0) +
                  (if p Query.value then 1 else 0)))) ∧
        (nGatesN (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) : ℝ) ≤
          (if τ = 0 then 0 else
            200 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) *
                ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                    (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                  simM (time (s : ℝ) τ γ) (ε / 2) +
                  simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) *
              (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s τ
                    (Real.log (1 / ε)) + 1) *
                ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                    (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                  simM (time (s : ℝ) τ γ) (ε / 2) +
                  simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) + 1) /
                    ε') + c₀)) ∧
        ‖nrun (prims (R := R) D en x)
              (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤
          ε + ε' ∧
        (τ = 0 → ‖nrun (prims (R := R) D en x)
              (synthBudget hS ε' (binaryCircuit k b σ hσ s γ c0 τ ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget_synth.{u, v, w, x} s hs1 τ ε hτ hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0
    hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨hv, hk, hcalls, hgates, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D en σ hσ hs
    hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  by_cases hτ0 : τ = 0
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = [] := if_pos hτ0
    rw [hc, synthBudget_nil, nrun_nil, exp_zero_time τ hτ0]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, ?_, identity_comp_error_le _ _ hε0, fun _ => identity_comp_error_eq_zero _⟩
    · rw [if_pos hτ0]
      simp
    · rw [if_pos hτ0]
      simp
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = binarySim k b σ hσ s γ c0 τ ε ζ :=
      if_neg hτ0
    rw [hc]
    refine ⟨hv, hk, fun p => ?_, ?_, ?_, fun h => absurd h hτ0⟩
    · rw [if_neg hτ0]
      exact hcalls p
    · rw [if_neg hτ0]
      exact hgates
    · convert herr using 1

/-- **The time-dependent gate budget from time-indexed binary sparse oracles over a finite gate set
for every `t ≥ 0`, with the identity circuit at `t = 0`** (equation `hs:eq:gate-total` in the
package extension: Theorem `hs:thm:time` with the circuit of `hs:thm:gates` (single-label case of
Lemma `ode:lem:gate-select`)). There is a rescaling `γ`, chosen before the gate set, the synthesis
budget,
the data, the path and the mesh, with every bound that the released
`GateSynth.binary_time_simulation_budget_synth` states (`d ≤ 4608 q`), such that: for every gate set
with a logarithmic synthesis length, every `0 < ε' ≤ 1` and all data, paths and meshes as in the
released budget, the synthesis of `binaryTimeCircuit` consists of valid gates of `𝒢` and primitive
calls, makes `0` calls and uses `0` gates if `t = 0` and has the released bounds otherwise,
`2^r ≤ 4 (4608 q + 1)`, the propagator of the lifted path exists, and the circuit is within `ε + ε'`
of every such propagator, with error exactly `0` at `t = 0`. -/
theorem binary_time_simulation_budget_synth_nonneg (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ)
    (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) ∧
      ∀ {Xa : Type x} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}
        (hS : Synthesis 𝒢 Xa L) {c₀ c₁ : ℝ}, 0 ≤ c₀ → 0 ≤ c₁ →
        (∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) →
        ∀ ε' : ℝ, 0 < ε' → ε' ≤ 1 →
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {k b m : ℕ} {R : Type w}
        [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
        (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
        (hσ : σ ≤ k), s = 2 ^ σ →
        (∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u)) →
        0 < b → ∀ c0 : ℝ, 0 < c0 → (∀ e z, D.decode e z = (c0 : ℂ) * gauss z) →
        ∀ x : X, (∀ r, (D.matrix (x, r)).IsHermitian) →
        (∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        (∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1) →
        ∀ (H : ℝ → Matrix n n ℂ) (β δ : ℝ), 0 ≤ β →
        (∀ u ∈ Set.Icc 0 t, (H u).IsHermitian) →
        (∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t,
          ‖SparseStateOverlap.matrixOperator (H u) - SparseStateOverlap.matrixOperator (H v)‖ ≤
            β * |u - v|) →
        (∀ r : Fin (2 ^ m),
          ‖SparseStateOverlap.matrixOperator (H (((r : ℕ) : ℝ) * t / 2 ^ m)) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ) →
        8 * t * δ ≤ ε →
        TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m →
        8 * β * t ^ 2 ≤ ε * 2 ^ m →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ ≤ ε →
        (∀ i ∈ synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) : ℝ) ≤
            (if t = 0 then 0 else
              55296 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
                (2 * (if p Query.rowLocation then 1 else 0) +
                  2 * (if p Query.columnLocation then 1 else 0) +
                  (if p Query.value then 1 else 0)))) ∧
        (nGatesN (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          (if t = 0 then 0 else
            200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
                ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                    (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
                  simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) *
              (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s t
                    (Real.log (2 / ε)) + 1) *
                ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                    (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
                  simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) + 1) /
                    ε') + c₀)) ∧
        ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) ∧
        (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
        (∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
          ‖nrun (primsT (R := R) D en x)
                (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) ∘L
              (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
              (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε') ∧
        (t = 0 → ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
          ‖nrun (primsT (R := R) D en x)
                (synthBudget hS ε' (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ)) ∘L
              (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
              (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ = 0) := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hall⟩ :=
    binary_time_simulation_budget_synth.{u, v, w, x} s hs1 t ε ht hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze ζ hζ hζ1
    hζε
  obtain ⟨hv, hk, hcalls, hgates, hr2, hex, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D
    en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget
    hCayley hFreeze ζ hζ hζ1 hζε
  by_cases ht0 : t = 0
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, synthBudget_nil, nrun_nil]
    have hε0 : 0 ≤ ε + ε' := by linarith
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil,
      fun p => ?_, ?_, hr2, hex, fun U hU0 _ => ?_, fun _ U hU0 _ => ?_⟩
    · rw [if_pos ht0]
      simp
    · rw [if_pos ht0]
      simp
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_le _ _ hε0
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_eq_zero _
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ =
        binaryTimeSim k b m σ hσ s γ c0 t ε ζ := if_neg ht0
    rw [hc]
    refine ⟨hv, hk, fun p => ?_, ?_, hr2, hex, fun U hU0 hU => ?_, fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · rw [if_neg ht0]
      exact hgates
    · convert herr U hU0 hU using 1

end Budgets

end

end SparseHamiltonian.GateRemarks
