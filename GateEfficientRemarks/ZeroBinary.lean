import GateEfficientBinaryTime.Budget
import ZeroTimeRemarks.Gates

/-!
# Theorem `hs:thm:gates` at zero time: binary sparse data

Theorem `hs:thm:gates` of the accompanying paper states "This is a time-independent result; at
`t = 0` the identity suffices." The released library `ZeroTimeRemarks` states this remark for the
exact-gate and native circuits (`ZeroTimeRemarks.Gates`) and lists the binary-data variants as not
formalised. The released binary-data endpoints (`GateBinary.binary_simulation`,
`GateBinary.binary_simulation_budget`, `GateBinary.binary_time_simulation`,
`GateBinary.binary_time_simulation_budget`) build one circuit for every time `τ ≥ 0`, which at zero
time still makes `12 d` times `2` row, `2` column and `1` value calls. This file states the remark
in the same model:

* `binaryCircuit`, `binary_simulation_nonneg`, `binary_simulation_budget_nonneg`: binary sparse
  data, every `τ ≥ 0`;
* `binaryTimeCircuit`, `binary_time_simulation_nonneg`, `binary_time_simulation_budget_nonneg`:
  time-indexed binary sparse data, every `t ≥ 0`.

The circuits are the empty circuit at zero time and the released circuit otherwise, on the same
wires. Every count is `0` at zero time and the released count otherwise; every other conclusion
of the released theorems (wire counts, degree and register bounds, existence of a propagator) is
kept; the error is at most `ε` and exactly `0` at zero time (`ZeroTimeRemarks.Gates.exp_zero_time`,
`ZeroTimeRemarks.Gates.identity_comp_error_eq_zero`). The budget forms keep the released order of
quantifiers: the rescaling `γ` is chosen from `s`, the time and `ε` before the data.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR SimWire Wire io)
open SparseHamiltonian.ZeroTimeRemarks.Gates (exp_zero_time identity_comp_error_eq_zero
  identity_comp_error_le)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w

/-! ### Binary sparse data -/

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The circuit of Theorem `hs:thm:gates` from binary sparse data for every `τ ≥ 0`: the empty
(identity) circuit at `τ = 0` and the released `binarySim` otherwise, on the same wires. -/
def binaryCircuit (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 τ ε ζ : ℝ) :
    List (NInstr (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2))
      (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
      (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A)
      (PY k b) Query) :=
  if τ = 0 then [] else binarySim k b σ hσ s γ c0 τ ε ζ

set_option maxHeartbeats 1000000 in
/-- **Theorem `hs:thm:gates` from binary sparse data for every `τ ≥ 0`, with the identity
circuit at `τ = 0`.** Under the hypotheses of the released `GateBinary.binary_simulation`, the
circuit `binaryCircuit k b σ hσ s γ c₀ τ ε ζ` consists of valid instructions, makes `0` primitive
calls if `τ = 0` and exactly `12 d` times `2` row, `2` column and `1` value calls otherwise, has
`0` elementary gates if `τ = 0` and at most
`200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d (56 k + 2 |circ| + 2 bP + bT + 1)` otherwise, and its
full output on the system embedding is within `ε` of `exp(-iτĤ)`; at `τ = 0` the error is exactly
`0`. The qubit count and the degree and register bounds of the released theorem are unchanged. -/
theorem binary_simulation_nonneg (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ τ ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binaryCircuit k b σ hσ s γ c0 τ ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binaryCircuit k b σ hσ s γ c0 τ ε ζ) =
      (if τ = 0 then 0 else
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0)))) ∧
    nGatesN (binaryCircuit k b σ hσ s γ c0 τ ε ζ) ≤
      (if τ = 0 then 0 else
        200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) *
            (k + 1 + simM (time (s : ℝ) τ γ) (ε / 2) +
              simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) +
          84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) * (σ + 1) +
          6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
            (2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
              (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
                (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1))) ∧
    Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2))
        (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) ∧
    ‖nrun (prims (R := R) D en x) (binaryCircuit k b σ hσ s γ c0 τ ε ζ) ∘L
        sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε ∧
    (τ = 0 → ‖nrun (prims (R := R) D en x) (binaryCircuit k b σ hσ s γ c0 τ ε ζ) ∘L
        sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) ∧
    (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) ≤
      128 * (time (s : ℝ) τ γ * moment γ + width (s : ℝ) γ * (1 + Real.log (6 / ε))) ∧
    TimeSchedule.steps (time (s : ℝ) τ γ) (ε / 6) ≤ 2 ^ simM (time (s : ℝ) τ γ) (ε / 2) ∧
    2 ^ simM (time (s : ℝ) τ γ) (ε / 2) < 2 * TimeSchedule.steps (time (s : ℝ) τ γ) (ε / 6) ∧
    2 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 2 ≤
      2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) ∧
    2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) ≤
      4 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) := by
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
    binary_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol γ τ ε ζ hγ hγ1
      hτ hε hε1 hζ hζ1 hζε
  by_cases hτ0 : τ = 0
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = [] := if_pos hτ0
    rw [hc, if_pos hτ0, nrun_nil, exp_zero_time τ hτ0]
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun p => ?_, le_rfl, hcard,
      identity_comp_error_le _ ε hε.le, fun _ => identity_comp_error_eq_zero _, hdeg, hm1, hm2,
      hr1, hr2⟩
    rw [if_pos hτ0]
    rfl
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = binarySim k b σ hσ s γ c0 τ ε ζ :=
      if_neg hτ0
    rw [hc, if_neg hτ0]
    refine ⟨hvalid, fun p => ?_, hgates, hcard, ?_, fun h => absurd h hτ0, hdeg, hm1, hm2, hr1,
      hr2⟩
    · rw [if_neg hτ0]
      exact hcalls p
    · convert herr using 1

end Binary

set_option maxHeartbeats 1000000 in
/-- **The budget of the binary construction for every `τ ≥ 0`, with the identity circuit at
`τ = 0`** (Theorem `hs:thm:gates`, pre-synthesis form of `hs:eq:gate-binary`). For `s ≥ 1`, `τ ≥ 0`,
`0 < ε ≤ 1/2` and `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`, there is a rescaling `γ`, chosen from
`s`, `τ` and `ε` before the data, with every bound that the released
`GateBinary.binary_simulation_budget` states, such that: for all data, inputs and arithmetic
accuracies as in the released budget, the circuit `binaryCircuit` makes `0` calls if `τ = 0` and at
most `55296 q` times `2` row, `2` column and `1` value calls otherwise, uses `0` elementary gates if
`τ = 0` and at most `200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)` otherwise, and has
full-output error at most `ε` against `exp(-iτĤ)`, exactly `0` at `τ = 0`. -/
theorem binary_simulation_budget_nonneg (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      time (s : ℝ) τ γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) τ γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) τ γ + Real.sqrt (6 * time (s : ℝ) τ γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) ∧
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
        (∀ p : Query → Bool, (nCallsN p (binaryCircuit k b σ hσ s γ c0 τ ε ζ) : ℝ) ≤
          (if τ = 0 then 0 else
            55296 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0)))) ∧
        (nGatesN (binaryCircuit k b σ hσ s γ c0 τ ε ζ) : ℝ) ≤
          (if τ = 0 then 0 else
            200 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) τ γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1)) ∧
        ‖nrun (prims (R := R) D en x) (binaryCircuit k b σ hσ s γ c0 τ ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε ∧
        (τ = 0 → ‖nrun (prims (R := R) D en x) (binaryCircuit k b σ hσ s γ c0 τ ε ζ) ∘L
            sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
              NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ = 0) := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget.{u, v, w} s hs1 τ ε hτ hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol ζ hζ hζ1 hζε
  by_cases hτ0 : τ = 0
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = [] := if_pos hτ0
    rw [hc, nrun_nil, exp_zero_time τ hτ0]
    refine ⟨fun p => ?_, ?_, identity_comp_error_le _ ε hε.le,
      fun _ => identity_comp_error_eq_zero _⟩
    · rw [if_pos hτ0]
      simp
    · rw [if_pos hτ0]
      simp
  · have hc : binaryCircuit k b σ hσ s γ c0 τ ε ζ = binarySim k b σ hσ s γ c0 τ ε ζ :=
      if_neg hτ0
    rw [hc]
    refine ⟨fun p => ?_, ?_, ?_, fun h => absurd h hτ0⟩
    · rw [if_neg hτ0]
      exact hcalls p
    · rw [if_neg hτ0]
      exact hgates
    · convert herr using 1

/-! ### Time-indexed binary sparse data -/

section BinaryTime

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The time-dependent circuit (Theorem `hs:thm:time` with the circuit of `hs:thm:gates`) from
time-indexed binary sparse data for every `t ≥ 0`: the empty (identity) circuit at `t = 0` and the
released `binaryTimeSim` otherwise, on the same wires. -/
def binaryTimeCircuit (k b m σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ) :
    List (NInstr (HW (Wire (k + 1) m
      (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
      (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
      (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
      (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
      (binArithT k b m (γ * Real.sqrt s * c0) ζ).A) (Fin m ⊕ PY k b) Query) :=
  if t = 0 then [] else binaryTimeSim k b m σ hσ s γ c0 t ε ζ

/-- **The time-dependent gate-level simulation (Theorem `hs:thm:time` with the circuit of
`hs:thm:gates`) from time-indexed binary sparse data for every `t ≥ 0`, with the identity circuit at
`t = 0`.** Under the hypotheses of the released `GateBinary.binary_time_simulation`, the circuit
`binaryTimeCircuit k b m σ hσ s γ c₀ t ε ζ` consists of valid instructions, makes `0` calls and has
`0` elementary gates if `t = 0`, has the released counts otherwise, and for every propagator `U` of
the lifted path its full output on the system embedding is within `ε` of `U(t)`; at `t = 0` the
error is exactly `0`. The qubit count, the degree and register bounds and the existence of a
propagator are those of the released theorem. -/
theorem binary_time_simulation_nonneg (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
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
    (∀ i ∈ binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) =
      (if t = 0 then 0 else
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) +
            (if p Query.value then 1 else 0)))) ∧
    nGatesN (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) ≤
      (if t = 0 then 0 else
        200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) *
            (k + 1 + m + simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) +
          84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) * (σ + 1) +
          6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
            (2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
              (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
                (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1))) ∧
    Fintype.card (HW (Wire (k + 1) m
        (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
        (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
        (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A) =
      k + (2 * (k + 1) + 3 * m +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 3) +
        (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) ∧
    (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) ≤
      128 * (time (s : ℝ) t γ * moment γ + width (s : ℝ) γ * (1 + Real.log (12 / ε))) ∧
    2 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 2 ≤
      2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) ∧
    2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) ≤
      4 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) ∧
    (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
    (∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
      ‖nrun (primsT (R := R) D en x) (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) ∘L
          sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ ≤ ε) ∧
    (t = 0 → ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
      ‖nrun (primsT (R := R) D en x) (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) ∘L
          sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ = 0) := by
  obtain ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, hex, herr⟩ :=
    binary_time_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H t β
      δ γ ε ζ ht hβ hγ hγ1 hε hε1 hζ hζ1 hPath hLip hVal hValBudget hCayley hFreeze hζε
  by_cases ht0 : t = 0
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, if_pos ht0, nrun_nil]
    refine ⟨fun i hi => absurd hi List.not_mem_nil, fun p => ?_, le_rfl, hcard, hdeg, hr1, hr2,
      hex, fun U hU0 _ => ?_, fun _ U hU0 _ => ?_⟩
    · rw [if_pos ht0]
      rfl
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_le _ ε hε.le
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_eq_zero _
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ =
        binaryTimeSim k b m σ hσ s γ c0 t ε ζ := if_neg ht0
    rw [hc, if_neg ht0]
    refine ⟨hvalid, fun p => ?_, hgates, hcard, hdeg, hr1, hr2, hex, fun U hU0 hU => ?_,
      fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · convert herr U hU0 hU using 1

end BinaryTime

/-- **The budget of the time-dependent binary construction for every `t ≥ 0`, with the identity
circuit at `t = 0`** (Theorem `hs:thm:time` with the circuit of `hs:thm:gates`, before finite-set
synthesis). For `s ≥ 1`, `t ≥ 0`, `0 < ε ≤ 1` and `q = √s t + √(s t log(2/ε)) + log(2/ε)`, there is
a rescaling `γ`, chosen from `s`, `t` and `ε` before the data, the path and the mesh, with every
bound that the released `GateBinary.binary_time_simulation_budget` states (`d ≤ 4608 q`), such that:
for all data, paths, meshes and arithmetic accuracies as in the released budget, the circuit
`binaryTimeCircuit` makes `0` calls if `t = 0` and at most `55296 q` times `2` row, `2` column and
`1` value calls otherwise, uses `0` elementary gates if `t = 0` and at most
`200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)` otherwise, `2^r ≤ 4 (4608 q + 1)`, the
propagator of the lifted path exists, and the full output is within `ε` of `U(t)` for every
propagator `U`, with error exactly `0` at `t = 0`. -/
theorem binary_time_simulation_budget_nonneg (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (ht : 0 ≤ t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) ∧
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
        (∀ p : Query → Bool, (nCallsN p (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) : ℝ) ≤
          (if t = 0 then 0 else
            55296 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0)))) ∧
        (nGatesN (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) : ℝ) ≤
          (if t = 0 then 0 else
            200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
              ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                  (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
                simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1)) ∧
        ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) ∧
        (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
        (∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
          ‖nrun (primsT (R := R) D en x) (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) ∘L
              sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ ≤
            ε) ∧
        (t = 0 → ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
          ‖nrun (primsT (R := R) D en x) (binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ) ∘L
              sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ =
            0) := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hall⟩ :=
    binary_time_simulation_budget.{u, v, w} s hs1 t ε ht hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath
    hLip hVal hValBudget hCayley hFreeze ζ hζ hζ1 hζε
  obtain ⟨hcalls, hgates, hr2, hex, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze ζ hζ hζ1 hζε
  by_cases ht0 : t = 0
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ = [] := if_pos ht0
    rw [hc, nrun_nil]
    refine ⟨fun p => ?_, ?_, hr2, hex, fun U hU0 _ => ?_, fun _ U hU0 _ => ?_⟩
    · rw [if_pos ht0]
      simp
    · rw [if_pos ht0]
      simp
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_le _ ε hε.le
    · have hUt : U t = 1 := by rw [ht0, hU0]
      rw [hUt]
      exact identity_comp_error_eq_zero _
  · have hc : binaryTimeCircuit k b m σ hσ s γ c0 t ε ζ =
        binaryTimeSim k b m σ hσ s γ c0 t ε ζ := if_neg ht0
    rw [hc]
    refine ⟨fun p => ?_, ?_, hr2, hex, fun U hU0 hU => ?_, fun h => absurd h ht0⟩
    · rw [if_neg ht0]
      exact hcalls p
    · rw [if_neg ht0]
      exact hgates
    · convert herr U hU0 hU using 1

end

end SparseHamiltonian.GateRemarks
