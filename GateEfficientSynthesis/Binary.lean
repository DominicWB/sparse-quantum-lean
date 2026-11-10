import GateEfficientSynthesis.Hamiltonian
import GateEfficientBinaryTime.Budget

/-!
# Theorem `hs:thm:gates` over a finite gate set, from binary sparse oracles

The binary-data circuits of `GateEfficientBinary` and `GateEfficientBinaryTime` are native
circuits, so a synthesis budget `ε'` turns them into circuits over the finite gate set `𝒢`
(`synthBudget`).

* `binary_simulation_synth`, `binary_time_simulation_synth`: the synthesised circuits consist of
  valid gates of `𝒢` and the calls of the native ones, have at most `N L(ε'/(N+1))` gates (`N`
  the native gate count, bounded explicitly) and `|X|` more qubits, and their full output is
  within `ε + ε'`.
* `binary_simulation_budget_synth`, `binary_time_simulation_budget_synth`: for the rescaling `γ`
  of `binary_simulation_budget` (respectively `binary_time_simulation_budget`), chosen before the
  gate set, the synthesis budget and the data, with its bounds, every gate set with a
  logarithmic synthesis length `L ζ ≤ c₁ log(1/ζ) + c₀` and every `0 < ε' ≤ 1`, the number of
  gates over `𝒢` is at most `G (c₁ log((G+1)/ε') + c₀)`, where `G` is the explicit
  pre-synthesis budget `200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`. This is an upper
  bound of the form `G_syn log((G_syn + 1)/ε)` of equation `hs:eq:gate-total`, with the gates of the
  native private calls synthesised as well. In the time-independent case, with `m` and `r`
  logarithmic (the bounds on `2^m` and `2^r`) and `G_C` polynomial in the word lengths and in
  `log(1/ζ)` for the arithmetic accuracy `ζ`, it is `Q_base poly(b, log N, log((Q_base+1)/ε))`
  with `Q_base = q` (equation `hs:eq:gate-binary` after synthesis).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open GateCircuit.Sim (fDeg simM simR SimWire io Wire io_apply)
open CayleyClockInterface
open GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w x

section Endpoints

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}

set_option maxHeartbeats 1000000 in
/-- **Gate-efficient sparse simulation from binary sparse oracles over a finite gate set**
(Theorem `hs:thm:gates`, with the binary-data construction of
`binary_simulation` and the synthesis budget `ε'`). -/
theorem binary_simulation_synth (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
    (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ τ ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ) → GateOf 𝒢 g) ∧
    (∀ p : Query → Bool, nCallsN p (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) =
      12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
        (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) ≤
      nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) *
        L (ε' / (nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) + 1)) ∧
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
    ‖nrun (prims (R := R) D en x) (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) ∘L
        (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε + ε' := by
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, -⟩ := binary_simulation (R := R) D en σ hσ hs
    hrange hb c0 hc0 hdec x hH hrow hcol γ τ ε ζ hγ hγ1 hτ hε hε1 hζ hζ1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, ?_, ?_⟩
  · rw [Fintype.card_sum, hcard]
  · generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) = U at herr ⊢
    generalize binarySim k b σ hσ s γ c0 τ ε ζ = C at hvalid herr ⊢
    have hpu := prims_isUnitary (R := R) D en x
    generalize prims (R := R) D en x = prim at hpu herr ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ U herr
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

set_option maxHeartbeats 1000000 in
/-- **Gate-efficient time-dependent sparse simulation from time-indexed binary sparse oracles over a
finite gate set** (Theorem `hs:thm:time` with the circuit of `hs:thm:gates`, with the construction
of `binary_time_simulation` and the synthesis budget `ε'`): for every propagator `U` of the lifted
path, the synthesised circuit is within `ε + ε'` of `U(t)`. -/
theorem binary_time_simulation_synth (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
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
    (∀ i ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool,
      nCallsN p (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) =
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ≤
      nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) *
        L (ε' / (nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) + 1)) ∧
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
    ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
      ‖nrun (primsT (R := R) D en x)
            (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ∘L
          (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε' := by
  obtain ⟨hvalid, hcalls, hgates, hcard, -, -, -, hex, herr⟩ := binary_time_simulation (R := R)
    D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol H t β δ γ ε ζ ht hβ hγ hγ1 hε hε1 hζ
    hζ1 hPath hLip hVal hValBudget hCayley hFreeze hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, ?_, hex, ?_⟩
  · rw [Fintype.card_sum, hcard]
  · intro U hU0 hU
    have h1 := herr U hU0 hU
    generalize U t = Ut at h1 ⊢
    generalize binaryTimeSim k b m σ hσ s γ c0 t ε ζ = C at hvalid h1 ⊢
    have hpu := primsT_isUnitary (R := R) D en x
    generalize primsT (R := R) D en x = prim at hpu h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end Endpoints

/-! ### Budgets with a logarithmic synthesis length -/

section Budgets

set_option maxHeartbeats 1000000 in
/-- **The gate budget from binary sparse oracles over a finite gate set** (equation
`hs:eq:gate-total`, with the binary-data construction). The rescaling `γ` and its bounds are
those of `binary_simulation_budget`: `γ` is chosen from `s`, `τ` and `ε` before the gate set,
the synthesis budget and the data, with `d ≤ 4608 q`, `τ' ≤ √s q`,
`2^m < 2 (2 + 4 τ' + √(6 τ'³/ε))` and `2^r ≤ 4 (4608 q + 1)`. For every gate set with a
logarithmic synthesis length `L ζ ≤ c₁ log(1/ζ) + c₀`, every synthesis budget `0 < ε' ≤ 1` and
all data as in `binary_simulation_budget`, the synthesised circuit consists of valid gates of
`𝒢` and primitive calls, makes at most `55296 q` times `2` row, `2` column and `1` value calls,
uses at most `G (c₁ log((G+1)/ε') + c₀)` gates, where
`G = 200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)` is the pre-synthesis budget, and has
full-output error at most `ε + ε'`. -/
theorem binary_simulation_budget_synth (s : ℕ) (hs1 : 1 ≤ s) (τ ε : ℝ) (hτ : 0 ≤ τ)
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
        (∀ i ∈ synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) : ℝ) ≤
            55296 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) ∧
        (nGatesN (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) : ℝ) ≤
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
                simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) + 1) / ε') +
              c₀) ∧
        ‖nrun (prims (R := R) D en x) (synthBudget hS ε' (binarySim k b σ hσ s γ c0 τ ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤
          ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget.{u, v, w} s hs1 τ ε hτ hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0
    hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨hvalid, -, -, -, -, -⟩ := binary_simulation (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hH hrow hcol γ τ ε ζ hγ hγ1 hτ hε hε1 hζ hζ1 hζε'
  obtain ⟨hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol ζ hζ hζ1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => by rw [hc p]; exact hcalls p, ?_, ?_⟩
  · refine (Nat.cast_le.mpr hg).trans ?_
    exact gates_log_le hc₀ hc₁ hL hε' hε'1 _ _ hgates
  · generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) = U at herr ⊢
    generalize binarySim k b σ hσ s γ c0 τ ε ζ = C at hvalid herr ⊢
    have hpu := prims_isUnitary (R := R) D en x
    generalize prims (R := R) D en x = prim at hpu herr ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ U herr
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

set_option maxHeartbeats 1000000 in
/-- **The time-dependent gate budget from time-indexed binary sparse oracles over a finite gate
set** (equation `hs:eq:gate-total` in the package extension: Theorem `hs:thm:time` with the
circuit of `hs:thm:gates` (single-label case of Lemma `ode:lem:gate-select`)). The rescaling `γ`
and its bound
`d ≤ 4608 q` are those of `binary_time_simulation_budget`: `γ` is chosen from `s`, `t` and `ε`
before the gate set, the synthesis budget, the data, the path and the mesh. For every gate set
with a logarithmic synthesis length, every synthesis budget `0 < ε' ≤ 1` and all data, paths and
meshes as in `binary_time_simulation_budget`, the synthesised circuit consists of valid gates of
`𝒢` and primitive calls, makes at most `55296 q` times `2` row, `2` column and `1` value calls,
uses at most `G (c₁ log((G+1)/ε') + c₀)` gates with the pre-synthesis budget
`G = 200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`, where `2^r ≤ 4 (4608 q + 1)`; the
propagator of the lifted path exists, and the circuit is within `ε + ε'` of every such
propagator. -/
theorem binary_time_simulation_budget_synth (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (ht : 0 ≤ t)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
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
        (∀ i ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) : ℝ) ≤
            55296 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) ∧
        (nGatesN (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
              ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                  (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
                simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) *
            (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s t
                  (Real.log (2 / ε)) + 1) *
              ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                  (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
                simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) + 1) / ε') +
              c₀) ∧
        ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) ∧
        (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
        ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
          TimeDependent.SolvesOn
            (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
          ‖nrun (primsT (R := R) D en x)
                (synthBudget hS ε' (binaryTimeSim k b m σ hσ s γ c0 t ε ζ)) ∘L
              (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
              (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L U t‖ ≤ ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hall⟩ := binary_time_simulation_budget.{u, v, w} s hs1 t ε ht
    hε hε1
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze ζ hζ hζ1
    hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨hvalid, -, -, -, -, -, -, -, -⟩ := binary_time_simulation (R := R) D en σ hσ hs hrange
    hb c0 hc0 hdec x hHerm hrow hcol H t β δ γ ε ζ ht hβ hγ hγ1 hε hε1 hζ hζ1 hPath hLip hVal
    hValBudget hCayley hFreeze hζε'
  obtain ⟨hcalls, hgates, hr2, hex, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hHerm hrow hcol H β δ hβ hPath hLip hVal hValBudget hCayley hFreeze ζ hζ hζ1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => by rw [hc p]; exact hcalls p, ?_, hr2, hex, ?_⟩
  · refine (Nat.cast_le.mpr hg).trans ?_
    exact gates_log_le hc₀ hc₁ hL hε' hε'1 _ _ hgates
  · intro U hU0 hU
    have h1 := herr U hU0 hU
    generalize U t = Ut at h1 ⊢
    generalize binaryTimeSim k b m σ hσ s γ c0 t ε ζ = C at hvalid h1 ⊢
    have hpu := primsT_isUnitary (R := R) D en x
    generalize primsT (R := R) D en x = prim at hpu h1 ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ Ut h1
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end Budgets

end

end SparseHamiltonian.GateSynth
