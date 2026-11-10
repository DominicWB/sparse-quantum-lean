import GateEfficientSigned.Binary
import GateEfficientRemarks.QubitsSynth

/-!
# Theorem `hs:thm:gates` over a finite gate set from binary sparse data for every real time

The finite-gate-set forms of the binary-data endpoints (`GateSynth.binary_simulation_synth`,
`GateSynth.binary_simulation_budget_synth`, `GateBitBudget.binary_simulation_budget_synth_bits`
and `GateRemarks.binary_simulation_budget_synth_bits_qubits`) synthesise the circuit
`GateBinary.binarySim` for `τ ≥ 0` with the synthesis budget `ε'` (`GateSynth.synthBudget`). This
file states each of them for every real `t`, synthesising the signed circuit `binarySimSigned`:

* `binary_simulation_synth_signed`: every conclusion of `GateSynth.binary_simulation_synth` for
  `|t|`, with the full-output error `ε + ε'` against `exp(-itĤ)`;
* `binary_simulation_budget_synth_signed`: the rescaling of `binary_simulation_budget_signed`,
  chosen before the gate set, the synthesis budget and the data, and the counts of
  `GateSynth.binary_simulation_budget_synth` for `|t|`;
* `binary_simulation_budget_synth_bits_signed`: the same with the gate count in `𝔟_H` of
  `GateBitBudget.binary_simulation_budget_synth_bits`;
* `binary_simulation_budget_synth_bits_qubits_signed`: the same with the qubit count in `𝔟_H` of
  `GateRemarks.binary_simulation_budget_synth_bits_qubits`.

The synthesis of the signed circuit is not the signed synthesis of the circuit for `|t|` (a
synthesised gate is not the inverse of the synthesis of its inverse); the statements are about
`synthBudget hS ε' (binarySimSigned …)`, and the synthesised counts follow from those of
`binarySimSigned`, which are the released ones for `|t|`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000

namespace SparseHamiltonian.GateSigned

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateBitBudget SparseHamiltonian.GateSynth SparseHamiltonian.GateRemarks
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR SimWire io io_apply)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

universe u v w x

section Endpoints

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {L : ℝ → ℕ}

set_option maxHeartbeats 1000000 in
/-- **Gate-efficient sparse simulation from binary sparse oracles over a finite gate set for
every real time** (Theorem `hs:thm:gates`). Under the hypotheses of the
released `GateSynth.binary_simulation_synth` for the time `|t|` (the synthesis hypothesis
`Synthesis 𝒢 Xa L`, a synthesis budget `ε' > 0` and the hypotheses of
`binary_simulation_signed`), for every real `t` the synthesis
`synthBudget hS ε' (binarySimSigned …)` consists of valid gates of `𝒢` and primitive calls,
makes `12 d` times `2` row, `2` column and `1` value calls, has at most `N L(ε'/(N+1))` gates
with `N` the gate count of `binarySimSigned` (bounded as in the released theorem for `|t|`),
has `|Xa|` more qubits than the native register, and its full output, with the synthesis
ancillas clean, is within `ε + ε'` of `exp(-itĤ)`. -/
theorem binary_simulation_synth_signed (hS : Synthesis 𝒢 Xa L) (ε' : ℝ) (hε' : 0 < ε')
    (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ t ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ) →
      GateOf 𝒢 g) ∧
    (∀ p : Query → Bool,
      nCallsN p (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) =
        12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) *
          (2 * (if p Query.rowLocation then 1 else 0) +
            2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) ≤
      nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) *
        L (ε' / (nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) + 1)) ∧
    nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) *
          (k + 1 + simM (time (s : ℝ) |t| γ) (ε / 2) +
            simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) *
          (2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2))
        (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A ⊕
        Xa) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) |t| γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
    ‖nrun (prims (R := R) D en x) (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) ∘L
        (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε + ε' := by
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, -⟩ := binary_simulation_signed (R := R) D en σ hσ
    hs hrange hb c0 hc0 hdec x hH hrow hcol γ t ε ζ hγ hγ1 hε hε1 hζ hζ1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => (hc p).trans (hcalls p), hg, hgates, ?_, ?_⟩
  · rw [Fintype.card_sum, hcard]
  · generalize NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) = U at herr ⊢
    generalize binarySimSigned k b σ hσ s γ c0 t ε ζ = C at hvalid herr ⊢
    have hpu := prims_isUnitary (R := R) D en x
    generalize prims (R := R) D en x = prim at hpu herr ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ U herr
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end Endpoints

section Budgets

set_option maxHeartbeats 1000000 in
/-- **The gate budget from binary sparse oracles over a finite gate set for every real time**
(equation `hs:eq:gate-total`, with the binary-data construction). The rescaling `γ` and its
bounds are those of `binary_simulation_budget_signed` (the released budget for `|t|`): `γ` is
chosen from `s`, `|t|` and `ε` before the gate set, the synthesis budget and the data, with
`d ≤ 4608 q`, `τ' ≤ √s q`, `2^m < 2 (2 + 4 τ' + √(6 τ'³/ε))` and `2^r ≤ 4 (4608 q + 1)`,
`q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`. For every gate set with a logarithmic synthesis
length `L ζ ≤ c₁ log(1/ζ) + c₀`, every synthesis budget `0 < ε' ≤ 1` and all data as in the
released budget, the synthesised signed circuit consists of valid gates of `𝒢` and primitive
calls, makes at most `55296 q` times `2` row, `2` column and `1` value calls, uses at most
`G (c₁ log((G+1)/ε') + c₀)` gates, where `G = 200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`
is the pre-synthesis budget, and has full-output error at most `ε + ε'` against `exp(-itĤ)`. -/
theorem binary_simulation_budget_synth_signed (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      time (s : ℝ) |t| γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) |t| γ + Real.sqrt (6 * time (s : ℝ) |t| γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) ∧
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
        221184 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ ≤ ε →
        (∀ i ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
            55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) ∧
        (nGatesN (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) |t| γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) *
            (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s |t|
                  (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) |t| γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) + 1) / ε') +
              c₀) ∧
        ‖nrun (prims (R := R) D en x)
              (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤
          ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget_signed.{u, v, w} s hs1 t ε hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb c0
    hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨hvalid, -⟩ := binary_simulation_signed (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x
    hH hrow hcol γ t ε ζ hγ hγ1 hε hε1 hζ hζ1 hζε'
  obtain ⟨hcalls, hgates, herr⟩ := hall (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hH hrow
    hcol ζ hζ hζ1 hζε
  obtain ⟨hv, hk, hg, hc⟩ := synthBudget_spec hS hε' _ hvalid
  refine ⟨hv, hk, fun p => by rw [hc p]; exact hcalls p, ?_, ?_⟩
  · refine (Nat.cast_le.mpr hg).trans ?_
    exact gates_log_le hc₀ hc₁ hL hε' hε'1 _ _ hgates
  · generalize NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) = U at herr ⊢
    generalize binarySimSigned k b σ hσ s γ c0 t ε ζ = C at hvalid herr ⊢
    have hpu := prims_isUnitary (R := R) D en x
    generalize prims (R := R) D en x = prim at hpu herr ⊢
    refine synthBudget_error hS hε' C hvalid prim hpu _ ?_ U herr
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

/-- **Equation `hs:eq:gate-binary` after finite-gate-set synthesis for every real time**
(Theorem `hs:thm:gates`, binary sparse data). For `s ≥ 1`, every real `t`, `0 < ε ≤ 1/2` and
`q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`, the rescaling `γ` of
`binary_simulation_budget_synth_signed` satisfies: under `Synthesis 𝒢 Xa L` with
`L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` (`c₀, c₁ ≥ 0` the synthesis constants, not the decoder
scale `c₀`), for every synthesis accuracy `ε' ∈ (0, 1]`, all binary sparse data with `s = 2^σ`
slots, `k`-bit indices and `b ≤ b_data` stored bits, every decoder scale `c₀ > 0` of bit length
`b_data`, every admissible input and every arithmetic accuracy
`ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`, the synthesised signed circuit uses at most
`10¹⁵ q (𝔟_H+1)³ (c₁ (36 (𝔟_H+1) + log(1/ε')) + c₀)` gates of `𝒢`,
`𝔟_H = bitH b_data (2^k) q ε`, and every conclusion of `binary_simulation_budget_synth_signed`
holds: valid gates of `𝒢` and primitive calls, at most `55296 q` times `2` row, `2` column and
`1` value calls, the gate count `G (c₁ log((G+1)/ε') + c₀)`, and full-output error at most
`ε + ε'` against `exp(-itĤ)` with the clean synthesis ancillas. -/
theorem binary_simulation_budget_synth_bits_signed (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      time (s : ℝ) |t| γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) |t| γ + Real.sqrt (6 * time (s : ℝ) |t| γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) ∧
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
        ∀ bd : ℕ, b ≤ bd → HasBits bd c0 →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ ≤ ε →
        ε ≤ 442368 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ →
        (nGatesN (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 *
            (c₁ * (36 * (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t|
              (Real.log (1 / ε))) ε + 1) + Real.log (1 / ε')) + c₀) ∧
        (∀ i ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
            55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) ∧
        (nGatesN (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) |t| γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) *
            (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s |t|
                  (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) |t| γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) + 1) / ε') +
              c₀) ∧
        ‖nrun (prims (R := R) D en x)
              (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤
          ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget_synth_signed.{u, v, w, x} s hs1 t ε hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hv, hk, hcalls, hgates, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D en σ hσ hs
    hrange hb c0 hc0 hdec x hH hrow hcol ζ hζ hζ1 hζε
  obtain ⟨-, hG0, hG⟩ := hs_gates_le s k b σ bd hs hσ hbd hγ hγ1 hγs (abs_nonneg t) hε hε2 hbits
    hc0 hζ hζlo hτq hm hr
  refine ⟨hgates.trans ?_, hv, hk, hcalls, hgates, herr⟩
  have hε1 : ε ≤ 1 := by linarith
  have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) :=
    (Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)).trans (le_shape _ _ _ (abs_nonneg t))
  have hℓ : 1 / 2 ≤ Real.log (1 / ε) := by
    have h1 : Real.log 2 ≤ Real.log (1 / ε) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
    have h2 := Real.log_two_gt_d9
    norm_num at h2
    linarith
  have hQ : 1 / 2 ≤ ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) :=
    hℓ.trans (le_shape _ _ _ (abs_nonneg t))
  have hY1 : 1 ≤ (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hQY : ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ≤
      (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hB0 := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
  have hLB : Real.logb 2 ((ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) / ε) ≤
      bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε := by
    have h1 := logb_succ_nonneg (2 ^ k)
    have h2 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    unfold bitH
    linarith
  exact hs_synth_arith hG0 hG hQ hB0 hQY hY1 hLB hε' hε'1 hc₀ hc₁

/-- **The qubits and gates of `hs:thm:gates` over a finite gate set for binary sparse data in the
bit lengths, for every real time** (equations `hs:eq:gate-total` and `hs:eq:gate-binary` after
synthesis). For `s ≥ 1`, every real `t`, `0 < ε ≤ 1/2` and
`q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)`, the rescaling `γ` of
`binary_simulation_budget_synth_bits_signed` (chosen before the gate set, the synthesis budget
and the data) satisfies: under `Synthesis 𝒢 Xa L` with `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, for
every synthesis accuracy `ε' ∈ (0, 1]` and all data, inputs and accuracies as in
`binary_simulation_bits_signed`, the synthesised signed circuit uses at most
`10¹⁵ q (𝔟_H+1)³ (c₁ (36 (𝔟_H+1) + log(1/ε')) + c₀)` gates of `𝒢` on at most
`4·10⁶ (𝔟_H + 1)³ + |Xa|` qubits, `𝔟_H = bitH b_data (2^k) q ε`; its register (the native one
and `Xa`) has exactly `k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3) + |Xa|` qubits;
and every other conclusion of `binary_simulation_budget_synth_bits_signed` holds. -/
theorem binary_simulation_budget_synth_bits_qubits_signed (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      (fDeg (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℝ) ≤
        4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      time (s : ℝ) |t| γ ≤ Real.sqrt s * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) ∧
      ((2 ^ simM (time (s : ℝ) |t| γ) (ε / 2) : ℕ) : ℝ) <
        2 * (2 + 4 * time (s : ℝ) |t| γ + Real.sqrt (6 * time (s : ℝ) |t| γ ^ 3 / ε)) ∧
      ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
        4 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) ∧
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
        ∀ bd : ℕ, b ≤ bd → HasBits bd c0 →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ ≤ ε →
        ε ≤ 442368 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) * ζ →
        (nGatesN (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          10 ^ 15 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 *
            (c₁ * (36 * (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t|
              (Real.log (1 / ε))) ε + 1) + Real.log (1 / ε')) + c₀) ∧
        (Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) : ℝ) ≤
          4 * 10 ^ 6 *
            (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε))) ε + 1) ^ 3 +
            Fintype.card Xa ∧
        Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ)
            (ε / 2)) (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
            (binArith k b (γ * Real.sqrt s * c0) ζ).bP
            (binArith k b (γ * Real.sqrt s * c0) ζ).A ⊕ Xa) =
          k + (2 * (k + 1) + 3 * simM (time (s : ℝ) |t| γ) (ε / 2) +
              6 * simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 3) +
            (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) + Fintype.card Xa ∧
        (∀ i ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ), i.Valid) ∧
        (∀ g, NInstr.gate g ∈ synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ) →
          GateOf 𝒢 g) ∧
        (∀ p : Query → Bool,
          (nCallsN p (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
            55296 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) *
              (2 * (if p Query.rowLocation then 1 else 0) +
                2 * (if p Query.columnLocation then 1 else 0) +
                (if p Query.value then 1 else 0))) ∧
        (nGatesN (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s |t| (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) |t| γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) *
            (c₁ * Real.log ((200 * (4608 * ImprovedPrecisionBudget.shape s |t|
                  (Real.log (1 / ε)) + 1) *
              ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
                  (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
                simM (time (s : ℝ) |t| γ) (ε / 2) +
                simR (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2) + 1) + 1) / ε') +
              c₀) ∧
        ‖nrun (prims (R := R) D en x)
              (synthBudget hS ε' (binarySimSigned k b σ hσ s γ c0 t ε ζ)) ∘L
            (cleanEmb (X := Xa) ∘L sysEmb (io (P := Reg (Fin k) R))) -
            (cleanEmb ∘L sysEmb (io (P := Reg (Fin k) R))) ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤
          ε + ε' := by
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budget_synth_bits_signed.{u, v, w, x} s hs1 t ε hε hε2
  refine ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, ?_⟩
  intro Xa _ _ 𝒢 L hS c₀ c₁ hc₀ hc₁ hL ε' hε' hε'1 X n _ _ k b R _ _ _ D en σ hσ hs hrange hb
    c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  obtain ⟨hG, hv, hk, hcalls, hgates, herr⟩ := hall hS hc₀ hc₁ hL ε' hε' hε'1 (R := R) D en σ hσ
    hs hrange hb c0 hc0 hdec x hH hrow hcol bd hbd hbits ζ hζ hζ1 hζε hζlo
  have hcard := card_binary_register k b (binArith k b (γ * Real.sqrt s * c0) ζ).bT
    (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A
    (width (s : ℝ) γ) (time (s : ℝ) |t| γ) (moment γ) (ε / 2)
  have hq := binary_register_le s k b σ bd (c0 := c0) hs hσ hbd hγ1 hγs (abs_nonneg t) hε hε2
    hbits hc0 hζ hζlo hτq hm hr
  refine ⟨hG, ?_, ?_, hv, hk, hcalls, hgates, herr⟩
  · rw [Fintype.card_sum, Nat.cast_add, hcard]
    linarith
  · rw [Fintype.card_sum, hcard]

end Budgets

end

end SparseHamiltonian.GateSigned
