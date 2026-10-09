import GateEfficientMesh.Binary

/-!
# Binary sparse data under integrated certificates: the endpoints

* `binary_time_simulation_certified`: the time-dependent part of Theorem `hs:thm:gates` from
  time-indexed binary sparse oracles (manuscript v15, lines 2754-2799 and the formalisation
  summary at lines 1447-1459) with the integrated certificate of the paragraph "Regularity and
  coherent parameters" (lines 2420-2434) in place of the Lipschitz bound of the released
  `GateBinary.binary_time_simulation`: the released circuit `binaryTimeSim` and counts, and
  full-output error at most `ε` against every propagator of the lifted matrix path whenever
  `∑_r ∫_{rt/2^m}^{(r+1)t/2^m} ‖H(u) - H̃_r‖ du ≤ ε/4`; the slot exponent is constrained only by
  the subdivision condition `steps τ' (ε/12) ≤ 2^m`.
* `binary_time_simulation_budget_certified`: the budget form of the released
  `GateBinary.binary_time_simulation_budget` (one rescaling `γ` chosen from `s`, `t` and `ε`
  before the data, `d ≤ 4608 q`), with the certificate in place of the Lipschitz path and the
  freezing condition; the regularity of the path enters neither the counts nor `m`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateCircuit.Sim (iota0 fDeg simR io Wire)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open NativeSparseBlockEncoding (Data Query)
open MeasureTheory Set
open TimeDependentExtensions (IsPiecewisePropagator)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct BigOperators

universe u v w

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **Gate-efficient time-dependent sparse simulation from binary data under the integrated
certificate** (Theorem `hs:thm:gates`, time-dependent part, for time-indexed binary sparse
oracles, before finite-set synthesis). For the released data format (`k`-bit indices, `s = 2^σ`
slots on the lowest `σ` index bits, entries `c₀ (X + i Y)` with `b`-bit two's complement
components, `b ≥ 1`, `c₀ > 0`), an input `x` whose `2^m` samples `H̃_r = D.matrix (x, r)` are
Hermitian with row and column norms at most one, a rescaling `0 < γ ≤ 1`, accuracies
`0 < ε ≤ 1`, `0 < ζ ≤ 1`, the subdivision condition `steps τ' (ε/12) ≤ 2^m` (`τ' = √s t/γ`) and
the arithmetic budget `48 d ζ ≤ ε`, the circuit `binaryTimeSim` consists of valid instructions,
makes `12 d` times `2` row-location, `2` column-location and `1` value calls, has at most
`200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d (56 k + 2 |circ| + 2 bP + bT + 1)` elementary gates
and the stated qubits, with `d ≤ 128 (τ' q̄ + Q (1 + log (12/ε)))` and `2d + 2 ≤ 2^r ≤ 4 (d+1)`;
and its full output on the system embedding is within `ε` of `U(t)` for every matrix path `H`
that is Hermitian at almost every time of `[0, t]` with `u ↦ H(u)` interval integrable (as
operators) and every integral-sense propagator `U` of the lifted path `u ↦ qlift en (H u)`, and
for every piecewise matrix path with one piece per slot and every classical piecewise
propagator of its lift, whenever the certificate
`∑_r ∫_{rt/2^m}^{(r+1)t/2^m} ‖H(u) - H̃_r‖ du` is at most `ε / 4`. -/
theorem binary_time_simulation_certified (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    (hrow : ∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (hcol : ∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (t γ ε ζ : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hCayley : TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binaryTimeSim k b m σ hσ s γ c0 t ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) =
      12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
        (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
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
    (∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ᵐ u, u ∈ Icc 0 t → (H u).IsHermitian) →
      IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 t →
      ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (H u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 4 →
      IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U t →
      ‖nrun (primsT (R := R) D en x) (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ∘L
          sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ ≤ ε) ∧
    (∀ (Hp : ℕ → ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
      (∀ r < 2 ^ m, ∀ u ∈ Icc (slotMesh t m r) (slotMesh t m (r + 1)), (Hp r u).IsHermitian) →
      (∀ r < 2 ^ m, IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (Hp r u))
        volume (slotMesh t m r) (slotMesh t m (r + 1))) →
      ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
          ‖SparseStateOverlap.matrixOperator (Hp r u) -
            SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 4 →
      IsPiecewisePropagator
        (fun r u => qlift (R := R) en (SparseStateOverlap.matrixOperator (Hp r u)))
        (slotMesh t m) (2 ^ m) U →
      ‖nrun (primsT (R := R) D en x) (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ∘L
          sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ ≤ ε) := by
  obtain ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, herr⟩ := binary_slot_bounds (R := R) D en
    σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol t γ ε ζ ht hγ hγ1 hε hε1 hζ hζ1 hCayley hζε
  refine ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, fun H U hH hint hcert hU => ?_,
    fun Hp U hH hint hcert hU => ?_⟩
  · have h1 := herr (U t)
    have h2 := (norm_sub_rev (slotEvolution (HsT (R := R) D en x) t m) (U t)).trans_le
      (binary_slot_error_integral (R := R) D en x hHerm ht H U hH hint hU)
    linarith
  · have h1 := herr (U t)
    have h2 := (norm_sub_rev (slotEvolution (HsT (R := R) D en x) t m) (U t)).trans_le
      (binary_slot_error_piecewise (R := R) D en x hHerm ht Hp U hH hint hU)
    linarith

end Main

/-- **The budget of the time-dependent binary construction under the integrated certificate**
(Theorem `hs:thm:gates`, time-dependent part, before finite-set synthesis, with the rescaled
sparse parameters of `hs:thm:time`). For `s ≥ 1` slots, a time `t ≥ 0` and `0 < ε ≤ 1`, put
`q = √s t + √(s t log(2/ε)) + log(2/ε)`. There is one rescaling `γ ∈ (0, 1]` with `γ √s ≥ 1`,
chosen from `s`, `t` and `ε` before the data, the input, the path and the slot exponent, with
filter degree `d ≤ 4608 q`, such that for all time-indexed binary sparse data with `s = 2^σ`
slots and `2^m` time slots, every input with Hermitian samples of row and column norms at most
one, the subdivision condition `steps τ' (ε/12) ≤ 2^m` (`τ' = √s t/γ`) and every arithmetic
accuracy `0 < ζ ≤ 1` with `221184 q ζ ≤ ε`, the circuit `binaryTimeSim` makes at most `55296 q`
times `2` row-location, `2` column-location and `1` value calls, uses at most
`200 (4608 q + 1) (G_C + (σ + 1) + (k + 1) + m + r + 1)` elementary gates with
`G_C = privGates` and `2^r ≤ 4 (4608 q + 1)`, and its full output is within `ε` of `U(t)` for
every integral-sense propagator `U` of the lift of every matrix path that is Hermitian almost
everywhere and interval integrable with certificate at most `ε / 4`. Neither the regularity of
the path nor the sample errors enter the counts or the choice of `m`. -/
theorem binary_time_simulation_budget_certified (s : ℕ) (hs1 : 1 ≤ s) (t ε : ℝ) (ht : 0 ≤ t)
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
        TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m →
        ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
        221184 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ ≤ ε →
        (∀ p : Query → Bool, (nCallsN p (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) : ℝ) ≤
          55296 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
            (2 * (if p Query.rowLocation then 1 else 0) +
              2 * (if p Query.columnLocation then 1 else 0) +
              (if p Query.value then 1 else 0))) ∧
        (nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) : ℝ) ≤
          200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
            ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
                (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
              simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) ∧
        ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
          4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) ∧
        ∀ (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R),
          (∀ᵐ u, u ∈ Icc 0 t → (H u).IsHermitian) →
          IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 t →
          ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
              ‖SparseStateOverlap.matrixOperator (H u) -
                SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 4 →
          IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)))
            U t →
          ‖nrun (primsT (R := R) D en x) (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ∘L
              sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ ≤
            ε := by
  have hs1' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hε2 : 0 < ε / 2 := by linarith
  -- The rescaling of the released time-dependent budget; it depends on `s`, `t` and `ε` only.
  obtain ⟨γ, hγ, hγ1, hγs, -, -, hdeg, -⟩ :=
    SlotSim.sparse_counts 0 (s : ℝ) 1 t (ε / 2) hs1' zero_le_one ht hε2 (by linarith)
  have ht' : 1 * Real.sqrt s / γ * t = time (s : ℝ) t γ := by
    unfold time
    ring
  have he4 : ε / 2 / 2 = ε / 4 := by ring
  have hl : (1 : ℝ) / (ε / 2) = 2 / ε := by
    field_simp
  rw [ht', he4, one_mul, hl] at hdeg
  refine ⟨γ, hγ, hγ1, hγs, hdeg, ?_⟩
  intro X n _ _ k b m R _ _ _ D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow hcol hCayley ζ hζ
    hζ1 hζε
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤
      ε := by
    nlinarith [hdeg, hζ]
  obtain ⟨-, hcalls, hgates, -, -, -, hr2, herr, -⟩ :=
    binary_time_simulation_certified (R := R) D en σ hσ hs hrange hb c0 hc0 hdec x hHerm hrow
      hcol t γ ε ζ ht hγ hγ1 hε hε1 hζ hζ1 hCayley hζε'
  refine ⟨fun p => ?_, ?_, ?_, herr⟩
  · rw [hcalls p]
    generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = dn at hdeg ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) t (Real.log (2 / ε)) = q at hdeg ⊢
    push_cast
    have hc : (0 : ℝ) ≤ 2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) := by
      split_ifs <;> norm_num
    generalize (2 * (if p Query.rowLocation then 1 else 0) +
        2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) : ℝ) =
      c at hc ⊢
    have h := mul_le_mul_of_nonneg_right hdeg hc
    linarith only [h]
  · have hpg : privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
        (binArithT k b m (γ * Real.sqrt s * c0) ζ) =
        2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
          (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
            (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1) := by
      rw [privGates, show (sparseOpT k b m (γ * Real.sqrt s * c0)).V = computeVT k b m from rfl,
        computeVT_nGates]
    rw [hpg]
    generalize 2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
        (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1) = G at hgates ⊢
    generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = dn
      at hdeg hgates ⊢
    generalize nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) = Gt at hgates ⊢
    generalize simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = N at hgates ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) t (Real.log (2 / ε)) = q at hdeg ⊢
    have hg : (Gt : ℝ) ≤ 200 * ((dn : ℝ) + 1) * ((k : ℝ) + 1 + m + N + 1) +
        84 * (dn : ℝ) * ((σ : ℝ) + 1) + 6 * (dn : ℝ) * G := by
      exact_mod_cast hgates
    have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
    have hA0 : (0 : ℝ) ≤ (k : ℝ) + 1 + m + N + 1 := by positivity
    have hB0 : (0 : ℝ) ≤ (σ : ℝ) + 1 := by positivity
    have hd0' : (0 : ℝ) ≤ (dn : ℝ) := Nat.cast_nonneg _
    have h1 := mul_le_mul_of_nonneg_right hdeg hA0
    have h2 := mul_le_mul_of_nonneg_right hdeg hB0
    have h3 := mul_le_mul_of_nonneg_right hdeg hG0
    nlinarith only [hg, h1, h2, h3, hG0, hA0, hB0, hd0']
  · generalize fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = dn
      at hdeg hr2 ⊢
    generalize simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) = N at hr2 ⊢
    generalize ImprovedPrecisionBudget.shape (s : ℝ) t (Real.log (2 / ε)) = q at hdeg ⊢
    have h : ((2 ^ N : ℕ) : ℝ) ≤ 4 * ((dn : ℝ) + 1) := by exact_mod_cast hr2
    linarith only [h, hdeg]

end

end SparseHamiltonian.GateMesh
