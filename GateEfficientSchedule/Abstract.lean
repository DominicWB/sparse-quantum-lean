import GateEfficientSchedule.Endpoint
import GateEfficientRemarks.Abstract

/-!
# Lemma `hs:lem:abstract` with the manuscript's schedule and the count `hs:eq:explicitcount`

Lemma `hs:lem:abstract` (the general boundary-resolvent simulation lemma): let `D₀` be unitary,
`J` a known isometry, `h = h†` with `‖h‖ ≤ 1`, and let the interface `hs:eq:interface` hold for
an integer `Q ≥ 1` and a real `0 < ν ≤ Q`. For a known `α > 0`, `H = α h` and `W = α |t| ν`,
simulation of `e^{-itH}` to error `ε ≤ 1/2` uses `O(W + Q log(1/ε))` calls of `D₀`, `D₀†` and their
coherent controls. Its proof takes the filter tolerance `δ = ε/8` in `hs:eq:kchoice` and the
Cayley discretisation error `ε/4`, so the ideal-gate error is at most `ε/2`, with at most
(`hs:eq:explicitcount`)

`6 (32 Q - 1) ⌈4 W / Q + log₂(4096 / ε)⌉`

calls. The released form `GateRemarks.abstract_simulation` (library `GateEfficientRemarks`) runs
the released circuit, with its own schedule, and bounds the count by `3840 (W + Q log(1/ε))`. This
module runs the circuit `simCircuitMs` of the manuscript's schedule (`hs:eq:gate-schedule`,
`hs:eq:gate-clocks`) through the same interface mapping: the compressed second moment in the
Loewner order (`GateRemarks.second_moment_iff`), and for `t < 0` the circuit for `|t|` with `D`
and `D†` exchanged (`GateRemarks.flipDs`), whose interface holds for `D†` and `-h`
(`GateRemarks.transfer_*`).

* `absCircuitMs a α t Q ν ε`: the circuit for every real time `t`;
* `degreeMs_cost_le`: `6 d ≤ 3880 (W + Q log(1/ε))` for the manuscript's degree and
  `0 < ε ≤ 1/2`, the form of `hs:eq:abstractcost` (`logb_4096_eq`: `log₂(4096/ε) = 12 +
  log(1/ε)/log 2`);
* `abstract_simulation_ms`: the lemma for any real `Q ≥ 1`, with exactly `6d` private calls and
  `12d` calls of `U_J` or `U_J†`, `d = degreeMs Q W ε`, the counts at most `3880 (W + Q log(1/ε))`
  and `7760 (W + Q log(1/ε))`, the gate, wire and register bounds of the circuit, the slot count
  of `hs:eq:gate-clocks` for the time `α|t|` (which enters neither `d` nor its bound), and
  full-output error at most `ε/2` against `exp(-it (α h))` on clean inputs;
* `abstract_simulation_ms_explicit`: at an integer `Q ≥ 1`, exactly
  `6 (32 Q - 1) ⌈4 W / Q + log₂(4096 / ε)⌉` private calls (`hs:eq:explicitcount`) and twice as
  many calls of `U_J` or `U_J†`, with error at most `ε/2`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateRemarks
open scoped InnerProduct

/-! ### The constant of `hs:eq:abstractcost` for the manuscript's degree -/

/-- `log₂(4096/ε) = 12 + log(1/ε)/log 2`. -/
theorem logb_4096_eq (ε : ℝ) (hε : 0 < ε) :
    Real.logb 2 (4096 / ε) = 12 + Real.log (1 / ε) / Real.log 2 := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Real.logb, show (4096 : ℝ) / ε = 2 ^ 12 * (1 / ε) by ring,
    Real.log_mul (by positivity) (by positivity), Real.log_pow]
  field_simp
  push_cast
  ring

/-- **The cost of `hs:eq:abstractcost` for the manuscript's degree**: for `1 ≤ Q`, `0 ≤ W` and
`0 < ε ≤ 1/2`, `6 d ≤ 3880 (W + Q log(1/ε))` with `d = degreeMs Q W ε` (from
`d ≤ 128 W + 32 Q (log₂(4096/ε) + 1)` and `log 2 > 2688/3880`). -/
theorem degreeMs_cost_le (Q W ε : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    6 * (degreeMs Q W ε : ℝ) ≤ 3880 * (W + Q * Real.log (1 / ε)) := by
  have hd := degreeMs_le Q W ε hQ hW hε (by linarith)
  rw [logb_4096_eq ε hε] at hd
  have hl2 := Real.log_two_gt_d9
  norm_num at hl2
  have hl2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have key : 192 * (13 + Real.log (1 / ε) / Real.log 2) ≤ 3880 * Real.log (1 / ε) := by
    have e : 192 * (13 + Real.log (1 / ε) / Real.log 2) * Real.log 2 =
        2496 * Real.log 2 + 192 * Real.log (1 / ε) := by
      field_simp
      ring
    have h1 : 192 * (13 + Real.log (1 / ε) / Real.log 2) * Real.log 2 ≤
        3880 * Real.log (1 / ε) * Real.log 2 := by
      rw [e]
      have hLnn : 0 ≤ Real.log (1 / ε) := by linarith
      have hc : 0 ≤ 3880 * Real.log 2 - 2688 := by linarith
      nlinarith [mul_nonneg hLnn hc]
    exact le_of_mul_le_mul_right h1 hl2pos
  have hQk := mul_le_mul_of_nonneg_left key (by linarith : (0 : ℝ) ≤ Q)
  have e1 : 128 * W + 32 * Q * (12 + Real.log (1 / ε) / Real.log 2 + 1) =
      128 * W + Q * (32 * (13 + Real.log (1 / ε) / Real.log 2)) := by ring
  have e2 : Q * (192 * (13 + Real.log (1 / ε) / Real.log 2)) =
      6 * (Q * (32 * (13 + Real.log (1 / ε) / Real.log 2))) := by ring
  have e3 : Q * (3880 * Real.log (1 / ε)) = 3880 * (Q * Real.log (1 / ε)) := by ring
  rw [e1] at hd
  rw [e2, e3] at hQk
  have e4 : 3880 * (W + Q * Real.log (1 / ε)) = 3880 * W + 3880 * (Q * Real.log (1 / ε)) := by
    ring
  rw [e4]
  linarith

/-! ### The lemma -/

/-- **The circuit of Lemma `hs:lem:abstract` with the manuscript's schedule** for the real time
`t`: `simCircuitMs` for the time `α |t|`, the width `Q` and the moment `ν`, with the private calls
`D` and `D†` exchanged when `t < 0`. It depends only on these public numbers. -/
def absCircuitMs (a : ℕ) (α t Q ν ε : ℝ) : List (Instr (SimWireMs a Q (α * |t|) ν ε)) :=
  if 0 ≤ t then simCircuitMs a (α * |t|) Q ν ε else flipDs (simCircuitMs a (α * |t|) Q ν ε)

set_option maxRecDepth 8192 in
/-- **Lemma `hs:lem:abstract` with the manuscript's schedule** (exact gates, every real time).
Let `U_J` and `D` be unitaries on `a` ancilla qubits and the system `P` (any complex Hilbert
space), `J = U_J ι₀` the known isometry, `R₁` the two-sided inverse of `1 - D`, and `h`
self-adjoint with `‖h‖ ≤ 1`. Assume the interface `hs:eq:interface`: `J† R₁ J = (1 + i h)/2`,
the compressed second moment `J† R₁† R₁ J ≤ (ν/2) 1` in the Loewner order, `‖R₁‖ ≤ Q`, `1 ≤ Q`
and `0 < ν ≤ Q`. For a known `α > 0`, every real time `t` and `0 < ε ≤ 1/2`, with `W = α |t| ν`
and the manuscript's `d = degreeMs Q W ε = k (⌈32Q⌉ - 1)`, `k = ⌈4W/Q + log₂(4096/ε)⌉`, the
circuit `absCircuitMs a α t Q ν ε` consists of valid instructions, makes exactly `6d` private
calls, each a call of `D` or `D†` with at most one control, with `6d ≤ 3880 (W + Q log(1/ε))`,
and exactly `12d` calls of `U_J` or `U_J†` (at most `7760 (W + Q log(1/ε))`), uses at most
`200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubit wires besides the system, and
its full output on clean inputs is within `ε/2` of `exp(-it (α h))` (filter `2 · ε/8`, Cayley
discretisation `ε/4`). The degree satisfies `d ≤ 128 W + 32 Q (log₂(4096/ε) + 1)`, whose right
side does not involve the slot register; `2^m` is the least power of two at least
`max{2, 4α|t|, √((α|t|)³/(3ε))}` (`hs:eq:gate-clocks`), and `2d + 2 ≤ 2^r ≤ 4 (d+1)`. -/
theorem abstract_simulation_ms (a : ℕ) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P] (UJ D R1 : Anc a P →L[ℂ] Anc a P)
    (h : P →L[ℂ] P) (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hSelf : star h = h) (hh : ‖h‖ ≤ 1)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • h))
    (Q ν : ℝ) (hQ : 1 ≤ Q) (hν : 0 < ν) (hνQ : ν ≤ Q)
    (hMoment : (UJ ∘L iota0)† ∘L R1† ∘L R1 ∘L (UJ ∘L iota0) ≤
      ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P))
    (hR1 : ‖R1‖ ≤ Q) (α t ε : ℝ) (hα : 0 < α) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ g ∈ absCircuitMs a α t Q ν ε, g.Valid Wire.anc) ∧
    nPriv (absCircuitMs a α t Q ν ε) = 6 * degreeMs Q (α * |t| * ν) ε ∧
    (nPriv (absCircuitMs a α t Q ν ε) : ℝ) ≤ 3880 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nUJ (absCircuitMs a α t Q ν ε) = 12 * degreeMs Q (α * |t| * ν) ε ∧
    (nUJ (absCircuitMs a α t Q ν ε) : ℝ) ≤ 7760 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nGates (absCircuitMs a α t Q ν ε) ≤
      200 * (degreeMs Q (α * |t| * ν) ε + 1) *
        (a + slotMs (α * |t|) ε + rMs Q (α * |t|) ν ε + 1) ∧
    Fintype.card (SimWireMs a Q (α * |t|) ν ε) =
      2 * a + 3 * slotMs (α * |t|) ε + 6 * rMs Q (α * |t|) ν ε + 3 ∧
    ‖run (simSem UJ D) (absCircuitMs a α t Q ν ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • h))‖ ≤ ε / 2 ∧
    (degreeMs Q (α * |t| * ν) ε : ℝ) ≤
      128 * (α * |t| * ν) + 32 * Q * (Real.logb 2 (4096 / ε) + 1) ∧
    meshMs (α * |t|) ε ≤ 2 ^ slotMs (α * |t|) ε ∧
    (∀ j : ℕ, meshMs (α * |t|) ε ≤ 2 ^ j → slotMs (α * |t|) ε ≤ j) ∧
    2 * degreeMs Q (α * |t| * ν) ε + 2 ≤ 2 ^ rMs Q (α * |t|) ν ε ∧
    2 ^ rMs Q (α * |t|) ν ε ≤ 4 * (degreeMs Q (α * |t| * ν) ε + 1) := by
  have hε1 : ε ≤ 1 := by linarith
  have hτ : 0 ≤ α * |t| := mul_nonneg hα.le (abs_nonneg t)
  have hW0 : 0 ≤ α * |t| * ν := mul_nonneg hτ hν.le
  have hUJ1 : UJ† ∘L UJ = 1 := by
    rw [← star_eq_adjoint, ← mul_def]
    exact hUJ.1
  have hJ : (UJ ∘L iota0 (a := a) (P := P))† ∘L (UJ ∘L iota0) = 1 := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc (UJ†) UJ iota0, hUJ1,
      show (1 : Anc a P →L[ℂ] Anc a P) ∘L iota0 = iota0 from id_comp _, iota0_isometry]
  have hmom : ‖R1 ∘L (UJ ∘L iota0 (a := a) (P := P))‖ ^ 2 ≤ ν / 2 :=
    (second_moment_iff R1 (UJ ∘L iota0) hν.le).mp hMoment
  have hdc := degreeMs_cost_le Q (α * |t| * ν) ε hQ hW0 hε hε2
  -- the counts in the form of `hs:eq:abstractcost`
  have hcost : ∀ n : ℕ, n = 6 * degreeMs Q (α * |t| * ν) ε →
      (n : ℝ) ≤ 3880 * (α * |t| * ν + Q * Real.log (1 / ε)) := by
    intro n hn
    rw [hn, Nat.cast_mul, Nat.cast_ofNat]
    exact hdc
  have hcostJ : ∀ n : ℕ, n = 12 * degreeMs Q (α * |t| * ν) ε →
      (n : ℝ) ≤ 7760 * (α * |t| * ν + Q * Real.log (1 / ε)) := by
    intro n hn
    rw [hn, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  by_cases ht : 0 ≤ t
  · obtain ⟨hvalid, hP, hU, hG, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
      gate_efficient_simulation_ms a UJ D R1 h hUJ hD (α * |t|) Q ‖R1 ∘L (UJ ∘L iota0)‖ ν ε
        hτ hQ hRight hLeft hR1 hBoundary hSelf hh le_rfl hmom hνQ hε hε1
    have hc : absCircuitMs a α t Q ν ε = simCircuitMs a (α * |t|) Q ν ε := if_pos ht
    rw [hc, ← exponent_nonneg α t ht h]
    exact ⟨hvalid, hP, hcost _ hP, hU, hcostJ _ hU, hG, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩
  · have ht' : t < 0 := lt_of_not_ge ht
    obtain ⟨hvalid, hP, hU, hG, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
      gate_efficient_simulation_ms a UJ (D†) (1 - R1) (-h) hUJ (transfer_unitary D hD)
        (α * |t|) Q ‖(1 - R1) ∘L (UJ ∘L iota0)‖ ν ε hτ hQ
        (transfer_right D R1 hD hRight hLeft) (transfer_left D R1 hD hRight hLeft)
        (by rw [transfer_norm D R1 hD hRight hLeft]; exact hR1)
        (transfer_boundary _ hJ R1 h hBoundary) (by rw [star_neg, hSelf])
        (by rw [norm_neg]; exact hh) le_rfl
        (by rw [transfer_endpoint D R1 hD hRight hLeft]; exact hmom) hνQ hε hε1
    have hc : absCircuitMs a α t Q ν ε = flipDs (simCircuitMs a (α * |t|) Q ν ε) := if_neg ht
    have hexp : (-Complex.I * ((α * |t| : ℝ) : ℂ)) • (-h) =
        (-Complex.I * (t : ℂ)) • ((α : ℂ) • h) := exponent_neg α t ht' h
    rw [hexp] at herr
    rw [hc, run_flipDs, nPriv_flipDs, nUJ_flipDs, nGates_flipDs]
    refine ⟨valid_flipDs _ _ hvalid, hP, hcost _ hP, hU, hcostJ _ hU, hG, hW, ?_, hdeg, hm1, hm2,
      hr1, hr2⟩
    convert herr using 4

/-- **Lemma `hs:lem:abstract` with the count `hs:eq:explicitcount`**: at an integer `Q ≥ 1`, under
the hypotheses of `abstract_simulation_ms`, the circuit makes exactly
`6 (32 Q - 1) ⌈4 W / Q + log₂(4096 / ε)⌉` private calls and `12 (32 Q - 1) ⌈4 W / Q +
log₂(4096 / ε)⌉` calls of `U_J` or `U_J†`, `W = α |t| ν`, and its full output on clean inputs is
within `ε/2` of `exp(-it (α h))`. -/
theorem abstract_simulation_ms_explicit (a : ℕ) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P] (UJ D R1 : Anc a P →L[ℂ] Anc a P)
    (h : P →L[ℂ] P) (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hSelf : star h = h) (hh : ‖h‖ ≤ 1)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • h))
    (Q : ℕ) (ν : ℝ) (hQ : 1 ≤ Q) (hν : 0 < ν) (hνQ : ν ≤ Q)
    (hMoment : (UJ ∘L iota0)† ∘L R1† ∘L R1 ∘L (UJ ∘L iota0) ≤
      ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P))
    (hR1 : ‖R1‖ ≤ Q) (α t ε : ℝ) (hα : 0 < α) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    nPriv (absCircuitMs a α t Q ν ε) =
      6 * (32 * Q - 1) * ⌈4 * (α * |t| * ν) / Q + Real.logb 2 (4096 / ε)⌉₊ ∧
    nUJ (absCircuitMs a α t Q ν ε) =
      12 * (32 * Q - 1) * ⌈4 * (α * |t| * ν) / Q + Real.logb 2 (4096 / ε)⌉₊ ∧
    ‖run (simSem UJ D) (absCircuitMs a α t Q ν ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • h))‖ ≤ ε / 2 := by
  obtain ⟨-, hP, -, hU, -, -, -, herr, -⟩ :=
    abstract_simulation_ms a UJ D R1 h hUJ hD hRight hLeft hSelf hh hBoundary (Q : ℝ) ν
      (by exact_mod_cast hQ) hν hνQ hMoment hR1 α t ε hα hε hε2
  rw [degreeMs_natCast, depthMs] at hP hU
  refine ⟨?_, ?_, herr⟩
  · rw [hP]
    ring
  · rw [hU]
    ring

end

end SparseHamiltonian.GateSchedule
