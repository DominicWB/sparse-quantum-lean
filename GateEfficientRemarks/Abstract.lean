import GateEfficientRemarks.AbstractTransfer

/-!
# Lemma `hs:lem:abstract`: the general boundary-resolvent simulation lemma

Lemma `hs:lem:abstract` of the accompanying paper: let `D₀` be unitary, `J` a known isometry,
`h = h†` with `‖h‖ ≤ 1`, and let the interface `hs:eq:interface` hold,

`J† R₀(1) J = (I + i h)/2`, `J† R₀(1)† R₀(1) J ⪯ (ν/2) I`, `‖R₀(1)‖ ≤ Q`, `0 < ν ≤ Q`,

for `R₀(1) = (I - D₀)⁻¹` and an integer `Q ≥ 1` (any real `Q ≥ 1` in Lean); let `D₀`, `D₀†` and
their coherent controls be available.
For a known `α > 0`, `H = α h` and `W = α |t| ν`, simulating `e^{-itH}` to error `ε ≤ 1/2` uses
`O(W + Q log(1/ε))` calls of these unitaries, and the number of time-discretisation slots does
not multiply the query count.

The content of the lemma is the released exact-gate theorem
`GateCircuit.Sim.gate_efficient_simulation` (library `GateEfficientHamiltonian`): for `J = U_J ι₀`
with a supplied unitary `U_J`, the circuit `simCircuit a τ Q q̄ ε` makes exactly `6 d` private
calls (each a call of `D` or `D†` with at most one control) and has full-output error `ε`
against `exp(-iτh)` for `τ ≥ 0`, with `d ≤ 128 (τ q̄ + Q (1 + log(3/ε)))`. This file states the
lemma for every real `t`:

* `absCircuit a α t Q ν ε`: the released `simCircuit` for the time `α |t|`; for `t < 0` its
  private calls `D` and `D†` are exchanged (`flipDs`), which runs the released circuit with `D†`
  in place of `D`, for the interface of `D†` and `-h` (`AbstractTransfer`);
* `abstract_simulation`: the lemma, with every conclusion of the released theorem and the
  explicit form `6 d ≤ 3840 (W + Q log(1/ε))` of `hs:eq:abstractcost`
  (`one_add_log_le`, `abstract_cost_le`); the slot register is fixed by
  `steps(α|t|, ε/3) ≤ 2^m < 2 steps(α|t|, ε/3)` and enters neither `d` nor its bound.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct

/-! ### The constant of `hs:eq:abstractcost` -/

/-- `1 + log(3/ε) ≤ 5 log(1/ε)` for `0 < ε ≤ 1/2` (`hs:lem:abstract`). -/
theorem one_add_log_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    1 + Real.log (1 / (ε / 3)) ≤ 5 * Real.log (1 / ε) := by
  have h2 : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have hl2 := Real.log_two_gt_d9
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have h4 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith
  have e : Real.log (1 / (ε / 3)) = Real.log 3 + Real.log (1 / ε) := by
    rw [show 1 / (ε / 3) = 3 * (1 / ε) by field_simp,
      Real.log_mul (by norm_num) (by positivity)]
  rw [e]
  norm_num at hl2
  linarith

/-- **The cost of `hs:eq:abstractcost`**: if `d ≤ 128 (W + Q (1 + log(3/ε)))` with `W, Q ≥ 0`
and `0 < ε ≤ 1/2`, then `6 d ≤ 3840 (W + Q log(1/ε))` (`hs:lem:abstract`). -/
theorem abstract_cost_le {d W Q ε : ℝ} (hd : d ≤ 128 * (W + Q * (1 + Real.log (1 / (ε / 3)))))
    (hW : 0 ≤ W) (hQ : 0 ≤ Q) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    6 * d ≤ 3840 * (W + Q * Real.log (1 / ε)) := by
  have h1 := mul_le_mul_of_nonneg_left (one_add_log_le hε hε2) hQ
  nlinarith

/-! ### The lemma -/

/-- **The circuit of Lemma `hs:lem:abstract`** for the real time `t`: the released `simCircuit`
for the time `α |t|`, the accuracy `ε`, the width `Q` and the moment `ν`, with the private calls
`D` and `D†` exchanged when `t < 0`. It depends only on these public numbers. -/
def absCircuit (a : ℕ) (α t Q ν ε : ℝ) : List (Instr (SimWire a Q (α * |t|) ν ε)) :=
  if 0 ≤ t then simCircuit a (α * |t|) Q ν ε else flipDs (simCircuit a (α * |t|) Q ν ε)

/-- The evolution of `α h` at time `t ≥ 0` is that of `h` at time `α |t|`
(`hs:lem:abstract`). -/
theorem exponent_nonneg (α t : ℝ) (ht : 0 ≤ t) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (h : E →L[ℂ] E) :
    (-Complex.I * ((α * |t| : ℝ) : ℂ)) • h = (-Complex.I * (t : ℂ)) • ((α : ℂ) • h) := by
  rw [smul_smul, abs_of_nonneg ht]
  congr 1
  push_cast
  ring

/-- The evolution of `α h` at time `t < 0` is that of `-h` at time `α |t|`
(`hs:lem:abstract`). -/
theorem exponent_neg (α t : ℝ) (ht : t < 0) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (h : E →L[ℂ] E) :
    (-Complex.I * ((α * |t| : ℝ) : ℂ)) • (-h) = (-Complex.I * (t : ℂ)) • ((α : ℂ) • h) := by
  rw [smul_neg, ← neg_smul, smul_smul, abs_of_neg ht]
  congr 1
  push_cast
  ring

/-- **Lemma `hs:lem:abstract` (the general boundary-resolvent simulation lemma).** Let `U_J` and
`D` be unitaries on `a` ancilla qubits and the system `P` (any complex Hilbert space), `J = U_J ι₀`
the known isometry, `R₁` the two-sided inverse of `1 - D`, and `h` self-adjoint with
`‖h‖ ≤ 1`. Assume the interface `hs:eq:interface`: `J† R₁ J = (1 + i h)/2`, the compressed second
moment `J† R₁† R₁ J ≤ (ν/2) 1` in the Loewner order, `‖R₁‖ ≤ Q`, `1 ≤ Q` and `0 < ν ≤ Q`. For a
known `α > 0`, every real time `t` and `0 < ε ≤ 1/2`, the circuit `absCircuit a α t Q ν ε`
(fixed by the public numbers; `D` and `D†` exchanged for `t < 0`) consists of valid
instructions, makes exactly `6 d` private calls, each a call of `D` or `D†` with at most one
control, with `6 d ≤ 3840 (W + Q log(1/ε))` for `W = α |t| ν`, and exactly `12 d` calls of `U_J`
or `U_J†` (at most `7680 (W + Q log(1/ε))`), uses at most `200 (d+1)(a+m+r+1)` elementary gates
on `2a + 3m + 6r + 3` qubit wires besides the system, and its full output on clean inputs is
within `ε` of
`exp(-it (α h))`. The filter degree satisfies the released bound
`d ≤ 128 (α|t| ν + Q (1 + log(3/ε)))`, whose right-hand side does not involve the slot register;
the `2^m` time slots are fixed separately by `steps(α|t|, ε/3) ≤ 2^m < 2 steps(α|t|, ε/3)`, and
`2d + 2 ≤ 2^r ≤ 4 (d+1)`. -/
theorem abstract_simulation (a : ℕ) {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (UJ D R1 : Anc a P →L[ℂ] Anc a P) (h : P →L[ℂ] P)
    (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hSelf : star h = h) (hh : ‖h‖ ≤ 1)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • h))
    (Q ν : ℝ) (hQ : 1 ≤ Q) (hν : 0 < ν) (hνQ : ν ≤ Q)
    (hMoment : (UJ ∘L iota0)† ∘L R1† ∘L R1 ∘L (UJ ∘L iota0) ≤
      ((ν / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P))
    (hR1 : ‖R1‖ ≤ Q) (α t ε : ℝ) (hα : 0 < α) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ g ∈ absCircuit a α t Q ν ε, g.Valid Wire.anc) ∧
    nPriv (absCircuit a α t Q ν ε) = 6 * fDeg Q (α * |t|) ν ε ∧
    (nPriv (absCircuit a α t Q ν ε) : ℝ) ≤ 3840 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nUJ (absCircuit a α t Q ν ε) = 12 * fDeg Q (α * |t|) ν ε ∧
    (nUJ (absCircuit a α t Q ν ε) : ℝ) ≤ 7680 * (α * |t| * ν + Q * Real.log (1 / ε)) ∧
    nGates (absCircuit a α t Q ν ε) ≤
      200 * (fDeg Q (α * |t|) ν ε + 1) * (a + simM (α * |t|) ε + simR Q (α * |t|) ν ε + 1) ∧
    Fintype.card (SimWire a Q (α * |t|) ν ε) =
      2 * a + 3 * simM (α * |t|) ε + 6 * simR Q (α * |t|) ν ε + 3 ∧
    ‖run (simSem UJ D) (absCircuit a α t Q ν ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • h))‖ ≤ ε ∧
    (fDeg Q (α * |t|) ν ε : ℝ) ≤ 128 * (α * |t| * ν + Q * (1 + Real.log (1 / (ε / 3)))) ∧
    TimeSchedule.steps (α * |t|) (ε / 3) ≤ 2 ^ simM (α * |t|) ε ∧
    2 ^ simM (α * |t|) ε < 2 * TimeSchedule.steps (α * |t|) (ε / 3) ∧
    2 * fDeg Q (α * |t|) ν ε + 2 ≤ 2 ^ simR Q (α * |t|) ν ε ∧
    2 ^ simR Q (α * |t|) ν ε ≤ 4 * (fDeg Q (α * |t|) ν ε + 1) := by
  have hε1 : ε ≤ 1 := by linarith
  have hτ : 0 ≤ α * |t| := mul_nonneg hα.le (abs_nonneg t)
  have hUJ1 : UJ† ∘L UJ = 1 := by
    rw [← star_eq_adjoint, ← mul_def]
    exact hUJ.1
  have hJ : (UJ ∘L iota0 (a := a) (P := P))† ∘L (UJ ∘L iota0) = 1 := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc (UJ†) UJ iota0, hUJ1,
      show (1 : Anc a P →L[ℂ] Anc a P) ∘L iota0 = iota0 from id_comp _, iota0_isometry]
  have hmom : ‖R1 ∘L (UJ ∘L iota0 (a := a) (P := P))‖ ^ 2 ≤ ν / 2 :=
    (second_moment_iff R1 (UJ ∘L iota0) hν.le).mp hMoment
  -- the count in the form of `hs:eq:abstractcost`
  have hcost : ∀ n : ℕ, n = 6 * fDeg Q (α * |t|) ν ε →
      (fDeg Q (α * |t|) ν ε : ℝ) ≤ 128 * (α * |t| * ν + Q * (1 + Real.log (1 / (ε / 3)))) →
      (n : ℝ) ≤ 3840 * (α * |t| * ν + Q * Real.log (1 / ε)) := by
    intro n hn hdeg
    rw [hn, Nat.cast_mul, Nat.cast_ofNat]
    exact abstract_cost_le hdeg (mul_nonneg hτ hν.le) (by linarith) hε hε2
  have hcostJ : ∀ n : ℕ, n = 12 * fDeg Q (α * |t|) ν ε →
      (fDeg Q (α * |t|) ν ε : ℝ) ≤ 128 * (α * |t| * ν + Q * (1 + Real.log (1 / (ε / 3)))) →
      (n : ℝ) ≤ 7680 * (α * |t| * ν + Q * Real.log (1 / ε)) := by
    intro n hn hdeg
    rw [hn, Nat.cast_mul, Nat.cast_ofNat]
    have := abstract_cost_le hdeg (mul_nonneg hτ hν.le) (by linarith) hε hε2
    linarith
  by_cases ht : 0 ≤ t
  · obtain ⟨hvalid, hP, hU, hG, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
      gate_efficient_simulation a UJ D R1 h hUJ hD (α * |t|) Q ‖R1 ∘L (UJ ∘L iota0)‖ ν ε hτ hQ
        hRight hLeft hR1 hBoundary hSelf hh le_rfl hmom hνQ hε hε1
    have hc : absCircuit a α t Q ν ε = simCircuit a (α * |t|) Q ν ε := if_pos ht
    rw [hc, ← exponent_nonneg α t ht h]
    exact ⟨hvalid, hP, hcost _ hP hdeg, hU, hcostJ _ hU hdeg, hG, hW, herr, hdeg, hm1, hm2, hr1,
      hr2⟩
  · have ht' : t < 0 := lt_of_not_ge ht
    obtain ⟨hvalid, hP, hU, hG, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
      gate_efficient_simulation a UJ (D†) (1 - R1) (-h) hUJ (transfer_unitary D hD) (α * |t|) Q
        ‖(1 - R1) ∘L (UJ ∘L iota0)‖ ν ε hτ hQ (transfer_right D R1 hD hRight hLeft)
        (transfer_left D R1 hD hRight hLeft)
        (by rw [transfer_norm D R1 hD hRight hLeft]; exact hR1)
        (transfer_boundary _ hJ R1 h hBoundary) (by rw [star_neg, hSelf])
        (by rw [norm_neg]; exact hh) le_rfl
        (by rw [transfer_endpoint D R1 hD hRight hLeft]; exact hmom) hνQ hε hε1
    have hc : absCircuit a α t Q ν ε = flipDs (simCircuit a (α * |t|) Q ν ε) := if_neg ht
    have hexp : (-Complex.I * ((α * |t| : ℝ) : ℂ)) • (-h) =
        (-Complex.I * (t : ℂ)) • ((α : ℂ) • h) := exponent_neg α t ht' h
    rw [hexp] at herr
    rw [hc, run_flipDs, nPriv_flipDs, nUJ_flipDs, nGates_flipDs]
    refine ⟨valid_flipDs _ _ hvalid, hP, hcost _ hP hdeg, hU, hcostJ _ hU hdeg, hG, hW, ?_,
      hdeg, hm1, hm2, hr1, hr2⟩
    convert herr using 4

end

end SparseHamiltonian.GateRemarks
