import GateEfficientHamiltonian.Circuit.GCount

/-!
# Gate-efficient sparse Hamiltonian simulation (exact gates)

This is the exact-gate core of Theorem `hs:thm:gates` of the manuscript.  The
circuit `simCircuit a τ Q qbar ε` is a list of instructions on
`2a + 3m + 6r + 3` qubit wires (and the system register): elementary gates,
each a one-qubit unitary with at most three literal controls, together with
sector-controlled calls of `U_J` and of the private Cayley operation `D`.
It depends only on the public data `a, τ, Q, qbar, ε`; the oracles enter only
through the semantics `simSem U_J D`.

Under the clock hypotheses of the released analysis for `J = U_J ι₀`
(`SharpClockSimulation.exists_precise_implementation`) and unitary oracles,
`gate_efficient_simulation` proves:

* every instruction is a valid elementary instruction;
* exactly `6d` private Cayley calls and `12d` calls of `U_J` or `U_J†`, where
  `d` is the filter degree;
* at most `200 (d+1) (a+m+r+1)` elementary gates;
* full-output error at most `ε` against `exp(-iτH)` on clean inputs, including
  every work register;
* the released degree bound `d ≤ 128 (τ qbar + Q (1 + log (3/ε)))`, and
  `2^m < 2·steps`, `2^r ≤ 4(d+1)`.

Finite-gate-set synthesis of the rotation angles is not formalised here.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

/-! ### Parameters -/

/-- Slot exponent: `2^m` is at least the released subdivision count. -/
def simM (τ ε : ℝ) : ℕ := Nat.clog 2 (TimeSchedule.steps τ (ε / 3))

/-- Size of the reuse pointer and label registers. -/
def simR (Q τ qbar ε : ℝ) : ℕ := Nat.clog 2 (2 * fDeg Q τ qbar ε + 2)

/-- Size of the AND-chain pool. -/
def simK (a : ℕ) (Q τ qbar ε : ℝ) : ℕ := a + simM τ ε + 2 * simR Q τ qbar ε

/-- The wires of the simulator. -/
abbrev SimWire (a : ℕ) (Q τ qbar ε : ℝ) := Wire a (simM τ ε) (simR Q τ qbar ε) (simK a Q τ qbar ε)

theorem simM_spec (τ ε : ℝ) :
    TimeSchedule.steps τ (ε / 3) ≤ 2 ^ simM τ ε ∧ 2 ^ simM τ ε < 2 * TimeSchedule.steps τ (ε / 3) := by
  have hS := TimeSchedule.steps_pos τ (ε / 3)
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  by_cases h1 : 1 < TimeSchedule.steps τ (ε / 3)
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
    have hpos : 0 < simM τ ε := Nat.clog_pos (by norm_num) h1
    unfold simM at hpos ⊢
    have : 2 ^ Nat.clog 2 (TimeSchedule.steps τ (ε / 3)) =
        2 * 2 ^ (Nat.clog 2 (TimeSchedule.steps τ (ε / 3))).pred := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ]; ring
    omega
  · have h1' : TimeSchedule.steps τ (ε / 3) = 1 := by omega
    unfold simM
    rw [h1']
    simp

theorem simR_spec (Q τ qbar ε : ℝ) :
    2 * fDeg Q τ qbar ε + 2 ≤ 2 ^ simR Q τ qbar ε ∧ 0 < simR Q τ qbar ε ∧
      2 ^ simR Q τ qbar ε ≤ 4 * (fDeg Q τ qbar ε + 1) := by
  have h1 : 1 < 2 * fDeg Q τ qbar ε + 2 := by omega
  refine ⟨Nat.le_pow_clog (by norm_num) _, Nat.clog_pos (by norm_num) h1, ?_⟩
  have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h1
  have hpos : 0 < simR Q τ qbar ε := Nat.clog_pos (by norm_num) h1
  unfold simR at hpos ⊢
  have : 2 ^ Nat.clog 2 (2 * fDeg Q τ qbar ε + 2) =
      2 * 2 ^ (Nat.clog 2 (2 * fDeg Q τ qbar ε + 2)).pred := by
    conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
    rw [pow_succ]; ring
  omega

theorem simL (Q τ qbar ε : ℝ) :
    (fDeg Q τ qbar ε + 1) + (fDeg Q τ qbar ε + 1) ≤ 2 ^ simR Q τ qbar ε := by
  have := (simR_spec Q τ qbar ε).1
  omega

/-- **The gate-level simulation circuit.**  It is fixed by the public data
`a, τ, Q, qbar, ε`, before the oracles are supplied. -/
def simCircuit (a : ℕ) (τ Q qbar ε : ℝ) : List (Instr (SimWire a Q τ qbar ε)) :=
  ampI (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε)
    (CayleyTransfer.c (stepW τ (simM τ ε))) (CayleyTransfer.sigma (stepW τ (simM τ ε)))
    (2 * fDeg Q τ qbar ε)

/-! ### The number of wires -/

/-- The wires as a sum of finite types. -/
def wireEquiv (a m r K : ℕ) : Wire a m r K ≃
    Fin a ⊕ Unit ⊕ Fin m ⊕ Fin r ⊕ Fin r ⊕ Unit ⊕ Fin m ⊕ Unit ⊕ Fin r ⊕ Fin r ⊕ Fin K where
  toFun w := match w with
    | .anc i => Sum.inl i
    | .sec => Sum.inr (Sum.inl ())
    | .slot i => Sum.inr (Sum.inr (Sum.inl i))
    | .ptr i => Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))
    | .lab i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
    | .hf => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
    | .pf i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
    | .lf => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))))
    | .tf i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl i))))))))
    | .cf i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl i)))))))))
    | .wk i => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr i)))))))))
  invFun s := match s with
    | Sum.inl i => .anc i
    | Sum.inr (Sum.inl _) => .sec
    | Sum.inr (Sum.inr (Sum.inl i)) => .slot i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => .ptr i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))) => .lab i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => .hf
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))) => .pf i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))))) => .lf
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inl i)))))))) => .tf i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inl i))))))))) => .cf i
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (Sum.inr (Sum.inr i))))))))) => .wk i
  left_inv w := by cases w <;> rfl
  right_inv s := by
    rcases s with i | _ | i | i | i | _ | i | _ | i | i | i <;> rfl

theorem card_wire (a m r K : ℕ) :
    Fintype.card (Wire a m r K) = a + 1 + m + r + r + 1 + m + 1 + r + r + K := by
  rw [Fintype.card_congr (wireEquiv a m r K)]
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

theorem card_simWire (a : ℕ) (Q τ qbar ε : ℝ) :
    Fintype.card (SimWire a Q τ qbar ε) = 2 * a + 3 * simM τ ε + 6 * simR Q τ qbar ε + 3 := by
  rw [card_wire, simK]
  ring

/-! ### The gate count -/

theorem gate_bound (a m r d T : ℕ) (hT : T ≤ 4 * (d + 1)) :
    3 * (2 * (T * (2 * r + 1)) + 2 * ((d + 1 + (d + 1)) * (8 * r + 2)) +
      2 * d * (4 * a + 8 * m + 7 * r + 5)) + 2 * (2 * (a + m + 2 * r) + 2) + 1 ≤
      200 * (d + 1) * (a + m + r + 1) := by
  have h1 : T * (2 * r + 1) ≤ 4 * (d + 1) * (2 * r + 1) := Nat.mul_le_mul_right _ hT
  nlinarith [Nat.zero_le (d * a), Nat.zero_le (d * m), Nat.zero_le (d * r)]

/-! ### The theorem -/

/-- **Gate-efficient sparse Hamiltonian simulation, exact gates.**

Let `U_J` and `D` be unitaries on `a` ancilla qubits and the system, and
suppose the clock hypotheses of the released analysis hold for the private
Cayley operation `D` and the boundary isometry `J = U_J ι₀` (as provided by
Theorem `hs:thm:main`).  Then the uniform circuit `simCircuit a τ Q qbar ε`
consists of valid elementary instructions, uses exactly `6d` private Cayley
calls, exactly `12d` calls of `U_J` or `U_J†`, at most
`200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits, and its
full output on clean inputs approximates `exp(-iτH)` within `ε`. -/
theorem gate_efficient_simulation (a : ℕ) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] [CompleteSpace P]
    (UJ D R1 : Anc a P →L[ℂ] Anc a P) (H : P →L[ℂ] P)
    (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJ ∘L iota0)† ∘L R1 ∘L (UJ ∘L iota0) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∀ g ∈ simCircuit a τ Q qbar ε, g.Valid Wire.anc) ∧
    nPriv (simCircuit a τ Q qbar ε) = 6 * fDeg Q τ qbar ε ∧
    nUJ (simCircuit a τ Q qbar ε) = 12 * fDeg Q τ qbar ε ∧
    nGates (simCircuit a τ Q qbar ε) ≤
      200 * (fDeg Q τ qbar ε + 1) * (a + simM τ ε + simR Q τ qbar ε + 1) ∧
    Fintype.card (SimWire a Q τ qbar ε) = 2 * a + 3 * simM τ ε + 6 * simR Q τ qbar ε + 3 ∧
    ‖run (simSem UJ D) (simCircuit a τ Q qbar ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (fDeg Q τ qbar ε : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (1 / (ε / 3)))) ∧
    TimeSchedule.steps τ (ε / 3) ≤ 2 ^ simM τ ε ∧ 2 ^ simM τ ε < 2 * TimeSchedule.steps τ (ε / 3) ∧
    2 * fDeg Q τ qbar ε + 2 ≤ 2 ^ simR Q τ qbar ε ∧ 2 ^ simR Q τ qbar ε ≤ 4 * (fDeg Q τ qbar ε + 1) := by
  obtain ⟨hm1, hm2⟩ := simM_spec τ ε
  obtain ⟨hr1, hr0, hr2⟩ := simR_spec Q τ qbar ε
  have hw0 : 0 ≤ stepW τ (simM τ ε) := div_nonneg hτ (Nat.cast_nonneg _)
  have hwq : stepW τ (simM τ ε) ≤ 1 / 4 :=
    (schedule_ge τ (ε / 3) hτ (by positivity) (2 ^ simM τ ε) hm1).2.1
  obtain ⟨_, _, _, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ (simM τ ε)) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ (simM τ ε)) ^ 2 +
      CayleyTransfer.sigma (stepW τ (simM τ ε)) ^ 2 = 1 := by
    linarith
  have hN : 2 * fDeg Q τ qbar ε ≤ cap (simR Q τ qbar ε) + 1 := by
    have := cap_succ (simR Q τ qbar ε)
    omega
  obtain ⟨hc1, hc2, hc3⟩ := ampI_counts (a := a) (m := simM τ ε) (K := simK a Q τ qbar ε)
    (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ (simM τ ε)))
    (CayleyTransfer.sigma (stepW τ (simM τ ε))) (2 * fDeg Q τ qbar ε) hN
  have hn : ∀ ℓ, labLen Q τ qbar ε ℓ < 2 ^ simR Q τ qbar ε := by
    intro ℓ
    have := (labLen_spec Q τ qbar ε hQ ℓ).2
    omega
  have hK : a + simM τ ε + 2 * simR Q τ qbar ε ≤ simK a Q τ qbar ε := le_rfl
  have hagree := amp_agrees (P := P) (a := a) (m := simM τ ε) (K := simK a Q τ qbar ε) UJ D hUJ hD
    (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε)
    (CayleyTransfer.c (stepW τ (simM τ ε))) (CayleyTransfer.sigma (stepW τ (simM τ ε))) hunit
    (2 * fDeg Q τ qbar ε) hn hK
  obtain ⟨herr, hdeg⟩ := amp_error (K := simK a Q τ qbar ε) (m := simM τ ε) UJ D R1 H hUJ hD τ Q b
    qbar ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hε hε1 hm1 hr0
    (simL Q τ qbar ε)
  have hgb := gate_bound a (simM τ ε) (simR Q τ qbar ε) (fDeg Q τ qbar ε) (2 ^ simR Q τ qbar ε) hr2
  refine ⟨ampI_valid _ _ _ _ _ hunit _, ?_, ?_, ?_, card_simWire a Q τ qbar ε, ?_, hdeg, hm1, hm2,
    hr1, hr2⟩
  · unfold simCircuit; rw [hc1]; ring
  · unfold simCircuit; rw [hc2]; ring
  · unfold simCircuit
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring
  · have hio : run (simSem UJ D) (simCircuit a τ Q qbar ε) ∘L io =
        AMP (K := simK a Q τ qbar ε) (m := simM τ ε) (simL Q τ qbar ε) (labLen Q τ qbar ε)
          (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ (simM τ ε)))
          (CayleyTransfer.sigma (stepW τ (simM τ ε))) UJ D (2 * fDeg Q τ qbar ε) ∘L io := by
      unfold simCircuit
      refine ContinuousLinearMap.ext (fun ψ => ?_)
      rw [comp_apply, comp_apply, io_apply]
      exact hagree _ (supp_bas _ (fun w _ => rfl) ψ)
    rw [hio]
    exact herr

end

end SparseHamiltonian.GateCircuit.Sim
