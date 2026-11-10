import GateEfficientRemarks.Abstract
import GateEfficientBinaryTime.Simulation

/-!
# Lemma `hs:lem:abstract`: the interface from binary sparse data

The hypotheses of Lemma `hs:lem:abstract` are the interface `hs:eq:interface`, which the paper
derives for sparse Hamiltonians with `ν = (1 + γ²)/2`, `Q = ⌈max(1, γ √s)⌉`, `α = η √s/γ`
(equations `hs:eq:scaled`, `ov:eq:response`, `ov:eq:Q`). This file checks that the
hypotheses of `abstract_simulation` can be met:

* `interface_binary`: the released gate-level operators of the binary-data construction
  (`GateBinary.Dbin`, `GateBinary.R1bin`, `GateBinary.Hbin` and
  `U_J = GateNative.UJop (GateBinary.hadUJ k σ hσ)`, library `GateEfficientBinary`) satisfy all
  of them, with the compressed second moment in the Loewner order, for every binary sparse input
  with a Hermitian matrix of row and column norms at most one (`η = 1`) and every rescaling
  `0 < γ ≤ 1`; then `α h` is the qubit lift of the represented matrix;
* `abstract_simulation_binary`: `abstract_simulation` for these operators, a simulation of
  `exp(-itĤ)` for every real `t` with `6 d ≤ 3840 (α|t|ν + Q log(1/ε))` calls of `D` or `D†`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateBinary
open CayleyClockInterface
open NativeSparseBlockEncoding (Data)
open scoped InnerProduct

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

set_option maxRecDepth 2000 in
/-- **The interface `hs:eq:interface` from binary sparse data** (non-vacuity of
`abstract_simulation`). For binary sparse data with `k`-bit indices and `s = 2^σ` slots on the
lowest `σ ≤ k` bits, an input `x` whose matrix `H` is Hermitian with row and column norms at most
one, and a rescaling `0 < γ ≤ 1`, the released operators `U_J = UJop (hadUJ k σ hσ)`,
`D = Dbin D en x γ`, `R₁ = R1bin D en x γ` and `h = Hbin D en x γ` on the `k + 1` ancilla qubits
and the `k` system qubits (with an untouched reference `R`) satisfy every hypothesis of
`abstract_simulation` with `Q = width s γ = ⌈max(1, γ √s)⌉` (an integer) and
`ν = moment γ = (1 + γ²)/2`: `U_J` and `D` are unitary, `R₁` is the two-sided inverse of
`1 - D`, `h` is self-adjoint with `‖h‖ ≤ 1`, `J† R₁ J = (1 + i h)/2` for `J = U_J ι₀`,
`1 ≤ Q`, `0 < ν ≤ Q`, `J† R₁† R₁ J ≤ (ν/2) 1` and `‖R₁‖ ≤ Q`; moreover `α h = Ĥ` for
`α = √s/γ`, where `Ĥ` is the qubit lift of `H`. -/
theorem interface_binary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    IsUnitary (UJop (R := R) (hadUJ k σ hσ)) ∧ IsUnitary (Dbin (R := R) D en x γ) ∧
    (1 - Dbin (R := R) D en x γ) ∘L R1bin (R := R) D en x γ = 1 ∧
    R1bin (R := R) D en x γ ∘L (1 - Dbin (R := R) D en x γ) = 1 ∧
    star (Hbin (R := R) D en x γ) = Hbin (R := R) D en x γ ∧ ‖Hbin (R := R) D en x γ‖ ≤ 1 ∧
    (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        R1bin (R := R) D en x γ ∘L
          (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • Hbin (R := R) D en x γ) ∧
    1 ≤ width (s : ℝ) γ ∧ 0 < moment γ ∧ moment γ ≤ width (s : ℝ) γ ∧
    (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        (R1bin (R := R) D en x γ)† ∘L R1bin (R := R) D en x γ ∘L
          (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) ≤
      ((moment γ / 2 : ℝ) : ℂ) • (1 : Reg (Fin k) R →L[ℂ] Reg (Fin k) R) ∧
    ‖R1bin (R := R) D en x γ‖ ≤ width (s : ℝ) γ ∧
    width (s : ℝ) γ = ((⌈max 1 (γ * Real.sqrt s)⌉₊ : ℕ) : ℝ) ∧
    ((Real.sqrt s / γ : ℝ) : ℂ) • Hbin (R := R) D en x γ =
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)) := by
  have hs0 : 0 < s := by
    rw [hs]
    exact Nat.two_pow_pos σ
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs0)
  have hmom0 : 0 < moment γ := by
    unfold moment
    positivity
  have hend := R1bin_endpoint (R := R) D en σ hσ hs hrange x γ hγ.le hrow hcol
  have hmom : ‖R1bin (R := R) D en x γ ∘L
      (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))‖ ^ 2 ≤
        moment γ / 2 := by
    rw [← endpoint_sq γ]
    gcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact UJop_isUnitary _ (hadUJ_ok σ hσ)
  · exact Dbin_isUnitary D en x γ
  · exact one_sub_Dbin_R1bin D en x γ
  · exact R1bin_one_sub_Dbin D en x γ
  · exact Hbin_self D en x γ
  · exact norm_Hbin_le D en x γ hγ.le hγ1 hrow hcol
  · exact R1bin_boundary D en σ hσ hs hrange x γ
  · exact width_ge_one _ _
  · exact hmom0
  · exact moment_le_width _ γ hγ.le hγ1
  · exact (second_moment_iff (R1bin (R := R) D en x γ)
      (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) hmom0.le).mpr hmom
  · exact norm_R1bin_le D en x γ hγ.le hrow
  · unfold width
    rfl
  · rw [Hbin_eq_smul D en x hH γ hγ.ne' hs0, smul_smul]
    have hc : ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) * ((γ / Real.sqrt (s : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, div_mul_div_comm, mul_comm (Real.sqrt (s : ℝ)) γ,
        div_self (mul_pos hγ hsq).ne', Complex.ofReal_one]
    rw [hc, one_smul]

set_option maxRecDepth 2000 in
/-- **Lemma `hs:lem:abstract` for binary sparse data** (exact gates; the private operation
`D = Dbin D en x γ` and `U_J` are supplied unitaries, with `D†` and controls available). With
the interface of `interface_binary` (`α = √s/γ`, `Q = ⌈max(1, γ √s)⌉`, `ν = (1 + γ²)/2`), for
every real time `t` and `0 < ε ≤ 1/2`, the circuit `absCircuit (k+1) α t Q ν ε` consists of
valid instructions, makes exactly `6 d` calls of `D` or `D†` with
`6 d ≤ 3840 (α |t| ν + Q log(1/ε))` and `12 d` calls of `U_J` or `U_J†`, and its full output on
clean inputs is within `ε` of `exp(-itĤ)` for the qubit lift `Ĥ` of the represented matrix. -/
theorem abstract_simulation_binary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (t ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    (∀ g ∈ absCircuit (k + 1) (Real.sqrt s / γ) t (width (s : ℝ) γ) (moment γ) ε,
      g.Valid Wire.anc) ∧
    nPriv (absCircuit (k + 1) (Real.sqrt s / γ) t (width (s : ℝ) γ) (moment γ) ε) =
      6 * fDeg (width (s : ℝ) γ) (Real.sqrt s / γ * |t|) (moment γ) ε ∧
    (nPriv (absCircuit (k + 1) (Real.sqrt s / γ) t (width (s : ℝ) γ) (moment γ) ε) : ℝ) ≤
      3840 * (Real.sqrt s / γ * |t| * moment γ + width (s : ℝ) γ * Real.log (1 / ε)) ∧
    nUJ (absCircuit (k + 1) (Real.sqrt s / γ) t (width (s : ℝ) γ) (moment γ) ε) =
      12 * fDeg (width (s : ℝ) γ) (Real.sqrt s / γ * |t|) (moment γ) ε ∧
    ‖run (simSem (a := k + 1) (P := Reg (Fin k) R) (UJop (R := R) (hadUJ k σ hσ))
          (Dbin (R := R) D en x γ))
        (absCircuit (k + 1) (Real.sqrt s / γ) t (width (s : ℝ) γ) (moment γ) ε) ∘L
          io (P := Reg (Fin k) R) - io (P := Reg (Fin k) R) ∘L
        NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε := by
  obtain ⟨hU, hD, hRi, hLe, hS, hN, hB, hQ, hν, hνQ, hM, hR, -, hα⟩ :=
    interface_binary (R := R) D en σ hσ hs hrange x hH hrow hcol γ hγ hγ1
  have hs0 : 0 < s := by
    rw [hs]
    exact Nat.two_pow_pos σ
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs0)
  obtain ⟨hvalid, hP, hPle, hJ, -, -, -, herr, -⟩ := abstract_simulation (k + 1) _ _ _ _ hU hD
    hRi hLe hS hN hB (width (s : ℝ) γ) (moment γ) hQ hν hνQ hM hR (Real.sqrt s / γ) t ε
    (div_pos hsq hγ) hε hε2
  rw [hα] at herr
  exact ⟨hvalid, hP, hPle, hJ, herr⟩

end

end SparseHamiltonian.GateRemarks
