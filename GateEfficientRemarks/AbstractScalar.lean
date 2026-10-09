import GateEfficientRemarks.Abstract

/-!
# Lemma `hs:lem:abstract`: a scalar instance with `h = 1`

The hypotheses of Lemma `hs:lem:abstract` are the interface `hs:eq:interface`, which
`interface_binary` derives for all binary sparse data. The explicit binary-data witness of the
package (`GateBitBudget.pointData`) has a zero matrix, for which that interface has `h = 0`. This
file gives an explicit instance with `h = 1` on every system and every number of ancilla qubits:

* `smul_one_comp_smul_one`: scalar operators `x • 1` compose by multiplication;
* `abstract_simulation_scalar`: `U_J = 1`, `D = i • 1`, `R₁ = ((1 + i)/2) • 1`, `h = 1` and
  `Q = ν = α = 1` meet every hypothesis of `abstract_simulation` (`1 - D = (1 - i) • 1` is
  inverted by `R₁`, `J† R₁ J = (1 + i)/2 = (1 + i h)/2`, `‖R₁ J‖² ≤ 1/2 = ν/2`), so for every real
  `t` the circuit `absCircuit a 1 t 1 1 (1/2)` simulates `exp(-it)` within `1/2` with at most
  `3840 (|t| + log 2)` calls of `D` or `D†`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct

section Scalar

variable (a : ℕ) {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- The scalar operators `x • 1` compose by multiplication (`hs:lem:abstract`, non-vacuity). -/
theorem smul_one_comp_smul_one (x y : ℂ) :
    (x • (1 : Anc a P →L[ℂ] Anc a P)) ∘L (y • (1 : Anc a P →L[ℂ] Anc a P)) =
      (x * y) • (1 : Anc a P →L[ℂ] Anc a P) := by
  rw [smul_comp, comp_smul, smul_smul]
  rfl

/-- **Lemma `hs:lem:abstract` with `h = 1`** (non-vacuity, `hs:eq:interface`): `U_J = 1`,
`D = i • 1`, `R₁ = ((1 + i)/2) • 1`, `h = 1` and `Q = ν = α = 1` meet every hypothesis of
`abstract_simulation`, for every number `a` of ancilla qubits, every system `P` and every real
time `t`, with `ε = 1/2`. Hence the circuit `absCircuit a 1 t 1 1 (1/2)` has full-output error at
most `1/2` against `exp(-it)` and makes at most `3840 (|t| + log 2)` calls of `D` or `D†`. -/
theorem abstract_simulation_scalar (t : ℝ) :
    ‖run (simSem (1 : Anc a P →L[ℂ] Anc a P) (Complex.I • 1)) (absCircuit a 1 t 1 1 (1 / 2)) ∘L
        io - io ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          (((1 : ℝ) : ℂ) • (1 : P →L[ℂ] P)))‖ ≤ 1 / 2 ∧
    (nPriv (absCircuit a 1 t 1 1 (1 / 2)) : ℝ) ≤
      3840 * (1 * |t| * 1 + 1 * Real.log (1 / (1 / 2))) := by
  set c : ℂ := (1 + Complex.I) / 2 with hc
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hD : IsUnitary (Complex.I • (1 : Anc a P →L[ℂ] Anc a P)) := by
    have h1 : star Complex.I * Complex.I = 1 := by
      rw [Complex.star_def, Complex.conj_I, neg_mul, hI2, neg_neg]
    refine ⟨?_, ?_⟩
    · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, h1, one_smul]
    · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, mul_comm, h1, one_smul]
  have he : (1 - Complex.I • (1 : Anc a P →L[ℂ] Anc a P)) =
      (1 - Complex.I) • (1 : Anc a P →L[ℂ] Anc a P) := by
    module
  have hc1 : (1 - Complex.I) * c = 1 := by
    rw [hc]
    linear_combination (-1 / 2 : ℂ) * hI2
  have hRight : (1 - Complex.I • (1 : Anc a P →L[ℂ] Anc a P)) ∘L
      (c • (1 : Anc a P →L[ℂ] Anc a P)) = 1 := by
    rw [he, smul_one_comp_smul_one, hc1, one_smul]
  have hLeft : (c • (1 : Anc a P →L[ℂ] Anc a P)) ∘L
      (1 - Complex.I • (1 : Anc a P →L[ℂ] Anc a P)) = 1 := by
    rw [he, smul_one_comp_smul_one, mul_comm, hc1, one_smul]
  have hJ : (1 : Anc a P →L[ℂ] Anc a P) ∘L iota0 = iota0 := id_comp _
  have hB : ((1 : Anc a P →L[ℂ] Anc a P) ∘L iota0)† ∘L (c • (1 : Anc a P →L[ℂ] Anc a P)) ∘L
      ((1 : Anc a P →L[ℂ] Anc a P) ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • (1 : P →L[ℂ] P)) := by
    rw [hJ, smul_comp, hJ, comp_smul, iota0_isometry, hc]
    module
  have hc2 : ‖c‖ ^ 2 = 1 / 2 := by
    rw [hc, Complex.sq_norm, Complex.normSq_apply]
    simp
    norm_num
  have hc0 := norm_nonneg c
  have hcle : ‖c‖ ≤ 1 := by nlinarith
  have hι : ‖(iota0 (a := a) (P := P))‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one (fun p => ?_)
    rw [(norm_map_iff_adjoint_comp_self _).mpr iota0_isometry p, one_mul]
  have hM : ((1 : Anc a P →L[ℂ] Anc a P) ∘L iota0)† ∘L (c • (1 : Anc a P →L[ℂ] Anc a P))† ∘L
      (c • (1 : Anc a P →L[ℂ] Anc a P)) ∘L ((1 : Anc a P →L[ℂ] Anc a P) ∘L iota0) ≤
      (((1 : ℝ) / 2 : ℝ) : ℂ) • (1 : P →L[ℂ] P) := by
    rw [second_moment_iff _ _ zero_le_one, hJ, smul_comp, hJ]
    have h3 := opNorm_smul_le c (iota0 (a := a) (P := P))
    have h4 : ‖c‖ * ‖(iota0 (a := a) (P := P))‖ ≤ ‖c‖ :=
      mul_le_of_le_one_right hc0 hι
    have h5 : ‖c • (iota0 (a := a) (P := P))‖ ^ 2 ≤ ‖c‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h3.trans h4) 2
    linarith
  have hR : ‖c • (1 : Anc a P →L[ℂ] Anc a P)‖ ≤ 1 :=
    (opNorm_smul_le _ _).trans (mul_le_one₀ hcle (norm_nonneg _) norm_id_le)
  have h := abstract_simulation a (P := P) 1 (Complex.I • 1) (c • 1) 1 isUnitary_one hD hRight
    hLeft (star_one (P →L[ℂ] P)) norm_id_le hB 1 1 le_rfl one_pos le_rfl hM hR 1 t (1 / 2)
    one_pos (by norm_num) le_rfl
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.1⟩

end Scalar

end

end SparseHamiltonian.GateRemarks
