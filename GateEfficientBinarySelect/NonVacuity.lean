import GateEfficientBinarySelect.BudgetTrials
import GateEfficientBinarySelect.SelectCost
import GateEfficientSelect.NonVacuity
import GateEfficientSelect.ODE.NonVacuity
import GateEfficientBitBudget.NonVacuity

/-!
# The endpoints are not vacuous

* **The integrated certificate is strictly weaker than the uniform sample bound**
  (`nvc_select`, `nvc_not_uniform`): on the explicit data of `GateSelect.nv_all_hyps` (two labels
  with start times `0`, `1/2` and frequencies `0`, `1`, `H(t) = t · 1`, `D(t) = (1/4) · 1`,
  `m = 4` slot wires, scalar private operations, `T = 1`, `α = 2`, `Q = q̄ = 1`, `ε = 1/2`) with
  represented samples that are exact except at the first slot of every branch, where the error is
  `1/4`, every hypothesis of `gate_select_certified` holds (the integrated sample error is at
  most `1/64 ≤ ε/16`, `nvc_sampleErr_le`) and its conclusion follows, while for no `ε < 1` a
  uniform sample bound `δ` with `4 T δ ≤ ε` exists, so the released `GateSelect.gate_select`
  does not apply to these data.
* **Coherent selection from binary data** (`nv_binary_gate_select`,
  `nv_binary_native_gate_select`): the public data `nvq = withChoiceT pointPubT` of
  `GateEfficientBitBudget` (`PubT.OK` with the coarsest admissible mesh), the one-point
  time-indexed binary data `pointData` on the grid of `2^(2m)` points, the identity equivalence,
  the zero paths and the accuracies `δ = 2ν` (exact gates) and `δ = 4ν` (native) satisfy every
  hypothesis of `binary_gate_select` and `binary_native_gate_select`, whose error bounds then
  hold.
* **The budget in `𝔟`** (`select_all_hyps`): the same public data and binary data with empty
  loading and weight-preparation circuits satisfy every hypothesis of
  `binary_select_budget_bits` for some `b_data`, and its gate bound holds for them;
  `nv_select_lemma`: for some `b_data` every hypothesis of `binary_select_lemma_words` and
  `binary_select_lemma_bits` holds for them, and the native selection circuit at `δ = 4ν` has
  at most `394300 (d+1) (𝔴+1)³` gates for the register words `𝔴` of the witness.
* **The instance conditions** (`nv_restB`, `nv_instanceB`): for the same public and binary data,
  the problem `x' = seedV` on `[0, 1]` with `x(0) = 0`, the zero generator path and the
  quadrature with the single node `T/2^m` of weight `1` (a forcing branch that starts off `0`),
  with the permutation matrix exchanging the zero word and the word of the forcing label as
  weight preparation, every condition of `RestB` holds, and hence every condition of the released
  `GateSelect.ODE.BInstanceOK` for the private operations constructed from the binary data.
* **The guarantee of the solver** (`nvh_restB`, `nv_select_outcome`): for the homogeneous problem
  `x' = 0` with `x(0) = seedV`, zero weights, empty loading and weight-preparation circuits (the
  loading `1` and the identity weight preparation, `ζs = 0`), every antecedent of the guarantee
  of `binary_select_solver` holds, and the native protocol has the guarantees `NOutcome`; with
  the left-endpoint weights and zero forcing samples (`nvh_restL`, `nv_select_outcomeL`), the
  same for `binary_select_solverL`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateCircuit.Sim (Wire Vsp simR fDeg)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateSelect (nvStart nvK nvH nvDp nvAddr cayleyScalar clock_scalar
  isUnitary_smul_one cayleyScalar_norm smul_one_star smul_one_norm_le nvH_sub nv_steps
  nvStart_mem nvK_mem nvAddr_mem branchPath runS selE)
open SparseHamiltonian.GateBitBudget (pointData pointData_range pointData_matrix withChoiceT
  withChoiceT_spec pointPubT pointPubT_ok withChoiceT_bits HasBits bitB)
open SparseHamiltonian.GateODEBudget (gammaOf qOf binary_ode_time_sizes)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The integrated certificate against the uniform sample bound -/

section Certificate

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The sample error at slot `j`: `1/4` at the first slot of every branch, `0` elsewhere. -/
def nvcErr (j : ℕ) : ℝ := if j = 0 then 1 / 4 else 0

/-- The scalar value of the represented sample: the exact value `t + k_z/4` at the branch
address plus the error `nvcErr j`. -/
def nvcVal (z : Cfg (Fin 1)) (j : ℕ) : ℝ := nvAddr z j + nvK z / 4 + nvcErr j

/-- The represented samples. -/
def nvcX (z : Cfg (Fin 1)) (j : ℕ) : P →L[ℂ] P := ((nvcVal z j : ℝ) : ℂ) • 1

/-- The scalar private operations for the normalised samples of the branches. -/
def nvcD (a : ℕ) (z : Cfg (Fin 1)) (j : ℕ) : Vsp a P →L[ℂ] Vsp a P :=
  cayleyScalar ((1 - nvStart z) / (2 * 1) * nvcVal z j) • 1

theorem nvcErr_mem (j : ℕ) : 0 ≤ nvcErr j ∧ nvcErr j ≤ 1 / 4 := by
  unfold nvcErr
  split_ifs <;> norm_num

theorem nvcVal_mem (z : Cfg (Fin 1)) (j : ℕ) (hj : j < 2 ^ 4) :
    0 ≤ nvcVal z j ∧ nvcVal z j ≤ 3 / 2 := by
  obtain ⟨a0, a1⟩ := nvAddr_mem z j hj
  obtain ⟨k0, k1⟩ := nvK_mem z
  obtain ⟨e0, e1⟩ := nvcErr_mem j
  unfold nvcVal
  constructor <;> linarith

omit [CompleteSpace P] in
/-- The sample error of the explicit data at slot `j` is `nvcErr j`. -/
theorem nvc_sample_eq (z : Cfg (Fin 1)) (j : ℕ) :
    (nvH (nvAddr z j) : P →L[ℂ] P) + ((nvK z : ℝ) : ℂ) • nvDp (nvAddr z j) - nvcX z j =
      ((-nvcErr j : ℝ) : ℂ) • 1 := by
  unfold nvH nvDp nvcX nvcVal
  rw [smul_smul, ← add_smul, ← sub_smul]
  congr 1
  push_cast
  ring

omit [CompleteSpace P] in
/-- **The integrated sample error of the explicit data is at most `1/64`.** -/
theorem nvc_sampleErr_le (z : Cfg (Fin 1)) :
    sampleErr (P := P) nvH nvDp nvK nvStart nvcX 1 4 z ≤ 1 / 64 := by
  obtain ⟨s0, s1⟩ := nvStart_mem z
  unfold sampleErr
  calc ∑ j ∈ Finset.range (2 ^ 4), (1 - nvStart z) / 2 ^ 4 *
        ‖(nvH (nvStart z + j * (1 - nvStart z) / 2 ^ 4) : P →L[ℂ] P) +
          ((nvK z : ℝ) : ℂ) • nvDp (nvStart z + j * (1 - nvStart z) / 2 ^ 4) - nvcX z j‖
      ≤ ∑ j ∈ Finset.range (2 ^ 4), 1 / 16 * nvcErr j := by
        apply Finset.sum_le_sum
        intro j _
        have e : nvStart z + j * (1 - nvStart z) / 2 ^ 4 = nvAddr z j := rfl
        rw [e, nvc_sample_eq]
        have h1 := smul_one_norm_le (P := P) (-nvcErr j)
        rw [abs_neg, abs_of_nonneg (nvcErr_mem j).1] at h1
        have h2 : 0 ≤ (1 - nvStart z) / 2 ^ 4 := by
          apply div_nonneg (by linarith) (by norm_num)
        have h3 : (1 - nvStart z) / 2 ^ 4 ≤ 1 / 16 := by
          rw [div_le_iff₀ (by norm_num)]
          linarith
        exact mul_le_mul h3 h1 (norm_nonneg _) (by norm_num)
    _ = 1 / 64 := by
        simp [nvcErr]
        norm_num

/-- **Coherent selection under the integrated certificate applies to the explicit data**: the
propagators of the two branch paths exist, and for every family of them the selection circuit
`simCircuitT a 2 1 1 (1/4) 4` with the scalar private operations `nvcD` is within `1/2` of the
controlled direct sum of the two branch propagators. -/
theorem nvc_select (a : ℕ) :
    (∀ z, ∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧
      TimeDependent.SolvesOn (branchPath nvH nvDp nvK nvStart z) U 0 (1 - nvStart z)) ∧
    ∀ U : Cfg (Fin 1) → ℝ → P →L[ℂ] P, (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath nvH nvDp nvK nvStart z) (U z) 0
        (1 - nvStart z)) →
      ‖runS (1 : Vsp a P →L[ℂ] Vsp a P) (nvcD a)
          (SlotSim.simCircuitT a (2 * 1) 1 1 (1 / 2 / 2) 4) ∘L selE -
        selE ∘L WeightedClock.diagonal (fun z => U z (1 - nvStart z))‖ ≤ 1 / 2 := by
  have hClock : ∀ z, ∀ j < 2 ^ 4, GateODE.ClockPromise (1 : Vsp a P →L[ℂ] Vsp a P) (nvcD a z j)
      ((((1 - nvStart z) / (2 * 1) : ℝ) : ℂ) • nvcX z j) 1 1 := by
    intro z j hj
    have hs : ((((1 - nvStart z) / (2 * 1) : ℝ) : ℂ) • (nvcX z j : P →L[ℂ] P)) =
        ((((1 - nvStart z) / (2 * 1) * nvcVal z j : ℝ)) : ℂ) • (1 : P →L[ℂ] P) := by
      unfold nvcX
      rw [smul_smul, Complex.ofReal_mul]
    rw [hs]
    apply clock_scalar
    obtain ⟨h0, h1⟩ := nvStart_mem z
    obtain ⟨g0, g1⟩ := nvcVal_mem z j hj
    have hc0 : 0 ≤ (1 - nvStart z) / (2 * 1) := by norm_num; linarith
    have hc1 : (1 - nvStart z) / (2 * 1) ≤ 1 / 2 := by norm_num; linarith
    rw [abs_of_nonneg (mul_nonneg hc0 g0)]
    calc (1 - nvStart z) / (2 * 1) * nvcVal z j ≤ 1 / 2 * (3 / 2) :=
          mul_le_mul hc1 g1 g0 (by norm_num)
      _ ≤ 1 := by norm_num
  obtain ⟨-, -, -, -, -, -, -, -, hex, herr⟩ := gate_select_certified (L := Fin 1) a 4 1 (nvcD a)
    nvH nvDp nvK nvStart nvcX 1 2 (2 * 1) 1 1 0 1 1 (1 / 2) (by norm_num) (by norm_num) rfl
    (by norm_num) le_rfl le_rfl le_rfl (by norm_num) (by norm_num) nv_steps (by norm_num)
    (fun z => by rw [abs_of_nonneg (nvK_mem z).1]; exact (nvK_mem z).2)
    (fun z => (nvStart_mem z).1) (fun z => (nvStart_mem z).2.trans (by norm_num)) isUnitary_one
    (fun z j _ => isUnitary_smul_one a _ (cayleyScalar_norm _)) hClock
    (fun z j _ => smul_one_star _)
    (fun z j hj => (smul_one_norm_le _).trans (by
      rw [abs_of_nonneg (nvcVal_mem z j hj).1]
      linarith [(nvcVal_mem z j hj).2]))
    (fun t _ => smul_one_star t) (fun t _ => smul_one_star _)
    (fun t _ t' _ => by
      rw [nvH_sub, one_mul]
      exact smul_one_norm_le _)
    (fun _ _ _ _ => by simp [nvDp])
    (fun z => (nvc_sampleErr_le z).trans (by norm_num))
  exact ⟨hex, herr⟩

/-- **The uniform sample bound of the released lemma fails for the explicit data**: on the
scalar system `ℂ`, for every accuracy `ε < 1` (in particular `ε = 1/2`, where
`gate_select_certified` applies, `nvc_select`) no `δ` bounds every sample error at the branch
addresses with `4 T δ ≤ ε` (`T = 1`), the hypotheses `hVal` and `hValBudget` of the released
`GateSelect.gate_select`; the error at the first slot is `1/4`. -/
theorem nvc_not_uniform (ε : ℝ) (hε : ε < 1) : ¬ ∃ δ : ℝ,
    (∀ z : Cfg (Fin 1), ∀ j : ℕ, j < 2 ^ 4 →
      ‖(nvH (nvStart z + j * (1 - nvStart z) / 2 ^ 4) : ℂ →L[ℂ] ℂ) +
        ((nvK z : ℝ) : ℂ) • nvDp (nvStart z + j * (1 - nvStart z) / 2 ^ 4) - nvcX z j‖ ≤ δ) ∧
      4 * 1 * δ ≤ ε := by
  rintro ⟨δ, hδ, hb⟩
  have h := hδ (fun _ => false) 0 (by norm_num)
  have e : nvStart (fun _ => false) + ((0 : ℕ) : ℝ) * (1 - nvStart (fun _ => false)) / 2 ^ 4 =
      nvAddr (fun _ => false) 0 := rfl
  rw [e, nvc_sample_eq] at h
  have hn : ‖(((-nvcErr 0 : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ))‖ = 1 / 4 := by
    rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    simp [nvcErr]
  rw [hn] at h
  linarith

end Certificate

/-! ### Coherent selection from binary data -/

section Binary

/-- **The explicit public data of the witnesses**: `withChoiceT pointPubT` of
`GateEfficientBitBudget` (`k_x = σ = 0`, `b = 1`, `c₀ = η_H = T = g = 1`, `η_D = 0`,
`ε = 1/2`, the public choices of `γ` and `ζ` and the coarsest admissible mesh). -/
abbrev nvq : PubT := withChoiceT pointPubT

theorem nvq_ok : nvq.OK := (withChoiceT_spec pointPubT pointPubT_ok).1

/-- The public rescaling of `nvq`. -/
theorem nvq_γ : nvq.γ = gammaOf nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) :=
  (withChoiceT_spec pointPubT pointPubT_ok).2.1

/-- **The one-point time-indexed binary data** on the grid of `2^(2m)` points. -/
abbrev nvData : Data (Unit × Fin (2 ^ (2 * nvq.m))) (Cfg (Fin 0)) (Cfg (VW nvq.b)) nvq.s :=
  pointData _ 1 1

theorem nvData_matrix (g : Unit × Fin (2 ^ (2 * nvq.m))) : nvData.matrix g = 0 :=
  pointData_matrix _ g

theorem nvData_dec : ∀ e z, nvData.decode e z = (nvq.c0 : ℂ) * gauss z := fun _ _ => by
  simp [pointData, withChoiceT, GateBitBudget.withChoiceT₀, pointPubT,
    GateBitBudget.pointPubT₀]
  rfl

theorem nv_hamiltonianPart_zero (g : Unit × Fin (2 ^ (2 * nvq.m))) :
    ODEMatrixEnergy.hamiltonianPart (nvData.matrix g) = 0 := by
  rw [nvData_matrix]
  simp [ODEMatrixEnergy.hamiltonianPart]

theorem nv_dissipativePart_zero (g : Unit × Fin (2 ^ (2 * nvq.m))) :
    ODEMatrixEnergy.dissipativePart (nvData.matrix g) = 0 := by
  rw [nvData_matrix]
  simp [ODEMatrixEnergy.dissipativePart]

/-- The lifted samples of the one-point data vanish. -/
theorem nv_XOf_zero (z : Cfg (LabW nvq.params.m nvq.params.l)) (j : ℕ) :
    XOf nvq nvData (Equiv.refl _) () z j = 0 := by
  have h0 : SparseStateOverlap.matrixOperator (0 : Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) = 0 := by
    ext v i
    simp [SparseStateOverlap.matrixOperator_apply]
  have hH : HbB (k := nvq.kx) nvq.params nvData (Equiv.refl _) () (labOfW z).1 j = 0 := by
    unfold HbB
    split_ifs
    · rw [hLift, nv_hamiltonianPart_zero, h0]
      exact map_zero (qliftHom (R := ℂ) _)
    · rfl
  have hL : LbB (k := nvq.kx) nvq.params nvData (Equiv.refl _) () (labOfW z).1 j = 0 := by
    unfold LbB
    split_ifs
    · rw [lLift, nv_dissipativePart_zero, h0]
      exact map_zero (qliftHom (R := ℂ) _)
    · rfl
  rw [XOf, hH, hL, zero_add]
  exact smul_zero (M := ℂ) (A := Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) _

/-- With the zero paths, the integrated sample error of the one-point data vanishes. -/
theorem nv_sampleErr_zero (z : Cfg (LabW nvq.params.m nvq.params.l)) :
    sampleErr (0 : ℝ → Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) 0 (kOf nvq) (vOf nvq)
      (XOf nvq nvData (Equiv.refl _) ()) nvq.T nvq.params.m z = 0 := by
  unfold sampleErr
  apply Finset.sum_eq_zero
  intro j _
  simp [nv_XOf_zero]

/-- The energy bounds hold for the one-point data. -/
theorem nv_energies :
    (∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (nvData.matrix ((), g)) i j‖ ^ 2 ≤
      nvq.etaH ^ 2) ∧
    (∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (nvData.matrix ((), g)) i j‖ ^ 2 ≤
      nvq.etaH ^ 2) ∧
    (∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (nvData.matrix ((), g)) i j‖ ^ 2 ≤
      nvq.etaD ^ 2) ∧
    (∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (nvData.matrix ((), g)) i j‖ ^ 2 ≤
      nvq.etaD ^ 2) := by
  refine ⟨fun g i => ?_, fun g j => ?_, fun g i => ?_, fun g j => ?_⟩
  · rw [nv_hamiltonianPart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · rw [nv_hamiltonianPart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · rw [nv_dissipativePart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity
  · rw [nv_dissipativePart_zero]
    simp only [Matrix.zero_apply, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    positivity

/-- The arithmetic budget of the native lemma at `δ = 4ν`: `48 d ζ ≤ 4ν`. -/
theorem nv_zeta :
    48 * (fDeg nvq.params.Q nvq.params.tau nvq.params.qbar (4 * nvq.params.nu / 4) : ℝ) *
      nvq.ζ ≤ 4 * nvq.params.nu := by
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes nvq nvq_ok nvq_γ
  have e : 4 * nvq.params.nu / 4 = nvq.params.nu := by ring
  rw [e]
  have hd' : (fDeg nvq.params.Q nvq.params.tau nvq.params.qbar nvq.params.nu : ℝ) ≤
      4096 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) := hd
  have hζ0 := nvq_ok.ζ_pos.le
  have hν := (nvq.params_ok nvq_ok).nu_pos
  have := mul_le_mul_of_nonneg_right hd' hζ0
  nlinarith

/-- **Coherent selection from binary data, exact gates, applies to explicit data**: the public
data `nvq`, the one-point data, the zero paths and `δ = 2ν` satisfy every hypothesis of
`binary_gate_select`, and for every family of propagators of the branch paths the released
selection circuit with the private operations `DOf` is within `2ν` of the controlled direct sum
of the branch propagators. -/
theorem nv_binary_gate_select :
    ∀ U : Cfg (LabW nvq.params.m nvq.params.l) → ℝ →
        Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ, (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath 0 0 (kOf nvq) (vOf nvq) z) (U z) 0
        (nvq.T - vOf nvq z)) →
      ‖runS (a := nvq.params.a) (P := Reg (Fin nvq.kx) ℂ) (L := LabW nvq.params.m nvq.params.l)
          (UJop (R := ℂ) nvq.UJg) (DOf nvq nvData (Equiv.refl _) ())
          (SlotSim.simCircuitT nvq.params.a nvq.params.tau nvq.params.Q nvq.params.qbar
            (2 * nvq.params.nu / 2) nvq.params.m) ∘L
          selE (a := nvq.params.a) (m := nvq.params.m)
            (r := simR nvq.params.Q nvq.params.tau nvq.params.qbar (2 * nvq.params.nu / 2))
            (K := nvq.params.a + nvq.params.m +
              2 * simR nvq.params.Q nvq.params.tau nvq.params.qbar (2 * nvq.params.nu / 2))
            (L := LabW nvq.params.m nvq.params.l) (P := Reg (Fin nvq.kx) ℂ) -
        selE (a := nvq.params.a) (m := nvq.params.m)
            (r := simR nvq.params.Q nvq.params.tau nvq.params.qbar (2 * nvq.params.nu / 2))
            (K := nvq.params.a + nvq.params.m +
              2 * simR nvq.params.Q nvq.params.tau nvq.params.qbar (2 * nvq.params.nu / 2))
            (L := LabW nvq.params.m nvq.params.l) (P := Reg (Fin nvq.kx) ℂ) ∘L
          WeightedClock.diagonal (fun z => U z (nvq.T - vOf nvq z))‖ ≤ 2 * nvq.params.nu := by
  have hp := nvq.params_ok nvq_ok
  have hν := hp.nu_pos
  have hν1 : nvq.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth nvq.params.ratio nvq.params.acc
      (nvq.params.ratio_ge hp.g_ge) (nvq.params.acc_le_one hp.eps_le_one)
  obtain ⟨hrH, hcH, hrD, hcD⟩ := nv_energies
  have hC : TimeSchedule.steps nvq.params.tau (2 * nvq.params.nu / 6) ≤ 2 ^ nvq.params.m := by
    rw [show 2 * nvq.params.nu / 6 = nvq.params.nu / 3 by ring]
    exact nvq_ok.mesh
  obtain ⟨-, -, -, -, -, -, herr⟩ := binary_gate_select nvq nvq_ok nvData (Equiv.refl _)
    (pointData_range _ 1 1) () hrH hcH hrD hcD 0 0 0 0 (2 * nvq.params.nu) le_rfl le_rfl
    (by positivity) (by linarith) hC (by simp; exact hν.le)
    (fun _ _ => by
      simp only [Pi.zero_apply]
      exact star_zero (Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (fun _ _ => by
      simp only [Pi.zero_apply]
      exact star_zero (Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)
    (fun z => by rw [nv_sampleErr_zero]; positivity)
  exact herr

/-- **Coherent selection from binary data with native private calls applies to explicit
data**: the public data `nvq`, the one-point data with its decoder, the zero paths and `δ = 4ν`
satisfy every hypothesis of `binary_native_gate_select` (the arithmetic budget `48 d ζ ≤ δ` by
`nv_zeta`), and for every family of propagators of the branch paths the native selection circuit
is within `4ν` of the controlled direct sum of the branch propagators on the clean-input
space. -/
theorem nv_binary_native_gate_select :
    ∀ U : Cfg (LabW nvq.params.m nvq.params.l) → ℝ →
        Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ, (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath 0 0 (kOf nvq) (vOf nvq) z) (U z) 0
        (nvq.T - vOf nvq z)) →
      ‖nrun (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ())
            (nativeSel (L := LabW nvq.params.m nvq.params.l) nvq.params.a nvq.params.m
              nvq.params.tau nvq.params.Q nvq.params.qbar (4 * nvq.params.nu) nvq.UJg (ndQ nvq)
              (arQ nvq)) ∘L
          selN (L := LabW nvq.params.m nvq.params.l) (S := Fin nvq.kx)
            (Z := ZA nvq.m ⊕ SZ4 nvq.kx nvq.b) (R := ℂ) nvq.params.a nvq.params.m
            (simR nvq.params.Q nvq.params.tau nvq.params.qbar (4 * nvq.params.nu / 4))
            (nvq.params.a + nvq.params.m +
              2 * simR nvq.params.Q nvq.params.tau nvq.params.qbar (4 * nvq.params.nu / 4))
            (arQ nvq).bT (arQ nvq).bP (arQ nvq).A -
        selN (L := LabW nvq.params.m nvq.params.l) (S := Fin nvq.kx)
            (Z := ZA nvq.m ⊕ SZ4 nvq.kx nvq.b) (R := ℂ) nvq.params.a nvq.params.m
            (simR nvq.params.Q nvq.params.tau nvq.params.qbar (4 * nvq.params.nu / 4))
            (nvq.params.a + nvq.params.m +
              2 * simR nvq.params.Q nvq.params.tau nvq.params.qbar (4 * nvq.params.nu / 4))
            (arQ nvq).bT (arQ nvq).bP (arQ nvq).A ∘L
          WeightedClock.diagonal (fun z => U z (nvq.T - vOf nvq z))‖ ≤ 4 * nvq.params.nu := by
  have hp := nvq.params_ok nvq_ok
  have hν := hp.nu_pos
  have hν1 : nvq.params.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth nvq.params.ratio nvq.params.acc
      (nvq.params.ratio_ge hp.g_ge) (nvq.params.acc_le_one hp.eps_le_one)
  obtain ⟨hrH, hcH, hrD, hcD⟩ := nv_energies
  have hC : TimeSchedule.steps nvq.params.tau (4 * nvq.params.nu / 12) ≤ 2 ^ nvq.params.m := by
    rw [show 4 * nvq.params.nu / 12 = nvq.params.nu / 3 by ring]
    exact nvq_ok.mesh
  obtain ⟨-, -, -, -, -, -, herr⟩ := binary_native_gate_select nvq nvq_ok nvData (Equiv.refl _)
    (pointData_range _ 1 1) nvData_dec () hrH hcH hrD hcD 0 0 0 0 (4 * nvq.params.nu) le_rfl
    le_rfl (by positivity) (by linarith) hC (by simp; exact hν.le)
    (fun _ _ => by
      simp only [Pi.zero_apply]
      exact star_zero (Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (fun _ _ => by
      simp only [Pi.zero_apply]
      exact star_zero (Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)
    (fun z => by rw [nv_sampleErr_zero]; positivity) nv_zeta
  exact herr

end Binary

/-! ### The budget in `𝔟` -/

/-- **Every hypothesis of `binary_select_budget_bits` holds at once** (equations
`ode:eq:gate-main`, `ode:eq:gate-space` in `𝔟` on branch-dependent meshes; the endpoint is not
vacuous): the public data `withChoiceT pointPubT` (the coarsest admissible mesh), the one-point
time-indexed binary data on the grid of `2^(2m)` points, the identity equivalence and empty
circuits `loadC`, `wpC` on the empty source scratch satisfy, for some `b_data`, `PubT.OK` (the
mesh condition included), the public rescaling, the accuracy bound, `b ≤ b_data`, the four
bit-length hypotheses, the slot range, the decoder and the validity of the circuits, and the
gate bound `2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` of the endpoint holds for them. -/
theorem select_all_hyps : ∃ (q : PubT) (bd : ℕ) (hq : q.OK)
    (D : Data (Unit × Fin (2 ^ (2 * q.m))) (Cfg (Fin 0)) (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ Cfg (Fin 0))
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Empty)
      (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Empty) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query)),
    q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ∧
    q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ ∧ q.b ≤ bd ∧
    HasBits bd q.c0 ∧ HasBits bd q.T ∧ HasBits bd q.etaH ∧ HasBits bd q.etaD ∧
    (∀ j, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u)) ∧
    (∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) ∧ (∀ i ∈ loadC, i.Valid) ∧
    (∀ i ∈ wpC, i.Valid) ∧
    ((nprotocol (prepQ q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Empty) := by
  obtain ⟨bd, hok, hγ, hζ, hb, hc0, hT, hH, hD⟩ :=
    withChoiceT_bits pointPubT pointPubT_ok
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨0, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
  refine ⟨withChoiceT pointPubT, bd, hok, pointData _ 1 1, Equiv.refl _, [], [], hγ, hζ, hb, hc0,
    hT, hH, hD, pointData_range _ 1 1, nvData_dec, fun _ hi => by simp at hi,
    fun _ hi => by simp at hi, ?_⟩
  exact (binary_select_budget_bits (X := Unit) (Zs := Empty) bd (withChoiceT pointPubT) hok hγ
    hζ hb hc0 hT hH hD (pointData _ 1 1) (Equiv.refl _) (pointData_range _ 1 1) nvData_dec []
    (fun _ hi => by simp at hi) [] (fun _ hi => by simp at hi)).1

/-! ### The instance conditions of the solvers -/

section Instance

open SparseHamiltonian.GateSelect.ODE (bsW mass_bsW zsrc_bsW permMat_unitary)
open SparseHamiltonian.GateODE.Time (TOracles)
open SparseHamiltonian.GateQuad (vQ)
open SparseHamiltonian.GatePointerEncoding (wordValue wordValue_injective)
open ODEStateNormalization (unitDirection)

theorem nvq_T : nvq.T = 1 := rfl

theorem nvq_g : nvq.g = 1 := rfl

theorem nvq_ε : nvq.ε = 1 / 2 := rfl

/-- The mesh of the witnesses has at least one bit (`steps τ (ν/3) ≥ 2`). -/
theorem nvq_m_pos : 0 < nvq.m := by
  have hmesh : TimeSchedule.steps nvq.params.tau (nvq.params.nu / 3) ≤ 2 ^ nvq.m := nvq_ok.mesh
  have hτ : 0 < nvq.params.tau := (nvq.params_ok nvq_ok).tau_pos
  have hth : 0 < TimeSchedule.threshold nvq.params.tau (nvq.params.nu / 3) :=
    lt_max_of_lt_left (by linarith)
  have hc : 0 < ⌈TimeSchedule.threshold nvq.params.tau (nvq.params.nu / 3)⌉₊ :=
    Nat.ceil_pos.mpr hth
  have h2 : 2 ≤ 2 ^ nvq.m := by
    unfold TimeSchedule.steps at hmesh
    omega
  rcases Nat.eq_zero_or_pos nvq.m with h | h
  · rw [h] at h2
    norm_num at h2
  · exact h

/-- The lifted samples of the one-point data vanish. -/
theorem nv_mLift_zero (g : Unit × Fin (2 ^ (2 * nvq.m))) :
    mLift (k := nvq.kx) nvData (Equiv.refl _) g = 0 := by
  have h0 : SparseStateOverlap.matrixOperator (0 : Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) = 0 := by
    ext v i
    simp [SparseStateOverlap.matrixOperator_apply]
  rw [mLift, nvData_matrix, h0]
  exact map_zero (qliftHom (R := ℂ) _)

/-- The dissipative parts of the one-point data are accretive. -/
theorem nv_psd (g : Fin (2 ^ (2 * nvq.m))) (w : EuclideanSpace ℂ (Cfg (Fin 0))) :
    0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (nvData.matrix ((), g))) w)).re := by
  have h0 : SparseStateOverlap.matrixOperator (0 : Matrix (Cfg (Fin 0)) (Cfg (Fin 0)) ℂ) = 0 := by
    ext v i
    simp [SparseStateOverlap.matrixOperator_apply]
  rw [nv_dissipativePart_zero, h0]
  simp

/-! #### A forcing node off the start -/

/-- The node word of the forcing node `1` (bit `0` set). -/
def nvW1 : Fin nvq.params.m → Bool := fun j => decide (j.val = 0)

theorem wordValue_nvW1 : wordValue nvW1 = 1 := by
  unfold GatePointerEncoding.wordValue
  rw [Finset.sum_eq_single ⟨0, nvq_m_pos⟩]
  · simp [nvW1]
  · intro j _ hj
    have hj' : j.val ≠ 0 := fun h => hj (Fin.ext h)
    simp [nvW1, hj']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The weight-preparation word of the forcing label `(true, nvW1)`. -/
def nvC1 : Cfg (Fin (nvq.params.m + 1)) := Fin.cons true nvW1

/-- The weight preparation: the permutation matrix exchanging the zero word and `nvC1`. -/
def nvWp : Matrix (Cfg (Fin (nvq.params.m + 1))) (Cfg (Fin (nvq.params.m + 1))) ℂ :=
  Matrix.of fun i j => if Equiv.swap (fun _ => false) nvC1 i = j then (1 : ℂ) else 0

/-- The quadrature weights: `w_1 = 1`, every other weight `0`. -/
def nvwq (u : ℕ) : ℝ := if u = 1 then 1 else 0

/-- The forcing `b = seedV` and its samples. -/
def nvbf (_ : ℝ) : Reg (Fin nvq.kx) ℂ := seedV

/-- The forcing samples `f_u = seedV`. -/
def nvfv (_ : ℕ) : Reg (Fin nvq.kx) ℂ := seedV

/-- The solution `x(t) = t · seedV` of `x' = seedV`, `x(0) = 0`. -/
def nvxs (t : ℝ) : Reg (Fin nvq.kx) ℂ := ((t : ℝ) : ℂ) • seedV

/-- The homogeneous branch solutions: constant, equal to the source vectors. -/
def nvys (s : Bool × (Fin nvq.m → Bool)) (_ : ℝ) : Reg (Fin nvq.kx) ℂ :=
  nvq.params.zsrc (nvxs 0) (bsW nvq.params nvwq nvfv) s

theorem nvxs_zero : nvxs 0 = 0 := by
  simp [nvxs]

theorem nvxs_T : nvxs nvq.T = seedV := by
  simp [nvxs, nvq_T]

theorem seedV_ne : (seedV : Reg (Fin nvq.kx) ℂ) ≠ 0 := by
  intro h
  have := norm_seedV (S := Fin nvq.kx)
  rw [h, norm_zero] at this
  norm_num at this

theorem nv_mass1 : nvq.params.mass (nvxs 0) (bsW nvq.params nvwq nvfv) = 1 := by
  rw [mass_bsW nvq.params nvq_ok.T_pos (nvxs 0) nvwq
    (fun u _ => by unfold nvwq; split_ifs <;> norm_num) nvfv, nvxs_zero, norm_zero, zero_add]
  rw [Finset.sum_eq_single 1]
  · simp [nvwq, nvfv, norm_seedV]
  · intro u _ hu
    simp [nvwq, hu]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.mp nvq_m_pos)))
      h

theorem nv_zsrc (s : Bool × (Fin nvq.params.m → Bool)) :
    nvq.params.zsrc (nvxs 0) (bsW nvq.params nvwq nvfv) s =
      if s = (true, nvW1) then seedV else 0 := by
  obtain ⟨c, w⟩ := s
  cases c
  · unfold GateODE.Time.TParams.zsrc
    simp [nvxs_zero]
  · rw [zsrc_bsW nvq.params nvq_ok.T_pos]
    by_cases hw : w = nvW1
    · subst hw
      simp [wordValue_nvW1, nvwq, nvfv]
    · have hv : wordValue w ≠ 1 := fun h =>
        hw (wordValue_injective (h.trans wordValue_nvW1.symm))
      simp [nvwq, hv, hw]

theorem nv_prep (w : Cfg (Fin (nvq.params.m + 1))) :
    nvWp w (fun _ => false) =
      ((nvq.params.srcAmp (nvxs 0) (bsW nvq.params nvwq nvfv) (w 0, Fin.tail w) : ℝ) : ℂ) := by
  unfold GateODE.Time.TParams.srcAmp
  rw [nv_mass1, nv_zsrc]
  unfold nvWp
  simp only [Matrix.of_apply]
  by_cases hw : w = nvC1
  · subst hw
    have h1 : ((nvC1 0, Fin.tail nvC1) : Bool × (Fin nvq.params.m → Bool)) = (true, nvW1) := by
      simp [nvC1]
    have h2 : Equiv.swap (fun _ => false) nvC1 nvC1 = (fun _ => false) :=
      Equiv.swap_apply_right _ _
    rw [h2, h1]
    simp [norm_seedV]
  · have h1 : ((w 0, Fin.tail w) : Bool × (Fin nvq.params.m → Bool)) ≠ (true, nvW1) := by
      intro h
      apply hw
      have h0 : w 0 = true := congrArg Prod.fst h
      have ht : Fin.tail w = nvW1 := congrArg Prod.snd h
      rw [← Fin.cons_self_tail w, h0, ht]
      rfl
    have h2 : Equiv.swap (fun _ => false) nvC1 w ≠ (fun _ => false) := by
      intro h
      apply hw
      rw [Equiv.swap_apply_eq_iff] at h
      rw [h]
      exact Equiv.swap_apply_left _ _
    rw [if_neg h2, if_neg h1]
    simp

/-- **Every condition of `RestB` holds for a forcing node off the start**: for the public data
`nvq` and the one-point data, the problem `x' = seedV` on `[0, 1]` with `x(0) = 0`, the zero
generator path, the quadrature with the single node `v_1 = T/2^m` of weight `1` (the branch of
the forcing label `(true, nvW1)` starts at `T/2^m`, not at `0`) and forcing sample `seedV`, the
loading `1` and the permutation matrix `nvWp` as weight preparation, the constant branch
solutions and `κ = βG = δG = 0`. -/
theorem nv_restB :
    RestB nvq nvData (Equiv.refl _) () (fun _ => 1) nvWp nvwq nvfv 0 nvbf nvxs nvys 0 0 0 where
  weights := fun u _ => by
    unfold nvwq
    split_ifs <;> norm_num
  load_unitary := fun _ => isUnitary_one
  prep_left := (permMat_unitary (Equiv.swap (fun _ => false) nvC1)).1
  prep_right := (permMat_unitary (Equiv.swap (fun _ => false) nvC1)).2
  prep := nv_prep
  init_load := fun h => absurd nvxs_zero h
  forcing_load := fun w _ _ => by
    show (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) seedV =
      unitDirection (nvfv (wordValue w))
    simp [nvfv, unitDirection, norm_seedV]
  solves := fun u _ => by
    have h := ((hasDerivAt_id u).ofReal_comp.smul_const
      (seedV : Reg (Fin nvq.kx) ℂ)).hasDerivWithinAt (s := Set.Icc 0 nvq.T)
    exact h.congr_deriv (by simp [nvbf])
  accretive := fun u _ v => by simp
  lipG := fun u _ u' _ => by simp
  βG_nonneg := le_rfl
  sampleG := fun s r hr => by simp [nv_mLift_zero]
  branch_sol := fun s u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  branch_init := fun s => rfl
  quad := by
    have hsum : ∑ s : Bool × (Fin nvq.m → Bool), nvys s nvq.T = seedV := by
      rw [Finset.sum_eq_single ((true, nvW1) : Bool × (Fin nvq.m → Bool))]
      · exact (nv_zsrc (true, nvW1)).trans (if_pos rfl)
      · intro s _ hs
        exact (nv_zsrc s).trans (if_neg hs)
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum, nvxs_T]
    simp
  target_ne := by
    rw [nvxs_T]
    exact seedV_ne
  budget := by
    rw [nv_mass1, nvxs_T, norm_seedV, nvq_g]
    norm_num
  disc := by
    rw [nv_mass1, nvq_ε, nvq_g]
    norm_num

/-- **The released instance conditions on branch-dependent meshes hold for the forcing
witness**: `instanceB` turns `nv_restB`, the energy bounds and the accretivity of the one-point
data into every condition of `GateSelect.ODE.BInstanceOK` for the private operations
`privFamB` constructed from the binary data, with the clock promises proved. -/
theorem nv_instanceB :
    GateSelect.ODE.BInstanceOK nvq.params (seedV (S := Fin nvq.kx))
      (⟨UJop (R := ℂ) nvq.UJg, privFamB nvq.params nvData (Equiv.refl _) () nvq.rho nvq.γ,
        fun _ => 1, nvWp⟩ :
        TOracles nvq.params.a nvq.params.m nvq.params.l (Reg (Fin nvq.kx) ℂ))
      (vQ nvq.params nvq.params.M) nvwq nvfv (HbB nvq.params nvData (Equiv.refl _) ())
      (LbB nvq.params nvData (Equiv.refl _) ()) 0 nvbf nvxs nvys 0 0 0 := by
  obtain ⟨hrH, hcH, hrD, hcD⟩ := nv_energies
  exact instanceB nvq nvq_ok nvData (Equiv.refl _) (pointData_range _ 1 1) () hrH hcH hrD hcD
    nv_psd (fun _ => 1) nvWp nvwq nvfv 0 nvbf nvxs nvys 0 0 0 nv_restB

/-! #### The guarantee of the solver -/

/-- The solution of the homogeneous witness: `x(t) = seedV`. -/
def nvhxs (_ : ℝ) : Reg (Fin nvq.kx) ℂ := seedV

/-- The homogeneous branch solutions: constant, equal to the source vectors. -/
def nvhys (s : Bool × (Fin nvq.m → Bool)) (_ : ℝ) : Reg (Fin nvq.kx) ℂ :=
  nvq.params.zsrc (nvhxs 0) (bsW nvq.params (fun _ => 0) nvfv) s

theorem nvh_mass : nvq.params.mass (nvhxs 0) (bsW nvq.params (fun _ => 0) nvfv) = 1 := by
  rw [mass_bsW nvq.params nvq_ok.T_pos (nvhxs 0) (fun _ => 0) (fun _ _ => le_rfl) nvfv]
  simp [nvhxs, norm_seedV]

theorem nvh_zsrc (s : Bool × (Fin nvq.params.m → Bool)) :
    nvq.params.zsrc (nvhxs 0) (bsW nvq.params (fun _ => 0) nvfv) s =
      if s = (false, fun _ => false) then seedV else 0 := by
  obtain ⟨c, w⟩ := s
  cases c
  · unfold GateODE.Time.TParams.zsrc
    simp [nvhxs]
  · rw [zsrc_bsW nvq.params nvq_ok.T_pos]
    simp

theorem nvh_prep (w : Cfg (Fin (nvq.params.m + 1))) :
    (1 : Matrix (Cfg (Fin (nvq.params.m + 1))) (Cfg (Fin (nvq.params.m + 1))) ℂ) w
        (fun _ => false) =
      ((nvq.params.srcAmp (nvhxs 0) (bsW nvq.params (fun _ => 0) nvfv) (w 0, Fin.tail w) :
        ℝ) : ℂ) := by
  unfold GateODE.Time.TParams.srcAmp
  rw [nvh_mass, nvh_zsrc]
  by_cases hw : w = fun _ => false
  · subst hw
    have h1 : (((fun _ => false : Cfg (Fin (nvq.params.m + 1))) 0,
        Fin.tail (fun _ => false : Cfg (Fin (nvq.params.m + 1)))) :
          Bool × (Fin nvq.params.m → Bool)) = (false, fun _ => false) := rfl
    rw [h1, Matrix.one_apply_eq]
    simp [norm_seedV]
  · have h1 : ((w 0, Fin.tail w) : Bool × (Fin nvq.params.m → Bool)) ≠ (false, fun _ => false) := by
      intro h
      apply hw
      have h0 : w 0 = false := congrArg Prod.fst h
      have ht : Fin.tail w = fun _ => false := congrArg Prod.snd h
      rw [← Fin.cons_self_tail w, h0, ht]
      funext j
      refine Fin.cases rfl (fun i => rfl) j
    rw [Matrix.one_apply_ne hw, if_neg h1]
    simp

/-- **Every condition of `RestB` holds for the homogeneous witness**: `x' = 0` on `[0, 1]` with
`x(0) = seedV`, all quadrature weights `0`, the zero generator path, the loading `1` and the
identity weight preparation, the constant branch solutions and `κ = βG = δG = 0`. -/
theorem nvh_restB :
    RestB nvq nvData (Equiv.refl _) () (fun _ => 1) 1 (fun _ => 0) nvfv 0 0 nvhxs nvhys 0 0 0 where
  weights := fun _ _ => le_rfl
  load_unitary := fun _ => isUnitary_one
  prep_left := by simp
  prep_right := by simp
  prep := nvh_prep
  init_load := fun _ => by
    show (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) seedV = unitDirection (nvhxs 0)
    simp [nvhxs, unitDirection, norm_seedV]
  forcing_load := fun _ h _ => absurd rfl h
  solves := fun u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  accretive := fun u _ v => by simp
  lipG := fun u _ u' _ => by simp
  βG_nonneg := le_rfl
  sampleG := fun s r hr => by simp [nv_mLift_zero]
  branch_sol := fun s u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  branch_init := fun s => rfl
  quad := by
    have hsum : ∑ s : Bool × (Fin nvq.m → Bool), nvhys s nvq.T = seedV := by
      rw [Finset.sum_eq_single ((false, fun _ => false) : Bool × (Fin nvq.m → Bool))]
      · exact (nvh_zsrc (false, fun _ => false)).trans (if_pos rfl)
      · intro s _ hs
        exact (nvh_zsrc s).trans (if_neg hs)
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hsum]
    simp [nvhxs]
  target_ne := seedV_ne
  budget := by
    rw [nvh_mass]
    simp [nvhxs, norm_seedV, nvq_g]
  disc := by
    rw [nvh_mass, nvq_ε, nvq_g]
    norm_num

/-- **The guarantee of the solver on branch-dependent meshes from binary data holds for explicit
data**: for the public data `nvq`, the one-point data, empty loading and weight-preparation
circuits (which implement the loading `1` and the identity weight preparation exactly,
`ζs = 0`), the arithmetic budget `24 d ζ ≤ ν` of the public choice of `ζ` and the homogeneous
witness `nvh_restB`, every antecedent of the guarantee of `binary_select_solver` holds, and the
native protocol has the guarantees `NOutcome` for `x(T) = seedV`. -/
theorem nv_select_outcome :
    NOutcome (prepQ nvq ([] : List (NInstr ((Fin (nvq.params.m + 1) ⊕ Fin nvq.kx) ⊕ Empty)
        (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query)) [])
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ()) seedV := by
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes nvq nvq_ok nvq_γ
  have hd' : (nvq.params.d : ℝ) ≤
      4096 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) := hd
  have hbud : 24 * (nvq.params.d : ℝ) * nvq.ζ + 3 * 0 ≤ nvq.params.nu := by
    have h1 := mul_le_mul_of_nonneg_right hd' nvq_ok.ζ_pos.le
    linarith
  obtain ⟨hrH, hcH, hrD, hcD⟩ := nv_energies
  obtain ⟨-, -, -, -, -, -, hout⟩ := binary_select_solver (X := Unit) (Zs := Empty) nvq nvq_ok
    nvData (Equiv.refl _) (pointData_range _ 1 1) nvData_dec [] (fun _ hi => by simp at hi) []
    (fun _ hi => by simp at hi)
  refine hout () hrH hcH hrD hcD nv_psd
    (fun _ : Bool × (Fin nvq.params.m → Bool) => (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (1 : Matrix (Cfg (Fin (nvq.params.m + 1))) (Cfg (Fin (nvq.params.m + 1))) ℂ) (fun _ => 0)
    nvfv 0 0 nvhxs nvhys 0 0 0 0 le_rfl ?_ ?_ hbud nvh_restB
  · have hL : ∀ k : ℕ, loadIdeal (k := k) (S := Fin nvq.kx)
        (fun _ => (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ)) = 1 := by
      intro k
      unfold loadIdeal
      exact localOp_one _
    rw [nrun_nil, hL, liftB_one]
    intro ψ _
    simp
  · rw [nrun_nil, matOp_one, liftB_one]
    intro ψ _
    simp

/-- **Coherent selection at `δ = 4ν` applies to explicit data**: for the
public data `nvq` and some `b_data`, the arithmetic accuracy satisfies both
`ν ≤ 196608 q* ζ` and `98304 q* ζ ≤ ν`, the bit-length hypotheses hold, and, with the one-point
data and the zero paths (which satisfy the remaining hypotheses of `binary_select_lemma_words`
and `binary_select_lemma_bits`), the native selection circuit at `δ = 4ν` has at most
`394300 (d+1) (𝔴+1)³` elementary gates for the register words `𝔴 = wordsB nvq` of the witness,
and at most `11·10¹² (d+1) (𝔟+1)³`. -/
theorem nv_select_lemma : ∃ bd : ℕ,
    nvq.params.nu ≤ 196608 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) * nvq.ζ ∧
    98304 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) * nvq.ζ ≤ nvq.params.nu ∧
    nvq.b ≤ bd ∧ HasBits bd nvq.c0 ∧ HasBits bd nvq.T ∧ HasBits bd nvq.etaH ∧
    HasBits bd nvq.etaD ∧
    nGatesN (nativeSel (L := LabW nvq.params.m nvq.params.l) nvq.params.a nvq.params.m
      nvq.params.tau nvq.params.Q nvq.params.qbar (4 * nvq.params.nu) nvq.UJg (ndQ nvq)
      (arQ nvq)) ≤ 394300 * (nvq.params.d + 1) * (wordsB nvq + 1) ^ 3 ∧
    (nGatesN (nativeSel (L := LabW nvq.params.m nvq.params.l) nvq.params.a nvq.params.m
      nvq.params.tau nvq.params.Q nvq.params.qbar (4 * nvq.params.nu) nvq.UJg (ndQ nvq)
      (arQ nvq)) : ℝ) ≤
      11 * 10 ^ 12 * ((nvq.params.d : ℝ) + 1) * (bitB bd (2 ^ nvq.kx) (2 ^ nvq.m) (2 ^ nvq.m)
        (qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2)) nvq.g nvq.ε + 1) ^ 3 := by
  obtain ⟨bd, -, -, hζl, hb, hc0, hT, hH, hD⟩ :=
    withChoiceT_bits pointPubT pointPubT_ok
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨1, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
      ⟨0, 0, by norm_num [pointPubT, GateBitBudget.pointPubT₀]⟩
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  have hζ : 98304 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) * nvq.ζ ≤
      nvq.params.nu := by linarith
  obtain ⟨hrH, hcH, hrD, hcD⟩ := nv_energies
  have hν := (nvq.params_ok nvq_ok).nu_pos
  have hst : ∀ t ∈ Set.Icc 0 nvq.T,
      star ((0 : ℝ → Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) t) =
        (0 : ℝ → Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) t := fun _ _ => by
    simp only [Pi.zero_apply]
    exact star_zero (Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ)
  have hcert : ∀ z, sampleErr (0 : ℝ → Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) 0
      (kOf nvq) (vOf nvq) (XOf nvq nvData (Equiv.refl _) ()) nvq.T nvq.params.m z ≤
      nvq.params.nu / 8 := fun z => by
    rw [nv_sampleErr_zero]
    positivity
  have hfr : 16 * (0 + nvq.params.R * 0) * nvq.T ^ 2 ≤ 4 * nvq.params.nu * 2 ^ nvq.params.m := by
    simp only [mul_zero, add_zero, zero_mul]
    exact mul_nonneg (by linarith) (by positivity)
  refine ⟨bd, hζl, hζ, hb, hc0, hT, hH, hD,
    (binary_select_lemma_words (X := Unit) nvq nvq_ok nvq_γ hζ nvData (Equiv.refl _)
      (pointData_range _ 1 1) nvData_dec () hrH hcH hrD hcD 0 0 0 0 le_rfl le_rfl hfr hst hst
      (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) hcert).2.1,
    (binary_select_lemma_bits (X := Unit) nvq bd nvq_ok nvq_γ hζl hζ hb hc0 hT hH hD nvData
      (Equiv.refl _) (pointData_range _ 1 1) nvData_dec () hrH hcH hrD hcD 0 0 0 0 le_rfl le_rfl
      hfr hst hst (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) hcert).2.1⟩

/-! #### The left-endpoint quadrature -/

/-- The zero forcing samples. -/
def nvz (_ : ℕ) : Reg (Fin nvq.kx) ℂ := 0

/-- The homogeneous branch solutions with the left-endpoint weights. -/
def nvlys (s : Bool × (Fin nvq.m → Bool)) (_ : ℝ) : Reg (Fin nvq.kx) ℂ :=
  nvq.params.zsrc (nvhxs 0) (bsW nvq.params (GateQuad.wQ nvq.params nvq.params.M) nvz) s

theorem nvl_mass :
    nvq.params.mass (nvhxs 0) (bsW nvq.params (GateQuad.wQ nvq.params nvq.params.M) nvz) = 1 := by
  rw [mass_bsW nvq.params nvq_ok.T_pos (nvhxs 0) _ (fun u hu => by
    unfold GateQuad.wQ
    rw [if_pos hu]
    exact div_nonneg nvq_ok.T_pos.le (Nat.cast_nonneg _)) nvz]
  simp [nvhxs, nvz, norm_seedV]

theorem nvl_zsrc (s : Bool × (Fin nvq.params.m → Bool)) :
    nvq.params.zsrc (nvhxs 0) (bsW nvq.params (GateQuad.wQ nvq.params nvq.params.M) nvz) s =
      if s = (false, fun _ => false) then seedV else 0 := by
  obtain ⟨c, w⟩ := s
  cases c
  · unfold GateODE.Time.TParams.zsrc
    simp [nvhxs]
  · rw [zsrc_bsW nvq.params nvq_ok.T_pos]
    simp [nvz]

theorem nvl_prep (w : Cfg (Fin (nvq.params.m + 1))) :
    (1 : Matrix (Cfg (Fin (nvq.params.m + 1))) (Cfg (Fin (nvq.params.m + 1))) ℂ) w
        (fun _ => false) =
      ((nvq.params.srcAmp (nvhxs 0) (bsW nvq.params (GateQuad.wQ nvq.params nvq.params.M) nvz)
        (w 0, Fin.tail w) : ℝ) : ℂ) := by
  unfold GateODE.Time.TParams.srcAmp
  rw [nvl_mass, nvl_zsrc]
  by_cases hw : w = fun _ => false
  · subst hw
    have h1 : (((fun _ => false : Cfg (Fin (nvq.params.m + 1))) 0,
        Fin.tail (fun _ => false : Cfg (Fin (nvq.params.m + 1)))) :
          Bool × (Fin nvq.params.m → Bool)) = (false, fun _ => false) := rfl
    rw [h1, Matrix.one_apply_eq]
    simp [norm_seedV]
  · have h1 : ((w 0, Fin.tail w) : Bool × (Fin nvq.params.m → Bool)) ≠ (false, fun _ => false) := by
      intro h
      apply hw
      have h0 : w 0 = false := congrArg Prod.fst h
      have ht : Fin.tail w = fun _ => false := congrArg Prod.snd h
      rw [← Fin.cons_self_tail w, h0, ht]
      funext j
      refine Fin.cases rfl (fun i => rfl) j
    rw [Matrix.one_apply_ne hw, if_neg h1]
    simp

/-- **Every condition of `RestL` holds for the homogeneous witness**: `x' = 0` on `[0, 1]` with
`x(0) = seedV`, the left-endpoint weights `T/2^m` with zero forcing samples, the zero generator
path (`Λ = 0`), the zero forcing (`L = b_s = δb = 0`), the loading `1` and the identity weight
preparation, the constant branch solutions and `βG = δG = 0`. -/
theorem nvh_restL :
    RestL nvq nvData (Equiv.refl _) () (fun _ => 1) 1 nvz 0 0 nvhxs nvlys 0 0 0 0 0 0 where
  load_unitary := fun _ => isUnitary_one
  prep_left := by simp
  prep_right := by simp
  prep := nvl_prep
  init_load := fun _ => by
    show (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ) seedV = unitDirection (nvhxs 0)
    simp [nvhxs, unitDirection, norm_seedV]
  forcing_load := fun _ h => absurd rfl h
  solves := fun u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  accretive := fun u _ v => by simp
  lipG := fun u _ u' _ => by simp
  βG_nonneg := le_rfl
  sampleG := fun s r hr => by simp [nv_mLift_zero]
  normG := fun u _ => by simp
  lipb := fun u _ u' _ => by simp
  L_nonneg := le_rfl
  sample_norm := fun u _ => by simp [nvz]
  sample_err := fun u _ => by simp [nvz]
  branch_sol := fun s u _ => (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)
  branch_init := fun s => rfl
  target_ne := seedV_ne
  budget := by
    unfold GateQuad.quadMass
    simp [nvhxs, nvz, norm_seedV, nvq_g]
  disc := by
    unfold GateQuad.quadMass
    simp only [nvhxs, nvz, norm_seedV, norm_zero, mul_zero, Finset.sum_const_zero, add_zero,
      zero_mul, zero_div, nvq_ε, nvq_g]
    norm_num

/-- **The guarantee of the solver with the left-endpoint quadrature holds for explicit data**:
with the homogeneous witness `nvh_restL`, empty loading and weight-preparation circuits and
`ζs = 0`, every hypothesis of `binary_select_solverL` holds, and the native protocol has the
guarantees `NOutcome` for `x(T) = seedV`. -/
theorem nv_select_outcomeL :
    NOutcome (prepQ nvq ([] : List (NInstr ((Fin (nvq.params.m + 1) ⊕ Fin nvq.kx) ⊕ Empty)
        (Fin (2 * nvq.m) ⊕ PY nvq.kx nvq.b) Query)) [])
      nvq.params.ratio nvq.ε (nvq.params.ratio_ge nvq_ok.g_ge)
      (primsT (R := ℂ) (m := 2 * nvq.m) nvData (Equiv.refl _) ()) seedV := by
  obtain ⟨-, -, -, hiff⟩ := withChoiceT_spec pointPubT pointPubT_ok
  have h0 := (hiff 0).mpr (by have := (nvq.params_ok nvq_ok).nu_pos; linarith)
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes nvq nvq_ok nvq_γ
  have hd' : (nvq.params.d : ℝ) ≤
      4096 * qOf nvq.s nvq.T nvq.etaH nvq.etaD (2 * nvq.g) (nvq.ε / 2) := hd
  have hbud : 24 * (nvq.params.d : ℝ) * nvq.ζ + 3 * 0 ≤ nvq.params.nu := by
    have h1 := mul_le_mul_of_nonneg_right hd' nvq_ok.ζ_pos.le
    linarith
  obtain ⟨hrH, hcH, hrD, hcD⟩ := nv_energies
  have hL : ∀ k : ℕ, loadIdeal (k := k) (S := Fin nvq.kx)
      (fun _ => (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ)) = 1 := by
    intro k
    unfold loadIdeal
    exact localOp_one _
  refine binary_select_solverL (X := Unit) (Zs := Empty) nvq nvq_ok nvData (Equiv.refl _)
    (pointData_range _ 1 1) nvData_dec [] (fun _ hi => by simp at hi) []
    (fun _ hi => by simp at hi) () hrH hcH hrD hcD nv_psd
    (fun _ : Bool × (Fin nvq.params.m → Bool) => (1 : Reg (Fin nvq.kx) ℂ →L[ℂ] Reg (Fin nvq.kx) ℂ))
    (1 : Matrix (Cfg (Fin (nvq.params.m + 1))) (Cfg (Fin (nvq.params.m + 1))) ℂ) nvz 0 0 nvhxs
    nvlys 0 0 0 0 0 0 0 le_rfl ?_ ?_ hbud nvh_restL
  · rw [nrun_nil, hL, liftB_one]
    intro ψ _
    simp
  · rw [nrun_nil, matOp_one, liftB_one]
    intro ψ _
    simp

end Instance

end

end SparseHamiltonian.GateBinarySelect
