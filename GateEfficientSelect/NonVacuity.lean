import GateEfficientSelect.Lemma

/-!
# The coherent selection lemma is not vacuous

Every hypothesis of `gate_select` (Lemma `ode:lem:gate-select`) holds at once for explicit data
with two labels on different meshes and with different frequencies, on every system `P` and for
every number `a` of ancilla qubits:

* `cayleyScalar s = (i s - 1)/(1 + i s)` has modulus one (`cayleyScalar_norm`), and the scalar
  operation `cayleyScalar s • 1` with `U_J = 1` carries the clock promise of the released
  simulator for the normalised sample `s • 1`, `|s| ≤ 1`, with `Q = qbar = 1`
  (`clock_scalar`: `R₁ = ((1 + i s)/2) • 1`);
* `nv_all_hyps`: one label wire (two labels) with the start times `0` and `1/2` (`nvStart`) and
  the frequencies `0` and `1` (`nvK`, `R = 1`), the time-dependent Hamiltonian `H(t) = t · 1`
  with Lipschitz bound `1`, the path `D(t) = (1/4) · 1` (`nvDp`), represented samples `nvX`
  with error `1/16` at the branch addresses `nvStart z + j (1 - nvStart z) / 16` of `m = 4` slot
  wires (`nv_sample_eq`), the scalar private operations `nvD` for their normalised samples,
  `T = 1`, `α = 2`, `Q = qbar = 1`, `δ = 1/16` and `ε = 1/2`; the subdivision condition holds
  since `steps 2 (1/12) ≤ 16` (`nv_steps`);
* `nv_select`: hence `gate_select` applies, and the selection circuit is within `1/2` of the
  controlled direct sum of the propagators of the two branches, which exist.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire Vsp iota0 iota0_isometry simR fDeg)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Scalar clock promises -/

/-- The Cayley parameter of the scalar private operation for the normalised sample `s • 1`. -/
def cayleyScalar (s : ℝ) : ℂ := (Complex.I * s - 1) / (1 + Complex.I * s)

theorem one_add_I_mul_ne_zero (s : ℝ) : (1 + Complex.I * s) ≠ 0 := by
  intro h
  have h1 := congrArg Complex.re h
  simp at h1

theorem cayleyScalar_norm (s : ℝ) : ‖cayleyScalar s‖ = 1 := by
  unfold cayleyScalar
  have h1 : ‖Complex.I * s - 1‖ = ‖1 + Complex.I * s‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
  rw [norm_div, h1, div_self (norm_ne_zero_iff.mpr (one_add_I_mul_ne_zero s))]

omit [CompleteSpace P] in
/-- The scalar operators `x • 1` compose by multiplication. -/
theorem smul_one_comp (a : ℕ) (x y : ℂ) :
    (x • (1 : Vsp a P →L[ℂ] Vsp a P)) ∘L (y • (1 : Vsp a P →L[ℂ] Vsp a P)) =
      (x * y) • (1 : Vsp a P →L[ℂ] Vsp a P) := by
  rw [smul_comp, comp_smul, smul_smul]
  rfl

/-- A scalar multiple of the identity by a number of modulus one is unitary. -/
theorem isUnitary_smul_one (a : ℕ) (c : ℂ) (hc : ‖c‖ = 1) :
    IsUnitary (c • (1 : Vsp a P →L[ℂ] Vsp a P)) := by
  have h1 : star c * c = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hc]
    simp
  refine ⟨?_, ?_⟩
  · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, h1, one_smul]
  · rw [star_smul, star_one, smul_mul_smul_comm, one_mul, mul_comm, h1, one_smul]

/-- **Scalar clock promises.** With `U_J = 1`, the scalar operation `cayleyScalar s • 1` carries
the clock promise of the released simulator for the normalised sample `s • 1`, `|s| ≤ 1`, with
`Q = qbar = 1`. -/
theorem clock_scalar (a : ℕ) (s : ℝ) (hs : |s| ≤ 1) :
    GateODE.ClockPromise (1 : Vsp a P →L[ℂ] Vsp a P) (cayleyScalar s • 1)
      ((s : ℂ) • (1 : P →L[ℂ] P)) 1 1 := by
  set c : ℂ := (1 + Complex.I * s) / 2 with hc
  have hne := one_add_I_mul_ne_zero s
  have hcs : (1 - cayleyScalar s) * c = 1 := by
    rw [hc]
    unfold cayleyScalar
    field_simp
    ring
  have he : (1 - cayleyScalar s • (1 : Vsp a P →L[ℂ] Vsp a P)) =
      (1 - cayleyScalar s) • (1 : Vsp a P →L[ℂ] Vsp a P) := by
    module
  have hc2 : ‖c‖ ^ 2 ≤ 1 / 2 := by
    rw [hc, norm_div, Complex.norm_two, div_pow, Complex.sq_norm, Complex.normSq_apply]
    have hs2 : s ^ 2 ≤ 1 := by
      have := sq_abs s
      nlinarith [abs_nonneg s]
    simp
    nlinarith
  have hcle : ‖c‖ ≤ 1 := by nlinarith [norm_nonneg c]
  have hJ : (1 : Vsp a P →L[ℂ] Vsp a P) ∘L iota0 = iota0 := id_comp _
  have hι : ‖(iota0 (a := a) (P := P))‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one (fun p => ?_)
    rw [(norm_map_iff_adjoint_comp_self _).mpr iota0_isometry p, one_mul]
  refine ⟨⟨c • 1, ‖c‖, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [he, smul_one_comp, hcs, one_smul]
  · rw [he, smul_one_comp, mul_comm, hcs, one_smul]
  · exact (opNorm_smul_le _ _).trans (mul_le_one₀ hcle (norm_nonneg _) norm_id_le)
  · rw [hJ, smul_comp, hJ, comp_smul, iota0_isometry, hc]
    module
  · rw [hJ, smul_comp, hJ]
    exact (opNorm_smul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hι)
  · linarith

/-! ### Two labels on different meshes -/

/-- The start times of the two labels of one label wire: `0` and `1/2`. -/
def nvStart (z : Cfg (Fin 1)) : ℝ := if z 0 then 1 / 2 else 0

/-- The frequencies of the two labels: `0` and `1`. -/
def nvK (z : Cfg (Fin 1)) : ℝ := if z 0 then 1 else 0

/-- The time-dependent Hamiltonian `H(t) = t · 1`. -/
def nvH (t : ℝ) : P →L[ℂ] P := ((t : ℝ) : ℂ) • 1

/-- The dissipative path `D(t) = (1/4) · 1`. -/
def nvDp (_t : ℝ) : P →L[ℂ] P := ((1 / 4 : ℝ) : ℂ) • 1

/-- The branch addresses of `m = 4` slot wires. -/
def nvAddr (z : Cfg (Fin 1)) (j : ℕ) : ℝ := nvStart z + j * (1 - nvStart z) / 2 ^ 4

/-- The scalar value of the represented sample: the exact value `t + k_z/4` at the address,
with the sample error `1/16`. -/
def nvVal (z : Cfg (Fin 1)) (j : ℕ) : ℝ := nvAddr z j + nvK z / 4 + 1 / 16

/-- The represented samples, within `1/16` of `H + k_z D` at the branch addresses. -/
def nvX (z : Cfg (Fin 1)) (j : ℕ) : P →L[ℂ] P := ((nvVal z j : ℝ) : ℂ) • 1

/-- The scalar private operations for the normalised samples of the branches. -/
def nvD (a : ℕ) (z : Cfg (Fin 1)) (j : ℕ) : Vsp a P →L[ℂ] Vsp a P :=
  cayleyScalar ((1 - nvStart z) / (2 * 1) * nvVal z j) • 1

theorem nvStart_mem (z : Cfg (Fin 1)) : 0 ≤ nvStart z ∧ nvStart z ≤ 1 / 2 := by
  unfold nvStart
  split_ifs <;> norm_num

theorem nvK_mem (z : Cfg (Fin 1)) : 0 ≤ nvK z ∧ nvK z ≤ 1 := by
  unfold nvK
  split_ifs <;> norm_num

theorem nvAddr_mem (z : Cfg (Fin 1)) (j : ℕ) (hj : j < 2 ^ 4) :
    0 ≤ nvAddr z j ∧ nvAddr z j ≤ 1 := by
  obtain ⟨h0, h1⟩ := nvStart_mem z
  have hj' : (j : ℝ) ≤ 16 := by
    have : (j : ℝ) < 16 := by exact_mod_cast hj
    linarith
  unfold nvAddr
  constructor
  · have : 0 ≤ (j : ℝ) * (1 - nvStart z) / 2 ^ 4 := by
      apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (by norm_num)
    linarith
  · have : (j : ℝ) * (1 - nvStart z) / 2 ^ 4 ≤ 1 - nvStart z := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith

theorem nvVal_mem (z : Cfg (Fin 1)) (j : ℕ) (hj : j < 2 ^ 4) :
    0 ≤ nvVal z j ∧ nvVal z j ≤ 21 / 16 := by
  obtain ⟨a0, a1⟩ := nvAddr_mem z j hj
  obtain ⟨k0, k1⟩ := nvK_mem z
  unfold nvVal
  constructor <;> linarith

omit [CompleteSpace P] in
theorem smul_one_norm_le (t : ℝ) : ‖(((t : ℝ) : ℂ) • (1 : P →L[ℂ] P))‖ ≤ |t| := by
  refine (opNorm_smul_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) norm_id_le

theorem smul_one_star (t : ℝ) : star (((t : ℝ) : ℂ) • (1 : P →L[ℂ] P)) = ((t : ℝ) : ℂ) • 1 := by
  rw [star_smul, star_one, Complex.star_def, Complex.conj_ofReal]

omit [CompleteSpace P] in
theorem nvH_sub (t t' : ℝ) : (nvH t : P →L[ℂ] P) - nvH t' = nvH (t - t') := by
  unfold nvH
  rw [← sub_smul, Complex.ofReal_sub]

omit [CompleteSpace P] in
/-- The sample error of the explicit data is `1/16`. -/
theorem nv_sample_eq (z : Cfg (Fin 1)) (j : ℕ) :
    (nvH (nvAddr z j) : P →L[ℂ] P) + ((nvK z : ℝ) : ℂ) • nvDp (nvAddr z j) - nvX z j =
      ((-(1 / 16) : ℝ) : ℂ) • 1 := by
  unfold nvH nvDp nvX nvVal
  rw [smul_smul, ← add_smul, ← sub_smul]
  congr 1
  push_cast
  ring

/-- The subdivision condition of the explicit data: `steps 2 (1/12) ≤ 16`. -/
theorem nv_steps : TimeSchedule.steps (2 * 1) (1 / 2 / 6) ≤ 2 ^ 4 := by
  have hth : TimeSchedule.threshold (2 * 1) (1 / 2 / 6) ≤ 10 := by
    unfold TimeSchedule.threshold
    refine max_le (by norm_num) ?_
    rw [show ((2 : ℝ) * 1) ^ 3 / (1 / 2 / 6) = 96 by norm_num]
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hc : ⌈TimeSchedule.threshold (2 * 1) (1 / 2 / 6)⌉₊ ≤ 10 := Nat.ceil_le.mpr (by
    exact_mod_cast hth)
  unfold TimeSchedule.steps
  omega

/-- **Every hypothesis of `gate_select` holds** for the explicit data: one label wire with the
labels `(start, frequency) = (0, 0)` and `(1/2, 1)`, `H(t) = t · 1`, `D(t) = (1/4) · 1`,
represented samples with error `1/16` at the branch addresses of `m = 4` slot wires, the scalar
private operations, `T = 1`, `α = 2`, `R = 1`, Lipschitz bounds `1` and `0`, `δ = 1/16`,
`Q = qbar = 1` and `ε = 1/2`; the two labels differ in start time and frequency. -/
theorem nv_all_hyps (a : ℕ) :
    (0 : ℝ) < 1 ∧ (0 : ℝ) < 2 ∧ (0 : ℝ) ≤ 1 ∧ (0 : ℝ) ≤ 0 ∧ (1 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 1 ∧
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧
    TimeSchedule.steps (2 * 1) (1 / 2 / 6) ≤ 2 ^ 4 ∧
    4 * ((1 : ℝ) + 1 * 0) * 1 ^ 2 ≤ 1 / 2 * 2 ^ 4 ∧ 4 * (1 : ℝ) * (1 / 16) ≤ 1 / 2 ∧
    (∀ z, |nvK z| ≤ 1) ∧ (∀ z, 0 ≤ nvStart z) ∧ (∀ z, nvStart z ≤ 1) ∧
    IsUnitary (1 : Vsp a P →L[ℂ] Vsp a P) ∧
    (∀ z, ∀ j < 2 ^ 4, IsUnitary (nvD (P := P) a z j)) ∧
    (∀ z, ∀ j < 2 ^ 4, GateODE.ClockPromise (1 : Vsp a P →L[ℂ] Vsp a P) (nvD a z j)
      ((((1 - nvStart z) / (2 * 1) : ℝ) : ℂ) • nvX z j) 1 1) ∧
    (∀ z, ∀ j < 2 ^ 4, star (nvX (P := P) z j) = nvX z j) ∧
    (∀ z, ∀ j < 2 ^ 4, ‖(nvX z j : P →L[ℂ] P)‖ ≤ 2) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, star (nvH (P := P) t) = nvH t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, star (nvDp (P := P) t) = nvDp t) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      ‖(nvH t : P →L[ℂ] P) - nvH t'‖ ≤ 1 * |t - t'|) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      ‖(nvDp t : P →L[ℂ] P) - nvDp t'‖ ≤ 0 * |t - t'|) ∧
    (∀ z, ∀ j : ℕ, j < 2 ^ 4 →
      ‖(nvH (nvStart z + j * (1 - nvStart z) / 2 ^ 4) : P →L[ℂ] P) +
        ((nvK z : ℝ) : ℂ) • nvDp (nvStart z + j * (1 - nvStart z) / 2 ^ 4) - nvX z j‖ ≤
          1 / 16) ∧
    nvStart (fun _ => true) ≠ nvStart (fun _ => false) ∧
      nvK (fun _ => true) ≠ nvK (fun _ => false) := by
  refine ⟨by norm_num, by norm_num, by norm_num, le_rfl, le_rfl, le_rfl, by norm_num,
    by norm_num, nv_steps, by norm_num, by norm_num, fun z => ?_, fun z => (nvStart_mem z).1,
    fun z => (nvStart_mem z).2.trans (by norm_num), isUnitary_one,
    fun z j _ => isUnitary_smul_one a _ (cayleyScalar_norm _), ?_, fun z j _ => smul_one_star _,
    fun z j hj => (smul_one_norm_le _).trans (by
      rw [abs_of_nonneg (nvVal_mem z j hj).1]
      linarith [(nvVal_mem z j hj).2]),
    fun t _ => smul_one_star t, fun t _ => smul_one_star _, fun t _ t' _ => by
      rw [nvH_sub, one_mul]
      exact smul_one_norm_le _,
    fun _ _ _ _ => by simp [nvDp], fun z j _ => ?_, by norm_num [nvStart], by norm_num [nvK]⟩
  · rw [abs_of_nonneg (nvK_mem z).1]
    exact (nvK_mem z).2
  · intro z j hj
    have hs : ((((1 - nvStart z) / (2 * 1) : ℝ) : ℂ) • (nvX z j : P →L[ℂ] P)) =
        ((((1 - nvStart z) / (2 * 1) * nvVal z j : ℝ)) : ℂ) • (1 : P →L[ℂ] P) := by
      unfold nvX
      rw [smul_smul, Complex.ofReal_mul]
    rw [hs]
    apply clock_scalar
    obtain ⟨h0, h1⟩ := nvStart_mem z
    obtain ⟨g0, g1⟩ := nvVal_mem z j hj
    have hc0 : 0 ≤ (1 - nvStart z) / (2 * 1) := by norm_num; linarith
    have hc1 : (1 - nvStart z) / (2 * 1) ≤ 1 / 2 := by norm_num; linarith
    rw [abs_of_nonneg (mul_nonneg hc0 g0)]
    calc (1 - nvStart z) / (2 * 1) * nvVal z j ≤ 1 / 2 * (21 / 16) :=
          mul_le_mul hc1 g1 g0 (by norm_num)
      _ ≤ 1 := by norm_num
  · have e : nvStart z + j * (1 - nvStart z) / 2 ^ 4 = nvAddr z j := rfl
    rw [e, nv_sample_eq]
    refine (smul_one_norm_le _).trans (le_of_eq ?_)
    norm_num

/-- **The selection lemma applies to the explicit data**: the propagators of the two branch paths
exist, and for every family of them the selection circuit `simCircuitT a 2 1 1 (1/4) 4` with the
scalar private operations is within `1/2` of the controlled direct sum of the two branch
propagators, from the start times `0` and `1/2` to `T = 1`, with the frequencies `0` and `1`. -/
theorem nv_select (a : ℕ) :
    (∀ z, ∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧
      TimeDependent.SolvesOn (branchPath nvH nvDp nvK nvStart z) U 0 (1 - nvStart z)) ∧
    ∀ U : Cfg (Fin 1) → ℝ → P →L[ℂ] P, (∀ z, U z 0 = 1) →
      (∀ z, TimeDependent.SolvesOn (branchPath nvH nvDp nvK nvStart z) (U z) 0
        (1 - nvStart z)) →
      ‖runS (1 : Vsp a P →L[ℂ] Vsp a P) (nvD a)
          (SlotSim.simCircuitT a (2 * 1) 1 1 (1 / 2 / 2) 4) ∘L selE -
        selE ∘L WeightedClock.diagonal (fun z => U z (1 - nvStart z))‖ ≤ 1 / 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, -⟩ := nv_all_hyps (P := P) a
  obtain ⟨-, -, -, -, -, -, -, -, hex, herr⟩ := gate_select (L := Fin 1) a 4 1 (nvD a) nvH nvDp
    nvK nvStart nvX 1 2 1 1 0 (1 / 16) 1 1 (1 / 2) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24
  exact ⟨hex, herr⟩

end

end SparseHamiltonian.GateSelect
