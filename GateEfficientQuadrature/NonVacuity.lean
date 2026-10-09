import GateEfficientQuadrature.Solver
import GateEfficientSelect.ODE.NonVacuity

/-!
# The solver with the left-endpoint quadrature is not vacuous

Every condition of `LInstanceOK` holds at once for explicit data with an interior quadrature node,
a forcing of positive Lipschitz constant, sample errors `δ > 0` and a positive certificate
bound, and `outcomeL` (the instance clause of `solverL`) then applies (`nvL_outcome`):

* the public data `GateSelect.ODE.nvP` (`T = 1`, `g = 1`, `ε = 1/2`, `m = 1`, two slots and two
  forcing labels; the released `PublicOK` by `GateSelect.ODE.nvP_ok`);
* the problem `x' = 1 + t / 4000` on `[0, 1]` with `x(0) = 0` (zero generator), the solution
  `x(t) = t + t² / 8000`, `x(1) = 1 + 1/8000`;
* the left-endpoint quadrature with `n = 2` nodes `0` and `1/2` of weight `1/2`; the forcing
  branch of the node `1/2` runs on `[1/2, 1]` with the addresses `1/2` and `3/4`, and `3/4` is not
  a point of the common mesh `{0, 1/2}`;
* the samples `f_0 = f_1 = 1 + 1/16000` (the mean of `b(0) = 1` and `b(1/2) = 1 + 1/8000`), so
  that `δ = 1/16000`, `b_s = 1 + 1/16000`, `L = 1/4000`, `Λ = 0` and the certificate bound is
  `κ = L T² / 4 + T δ = 1/8000` (`nvL_kappa`); the certificate error is `1/16000` (`nvL_error`);
  the quadrature mass is `B_2 = 1 + 1/16000`, within the budget `B_2 ≤ g ‖x(1)‖` and
  `κ ≤ ε B_2 / (2000 g)`;
* the supplied unitaries: `U_J = 1`, the scalar private operation `-1` (the clock promise for the
  zero normalised Hamiltonian), the loading `1` and the weight preparation `nvWp2 = X ⊗ H`, whose
  column at the zero word carries the amplitudes `1/√2` of the two forcing labels.

The generator of the witness is zero, so `Λ = βG = δG = 0` there, its branch samples and clock
promises hold trivially, and `x(0) = 0` makes the initial loading condition vacuous. With
`n = 2^m` it has no padding label; the second witness `nvL1_instance` (one node `0`, the exact
sample `f_0 = b(0) = 1`, the second forcing label as padding of weight `0` at the node `1`, the
weight preparation `GateSelect.ODE.nvWp` and `κ = 1/8000`, which is its exact certificate error,
`nvL1_error`) exercises the padding, and `nvL1_outcome` applies `outcomeL` to it.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateQuad

noncomputable section
open Set
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE.Time (TParams TOracles gens)
open GatePointerEncoding (wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open GateSelect GateSelect.ODE
open scoped InnerProduct BigOperators

/-! ### The weight preparation `X ⊗ H` -/

theorem cfg2_eq (i : Cfg (Fin 2)) : i = ![i 0, i 1] := by
  funext k
  fin_cases k <;> rfl

/-- The weight preparation `X ⊗ H` on the two wires `(initial-or-forcing bit, source bit)`. -/
def nvWp2 : Matrix (Cfg (Fin 2)) (Cfg (Fin 2)) ℂ := Matrix.of fun i j =>
  if i 0 = !j 0 then (if i 1 = true ∧ j 1 = true then -((Real.sqrt (1 / 2) : ℝ) : ℂ)
    else ((Real.sqrt (1 / 2) : ℝ) : ℂ)) else 0

theorem inv_sqrt_two_sq :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem nvWp2_mul_self : nvWp2 * nvWp2 = 1 := by
  ext i j
  rw [Matrix.mul_apply, ← (piFinTwoEquiv fun _ => Bool).symm.sum_comp, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  simp only [piFinTwoEquiv_symm_apply]
  rw [cfg2_eq i, cfg2_eq j]
  generalize i 0 = a
  generalize i 1 = b
  generalize j 0 = c
  generalize j 1 = d
  cases a <;> cases b <;> cases c <;> cases d <;> simp [nvWp2] <;> rw [inv_sqrt_two_sq] <;>
    norm_num

theorem nvWp2_conjTranspose : nvWp2.conjTranspose = nvWp2 := by
  ext i j
  simp only [Matrix.conjTranspose_apply, nvWp2, Matrix.of_apply]
  rw [cfg2_eq i, cfg2_eq j]
  generalize i 0 = a
  generalize i 1 = b
  generalize j 0 = c
  generalize j 1 = d
  cases a <;> cases b <;> cases c <;> cases d <;> simp

/-! ### The instance -/

/-- The supplied unitaries: `U_J = 1`, the private operation `-1` at every label and slot, the
loading `1` and the weight preparation `X ⊗ H`. -/
def nvσ2 : TOracles nvP.a nvP.m nvP.l ℂ :=
  ⟨1, fun _ _ => cayleyScalar 0 • 1, fun _ => 1, nvWp2⟩

/-- The forcing `b(t) = 1 + t / 4000`. -/
def nvB (t : ℝ) : ℂ := ((1 + t / 4000 : ℝ) : ℂ)

/-- The solution `x(t) = t + t² / 8000`. -/
def nvXL (t : ℝ) : ℂ := ((t + t ^ 2 / 8000 : ℝ) : ℂ)

/-- The forcing samples `f_q = 1 + 1/16000`. -/
def nvFL (_q : ℕ) : ℂ := ((1 + 1 / 16000 : ℝ) : ℂ)

/-- The homogeneous branch solutions: `(1/2)(1 + 1/16000)` on the forcing labels, `0` on the
initial labels. -/
def nvYL (s : Bool × (Fin 1 → Bool)) (_t : ℝ) : ℂ :=
  if s.1 then ((1 / 2 * (1 + 1 / 16000) : ℝ) : ℂ) else 0

theorem nvL_quadMass : quadMass (nvXL 0) nvFL nvP.T 2 = 1 + 1 / 16000 := by
  simp only [quadMass, nvXL, nvFL, Finset.sum_range_succ, Finset.sum_range_zero,
    Complex.norm_real, Real.norm_eq_abs]
  norm_num [nvP]

theorem nvL_mass : nvP.mass (nvXL 0) (bsW nvP (wQ nvP 2) nvFL) = 1 + 1 / 16000 := by
  rw [mass_wQ nvP (by norm_num [nvP]) (by norm_num [nvP]), nvL_quadMass]

theorem nvL_zsrc (s : Bool × (Fin 1 → Bool)) :
    nvP.zsrc (nvXL 0) (bsW nvP (wQ nvP 2) nvFL) s = nvYL s 0 := by
  obtain ⟨c, w⟩ := s
  cases c
  · unfold GateODE.Time.TParams.zsrc nvYL
    simp [nvXL]
  · rw [zsrc_bsW nvP (by norm_num [nvP])]
    have hw : wordValue w < 2 := GatePointerEncoding.wordValue_lt_pow w
    unfold nvYL wQ nvFL
    rw [if_pos hw, smul_eq_mul, ← Complex.ofReal_mul, if_pos rfl]
    norm_num [nvP]

/-- **Every condition of `LInstanceOK` holds** for the explicit data, with `n = 2`, `Λ = 0`,
`L = 1/4000`, `b_s = 1 + 1/16000` and `δ = 1/16000`. -/
theorem nvL_instance :
    LInstanceOK nvP 2 (1 : ℂ) nvσ2 nvFL (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) nvB nvXL nvYL
      0 0 0 (1 / 4000) (1 + 1 / 16000) (1 / 16000) := by
  have hmass := nvL_mass
  constructor
  · norm_num
  · norm_num [nvP]
  · exact isUnitary_one
  · intro z r _
    exact isUnitary_smul_one 0 _ (cayleyScalar_norm 0)
  · intro z r _
    have e : branchHB nvP (vQ nvP 2) (fun _ _ => 0) (fun _ _ => 0) z r =
        ((0 : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
      ext
      simp [branchHB]
    rw [e]
    exact clock_scalar 0 0 (by norm_num)
  · intro s r _; exact star_zero _
  · intro s r _; exact star_zero _
  · intro s r _; simp
  · intro s r _; simp
  · intro s r _ w; simp
  · intro s; exact isUnitary_one
  · show nvWp2.conjTranspose * nvWp2 = 1
    rw [nvWp2_conjTranspose, nvWp2_mul_self]
  · show nvWp2 * nvWp2.conjTranspose = 1
    rw [nvWp2_conjTranspose, nvWp2_mul_self]
  · intro w
    show nvWp2 w (fun _ => false) =
      ((Real.sqrt (‖nvP.zsrc (nvXL 0) (bsW nvP (wQ nvP 2) nvFL) (w 0, Fin.tail w)‖ /
        nvP.mass (nvXL 0) (bsW nvP (wQ nvP 2) nvFL)) : ℝ) : ℂ)
    rw [hmass, nvL_zsrc]
    unfold nvWp2 nvYL
    simp only [Matrix.of_apply, Bool.not_false]
    cases h : w 0
    · simp
    · have e : ‖((1 / 2 * (1 + 1 / 16000) : ℝ) : ℂ)‖ / (1 + 1 / 16000) = 1 / 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        norm_num
      simp only [if_true, e]
      simp
  · intro h
    exact absurd (by simp [nvXL]) h
  · intro w _ _
    show (1 : ℂ →L[ℂ] ℂ) 1 = unitDirection (((1 + 1 / 16000 : ℝ) : ℂ))
    have e : (((1 + 1 / 16000 : ℝ) : ℂ)) = (1 + 1 / 16000 : ℝ) • (1 : ℂ) := by
      rw [Complex.real_smul, mul_one]
    rw [e, ODEHeraldedSuccess.unitDirection_pos_smul _ (by norm_num)]
    simp [unitDirection]
  · intro u _
    have h1 : HasDerivAt (fun t : ℝ => t + t ^ 2 / 8000) (1 + u / 4000) u := by
      have := (hasDerivAt_id u).add ((hasDerivAt_pow 2 u).div_const 8000)
      exact this.congr_deriv (by norm_num; ring)
    have h := (h1.ofReal_comp).hasDerivWithinAt (s := Icc 0 nvP.T)
    refine h.congr_deriv ?_
    simp [nvB]
  · intro u _ w; simp
  · intro u _ u' _; simp
  · exact le_rfl
  · intro s r _; simp [gens]
  · intro u _; simp
  · intro u _ u' _
    unfold nvB
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e : 1 + u / 4000 - (1 + u' / 4000) = (u - u') / 4000 := by ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4000)]
    ring_nf
    exact le_rfl
  · norm_num
  · intro q _
    simp only [nvFL, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num)]
  · intro q hq
    interval_cases q
    · simp only [nvB, nvFL]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      norm_num [nvP]
    · simp only [nvB, nvFL]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      norm_num [nvP]
  · intro s u _
    exact hasDerivWithinAt_const _ _ _ |>.congr_deriv (by simp)
  · intro s
    rw [nvL_zsrc]
    rfl
  · simp only [nvXL, ne_eq, Complex.ofReal_eq_zero]
    norm_num [nvP]
  · rw [nvL_quadMass]
    simp only [nvXL, Complex.norm_real, Real.norm_eq_abs]
    norm_num [nvP]
  · rw [nvL_quadMass]
    norm_num [nvP]

/-- **`outcomeL` applies to the explicit data**: the released protocol on the public data `nvP`
with the seed `1` satisfies the released `Outcome` for `x(1) = 1 + 1/8000`. -/
theorem nvL_outcome : nvP.Outcome (1 : ℂ) norm_one nvP_ok.g_ge nvσ2 (nvXL nvP.T) :=
  outcomeL nvP nvP_ok (1 : ℂ) norm_one nvσ2 2 nvFL (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
    nvB nvXL nvYL 0 0 0 (1 / 4000) (1 + 1 / 16000) (1 / 16000) nvL_instance

/-- The certificate error of the witness is `1/16000`. -/
theorem nvL_error : ‖nvXL nvP.T - ∑ s, nvYL s nvP.T‖ = 1 / 16000 := by
  have hsum : ∑ s, nvYL s nvP.T = ((1 + 1 / 16000 : ℝ) : ℂ) := by
    rw [sum_labels nvP]
    simp only [nvYL, Bool.false_eq_true, if_false, if_true, Finset.sum_const_zero, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [nsmul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    norm_num
  rw [hsum]
  unfold nvXL
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  norm_num [nvP]

/-- The certificate bound of the witness: `κ = (Λ b_s + L) T² / (2n) + T δ = 1/8000`. -/
theorem nvL_kappa : ((0 : ℝ) * (1 + 1 / 16000) + 1 / 4000) * nvP.T ^ 2 / (2 * ((2 : ℕ) : ℝ)) +
    nvP.T * (1 / 16000) = 1 / 8000 := by
  norm_num [nvP]


/-! ### A witness with a padding label -/

/-- The exact forcing sample `f_q = 1 = b(0)`. -/
def nvF1 (_q : ℕ) : ℂ := 1

theorem nvL1_quadMass : quadMass (nvXL 0) nvF1 nvP.T 1 = 1 := by
  simp [quadMass, nvXL, nvF1]

theorem nvL1_mass : nvP.mass (nvXL 0) (bsW nvP (wQ nvP 1) nvF1) = 1 := by
  rw [mass_wQ nvP (by norm_num [nvP]) (by norm_num [nvP]), nvL1_quadMass]

theorem nvL1_zsrc (s : Bool × (Fin 1 → Bool)) :
    nvP.zsrc (nvXL 0) (bsW nvP (wQ nvP 1) nvF1) s = nvY s 0 := by
  obtain ⟨c, w⟩ := s
  cases c
  · unfold GateODE.Time.TParams.zsrc nvY
    simp [nvXL]
  · rw [zsrc_bsW nvP (by norm_num [nvP])]
    unfold nvY wQ nvF1
    rw [wordValue_fin_one]
    rcases (fin_one_fun_eq w) with hw
    cases h : w 0
    · have : w = fun _ => false := by rw [hw, h]
      simp [this]
    · have : w ≠ fun _ => false := by
        intro e
        rw [e] at h
        exact absurd h (by decide)
      simp [this]

/-- **Every condition of `LInstanceOK` holds** for one node `0` (the second forcing label is
padding of weight `0` at the node `1`), with `Λ = 0`, `L = 1/4000`, `b_s = 1` and `δ = 0`. -/
theorem nvL1_instance :
    LInstanceOK nvP 1 (1 : ℂ) nvσ nvF1 (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) nvB nvXL nvY
      0 0 0 (1 / 4000) 1 0 := by
  have hmass := nvL1_mass
  constructor
  · norm_num
  · norm_num [nvP]
  · exact isUnitary_one
  · intro z r _
    exact isUnitary_smul_one 0 _ (cayleyScalar_norm 0)
  · intro z r _
    have e : branchHB nvP (vQ nvP 1) (fun _ _ => 0) (fun _ _ => 0) z r =
        ((0 : ℝ) : ℂ) • (1 : ℂ →L[ℂ] ℂ) := by
      ext
      simp [branchHB]
    rw [e]
    exact clock_scalar 0 0 (by norm_num)
  · intro s r _; exact star_zero _
  · intro s r _; exact star_zero _
  · intro s r _; simp
  · intro s r _; simp
  · intro s r _ w; simp
  · intro s; exact isUnitary_one
  · exact (permMat_unitary (Equiv.swap nvC0 nvC1)).1
  · exact (permMat_unitary (Equiv.swap nvC0 nvC1)).2
  · intro w
    show nvWp w (fun _ => false) =
      ((Real.sqrt (‖nvP.zsrc (nvXL 0) (bsW nvP (wQ nvP 1) nvF1) (w 0, Fin.tail w)‖ /
        nvP.mass (nvXL 0) (bsW nvP (wQ nvP 1) nvF1)) : ℝ) : ℂ)
    rw [hmass, nvL1_zsrc]
    unfold nvWp nvY
    simp only [Matrix.of_apply]
    by_cases hw : w = nvC1
    · subst hw
      have h1 : ((nvC1 0, Fin.tail nvC1) : Bool × (Fin 1 → Bool)) = (true, fun _ => false) := by
        decide
      have h2 : Equiv.swap nvC0 nvC1 nvC1 = (fun _ => false) := Equiv.swap_apply_right _ _
      rw [h2, h1]
      simp
    · have h1 : ((w 0, Fin.tail w) : Bool × (Fin 1 → Bool)) ≠ (true, fun _ => false) := by
        intro h
        apply hw
        have h0 : w 0 = true := congrArg Prod.fst h
        have ht : Fin.tail w = fun _ => false := congrArg Prod.snd h
        funext i
        fin_cases i
        · simp [nvC1, h0]
        · have := congrFun ht 0
          simpa [nvC1, Fin.tail] using this
      have h2 : Equiv.swap nvC0 nvC1 w ≠ (fun _ => false) := by
        intro h
        apply hw
        rw [Equiv.swap_apply_eq_iff] at h
        rw [h]
        exact Equiv.swap_apply_left _ _
      rw [if_neg h2, if_neg h1]
      simp
  · intro h
    exact absurd (by simp [nvXL]) h
  · intro w _ _
    show (1 : ℂ →L[ℂ] ℂ) 1 = unitDirection 1
    simp [unitDirection]
  · intro u _
    have h1 : HasDerivAt (fun t : ℝ => t + t ^ 2 / 8000) (1 + u / 4000) u := by
      have := (hasDerivAt_id u).add ((hasDerivAt_pow 2 u).div_const 8000)
      exact this.congr_deriv (by norm_num; ring)
    have h := (h1.ofReal_comp).hasDerivWithinAt (s := Icc 0 nvP.T)
    refine h.congr_deriv ?_
    simp [nvB]
  · intro u _ w; simp
  · intro u _ u' _; simp
  · exact le_rfl
  · intro s r _; simp [gens]
  · intro u _; simp
  · intro u _ u' _
    unfold nvB
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e : 1 + u / 4000 - (1 + u' / 4000) = (u - u') / 4000 := by ring
    rw [e, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4000)]
    ring_nf
    exact le_rfl
  · norm_num
  · intro q _; simp [nvF1]
  · intro q hq
    have hq0 : q = 0 := by omega
    subst hq0
    simp [nvB, nvF1]
  · intro s u _
    exact hasDerivWithinAt_const _ _ _ |>.congr_deriv (by simp)
  · intro s
    rw [nvL1_zsrc]
    rfl
  · simp only [nvXL, ne_eq, Complex.ofReal_eq_zero]
    norm_num [nvP]
  · rw [nvL1_quadMass]
    simp only [nvXL, Complex.norm_real, Real.norm_eq_abs]
    norm_num [nvP]
  · rw [nvL1_quadMass]
    norm_num [nvP]

/-- **`outcomeL` applies to the witness with a padding label.** -/
theorem nvL1_outcome : nvP.Outcome (1 : ℂ) norm_one nvP_ok.g_ge nvσ (nvXL nvP.T) :=
  outcomeL nvP nvP_ok (1 : ℂ) norm_one nvσ 1 nvF1 (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0)
    nvB nvXL nvY 0 0 0 (1 / 4000) 1 0 nvL1_instance

/-- The certificate error of the witness with a padding label is its bound
`κ = L T² / 2 = 1/8000`. -/
theorem nvL1_error : ‖nvXL nvP.T - ∑ s, nvY s nvP.T‖ = 1 / 8000 := by
  have hsum : ∑ s, nvY s nvP.T = 1 := by
    unfold nvY
    rw [Finset.sum_ite_eq']
    simp
  rw [hsum]
  unfold nvXL
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  norm_num [nvP]

end

end SparseHamiltonian.GateQuad
