import GateEfficientBinaryODE.Boundary

/-!
# The rounded LCHS step and the clock promises of the four sectors

The ingredients of the native solver from binary data that do not depend on the bundled public
data:

* the LCHS step `h` of the public grid is in `(0, 1]` (`hStep_le_one`, from `exp π ≤ 81` and
  `ν ≤ 1/10000`); with `F = fOf p ζ` fractional bits, `2^F h ≥ 4/ζ`, so the rounded step
  `Hn = round(2^F h)` satisfies `Hn ≥ 2/ζ`, `Hn < 2^(F+1)` and the step factor `ρ_L = 2^F h / Hn`
  is within `ζ/4` of one (`rhoL_close`); the integer layout `layOf` is admissible (`layOf_ok`);
* the qubit lift with payload `ℂ` preserves accretivity (`re_inner_qlift_nonneg`), and a Hermitian
  matrix on the sparsity pattern with row and column energies at most `η²` has operator norm at
  most `√(2s) η` (`norm_matrixOperator_le`, from the tagged compression);
* the lifted Hamiltonian part `hLift`, dissipative part `lLift` and matrix `mLift`, with the
  released generator `-(L + iH) = -M̂` (`gen_lift`, `target_lift`);
* the label-selected private operation `privFam`, the lifted four-sector Cayley action at the
  LCHS node of the label and the rescaling `γ dur / T`, and its clock promises (`clock4`): the
  lifted resolvent at one inverts `1 - D`, has norm at most `width(4s, γ)`, compresses on the
  boundary prepared by `hadUJ4` to `(1 + i H_z)/2` for the rescaled branch Hamiltonian `H_z` of
  the released solver, and its endpoint is at most `endpoint(γ dur / T)`, with square at most
  `moment γ / 2`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (iota0)
open SparseHamiltonian.GateODE (Params Label Oracles ClockPromise)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The LCHS step and its rounding -/

section Grid

variable (p : Params)

theorem exp_pi_le : Real.exp Real.pi ≤ 81 := by
  have h1 : Real.exp Real.pi ≤ Real.exp 4 := Real.exp_le_exp.mpr Real.pi_le_four
  have h2 : Real.exp 1 ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h4 : Real.exp 1 ^ 4 ≤ 3 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le h3 4
  linarith

theorem hStep_pos (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) :
    0 < hStep p :=
  GateODE.AnalyticLCHS.step_pos hTD hg hε hε1

/-- The LCHS step is at most one. -/
theorem hStep_le_one (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) :
    hStep p ≤ 1 := by
  refine (GateODE.AnalyticLCHS.step_le hTD hg hε hε1).trans ?_
  have hν := ImprovedODEQueryBudget.precision_pos p.g p.ε hg hε
  have hν1 := ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.g p.ε hg hε1
  have hlog : Real.pi ≤ Real.log (512 / ImprovedODEQueryBudget.precision p.g p.ε) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    refine exp_pi_le.trans ?_
    rw [le_div_iff₀ hν]
    linarith
  unfold GateODE.AnalyticLCHS.stepBound
  rw [div_le_one (by linarith [Real.pi_pos])]
  linarith

/-- The fractional bits of the LCHS step for the arithmetic accuracy `ζ`: `2^F ≥ 4 / (ζ h)`. -/
def fOf (ζ : ℝ) : ℕ := Nat.clog 2 ⌈4 / (ζ * hStep p)⌉₊

theorem fOf_spec (ζ : ℝ) (hζ : 0 < ζ) (hh : 0 < hStep p) :
    4 / ζ ≤ 2 ^ fOf p ζ * hStep p := by
  have h1 : (⌈4 / (ζ * hStep p)⌉₊ : ℝ) ≤ 2 ^ fOf p ζ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h2 : 4 / (ζ * hStep p) ≤ 2 ^ fOf p ζ := (Nat.le_ceil _).trans h1
  rw [div_le_iff₀ (mul_pos hζ hh)] at h2
  rw [div_le_iff₀ hζ]
  calc (4 : ℝ) ≤ 2 ^ fOf p ζ * (ζ * hStep p) := h2
    _ = 2 ^ fOf p ζ * hStep p * ζ := by ring

theorem round_bounds (x : ℝ) (hx : 0 ≤ x) :
    x - 1 / 2 < (⌊x + 1 / 2⌋₊ : ℝ) ∧ (⌊x + 1 / 2⌋₊ : ℝ) ≤ x + 1 / 2 := by
  constructor
  · have := Nat.lt_floor_add_one (x + 1 / 2)
    linarith
  · exact Nat.floor_le (by linarith)

theorem hRound_bounds (F : ℕ) (hh : 0 ≤ hStep p) :
    2 ^ F * hStep p - 1 / 2 < (hRound p F : ℝ) ∧ (hRound p F : ℝ) ≤ 2 ^ F * hStep p + 1 / 2 :=
  round_bounds _ (by positivity)

theorem hRound_ge (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hh : 0 < hStep p) :
    2 / ζ ≤ (hRound p (fOf p ζ) : ℝ) := by
  have h1 := fOf_spec p ζ hζ hh
  have h2 := (hRound_bounds p (fOf p ζ) hh.le).1
  have h3 : 2 ≤ 2 / ζ := by
    rw [le_div_iff₀ hζ]
    linarith
  have h4 : 4 / ζ = 2 * (2 / ζ) := by ring
  linarith

/-- **The rounded LCHS step factor** `ρ_L = 2^F h / Hn` is within `ζ/4` of one. -/
theorem rhoL_close (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hh : 0 < hStep p) :
    |rhoL p (fOf p ζ) - 1| ≤ ζ / 4 := by
  have hHn := hRound_ge p ζ hζ hζ1 hh
  have hb := hRound_bounds p (fOf p ζ) hh.le
  have hpos : 0 < (hRound p (fOf p ζ) : ℝ) := lt_of_lt_of_le (by positivity) hHn
  unfold rhoL
  rw [div_sub_one hpos.ne', abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have h1 : |2 ^ fOf p ζ * hStep p - hRound p (fOf p ζ)| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [hb.2], by linarith [hb.1]⟩
  have h2 : ζ / 4 * (2 / ζ) = 1 / 2 := by
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  have h3 := mul_le_mul_of_nonneg_left hHn (by positivity : (0 : ℝ) ≤ ζ / 4)
  linarith

theorem hRound_lt (F : ℕ) (hh0 : 0 ≤ hStep p) (hh : hStep p ≤ 1) :
    hRound p F < 2 ^ (F + 1) := by
  have hb := (hRound_bounds p F hh0).2
  have h1 : 2 ^ F * hStep p ≤ 2 ^ F := by
    calc 2 ^ F * hStep p ≤ 2 ^ F * 1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = 2 ^ F := mul_one _
  have h2 : (1 : ℝ) ≤ 2 ^ F := one_le_pow₀ (by norm_num)
  have h3 : (hRound p F : ℝ) < (2 : ℝ) ^ (F + 1) := by
    rw [pow_succ]
    linarith
  exact_mod_cast h3

/-- **The integer layout** of the arithmetic is admissible. -/
theorem layOf_ok (b F : ℕ) (hb : 0 < b) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) : (layOf p b F).OK where
  b_pos := hb
  J_le := by
    have := p.J_add_two_le
    show p.J ≤ 2 ^ p.l
    omega
  K_lt := by
    show GateODE.AnalyticLCHS.halfCount (p.T * p.lamD) p.g p.ε <
      GateODE.AnalyticLCHS.gridSize (p.T * p.lamD) p.g p.ε
    unfold GateODE.AnalyticLCHS.gridSize
    omega
  Hn_lt := hRound_lt p F (hStep_pos p hg hε hε1 hTD).le (hStep_le_one p hg hε hε1 hTD)

end Grid

/-! ### Scalar and lift facts -/

theorem width_mono (s : ℝ) {γ γ' : ℝ} (h : γ ≤ γ') : width s γ ≤ width s γ' := by
  unfold width
  exact_mod_cast Nat.ceil_mono
    (max_le_max le_rfl (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg s)))

theorem moment_mono {γ γ' : ℝ} (h0 : 0 ≤ γ) (h : γ ≤ γ') : moment γ ≤ moment γ' := by
  unfold moment
  have := pow_le_pow_left₀ h0 h 2
  linarith

section Lift

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

/-- The qubit lift with payload `ℂ` preserves accretivity. -/
theorem re_inner_qlift_nonneg (φ : Cfg V ≃ ι)
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (hA : ∀ v, 0 ≤ (inner ℂ v (A v)).re)
    (w : Reg V ℂ) : 0 ≤ (inner ℂ w (qlift (R := ℂ) φ A w)).re := by
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 (fun i => w (φ.symm i))
  have hAv : ∀ b, A v (φ b) = ∑ c, toMat φ A b c * w c := by
    intro b
    conv_lhs => rw [euclid_eq_sum v]
    rw [map_sum]
    simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← φ.sum_comp]
    apply Finset.sum_congr rfl
    intro c _
    simp [v, toMat, mul_comm]
  have key : inner ℂ w (qlift (R := ℂ) φ A w) = inner ℂ v (A v) := by
    rw [PiLp.inner_apply, PiLp.inner_apply, ← φ.sum_comp]
    apply Finset.sum_congr rfl
    intro b _
    rw [hAv, qlift_eq, matOp_apply]
    simp [v, smul_eq_mul]
  rw [key]
  exact hA v

end Lift

section Norm

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- **The operator norm** of a Hermitian matrix supported on the sparsity pattern of the input with
row and column energies at most `η²` is at most `√(2s) η`, from its tagged compression. -/
theorem norm_matrixOperator_le (D : Data X n Z s) (x : X) (K : Matrix n n ℂ)
    (hK : K.IsHermitian) (hsupp : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0)
    (η : ℝ) (hη : 0 ≤ η) (hr : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ η ^ 2)
    (hc : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ η ^ 2) :
    ‖SparseStateOverlap.matrixOperator K‖ ≤ Real.sqrt (2 * (s : ℝ)) * η := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hsq : 0 < Real.sqrt (2 * (s : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hcomp := ODEFixedTaggedMoments.compression D x K hK 1 hsupp
  have hne : ((1 : ℝ) : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_one, one_mul]
    exact_mod_cast hsq.ne'
  have hmO : SparseStateOverlap.matrixOperator K =
      (((1 : ℝ) : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ)) •
        ((ODEFixedTaggedMoments.boundary D)† ∘L
          (ODEFixedTaggedMoments.generator D x K 1 ∘L ODEFixedTaggedMoments.boundary D)) := by
    rw [hcomp, smul_smul, mul_inv_cancel₀ hne, one_smul]
  have hGB : ‖ODEFixedTaggedMoments.generator D x K 1 ∘L ODEFixedTaggedMoments.boundary D‖ ≤
      η := by
    refine opNorm_le_bound _ hη (fun v => ?_)
    have h := sector_bdry_sq D x K 1 η one_pos hr hc v
    rw [one_pow, div_one, ← mul_pow] at h
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h
  have hB : ‖(ODEFixedTaggedMoments.boundary D)†‖ ≤ 1 := by
    rw [adjoint.norm_map]
    exact SparseMatrixNorm.norm_le_one_of_adjoint_comp _
      (ODEFixedTaggedMoments.boundary_isometry D)
  rw [hmO, norm_smul, Complex.ofReal_one, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsq]
  refine mul_le_mul_of_nonneg_left ((opNorm_comp_le _ _).trans ?_) hsq.le
  calc ‖(ODEFixedTaggedMoments.boundary D)†‖ *
        ‖ODEFixedTaggedMoments.generator D x K 1 ∘L ODEFixedTaggedMoments.boundary D‖ ≤ 1 * η :=
        mul_le_mul hB hGB (norm_nonneg _) zero_le_one
    _ = η := one_mul η

end Norm

/-! ### The lifted parts and the clock promises -/

section Clock

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s k : ℕ}

/-- The qubit lift of the Hamiltonian part `(M - M†)/(2i)` of the matrix of the input `x`. -/
def hLift (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  qlift en (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.hamiltonianPart (D.matrix x)))

/-- The qubit lift of the dissipative part `(M + M†)/2` of the matrix of the input `x`. -/
def lLift (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  qlift en (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)))

/-- The qubit lift `M̂` of the matrix of the input `x` on the `k` system qubits. -/
def mLift (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  qlift en (SparseStateOverlap.matrixOperator (D.matrix x))

/-- The generator `-(L + i H)` of the released solver is `-M̂`. -/
theorem gen_lift (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) :
    GateODE.gen (hLift D en x) (lLift D en x) = -mLift D en x := by
  unfold GateODE.gen hLift lLift mLift
  rw [← qlift_smul, ← qlift_add, ← ODEMatrixEnergy.matrixOperator_smul,
    ← ODEMatrixEnergy.matrixOperator_add, ODEMatrixEnergy.decomposition]

/-- The target of the released solver is the solution of `x' = -M̂ x + b`. -/
theorem target_lift (p : Params) (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X)
    (x0 v : Reg (Fin k) ℂ) :
    p.target (hLift D en x) (lLift D en x) x0 v =
      ODEConstantForcing.solution (-mLift D en x) x0 v p.T := by
  unfold GateODE.Params.target
  rw [gen_lift]

/-- **The label-selected private operation**: the lifted four-sector Cayley action at the LCHS node
of the label and the rescaling `γ dur / T`. -/
def privFam (p : Params) (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (ρ γ : ℝ)
    (z : Label p.k p.l) :
    Reg (Fin (k + 3)) (Reg (Fin k) ℂ) →L[ℂ] Reg (Fin (k + 3)) (Reg (Fin k) ℂ) :=
  elift4 en (act4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T))

/-- **The clock promises** of every label: with `R₁` the lifted resolvent at one of the
four-sector generator and `b = endpoint (γ dur / T)`, for the common time
`τ = T √(4s) ρ / γ`. -/
theorem clock4 (p : Params) (D : Data X n Z s) (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k)
    (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (ηH ηD ρ γ : ℝ) (hηH : 0 ≤ ηH) (hηD : 0 ≤ ηD) (hρ : ρ = ηH + p.R * ηD)
    (hρpos : 0 < ρ) (hγ : 0 < γ) (hT : 0 < p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (hτ : p.tau = p.T * (Real.sqrt (4 * (s : ℝ)) * ρ) / γ)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ ηH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ ηH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ ηD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ ηD ^ 2)
    (z : Label p.k p.l) :
    ClockPromise (P := Reg (Fin k) ℂ) (a := k + 3) (UJop (R := ℂ) (hadUJ4 k σ hσ))
      (privFam p D en x ρ γ z) (p.branchH (hLift D en x) (lLift D en x) z)
      (width (4 * (s : ℝ)) γ) (moment γ) := by
  have hγz0 : 0 ≤ γ * p.dur z.1 / p.T :=
    div_nonneg (mul_nonneg hγ.le (p.dur_nonneg hT.le z.1)) hT.le
  have hγz1 : γ * p.dur z.1 / p.T ≤ γ := by
    rw [div_le_iff₀ hT]
    exact mul_le_mul_of_nonneg_left (p.dur_le hT.le z.1) hγ.le
  have hk : |p.nodeW z.2| ≤ p.R := p.nodeW_abs_le hg hε hε1 hTD z.2
  have hr : ∀ pp i, ∑ j, ‖partK (D.matrix x) (p.nodeW z.2) pp i j‖ ^ 2 ≤
      rhoP (p.nodeW z.2) ηH ηD pp ^ 2 :=
    fun pp i => partK_row_energy _ _ ηH ηD hrH hrD pp i
  have hc : ∀ pp j, ∑ i, ‖partK (D.matrix x) (p.nodeW z.2) pp i j‖ ^ 2 ≤
      rhoP (p.nodeW z.2) ηH ηD pp ^ 2 :=
    fun pp j => partK_col_energy _ _ ηH ηD hcH hcD pp j
  have hsum : rhoP (p.nodeW z.2) ηH ηD false ^ 2 + rhoP (p.nodeW z.2) ηH ηD true ^ 2 ≤ ρ ^ 2 := by
    rw [hρ]
    exact rhoP_sq_sum_le _ ηH ηD p.R hηH hηD hk
  have hent : ∀ pp i j, ‖partK (D.matrix x) (p.nodeW z.2) pp i j‖ ≤ ρ := by
    intro pp i j
    have h1 := norm_le_of_energy_le (rhoP (p.nodeW z.2) ηH ηD pp)
      (partK (D.matrix x) (p.nodeW z.2) pp i) (rhoP_nonneg _ ηH ηD hηH hηD pp) (hr pp i) j
    rw [hρ]
    exact h1.trans (rhoP_le _ ηH ηD p.R hηH hηD hk pp)
  refine ⟨⟨elift4 en (res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T)),
    endpoint (γ * p.dur z.1 / p.T), ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h := one_sub_act4_res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T)
    rw [mul_def] at h
    rw [privFam, ← elift4_one (R := ℂ) en, ← elift4_sub, ← elift4_comp, h, elift4_one]
  · have h := res4_one_sub_act4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T)
    rw [mul_def] at h
    rw [privFam, ← elift4_one (R := ℂ) en, ← elift4_sub, ← elift4_comp, h, elift4_one]
  · exact (norm_elift4_le en _).trans ((norm_res4_le D x _ ρ _ hρpos hγz0 hent).trans
      (width_mono _ hγz1))
  · have hsc : ((γ * p.dur z.1 / p.T : ℝ) : ℂ) * ((ρ : ℂ) * (Real.sqrt (4 * (s : ℝ)) : ℂ))⁻¹ =
        ((p.dur z.1 / p.tau : ℝ) : ℂ) := by
      rw [hτ, div_div_eq_mul_div]
      push_cast
      ring
    have hq : qlift (R := ℂ) en (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (p.nodeW z.2))) =
        hLift D en x + ((p.nodeW z.2 : ℝ) : ℂ) • lLift D en x := by
      rw [ODEMatrixEnergy.lchsHamiltonian, ODEMatrixEnergy.matrixOperator_add,
        ODEMatrixEnergy.matrixOperator_smul, qlift_add, qlift_smul]
      rfl
    rw [boundary_lift4 D σ hσ en hs hrange, res4_compression, qlift_smul, qlift_add, qlift_one,
      qlift_smul, qlift_smul, hsc, hq]
    rfl
  · have hq := norm_res4_bdry4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T)
      (rhoP (p.nodeW z.2) ηH ηD) hρpos hγz0 hr hc hsum
    have hgram : (elift4 (R := ℂ) en (res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T)) ∘L
        (UJop (R := ℂ) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) ℂ)))† ∘L
        (elift4 (R := ℂ) en (res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T)) ∘L
          (UJop (R := ℂ) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) ℂ))) =
        qlift en ((res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T) ∘L bdry4 D)† ∘L
          (res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T) ∘L bdry4 D)) := by
      rw [adjoint_comp_comp, adjoint_comp_comp, ← elift4_adjoint, ← elift4_comp,
        boundary_lift4 D σ hσ en hs hrange]
    have h1 := norm_adjoint_comp_self
      (elift4 (R := ℂ) en (res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T)) ∘L
        (UJop (R := ℂ) (hadUJ4 k σ hσ) ∘L iota0 (a := k + 3) (P := Reg (Fin k) ℂ)))
    rw [hgram] at h1
    have h2 := norm_qlift_le (R := ℂ) en
      ((res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T) ∘L bdry4 D)† ∘L
        (res4 D x (p.nodeW z.2) ρ (γ * p.dur z.1 / p.T) ∘L bdry4 D))
    rw [norm_adjoint_comp_self, h1] at h2
    have he : 0 ≤ endpoint (γ * p.dur z.1 / p.T) := Real.sqrt_nonneg _
    exact (mul_self_le_mul_self_iff (norm_nonneg _) he).2
      (h2.trans (mul_le_mul hq hq (norm_nonneg _) he))
  · rw [endpoint_sq]
    exact div_le_div_of_nonneg_right (moment_mono hγz0 hγz1) (by norm_num)

end Clock

end

end SparseHamiltonian.GateBinaryODE
