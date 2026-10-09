import GateEfficientNative.Model.Flatten

/-!
# The edge Cayley rotation and its angle form

On an edge with represented value `z`, the private Cayley operation acts on
the orientation qubit by (equation `hs:eq:edge`)

  `D_edge(z) = ((|z|² - 1) I + 2 i [[0, z], [conj z, 0]]) / (1 + |z|²)`

(`edgeMat`).  With `θ = 2 arctan |z|` and `φ = arg z` it is
`angMat θ φ = [[-cos θ, i sin θ e^{iφ}], [i sin θ e^{-iφ}, -cos θ]]`
(`edgeMat_eq_angMat`), and `angMat θ φ = -R_z(-φ) R_x(2θ) R_z(φ)`
(`angMat_eq_rot`) with the rotations `R_z(α) = diag(e^{-iα/2}, e^{iα/2})` and
`R_x(α) = cos(α/2) I - i sin(α/2) X`, which add their angles (`rzMat_mul`,
`rxMat_mul`).  The error of approximate angles is controlled entrywise
(`frob2_angMat_sub_le`), and the Frobenius norm of a one-qubit matrix bounds
the operator norm of the corresponding controlled operation (`norm_condOp_sub_le`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit Complex
open scoped InnerProduct BigOperators ComplexConjugate

/-! ### The matrices -/

/-- The edge Cayley rotation of the represented value `z` (`hs:eq:edge`). -/
def edgeMat (z : ℂ) : Matrix Bool Bool ℂ := fun b c =>
  ((1 + (‖z‖ : ℂ) ^ 2)⁻¹) *
    (if b = c then (‖z‖ : ℂ) ^ 2 - 1 else if b then 2 * I * conj z else 2 * I * z)

/-- The angle form of the edge rotation. -/
def angMat (θ φ : ℝ) : Matrix Bool Bool ℂ := fun b c =>
  if b = c then -(Real.cos θ : ℂ)
  else if b then I * Real.sin θ * exp (-(φ * I)) else I * Real.sin θ * exp (φ * I)

/-- `R_z(α) = diag(e^{-iα/2}, e^{iα/2})`. -/
def rzMat (α : ℝ) : Matrix Bool Bool ℂ := fun b c =>
  if b = c then (if b then exp ((α / 2 : ℝ) * I) else exp (-((α / 2 : ℝ) * I))) else 0

/-- `R_x(α) = cos(α/2) I - i sin(α/2) X`. -/
def rxMat (α : ℝ) : Matrix Bool Bool ℂ := fun b c =>
  if b = c then (Real.cos (α / 2) : ℂ) else -(I * Real.sin (α / 2))

theorem real_cos_two_arctan (t : ℝ) :
    Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  have h1 : 0 < 1 + t ^ 2 := by positivity
  rw [Real.cos_two_mul, Real.cos_sq_arctan]
  field_simp
  ring

theorem real_sin_two_arctan (t : ℝ) :
    Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
  have h1 : 0 < 1 + t ^ 2 := by positivity
  have hs : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt h1.le
  have hs0 : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr h1
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  field_simp
  rw [hs]

/-- The edge rotation in angle form. -/
theorem edgeMat_eq_angMat (z : ℂ) :
    edgeMat z = angMat (2 * Real.arctan ‖z‖) (arg z) := by
  have h1 : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have h1c : (1 + (‖z‖ : ℂ) ^ 2) ≠ 0 := by exact_mod_cast h1.ne'
  have hz : (‖z‖ : ℂ) * exp (arg z * I) = z := norm_mul_exp_arg_mul_I z
  have hzc : (‖z‖ : ℂ) * exp (-(arg z * I)) = conj z := by
    have h := congrArg conj hz
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj] at h
    rw [← h]
    congr 2
    simp [Complex.conj_ofReal]
  have key : I * (((2 * ‖z‖ / (1 + ‖z‖ ^ 2) : ℝ)) : ℂ) * exp (arg z * I) =
      (1 + (‖z‖ : ℂ) ^ 2)⁻¹ * (2 * I * ((‖z‖ : ℂ) * exp (arg z * I))) := by
    push_cast
    field_simp
  have key' : I * (((2 * ‖z‖ / (1 + ‖z‖ ^ 2) : ℝ)) : ℂ) * exp (-(arg z * I)) =
      (1 + (‖z‖ : ℂ) ^ 2)⁻¹ * (2 * I * ((‖z‖ : ℂ) * exp (-(arg z * I)))) := by
    push_cast
    field_simp
  funext b c
  simp only [edgeMat, angMat]
  rw [real_cos_two_arctan, real_sin_two_arctan]
  by_cases hbc : b = c
  · rw [if_pos hbc, if_pos hbc]
    push_cast
    field_simp
    ring
  · rw [if_neg hbc, if_neg hbc]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      rw [key, hz]
    · simp only [if_true]
      rw [key', hzc]

/-! ### Rotation algebra -/

theorem rzMat_mul (α β : ℝ) : rzMat α * rzMat β = rzMat (α + β) := by
  funext b c
  simp only [Matrix.mul_apply, Fintype.sum_bool, rzMat]
  cases b <;> cases c <;>
    simp [← Complex.exp_add] <;> congr 1 <;> ring

theorem rzMat_zero : rzMat 0 = 1 := by
  funext b c
  cases b <;> cases c <;> simp [rzMat]

theorem rxMat_mul (α β : ℝ) : rxMat α * rxMat β = rxMat (α + β) := by
  funext b c
  simp only [Matrix.mul_apply, Fintype.sum_bool, rxMat]
  have hc : Real.cos ((α + β) / 2) = Real.cos (α / 2) * Real.cos (β / 2) -
      Real.sin (α / 2) * Real.sin (β / 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.cos_add]
  have hs : Real.sin ((α + β) / 2) = Real.sin (α / 2) * Real.cos (β / 2) +
      Real.cos (α / 2) * Real.sin (β / 2) := by
    rw [show (α + β) / 2 = α / 2 + β / 2 by ring, Real.sin_add]
  cases b <;> cases c <;> simp only [if_true, if_false, Bool.false_eq_true,
    reduceCtorEq, hc, hs] <;> push_cast <;> ring_nf <;> simp [Complex.I_sq, ← sub_eq_add_neg]

theorem rxMat_zero : rxMat 0 = 1 := by
  funext b c
  cases b <;> cases c <;> simp [rxMat]

/-- The angle form is `-R_z(-φ) R_x(2θ) R_z(φ)`. -/
theorem angMat_eq_rot (θ φ : ℝ) : angMat θ φ = -(rzMat (-φ) * rxMat (2 * θ) * rzMat φ) := by
  funext b c
  simp only [Matrix.neg_apply, Matrix.mul_apply, Fintype.sum_bool, rzMat, rxMat, angMat]
  have h2 : 2 * θ / 2 = θ := by ring
  rw [h2]
  cases b <;> cases c <;> simp only [if_true, if_false, Bool.false_eq_true, reduceCtorEq,
    mul_zero, zero_mul, add_zero, zero_add]
  · rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  · have e : exp (-(((-φ / 2 : ℝ) : ℂ) * I)) * exp (((φ / 2 : ℝ) : ℂ) * I) =
        exp ((φ : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (-(I * (Real.sin θ : ℂ))) * e
  · have e : exp (((-φ / 2 : ℝ) : ℂ) * I) * exp (-(((φ / 2 : ℝ) : ℂ) * I)) =
        exp (-((φ : ℂ) * I)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (-(I * (Real.sin θ : ℂ))) * e
  · rw [mul_comm, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp

/-! ### Unitarity -/

theorem unitaryMat_mul {u v : Matrix Bool Bool ℂ} (hu : UnitaryMat u) (hv : UnitaryMat v) :
    UnitaryMat (u * v) := by
  constructor
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc u.conjTranspose,
      hu.1, Matrix.one_mul, hv.1]
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc v, hv.2,
      Matrix.one_mul, hu.2]

theorem rzMat_conjTranspose (α : ℝ) : (rzMat α).conjTranspose = rzMat (-α) := by
  funext b c
  simp only [Matrix.conjTranspose_apply, rzMat]
  cases b <;> cases c <;> simp [← Complex.exp_conj, map_ofNat] <;> ring_nf

theorem rzMat_unitary (α : ℝ) : UnitaryMat (rzMat α) := by
  constructor
  · rw [rzMat_conjTranspose, rzMat_mul, neg_add_cancel, rzMat_zero]
  · rw [rzMat_conjTranspose, rzMat_mul, add_neg_cancel, rzMat_zero]

theorem rxMat_conjTranspose (α : ℝ) : (rxMat α).conjTranspose = rxMat (-α) := by
  funext b c
  simp only [Matrix.conjTranspose_apply, rxMat]
  have hc : Real.cos (-α / 2) = Real.cos (α / 2) := by
    rw [neg_div, Real.cos_neg]
  have hs : Real.sin (-α / 2) = -Real.sin (α / 2) := by
    rw [neg_div, Real.sin_neg]
  cases b <;> cases c <;>
    simp only [if_true, if_false, Bool.false_eq_true, reduceCtorEq, hc, hs, Complex.star_def,
      map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg] <;> ring

theorem rxMat_unitary (α : ℝ) : UnitaryMat (rxMat α) := by
  constructor
  · rw [rxMat_conjTranspose, rxMat_mul, neg_add_cancel, rxMat_zero]
  · rw [rxMat_conjTranspose, rxMat_mul, add_neg_cancel, rxMat_zero]

theorem neg_one_unitaryMat : UnitaryMat (-1 : Matrix Bool Bool ℂ) := by
  constructor <;> simp

/-! ### The Frobenius norm of a one-qubit matrix -/

/-- The Frobenius norm of a one-qubit matrix. -/
def frob2 (M : Matrix Bool Bool ℂ) : ℝ := Real.sqrt (∑ b, ∑ c, ‖M b c‖ ^ 2)

theorem frob2_nonneg (M : Matrix Bool Bool ℂ) : 0 ≤ frob2 M := Real.sqrt_nonneg _

theorem norm_exp_sub_exp_le (a b : ℝ) :
    ‖exp (a * I) - exp (b * I)‖ ≤ |a - b| := by
  have e : exp (a * I) - exp (b * I) = exp (b * I) * (exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b)
  rwa [Real.norm_eq_abs] at h

/-- Entrywise control of the angle form. -/
theorem frob2_angMat_sub_le (θ φ θ' φ' : ℝ) (eθ eφ : ℝ)
    (hθ : |θ - θ'| ≤ eθ) (hφ : |Real.sin θ'| * ‖exp (φ * I) - exp (φ' * I)‖ ≤ eφ) :
    frob2 (angMat θ φ - angMat θ' φ') ≤ 2 * (eθ + eφ) := by
  have heθ : 0 ≤ eθ := (abs_nonneg _).trans hθ
  have heφ : 0 ≤ eφ := (mul_nonneg (abs_nonneg _) (norm_nonneg _)).trans hφ
  have hcos : ‖-(Real.cos θ : ℂ) - -(Real.cos θ' : ℂ)‖ ≤ eθ := by
    rw [show -(Real.cos θ : ℂ) - -(Real.cos θ' : ℂ) = ((Real.cos θ' - Real.cos θ : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact (Real.abs_cos_sub_cos_le θ θ').trans hθ
  have hoff : ∀ s : ℝ, s = 1 ∨ s = -1 →
      ‖I * Real.sin θ * exp ((s * φ : ℝ) * I) - I * Real.sin θ' * exp ((s * φ' : ℝ) * I)‖ ≤
        eθ + eφ := by
    intro s hs
    have e : I * Real.sin θ * exp ((s * φ : ℝ) * I) - I * Real.sin θ' * exp ((s * φ' : ℝ) * I) =
        I * (((Real.sin θ - Real.sin θ' : ℝ) : ℂ) * exp ((s * φ : ℝ) * I) +
          (Real.sin θ' : ℂ) * (exp ((s * φ : ℝ) * I) - exp ((s * φ' : ℝ) * I))) := by
      push_cast; ring
    have hexp : ‖exp ((s * φ : ℝ) * I) - exp ((s * φ' : ℝ) * I)‖ =
        ‖exp (φ * I) - exp (φ' * I)‖ := by
      rcases hs with rfl | rfl
      · simp
      · have hc : exp (((-1) * φ : ℝ) * I) - exp (((-1) * φ' : ℝ) * I) =
            conj (exp (φ * I) - exp (φ' * I)) := by
          rw [map_sub, ← Complex.exp_conj, ← Complex.exp_conj]
          simp [Complex.conj_ofReal]
        rw [hc, Complex.norm_conj]
    rw [e, norm_mul, Complex.norm_I, one_mul]
    calc ‖((Real.sin θ - Real.sin θ' : ℝ) : ℂ) * exp ((s * φ : ℝ) * I) +
          (Real.sin θ' : ℂ) * (exp ((s * φ : ℝ) * I) - exp ((s * φ' : ℝ) * I))‖
        ≤ ‖((Real.sin θ - Real.sin θ' : ℝ) : ℂ) * exp ((s * φ : ℝ) * I)‖ +
          ‖(Real.sin θ' : ℂ) * (exp ((s * φ : ℝ) * I) - exp ((s * φ' : ℝ) * I))‖ :=
          norm_add_le _ _
      _ = |Real.sin θ - Real.sin θ'| + |Real.sin θ'| * ‖exp (φ * I) - exp (φ' * I)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hexp]
      _ ≤ eθ + eφ := add_le_add ((Real.abs_sin_sub_sin_le θ θ').trans hθ) hφ
  have hsq : ∑ b, ∑ c, ‖(angMat θ φ - angMat θ' φ') b c‖ ^ 2 ≤ (2 * (eθ + eφ)) ^ 2 := by
    simp only [Fintype.sum_bool, Matrix.sub_apply, angMat, if_true, if_false,
      Bool.false_eq_true, reduceCtorEq]
    have h1 := hoff 1 (Or.inl rfl)
    have h2 := hoff (-1) (Or.inr rfl)
    simp only [one_mul, neg_mul, one_mul, Complex.ofReal_neg] at h1 h2
    have hc2 : ‖-(Real.cos θ : ℂ) - -(Real.cos θ' : ℂ)‖ ^ 2 ≤ (eθ + eφ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hcos.trans (by linarith)) 2
    have h12 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h22 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [hc2, h12, h22]
  unfold frob2
  calc Real.sqrt (∑ b, ∑ c, ‖(angMat θ φ - angMat θ' φ') b c‖ ^ 2)
      ≤ Real.sqrt ((2 * (eθ + eφ)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * (eθ + eφ) := Real.sqrt_sq (by positivity)

/-! ### Operator norms of controlled one-qubit operations -/

section Norms

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
theorem matOp_sub (M N : Matrix (Cfg Unit) (Cfg Unit) ℂ) :
    matOp (Q := Q) (M - N) = matOp M - matOp N := by
  ext ψ b
  simp only [matOp_apply, sub_apply, PiLp.sub_apply, Matrix.sub_apply, sub_smul,
    Finset.sum_sub_distrib]

theorem qubitMat_sub (u v : Matrix Bool Bool ℂ) : qubitMat (u - v) = qubitMat u - qubitMat v := by
  funext b c; rfl

omit [CompleteSpace Q] in
/-- The Frobenius norm bounds a one-qubit operation with any payload. -/
theorem norm_matOp_qubitMat_le (M : Matrix Bool Bool ℂ) (ψ : Reg Unit Q) :
    ‖matOp (qubitMat M) ψ‖ ≤ frob2 M * ‖ψ‖ := by
  have hrow : ∀ c : Cfg Unit, ‖matOp (qubitMat M) ψ c‖ ^ 2 ≤
      (∑ c' : Cfg Unit, ‖qubitMat M c c'‖ ^ 2) * ‖ψ‖ ^ 2 := by
    intro c
    rw [matOp_apply]
    have h1 : ‖∑ c', qubitMat M c c' • ψ c'‖ ≤ ∑ c', ‖qubitMat M c c'‖ * ‖ψ c'‖ := by
      refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro c' _
      rw [norm_smul]
    have h2 : (∑ c', ‖qubitMat M c c'‖ * ‖ψ c'‖) ^ 2 ≤
        (∑ c', ‖qubitMat M c c'‖ ^ 2) * (∑ c', ‖ψ c'‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [PiLp.norm_sq_eq_of_L2 _ ψ]
    calc ‖∑ c', qubitMat M c c' • ψ c'‖ ^ 2 ≤ (∑ c', ‖qubitMat M c c'‖ * ‖ψ c'‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hsq : ‖matOp (qubitMat M) ψ‖ ^ 2 ≤ (frob2 M * ‖ψ‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 _ (matOp (qubitMat M) ψ), mul_pow, frob2,
      Real.sq_sqrt (by positivity)]
    calc ∑ c, ‖matOp (qubitMat M) ψ c‖ ^ 2
        ≤ ∑ c : Cfg Unit, (∑ c' : Cfg Unit, ‖qubitMat M c c'‖ ^ 2) * ‖ψ‖ ^ 2 :=
          Finset.sum_le_sum (fun c _ => hrow c)
      _ = (∑ b, ∑ c, ‖M b c‖ ^ 2) * ‖ψ‖ ^ 2 := by
          rw [← Finset.sum_mul]
          congr 1
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (frob2_nonneg _) (norm_nonneg _))).mp hsq

/-- Two controlled one-qubit operations on the same target differ by at most
the largest Frobenius norm of the difference of their matrices. -/
theorem norm_condOp_sub_le (t : W) (u v : Cfg W → Matrix Bool Bool ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ x, frob2 (u x - v x) ≤ δ) :
    ApproxOn (fun _ => True) (condOp (Q := Q) t u) (condOp t v) δ := by
  have hA := approxOn_localOp (Q := Q) (single_injective t)
    (fun x => matOp (qubitMat (u x))) (fun x => matOp (qubitMat (v x)))
    (SA := fun _ => True) (SW := fun _ => True) hδ (fun _ _ => trivial) (by
      intro x φ _
      rw [← sub_apply, ← matOp_sub, ← qubitMat_sub]
      exact (norm_matOp_qubitMat_le _ _).trans
        (mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)))
  exact hA

end Norms

end

end SparseHamiltonian.GateNative
