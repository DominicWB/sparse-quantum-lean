import SparseLowerBounds.Helpers.Ode.JointFamily.Eigen

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The explicit solution of the joint family

Helper of `ODE/JointInstance` (manuscript lines 3826-3850, 3883-3884, eqs. `odel:eq:stages`,
`odel:eq:beforeforce`, `odel:eq:force`, `odel:eq:cancel`). With the clamped ramps
`clamp(t - c, 0, L)`, the phase `Φ_a` of `jointSol` is affine with slope
`(-1)^{j_{ak}}` on the hidden stage `[kπ/2, (k+1)π/2]` and constant after `nπ/2`,
and the source weight `clamp(t - (T-1), 0, 1)` vanishes before `T - 1` and has
slope `1` on `[T - 1, T]`. Since `|a, ω⟩` is an eigenvector of `H_k`, the path
solves the release's `SolvesODE` on each stage (`solvesODE_hidden`,
`solvesODE_idle`, `solvesODE_source`), starts at `x₀` (`jointSol_zero`), and
ends at `x(T) = -2(-i)^n M^{-1/2} |a_*, ω⟩` (`jointSol_end`): the factor
`e^{-iπσ/2} = -iσ` of each hidden stage multiplies to `(-i)^n σ_a`, and the
source cancels every even candidate.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian Set
open scoped InnerProductSpace

/-! ### Clamped ramps -/

section Ramp

variable {c L p q u : ℝ}

theorem hasDerivWithinAt_ramp_below (hL : 0 ≤ L) (h : q ≤ c) (hu : u ∈ Icc p q) :
    HasDerivWithinAt (fun t => min (max (t - c) 0) L) 0 (Icc p q) u :=
  (hasDerivWithinAt_const u _ (0 : ℝ)).congr_of_mem (fun t ht => by
    rw [max_eq_right (by linarith [ht.2]), min_eq_left hL]) hu

theorem hasDerivWithinAt_ramp_above (hL : 0 ≤ L) (h : c + L ≤ p) (hu : u ∈ Icc p q) :
    HasDerivWithinAt (fun t => min (max (t - c) 0) L) 0 (Icc p q) u :=
  (hasDerivWithinAt_const u _ L).congr_of_mem (fun t ht => by
    rw [max_eq_left (by linarith [ht.1]), min_eq_right (by linarith [ht.1])]) hu

theorem hasDerivWithinAt_ramp_mid (h1 : c ≤ p) (h2 : q ≤ c + L) (hu : u ∈ Icc p q) :
    HasDerivWithinAt (fun t => min (max (t - c) 0) L) 1 (Icc p q) u :=
  ((hasDerivAt_id u).sub_const c).hasDerivWithinAt.congr_of_mem (fun t ht => by
    rw [max_eq_left (by linarith [ht.1]), min_eq_left (by linarith [ht.2])]; rfl) hu

end Ramp

/-! ### Phase paths -/

section Path

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Derivative of `t ↦ Σ_i c_i e^{-iΦ_i(t)} v_i + κ(t) b` from those of `Φ_i` and `κ`. -/
theorem hasDerivWithinAt_phasePath {ι : Type*} [Fintype ι] (c : ι → ℂ) (Φ : ι → ℝ → ℝ)
    (σ : ι → ℝ) (v : ι → V) (κ : ℝ → ℝ) (γ : ℝ) (b : V) {S : Set ℝ} {u : ℝ}
    (hΦ : ∀ i, HasDerivWithinAt (Φ i) (σ i) S u) (hκ : HasDerivWithinAt κ γ S u) :
    HasDerivWithinAt
      (fun t => ∑ i, (c i * Complex.exp (-Complex.I * (Φ i t : ℂ))) • v i + (κ t : ℂ) • b)
      (∑ i, (c i * (Complex.exp (-Complex.I * (Φ i u : ℂ)) * (-Complex.I * (σ i : ℂ)))) • v i +
        (γ : ℂ) • b) S u := by
  refine HasDerivWithinAt.add (HasDerivWithinAt.fun_sum fun i _ => ?_) (hκ.ofReal_comp.smul_const b)
  exact ((((hΦ i).ofReal_comp.const_mul (-Complex.I)).cexp).const_mul (c i)).smul_const (v i)

end Path

variable {M n μ s : ℕ}

/-! ### The candidate phases -/

/-- On the hidden stage `k`, `Φ_a` has slope `(-1)^{j_{ak}}`. -/
theorem hasDerivWithinAt_candPhase_stage (j : Positions M n (2 ^ μ)) (a : Fin M) (k : Fin n)
    {u : ℝ} (hu : u ∈ Icc (((k : ℕ) : ℝ) * (Real.pi / 2)) ((((k : ℕ) : ℝ) + 1) * (Real.pi / 2))) :
    HasDerivWithinAt (candPhase j a) ((-1 : ℝ) ^ (j a k : ℕ))
      (Icc (((k : ℕ) : ℝ) * (Real.pi / 2)) ((((k : ℕ) : ℝ) + 1) * (Real.pi / 2))) u := by
  have hπ := Real.pi_pos
  have h : ∀ k' ∈ (Finset.univ : Finset (Fin n)), HasDerivWithinAt
      (fun t => (-1 : ℝ) ^ (j a k' : ℕ) * min (max (t - k' * (Real.pi / 2)) 0) (Real.pi / 2))
      ((-1 : ℝ) ^ (j a k' : ℕ) * if k' = k then 1 else 0)
      (Icc (((k : ℕ) : ℝ) * (Real.pi / 2)) ((((k : ℕ) : ℝ) + 1) * (Real.pi / 2))) u := by
    intro k' _
    refine HasDerivWithinAt.const_mul _ ?_
    rcases lt_trichotomy (k' : ℕ) k with hlt | heq | hgt
    · rw [if_neg (by rintro rfl; omega)]
      have : ((k' : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast hlt
      exact hasDerivWithinAt_ramp_above (by positivity) (by nlinarith) hu
    · obtain rfl : k' = k := Fin.ext heq
      rw [if_pos rfl]
      exact hasDerivWithinAt_ramp_mid le_rfl (by linarith) hu
    · rw [if_neg (by rintro rfl; omega)]
      have : ((k : ℕ) : ℝ) + 1 ≤ (k' : ℕ) := by exact_mod_cast hgt
      exact hasDerivWithinAt_ramp_below (by positivity) (by nlinarith) hu
  have hs := HasDerivWithinAt.fun_sum h
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  exact hs

/-- After the hidden stages, `Φ_a` is constant. -/
theorem hasDerivWithinAt_candPhase_after (j : Positions M n (2 ^ μ)) (a : Fin M) {p q u : ℝ}
    (hp : (n : ℝ) * (Real.pi / 2) ≤ p) (hu : u ∈ Icc p q) :
    HasDerivWithinAt (candPhase j a) 0 (Icc p q) u := by
  have h : ∀ k ∈ (Finset.univ : Finset (Fin n)), HasDerivWithinAt
      (fun t => (-1 : ℝ) ^ (j a k : ℕ) * min (max (t - k * (Real.pi / 2)) 0) (Real.pi / 2))
      ((-1 : ℝ) ^ (j a k : ℕ) * 0) (Icc p q) u := by
    intro k _
    have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.2
    exact (hasDerivWithinAt_ramp_above (by positivity) (by nlinarith [Real.pi_pos]) hu).const_mul _
  have hs := HasDerivWithinAt.fun_sum h
  simp only [mul_zero, Finset.sum_const_zero] at hs
  exact hs

theorem candPhase_zero (j : Positions M n (2 ^ μ)) (a : Fin M) : candPhase j a 0 = 0 := by
  unfold candPhase
  refine Finset.sum_eq_zero fun k _ => ?_
  have : (0 : ℝ) ≤ ((k : ℕ) : ℝ) * (Real.pi / 2) := by positivity
  rw [max_eq_right (by linarith), min_eq_left (by positivity), mul_zero]

/-- After the hidden stages, `Φ_a = (π/2) Σ_k (-1)^{j_{ak}}`. -/
theorem candPhase_of_ge (j : Positions M n (2 ^ μ)) (a : Fin M) {t : ℝ}
    (ht : (n : ℝ) * (Real.pi / 2) ≤ t) :
    candPhase j a t = ∑ k : Fin n, (-1 : ℝ) ^ (j a k : ℕ) * (Real.pi / 2) := by
  unfold candPhase
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast k.2
  have hπ := Real.pi_pos
  rw [max_eq_left (by nlinarith), min_eq_right (by nlinarith)]

/-- One hidden stage multiplies by `e^{-iπσ/2} = -iσ`, `σ = (-1)^m`. -/
theorem exp_neg_I_mul_sign (m : ℕ) :
    Complex.exp (-Complex.I * ((((-1 : ℝ) ^ m * (Real.pi / 2) : ℝ)) : ℂ)) =
      -Complex.I * (-1 : ℂ) ^ m := by
  rcases Nat.even_or_odd m with he | ho
  · simp only [he.neg_one_pow, one_mul, mul_one]
    have : -Complex.I * ((Real.pi / 2 : ℝ) : ℂ) = ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  · simp only [ho.neg_one_pow]
    have : -Complex.I * ((-1 * (Real.pi / 2) : ℝ) : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring

/-- The hidden stages multiply `|a, ω⟩` by `(-i)^n σ_a` (eq. `odel:eq:beforeforce`). -/
theorem exp_candPhase_final (j : Positions M n (2 ^ μ)) (a : Fin M) :
    Complex.exp (-Complex.I * ((∑ k : Fin n, (-1 : ℝ) ^ (j a k : ℕ) * (Real.pi / 2) : ℝ) : ℂ)) =
      (-Complex.I) ^ n * (parity (j a) : ℂ) := by
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum, parity_eq_prod]
  simp only [exp_neg_I_mul_sign]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  rfl

/-! ### The solution -/

theorem one_le_of_time {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) : 1 ≤ T := by
  have : (0 : ℝ) ≤ (n : ℝ) * (Real.pi / 2) := by positivity
  linarith

/-- `x(0) = x₀`. -/
theorem jointSol_zero {T : ℝ} (hT : 1 ≤ T) (x : Promised M n (2 ^ μ)) :
    jointSol M n μ s T x 0 = jointInit M μ s := by
  unfold jointSol jointInit
  simp only [candPhase_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
  rw [max_eq_right (by linarith), min_eq_left zero_le_one, Complex.ofReal_zero, zero_smul,
    add_zero, Finset.smul_sum]

/-- **Eq. `odel:eq:cancel`**: `x(T) = -2(-i)^n M^{-1/2} |a_*, ω⟩`. -/
theorem jointSol_end {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) (x : Promised M n (2 ^ μ)) :
    jointSol M n μ s T x T =
      ((-2 : ℂ) * (-Complex.I) ^ n / (Real.sqrt M : ℂ)) • candState M μ s (oddCand x) := by
  have hge : (n : ℝ) * (Real.pi / 2) ≤ T := by linarith
  unfold jointSol jointSrc jointInit
  simp only [candPhase_of_ge _ _ hge, exp_candPhase_final]
  rw [show T - (T - 1) = 1 by ring, max_eq_left zero_le_one, min_self, Complex.ofReal_one,
    one_smul, smul_smul, Finset.smul_sum, ← Finset.sum_add_distrib,
    Finset.sum_eq_single (oddCand x)]
  · rw [← add_smul, parity_oddCand]
    congr 1
    push_cast
    ring
  · intro a _ ha
    rw [← add_smul, parity_eq_one_of_ne x ha]
    convert zero_smul ℂ (candState M μ s a) using 2
    push_cast
    ring
  · simp

/-- **Hidden stage `k < n`** (eq. `odel:eq:stages`): on `[kπ/2, (k+1)π/2]` the
path solves `ẋ = -i H_k x`. -/
theorem solvesODE_hidden (hμ : 1 ≤ μ) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T)
    (x : Promised M n (2 ^ μ)) (k : Fin (n + 2)) (hk : (k : ℕ) < n) :
    TimeDependentODE.SolvesODE
      (fun _ => SparseStateOverlap.matrixOperator (jointGen (s := s) x.1 k))
      (fun _ => if (k : ℕ) = n + 1 then jointSrc M n μ s else 0) (jointSol M n μ s T x)
      (((k : ℕ) : ℝ) * (Real.pi / 2)) ((((k : ℕ) : ℝ) + 1) * (Real.pi / 2)) := by
  have hkn : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hπ := Real.pi_pos
  have hgen : jointGen (s := s) x.1 k = Complex.I • stageHam x.1 ⟨k, hk⟩ := dif_pos hk
  rw [hgen, if_neg (by omega)]
  intro u hu
  have hq : (((k : ℕ) : ℝ) + 1) * (Real.pi / 2) ≤ T - 1 := by nlinarith
  have hd := hasDerivWithinAt_phasePath (fun _ : Fin M => ((Real.sqrt M : ℂ))⁻¹)
    (fun a => candPhase x.1 a) (fun a => (-1 : ℝ) ^ (x.1 a ⟨k, hk⟩ : ℕ)) (candState M μ s)
    (fun t => min (max (t - (T - 1)) 0) 1) 0 (jointSrc M n μ s)
    (fun a => hasDerivWithinAt_candPhase_stage x.1 a ⟨k, hk⟩ hu)
    (hasDerivWithinAt_ramp_below zero_le_one hq hu)
  refine hd.congr_deriv ?_
  have hκ : min (max (u - (T - 1)) 0) 1 = 0 := by
    rw [max_eq_right (by linarith [hu.2]), min_eq_left zero_le_one]
  simp only [jointSol, hκ, Complex.ofReal_zero, zero_smul, add_zero, matrixOperator_I_smul,
    FunLike.coe_smul, Pi.smul_apply, map_sum, map_smul,
    matrixOperator_stageHam_candState hμ, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul, ← neg_smul]
  congr 1
  push_cast
  ring

/-- **Idle stage** (lines 3883-3884): on `[nπ/2, T - 1]` the path is constant. -/
theorem solvesODE_idle {T : ℝ} (x : Promised M n (2 ^ μ)) (k : Fin (n + 2)) (hk : (k : ℕ) = n) :
    TimeDependentODE.SolvesODE
      (fun _ => SparseStateOverlap.matrixOperator (jointGen (s := s) x.1 k))
      (fun _ => if (k : ℕ) = n + 1 then jointSrc M n μ s else 0) (jointSol M n μ s T x)
      ((n : ℝ) * (Real.pi / 2)) (T - 1) := by
  have hgen : jointGen (s := s) x.1 k = 0 := dif_neg (by omega)
  rw [hgen, if_neg (by omega), Hamiltonian.matrixOperator_eq_toEuclideanCLM, map_zero]
  intro u hu
  have hd := hasDerivWithinAt_phasePath (fun _ : Fin M => ((Real.sqrt M : ℂ))⁻¹)
    (fun a => candPhase x.1 a) (fun _ => 0) (candState M μ s)
    (fun t => min (max (t - (T - 1)) 0) 1) 0 (jointSrc M n μ s)
    (fun a => hasDerivWithinAt_candPhase_after x.1 a le_rfl hu)
    (hasDerivWithinAt_ramp_below zero_le_one le_rfl hu)
  refine hd.congr_deriv ?_
  simp

/-- **Source stage** (eq. `odel:eq:force`): on `[T - 1, T]`, `ẋ = b`. -/
theorem solvesODE_source {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T)
    (x : Promised M n (2 ^ μ)) (k : Fin (n + 2)) (hk : (k : ℕ) = n + 1) :
    TimeDependentODE.SolvesODE
      (fun _ => SparseStateOverlap.matrixOperator (jointGen (s := s) x.1 k))
      (fun _ => if (k : ℕ) = n + 1 then jointSrc M n μ s else 0) (jointSol M n μ s T x)
      (T - 1) T := by
  have hgen : jointGen (s := s) x.1 k = 0 := dif_neg (by omega)
  rw [hgen, if_pos hk, Hamiltonian.matrixOperator_eq_toEuclideanCLM, map_zero]
  intro u hu
  have hd := hasDerivWithinAt_phasePath (fun _ : Fin M => ((Real.sqrt M : ℂ))⁻¹)
    (fun a => candPhase x.1 a) (fun _ => 0) (candState M μ s)
    (fun t => min (max (t - (T - 1)) 0) 1) 1 (jointSrc M n μ s)
    (fun a => hasDerivWithinAt_candPhase_after x.1 a (by linarith) hu)
    (hasDerivWithinAt_ramp_mid le_rfl (by linarith) hu)
  refine hd.congr_deriv ?_
  simp

end

end SparseLowerBounds.ODE
end
