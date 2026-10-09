import GateEfficientSchedule.Cayley
import TimeDependentHamiltonian.Continuous.Propagator

/-!
# The manuscript's discretisation estimate `hs:eq:timedisc` with its constants

The manuscript bounds the distance between the ordered product of the Cayley steps on a uniform
mesh and the time-ordered propagator by
`∑_r [Λ³Δ_r³/12 + βΔ_r²/2 + δ_val Δ_r]` (equation `hs:eq:timedisc`), and the mesh condition
`hs:eq:timegrid` makes each of the three sums at most `ε/12`. The released estimates have the
constants `1` in place of `1/12` (`SlotSim.cayley_evolution_error`) and of `1/2`
(`TimeDependent.mesh_error`). This file proves the manuscript's constants:

* `duhamel_step_sharp`: on one interval, if `‖H(u) - H̃‖ ≤ β (u - a) + δ`, then
  `‖U(b) - exp(-i(b-a)H̃) U(a)‖ ≤ β (b-a)²/2 + δ (b-a)` (mean value inequality with a moving
  bound);
* `mesh_error_sharp`: on the uniform mesh `u_k = k t/M` with Lipschitz constant `β` and samples
  within `δ` of `H(u_k)`, `‖U(t) - ∏_k exp(-i(t/M)H̃_k)‖ ≤ β t²/(2M) + t δ`;
* `cayley_step_sharp`, `cayley_evolution_error_sharp`: a Cayley step of a self-adjoint `H` with
  `‖H‖ ≤ λ` is a contraction within `(wλ)³/12` of `exp(-iwH)`, so `n` steps err by at most
  `n (wλ)³/12`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section

open ContinuousLinearMap Set
open SparseHamiltonian.TimeDependent
open scoped BigOperators InnerProduct

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Cayley steps -/

/-- **One sharp Cayley step**: for self-adjoint `H` with `‖H‖ ≤ λ`, `w ≥ 0` and a right inverse
`R` of the denominator, the Cayley step is a contraction within `(wλ)³/12` of `exp(-iwH)`. -/
theorem cayley_step_sharp (H R : P →L[ℂ] P) (w lam : ℝ) (hw : 0 ≤ w)
    (hSelf : star H = H) (hH : ‖H‖ ≤ lam)
    (hR : CayleyTransfer.cayleyDenominator w H * R = 1) :
    ‖CayleyTransfer.cayleyNumerator w H * R - NormedSpace.exp ((-Complex.I * (w : ℂ)) • H)‖ ≤
      (w * lam) ^ 3 / 12 ∧ ‖CayleyTransfer.cayleyNumerator w H * R‖ ≤ 1 := by
  let X : P →L[ℂ] P := (-Complex.I * (w : ℂ)) • H
  have hXw : ‖X‖ ≤ w * lam := by
    simp only [X, norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_left hH hw
  have hSkew : star X = -X := by
    simp only [X, star_smul, hSelf, star_mul, star_neg, Complex.star_def,
      Complex.conj_I, Complex.conj_ofReal]
    module
  have hDen : 1 - (1 / 2 : ℂ) • X = CayleyTransfer.cayleyDenominator w H := by
    simp only [X, CayleyTransfer.cayleyDenominator, smul_smul]
    module
  have hNum : 1 + (1 / 2 : ℂ) • X = CayleyTransfer.cayleyNumerator w H := by
    simp only [X, CayleyTransfer.cayleyNumerator, smul_smul]
    module
  have hR' : (1 - (1 / 2 : ℂ) • X) * R = 1 := by rw [hDen]; exact hR
  have h := cayley_exp_error_sharp X R hSkew hR'
  have hc := CayleyTransfer.skew_cayley_norm_le_one X R hSkew hR'
  rw [hNum] at h hc
  refine ⟨h.trans ?_, hc⟩
  have h3 := pow_le_pow_left₀ (norm_nonneg X) hXw 3
  linarith

/-- The exponential of `-i w H` for a self-adjoint `H` is a contraction. -/
theorem exp_selfAdjoint_norm_le (H : P →L[ℂ] P) (hH : star H = H) (w : ℝ) :
    ‖NormedSpace.exp ((-Complex.I * (w : ℂ)) • H)‖ ≤ 1 := by
  apply CayleyApproximation.skew_exp_norm_le
  simp only [star_smul, hH, star_mul, star_neg, Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal]
  module

/-- **The sharp Cayley error of an ordered product**: `n` Cayley steps of self-adjoint
generators with `‖H k‖ ≤ λ` are within `n (wλ)³/12` of the ordered product of the exponentials. -/
theorem cayley_evolution_error_sharp (H R U : ℕ → P →L[ℂ] P) (w lam : ℝ) (hw : 0 ≤ w)
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ lam)
    (hRR : ∀ k, CayleyTransfer.cayleyDenominator w (H k) ∘L R k = 1)
    (hCay : ∀ k, U k = CayleyTransfer.cayleyNumerator w (H k) ∘L R k) (n : ℕ) :
    ‖evolution U n - evolution (fun k => NormedSpace.exp ((-Complex.I * (w : ℂ)) • H k)) n‖ ≤
      n * ((w * lam) ^ 3 / 12) := by
  have hstep := fun k => cayley_step_sharp (H k) (R k) w lam hw (hSelf k) (hH k)
    (by rw [mul_def]; exact hRR k)
  apply evolution_sub_norm_le_mul
  · intro k
    rw [hCay k, ← mul_def]
    exact (hstep k).2
  · exact fun k => exp_selfAdjoint_norm_le (H k) (hSelf k) w
  · intro k
    rw [hCay k, ← mul_def]
    exact (hstep k).1

/-! ### The Duhamel estimate with the moving bound -/

/-- The derivative of the moving bound `u ↦ β (u - a)²/2 + δ (u - a)`. -/
theorem hasDerivAt_duhamel_bound (a β δ u : ℝ) :
    HasDerivAt (fun x : ℝ => β * (x - a) ^ 2 / 2 + δ * (x - a)) (β * (u - a) + δ) u := by
  have hlin : HasDerivAt (fun x : ℝ => x - a) 1 u := (hasDerivAt_id' u).sub_const a
  have h1 := ((hlin.fun_pow 2).const_mul β).div_const 2
  have h2 := hlin.const_mul δ
  refine (h1.add h2).congr_deriv ?_
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  push_cast
  ring

/-- **One interval of the unitary Duhamel formula with the manuscript's constant**: if
`‖H(u) - H̃‖ ≤ β (u - a) + δ` on `[a, b]`, then `‖U(b) - exp(-i(b-a)H̃) U(a)‖ ≤
β (b-a)²/2 + δ (b-a)`. -/
theorem duhamel_step_sharp {H U : ℝ → P →L[ℂ] P} (Hs : P →L[ℂ] P) {a b β δ : ℝ} (hab : a ≤ b)
    (hU : SolvesOn H U a b) (hUnorm : ∀ u ∈ Icc a b, ‖U u‖ ≤ 1)
    (hHs : star Hs = Hs) (hC : ∀ u ∈ Icc a b, ‖H u - Hs‖ ≤ β * (u - a) + δ) :
    ‖U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a‖ ≤
      β * (b - a) ^ 2 / 2 + δ * (b - a) := by
  let X : P →L[ℂ] P := Complex.I • Hs
  have hXskew : star X = -X := by
    simp only [X, star_smul, hHs, Complex.star_def, Complex.conj_I, neg_smul]
  let E : ℝ → P →L[ℂ] P := fun u => NormedSpace.exp ((u - a) • X)
  have hEnorm : ∀ u, ‖E u‖ ≤ 1 := fun u =>
    CayleyApproximation.skew_exp_norm_le _ (real_smul_skew X hXskew (u - a))
  have hE : ∀ u, HasDerivAt E (E u * X) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => v - a) 1 u := (hasDerivAt_id' u).sub_const a
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X (u - a)).scomp u hlin
    simpa only [one_smul, Function.comp_def] using h
  have hf : ∀ u ∈ Icc a b, HasDerivWithinAt (fun s => E s * U s - U a)
      (E u * X * U u + E u * ((-Complex.I) • (H u * U u))) (Icc a b) u := by
    intro u hu
    exact (((hE u).hasDerivWithinAt).mul (hU u hu)).sub_const (U a)
  have hbound : ∀ u ∈ Ico a b,
      ‖E u * X * U u + E u * ((-Complex.I) • (H u * U u))‖ ≤ β * (u - a) + δ := by
    intro u hu
    have huIcc : u ∈ Icc a b := Ico_subset_Icc_self hu
    have hrw : E u * X * U u + E u * ((-Complex.I) • (H u * U u)) =
        E u * (Complex.I • ((Hs - H u) * U u)) := by
      simp only [X, mul_smul_comm, smul_mul_assoc, sub_mul, smul_sub, mul_sub, mul_assoc]
      rw [sub_eq_add_neg]
      simp only [neg_smul]
    rw [hrw]
    have hCu : ‖Hs - H u‖ ≤ β * (u - a) + δ := by
      rw [norm_sub_rev]
      exact hC u huIcc
    have hC0 : 0 ≤ β * (u - a) + δ := (norm_nonneg _).trans hCu
    calc
      ‖E u * (Complex.I • ((Hs - H u) * U u))‖ ≤ ‖E u‖ * (‖Hs - H u‖ * ‖U u‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [norm_smul, Complex.norm_I, one_mul]
        exact norm_mul_le _ _
      _ ≤ 1 * ((β * (u - a) + δ) * 1) :=
        mul_le_mul (hEnorm u) (mul_le_mul hCu (hUnorm u huIcc) (norm_nonneg _) hC0)
          (by positivity) zero_le_one
      _ = β * (u - a) + δ := by ring
  have hEa : E a = 1 := by simp [E]
  have hmvt := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun s => E s * U s - U a)
    (f' := fun u => E u * X * U u + E u * ((-Complex.I) • (H u * U u)))
    (B := fun x : ℝ => β * (x - a) ^ 2 / 2 + δ * (x - a)) (B' := fun x : ℝ => β * (x - a) + δ)
    (fun u hu => (hf u hu).continuousWithinAt)
    (fun u hu => (hf u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hu))
    (by simp [hEa]) (fun u => hasDerivAt_duhamel_bound a β δ u) hbound
    (⟨hab, le_rfl⟩ : b ∈ Icc a b)
  -- Undo the frozen evolution.
  let Y : P →L[ℂ] P := (b - a) • X
  have hinv : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) (Commute.neg_left (Commute.refl Y))
      ((NormedSpace.expSeries_radius_eq_top ℂ (P →L[ℂ] P)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℂ (P →L[ℂ] P)).symm ▸ edist_lt_top _ _),
      neg_add_cancel, NormedSpace.exp_zero]
  have hY : -Y = (-Complex.I * ((b - a : ℝ) : ℂ)) • Hs := by
    simp only [Y, X, ← Complex.coe_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  have hfactor : U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a =
      NormedSpace.exp (-Y) * (E b * U b - U a) := by
    rw [mul_sub, ← mul_assoc, show E b = NormedSpace.exp Y from rfl, hinv, one_mul, hY]
  rw [hfactor]
  calc
    ‖NormedSpace.exp (-Y) * (E b * U b - U a)‖ ≤ ‖NormedSpace.exp (-Y)‖ * ‖E b * U b - U a‖ :=
      norm_mul_le _ _
    _ ≤ 1 * (β * (b - a) ^ 2 / 2 + δ * (b - a)) := by
      apply mul_le_mul _ hmvt (norm_nonneg _) zero_le_one
      have hskew : star (-Y) = -(-Y) := by
        rw [star_neg, real_smul_skew X hXskew (b - a)]
      exact CayleyApproximation.skew_exp_norm_le _ hskew
    _ = β * (b - a) ^ 2 / 2 + δ * (b - a) := one_mul _

/-- **The uniform-mesh discretisation estimate with the manuscript's constant** (equation
`hs:eq:timedisc` without the Cayley term): freezing at the left endpoints together with the
sample representation error gives `‖U(t) - ∏_k exp(-i(t/M)H̃_k)‖ ≤ β t²/(2M) + t δ`. -/
theorem mesh_error_sharp {H U : ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P) {t β δ : ℝ} {M : ℕ}
    (hM : 0 < M) (ht : 0 ≤ t)
    (hU0 : U 0 = 1) (hU : SolvesOn H U 0 t)
    (hH : ∀ u ∈ Icc 0 t, star (H u) = H u) (hHs : ∀ k, star (Hs k) = Hs k)
    (hLip : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, ‖H u - H v‖ ≤ β * |u - v|)
    (hVal : ∀ k < M, ‖H (k * t / M) - Hs k‖ ≤ δ) :
    ‖U t - evolution (fun k => NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k)) M‖ ≤
      β * t ^ 2 / (2 * M) + t * δ := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  let Δ : ℝ := t / M
  have hΔ : 0 ≤ Δ := div_nonneg ht hMR.le
  let u : ℕ → ℝ := fun k => k * t / M
  have hu : ∀ k, u k = k * Δ := fun k => by simp only [u, Δ]; ring
  have huM : u M = t := by simp only [u]; field_simp
  have hUnorm := hU.norm_le_one hH hU0
  have hEnorm : ∀ k, ‖NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k)‖ ≤ 1 :=
    fun k => exp_selfAdjoint_norm_le (Hs k) (hHs k) (t / M)
  have hstep : ∀ k < M, ‖U (u (k + 1)) -
      NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k) * U (u k)‖ ≤
        β * Δ ^ 2 / 2 + δ * Δ := by
    intro k hk
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hk
    have hlo : 0 ≤ u k := by rw [hu]; positivity
    have hhi : u (k + 1) ≤ t := by
      rw [hu]
      calc
        ((k + 1 : ℕ) : ℝ) * Δ ≤ M * Δ := mul_le_mul_of_nonneg_right hk1 hΔ
        _ = t := by simp only [Δ]; field_simp
    have hlen : u (k + 1) - u k = Δ := by
      rw [hu, hu]
      push_cast
      ring
    have hsub : Icc (u k) (u (k + 1)) ⊆ Icc 0 t :=
      Icc_subset_Icc hlo hhi
    have hC : ∀ v ∈ Icc (u k) (u (k + 1)), ‖H v - Hs k‖ ≤ β * (v - u k) + δ := by
      intro v hv
      have hvI := hsub hv
      have hkI : u k ∈ Icc 0 t := hsub ⟨le_rfl, by linarith [hv.1, hv.2]⟩
      calc
        ‖H v - Hs k‖ ≤ ‖H v - H (u k)‖ + ‖H (u k) - Hs k‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ β * |v - u k| + δ := add_le_add (hLip v hvI (u k) hkI) (hVal k hk)
        _ = β * (v - u k) + δ := by rw [abs_of_nonneg (by linarith [hv.1])]
    have h := duhamel_step_sharp (Hs k) (by linarith) (hU.mono hlo hhi)
      (fun v hv => hUnorm v (hsub hv)) (hHs k) hC
    rw [hlen] at h
    exact h
  have htel := propagator_telescope U _ hEnorm u (by simp [u, hU0]) M
  rw [huM] at htel
  calc
    _ ≤ ∑ k ∈ Finset.range M, ‖U (u (k + 1)) -
        NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k) * U (u k)‖ := htel
    _ ≤ ∑ _k ∈ Finset.range M, (β * Δ ^ 2 / 2 + δ * Δ) :=
      Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
    _ = β * t ^ 2 / (2 * M) + t * δ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Δ]
      field_simp

end

end SparseHamiltonian.GateSchedule
