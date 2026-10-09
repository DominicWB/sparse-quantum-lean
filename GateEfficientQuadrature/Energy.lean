import TimeDependentODE.Continuous.Solution

/-!
# The energy bound with an affine forcing bound

For a solution of `x' = -G(u) x + F(u)` within `[a, c]` with accretive `G(u)` the dissipative part
cannot increase the norm, so `‖x(c)‖ ≤ ‖x(a)‖ + ∫_a^c ‖F‖`. The released
`TimeDependentODE.SolvesODE.norm_le` states this on `[0, T]` for a constant bound of `‖F‖`;
the left-endpoint quadrature needs it on every interval for the affine bound
`‖F(u)‖ ≤ A (c - u) + L (u - a) + δ`, whose integral is `(A + L)(c - a)² / 2 + δ (c - a)`
(`energy_affine`). With `F = 0` it gives the contractivity of the homogeneous equation
(`homog_norm_le`, `homog_eq_zero`).

The module also records the algebra of solutions used below: adding a differentiable path
(`solves_add_path`), subtracting, adding and summing solutions of the homogeneous equation
(`solves_sub_homog`, `homog_add`, `homog_sum`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateQuad

noncomputable section
open Set
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The antiderivative `∫_a^u (A (c - t) + L (t - a) + δ) dt` of the affine bound. -/
def affInt (A L δ a c u : ℝ) : ℝ :=
  A * ((c - a) ^ 2 - (c - u) ^ 2) / 2 + L * (u - a) ^ 2 / 2 + δ * (u - a)

theorem affInt_hasDerivAt (A L δ a c u : ℝ) :
    HasDerivAt (affInt A L δ a c) (A * (c - u) + L * (u - a) + δ) u := by
  have hc : HasDerivAt (fun t : ℝ => c - t) (-1) u := (hasDerivAt_id u).const_sub c
  have ha : HasDerivAt (fun t : ℝ => t - a) 1 u := (hasDerivAt_id u).sub_const a
  have h := ((((hc.pow 2).const_sub ((c - a) ^ 2)).const_mul A).div_const 2).add
    (((ha.pow 2).const_mul L).div_const 2) |>.add (ha.const_mul δ)
  unfold affInt
  exact h.congr_deriv (by norm_num; ring)

theorem affInt_left (A L δ a c : ℝ) : affInt A L δ a c a = 0 := by
  unfold affInt
  ring

theorem affInt_right (A L δ a c : ℝ) :
    affInt A L δ a c c = (A + L) * (c - a) ^ 2 / 2 + δ * (c - a) := by
  unfold affInt
  ring

theorem affInt_nonneg {A L δ a c u : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hu : u ∈ Icc a c) : 0 ≤ affInt A L δ a c u := by
  unfold affInt
  have h1 : 0 ≤ (c - a) ^ 2 - (c - u) ^ 2 := by nlinarith [hu.1, hu.2]
  have h2 : 0 ≤ u - a := by linarith [hu.1]
  positivity

/-- **Energy bound with an affine forcing bound.** For a solution of `x' = -G(u) x + F(u)`
within `[a, c]` with accretive `G(u)` and `‖F(u)‖ ≤ A (c - u) + L (u - a) + δ`,
`‖x(c)‖ ≤ ‖x(a)‖ + (A + L)(c - a)² / 2 + δ (c - a)`. -/
theorem energy_affine {G : ℝ → V →L[ℂ] V} {F x : ℝ → V} {a c : ℝ} (hac : a ≤ c)
    (hx : SolvesODE G F x a c) (hG : ∀ u ∈ Icc a c, Accretive (G u)) {A L δ : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hδ : 0 ≤ δ)
    (hF : ∀ u ∈ Icc a c, ‖F u‖ ≤ A * (c - u) + L * (u - a) + δ) :
    ‖x c‖ ≤ ‖x a‖ + (A + L) * (c - a) ^ 2 / 2 + δ * (c - a) := by
  -- The right derivative of `‖x‖ ^ 2` is at most `2 ‖x‖ (A (c - u) + L (u - a) + δ)`.
  have hslope : ∀ u ∈ Ico a c, 2 * (inner ℂ (x u) (-(G u (x u)) + F u)).re ≤
      2 * ‖x u‖ * (A * (c - u) + L * (u - a) + δ) := by
    intro u hu
    have huI : u ∈ Icc a c := Ico_subset_Icc_self hu
    have hacc := hG u huI (x u)
    have hre : (inner ℂ (x u) (F u)).re ≤ ‖x u‖ * (A * (c - u) + L * (u - a) + δ) :=
      (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hF u huI) (norm_nonneg _)))
    rw [inner_add_right, inner_neg_right, Complex.add_re, Complex.neg_re]
    linarith
  -- Comparison with `R ε u = ‖x a‖ + affInt u + ε (u - a) + ε` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → ∀ u ∈ Icc a c,
      ‖x u‖ ≤ ‖x a‖ + affInt A L δ a c u + ε * (u - a) + ε := by
    intro ε hε
    have hRpos : ∀ u ∈ Icc a c, 0 < ‖x a‖ + affInt A L δ a c u + ε * (u - a) + ε := by
      intro u hu
      have h1 := affInt_nonneg hA hL hδ hu
      have h2 : 0 ≤ ε * (u - a) := mul_nonneg hε.le (by linarith [hu.1])
      have h3 := norm_nonneg (x a)
      linarith
    have hR : ∀ u, HasDerivAt (fun t => ‖x a‖ + affInt A L δ a c t + ε * (t - a) + ε)
        (A * (c - u) + L * (u - a) + δ + ε) u := by
      intro u
      have h := (((affInt_hasDerivAt A L δ a c u).const_add ‖x a‖).add
        (((hasDerivAt_id u).sub_const a).const_mul ε)).add_const ε
      exact h.congr_deriv (by ring)
    have hsq : ∀ u ∈ Icc a c,
        ‖x u‖ ^ 2 ≤ (‖x a‖ + affInt A L δ a c u + ε * (u - a) + ε) ^ 2 := by
      apply image_le_of_deriv_right_lt_deriv_boundary' (hx.continuousOn.norm.pow 2)
        (fun u hu => hx.hasDerivWithinAt_norm_sq hu)
        (B' := fun u => 2 * (‖x a‖ + affInt A L δ a c u + ε * (u - a) + ε) *
          (A * (c - u) + L * (u - a) + δ + ε))
      · rw [affInt_left, sub_self, mul_zero, add_zero, add_zero]
        exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
      · exact continuous_iff_continuousAt.mpr (fun u => ((hR u).pow 2).continuousAt)
          |>.continuousOn
      · intro u _
        exact ((hR u).pow 2).hasDerivWithinAt.congr_deriv (by push_cast; ring)
      · intro u hu heq
        have hpos := hRpos u (Ico_subset_Icc_self hu)
        have hnorm : ‖x u‖ = ‖x a‖ + affInt A L δ a c u + ε * (u - a) + ε :=
          (sq_eq_sq₀ (norm_nonneg _) hpos.le).mp heq
        have h1 := hslope u hu
        rw [hnorm] at h1
        nlinarith
    intro u hu
    exact (sq_le_sq₀ (norm_nonneg _) (hRpos u hu).le).mp (hsq u hu)
  have hcI : c ∈ Icc a c := ⟨hac, le_rfl⟩
  have hfin : ‖x c‖ ≤ ‖x a‖ + affInt A L δ a c c := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hc1 : 0 < c - a + 1 := by linarith
    have h := key (ε / (c - a + 1)) (div_pos hε hc1) c hcI
    calc
      ‖x c‖ ≤ ‖x a‖ + affInt A L δ a c c + ε / (c - a + 1) * (c - a) + ε / (c - a + 1) := h
      _ = ‖x a‖ + affInt A L δ a c c + ε / (c - a + 1) * (c - a + 1) := by ring
      _ = ‖x a‖ + affInt A L δ a c c + ε := by rw [div_mul_cancel₀ _ hc1.ne']
  rw [affInt_right] at hfin
  linarith

/-- **Contractivity of the homogeneous equation**: `‖y(c)‖ ≤ ‖y(a)‖`. -/
theorem homog_norm_le {G : ℝ → V →L[ℂ] V} {y : ℝ → V} {a c : ℝ} (hac : a ≤ c)
    (hy : SolvesODE G (fun _ => 0) y a c) (hG : ∀ u ∈ Icc a c, Accretive (G u)) :
    ‖y c‖ ≤ ‖y a‖ := by
  have h := energy_affine hac hy hG (A := 0) (L := 0) (δ := 0) le_rfl le_rfl le_rfl
    (fun u _ => by simp)
  simpa using h

/-- A homogeneous solution that starts at `0` stays `0`. -/
theorem homog_eq_zero {G : ℝ → V →L[ℂ] V} {y : ℝ → V} {a c : ℝ} (hac : a ≤ c)
    (hy : SolvesODE G (fun _ => 0) y a c) (hG : ∀ u ∈ Icc a c, Accretive (G u))
    (hy0 : y a = 0) : y c = 0 := by
  have h := homog_norm_le hac hy hG
  rw [hy0, norm_zero] at h
  exact norm_le_zero_iff.mp h

/-- Adding a differentiable path `φ` to a solution changes the forcing by `φ' + G φ`. -/
theorem solves_add_path {G : ℝ → V →L[ℂ] V} {F x φ φ' : ℝ → V} {a c : ℝ}
    (hx : SolvesODE G F x a c)
    (hφ : ∀ u ∈ Icc a c, HasDerivWithinAt φ (φ' u) (Icc a c) u) :
    SolvesODE G (fun u => F u + φ' u + G u (φ u)) (fun u => x u + φ u) a c := by
  intro u hu
  refine ((hx u hu).add (hφ u hu)).congr_deriv ?_
  simp only [map_add]
  abel

/-- Subtracting a homogeneous solution keeps the forcing. -/
theorem solves_sub_homog {G : ℝ → V →L[ℂ] V} {F x y : ℝ → V} {a c : ℝ}
    (hx : SolvesODE G F x a c) (hy : SolvesODE G (fun _ => 0) y a c) :
    SolvesODE G F (fun u => x u - y u) a c := by
  intro u hu
  refine ((hx u hu).sub (hy u hu)).congr_deriv ?_
  simp only [map_sub]
  abel

/-- The sum of two homogeneous solutions is a homogeneous solution. -/
theorem homog_add {G : ℝ → V →L[ℂ] V} {y z : ℝ → V} {a c : ℝ}
    (hy : SolvesODE G (fun _ => 0) y a c) (hz : SolvesODE G (fun _ => 0) z a c) :
    SolvesODE G (fun _ => 0) (fun u => y u + z u) a c := by
  intro u hu
  refine ((hy u hu).add (hz u hu)).congr_deriv ?_
  simp only [map_add]
  abel

/-- A finite sum of homogeneous solutions is a homogeneous solution. -/
theorem homog_sum {G : ℝ → V →L[ℂ] V} {Y : ℕ → ℝ → V} {a c : ℝ} (s : Finset ℕ)
    (hY : ∀ q ∈ s, SolvesODE G (fun _ => 0) (Y q) a c) :
    SolvesODE G (fun _ => 0) (fun u => ∑ q ∈ s, Y q u) a c := by
  intro u hu
  refine (HasDerivWithinAt.fun_sum (fun q hq => hY q hq u hu)).congr_deriv ?_
  rw [map_sum, ← Finset.sum_neg_distrib]
  simp

end

end SparseHamiltonian.GateQuad
