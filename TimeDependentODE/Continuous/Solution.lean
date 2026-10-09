import TimeDependentHamiltonian.Chronology.Products
import SparseHamiltonian.ODEDissipative

/-!
# Forced dissipative linear ODEs: solutions and the energy bound

For a family `G u` of bounded operators on a complex Hilbert space and a forcing
`b u`, a solution of `x' = -G(u) x + b(u)` within `[a, c]` is a path with
one-sided derivatives at the endpoints (`SolvesODE`). A generator is accretive
when `0 ≤ Re ⟪v, G v⟫` (`Accretive`); this is dissipativity of `-G` in the
sense of `SparseHamiltonian.ODEDissipative` (`accretive_iff_dissipative`).
This module proves

* that the frozen exponentials `exp (t • (-A))`, `t ≥ 0`, of an accretive `A`
  are contractions (`accretive_exp_norm_le_one`), Lipschitz in `t` with
  constant `‖A‖` (`accretive_exp_sub_norm_le`), so that
  `‖1 - exp (t • (-A))‖ ≤ t ‖A‖` (`one_sub_exp_norm_le`);
* the energy bound `‖x u‖ ≤ ‖x 0‖ + bmax u` for an accretive family
  (`SolvesODE.norm_le`): the dissipative part cannot increase the norm, so only
  the forcing can.
-/

namespace SparseHamiltonian.TimeDependentODE

noncomputable section

open ContinuousLinearMap Set
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- `x` solves `x' = -G(u) x + b(u)` within `[a, c]` (one-sided derivatives at the ends). -/
def SolvesODE (G : ℝ → V →L[ℂ] V) (b : ℝ → V) (x : ℝ → V) (a c : ℝ) : Prop :=
  ∀ u ∈ Set.Icc a c, HasDerivWithinAt x (-(G u (x u)) + b u) (Set.Icc a c) u

/-- Accretive generator of decay: `0 ≤ Re ⟪v, G v⟫`. -/
def Accretive (G : V →L[ℂ] V) : Prop := ∀ v : V, 0 ≤ (inner ℂ v (G v)).re

omit [CompleteSpace V] in
/-- A solution on an interval restricts to every subinterval. -/
theorem SolvesODE.mono {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c a' c' : ℝ}
    (h : SolvesODE G b x a c) (ha : a ≤ a') (hc : c' ≤ c) : SolvesODE G b x a' c' := by
  intro u hu
  have hsub : Icc a' c' ⊆ Icc a c := Icc_subset_Icc ha hc
  exact (h u (hsub hu)).mono hsub

omit [CompleteSpace V] in
/-- A solution is continuous on its interval. -/
theorem SolvesODE.continuousOn {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c : ℝ}
    (h : SolvesODE G b x a c) : ContinuousOn x (Icc a c) :=
  fun u hu => (h u hu).continuousWithinAt

omit [CompleteSpace V] in
/-- Accretivity of `A` is dissipativity of `-A`. -/
theorem accretive_iff_dissipative (A : V →L[ℂ] V) :
    Accretive A ↔ ODEDissipative.Dissipative (-A) := by
  constructor
  · intro h v
    have hv := h v
    rw [neg_apply, inner_neg_right, Complex.neg_re]
    linarith
  · intro h v
    have hv := h v
    rw [neg_apply, inner_neg_right, Complex.neg_re] at hv
    linarith

/-- The frozen exponential of an accretive generator is a contraction in
nonnegative time. -/
theorem accretive_exp_norm_le_one (A : V →L[ℂ] V) (hA : Accretive A) (t : ℝ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • (-A))‖ ≤ 1 :=
  ODEDissipative.exp_norm_le_one (-A) ((accretive_iff_dissipative A).mp hA) t ht

/-- The frozen exponential of an accretive generator is Lipschitz in nonnegative
time with constant `‖A‖`. -/
theorem accretive_exp_sub_norm_le (A : V →L[ℂ] V) (hA : Accretive A) (t s : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ‖NormedSpace.exp (t • (-A)) - NormedSpace.exp (s • (-A))‖ ≤ |t - s| * ‖A‖ := by
  simpa only [norm_neg] using
    ODEDissipative.exp_sub_norm_le (-A) ((accretive_iff_dissipative A).mp hA) t s ht hs

/-- For short times the frozen exponential of an accretive generator is close to
the identity: `‖1 - exp (t • (-A))‖ ≤ t ‖A‖`. -/
theorem one_sub_exp_norm_le (A : V →L[ℂ] V) (hA : Accretive A) (t : ℝ) (ht : 0 ≤ t) :
    ‖1 - NormedSpace.exp (t • (-A))‖ ≤ t * ‖A‖ := by
  have h := accretive_exp_sub_norm_le A hA t 0 ht le_rfl
  rw [zero_smul, NormedSpace.exp_zero, sub_zero, abs_of_nonneg ht] at h
  rwa [norm_sub_rev]

omit [CompleteSpace V] in
/-- The right derivative of the squared norm of a solution. -/
theorem SolvesODE.hasDerivWithinAt_norm_sq {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c : ℝ}
    (hx : SolvesODE G b x a c) {u : ℝ} (hu : u ∈ Ico a c) :
    HasDerivWithinAt (fun s => ‖x s‖ ^ 2)
      (2 * (inner ℂ (x u) (-(G u (x u)) + b u)).re) (Ici u) u := by
  letI : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  have h1 := (hx u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hu)
  simpa only [real_inner_eq_re_inner ℂ, RCLike.re_to_complex] using h1.norm_sq

omit [CompleteSpace V] in
/-- Energy bound: dissipativity means the forcing alone can increase the norm. -/
theorem SolvesODE.norm_le {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {T : ℝ}
    (hx : SolvesODE G b x 0 T) (hT : 0 ≤ T)
    (hG : ∀ u ∈ Set.Icc 0 T, Accretive (G u)) (bmax : ℝ)
    (hb : ∀ u ∈ Set.Icc 0 T, ‖b u‖ ≤ bmax) :
    ∀ u ∈ Set.Icc 0 T, ‖x u‖ ≤ ‖x 0‖ + bmax * u := by
  have hbmax : 0 ≤ bmax := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  -- The right derivative of `‖x‖ ^ 2` is at most `2 ‖x‖ bmax`.
  have hslope : ∀ u ∈ Ico 0 T,
      2 * (inner ℂ (x u) (-(G u (x u)) + b u)).re ≤ 2 * ‖x u‖ * bmax := by
    intro u hu
    have huI : u ∈ Icc 0 T := Ico_subset_Icc_self hu
    have hacc := hG u huI (x u)
    have hre : (inner ℂ (x u) (b u)).re ≤ ‖x u‖ * bmax :=
      (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hb u huI) (norm_nonneg _)))
    rw [inner_add_right, inner_neg_right, Complex.add_re, Complex.neg_re]
    linarith
  -- Comparison with `(‖x 0‖ + (bmax + ε) u + ε) ^ 2` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → ∀ u ∈ Icc 0 T, ‖x u‖ ≤ ‖x 0‖ + (bmax + ε) * u + ε := by
    intro ε hε
    have hsq : ∀ u ∈ Icc 0 T, ‖x u‖ ^ 2 ≤ (‖x 0‖ + (bmax + ε) * u + ε) ^ 2 := by
      apply image_le_of_deriv_right_lt_deriv_boundary' (hx.continuousOn.norm.pow 2)
        (fun u hu => hx.hasDerivWithinAt_norm_sq hu)
        (B' := fun u => 2 * (‖x 0‖ + (bmax + ε) * u + ε) * (bmax + ε))
      · rw [mul_zero, add_zero]
        exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
      · exact (((continuous_const.add (continuous_const.mul continuous_id)).add
          continuous_const).pow 2).continuousOn
      · intro u _
        have h1 : HasDerivAt (fun s : ℝ => ‖x 0‖ + (bmax + ε) * s + ε) (bmax + ε) u :=
          ((((hasDerivAt_id' u).const_mul (bmax + ε)).const_add ‖x 0‖).add_const
            ε).congr_deriv (mul_one _)
        exact (h1.fun_pow 2).hasDerivWithinAt.congr_deriv (by simp only [Nat.cast_ofNat,
          Nat.add_one_sub_one, pow_one])
      · intro u hu heq
        have hR : 0 < ‖x 0‖ + (bmax + ε) * u + ε := by
          have := hu.1
          positivity
        have hnorm : ‖x u‖ = ‖x 0‖ + (bmax + ε) * u + ε :=
          (sq_eq_sq₀ (norm_nonneg _) hR.le).mp heq
        have h1 := hslope u hu
        rw [hnorm] at h1
        nlinarith
    intro u hu
    have hR : 0 ≤ ‖x 0‖ + (bmax + ε) * u + ε := by
      have := hu.1
      positivity
    exact (sq_le_sq₀ (norm_nonneg _) hR).mp (hsq u hu)
  intro u hu
  apply le_of_forall_pos_le_add
  intro ε hε
  have hu1 : 0 < u + 1 := by linarith [hu.1]
  have h := key (ε / (u + 1)) (div_pos hε hu1) u hu
  calc
    ‖x u‖ ≤ ‖x 0‖ + (bmax + ε / (u + 1)) * u + ε / (u + 1) := h
    _ = ‖x 0‖ + bmax * u + ε / (u + 1) * (u + 1) := by ring
    _ = ‖x 0‖ + bmax * u + ε := by rw [div_mul_cancel₀ _ hu1.ne']

end

end SparseHamiltonian.TimeDependentODE
