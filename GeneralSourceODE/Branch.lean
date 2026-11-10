import GeneralSourceODE.Durations
import TimeDependentODE.Continuous.Discretisation

/-!
# Propagation of one source branch from its node

For the general source interface the target of `ode:thm:time` is assembled
from homogeneous propagations `U(T, v) w`: the initial state from `0` and each
loaded forcing vector from its node `v`. Here `U(T, v) w` is the value at `T`
of a solution of `y' = -G(u) y` on `[v, T]` with `y(v) = w`.

The circuit propagates a branch with the node propagator of its start time
(`nodePropagator`): the exponentials of the represented samples `G̃_r` on the
parts of the slots after `v`, with a partial first step when `v` is inside a
slot. Against a `β_G`-Lipschitz accretive path with sample errors
`‖G(t_r) - G̃_r‖ ≤ δ_G`, the branch error is at most

  `(T - v) (β_G T / M + δ_G) ‖w‖`   (`branch_error`),

uniformly over the start time. The proof applies the released one-step
estimate `TimeDependentODE.step_error` on every slot part and uses that
homogeneous solutions are contractions (`homogeneous_norm_le`).
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap Set TimeDependentODE
open scoped BigOperators InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- Homogeneous solutions of an accretive equation do not grow. -/
theorem homogeneous_norm_le {G : ℝ → V →L[ℂ] V} {y : ℝ → V} {a c : ℝ}
    (hy : SolvesODE G 0 y a c) (hG : ∀ u ∈ Icc a c, Accretive (G u)) :
    ∀ u ∈ Icc a c, ‖y u‖ ≤ ‖y a‖ := by
  have hsq : ∀ u ∈ Icc a c, ‖y u‖ ^ 2 ≤ ‖y a‖ ^ 2 := by
    apply image_le_of_deriv_right_le_deriv_boundary (hy.continuousOn.norm.pow 2)
      (fun u hu => hy.hasDerivWithinAt_norm_sq hu)
      (B := fun _ => ‖y a‖ ^ 2) (B' := fun _ => 0) le_rfl continuousOn_const
      (fun u _ => hasDerivWithinAt_const u _ _)
    intro u hu
    have hacc := hG u (Ico_subset_Icc_self hu) (y u)
    simp only [Pi.zero_apply, add_zero, inner_neg_right, Complex.neg_re]
    linarith
  intro u hu
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsq u hu)

/-- **Branch error.** The node propagator of the start time `t₀` approximates
the homogeneous propagation from `t₀` to `T` within
`(T - t₀) (β_G T/M + δ_G) ‖y(t₀)‖`. -/
theorem branch_error {G : ℝ → V →L[ℂ] V} {y : ℝ → V} {T t₀ : ℝ} {M : ℕ}
    (hT : 0 ≤ T) (hM : 0 < M) (ht₀ : 0 ≤ t₀) (ht₀T : t₀ ≤ T)
    (hy : SolvesODE G 0 y t₀ T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r))
    (βG δG : ℝ) (hβG : 0 ≤ βG) (hδG : 0 ≤ δG)
    (hGLip : ∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|)
    (hGs_err : ∀ r < M, ‖G (r * T / M) - Gs r‖ ≤ δG) :
    ‖y T - nodePropagator Gs T M t₀ (y t₀)‖ ≤
      (T - t₀) * ((βG * (T / M) + δG) * ‖y t₀‖) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set Δ : ℝ := T / M with hΔdef
  have hΔ : 0 ≤ Δ := div_nonneg hT hMR.le
  set C : ℝ := (βG * Δ + δG) * ‖y t₀‖ with hCdef
  have hC0 : 0 ≤ C := mul_nonneg (by positivity) (norm_nonneg _)
  let c : ℕ → ℝ := clip T M t₀
  let ev : ℕ → V →L[ℂ] V := fun r =>
    TimeDependent.evolution (fun k => NormedSpace.exp (width T M t₀ k • (-Gs k))) r
  have hGsub : ∀ u ∈ Icc t₀ T, Accretive (G u) := fun u hu => hG u ⟨ht₀.trans hu.1, hu.2⟩
  have hnorm := homogeneous_norm_le hy hGsub
  have hacc : ∀ r ≤ M, ‖y (c r) - ev r (y t₀)‖ ≤ (c r - t₀) * C := by
    intro r
    induction r with
    | zero =>
        intro _
        have h0 : c 0 = t₀ := clip_zero ht₀
        rw [h0]
        simp [ev]
    | succ r ih =>
        intro hr
        have hrM : r < M := by omega
        have ih' := ih hrM.le
        have hlo : t₀ ≤ c r := le_clip r
        have hhi : c (r + 1) ≤ T := clip_le hT hM ht₀T hr
        have hcr : c r ≤ c (r + 1) := clip_mono hT (Nat.le_succ r)
        have hw : width T M t₀ r = c (r + 1) - c r := rfl
        set E : V →L[ℂ] V := NormedSpace.exp (width T M t₀ r • (-Gs r)) with hEdef
        have hEn : ‖E‖ ≤ 1 := accretive_exp_norm_le_one (Gs r) (hGs r) _ (width_nonneg hT r)
        have hev : ev (r + 1) = E * ev r := TimeDependent.evolution_succ _ r
        -- one slot part
        have hstep : ‖y (c (r + 1)) - E (y (c r))‖ ≤ C * width T M t₀ r := by
          rcases (width_nonneg (T := T) (M := M) (t₀ := t₀) hT r).eq_or_lt with h0 | hpos
          · have hceq : c (r + 1) = c r := by linarith
            rw [← h0, mul_zero, hEdef, ← h0, zero_smul, NormedSpace.exp_zero,
              one_apply_eq_self, hceq, sub_self, norm_zero]
          · have hsol : SolvesODE G 0 y (c r) (c (r + 1)) := hy.mono hlo hhi
            have hbound : ∀ u ∈ Icc (c r) (c (r + 1)),
                ‖Gs r - G u‖ * ‖y u‖ + ‖(0 : ℝ → V) u - 0‖ +
                  (u - c r) * ‖Gs r‖ * ‖(0 : V)‖ ≤ C := by
              intro u hu
              obtain ⟨hu1, hu2⟩ := mem_slot_of_width_pos hpos hu
              have huT : u ∈ Icc 0 T := ⟨ht₀.trans (hlo.trans hu.1), hu.2.trans hhi⟩
              have hsT : (r : ℝ) * T / M ∈ Icc 0 T := by
                refine ⟨by positivity, ?_⟩
                rw [div_le_iff₀ hMR]
                have : (r : ℝ) ≤ M := by exact_mod_cast hrM.le
                nlinarith
              have hdist : |u - r * T / M| ≤ Δ := by
                rw [abs_of_nonneg (by linarith)]
                exact hu2
              have hG1 : ‖Gs r - G u‖ ≤ βG * Δ + δG := by
                calc
                  ‖Gs r - G u‖ = ‖(G u - G (r * T / M)) + (G (r * T / M) - Gs r)‖ := by
                    rw [norm_sub_rev]
                    congr 1
                    abel
                  _ ≤ ‖G u - G (r * T / M)‖ + ‖G (r * T / M) - Gs r‖ := norm_add_le _ _
                  _ ≤ βG * |u - r * T / M| + δG :=
                    add_le_add (hGLip u huT _ hsT) (hGs_err r hrM)
                  _ ≤ βG * Δ + δG := add_le_add (mul_le_mul_of_nonneg_left hdist hβG) le_rfl
              have hy1 : ‖y u‖ ≤ ‖y t₀‖ := hnorm u ⟨hlo.trans hu.1, hu.2.trans hhi⟩
              have hprod : ‖Gs r - G u‖ * ‖y u‖ ≤ C :=
                mul_le_mul hG1 hy1 (norm_nonneg _) (by positivity)
              simp only [Pi.zero_apply, sub_zero, norm_zero, mul_zero, add_zero]
              exact hprod
            have h := step_error hsol hcr (Gs r) (hGs r) 0 C hbound
            simp only [smul_zero, add_zero] at h
            rw [hEdef, hw]
            exact h
        have hsplit : y (c (r + 1)) - ev (r + 1) (y t₀) =
            (y (c (r + 1)) - E (y (c r))) + E (y (c r) - ev r (y t₀)) := by
          rw [hev]
          simp only [mul_apply_eq_comp, map_sub]
          abel
        rw [hsplit]
        calc
          ‖(y (c (r + 1)) - E (y (c r))) + E (y (c r) - ev r (y t₀))‖ ≤
              C * width T M t₀ r + ‖E‖ * ‖y (c r) - ev r (y t₀)‖ :=
            (norm_add_le _ _).trans (add_le_add hstep (le_opNorm _ _))
          _ ≤ C * width T M t₀ r + 1 * ((c r - t₀) * C) :=
            add_le_add le_rfl (mul_le_mul hEn ih' (norm_nonneg _) zero_le_one)
          _ = (c (r + 1) - t₀) * C := by
            rw [hw]
            ring
  have hfinal := hacc M le_rfl
  have hcM : c M = T := clip_last hM ht₀T
  rw [hcM] at hfinal
  exact hfinal

end

end SparseHamiltonian.GeneralSourceODE
