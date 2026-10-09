import TimeDependentExtensions.Mesh.Refinement
import TimeDependentODE.Continuous.Discretisation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

/-!
# Forced dissipative ODEs on general meshes with integrated certificates

For `x' = -G(u) x + b(u)` with accretive generators, a mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` and
pieces `G_r`, `b_r` on the intervals `[t_r, t_{r+1}]` (breakpoints at the mesh points, with
one-sided derivatives there), the exponential left-endpoint scheme with steps
`Δ_r = t_{r+1} - t_r` and represented samples `G̃_r`, `b̃_r` is

  `y_{r+1} = exp(-Δ_r G̃_r) (y_r + Δ_r b̃_r)` (`meshRecurrence`).

* `step_error_integral`: one step against a frozen accretive sample, with integrated sample
  errors, `‖x(c) - exp(-(c-a) G̃)(x(a) + (c-a) b̃)‖ ≤
  X ∫ ‖G - G̃‖ + ∫ ‖b - b̃‖ + (c-a)²/2 ‖G̃‖ ‖b̃‖`, for interval-integrable pieces and
  `‖x‖ ≤ X` (the integral form of the released `TimeDependentODE.step_error`);
* `piecewise_norm_le`: the energy bound `‖x(u)‖ ≤ ‖x(0)‖ + b_max T` across the breakpoints;
* `mesh_error`: the accumulated error of the scheme, the sum of the one-step bounds;
* `meshRecurrence_eq_sum`: the scheme is the sum of the masked propagators applied to the
  initial state and to the weighted forcing samples;
* `refinedPropagator_eq`, `refinedPropagator_sub_le`: on the refinement of the mesh into `N`
  slots of length `T / N`, the masked propagators are within `M (T / N) Λ` of those of the
  mesh, `Λ ≥ ‖G̃_r‖`.
-/

namespace TimeDependentExtensions

namespace ODEMesh

noncomputable section

open SparseHamiltonian ContinuousLinearMap Set MeasureTheory
open SparseHamiltonian.TimeDependentODE (SolvesODE Accretive accretive_exp_norm_le_one
  accretive_exp_sub_norm_le hasDerivWithinAt_clm_apply mask mask_nonneg mask_of_le mask_of_lt)
open SparseHamiltonian.TimeDependent (evolution evolution_succ evolution_zero
  evolution_norm_le_one evolution_sub_norm_le)
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### Helpers -/

/-- `exp (a • X) ^ n = exp ((n a) • X)`. -/
theorem exp_smul_pow (X : V →L[ℂ] V) (a : ℝ) (n : ℕ) :
    NormedSpace.exp (a • X) ^ n = NormedSpace.exp (((n : ℝ) * a) • X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← exp_add_commute]
    · congr 1
      rw [← add_smul]
      congr 1
      push_cast
      ring
    · exact ((Commute.refl X).smul_left _).smul_right _

omit [CompleteSpace V] in
/-- An interval-integrable operator path applied to a continuous vector path. -/
theorem intervalIntegrable_apply_right {G : ℝ → V →L[ℂ] V} {x : ℝ → V} {a b : ℝ}
    (hab : a ≤ b) (hG : IntervalIntegrable G volume a b) (hx : ContinuousOn x (Icc a b)) :
    IntervalIntegrable (fun u => G u (x u)) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hG ⊢
  refine Integrable.mono' (hG.norm.const_mul C) ?_ ?_
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hG.aestronglyMeasurable.prodMk (hx.aestronglyMeasurable measurableSet_Icc))
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    calc ‖G u (x u)‖ ≤ ‖G u‖ * ‖x u‖ := le_opNorm _ _
      _ ≤ ‖G u‖ * C := mul_le_mul_of_nonneg_left (hC u hu) (norm_nonneg _)
      _ = C * ‖G u‖ := mul_comm _ _

omit [CompleteSpace V] in
/-- A continuous operator path applied to an interval-integrable vector path. -/
theorem intervalIntegrable_apply_left {E : ℝ → V →L[ℂ] V} {v : ℝ → V} {a b : ℝ}
    (hab : a ≤ b) (hE : ContinuousOn E (Icc a b)) (hv : IntervalIntegrable v volume a b) :
    IntervalIntegrable (fun u => E u (v u)) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hE
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hv ⊢
  refine Integrable.mono' (hv.norm.const_mul C) ?_ ?_
  · exact (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      ((hE.aestronglyMeasurable measurableSet_Icc).prodMk hv.aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    calc ‖E u (v u)‖ ≤ ‖E u‖ * ‖v u‖ := le_opNorm _ _
      _ ≤ C * ‖v u‖ := mul_le_mul_of_nonneg_right (hC u hu) (norm_nonneg _)

/-! ### Energy bound across breakpoints -/

omit [CompleteSpace V] in
/-- The energy bound on an interval `[a, c]`. -/
theorem norm_le_from {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c : ℝ} (hx : SolvesODE G b x a c)
    (hac : a ≤ c) (hG : ∀ u ∈ Icc a c, Accretive (G u)) (bmax : ℝ)
    (hb : ∀ u ∈ Icc a c, ‖b u‖ ≤ bmax) :
    ∀ u ∈ Icc a c, ‖x u‖ ≤ ‖x a‖ + bmax * (u - a) := by
  have hmaps : MapsTo (fun v : ℝ => v + a) (Icc 0 (c - a)) (Icc a c) := by
    intro w hw
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  have hx' : SolvesODE (fun v => G (v + a)) (fun v => b (v + a)) (fun v => x (v + a)) 0
      (c - a) := by
    intro v hv
    have hg : HasDerivWithinAt (fun v : ℝ => v + a) 1 (Icc 0 (c - a)) v :=
      ((hasDerivAt_id' v).add_const a).hasDerivWithinAt
    have h := (hx (v + a) (hmaps hv)).scomp v hg hmaps
    simpa only [one_smul, Function.comp_def] using h
  have h := hx'.norm_le (sub_nonneg.mpr hac) (fun v hv => hG _ (hmaps hv)) bmax
    (fun v hv => hb _ (hmaps hv))
  intro u hu
  have hmem : u - a ∈ Icc 0 (c - a) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h1 := h (u - a) hmem
  simpa only [sub_add_cancel, zero_add] using h1

variable {t : ℕ → ℝ} {M N : ℕ} {T : ℝ}

omit [CompleteSpace V] in
/-- **Energy bound across the breakpoints**: `‖x(u)‖ ≤ ‖x(0)‖ + b_max T`. -/
theorem piecewise_norm_le {G : ℕ → ℝ → V →L[ℂ] V} {b : ℕ → ℝ → V} {x : ℝ → V}
    (hmesh : IsMesh t M T) (hx : ∀ r < M, SolvesODE (G r) (b r) x (t r) (t (r + 1)))
    (hG : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (G r u)) (bmax : ℝ)
    (hbmax : 0 ≤ bmax) (hb : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), ‖b r u‖ ≤ bmax) :
    ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), ‖x u‖ ≤ ‖x 0‖ + bmax * T := by
  have hle : ∀ r, t r ≤ t (r + 1) := fun r => hmesh.mono (Nat.le_succ r)
  have hnode : ∀ r ≤ M, ‖x (t r)‖ ≤ ‖x 0‖ + bmax * t r := by
    intro r
    induction r with
    | zero => intro _; rw [hmesh.zero, mul_zero, add_zero]
    | succ r ih =>
      intro hr
      have h1 := norm_le_from (hx r (by omega)) (hle r) (hG r (by omega)) bmax (hb r (by omega))
        (t (r + 1)) ⟨hle r, le_rfl⟩
      have h2 := ih (by omega)
      nlinarith
  intro r hr u hu
  have h1 := norm_le_from (hx r hr) (hle r) (hG r hr) bmax (hb r hr) u hu
  have h2 := hnode r hr.le
  have hT : u ≤ T := hu.2.trans (hmesh.le_last hr)
  nlinarith [hu.1]

/-! ### One step with integrated sample errors -/

/-- **One step with integrated sample errors.** -/
theorem step_error_integral {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c : ℝ}
    (hx : SolvesODE G b x a c) (hac : a ≤ c)
    (hGint : IntervalIntegrable G volume a c) (hbint : IntervalIntegrable b volume a c)
    (Gs : V →L[ℂ] V) (hGs : Accretive Gs) (bs : V) (X : ℝ)
    (hX : ∀ u ∈ Icc a c, ‖x u‖ ≤ X) :
    ‖x c - NormedSpace.exp ((c - a) • (-Gs)) (x a + (c - a) • bs)‖ ≤
      X * (∫ u in a..c, ‖G u - Gs‖) + (∫ u in a..c, ‖b u - bs‖) +
        (c - a) ^ 2 / 2 * (‖Gs‖ * ‖bs‖) := by
  let E : ℝ → V →L[ℂ] V := fun u => NormedSpace.exp ((c - u) • (-Gs))
  have hE : ∀ u, HasDerivAt E (E u * Gs) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => c - v) (-1) u := (hasDerivAt_id' u).const_sub c
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Gs) (c - u)).scomp u hlin
    simpa only [Function.comp_def, neg_one_smul, mul_neg, neg_neg] using h
  have hEcont : Continuous E := continuous_iff_continuousAt.2 fun u => (hE u).continuousAt
  let ψ : ℝ → V := fun u => E u (x u) + (c - u) • E a bs
  let ψ' : ℝ → V := fun u => (E u * Gs) (x u) + E u (-(G u (x u)) + b u) + (-1 : ℝ) • E a bs
  have hψ : ∀ u ∈ Icc a c, HasDerivWithinAt ψ (ψ' u) (Icc a c) u := by
    intro u hu
    have h1 := hasDerivWithinAt_clm_apply (hE u).hasDerivWithinAt (hx u hu)
    have h2 := ((hasDerivAt_id' u).const_sub c).smul_const (E a bs)
    exact h1.fun_add h2.hasDerivWithinAt
  have hxc : ContinuousOn x (Icc a c) := hx.continuousOn
  have hψcont : ContinuousOn ψ (Icc a c) := fun u hu => (hψ u hu).continuousWithinAt
  have hψ'int : IntervalIntegrable ψ' volume a c := by
    have h1 : IntervalIntegrable (fun u => (E u * Gs) (x u)) volume a c :=
      ContinuousOn.intervalIntegrable_of_Icc hac
        ((hEcont.mul continuous_const).continuousOn.clm_apply hxc)
    have h2 : IntervalIntegrable (fun u => E u (-(G u (x u)) + b u)) volume a c :=
      intervalIntegrable_apply_left hac hEcont.continuousOn
        ((intervalIntegrable_apply_right hac hGint hxc).neg.add hbint)
    exact (h1.add h2).add intervalIntegrable_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hac hψcont
    (fun u hu => ((hψ u (Ioo_subset_Icc_self hu)).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)).hasDerivWithinAt) hψ'int
  have hbound : ∀ u ∈ Icc a c,
      ‖ψ' u‖ ≤ X * ‖G u - Gs‖ + ‖b u - bs‖ + (u - a) * (‖Gs‖ * ‖bs‖) := by
    intro u hu
    have hrw : ψ' u = E u ((Gs - G u) (x u) + (b u - bs)) + (E u - E a) bs := by
      simp only [ψ', mul_apply_eq_comp, sub_apply, map_add, map_sub, map_neg, neg_one_smul]
      abel
    have hEu : ‖E u‖ ≤ 1 := accretive_exp_norm_le_one Gs hGs (c - u) (by linarith [hu.2])
    have hEdiff : ‖E u - E a‖ ≤ (u - a) * ‖Gs‖ := by
      have h := accretive_exp_sub_norm_le Gs hGs (c - u) (c - a) (by linarith [hu.2])
        (by linarith)
      rwa [show c - u - (c - a) = -(u - a) by ring, abs_neg,
        abs_of_nonneg (by linarith [hu.1])] at h
    have hxu : ‖Gs - G u‖ * ‖x u‖ ≤ X * ‖G u - Gs‖ := by
      rw [norm_sub_rev, mul_comm]
      exact mul_le_mul_of_nonneg_right (hX u hu) (norm_nonneg _)
    rw [hrw]
    calc
      ‖E u ((Gs - G u) (x u) + (b u - bs)) + (E u - E a) bs‖ ≤
          ‖E u ((Gs - G u) (x u) + (b u - bs))‖ + ‖(E u - E a) bs‖ := norm_add_le _ _
      _ ≤ ‖E u‖ * ‖(Gs - G u) (x u) + (b u - bs)‖ + ‖E u - E a‖ * ‖bs‖ :=
        add_le_add (le_opNorm _ _) (le_opNorm _ _)
      _ ≤ 1 * (‖Gs - G u‖ * ‖x u‖ + ‖b u - bs‖) + (u - a) * ‖Gs‖ * ‖bs‖ := by
        apply add_le_add
        · apply mul_le_mul hEu _ (norm_nonneg _) zero_le_one
          exact (norm_add_le _ _).trans (add_le_add (le_opNorm _ _) le_rfl)
        · exact mul_le_mul_of_nonneg_right hEdiff (norm_nonneg _)
      _ ≤ X * ‖G u - Gs‖ + ‖b u - bs‖ + (u - a) * (‖Gs‖ * ‖bs‖) := by
        rw [one_mul, mul_assoc]
        linarith
  have hψc : ψ c = x c := by
    simp only [ψ, E, sub_self, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, add_zero]
  have hψa : ψ a = NormedSpace.exp ((c - a) • (-Gs)) (x a + (c - a) • bs) := by
    simp only [ψ, E, map_add, ContinuousLinearMap.map_smul_of_tower]
  have hint1 : IntervalIntegrable (fun u => X * ‖G u - Gs‖) volume a c :=
    (hGint.sub intervalIntegrable_const).norm.const_mul X
  have hint2 : IntervalIntegrable (fun u => ‖b u - bs‖) volume a c :=
    (hbint.sub intervalIntegrable_const).norm
  have hint3 : IntervalIntegrable (fun u => (u - a) * (‖Gs‖ * ‖bs‖)) volume a c :=
    ((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable a c
  have hlin : ∫ u in a..c, (u - a) * (‖Gs‖ * ‖bs‖) = (c - a) ^ 2 / 2 * (‖Gs‖ * ‖bs‖) := by
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_right
      (fun u => u) a, integral_id]
    ring
  calc ‖x c - NormedSpace.exp ((c - a) • (-Gs)) (x a + (c - a) • bs)‖ = ‖ψ c - ψ a‖ := by
        rw [hψc, hψa]
    _ = ‖∫ u in a..c, ψ' u‖ := by rw [hFTC]
    _ ≤ ∫ u in a..c, ‖ψ' u‖ := intervalIntegral.norm_integral_le_integral_norm hac
    _ ≤ ∫ u in a..c, (X * ‖G u - Gs‖ + ‖b u - bs‖ + (u - a) * (‖Gs‖ * ‖bs‖)) :=
        intervalIntegral.integral_mono_on hac hψ'int.norm ((hint1.add hint2).add hint3)
          hbound
    _ = X * (∫ u in a..c, ‖G u - Gs‖) + (∫ u in a..c, ‖b u - bs‖) +
          (c - a) ^ 2 / 2 * (‖Gs‖ * ‖bs‖) := by
        rw [intervalIntegral.integral_add (hint1.add hint2) hint3,
          intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul, hlin]

/-! ### The scheme on the mesh -/

/-- The exponential left-endpoint scheme with steps `h r`. -/
def meshRecurrence (Gs : ℕ → V →L[ℂ] V) (bs : ℕ → V) (h : ℕ → ℝ) (y0 : V) : ℕ → V
  | 0 => y0
  | r + 1 => NormedSpace.exp (h r • (-Gs r)) (meshRecurrence Gs bs h y0 r + h r • bs r)

omit [CompleteSpace V] in
theorem meshRecurrence_succ (Gs : ℕ → V →L[ℂ] V) (bs : ℕ → V) (h : ℕ → ℝ) (y0 : V)
    (r : ℕ) :
    meshRecurrence Gs bs h y0 (r + 1) =
      NormedSpace.exp (h r • (-Gs r)) (meshRecurrence Gs bs h y0 r + h r • bs r) := rfl

/-- **Accumulated error of the scheme on the mesh**: the sum of the one-step bounds. -/
theorem mesh_error {G : ℕ → ℝ → V →L[ℂ] V} {b : ℕ → ℝ → V} {x : ℝ → V}
    (hmesh : IsMesh t M T) (hx : ∀ r < M, SolvesODE (G r) (b r) x (t r) (t (r + 1)))
    (hGint : ∀ r < M, IntervalIntegrable (G r) volume (t r) (t (r + 1)))
    (hbint : ∀ r < M, IntervalIntegrable (b r) volume (t r) (t (r + 1)))
    (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r)) (bs : ℕ → V) (X : ℝ)
    (hX : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), ‖x u‖ ≤ X) :
    ‖x T - meshRecurrence Gs bs (fun r => t (r + 1) - t r) (x 0) M‖ ≤
      ∑ r ∈ Finset.range M, (X * (∫ u in t r..t (r + 1), ‖G r u - Gs r‖) +
        (∫ u in t r..t (r + 1), ‖b r u - bs r‖) +
          (t (r + 1) - t r) ^ 2 / 2 * (‖Gs r‖ * ‖bs r‖)) := by
  have hle : ∀ r, t r ≤ t (r + 1) := fun r => hmesh.mono (Nat.le_succ r)
  have hacc : ∀ m ≤ M, ‖x (t m) - meshRecurrence Gs bs (fun r => t (r + 1) - t r) (x 0) m‖ ≤
      ∑ r ∈ Finset.range m, (X * (∫ u in t r..t (r + 1), ‖G r u - Gs r‖) +
        (∫ u in t r..t (r + 1), ‖b r u - bs r‖) +
          (t (r + 1) - t r) ^ 2 / 2 * (‖Gs r‖ * ‖bs r‖)) := by
    intro m
    induction m with
    | zero => intro _; simp [hmesh.zero, meshRecurrence]
    | succ m ih =>
      intro hm
      have hmM : m < M := by omega
      have hstep := step_error_integral (hx m hmM) (hle m) (hGint m hmM) (hbint m hmM) (Gs m)
        (hGs m) (bs m) X (hX m hmM)
      have hEn : ‖NormedSpace.exp ((t (m + 1) - t m) • (-Gs m))‖ ≤ 1 :=
        accretive_exp_norm_le_one (Gs m) (hGs m) _ (sub_nonneg.mpr (hle m))
      have hsplit : x (t (m + 1)) - meshRecurrence Gs bs (fun r => t (r + 1) - t r) (x 0)
          (m + 1) = (x (t (m + 1)) - NormedSpace.exp ((t (m + 1) - t m) • (-Gs m))
            (x (t m) + (t (m + 1) - t m) • bs m)) +
            NormedSpace.exp ((t (m + 1) - t m) • (-Gs m))
              (x (t m) - meshRecurrence Gs bs (fun r => t (r + 1) - t r) (x 0) m) := by
        rw [meshRecurrence_succ]
        simp only [map_add, map_sub]
        abel
      rw [hsplit, Finset.sum_range_succ]
      calc _ ≤ ‖x (t (m + 1)) - NormedSpace.exp ((t (m + 1) - t m) • (-Gs m))
              (x (t m) + (t (m + 1) - t m) • bs m)‖ +
            ‖NormedSpace.exp ((t (m + 1) - t m) • (-Gs m))‖ *
              ‖x (t m) - meshRecurrence Gs bs (fun r => t (r + 1) - t r) (x 0) m‖ :=
            (norm_add_le _ _).trans (add_le_add le_rfl (le_opNorm _ _))
        _ ≤ _ := by
          have h1 := ih hmM.le
          have h2 : ‖NormedSpace.exp ((t (m + 1) - t m) • (-Gs m))‖ *
              ‖x (t m) - meshRecurrence Gs bs (fun r => t (r + 1) - t r) (x 0) m‖ ≤
                ‖x (t m) - meshRecurrence Gs bs (fun r => t (r + 1) - t r) (x 0) m‖ :=
            mul_le_of_le_one_left (norm_nonneg _) hEn
          linarith
  have h := hacc M le_rfl
  rwa [hmesh.last] at h

/-! ### Masked propagators -/

/-- The masked ordered product of the step exponentials from step `q` up to `M - 1`. -/
def meshPropagator (Gs : ℕ → V →L[ℂ] V) (h : ℕ → ℝ) (q M : ℕ) : V →L[ℂ] V :=
  evolution (fun r => NormedSpace.exp ((h r * mask q r) • (-Gs r))) M

/-- Each masked propagator is a contraction. -/
theorem meshPropagator_norm_le_one (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r))
    (h : ℕ → ℝ) (hh : ∀ r, 0 ≤ h r) (q M : ℕ) : ‖meshPropagator Gs h q M‖ ≤ 1 :=
  evolution_norm_le_one _
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _ (mul_nonneg (hh r) (mask_nonneg q r)))
    M

omit [CompleteSpace V] in
theorem meshPropagator_of_le (Gs : ℕ → V →L[ℂ] V) (h : ℕ → ℝ) {q M : ℕ} (hMq : M ≤ q) :
    meshPropagator Gs h q M = 1 := by
  induction M with
  | zero => rfl
  | succ M ih =>
      rw [meshPropagator, evolution_succ, mask_of_lt (by omega), mul_zero,
        zero_smul, NormedSpace.exp_zero, one_mul]
      exact ih (by omega)

omit [CompleteSpace V] in
theorem meshPropagator_succ_of_le (Gs : ℕ → V →L[ℂ] V) (h : ℕ → ℝ) {q M : ℕ} (hqM : q ≤ M) :
    meshPropagator Gs h q (M + 1) =
      NormedSpace.exp (h M • (-Gs M)) * meshPropagator Gs h q M := by
  rw [meshPropagator, evolution_succ, mask_of_le hqM, mul_one]
  rfl

omit [CompleteSpace V] in
/-- The scheme is the sum of the masked propagators applied to the source terms. -/
theorem meshRecurrence_eq_sum (Gs : ℕ → V →L[ℂ] V) (bs : ℕ → V) (h : ℕ → ℝ) (y0 : V)
    (M : ℕ) :
    meshRecurrence Gs bs h y0 M =
      meshPropagator Gs h 0 M y0 +
        ∑ q ∈ Finset.range M, meshPropagator Gs h q M (h q • bs q) := by
  induction M with
  | zero => simp [meshPropagator, meshRecurrence]
  | succ M ih =>
      have hsum : ∑ q ∈ Finset.range M, meshPropagator Gs h q (M + 1) (h q • bs q) =
          NormedSpace.exp (h M • (-Gs M))
            (∑ q ∈ Finset.range M, meshPropagator Gs h q M (h q • bs q)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [meshPropagator_succ_of_le Gs h (Finset.mem_range.mp hq).le, mul_apply_eq_comp]
      rw [meshRecurrence_succ, ih, Finset.sum_range_succ, hsum,
        meshPropagator_succ_of_le Gs h (Nat.zero_le M),
        meshPropagator_succ_of_le Gs h (le_refl M), meshPropagator_of_le Gs h (le_refl M),
        mul_one, mul_apply_eq_comp, map_add, map_add]
      abel

/-! ### The refinement into `N` slots -/

/-- The masked product over the `N` slots of length `T / N`, slot `k` using the sample of its
interval. -/
def refinedPropagator (Gs : ℕ → V →L[ℂ] V) (t : ℕ → ℝ) (T : ℝ) (N M q : ℕ) : V →L[ℂ] V :=
  evolution (fun k => NormedSpace.exp ((T / N * mask q (slotPiece t T N M k)) •
    (-Gs (slotPiece t T N M k)))) N

/-- The refined propagator is the mesh propagator with the block lengths `n_r T / N`. -/
theorem refinedPropagator_eq (Gs : ℕ → V →L[ℂ] V) (h : IsMesh t M T) (hT : 0 < T) (q : ℕ) :
    refinedPropagator Gs t T N M q =
      meshPropagator Gs (fun r => (blockLength t T N r : ℝ) * (T / N)) q M := by
  unfold refinedPropagator meshPropagator
  rw [evolution_slotPiece (fun r => NormedSpace.exp ((T / N * mask q r) • (-Gs r))) h hT]
  congr 1
  funext r
  rw [exp_smul_pow]
  congr 2
  ring

/-- **Refinement error**: the refined masked propagators are within `M (T / N) Λ` of those of
the mesh, for accretive samples with `‖G̃_r‖ ≤ Λ`. -/
theorem refinedPropagator_sub_le (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r)) {Λ : ℝ}
    (hΛ : ∀ r, ‖Gs r‖ ≤ Λ) (h : IsMesh t M T) (hT : 0 < T) (hN : 0 < N) (q : ℕ) :
    ‖refinedPropagator Gs t T N M q - meshPropagator Gs (fun r => t (r + 1) - t r) q M‖ ≤
      M * (T / N) * Λ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hTN : 0 ≤ T / N := (div_pos hT hNR).le
  rw [refinedPropagator_eq Gs h hT q]
  unfold meshPropagator
  have hm1 : ∀ r, mask q r ≤ 1 := fun r => by unfold mask; split_ifs <;> norm_num
  have hstep : ∀ r, ‖NormedSpace.exp (((blockLength t T N r : ℝ) * (T / N) * mask q r) •
      (-Gs r)) - NormedSpace.exp ((((t (r + 1) - t r : ℝ)) * mask q r) • (-Gs r))‖ ≤
        T / N * Λ := by
    intro r
    have hl : 0 ≤ (blockLength t T N r : ℝ) * (T / N) * mask q r :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hTN) (mask_nonneg q r)
    have hd : 0 ≤ (t (r + 1) - t r) * mask q r :=
      mul_nonneg (h.length_nonneg r) (mask_nonneg q r)
    refine (accretive_exp_sub_norm_le (Gs r) (hGs r) _ _ hl hd).trans ?_
    have habs : |(blockLength t T N r : ℝ) * (T / N) * mask q r -
        (t (r + 1) - t r) * mask q r| ≤ T / N := by
      rw [← sub_mul, abs_mul, abs_of_nonneg (mask_nonneg q r)]
      calc |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| * mask q r ≤
            |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| * 1 :=
          mul_le_mul_of_nonneg_left (hm1 r) (abs_nonneg _)
        _ ≤ T / N := by rw [mul_one]; exact (blockLength_sub_lt h hT hN r).le
    exact mul_le_mul habs (hΛ r) (norm_nonneg _) hTN
  have h1 := SparseHamiltonian.TimeDependent.evolution_sub_norm_le_mul _ _
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hTN) (mask_nonneg q r)))
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _
      (mul_nonneg (h.length_nonneg r) (mask_nonneg q r))) hstep M
  calc _ ≤ (M : ℝ) * (T / N * Λ) := h1
    _ = M * (T / N) * Λ := by ring

end

end ODEMesh

end TimeDependentExtensions
