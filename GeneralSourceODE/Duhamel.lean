import GeneralSourceODE.Branch
import TimeDependentODE.Continuous.Existence

/-!
# Duhamel's formula for accretive time-dependent generators

Let `U t w` be the homogeneous solution of `y' = -G(u) y` on `[t, T]` with
value `w` at `t` (`IsPropagator`). For an accretive generator path, these
solutions are unique (`homogeneous_unique`), so `U` is linear in `w`
(`IsPropagator.lincomb`), contractive (`IsPropagator.norm_le`) and satisfies
the cocycle law (`IsPropagator.cocycle`). For every solution `x` of the forced
equation `x' = -G(u) x + b(u)` with continuous forcing, the function
`t ↦ U(T, t) x(t)` is Lipschitz with right derivative `U(T, t) b(t)`, so the
fundamental theorem of calculus gives Duhamel's formula

  `∫₀ᵀ U(T, v) b(v) dv = x(T) - U(T, 0) x(0)`   (`duhamel`).

This identifies the certificate on the propagated vector integral of
`ode:eq:source-interface-mass` with a bound on
`x(T) - U(T,0)x₀ - ∑ ω_i U(T, v_i) b(v_i)`.
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap Set TimeDependentODE Filter Topology Asymptotics
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

section Linear

variable {G : ℝ → V →L[ℂ] V} {a c : ℝ}

theorem solvesODE_sub {b₁ b₂ x₁ x₂ : ℝ → V}
    (h₁ : SolvesODE G b₁ x₁ a c) (h₂ : SolvesODE G b₂ x₂ a c) :
    SolvesODE G (fun u => b₁ u - b₂ u) (fun u => x₁ u - x₂ u) a c := by
  intro u hu
  have h := (h₁ u hu).sub (h₂ u hu)
  refine h.congr_deriv ?_
  simp only [map_sub]
  abel

theorem solvesODE_smul {b x : ℝ → V} (h : SolvesODE G b x a c) (k : ℂ) :
    SolvesODE G (fun u => k • b u) (fun u => k • x u) a c := by
  intro u hu
  have h' := (h u hu).const_smul k
  refine h'.congr_deriv ?_
  simp only [map_smul, smul_add, smul_neg]

/-- A homogeneous solution minus its initial value solves the equation forced
by `-G(u) w`. -/
theorem solvesODE_sub_const {y : ℝ → V} (h : SolvesODE G 0 y a c) (w : V) :
    SolvesODE G (fun u => -(G u w)) (fun u => y u - w) a c := by
  intro u hu
  have h' := (h u hu).sub_const w
  refine h'.congr_deriv ?_
  simp only [Pi.zero_apply, add_zero, map_sub]
  abel

theorem solvesODE_zero_sub {y₁ y₂ : ℝ → V}
    (h₁ : SolvesODE G 0 y₁ a c) (h₂ : SolvesODE G 0 y₂ a c) :
    SolvesODE G 0 (fun u => y₁ u - y₂ u) a c := by
  have h := solvesODE_sub h₁ h₂
  have h0 : (fun u => (0 : ℝ → V) u - (0 : ℝ → V) u) = 0 := by
    funext u
    simp
  rwa [h0] at h

/-- Uniqueness of homogeneous solutions of an accretive equation. -/
theorem homogeneous_unique {y₁ y₂ : ℝ → V}
    (h₁ : SolvesODE G 0 y₁ a c) (h₂ : SolvesODE G 0 y₂ a c)
    (hG : ∀ u ∈ Icc a c, Accretive (G u)) (h : y₁ a = y₂ a) :
    ∀ u ∈ Icc a c, y₁ u = y₂ u := by
  intro u hu
  have hd := homogeneous_norm_le (solvesODE_zero_sub h₁ h₂) hG u hu
  rw [h, sub_self, norm_zero] at hd
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hd)

/-- Energy bound on an arbitrary interval: dissipativity means the forcing
alone can increase the norm. -/
theorem solvesODE_norm_le {b x : ℝ → V} (hx : SolvesODE G b x a c) (hac : a ≤ c)
    (hG : ∀ u ∈ Icc a c, Accretive (G u)) (bmax : ℝ)
    (hb : ∀ u ∈ Icc a c, ‖b u‖ ≤ bmax) :
    ∀ u ∈ Icc a c, ‖x u‖ ≤ ‖x a‖ + bmax * (u - a) := by
  have hbmax : 0 ≤ bmax := (norm_nonneg _).trans (hb a ⟨le_rfl, hac⟩)
  have hslope : ∀ u ∈ Ico a c,
      2 * (inner ℂ (x u) (-(G u (x u)) + b u)).re ≤ 2 * ‖x u‖ * bmax := by
    intro u hu
    have huI : u ∈ Icc a c := Ico_subset_Icc_self hu
    have hacc := hG u huI (x u)
    have hre : (inner ℂ (x u) (b u)).re ≤ ‖x u‖ * bmax :=
      (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hb u huI) (norm_nonneg _)))
    rw [inner_add_right, inner_neg_right, Complex.add_re, Complex.neg_re]
    linarith
  have key : ∀ ε : ℝ, 0 < ε → ∀ u ∈ Icc a c,
      ‖x u‖ ≤ ‖x a‖ + (bmax + ε) * (u - a) + ε := by
    intro ε hε
    have hsq : ∀ u ∈ Icc a c, ‖x u‖ ^ 2 ≤ (‖x a‖ + (bmax + ε) * (u - a) + ε) ^ 2 := by
      apply image_le_of_deriv_right_lt_deriv_boundary' (hx.continuousOn.norm.pow 2)
        (fun u hu => hx.hasDerivWithinAt_norm_sq hu)
        (B' := fun u => 2 * (‖x a‖ + (bmax + ε) * (u - a) + ε) * (bmax + ε))
      · rw [sub_self, mul_zero, add_zero]
        exact pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
      · exact (((continuous_const.add (continuous_const.mul
          (continuous_id.sub continuous_const))).add continuous_const).pow 2).continuousOn
      · intro u _
        have h1 : HasDerivAt (fun s : ℝ => ‖x a‖ + (bmax + ε) * (s - a) + ε) (bmax + ε) u :=
          (((((hasDerivAt_id' u).sub_const a).const_mul (bmax + ε)).const_add ‖x a‖).add_const
            ε).congr_deriv (mul_one _)
        exact (h1.fun_pow 2).hasDerivWithinAt.congr_deriv (by simp only [Nat.cast_ofNat,
          Nat.add_one_sub_one, pow_one])
      · intro u hu heq
        have hR : 0 < ‖x a‖ + (bmax + ε) * (u - a) + ε := by
          have : 0 ≤ u - a := by linarith [hu.1]
          positivity
        have hnorm : ‖x u‖ = ‖x a‖ + (bmax + ε) * (u - a) + ε :=
          (sq_eq_sq₀ (norm_nonneg _) hR.le).mp heq
        have h1 := hslope u hu
        rw [hnorm] at h1
        nlinarith
    intro u hu
    have hR : 0 ≤ ‖x a‖ + (bmax + ε) * (u - a) + ε := by
      have : 0 ≤ u - a := by linarith [hu.1]
      positivity
    exact (sq_le_sq₀ (norm_nonneg _) hR).mp (hsq u hu)
  intro u hu
  have hua : 0 ≤ u - a := by linarith [hu.1]
  apply le_of_forall_pos_le_add
  intro ε hε
  have hu1 : 0 < u - a + 1 := by linarith
  have h := key (ε / (u - a + 1)) (div_pos hε hu1) u hu
  calc
    ‖x u‖ ≤ ‖x a‖ + (bmax + ε / (u - a + 1)) * (u - a) + ε / (u - a + 1) := h
    _ = ‖x a‖ + bmax * (u - a) + ε / (u - a + 1) * (u - a + 1) := by ring
    _ = ‖x a‖ + bmax * (u - a) + ε := by rw [div_mul_cancel₀ _ hu1.ne']

end Linear

section Propagator

variable {G : ℝ → V →L[ℂ] V} {U : ℝ → V → ℝ → V} {T : ℝ}

/-- `U t w` is the homogeneous solution on `[t, T]` with value `w` at `t`, for
every start time `t ∈ [0, T]`. -/
def IsPropagator (G : ℝ → V →L[ℂ] V) (U : ℝ → V → ℝ → V) (T : ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, ∀ w, SolvesODE G 0 (U t w) t T ∧ U t w t = w

theorem accretive_sub (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ u ∈ Icc t T, Accretive (G u) := fun u hu => hG u ⟨ht.1.trans hu.1, hu.2⟩

/-- Linear combinations of propagated vectors. -/
theorem IsPropagator.lincomb (hU : IsPropagator G U T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) {t : ℝ} (ht : t ∈ Icc 0 T) (w₁ w₂ : V) (k : ℂ) :
    ∀ u ∈ Icc t T, U t w₁ u - k • U t w₂ u = U t (w₁ - k • w₂) u := by
  have h₁ := (hU t ht w₁).1
  have h₂ := solvesODE_smul (hU t ht w₂).1 k
  have h₂' : SolvesODE G 0 (fun u => k • U t w₂ u) t T := by
    have h0 : (fun u => k • (0 : ℝ → V) u) = 0 := by
      funext u
      simp
    rwa [h0] at h₂
  have hd := solvesODE_zero_sub h₁ h₂'
  apply homogeneous_unique hd (hU t ht (w₁ - k • w₂)).1 (accretive_sub hG ht)
  show U t w₁ t - k • U t w₂ t = U t (w₁ - k • w₂) t
  rw [(hU t ht w₁).2, (hU t ht w₂).2, (hU t ht (w₁ - k • w₂)).2]

theorem IsPropagator.sub (hU : IsPropagator G U T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) {t : ℝ} (ht : t ∈ Icc 0 T) (w₁ w₂ : V) :
    ∀ u ∈ Icc t T, U t w₁ u - U t w₂ u = U t (w₁ - w₂) u := by
  intro u hu
  have h := hU.lincomb hG ht w₁ w₂ 1 u hu
  rwa [one_smul, one_smul] at h

/-- Propagated vectors do not grow. -/
theorem IsPropagator.norm_le (hU : IsPropagator G U T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) {t : ℝ} (ht : t ∈ Icc 0 T) (w : V) :
    ∀ u ∈ Icc t T, ‖U t w u‖ ≤ ‖w‖ := by
  intro u hu
  have h := homogeneous_norm_le (hU t ht w).1 (accretive_sub hG ht) u hu
  rwa [(hU t ht w).2] at h

/-- The cocycle law `U(u, t) = U(u, t') U(t', t)`. -/
theorem IsPropagator.cocycle (hU : IsPropagator G U T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) {t t' : ℝ} (ht : t ∈ Icc 0 T) (htt' : t ≤ t') (ht'T : t' ≤ T)
    (w : V) : ∀ u ∈ Icc t' T, U t w u = U t' (U t w t') u := by
  have ht' : t' ∈ Icc 0 T := ⟨ht.1.trans htt', ht'T⟩
  apply homogeneous_unique ((hU t ht w).1.mono htt' le_rfl) (hU t' ht' (U t w t')).1
    (accretive_sub hG ht')
  rw [(hU t' ht' (U t w t')).2]

/-- A propagated vector moves at most `Λ ‖w‖ (u - t)`. -/
theorem IsPropagator.move (hU : IsPropagator G U T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) {t : ℝ} (ht : t ∈ Icc 0 T) (Λ : ℝ)
    (hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ) (w : V) :
    ∀ u ∈ Icc t T, ‖U t w u - w‖ ≤ Λ * ‖w‖ * (u - t) := by
  intro u hu
  have hsol := solvesODE_sub_const (hU t ht w).1 w
  have hb : ∀ u ∈ Icc t T, ‖-(G u w)‖ ≤ Λ * ‖w‖ := by
    intro u' hu'
    rw [norm_neg]
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (hΛ u' ⟨ht.1.trans hu'.1, hu'.2⟩) (norm_nonneg _))
  have h := solvesODE_norm_le hsol (hu.1.trans hu.2) (accretive_sub hG ht) _ hb u hu
  rw [(hU t ht w).2, sub_self, norm_zero, zero_add] at h
  exact h

/-- A forced solution departs from the propagation of its value at `t` by at
most `bmax (u - t)`. -/
theorem forced_move (hU : IsPropagator G U T) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    {b sol : ℝ → V} (hsol : SolvesODE G b sol 0 T) (bmax : ℝ)
    (hb : ∀ u ∈ Icc 0 T, ‖b u‖ ≤ bmax) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ u ∈ Icc t T, ‖sol u - U t (sol t) u‖ ≤ bmax * (u - t) := by
  intro u hu
  have hd := solvesODE_sub (hsol.mono ht.1 le_rfl) (hU t ht (sol t)).1
  have hd' : SolvesODE G b (fun u => sol u - U t (sol t) u) t T := by
    have h0 : (fun u => b u - (0 : ℝ → V) u) = b := by
      funext u
      simp
    rwa [h0] at hd
  have hb' : ∀ u ∈ Icc t T, ‖b u‖ ≤ bmax := fun u' hu' => hb u' ⟨ht.1.trans hu'.1, hu'.2⟩
  have h := solvesODE_norm_le hd' (hu.1.trans hu.2) (accretive_sub hG ht) bmax hb' u hu
  rw [(hU t ht (sol t)).2, sub_self, norm_zero, zero_add] at h
  exact h

end Propagator

section Duhamel

variable {G : ℝ → V →L[ℂ] V} {U : ℝ → V → ℝ → V} {T : ℝ}

/-- The Duhamel function `t ↦ U(T, t) x(t)` is Lipschitz. -/
theorem duhamel_lipschitz (hU : IsPropagator G U T) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    {b sol : ℝ → V} (hsol : SolvesODE G b sol 0 T) (bmax : ℝ)
    (hb : ∀ u ∈ Icc 0 T, ‖b u‖ ≤ bmax) {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Icc 0 T) (h₂ : t₂ ∈ Icc 0 T)
    (h12 : t₁ ≤ t₂) :
    ‖U t₂ (sol t₂) T - U t₁ (sol t₁) T‖ ≤ bmax * (t₂ - t₁) := by
  have hT₂ : T ∈ Icc t₂ T := ⟨h₂.2, le_rfl⟩
  rw [hU.cocycle hG h₁ h12 h₂.2 (sol t₁) T hT₂, hU.sub hG h₂ _ _ T hT₂]
  exact (hU.norm_le hG h₂ _ T hT₂).trans (forced_move hU hG hsol bmax hb h₁ t₂ ⟨h12, h₂.2⟩)

/-- The propagated forcing `t ↦ U(T, t) b(t)` moves by at most
`‖b(t₂) - b(t₁)‖ + Λ bmax (t₂ - t₁)`. -/
theorem forcing_move (hU : IsPropagator G U T) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    (Λ : ℝ) (hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ) {b : ℝ → V} (bmax : ℝ)
    (hb : ∀ u ∈ Icc 0 T, ‖b u‖ ≤ bmax) {t₁ t₂ : ℝ} (h₁ : t₁ ∈ Icc 0 T) (h₂ : t₂ ∈ Icc 0 T)
    (h12 : t₁ ≤ t₂) :
    ‖U t₂ (b t₂) T - U t₁ (b t₁) T‖ ≤ ‖b t₂ - b t₁‖ + Λ * bmax * (t₂ - t₁) := by
  have hT₂ : T ∈ Icc t₂ T := ⟨h₂.2, le_rfl⟩
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0 ⟨le_rfl, h₁.1.trans h₁.2⟩)
  rw [hU.cocycle hG h₁ h12 h₂.2 (b t₁) T hT₂, hU.sub hG h₂ _ _ T hT₂]
  refine (hU.norm_le hG h₂ _ T hT₂).trans ?_
  have hmove := hU.move hG h₁ Λ hΛ (b t₁) t₂ ⟨h12, h₂.2⟩
  calc
    ‖b t₂ - U t₁ (b t₁) t₂‖ = ‖(b t₂ - b t₁) - (U t₁ (b t₁) t₂ - b t₁)‖ := by
      congr 1
      abel
    _ ≤ ‖b t₂ - b t₁‖ + ‖U t₁ (b t₁) t₂ - b t₁‖ := norm_sub_le _ _
    _ ≤ ‖b t₂ - b t₁‖ + Λ * ‖b t₁‖ * (t₂ - t₁) := add_le_add le_rfl hmove
    _ ≤ ‖b t₂ - b t₁‖ + Λ * bmax * (t₂ - t₁) := by
      have : Λ * ‖b t₁‖ ≤ Λ * bmax := mul_le_mul_of_nonneg_left (hb t₁ h₁) hΛ0
      nlinarith

/-- The propagated forcing is continuous. -/
theorem forcing_continuousOn (hU : IsPropagator G U T) (hG : ∀ u ∈ Icc 0 T, Accretive (G u))
    (Λ : ℝ) (hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ) {b : ℝ → V} (hbc : ContinuousOn b (Icc 0 T))
    (bmax : ℝ) (hb : ∀ u ∈ Icc 0 T, ‖b u‖ ≤ bmax) :
    ContinuousOn (fun t => U t (b t) T) (Icc 0 T) := by
  have hΛ0 : ∀ t ∈ Icc 0 T, 0 ≤ Λ := fun t ht => (norm_nonneg _).trans (hΛ t ht)
  have hbm0 : ∀ t ∈ Icc 0 T, 0 ≤ bmax := fun t ht => (norm_nonneg _).trans (hb t ht)
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.continuousOn_iff.mp hbc t ht (ε / 2) (half_pos hε)
  have hK : 0 < Λ * bmax + 1 := by
    have := mul_nonneg (hΛ0 t ht) (hbm0 t ht)
    linarith
  refine ⟨min δ₁ (ε / (2 * (Λ * bmax + 1))), lt_min hδ₁ (by positivity), ?_⟩
  intro t' ht' hdist
  have hd₁ : dist t' t < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd₂ : |t' - t| < ε / (2 * (Λ * bmax + 1)) := by
    rw [← Real.dist_eq]
    exact lt_of_lt_of_le hdist (min_le_right _ _)
  have hbt : ‖b t' - b t‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hb₁ t' ht' hd₁
  have hKpos : 0 ≤ Λ * bmax := mul_nonneg (hΛ0 t ht) (hbm0 t ht)
  have hlin : Λ * bmax * |t' - t| < ε / 2 := by
    have h1 : Λ * bmax * |t' - t| ≤ (Λ * bmax + 1) * |t' - t| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h2 : (Λ * bmax + 1) * |t' - t| < (Λ * bmax + 1) * (ε / (2 * (Λ * bmax + 1))) :=
      mul_lt_mul_of_pos_left hd₂ hK
    have h3 : (Λ * bmax + 1) * (ε / (2 * (Λ * bmax + 1))) = ε / 2 := by
      field_simp
    linarith
  rw [dist_eq_norm]
  rcases le_total t t' with h | h
  · have hm := forcing_move hU hG Λ hΛ bmax hb ht ht' h
    rw [abs_of_nonneg (sub_nonneg.mpr h)] at hlin
    linarith
  · have hm := forcing_move hU hG Λ hΛ bmax hb ht' ht h
    rw [norm_sub_rev] at hm
    rw [norm_sub_rev] at hbt
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub] at hlin
    linarith

/-- The right derivative of the Duhamel function is the propagated forcing. -/
theorem duhamel_hasDerivWithinAt (hU : IsPropagator G U T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) (Λ : ℝ) (hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ)
    {b sol : ℝ → V} (hsol : SolvesODE G b sol 0 T) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivWithinAt (fun t => U t (sol t) T) (U t (b t) T) (Ioi t) t := by
  have htI : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ t htI)
  -- the departure `e(u) = x(u) - U(u, t) x(t)` has right derivative `b(t)`
  have he : HasDerivWithinAt (fun u => sol u - U t (sol t) u) (b t) (Icc t T) t := by
    have h1 := (hsol t htI).mono (Icc_subset_Icc ht.1.le le_rfl)
    have h2 := (hU t htI (sol t)).1 t ⟨le_rfl, ht.2.le⟩
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    rw [(hU t htI (sol t)).2]
    simp
  have hfilter : 𝓝[>] t ≤ 𝓝[Icc t T] t := by
    rw [← nhdsWithin_Ioc_eq_nhdsGT ht.2]
    exact nhdsWithin_mono t Ioc_subset_Icc_self
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have heo := (hasDerivWithinAt_iff_isLittleO.mp he).def (half_pos hε)
  have heo' := hfilter heo
  have hclose : ∀ᶠ u in 𝓝[>] t, Λ * ‖b t‖ * (u - t) ≤ ε / 2 := by
    have hlim : Tendsto (fun u => Λ * ‖b t‖ * (u - t)) (𝓝[>] t) (𝓝 0) := by
      have : Tendsto (fun u : ℝ => Λ * ‖b t‖ * (u - t)) (𝓝 t) (𝓝 (Λ * ‖b t‖ * (t - t))) :=
        ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto t)
      rw [sub_self, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hlim.eventually (ge_mem_nhds (half_pos hε))
  filter_upwards [heo', hclose, Ioc_mem_nhdsGT ht.2] with u hu hu2 hmem
  show ‖U u (sol u) T - U t (sol t) T - (u - t) • U t (b t) T‖ ≤ ε * ‖u - t‖
  have huI : u ∈ Icc 0 T := ⟨ht.1.le.trans hmem.1.le, hmem.2⟩
  have hTu : T ∈ Icc u T := ⟨hmem.2, le_rfl⟩
  have htu : t ≤ u := hmem.1.le
  have hpos : 0 ≤ u - t := sub_nonneg.mpr htu
  -- rewrite everything as one propagated vector from `u`
  have hrw : U u (sol u) T - U t (sol t) T - (u - t) • U t (b t) T =
      U u (sol u - U t (sol t) u - ((u - t : ℝ) : ℂ) • U t (b t) u) T := by
    rw [hU.cocycle hG htI htu hmem.2 (sol t) T hTu,
      hU.cocycle hG htI htu hmem.2 (b t) T hTu, ← Complex.coe_smul,
      hU.sub hG huI _ _ T hTu, hU.lincomb hG huI _ _ _ T hTu]
  rw [hrw]
  refine (hU.norm_le hG huI _ T hTu).trans ?_
  have hmove := hU.move hG htI Λ hΛ (b t) u ⟨htu, hmem.2⟩
  have he_u : ‖sol u - U t (sol t) u - (sol t - U t (sol t) t) - (u - t) • b t‖ ≤
      ε / 2 * ‖u - t‖ := hu
  rw [(hU t htI (sol t)).2, sub_self, sub_zero] at he_u
  rw [Real.norm_eq_abs, abs_of_nonneg hpos] at he_u ⊢
  calc
    ‖sol u - U t (sol t) u - ((u - t : ℝ) : ℂ) • U t (b t) u‖ =
        ‖(sol u - U t (sol t) u - (u - t) • b t) -
          (u - t) • (U t (b t) u - b t)‖ := by
      rw [Complex.coe_smul, smul_sub]
      congr 1
      abel
    _ ≤ ‖sol u - U t (sol t) u - (u - t) • b t‖ + ‖(u - t) • (U t (b t) u - b t)‖ :=
      norm_sub_le _ _
    _ ≤ ε / 2 * (u - t) + (u - t) * (Λ * ‖b t‖ * (u - t)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
      exact add_le_add he_u (mul_le_mul_of_nonneg_left hmove hpos)
    _ ≤ ε / 2 * (u - t) + (u - t) * (ε / 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hu2 hpos)
    _ = ε * (u - t) := by ring

/-- **Duhamel's formula.** For an accretive generator path bounded by `Λ`, a
continuous forcing and any solution of the forced equation,
`∫₀ᵀ U(T, v) b(v) dv = x(T) - U(T, 0) x(0)`. -/
theorem duhamel [CompleteSpace V] (hT : 0 ≤ T) (hU : IsPropagator G U T)
    (hG : ∀ u ∈ Icc 0 T, Accretive (G u)) (Λ : ℝ) (hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ)
    {b sol : ℝ → V} (hbc : ContinuousOn b (Icc 0 T)) (hsol : SolvesODE G b sol 0 T) :
    ∫ t in (0 : ℝ)..T, U t (b t) T = sol T - U 0 (sol 0) T := by
  obtain ⟨bmax, hb⟩ := isCompact_Icc.exists_bound_of_continuousOn hbc
  have hFcont : ContinuousOn (fun t => U t (sol t) T) (Icc 0 T) := by
    apply continuousOn_of_norm_sub_le (β := bmax)
    intro t₁ h₁ t₂ h₂
    rcases le_total t₁ t₂ with h | h
    · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
      exact duhamel_lipschitz hU hG hsol bmax hb h₁ h₂ h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact duhamel_lipschitz hU hG hsol bmax hb h₂ h₁ h
  have hgint : IntervalIntegrable (fun t => U t (b t) T) MeasureTheory.volume 0 T :=
    (forcing_continuousOn hU hG Λ hΛ hbc bmax hb).intervalIntegrable_of_Icc hT
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hFcont
    (fun t ht => duhamel_hasDerivWithinAt hU hG Λ hΛ hsol ht) hgint
  rw [h, (hU T ⟨hT, le_rfl⟩ (sol T)).2]

end Duhamel

end

end SparseHamiltonian.GeneralSourceODE
