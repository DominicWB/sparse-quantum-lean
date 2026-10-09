import TimeDependentODE.Continuous.Solution

/-!
# Exponential left-endpoint discretisation of a forced dissipative ODE

For `x' = -G(u) x + b(u)` with accretive generators, the left-endpoint
exponential recurrence with step `h` and samples `Gs r`, `bs r` is

  `y (r + 1) = exp (h • (-Gs r)) (y r + h • bs r)` (`recurrence`).

This module proves

* the one-step estimate against a frozen accretive sample
  (`step_error`): `‖x c - exp ((c - a) • (-Gs)) (x a + (c - a) • bs)‖ ≤ C (c - a)`
  whenever `‖Gs - G u‖ ‖x u‖ + ‖b u - bs‖ + (u - a) ‖Gs‖ ‖bs‖ ≤ C` on `[a, c]`;
* the accumulated error on the uniform mesh `u_r = r T / M` (`mesh_error`),
  for Lipschitz coefficients sampled up to errors `δG`, `δb`;
* the representation of the recurrence as the masked propagators applied to the
  initial state and to the source terms (`recurrence_eq_sum`), each masked
  propagator being a contraction (`maskedPropagator_norm_le_one`).
-/

namespace SparseHamiltonian.TimeDependentODE

noncomputable section

open ContinuousLinearMap Set
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Left-endpoint exponential recurrence with step `h`. -/
def recurrence (Gs : ℕ → V →L[ℂ] V) (bs : ℕ → V) (h : ℝ) (y0 : V) : ℕ → V
  | 0 => y0
  | r + 1 => NormedSpace.exp (h • (-Gs r)) (recurrence Gs bs h y0 r + h • bs r)

/-- Indicator of the slots at or after the start slot `q`. -/
def mask (q r : ℕ) : ℝ := if q ≤ r then 1 else 0

/-- The masked ordered product of the slot exponentials from slot `q` up to `M - 1`. -/
def maskedPropagator (Gs : ℕ → V →L[ℂ] V) (h : ℝ) (q M : ℕ) : V →L[ℂ] V :=
  TimeDependent.evolution (fun r => NormedSpace.exp ((h * mask q r) • (-Gs r))) M

omit [CompleteSpace V] in
@[simp] theorem recurrence_zero (Gs : ℕ → V →L[ℂ] V) (bs : ℕ → V) (h : ℝ) (y0 : V) :
    recurrence Gs bs h y0 0 = y0 := rfl

omit [CompleteSpace V] in
theorem recurrence_succ (Gs : ℕ → V →L[ℂ] V) (bs : ℕ → V) (h : ℝ) (y0 : V) (r : ℕ) :
    recurrence Gs bs h y0 (r + 1) =
      NormedSpace.exp (h • (-Gs r)) (recurrence Gs bs h y0 r + h • bs r) := rfl

theorem mask_of_le {q r : ℕ} (hqr : q ≤ r) : mask q r = 1 := if_pos hqr

theorem mask_of_lt {q r : ℕ} (hrq : r < q) : mask q r = 0 := if_neg (not_le.mpr hrq)

theorem mask_nonneg (q r : ℕ) : 0 ≤ mask q r := by
  unfold mask
  split_ifs <;> norm_num

/-! ### Product rule for complex-linear operator paths -/

omit [CompleteSpace V] in
/-- Product rule for a path of complex-linear operators applied to a path of
vectors, differentiated in a real variable. -/
theorem hasDerivWithinAt_clm_apply {A : ℝ → V →L[ℂ] V} {A' : V →L[ℂ] V}
    {y : ℝ → V} {y' : V} {s : Set ℝ} {u : ℝ}
    (hA : HasDerivWithinAt A A' s u) (hy : HasDerivWithinAt y y' s u) :
    HasDerivWithinAt (fun t => A t (y t)) (A' (y u) + A u y') s u := by
  have hR : HasDerivWithinAt (fun t => (A t).restrictScalars ℝ) (A'.restrictScalars ℝ) s u :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivWithinAt u hA
  exact hR.clm_apply hy

/-! ### One step -/

/-- One step: compare the solution with one exponential step of a frozen sample. -/
theorem step_error {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {a c : ℝ}
    (hx : SolvesODE G b x a c) (hac : a ≤ c)
    (Gs : V →L[ℂ] V) (hGs : Accretive Gs) (bs : V) (C : ℝ)
    (hC : ∀ u ∈ Set.Icc a c,
      ‖Gs - G u‖ * ‖x u‖ + ‖b u - bs‖ + (u - a) * ‖Gs‖ * ‖bs‖ ≤ C) :
    ‖x c - NormedSpace.exp ((c - a) • (-Gs)) (x a + (c - a) • bs)‖ ≤ C * (c - a) := by
  let E : ℝ → V →L[ℂ] V := fun u => NormedSpace.exp ((c - u) • (-Gs))
  have hE : ∀ u, HasDerivAt E (E u * Gs) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => c - v) (-1) u := (hasDerivAt_id' u).const_sub c
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Gs) (c - u)).scomp u hlin
    simpa only [Function.comp_def, neg_one_smul, mul_neg, neg_neg] using h
  let ψ : ℝ → V := fun u => E u (x u) + (c - u) • E a bs
  have hψ : ∀ u ∈ Icc a c, HasDerivWithinAt ψ
      ((E u * Gs) (x u) + E u (-(G u (x u)) + b u) + (-1 : ℝ) • E a bs) (Icc a c) u := by
    intro u hu
    have h1 := hasDerivWithinAt_clm_apply (hE u).hasDerivWithinAt (hx u hu)
    have h2 := ((hasDerivAt_id' u).const_sub c).smul_const (E a bs)
    exact h1.fun_add h2.hasDerivWithinAt
  have hbound : ∀ u ∈ Ico a c,
      ‖(E u * Gs) (x u) + E u (-(G u (x u)) + b u) + (-1 : ℝ) • E a bs‖ ≤ C := by
    intro u hu
    have huI : u ∈ Icc a c := Ico_subset_Icc_self hu
    have hrw : (E u * Gs) (x u) + E u (-(G u (x u)) + b u) + (-1 : ℝ) • E a bs =
        E u ((Gs - G u) (x u) + (b u - bs)) + (E u - E a) bs := by
      simp only [mul_apply_eq_comp, sub_apply, map_add, map_sub, map_neg, neg_one_smul]
      abel
    have hEu : ‖E u‖ ≤ 1 := accretive_exp_norm_le_one Gs hGs (c - u) (by linarith [hu.2])
    have hEdiff : ‖E u - E a‖ ≤ (u - a) * ‖Gs‖ := by
      have h := accretive_exp_sub_norm_le Gs hGs (c - u) (c - a) (by linarith [hu.2])
        (by linarith)
      rwa [show c - u - (c - a) = -(u - a) by ring, abs_neg, abs_of_nonneg (by linarith [hu.1])]
        at h
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
      _ ≤ C := by rw [one_mul]; exact hC u huI
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hψ hbound c ⟨hac, le_rfl⟩
  have hψc : ψ c = x c := by
    simp only [ψ, E, sub_self, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, add_zero]
  have hψa : ψ a = NormedSpace.exp ((c - a) • (-Gs)) (x a + (c - a) • bs) := by
    simp only [ψ, E, map_add, ContinuousLinearMap.map_smul_of_tower]
  rwa [hψc, hψa] at hmvt

/-! ### The uniform mesh -/

/-- Uniform mesh `u_r = r T / M`: accumulated error of the recurrence. -/
theorem mesh_error {G : ℝ → V →L[ℂ] V} {b x : ℝ → V} {T : ℝ} {M : ℕ}
    (hx : SolvesODE G b x 0 T) (hT : 0 ≤ T) (hM : 0 < M)
    (hG : ∀ u ∈ Set.Icc 0 T, Accretive (G u))
    (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r)) (bs : ℕ → V)
    (βG δG βb δb bmax Λ bsmax : ℝ)
    (hβG : 0 ≤ βG) (hβb : 0 ≤ βb) (hbmax : 0 ≤ bmax) (hΛ : 0 ≤ Λ) (hbsmax : 0 ≤ bsmax)
    (hGLip : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖G u - G v‖ ≤ βG * |u - v|)
    (hGs_err : ∀ r < M, ‖G (r * T / M) - Gs r‖ ≤ δG)
    (hbLip : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖b u - b v‖ ≤ βb * |u - v|)
    (hbs_err : ∀ r < M, ‖b (r * T / M) - bs r‖ ≤ δb)
    (hb : ∀ u ∈ Set.Icc 0 T, ‖b u‖ ≤ bmax)
    (hGs_norm : ∀ r < M, ‖Gs r‖ ≤ Λ) (hbs_norm : ∀ r < M, ‖bs r‖ ≤ bsmax) :
    ‖x T - recurrence Gs bs (T / M) (x 0) M‖ ≤
      T * ((βG * (T / M) + δG) * (‖x 0‖ + bmax * T) + βb * (T / M) + δb +
        (T / M) * Λ * bsmax) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  set Δ : ℝ := T / M with hΔdef
  have hΔ : 0 ≤ Δ := div_nonneg hT hMR.le
  set C : ℝ := (βG * Δ + δG) * (‖x 0‖ + bmax * T) + βb * Δ + δb + Δ * Λ * bsmax with hCdef
  let u : ℕ → ℝ := fun r => r * T / M
  have hu : ∀ r, u r = r * Δ := fun r => by simp only [u, hΔdef, mul_div_assoc]
  have hMΔ : (M : ℝ) * Δ = T := by rw [hΔdef]; field_simp
  have hxnorm := hx.norm_le hT hG bmax hb
  -- One step of the recurrence against the solution.
  have hstep : ∀ r < M,
      ‖x (u (r + 1)) - NormedSpace.exp (Δ • (-Gs r)) (x (u r) + Δ • bs r)‖ ≤ C * Δ := by
    intro r hr
    have hr1 : ((r + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hr
    have hlo : 0 ≤ u r := by rw [hu]; positivity
    have hhi : u (r + 1) ≤ T := by
      rw [hu, ← hMΔ]
      exact mul_le_mul_of_nonneg_right hr1 hΔ
    have hlen : u (r + 1) - u r = Δ := by
      rw [hu, hu]
      push_cast
      ring
    have hsub : Icc (u r) (u (r + 1)) ⊆ Icc 0 T := Icc_subset_Icc hlo hhi
    have hurI : u r ∈ Icc 0 T := hsub ⟨le_rfl, by linarith⟩
    have hC : ∀ v ∈ Icc (u r) (u (r + 1)),
        ‖Gs r - G v‖ * ‖x v‖ + ‖b v - bs r‖ + (v - u r) * ‖Gs r‖ * ‖bs r‖ ≤ C := by
      intro v hv
      have hvI := hsub hv
      have hv0 : 0 ≤ v - u r := by linarith [hv.1]
      have hvΔ : v - u r ≤ Δ := by linarith [hv.2]
      have hdist : |v - u r| ≤ Δ := by rw [abs_of_nonneg hv0]; exact hvΔ
      have hG1 : ‖Gs r - G v‖ ≤ βG * Δ + δG := by
        calc
          ‖Gs r - G v‖ = ‖(G v - G (u r)) + (G (u r) - Gs r)‖ := by
            rw [norm_sub_rev]
            congr 1
            abel
          _ ≤ ‖G v - G (u r)‖ + ‖G (u r) - Gs r‖ := norm_add_le _ _
          _ ≤ βG * |v - u r| + δG := add_le_add (hGLip v hvI (u r) hurI) (hGs_err r hr)
          _ ≤ βG * Δ + δG := add_le_add (mul_le_mul_of_nonneg_left hdist hβG) le_rfl
      have hb1 : ‖b v - bs r‖ ≤ βb * Δ + δb := by
        calc
          ‖b v - bs r‖ = ‖(b v - b (u r)) + (b (u r) - bs r)‖ := by
            congr 1
            abel
          _ ≤ ‖b v - b (u r)‖ + ‖b (u r) - bs r‖ := norm_add_le _ _
          _ ≤ βb * |v - u r| + δb := add_le_add (hbLip v hvI (u r) hurI) (hbs_err r hr)
          _ ≤ βb * Δ + δb := add_le_add (mul_le_mul_of_nonneg_left hdist hβb) le_rfl
      have hx1 : ‖x v‖ ≤ ‖x 0‖ + bmax * T :=
        (hxnorm v hvI).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hvI.2 hbmax))
      have hprod : ‖Gs r - G v‖ * ‖x v‖ ≤ (βG * Δ + δG) * (‖x 0‖ + bmax * T) :=
        mul_le_mul hG1 hx1 (norm_nonneg _) ((norm_nonneg _).trans hG1)
      have hsrc : ‖Gs r‖ * ‖bs r‖ ≤ Λ * bsmax :=
        mul_le_mul_of_nonneg (hGs_norm r hr) (hbs_norm r hr) (norm_nonneg _) hbsmax
      have hS : (v - u r) * ‖Gs r‖ * ‖bs r‖ ≤ Δ * Λ * bsmax := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul hvΔ hsrc (by positivity) hΔ
      have hΛb : 0 ≤ Λ * bsmax := mul_nonneg hΛ hbsmax
      rw [hCdef]
      linarith
    have h := step_error (hx.mono hlo hhi) (by linarith) (Gs r) (hGs r) (bs r) C hC
    rw [hlen] at h
    exact h
  -- Accumulation: each exponential step is a contraction.
  have hacc : ∀ r ≤ M, ‖x (u r) - recurrence Gs bs Δ (x 0) r‖ ≤ r * (C * Δ) := by
    intro r
    induction r with
    | zero =>
        intro _
        simp [u]
    | succ r ih =>
        intro hr
        have hrM : r < M := by omega
        have ih' := ih hrM.le
        have hEn : ‖NormedSpace.exp (Δ • (-Gs r))‖ ≤ 1 :=
          accretive_exp_norm_le_one (Gs r) (hGs r) Δ hΔ
        have hsplit : x (u (r + 1)) - recurrence Gs bs Δ (x 0) (r + 1) =
            (x (u (r + 1)) - NormedSpace.exp (Δ • (-Gs r)) (x (u r) + Δ • bs r)) +
              NormedSpace.exp (Δ • (-Gs r)) (x (u r) - recurrence Gs bs Δ (x 0) r) := by
          rw [recurrence_succ]
          simp only [map_add, map_sub]
          abel
        rw [hsplit]
        calc
          ‖(x (u (r + 1)) - NormedSpace.exp (Δ • (-Gs r)) (x (u r) + Δ • bs r)) +
              NormedSpace.exp (Δ • (-Gs r)) (x (u r) - recurrence Gs bs Δ (x 0) r)‖ ≤
              C * Δ + ‖NormedSpace.exp (Δ • (-Gs r))‖ *
                ‖x (u r) - recurrence Gs bs Δ (x 0) r‖ :=
            (norm_add_le _ _).trans (add_le_add (hstep r hrM) (le_opNorm _ _))
          _ ≤ C * Δ + 1 * (r * (C * Δ)) :=
            add_le_add le_rfl (mul_le_mul hEn ih' (norm_nonneg _) zero_le_one)
          _ = ((r + 1 : ℕ) : ℝ) * (C * Δ) := by
            push_cast
            ring
  have hfinal := hacc M le_rfl
  have huM : u M = T := by rw [hu, hMΔ]
  rw [huM] at hfinal
  calc
    ‖x T - recurrence Gs bs Δ (x 0) M‖ ≤ M * (C * Δ) := hfinal
    _ = T * C := by rw [← hMΔ]; ring

/-! ### Masked propagators -/

/-- Each masked propagator is a contraction. -/
theorem maskedPropagator_norm_le_one (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r))
    (h : ℝ) (hh : 0 ≤ h) (q M : ℕ) : ‖maskedPropagator Gs h q M‖ ≤ 1 :=
  TimeDependent.evolution_norm_le_one _
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _ (mul_nonneg hh (mask_nonneg q r))) M

omit [CompleteSpace V] in
/-- Before its start slot, a masked propagator is the identity. -/
theorem maskedPropagator_of_le (Gs : ℕ → V →L[ℂ] V) (h : ℝ) {q M : ℕ} (hMq : M ≤ q) :
    maskedPropagator Gs h q M = 1 := by
  induction M with
  | zero => rfl
  | succ M ih =>
      rw [maskedPropagator, TimeDependent.evolution_succ, mask_of_lt (by omega), mul_zero,
        zero_smul, NormedSpace.exp_zero, one_mul]
      exact ih (by omega)

omit [CompleteSpace V] in
/-- From its start slot on, a masked propagator gains one exponential per slot. -/
theorem maskedPropagator_succ_of_le (Gs : ℕ → V →L[ℂ] V) (h : ℝ) {q M : ℕ} (hqM : q ≤ M) :
    maskedPropagator Gs h q (M + 1) =
      NormedSpace.exp (h • (-Gs M)) * maskedPropagator Gs h q M := by
  rw [maskedPropagator, TimeDependent.evolution_succ, mask_of_le hqM, mul_one]
  rfl

omit [CompleteSpace V] in
/-- The recurrence is the sum of the masked propagators applied to the source terms. -/
theorem recurrence_eq_sum (Gs : ℕ → V →L[ℂ] V) (bs : ℕ → V) (h : ℝ) (y0 : V) (M : ℕ) :
    recurrence Gs bs h y0 M =
      maskedPropagator Gs h 0 M y0 +
        ∑ q ∈ Finset.range M, maskedPropagator Gs h q M (h • bs q) := by
  induction M with
  | zero => simp [maskedPropagator]
  | succ M ih =>
      have hsum : ∑ q ∈ Finset.range M, maskedPropagator Gs h q (M + 1) (h • bs q) =
          NormedSpace.exp (h • (-Gs M))
            (∑ q ∈ Finset.range M, maskedPropagator Gs h q M (h • bs q)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [maskedPropagator_succ_of_le Gs h (Finset.mem_range.mp hq).le, mul_apply_eq_comp]
      rw [recurrence_succ, ih, Finset.sum_range_succ, hsum,
        maskedPropagator_succ_of_le Gs h (Nat.zero_le M),
        maskedPropagator_succ_of_le Gs h (le_refl M), maskedPropagator_of_le Gs h (le_refl M),
        mul_one, mul_apply_eq_comp, map_add, map_add]
      abel

end

end SparseHamiltonian.TimeDependentODE
