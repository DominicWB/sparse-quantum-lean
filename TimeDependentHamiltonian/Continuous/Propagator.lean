import TimeDependentHamiltonian.Chronology.Products

/-!
# The time-ordered propagator and its uniform-mesh discretisation

For a family of bounded operators `H u`, a propagator on `[a, b]` is a
function `U` with `U' (u) = -i H(u) U(u)` within `[a, b]` (`SolvesOn`); with
`U 0 = 1` this is `U_H(u, 0) = 𝒯 exp (-i ∫₀ᵘ H)`. This module proves, for
self-adjoint `H`,

* norm conservation `‖U(u) v‖ = ‖U(a) v‖` (`SolvesOn.norm_apply_eq`);
* the unitary Duhamel estimate on one interval against a frozen self-adjoint
  sample `H̃`: `‖U(b) - exp(-i (b-a) H̃) U(a)‖ ≤ C (b - a)` whenever
  `‖H(u) - H̃‖ ≤ C` (`duhamel_step`);
* the telescoping estimate on the uniform mesh `u_k = k t / M` with samples
  obeying `‖H̃_k - H(u_k)‖ ≤ δ` and an operator-norm Lipschitz bound `β`:
  `‖U(t) - ∏_k exp(-i (t/M) H̃_k)‖ ≤ β t² / M + t δ` (`mesh_error`).

This is the discretisation estimate `hs:eq:timedisc` of the manuscript, in
the form used for the uniform mesh; existence of the propagator is proved in
`TimeDependentHamiltonian.Continuous.Existence`.
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap Set
open scoped BigOperators InnerProduct

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- `U` solves the Schrödinger equation `U' = -i H U` within `[a, b]`. -/
def SolvesOn (H U : ℝ → P →L[ℂ] P) (a b : ℝ) : Prop :=
  ∀ u ∈ Icc a b, HasDerivWithinAt U ((-Complex.I) • (H u * U u)) (Icc a b) u

omit [CompleteSpace P] in
theorem SolvesOn.mono {H U : ℝ → P →L[ℂ] P} {a b a' b' : ℝ} (h : SolvesOn H U a b)
    (ha : a ≤ a') (hb : b' ≤ b) : SolvesOn H U a' b' := by
  intro u hu
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  exact (h u (hsub hu)).mono hsub

/-- Self-adjoint generators conserve the norm of every propagated vector. -/
theorem SolvesOn.norm_apply_eq {H U : ℝ → P →L[ℂ] P} {a b : ℝ} (hU : SolvesOn H U a b)
    (hH : ∀ u ∈ Icc a b, star (H u) = H u) (v : P) :
    ∀ u ∈ Icc a b, ‖U u v‖ = ‖U a v‖ := by
  let ev : (P →L[ℂ] P) →L[ℝ] P := (ContinuousLinearMap.apply ℂ P v).restrictScalars ℝ
  have hv : ∀ u ∈ Icc a b, HasDerivWithinAt (fun s => U s v)
      (((-Complex.I) • (H u * U u)) v) (Icc a b) u := by
    intro u hu
    exact ev.hasFDerivAt.comp_hasDerivWithinAt u (hU u hu)
  have hg : ∀ u ∈ Icc a b, HasDerivWithinAt (fun s => inner ℂ (U s v) (U s v)) 0 (Icc a b) u := by
    intro u hu
    have h := (hv u hu).inner ℂ (hv u hu)
    have hself : inner ℂ (H u (U u v)) (U u v) = inner ℂ (U u v) (H u (U u v)) := by
      have h1 := ContinuousLinearMap.adjoint_inner_left (H u) (U u v) (U u v)
      rw [← star_eq_adjoint, hH u hu] at h1
      exact h1
    have hD : ((-Complex.I) • (H u * U u)) v = (-Complex.I) • H u (U u v) := rfl
    have hzero : inner ℂ (U u v) (((-Complex.I) • (H u * U u)) v) +
        inner ℂ (((-Complex.I) • (H u * U u)) v) (U u v) = 0 := by
      rw [hD, inner_smul_right, inner_smul_left, hself, Complex.conj_neg_I]
      ring
    rw [hzero] at h
    exact h
  intro u hu
  have hab : a ≤ b := hu.1.trans hu.2
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' (f' := fun _ => (0 : ℂ))
    (C := 0) hg (fun _ _ => by simp) u hu
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K] at hbound
  have hsq : ‖U u v‖ ^ 2 = ‖U a v‖ ^ 2 := by exact_mod_cast hbound
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- A propagator starting from the identity is a contraction on its interval. -/
theorem SolvesOn.norm_le_one {H U : ℝ → P →L[ℂ] P} {a b : ℝ} (hU : SolvesOn H U a b)
    (hH : ∀ u ∈ Icc a b, star (H u) = H u) (hUa : U a = 1) :
    ∀ u ∈ Icc a b, ‖U u‖ ≤ 1 := by
  intro u hu
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [hU.norm_apply_eq hH v u hu, hUa, one_mul]
  rfl

theorem real_smul_skew (X : P →L[ℂ] P) (hX : star X = -X) (r : ℝ) :
    star (r • X) = -(r • X) := by
  rw [star_smul, hX, smul_neg, star_trivial]

/-- One interval of the unitary Duhamel formula, with a frozen self-adjoint
sample. -/
theorem duhamel_step {H U : ℝ → P →L[ℂ] P} (Hs : P →L[ℂ] P) {a b C : ℝ} (hab : a ≤ b)
    (hU : SolvesOn H U a b) (hUnorm : ∀ u ∈ Icc a b, ‖U u‖ ≤ 1)
    (hHs : star Hs = Hs) (hC : ∀ u ∈ Icc a b, ‖H u - Hs‖ ≤ C) :
    ‖U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a‖ ≤ C * (b - a) := by
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
  have hf : ∀ u ∈ Icc a b, HasDerivWithinAt (fun s => E s * U s)
      (E u * X * U u + E u * ((-Complex.I) • (H u * U u))) (Icc a b) u := by
    intro u hu
    exact ((hE u).hasDerivWithinAt).mul (hU u hu)
  have hbound : ∀ u ∈ Ico a b,
      ‖E u * X * U u + E u * ((-Complex.I) • (H u * U u))‖ ≤ C := by
    intro u hu
    have huIcc : u ∈ Icc a b := Ico_subset_Icc_self hu
    have hrw : E u * X * U u + E u * ((-Complex.I) • (H u * U u)) =
        E u * (Complex.I • ((Hs - H u) * U u)) := by
      simp only [X, mul_smul_comm, smul_mul_assoc, sub_mul, smul_sub, mul_sub, mul_assoc]
      rw [sub_eq_add_neg]
      simp only [neg_smul]
    rw [hrw]
    calc
      ‖E u * (Complex.I • ((Hs - H u) * U u))‖ ≤ ‖E u‖ * (‖Hs - H u‖ * ‖U u‖) := by
        refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
        rw [norm_smul, Complex.norm_I, one_mul]
        exact norm_mul_le _ _
      _ ≤ 1 * (C * 1) := by
        have hCu : ‖Hs - H u‖ ≤ C := by
          rw [norm_sub_rev]
          exact hC u huIcc
        have hC0 : 0 ≤ C := (norm_nonneg _).trans hCu
        exact mul_le_mul (hEnorm u) (mul_le_mul hCu (hUnorm u huIcc) (norm_nonneg _) hC0)
          (by positivity) zero_le_one
      _ = C := by ring
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound b ⟨hab, le_rfl⟩
  have hEa : E a = 1 := by simp [E]
  rw [hEa, one_mul] at hmvt
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
    _ ≤ 1 * (C * (b - a)) := by
      apply mul_le_mul _ hmvt (norm_nonneg _) zero_le_one
      have hskew : star (-Y) = -(-Y) := by
        rw [star_neg, real_smul_skew X hXskew (b - a)]
      exact CayleyApproximation.skew_exp_norm_le _ hskew
    _ = C * (b - a) := one_mul _

omit [CompleteSpace P] in
/-- Telescoping a propagator against an ordered product of contractions. -/
theorem propagator_telescope (U : ℝ → P →L[ℂ] P) (E : ℕ → P →L[ℂ] P)
    (hE : ∀ k, ‖E k‖ ≤ 1) (u : ℕ → ℝ) (hU0 : U (u 0) = 1) (n : ℕ) :
    ‖U (u n) - evolution E n‖ ≤
      ∑ k ∈ Finset.range n, ‖U (u (k + 1)) - E k * U (u k)‖ := by
  induction n with
  | zero => simp [hU0]
  | succ n ih =>
      rw [evolution_succ, Finset.sum_range_succ]
      have hsplit : U (u (n + 1)) - E n * evolution E n =
          (U (u (n + 1)) - E n * U (u n)) + E n * (U (u n) - evolution E n) := by
        noncomm_ring
      rw [hsplit]
      calc
        ‖(U (u (n + 1)) - E n * U (u n)) + E n * (U (u n) - evolution E n)‖ ≤
            ‖U (u (n + 1)) - E n * U (u n)‖ + ‖E n‖ * ‖U (u n) - evolution E n‖ :=
          (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
        _ ≤ ‖U (u (n + 1)) - E n * U (u n)‖ +
            1 * ∑ k ∈ Finset.range n, ‖U (u (k + 1)) - E k * U (u k)‖ :=
          add_le_add le_rfl (mul_le_mul (hE n) ih (norm_nonneg _) zero_le_one)
        _ = _ := by ring

/-- The uniform-mesh discretisation estimate: freezing at the left endpoints,
together with the sample representation error. -/
theorem mesh_error {H U : ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P) {t β δ : ℝ} {M : ℕ}
    (hM : 0 < M) (ht : 0 ≤ t) (hβ : 0 ≤ β)
    (hU0 : U 0 = 1) (hU : SolvesOn H U 0 t)
    (hH : ∀ u ∈ Icc 0 t, star (H u) = H u) (hHs : ∀ k, star (Hs k) = Hs k)
    (hLip : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, ‖H u - H v‖ ≤ β * |u - v|)
    (hVal : ∀ k < M, ‖H (k * t / M) - Hs k‖ ≤ δ) :
    ‖U t - evolution (fun k => NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k)) M‖ ≤
      β * t ^ 2 / M + t * δ := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  let Δ : ℝ := t / M
  have hΔ : 0 ≤ Δ := div_nonneg ht hMR.le
  let u : ℕ → ℝ := fun k => k * t / M
  have hu : ∀ k, u k = k * Δ := fun k => by simp only [u, Δ]; ring
  have huM : u M = t := by simp only [u]; field_simp
  have hUnorm := hU.norm_le_one hH hU0
  have hEnorm : ∀ k, ‖NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k)‖ ≤ 1 := by
    intro k
    apply CayleyApproximation.skew_exp_norm_le
    rw [star_smul, hHs k, ← neg_smul]
    congr 1
    simp [Complex.conj_ofReal]
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hVal 0 hM)
  have hstep : ∀ k < M, ‖U (u (k + 1)) -
      NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k) * U (u k)‖ ≤
        (β * Δ + δ) * Δ := by
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
    have hC : ∀ v ∈ Icc (u k) (u (k + 1)), ‖H v - Hs k‖ ≤ β * Δ + δ := by
      intro v hv
      have hvI := hsub hv
      have hkI : u k ∈ Icc 0 t := hsub ⟨le_rfl, by linarith [hv.1, hv.2]⟩
      calc
        ‖H v - Hs k‖ ≤ ‖H v - H (u k)‖ + ‖H (u k) - Hs k‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ β * |v - u k| + δ := add_le_add (hLip v hvI (u k) hkI) (hVal k hk)
        _ ≤ β * Δ + δ := by
          gcongr
          rw [abs_of_nonneg (by linarith [hv.1])]
          linarith [hv.2]
    have h := duhamel_step (Hs k) (by linarith) (hU.mono hlo hhi)
      (fun v hv => hUnorm v (hsub hv)) (hHs k) hC
    rw [hlen] at h
    exact h
  have htel := propagator_telescope U _ hEnorm u (by simp [u, hU0]) M
  rw [huM] at htel
  calc
    _ ≤ ∑ k ∈ Finset.range M, ‖U (u (k + 1)) -
        NormedSpace.exp ((-Complex.I * ((t / M : ℝ) : ℂ)) • Hs k) * U (u k)‖ := htel
    _ ≤ ∑ _k ∈ Finset.range M, (β * Δ + δ) * Δ :=
      Finset.sum_le_sum (fun k hk => hstep k (Finset.mem_range.mp hk))
    _ = β * t ^ 2 / M + t * δ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Δ]
      field_simp

end

end SparseHamiltonian.TimeDependent
