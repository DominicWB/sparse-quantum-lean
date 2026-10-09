import TimeDependentExtensions.Mesh.Refinement
import TimeDependentHamiltonian.Continuous.Existence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

/-!
# Piecewise paths and integrated sample-error certificates

A path with breakpoints at the mesh points is given by one piece `H_r` per interval
`[t_r, t_{r+1}]`; a propagator of the piecewise path solves `U' = -i H_r(u) U` on every closed
interval, with one-sided derivatives at the mesh points (`IsPiecewisePropagator`). This is
the manuscript's piecewise Lipschitz path "when all breakpoints are supplied", and more
generally a path with continuous pieces, measured by the integrated certificate. Propagators
are classical (`SolvesOn`: a derivative at every point of each closed interval), so a piece
with a jump inside its interval has no propagator and every discontinuity must be a mesh
point; Carathéodory propagators of general integrable paths are not treated.

* `duhamel_integral`: on one interval, against a frozen self-adjoint sample `H̃`,
  `‖U(b) - exp(-i (b - a) H̃) U(a)‖ ≤ ∫_a^b ‖H(u) - H̃‖ du` for an interval-integrable
  self-adjoint `H` (the integral form of the unitary Duhamel formula; the released
  `duhamel_step` is the special case of a constant bound).
* `mesh_error_integral`: `‖U(T) - ∏_r exp(-i (t_{r+1} - t_r) H̃_r)‖ ≤ ∑_r ∫ ‖H_r - H̃_r‖`,
  the certified sum of integrated sample errors of the manuscript.
* `refined_error`: the same against the refined slot product of `Refinement.lean`, with the
  additional refinement error `M (T / N) Λ`.
* `integral_le_of_lipschitz`, `integral_le_of_lipschitz'`: a `β`-Lipschitz piece with
  left-endpoint sample error `δ` contributes at most `β Δ²/2 + δ Δ` (equation
  `hs:eq:timedisc` without the Cayley term), for paths in any normed group.
* `exists_piecewise_propagator`: continuous pieces have a propagator, so the hypotheses are
  satisfiable for them; `isPiecewisePropagator_of_solvesOn`: a propagator of one path on
  `[0, T]` is a piecewise propagator on every mesh.
-/

namespace TimeDependentExtensions

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap Set MeasureTheory
open scoped BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### One interval -/

/-- **Integral form of the unitary Duhamel estimate** on one interval, against a frozen
self-adjoint sample. -/
theorem duhamel_integral {H U : ℝ → P →L[ℂ] P} (Hs : P →L[ℂ] P) {a b : ℝ} (hab : a ≤ b)
    (hU : SolvesOn H U a b) (hUnorm : ∀ u ∈ Icc a b, ‖U u‖ ≤ 1)
    (hHs : star Hs = Hs) (hint : IntervalIntegrable H volume a b) :
    ‖U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a‖ ≤
      ∫ u in a..b, ‖H u - Hs‖ := by
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
  let f' : ℝ → P →L[ℂ] P := fun u => E u * (Complex.I • ((Hs - H u) * U u))
  have hderiv : ∀ u ∈ Icc a b, HasDerivWithinAt (fun s => E s * U s) (f' u) (Icc a b) u := by
    intro u hu
    have hrw : E u * X * U u + E u * ((-Complex.I) • (H u * U u)) =
        E u * (Complex.I • ((Hs - H u) * U u)) := by
      simp only [X, mul_smul_comm, smul_mul_assoc, sub_mul, smul_sub, mul_sub, mul_assoc]
      rw [sub_eq_add_neg]
      simp only [neg_smul]
    have h := ((hE u).hasDerivWithinAt).mul (hU u hu)
    rw [hrw] at h
    exact h
  have hcont : ContinuousOn (fun s => E s * U s) (Icc a b) := fun u hu =>
    (hderiv u hu).continuousWithinAt
  have hderiv' : ∀ u ∈ Ioo a b, HasDerivAt (fun s => E s * U s) (f' u) u := fun u hu =>
    (hderiv u (Ioo_subset_Icc_self hu)).hasDerivAt (Icc_mem_nhds hu.1 hu.2)
  have hUcont : ContinuousOn U (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun u hu => (hU u hu).continuousWithinAt
  have hEcont : ContinuousOn E (uIcc a b) := fun u _ => (hE u).continuousAt.continuousWithinAt
  have hint' : IntervalIntegrable f' volume a b := by
    have h1 : IntervalIntegrable (fun u => Hs - H u) volume a b :=
      intervalIntegrable_const.sub hint
    have h2 : IntervalIntegrable (fun u => (Hs - H u) * U u) volume a b :=
      h1.mul_continuousOn hUcont
    have h3 : IntervalIntegrable (fun u => Complex.I • ((Hs - H u) * U u)) volume a b :=
      h2.smul Complex.I
    exact h3.continuousOn_mul hEcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv' hint'
  have hbound : ‖E b * U b - E a * U a‖ ≤ ∫ u in a..b, ‖H u - Hs‖ := by
    rw [← hFTC]
    apply intervalIntegral.norm_integral_le_of_norm_le hab
    · refine ae_of_all _ (fun u hu => ?_)
      have huIcc : u ∈ Icc a b := Ioc_subset_Icc_self hu
      calc ‖f' u‖ ≤ ‖E u‖ * (‖Hs - H u‖ * ‖U u‖) := by
            refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
            rw [norm_smul, Complex.norm_I, one_mul]
            exact norm_mul_le _ _
        _ ≤ 1 * (‖H u - Hs‖ * 1) := by
            rw [norm_sub_rev]
            exact mul_le_mul (hEnorm u) (mul_le_mul le_rfl (hUnorm u huIcc) (norm_nonneg _)
              (norm_nonneg _)) (by positivity) zero_le_one
        _ = ‖H u - Hs‖ := by ring
    · exact (hint.sub intervalIntegrable_const).norm
  have hEa : E a = 1 := by simp [E]
  rw [hEa, one_mul] at hbound
  let Y : P →L[ℂ] P := (b - a) • X
  have hinv : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← exp_add_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
      NormedSpace.exp_zero]
  have hY : -Y = (-Complex.I * ((b - a : ℝ) : ℂ)) • Hs := by
    simp only [Y, X, ← Complex.coe_smul, smul_smul, ← neg_smul]
    congr 1
    ring
  have hfactor : U b - NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • Hs) * U a =
      NormedSpace.exp (-Y) * (E b * U b - U a) := by
    rw [mul_sub, ← mul_assoc, show E b = NormedSpace.exp Y from rfl, hinv, one_mul, hY]
  rw [hfactor]
  calc ‖NormedSpace.exp (-Y) * (E b * U b - U a)‖ ≤
        ‖NormedSpace.exp (-Y)‖ * ‖E b * U b - U a‖ := norm_mul_le _ _
    _ ≤ 1 * ∫ u in a..b, ‖H u - Hs‖ := by
      apply mul_le_mul _ hbound (norm_nonneg _) zero_le_one
      have hskew : star (-Y) = -(-Y) := by
        rw [star_neg, real_smul_skew X hXskew (b - a)]
      exact CayleyApproximation.skew_exp_norm_le _ hskew
    _ = ∫ u in a..b, ‖H u - Hs‖ := one_mul _

section Lipschitz

variable {E : Type*} [NormedAddCommGroup E]

/-- A `β`-Lipschitz piece with left-endpoint sample error `δ` has integrated sample error at
most `β Δ² / 2 + δ Δ` (paths in any normed group: generators, forcing). -/
theorem integral_le_of_lipschitz (H : ℝ → E) (Hs : E) {a b β δ : ℝ}
    (hab : a ≤ b) (hLip : ∀ u ∈ Icc a b, ‖H u - H a‖ ≤ β * (u - a)) (hδ : ‖H a - Hs‖ ≤ δ)
    (hint : IntervalIntegrable (fun u => ‖H u - Hs‖) volume a b) :
    ∫ u in a..b, ‖H u - Hs‖ ≤ β * (b - a) ^ 2 / 2 + δ * (b - a) := by
  have hF : ∀ u ∈ uIcc a b, HasDerivAt (fun v => β * ((v - a) * (v - a)) / 2 + δ * v)
      (β * (u - a) + δ) u := by
    intro u _
    have h1 : HasDerivAt (fun v : ℝ => v - a) 1 u := (hasDerivAt_id' u).sub_const a
    have h3 : HasDerivAt (fun v : ℝ => β * ((v - a) * (v - a)) / 2 + δ * v)
        (β * (1 * (u - a) + (u - a) * 1) / 2 + δ * 1) u :=
      (((h1.mul h1).const_mul β).div_const 2).add ((hasDerivAt_id' u).const_mul δ)
    convert h3 using 1
    ring
  have hcontB : Continuous (fun u : ℝ => β * (u - a) + δ) := by continuity
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (hcontB.intervalIntegrable a b)
  calc ∫ u in a..b, ‖H u - Hs‖ ≤ ∫ u in a..b, (β * (u - a) + δ) :=
        intervalIntegral.integral_mono_on hab hint (hcontB.intervalIntegrable a b)
          (fun u hu => (norm_sub_le_norm_sub_add_norm_sub (H u) (H a) Hs).trans
            (add_le_add (hLip u hu) hδ))
    _ = β * (b - a) ^ 2 / 2 + δ * (b - a) := by
      rw [hval]
      ring

/-- A Lipschitz path is continuous on its closed interval. -/
theorem continuousOn_of_lipschitz (H : ℝ → E) {a b β : ℝ}
    (hLip : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, ‖H u - H v‖ ≤ β * |u - v|) :
    ContinuousOn H (Icc a b) := by
  intro u hu
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_cases hβ : β ≤ 0
  · refine ⟨1, one_pos, fun v hv _ => ?_⟩
    rw [dist_eq_norm]
    have h := hLip v hv u hu
    have : β * |v - u| ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ (abs_nonneg _)
    linarith [norm_nonneg (H v - H u)]
  · have hβ' : 0 < β := lt_of_not_ge hβ
    refine ⟨ε / β, div_pos hε hβ', fun v hv hvu => ?_⟩
    rw [dist_eq_norm]
    rw [Real.dist_eq] at hvu
    calc
      ‖H v - H u‖ ≤ β * |v - u| := hLip v hv u hu
      _ < β * (ε / β) := mul_lt_mul_of_pos_left hvu hβ'
      _ = ε := by field_simp

/-- The same with the two-point Lipschitz bound of the manuscript. -/
theorem integral_le_of_lipschitz' (H : ℝ → E) (Hs : E) {a b β δ : ℝ}
    (hab : a ≤ b) (hLip : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, ‖H u - H v‖ ≤ β * |u - v|)
    (hδ : ‖H a - Hs‖ ≤ δ) :
    ∫ u in a..b, ‖H u - Hs‖ ≤ β * (b - a) ^ 2 / 2 + δ * (b - a) := by
  have hcont := continuousOn_of_lipschitz H hLip
  apply integral_le_of_lipschitz H Hs hab _ hδ
  · exact ((hcont.sub continuousOn_const).norm).intervalIntegrable_of_Icc hab
  · intro u hu
    have h := hLip u hu a ⟨le_rfl, hab⟩
    rwa [abs_of_nonneg (sub_nonneg.mpr hu.1)] at h

end Lipschitz

/-! ### Piecewise propagators -/

/-- `U` is a propagator of the piecewise path `H_r` on the mesh `t`: it starts at the
identity and solves `U' = -i H_r(u) U` on every closed interval `[t_r, t_{r+1}]`, `r < M`. -/
def IsPiecewisePropagator (Hp : ℕ → ℝ → P →L[ℂ] P) (t : ℕ → ℝ) (M : ℕ)
    (U : ℝ → P →L[ℂ] P) : Prop :=
  U 0 = 1 ∧ ∀ r < M, SolvesOn (Hp r) U (t r) (t (r + 1))

variable {t : ℕ → ℝ} {M N : ℕ} {T : ℝ}

/-- A piecewise propagator of self-adjoint pieces is unitary at the mesh points. -/
theorem piecewise_norm_apply {Hp : ℕ → ℝ → P →L[ℂ] P} {U : ℝ → P →L[ℂ] P}
    (h : IsMesh t M T) (hU : IsPiecewisePropagator Hp t M U)
    (hH : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hp r u) = Hp r u) :
    ∀ r ≤ M, ∀ v : P, ‖U (t r) v‖ = ‖v‖ := by
  intro r
  induction r with
  | zero => intro _ v; rw [h.zero, hU.1, one_apply_eq_self]
  | succ r ih =>
    intro hr v
    have hrM : r < M := by omega
    have hmem : t (r + 1) ∈ Icc (t r) (t (r + 1)) := ⟨h.mono (Nat.le_succ r), le_rfl⟩
    rw [(hU.2 r hrM).norm_apply_eq (hH r hrM) v (t (r + 1)) hmem, ih (by omega)]

/-- A piecewise propagator of self-adjoint pieces is a contraction on every interval. -/
theorem piecewise_norm_le {Hp : ℕ → ℝ → P →L[ℂ] P} {U : ℝ → P →L[ℂ] P}
    (h : IsMesh t M T) (hU : IsPiecewisePropagator Hp t M U)
    (hH : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hp r u) = Hp r u) :
    ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), ‖U u‖ ≤ 1 := by
  intro r hr u hu
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [(hU.2 r hr).norm_apply_eq (hH r hr) v u hu, piecewise_norm_apply h hU hH r hr.le v,
    one_mul]

/-- **The integrated sample-error certificate**:
`‖U(T) - ∏_r exp(-i (t_{r+1} - t_r) H̃_r)‖ ≤ ∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du`. -/
theorem mesh_error_integral {Hp : ℕ → ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P)
    {U : ℝ → P →L[ℂ] P} (h : IsMesh t M T) (hU : IsPiecewisePropagator Hp t M U)
    (hH : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hp r u) = Hp r u)
    (hHs : ∀ r, star (Hs r) = Hs r)
    (hint : ∀ r < M, IntervalIntegrable (Hp r) volume (t r) (t (r + 1))) :
    ‖U T - meshEvolution Hs t M‖ ≤
      ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hp r u - Hs r‖ := by
  have hE : ∀ r, ‖NormedSpace.exp ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • Hs r)‖ ≤ 1 :=
    fun r => exp_skew_norm_le (Hs r) (hHs r) _
  have htel := propagator_telescope U _ hE t (by rw [h.zero]; exact hU.1) M
  rw [h.last] at htel
  refine htel.trans (Finset.sum_le_sum fun r hr => ?_)
  have hrM := Finset.mem_range.mp hr
  exact duhamel_integral (Hs r) (h.mono (Nat.le_succ r)) (hU.2 r hrM)
    (piecewise_norm_le h hU hH r hrM) (hHs r) (hint r hrM)

/-- **Integrated certificate and refinement together**: the refined slot product of the
samples is within `∑_r ∫ ‖H_r - H̃_r‖ + M (T / N) Λ` of the piecewise propagator. -/
theorem refined_error {Hp : ℕ → ℝ → P →L[ℂ] P} (Hs : ℕ → P →L[ℂ] P)
    {U : ℝ → P →L[ℂ] P} (h : IsMesh t M T) (hT : 0 < T) (hN : 0 < N)
    (hU : IsPiecewisePropagator Hp t M U)
    (hH : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hp r u) = Hp r u)
    (hHs : ∀ r, star (Hs r) = Hs r) {Λ : ℝ} (hΛ : ∀ r, ‖Hs r‖ ≤ Λ)
    (hint : ∀ r < M, IntervalIntegrable (Hp r) volume (t r) (t (r + 1))) :
    ‖U T - refinedEvolution Hs t T N M‖ ≤
      (∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hp r u - Hs r‖) + M * (T / N) * Λ := by
  calc ‖U T - refinedEvolution Hs t T N M‖ ≤ ‖U T - meshEvolution Hs t M‖ +
        ‖meshEvolution Hs t M - refinedEvolution Hs t T N M‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      apply add_le_add (mesh_error_integral Hs h hU hH hHs hint)
      rw [norm_sub_rev]
      exact refined_evolution_sub_le Hs hHs hΛ h hT hN

/-! ### Existence -/

/-- A continuous family has a propagator from the identity on any `[a, b]`. -/
theorem exists_solvesOn_from (H : ℝ → P →L[ℂ] P) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn H (Icc a b)) : ∃ V : ℝ → P →L[ℂ] P, V a = 1 ∧ SolvesOn H V a b := by
  have hcont' : ContinuousOn (fun u => H (u + a)) (Icc 0 (b - a)) := by
    refine hcont.comp (continuous_add_const a).continuousOn ?_
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨V', hV'0, hV'⟩ := exists_solvesOn (fun u => H (u + a)) (sub_nonneg.mpr hab) hcont'
  refine ⟨fun u => V' (u - a), by simp [hV'0], ?_⟩
  intro u hu
  have hmaps : MapsTo (fun v : ℝ => v - a) (Icc a b) (Icc 0 (b - a)) := by
    intro v hv
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hmem : u - a ∈ Icc 0 (b - a) := hmaps hu
  have hg : HasDerivWithinAt (fun v : ℝ => v - a) 1 (Icc a b) u :=
    ((hasDerivAt_id' u).sub_const a).hasDerivWithinAt
  have h := (hV' (u - a) hmem).scomp u hg hmaps
  simp only [one_smul, sub_add_cancel] at h
  exact h

/-- **Existence**: continuous pieces have a piecewise propagator. -/
theorem exists_piecewise_propagator (Hp : ℕ → ℝ → P →L[ℂ] P) (ht0 : t 0 = 0)
    (hmono : Monotone t) (M : ℕ)
    (hcont : ∀ r < M, ContinuousOn (Hp r) (Icc (t r) (t (r + 1)))) :
    ∃ U : ℝ → P →L[ℂ] P, IsPiecewisePropagator Hp t M U := by
  induction M with
  | zero => exact ⟨fun _ => 1, rfl, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ M ih =>
    obtain ⟨U, hU0, hU⟩ := ih (fun r hr => hcont r (by omega))
    have hle : t M ≤ t (M + 1) := hmono (Nat.le_succ M)
    obtain ⟨V, hV0, hV⟩ := exists_solvesOn_from (Hp M) hle (hcont M (Nat.lt_succ_self M))
    let W : ℝ → P →L[ℂ] P := fun u => if u ≤ t M then U u else V u * U (t M)
    have hW0 : W 0 = 1 := by
      have h0 : (0 : ℝ) ≤ t M := by rw [← ht0]; exact hmono (Nat.zero_le M)
      simp only [W, if_pos h0, hU0]
    refine ⟨W, hW0, fun r hr => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hrM | hrM
    · -- earlier pieces lie below `t M`, where `W = U`
      have hsub : ∀ u ∈ Icc (t r) (t (r + 1)), W u = U u := by
        intro u hu
        have hu' : u ≤ t M := hu.2.trans (hmono (by omega))
        simp only [W, if_pos hu']
      intro u hu
      have h1 := (hU r hrM u hu).congr_of_mem hsub hu
      rw [hsub u hu]
      exact h1
    · subst hrM
      have hsub : ∀ u ∈ Icc (t r) (t (r + 1)), W u = V u * U (t r) := by
        intro u hu
        by_cases hle' : u ≤ t r
        · have hu' : u = t r := le_antisymm hle' hu.1
          rw [hu']
          simp [W, hV0]
        · simp only [W, if_neg hle']
      intro u hu
      have h1 := ((hV u hu).mul_const (U (t r))).congr_of_mem hsub hu
      have hval : ((-Complex.I) • (Hp r u * V u)) * U (t r) =
          (-Complex.I) • (Hp r u * W u) := by
        rw [hsub u hu]
        simp only [smul_mul_assoc, mul_assoc]
      rwa [hval] at h1

omit [CompleteSpace P] in
/-- A propagator of one path on `[0, T]` is a piecewise propagator on every mesh. -/
theorem isPiecewisePropagator_of_solvesOn {H U : ℝ → P →L[ℂ] P} (h : IsMesh t M T)
    (hU0 : U 0 = 1) (hU : SolvesOn H U 0 T) :
    IsPiecewisePropagator (fun _ => H) t M U :=
  ⟨hU0, fun r hr => hU.mono (h.nonneg r) (h.le_last (by omega))⟩

end

end TimeDependentExtensions
