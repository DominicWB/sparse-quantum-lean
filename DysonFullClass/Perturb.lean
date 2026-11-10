import GeneralSourceExtensions.Mesh.Durations
import GeneralSourceODE.Branch
import TimeDependentExtensions.ODE.Discretisation
import GeneralODE.Analysis.ExpBounds

set_option autoImplicit false

/-!
# The represented propagator against the true propagator, samples of either sign

Manuscript, proof of Lemma `odel:lem:dyson`: "Let `U` and `V` be the propagators of `A` and
`A_mesh`, respectively, and set `R = A_mesh - A`. Only `U` is known to be contractive. [...]
Substitution in the same identity bounds the propagator error by
`‖V(T,u) - U(T,u)‖ ≤ exp(∫_u^T ‖R(v)‖ dv) - 1 ≤ e^E - 1 ≤ δ`, uniformly over source start times.
This permits a represented sample whose Hermitian part is not negative semidefinite."

In the Lean convention `ẋ = -G(t) x + b(t)` (so `G = -A`), the true pieces `G_r` are accretive and
the represented generator is a constant `C_r` on mesh cell `r` (any sign of its Hermitian part).
The represented propagator from a start time `t₀` is the ordered product
`meshNodeProduct C t M t₀ = exp(-w_{M-1} C_{M-1}) ⋯ exp(-w_0 C_0)`, later cells to the left, with
the cell lengths `w_r = max(t₀, t_{r+1}) - max(t₀, t_r)` (`meshWidth`; the partial first cell for an
off-mesh start). The proof is a direct perturbation estimate, with the same constants as the
manuscript:

* `exp_norm_le_of_reLower`: if `Re ⟨w, C w⟩ ≥ -m ‖w‖²` (`m ≥ 0`), then
  `‖exp(-τ C)‖ ≤ e^{τ m}` for `τ ≥ 0`;
* `integral_exp_weight_le`: the scalar Gronwall step, `∫_a^c e^{(c-u) m} f(u) du ≤ e^{∫ f} - 1`
  whenever `m ≤ f` on `[a, c]`;
* `cell_perturb`: one cell (the variation-of-constants identity
  `y(c) - e^{-(c-a) C} y(a) = ∫_a^c e^{-(c-u) C} (C - G(u)) y(u) du` with the represented
  exponential on the left): `‖e^{-(c-a) C}‖ ≤ e^{E}` and
  `‖y(c) - e^{-(c-a) C} y(a)‖ ≤ ‖y(a)‖ (e^{E} - 1)`, `E = ∫_a^c ‖G - C‖`, for every homogeneous
  solution `y` of the accretive true equation; the numerical range of `C` is bounded below by the
  infimum of `‖G(u) - C‖` over the cell, because `G(u)` is accretive;
* `node_perturb`: the mesh, chronological composition across the breakpoints, every start time
  `t₀ ∈ [0, T]` (partial first cell included):
  `‖V(T, t₀)‖ ≤ e^{E}` and `‖y(T) - V(T, t₀) y(t₀)‖ ≤ ‖y(t₀)‖ (e^{E} - 1)` with
  `E = ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r - C_r‖` (uniform over start times);
* `propagator_perturb`: the same for the mesh propagator `U` of the true pieces
  (`Mesh.IsMeshPropagator`): `‖U(T, t₀) w - V(T, t₀) w‖ ≤ ‖w‖ (e^{E} - 1)`.

Only `U` is contractive: no positivity of the represented samples is assumed anywhere.
-/

namespace DysonFullClass

noncomputable section

open SparseHamiltonian ContinuousLinearMap Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (SolvesODE Accretive accretive_exp_norm_le_one
  hasDerivWithinAt_clm_apply)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshWidth meshWidth_nonneg meshWidth_le
  meshNodeProduct IsMeshPropagator)
open scoped BigOperators InnerProduct

/-! ### Scalar estimates -/

/-- `∫_a^c m e^{(c-u) m} du = e^{(c-a) m} - 1`. -/
theorem integral_mul_exp (a c m : ℝ) :
    ∫ u in a..c, m * Real.exp ((c - u) * m) = Real.exp ((c - a) * m) - 1 := by
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => -Real.exp ((c - u) * m))
      (m * Real.exp ((c - u) * m)) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (c - u) * m) (-m) u := by
      have h := ((hasDerivAt_id' u).const_sub c).mul_const m
      simpa only [neg_mul, one_mul] using h
    have h2 : HasDerivAt (fun u : ℝ => Real.exp ((c - u) * m)) (Real.exp ((c - u) * m) * -m) u :=
      h1.exp
    exact h2.neg.congr_deriv (by ring)
  have hcont : Continuous (fun u : ℝ => m * Real.exp ((c - u) * m)) :=
    continuous_const.mul (Real.continuous_exp.comp
      ((continuous_const.sub continuous_id).mul continuous_const))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (hcont.intervalIntegrable a c)]
  simp only [sub_self, zero_mul, Real.exp_zero]
  ring

/-- **The scalar Gronwall step**: for `m ≥ 0` and an integrable `f ≥ m` on `[a, c]`,
`∫_a^c e^{(c-u) m} f(u) du ≤ e^{∫_a^c f} - 1`. -/
theorem integral_exp_weight_le {f : ℝ → ℝ} {a c m : ℝ} (hac : a ≤ c) (hm : 0 ≤ m)
    (hf : IntervalIntegrable f volume a c) (hmf : ∀ u ∈ Icc a c, m ≤ f u) :
    ∫ u in a..c, Real.exp ((c - u) * m) * f u ≤ Real.exp (∫ u in a..c, f u) - 1 := by
  have hcont : Continuous (fun u : ℝ => Real.exp ((c - u) * m)) :=
    Real.continuous_exp.comp ((continuous_const.sub continuous_id).mul continuous_const)
  have hint1 : IntervalIntegrable (fun u => Real.exp ((c - u) * m) * f u) volume a c :=
    hf.continuousOn_mul hcont.continuousOn
  have hint2 : IntervalIntegrable (fun u => m * Real.exp ((c - u) * m)) volume a c :=
    (continuous_const.mul hcont).intervalIntegrable a c
  have hint3 : IntervalIntegrable (fun u => Real.exp ((c - a) * m) * (f u - m)) volume a c :=
    (hf.sub intervalIntegrable_const).const_mul _
  have hpt : ∀ u ∈ Icc a c, Real.exp ((c - u) * m) * f u ≤
      m * Real.exp ((c - u) * m) + Real.exp ((c - a) * m) * (f u - m) := by
    intro u hu
    have hexp : Real.exp ((c - u) * m) ≤ Real.exp ((c - a) * m) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [hu.1]) hm)
    have hfm : 0 ≤ f u - m := sub_nonneg.mpr (hmf u hu)
    have h := mul_le_mul_of_nonneg_right hexp hfm
    nlinarith
  have hF : (c - a) * m ≤ ∫ u in a..c, f u := by
    have h := intervalIntegral.integral_mono_on hac intervalIntegrable_const hf hmf
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have hsum : ∫ u in a..c, (m * Real.exp ((c - u) * m) + Real.exp ((c - a) * m) * (f u - m)) =
      (Real.exp ((c - a) * m) - 1) +
        Real.exp ((c - a) * m) * ((∫ u in a..c, f u) - (c - a) * m) := by
    rw [intervalIntegral.integral_add hint2 hint3, integral_mul_exp,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hf intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  have hmono := intervalIntegral.integral_mono_on hac hint1 (hint2.add hint3) hpt
  rw [hsum] at hmono
  refine hmono.trans ?_
  set x := (c - a) * m
  set F := ∫ u in a..c, f u
  have hy : 1 + (F - x) ≤ Real.exp (F - x) := by
    have := Real.add_one_le_exp (F - x)
    linarith
  have hex : Real.exp x * Real.exp (F - x) = Real.exp F := by
    rw [← Real.exp_add]; ring_nf
  have hpos := Real.exp_pos x
  nlinarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### The exponential of a generator whose numerical range is bounded below -/

omit [CompleteSpace V] in
/-- Shifting by `m` makes a generator with `Re ⟨w, C w⟩ ≥ -m ‖w‖²` accretive. -/
theorem accretive_add_smul_one {C : V →L[ℂ] V} {m : ℝ}
    (hC : ∀ w : V, -(m * ‖w‖ ^ 2) ≤ (inner ℂ w (C w)).re) :
    Accretive (C + (m : ℂ) • (1 : V →L[ℂ] V)) := by
  intro w
  have h := hC w
  have hww : (inner ℂ w w : ℂ).re = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hre : (inner ℂ w ((C + (m : ℂ) • (1 : V →L[ℂ] V)) w)).re =
      (inner ℂ w (C w)).re + m * ‖w‖ ^ 2 := by
    rw [add_apply, smul_apply, one_apply_eq_self, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.re_ofReal_mul, hww]
  rw [hre]
  linarith

/-- **The exponential of a generator of either sign**: if `Re ⟨w, C w⟩ ≥ -m ‖w‖²` with `m ≥ 0`,
then `‖exp(-τ C)‖ ≤ e^{τ m}` for every `τ ≥ 0`. -/
theorem exp_norm_le_of_reLower (C : V →L[ℂ] V) {m : ℝ} (hm : 0 ≤ m)
    (hC : ∀ w : V, -(m * ‖w‖ ^ 2) ≤ (inner ℂ w (C w)).re) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖NormedSpace.exp (τ • (-C))‖ ≤ Real.exp (τ * m) := by
  set A : V →L[ℂ] V := C + (m : ℂ) • (1 : V →L[ℂ] V) with hAdef
  have hA : Accretive A := accretive_add_smul_one hC
  set Y : V →L[ℂ] V := ((τ * m : ℝ) : ℂ) • (1 : V →L[ℂ] V) with hYdef
  have hsplit : τ • (-C) = τ • (-A) + Y := by
    have h1 : τ • ((m : ℂ) • (1 : V →L[ℂ] V)) = Y := by
      rw [hYdef, ← Complex.coe_smul, smul_smul]
      push_cast
      ring_nf
    rw [hAdef, neg_add, smul_add]
    simp only [smul_neg]
    rw [h1]
    abel
  have hcomm : Commute (τ • (-A)) Y := (Commute.one_right _).smul_right _
  have hY : ‖Y‖ ≤ τ * m := by
    rw [hYdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hτ hm)]
    exact mul_le_of_le_one_right (mul_nonneg hτ hm) ContinuousLinearMap.norm_id_le
  rcases subsingleton_or_nontrivial V with hV | hV
  · have h0 : NormedSpace.exp (τ • (-C)) = 0 :=
      ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _
    rw [h0, norm_zero]
    exact (Real.exp_pos _).le
  rw [hsplit, TimeDependentExtensions.exp_add_commute _ _ hcomm]
  calc ‖NormedSpace.exp (τ • (-A)) * NormedSpace.exp Y‖
      ≤ ‖NormedSpace.exp (τ • (-A))‖ * ‖NormedSpace.exp Y‖ := norm_mul_le _ _
    _ ≤ 1 * Real.exp (τ * m) :=
        mul_le_mul (accretive_exp_norm_le_one A hA τ hτ)
          ((SparseHamiltonian.GeneralODE.ExpBounds.norm_exp_le Y).trans (Real.exp_le_exp.mpr hY))
          (norm_nonneg _) zero_le_one
    _ = Real.exp (τ * m) := one_mul _

/-! ### One cell -/

omit [CompleteSpace V] in
/-- On a cell where the true generator is accretive, the numerical range of any constant `C` is
bounded below by `-inf_u ‖G(u) - C‖`. -/
theorem reLower_of_accretive {G : ℝ → V →L[ℂ] V} {a c : ℝ} (hac : a ≤ c)
    (hG : ∀ u ∈ Icc a c, Accretive (G u)) (C : V →L[ℂ] V) :
    ∀ w : V, -(sInf ((fun u => ‖G u - C‖) '' Icc a c) * ‖w‖ ^ 2) ≤ (inner ℂ w (C w)).re := by
  intro w
  have hne : ((fun u => ‖G u - C‖) '' Icc a c).Nonempty := ⟨_, a, ⟨le_rfl, hac⟩, rfl⟩
  have hpt : ∀ u ∈ Icc a c, -(inner ℂ w (C w)).re ≤ ‖G u - C‖ * ‖w‖ ^ 2 := by
    intro u hu
    have hacc := hG u hu w
    have hsplit : (inner ℂ w (C w)).re =
        (inner ℂ w (G u w)).re - (inner ℂ w ((G u - C) w)).re := by
      rw [sub_apply, inner_sub_right, Complex.sub_re]
      ring
    have hb : (inner ℂ w ((G u - C) w)).re ≤ ‖G u - C‖ * ‖w‖ ^ 2 := by
      calc (inner ℂ w ((G u - C) w)).re ≤ ‖inner ℂ w ((G u - C) w)‖ := Complex.re_le_norm _
        _ ≤ ‖w‖ * ‖(G u - C) w‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖G u - C‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
        _ = ‖G u - C‖ * ‖w‖ ^ 2 := by ring
    linarith
  rcases eq_or_lt_of_le (sq_nonneg ‖w‖) with h0 | hpos
  · have hw : w = 0 := by
      have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
      exact norm_eq_zero.mp this
    subst hw
    simp
  · have hle : -(inner ℂ w (C w)).re / ‖w‖ ^ 2 ≤
        sInf ((fun u => ‖G u - C‖) '' Icc a c) := by
      refine le_csInf hne ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [div_le_iff₀ hpos]
      exact hpt u hu
    rw [div_le_iff₀ hpos] at hle
    linarith

/-- **One cell, represented sample of either sign** (proof of Lemma `odel:lem:dyson`): for a
homogeneous solution `y` of the accretive true equation `y' = -G(u) y` on `[a, c]` and any constant
generator `C`, with `E = ∫_a^c ‖G - C‖`,
`‖exp(-(c-a) C)‖ ≤ e^{E}` and `‖y(c) - exp(-(c-a) C) y(a)‖ ≤ ‖y(a)‖ (e^{E} - 1)`. -/
theorem cell_perturb {G : ℝ → V →L[ℂ] V} {y : ℝ → V} {a c : ℝ}
    (hy : SolvesODE G 0 y a c) (hac : a ≤ c) (hG : ∀ u ∈ Icc a c, Accretive (G u))
    (hGint : IntervalIntegrable G volume a c) (C : V →L[ℂ] V) :
    ‖NormedSpace.exp ((c - a) • (-C))‖ ≤ Real.exp (∫ u in a..c, ‖G u - C‖) ∧
      ‖y c - NormedSpace.exp ((c - a) • (-C)) (y a)‖ ≤
        ‖y a‖ * (Real.exp (∫ u in a..c, ‖G u - C‖) - 1) := by
  set f : ℝ → ℝ := fun u => ‖G u - C‖ with hfdef
  have hfint : IntervalIntegrable f volume a c := (hGint.sub intervalIntegrable_const).norm
  set m : ℝ := sInf (f '' Icc a c) with hmdef
  have hne : (f '' Icc a c).Nonempty := ⟨_, a, ⟨le_rfl, hac⟩, rfl⟩
  have hbdd : BddBelow (f '' Icc a c) := ⟨0, by rintro _ ⟨u, -, rfl⟩; exact norm_nonneg _⟩
  have hm0 : 0 ≤ m := le_csInf hne (by rintro _ ⟨u, -, rfl⟩; exact norm_nonneg _)
  have hmf : ∀ u ∈ Icc a c, m ≤ f u := fun u hu => csInf_le hbdd ⟨u, hu, rfl⟩
  have hC : ∀ w : V, -(m * ‖w‖ ^ 2) ≤ (inner ℂ w (C w)).re := reLower_of_accretive hac hG C
  have hmF : (c - a) * m ≤ ∫ u in a..c, f u := by
    have h := intervalIntegral.integral_mono_on hac intervalIntegrable_const hfint hmf
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have hEn : ∀ τ, 0 ≤ τ → ‖NormedSpace.exp (τ • (-C))‖ ≤ Real.exp (τ * m) :=
    fun τ hτ => exp_norm_le_of_reLower C hm0 hC hτ
  refine ⟨(hEn (c - a) (sub_nonneg.mpr hac)).trans (Real.exp_le_exp.mpr hmF), ?_⟩
  -- the variation-of-constants identity with the represented exponential on the left
  let E : ℝ → V →L[ℂ] V := fun u => NormedSpace.exp ((c - u) • (-C))
  have hE : ∀ u, HasDerivAt E (E u * C) u := by
    intro u
    have hlin : HasDerivAt (fun v : ℝ => c - v) (-1) u := (hasDerivAt_id' u).const_sub c
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-C) (c - u)).scomp u hlin
    simpa only [Function.comp_def, neg_one_smul, mul_neg, neg_neg] using h
  have hEcont : Continuous E := continuous_iff_continuousAt.2 fun u => (hE u).continuousAt
  let ψ : ℝ → V := fun u => E u (y u)
  let ψ' : ℝ → V := fun u => (E u * C) (y u) + E u (-(G u (y u)) + (0 : ℝ → V) u)
  have hψ : ∀ u ∈ Icc a c, HasDerivWithinAt ψ (ψ' u) (Icc a c) u := fun u hu =>
    hasDerivWithinAt_clm_apply (hE u).hasDerivWithinAt (hy u hu)
  have hyc : ContinuousOn y (Icc a c) := hy.continuousOn
  have hψcont : ContinuousOn ψ (Icc a c) := fun u hu => (hψ u hu).continuousWithinAt
  have hψ'int : IntervalIntegrable ψ' volume a c := by
    have h1 : IntervalIntegrable (fun u => (E u * C) (y u)) volume a c :=
      ContinuousOn.intervalIntegrable_of_Icc hac
        ((hEcont.mul continuous_const).continuousOn.clm_apply hyc)
    have h2 : IntervalIntegrable (fun u => E u (-(G u (y u)) + (0 : ℝ → V) u)) volume a c := by
      have h3 := TimeDependentExtensions.ODEMesh.intervalIntegrable_apply_left hac
        hEcont.continuousOn
        ((TimeDependentExtensions.ODEMesh.intervalIntegrable_apply_right hac hGint hyc).neg.add
          (intervalIntegrable_const (c := (0 : V))))
      simpa only [Pi.zero_apply, Pi.neg_apply] using h3
    exact h1.add h2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hac hψcont
    (fun u hu => ((hψ u (Ioo_subset_Icc_self hu)).hasDerivAt
      (Icc_mem_nhds hu.1 hu.2)).hasDerivWithinAt) hψ'int
  have hψc : ψ c = y c := by
    simp only [ψ, E, sub_self, zero_smul, NormedSpace.exp_zero, one_apply_eq_self]
  have hψa : ψ a = NormedSpace.exp ((c - a) • (-C)) (y a) := rfl
  have hya : ∀ u ∈ Icc a c, ‖y u‖ ≤ ‖y a‖ := GeneralSourceODE.homogeneous_norm_le hy hG
  have hbound : ∀ u ∈ Icc a c, ‖ψ' u‖ ≤ Real.exp ((c - u) * m) * f u * ‖y a‖ := by
    intro u hu
    have hrw : ψ' u = E u ((C - G u) (y u)) := by
      simp only [ψ', mul_apply_eq_comp, Pi.zero_apply, add_zero, sub_apply, map_sub, map_neg]
      abel
    rw [hrw]
    calc ‖E u ((C - G u) (y u))‖ ≤ ‖E u‖ * (‖C - G u‖ * ‖y u‖) :=
          (le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _))
      _ ≤ Real.exp ((c - u) * m) * (f u * ‖y a‖) := by
          refine mul_le_mul (hEn (c - u) (by linarith [hu.2])) ?_ (by positivity)
            (Real.exp_pos _).le
          rw [norm_sub_rev]
          exact mul_le_mul_of_nonneg_left (hya u hu) (norm_nonneg _)
      _ = Real.exp ((c - u) * m) * f u * ‖y a‖ := by ring
  have hcont : Continuous (fun u : ℝ => Real.exp ((c - u) * m)) :=
    Real.continuous_exp.comp ((continuous_const.sub continuous_id).mul continuous_const)
  have hwint : IntervalIntegrable (fun u => Real.exp ((c - u) * m) * f u * ‖y a‖) volume a c :=
    (hfint.continuousOn_mul hcont.continuousOn).mul_const _
  have hscalar := integral_exp_weight_le hac hm0 hfint hmf
  calc ‖y c - NormedSpace.exp ((c - a) • (-C)) (y a)‖ = ‖ψ c - ψ a‖ := by rw [hψc, hψa]
    _ = ‖∫ u in a..c, ψ' u‖ := by rw [hFTC]
    _ ≤ ∫ u in a..c, ‖ψ' u‖ := intervalIntegral.norm_integral_le_integral_norm hac
    _ ≤ ∫ u in a..c, Real.exp ((c - u) * m) * f u * ‖y a‖ :=
        intervalIntegral.integral_mono_on hac hψ'int.norm hwint hbound
    _ = (∫ u in a..c, Real.exp ((c - u) * m) * f u) * ‖y a‖ := intervalIntegral.integral_mul_const _ _
    _ ≤ (Real.exp (∫ u in a..c, f u) - 1) * ‖y a‖ :=
        mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
    _ = ‖y a‖ * (Real.exp (∫ u in a..c, ‖G u - C‖) - 1) := by rw [mul_comm]

/-! ### The mesh: chronological composition across the breakpoints -/

variable {t : ℕ → ℝ} {M : ℕ} {T : ℝ}

set_option maxHeartbeats 2000000 in
/-- **The represented propagator from any start time** (proof of Lemma `odel:lem:dyson`, samples
of either sign): for accretive integrable true pieces `Gq r`, any constant represented generators
`Cs r`, every start time `t₀ ∈ [0, T]` and every homogeneous solution `y` from `t₀`, with
`E = ∑_{r<M} ∫_{t_r}^{t_{r+1}} ‖Gq r - Cs r‖`,
`‖meshNodeProduct Cs t M t₀‖ ≤ e^{E}` and `‖y(T) - meshNodeProduct Cs t M t₀ (y t₀)‖ ≤
‖y(t₀)‖ (e^{E} - 1)`. -/
theorem node_perturb (hmesh : IsMesh t M T) (Gq : ℕ → ℝ → V →L[ℂ] V)
    (hG : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (Gq r u))
    (hGint : ∀ r < M, IntervalIntegrable (Gq r) volume (t r) (t (r + 1)))
    (Cs : ℕ → V →L[ℂ] V) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (y : ℝ → V)
    (hsol : ∀ r < M, t₀ ≤ t (r + 1) → SolvesODE (Gq r) 0 y (max t₀ (t r)) (t (r + 1))) :
    ‖meshNodeProduct Cs t M t₀‖ ≤
        Real.exp (∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖) ∧
      ‖y T - meshNodeProduct Cs t M t₀ (y t₀)‖ ≤
        ‖y t₀‖ * (Real.exp (∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖) - 1) := by
  have hle : ∀ r, t r ≤ t (r + 1) := fun r => hmesh.mono (Nat.le_succ r)
  have hI0 : ∀ r, 0 ≤ ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖ := fun r =>
    intervalIntegral.integral_nonneg (hle r) (fun u _ => norm_nonneg _)
  -- the factor bound and the one-cell estimate on the part of cell `m` after `t₀`
  have hfactor : ∀ m < M,
      ‖NormedSpace.exp (meshWidth t₀ t m • (-Cs m))‖ ≤
          Real.exp (∫ u in t m..t (m + 1), ‖Gq m u - Cs m‖) ∧
        (t₀ ≤ t (m + 1) →
          ‖y (max t₀ (t (m + 1))) - NormedSpace.exp (meshWidth t₀ t m • (-Cs m)) (y (max t₀ (t m)))‖ ≤
            ‖y (max t₀ (t m))‖ * (Real.exp (∫ u in t m..t (m + 1), ‖Gq m u - Cs m‖) - 1)) := by
    intro m hmM
    by_cases hst : t₀ ≤ t (m + 1)
    · set a := max t₀ (t m) with ha
      set c := max t₀ (t (m + 1)) with hc
      have hcm : c = t (m + 1) := max_eq_right hst
      have hac : a ≤ c := max_le_max le_rfl (hle m)
      have hsolm := hsol m hmM hst
      rw [← ha, ← hcm] at hsolm
      have hGm : ∀ u ∈ Icc a c, Accretive (Gq m u) := fun u hu =>
        hG m hmM u ⟨(le_max_right t₀ (t m)).trans hu.1, hcm ▸ hu.2⟩
      have hint : IntervalIntegrable (Gq m) volume a c := by
        refine (hGint m hmM).mono_set ?_
        rw [uIcc_of_le hac, uIcc_of_le (hle m)]
        exact Icc_subset_Icc (le_max_right _ _) (le_of_eq hcm)
      obtain ⟨h1, h2⟩ := cell_perturb hsolm hac hGm hint (Cs m)
      have hmono : ∫ u in a..c, ‖Gq m u - Cs m‖ ≤ ∫ u in t m..t (m + 1), ‖Gq m u - Cs m‖ :=
        intervalIntegral.integral_mono_interval (le_max_right _ _) hac (le_of_eq hcm)
          (Filter.Eventually.of_forall fun u => norm_nonneg _)
          (((hGint m hmM).sub intervalIntegrable_const).norm)
      have hwidth : c - a = meshWidth t₀ t m := rfl
      rw [hwidth] at h1 h2
      refine ⟨h1.trans (Real.exp_le_exp.mpr hmono), fun _ => h2.trans ?_⟩
      exact mul_le_mul_of_nonneg_left (by linarith [Real.exp_le_exp.mpr hmono]) (norm_nonneg _)
    · push Not at hst
      have hw0 : meshWidth t₀ t m = 0 := by
        change max t₀ (t (m + 1)) - max t₀ (t m) = 0
        rw [max_eq_left hst.le, max_eq_left ((hle m).trans hst.le), sub_self]
      refine ⟨?_, fun h => absurd h (not_le.mpr hst)⟩
      rw [hw0, zero_smul, NormedSpace.exp_zero]
      exact ContinuousLinearMap.norm_id_le.trans (Real.one_le_exp (hI0 m))
  have hstep : ∀ m ≤ M,
      ‖TimeDependent.evolution (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Cs r))) m‖ ≤
          Real.exp (∑ r ∈ Finset.range m, ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖) ∧
        ‖y (max t₀ (t m)) -
            TimeDependent.evolution (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Cs r))) m
              (y t₀)‖ ≤
          ‖y t₀‖ * (Real.exp (∑ r ∈ Finset.range m, ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖) - 1) ∧
        ‖y (max t₀ (t m))‖ ≤ ‖y t₀‖ := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [hmesh.zero, max_eq_left ht₀.1, TimeDependent.evolution_zero, one_apply_eq_self,
          sub_self, norm_zero, Finset.sum_range_zero, Real.exp_zero, sub_self, mul_zero]
        exact ⟨ContinuousLinearMap.norm_id_le, le_rfl, le_rfl⟩
    | succ m ih =>
        intro hm
        have hmM : m < M := by omega
        obtain ⟨ih0, ih1, ih2⟩ := ih hmM.le
        obtain ⟨hF1, hF2⟩ := hfactor m hmM
        set S := ∑ r ∈ Finset.range m, ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖ with hS
        set I := ∫ u in t m..t (m + 1), ‖Gq m u - Cs m‖ with hI
        have hS0 : 0 ≤ S := Finset.sum_nonneg fun r _ => hI0 r
        have hexpS : 1 ≤ Real.exp S := Real.one_le_exp hS0
        have hexpI : 1 ≤ Real.exp I := Real.one_le_exp (hI0 m)
        have hexpadd : Real.exp (S + I) = Real.exp S * Real.exp I := Real.exp_add S I
        rw [TimeDependent.evolution_succ, mul_apply_eq_comp, Finset.sum_range_succ, ← hS, ← hI,
          hexpadd]
        refine ⟨?_, ?_⟩
        · calc ‖NormedSpace.exp (meshWidth t₀ t m • (-Cs m)) *
                TimeDependent.evolution (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Cs r))) m‖
              ≤ ‖NormedSpace.exp (meshWidth t₀ t m • (-Cs m))‖ *
                  ‖TimeDependent.evolution
                    (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Cs r))) m‖ := norm_mul_le _ _
            _ ≤ Real.exp I * Real.exp S :=
                mul_le_mul hF1 ih0 (norm_nonneg _) (Real.exp_pos _).le
            _ = Real.exp S * Real.exp I := mul_comm _ _
        by_cases hst : t₀ ≤ t (m + 1)
        · have h2 := hF2 hst
          set a := max t₀ (t m)
          set c := max t₀ (t (m + 1))
          have hcm : c = t (m + 1) := max_eq_right hst
          have hac : a ≤ c := max_le_max le_rfl (hle m)
          have hsolm := hsol m hmM hst
          have hGm : ∀ u ∈ Icc a c, Accretive (Gq m u) := fun u hu =>
            hG m hmM u ⟨(le_max_right t₀ (t m)).trans hu.1, hcm ▸ hu.2⟩
          have hsolm' : SolvesODE (Gq m) 0 y a c := by rw [hcm]; exact hsolm
          have hnorm : ‖y c‖ ≤ ‖y t₀‖ :=
            (GeneralSourceODE.homogeneous_norm_le hsolm' hGm c ⟨hac, le_rfl⟩).trans ih2
          have hsplit : y c - NormedSpace.exp (meshWidth t₀ t m • (-Cs m))
              (TimeDependent.evolution (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Cs r))) m
                (y t₀)) =
              (y c - NormedSpace.exp (meshWidth t₀ t m • (-Cs m)) (y a)) +
                NormedSpace.exp (meshWidth t₀ t m • (-Cs m))
                  (y a - TimeDependent.evolution
                    (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Cs r))) m (y t₀)) := by
            rw [map_sub]
            abel
          refine ⟨?_, hnorm⟩
          rw [hsplit]
          calc _ ≤ ‖y c - NormedSpace.exp (meshWidth t₀ t m • (-Cs m)) (y a)‖ +
                ‖NormedSpace.exp (meshWidth t₀ t m • (-Cs m))‖ *
                  ‖y a - TimeDependent.evolution
                    (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Cs r))) m (y t₀)‖ :=
                (norm_add_le _ _).trans (add_le_add le_rfl (le_opNorm _ _))
            _ ≤ ‖y a‖ * (Real.exp I - 1) + Real.exp I * (‖y t₀‖ * (Real.exp S - 1)) :=
                add_le_add h2 (mul_le_mul hF1 ih1 (norm_nonneg _) (Real.exp_pos _).le)
            _ ≤ ‖y t₀‖ * (Real.exp I - 1) + Real.exp I * (‖y t₀‖ * (Real.exp S - 1)) :=
                add_le_add (mul_le_mul_of_nonneg_right ih2 (by linarith)) le_rfl
            _ = ‖y t₀‖ * (Real.exp S * Real.exp I - 1) := by ring
        · push Not at hst
          have hw0 : meshWidth t₀ t m = 0 := by
            change max t₀ (t (m + 1)) - max t₀ (t m) = 0
            rw [max_eq_left hst.le, max_eq_left ((hle m).trans hst.le), sub_self]
          have hcm : max t₀ (t (m + 1)) = t₀ := max_eq_left hst.le
          have ham : max t₀ (t m) = t₀ := max_eq_left ((hle m).trans hst.le)
          rw [hw0, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, hcm]
          rw [ham] at ih1
          refine ⟨ih1.trans ?_, le_rfl⟩
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          nlinarith
  obtain ⟨h0, h1, -⟩ := hstep M le_rfl
  rw [hmesh.last, max_eq_right ht₀.2] at h1
  exact ⟨h0, h1⟩

/-- **The mesh propagator against the represented propagator, every start time** (proof of Lemma
`odel:lem:dyson`): for the propagator `U` of accretive integrable true pieces `G r`
(`Mesh.IsMeshPropagator`, classical on every closed cell) and constant represented generators
`C r` of either sign, with `E = ∑_r ∫_{t_r}^{t_{r+1}} ‖G r - C r‖`, for every `t₀ ∈ [0, T]` and
every `w`: `‖U(T, t₀) w - V(T, t₀) w‖ ≤ ‖w‖ (e^{E} - 1)`, `V(T, t₀) = meshNodeProduct` of the
cell generators. -/
theorem propagator_perturb (hmesh : IsMesh t M T) (G : Fin M → ℝ → V →L[ℂ] V)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (U : ℝ → V → ℝ → V) (hU : IsMeshPropagator G t T U)
    (Cs : ℕ → V →L[ℂ] V) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (w : V) :
    ‖meshNodeProduct Cs t M t₀‖ ≤
        Real.exp (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖G r u - Cs r‖) ∧
      ‖U t₀ w T - meshNodeProduct Cs t M t₀ w‖ ≤
        ‖w‖ * (Real.exp (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖G r u - Cs r‖) - 1) := by
  classical
  let Gq : ℕ → ℝ → V →L[ℂ] V := fun r => if h : r < M then G ⟨r, h⟩ else 0
  have hGq : ∀ r (h : r < M), Gq r = G ⟨r, h⟩ := fun r h => by simp only [Gq, dif_pos h]
  have hGacc : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (Gq r u) := by
    intro r hr u hu
    rw [hGq r hr]
    exact hG ⟨r, hr⟩ u hu
  have hGqint : ∀ r < M, IntervalIntegrable (Gq r) volume (t r) (t (r + 1)) := by
    intro r hr
    rw [hGq r hr]
    exact hGint ⟨r, hr⟩
  obtain ⟨h0, hsol⟩ := hU t₀ ht₀ w
  have hsolq : ∀ r < M, t₀ ≤ t (r + 1) → SolvesODE (Gq r) 0 (U t₀ w) (max t₀ (t r)) (t (r + 1)) := by
    intro r hr hst
    rw [hGq r hr]
    exact hsol ⟨r, hr⟩ hst
  have hSum : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖ =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖G r u - Cs r‖ := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Gq r u - Cs r‖) M]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hGq r r.isLt]
  have hN := node_perturb hmesh Gq hGacc hGqint Cs ht₀ (U t₀ w) hsolq
  rw [h0, hSum] at hN
  exact hN

end

end DysonFullClass
