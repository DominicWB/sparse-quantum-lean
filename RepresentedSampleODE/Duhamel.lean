import GeneralSourceExtensions.Mesh.Duhamel

/-!
# Duhamel's formula on a mesh for bounded pieces

`GeneralSourceExtensions.Mesh.mesh_duhamel` proves Duhamel's formula on a mesh for continuous
generator and forcing pieces. Continuity is used there only to bound the generator pieces and to
make the propagated forcing integrable. Here the formula is proved for **bounded** generator pieces
(`‖G_r(u)‖ ≤ Λ_r`) and an **integrable propagated forcing** `v ↦ U(T, v) b_r(v)` on every mesh
interval, which the manuscript's certificate on the propagated vector integral presupposes:

  `∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv = x(T) - U(T, 0) x(0)`   (`mesh_duhamel_bounded`).

* `mesh_move_le`: on a piece, `‖U(u, v) w - w‖ ≤ Λ ‖w‖ (u - v)`;
* `propagated_sub_le`, `propagated_continuousOn`: for `g` continuous on a piece, `v ↦ U(T, v) g(v)`
  is continuous there;
* `duhamel_right_deriv`: the right derivative of `v ↦ U(T, v) x(v)` is `U(T, v) b(v)`;
* `piece_duhamel_bounded`, `mesh_duhamel_bounded`;
* `continuous_pieces_regular`: continuous generator and forcing pieces satisfy the hypotheses
  (bounded, integrable generator pieces and an integrable propagated forcing).
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory Filter Topology Asymptotics
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (IsMeshPropagator endMap endMap_apply)
open scoped BigOperators InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {t : ℕ → ℝ} {M : ℕ} {T : ℝ} {G : Fin M → ℝ → V →L[ℂ] V} {U : ℝ → V → ℝ → V}

theorem piece_le_last (hmesh : IsMesh t M T) (r : Fin M) : t ((r : ℕ) + 1) ≤ T :=
  hmesh.le_last (Nat.succ_le_of_lt r.isLt)

theorem piece_mem (hmesh : IsMesh t M T) (r : Fin M) {v : ℝ}
    (hv : v ∈ Icc (t r) (t ((r : ℕ) + 1))) : v ∈ Icc 0 T :=
  ⟨(hmesh.nonneg r).trans hv.1, hv.2.trans (piece_le_last hmesh r)⟩

/-- On a piece, a propagated vector moves by at most `Λ ‖w‖ (u - v)`. -/
theorem mesh_move_le (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (r : Fin M) {Λ : ℝ} (hΛ : ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ)
    {v : ℝ} (hv : v ∈ Icc (t r) (t ((r : ℕ) + 1))) (w : V) :
    ∀ u ∈ Icc v (t ((r : ℕ) + 1)), ‖U v w u - w‖ ≤ Λ * ‖w‖ * (u - v) := by
  have hv0 := piece_mem hmesh r hv
  have hc := piece_le_last hmesh r
  obtain ⟨h0, hsol⟩ := hU v hv0 w
  have hs := hsol r hv.2
  rw [max_eq_left hv.1] at hs
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ v hv)
  intro u hu
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := U v w)
    (f' := fun x => -(G r x (U v w x)) + (0 : ℝ → V) x) hs (C := Λ * ‖w‖) ?_ u hu
  · rwa [h0] at key
  · intro x hx
    have hxI : x ∈ Icc (t r) (t ((r : ℕ) + 1)) := ⟨hv.1.trans hx.1, hx.2.le⟩
    have hn := hU.norm_le hmesh hG hv0 w x ⟨hx.1, hx.2.le.trans hc⟩
    simp only [Pi.zero_apply, add_zero, norm_neg]
    calc ‖G r x (U v w x)‖ ≤ ‖G r x‖ * ‖U v w x‖ := le_opNorm _ _
      _ ≤ Λ * ‖w‖ := mul_le_mul (hΛ x hxI) hn (norm_nonneg _) hΛ0

/-- The propagation to the final time is a contraction. -/
theorem endMap_norm_le (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    {c : ℝ} (hc : c ∈ Icc 0 T) : ‖endMap hmesh hU hG hc‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul, endMap_apply]
    exact hU.norm_le hmesh hG hc w T ⟨hc.2, le_rfl⟩

/-- The propagation to the final time moves by at most `‖g(v₂) - g(v₁)‖ + Λ ‖g(v₁)‖ (v₂ - v₁)`. -/
theorem propagated_sub_le (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (r : Fin M) {Λ : ℝ} (hΛ : ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ) (g : ℝ → V)
    {v₁ v₂ : ℝ} (h₁ : v₁ ∈ Icc (t r) (t ((r : ℕ) + 1))) (h₂ : v₂ ∈ Icc (t r) (t ((r : ℕ) + 1)))
    (h12 : v₁ ≤ v₂) :
    ‖U v₂ (g v₂) T - U v₁ (g v₁) T‖ ≤ ‖g v₂ - g v₁‖ + Λ * ‖g v₁‖ * (v₂ - v₁) := by
  have hc := piece_le_last hmesh r
  have h₁0 := piece_mem hmesh r h₁
  have h₂0 := piece_mem hmesh r h₂
  have hcoc := hU.cocycle hmesh hG h₁0 h12 h₂0.2 (g v₁) T ⟨h₂0.2, le_rfl⟩
  have e : U v₂ (g v₂) T - U v₁ (g v₁) T = endMap hmesh hU hG h₂0 (g v₂ - U v₁ (g v₁) v₂) := by
    rw [hcoc, map_sub, endMap_apply, endMap_apply]
  have hE := endMap_norm_le hmesh hU hG h₂0
  rw [e]
  calc ‖endMap hmesh hU hG h₂0 (g v₂ - U v₁ (g v₁) v₂)‖
      ≤ ‖endMap hmesh hU hG h₂0‖ * ‖g v₂ - U v₁ (g v₁) v₂‖ := le_opNorm _ _
    _ ≤ 1 * ‖g v₂ - U v₁ (g v₁) v₂‖ := mul_le_mul_of_nonneg_right hE (norm_nonneg _)
    _ = ‖(g v₂ - g v₁) - (U v₁ (g v₁) v₂ - g v₁)‖ := by rw [one_mul]; congr 1; abel
    _ ≤ ‖g v₂ - g v₁‖ + ‖U v₁ (g v₁) v₂ - g v₁‖ := norm_sub_le _ _
    _ ≤ ‖g v₂ - g v₁‖ + Λ * ‖g v₁‖ * (v₂ - v₁) :=
        add_le_add le_rfl (mesh_move_le hmesh hU hG r hΛ h₁ (g v₁) v₂ ⟨h12, h₂.2⟩)

/-- For `g` continuous on a piece, the propagation `v ↦ U(T, v) g(v)` is continuous there. -/
theorem propagated_continuousOn (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (r : Fin M) {Λ : ℝ} (hΛ : ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ) (g : ℝ → V)
    (hg : ContinuousOn g (Icc (t r) (t ((r : ℕ) + 1)))) :
    ContinuousOn (fun v => U v (g v) T) (Icc (t r) (t ((r : ℕ) + 1))) := by
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ x hx)
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS x hx)
  obtain ⟨δ₁, hδ₁, hg₁⟩ := Metric.continuousOn_iff.mp hg x hx (ε / 2) (half_pos hε)
  have hK : 0 < Λ * S + 1 := by have := mul_nonneg hΛ0 hS0; linarith
  refine ⟨min δ₁ (ε / (2 * (Λ * S + 1))), lt_min hδ₁ (by positivity), ?_⟩
  intro y hy hdist
  have hd₁ : dist y x < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd₂ : |y - x| < ε / (2 * (Λ * S + 1)) := by
    rw [← Real.dist_eq]
    exact lt_of_lt_of_le hdist (min_le_right _ _)
  have hgy : ‖g y - g x‖ < ε / 2 := by
    rw [← dist_eq_norm]
    exact hg₁ y hy hd₁
  have hlin : Λ * S * |y - x| < ε / 2 := by
    have h1 : Λ * S * |y - x| ≤ (Λ * S + 1) * |y - x| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have h2 : (Λ * S + 1) * |y - x| < (Λ * S + 1) * (ε / (2 * (Λ * S + 1))) :=
      mul_lt_mul_of_pos_left hd₂ hK
    have h3 : (Λ * S + 1) * (ε / (2 * (Λ * S + 1))) = ε / 2 := by
      field_simp
    linarith
  rw [dist_eq_norm]
  rcases le_total x y with h | h
  · have hm := propagated_sub_le hmesh hU hG r hΛ g hx hy h
    have hb : Λ * ‖g x‖ * (y - x) ≤ Λ * S * |y - x| := by
      rw [abs_of_nonneg (sub_nonneg.mpr h)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hS x hx) hΛ0)
        (sub_nonneg.mpr h)
    linarith
  · have hm := propagated_sub_le hmesh hU hG r hΛ g hy hx h
    rw [norm_sub_rev] at hm
    rw [norm_sub_rev] at hgy
    have hb : Λ * ‖g y‖ * (x - y) ≤ Λ * S * |y - x| := by
      rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hS y hy) hΛ0)
        (sub_nonneg.mpr h)
    linarith

/-- **The right derivative of the Duhamel function** `v ↦ U(T, v) x(v)` on a piece is the
propagated forcing `U(T, v) b(v)`. -/
theorem duhamel_right_deriv (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (r : Fin M) {Λ : ℝ} (hΛ : ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ)
    {b sol : ℝ → V} (hsol : SolvesODE (G r) b sol (t r) (t ((r : ℕ) + 1)))
    {v : ℝ} (hv : v ∈ Ioo (t r) (t ((r : ℕ) + 1))) :
    HasDerivWithinAt (fun v => U v (sol v) T) (U v (b v) T) (Ioi v) v := by
  set c := t ((r : ℕ) + 1) with hcdef
  have hc := piece_le_last hmesh r
  have hvI : v ∈ Icc (t r) c := Ioo_subset_Icc_self hv
  have hv0 := piece_mem hmesh r hvI
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ v hvI)
  obtain ⟨h0, hsolU⟩ := hU v hv0 (sol v)
  have hsU := hsolU r hvI.2
  rw [max_eq_left hvI.1] at hsU
  -- the departure `e(u) = x(u) - U(u, v) x(v)` has right derivative `b(v)`
  have he : HasDerivWithinAt (fun u => sol u - U v (sol v) u) (b v) (Icc v c) v := by
    have h1 := (hsol v hvI).mono (Icc_subset_Icc hvI.1 le_rfl)
    have h2 := hsU v ⟨le_rfl, hvI.2⟩
    have h3 := h1.sub h2
    refine h3.congr_deriv ?_
    rw [h0]
    simp
  have hfilter : 𝓝[>] v ≤ 𝓝[Icc v c] v := by
    rw [← nhdsWithin_Ioc_eq_nhdsGT hv.2]
    exact nhdsWithin_mono v Ioc_subset_Icc_self
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have heo := (hasDerivWithinAt_iff_isLittleO.mp he).def (half_pos hε)
  have heo' := hfilter heo
  have hclose : ∀ᶠ u in 𝓝[>] v, Λ * ‖b v‖ * (u - v) ≤ ε / 2 := by
    have hlim : Tendsto (fun u => Λ * ‖b v‖ * (u - v)) (𝓝[>] v) (𝓝 0) := by
      have : Tendsto (fun u : ℝ => Λ * ‖b v‖ * (u - v)) (𝓝 v) (𝓝 (Λ * ‖b v‖ * (v - v))) :=
        ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto v)
      rw [sub_self, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hlim.eventually (ge_mem_nhds (half_pos hε))
  filter_upwards [heo', hclose, Ioc_mem_nhdsGT hv.2] with u hu hu2 hmem
  show ‖U u (sol u) T - U v (sol v) T - (u - v) • U v (b v) T‖ ≤ ε * ‖u - v‖
  have huI : u ∈ Icc (t r) c := ⟨hvI.1.trans hmem.1.le, hmem.2⟩
  have hu0 := piece_mem hmesh r huI
  have hvu : v ≤ u := hmem.1.le
  have hpos : 0 ≤ u - v := sub_nonneg.mpr hvu
  have hE := endMap_norm_le hmesh hU hG hu0
  -- rewrite everything as one propagated vector from `u`
  have hrw : U u (sol u) T - U v (sol v) T - (u - v) • U v (b v) T =
      endMap hmesh hU hG hu0 (sol u - U v (sol v) u - ((u - v : ℝ) : ℂ) • U v (b v) u) := by
    rw [hU.cocycle hmesh hG hv0 hvu hu0.2 (sol v) T ⟨hu0.2, le_rfl⟩,
      hU.cocycle hmesh hG hv0 hvu hu0.2 (b v) T ⟨hu0.2, le_rfl⟩, map_sub, map_sub, map_smul,
      endMap_apply, endMap_apply, endMap_apply, Complex.coe_smul]
  rw [hrw]
  refine (le_opNorm _ _).trans ?_
  refine (mul_le_mul_of_nonneg_right hE (norm_nonneg _)).trans ?_
  rw [one_mul]
  have hmove := mesh_move_le hmesh hU hG r hΛ hvI (b v) u ⟨hvu, hmem.2⟩
  have he_u : ‖sol u - U v (sol v) u - (sol v - U v (sol v) v) - (u - v) • b v‖ ≤
      ε / 2 * ‖u - v‖ := hu
  rw [h0, sub_self, sub_zero] at he_u
  rw [Real.norm_eq_abs, abs_of_nonneg hpos] at he_u ⊢
  calc
    ‖sol u - U v (sol v) u - ((u - v : ℝ) : ℂ) • U v (b v) u‖ =
        ‖(sol u - U v (sol v) u - (u - v) • b v) -
          (u - v) • (U v (b v) u - b v)‖ := by
      rw [Complex.coe_smul, smul_sub]
      congr 1
      abel
    _ ≤ ‖sol u - U v (sol v) u - (u - v) • b v‖ + ‖(u - v) • (U v (b v) u - b v)‖ :=
      norm_sub_le _ _
    _ ≤ ε / 2 * (u - v) + (u - v) * (Λ * ‖b v‖ * (u - v)) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hpos]
      exact add_le_add he_u (mul_le_mul_of_nonneg_left hmove hpos)
    _ ≤ ε / 2 * (u - v) + (u - v) * (ε / 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hu2 hpos)
    _ = ε * (u - v) := by ring

/-- **Duhamel's formula on one interval for a bounded piece**, carried to the final time:
`∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv = U(T, t_{r+1}) x(t_{r+1}) - U(T, t_r) x(t_r)`. -/
theorem piece_duhamel_bounded [CompleteSpace V] (hmesh : IsMesh t M T)
    (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (r : Fin M) {Λ : ℝ} (hΛ : ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ)
    {b sol : ℝ → V}
    (hint : IntervalIntegrable (fun v => U v (b v) T) volume (t r) (t ((r : ℕ) + 1)))
    (hsol : SolvesODE (G r) b sol (t r) (t ((r : ℕ) + 1))) :
    ∫ v in t r..t ((r : ℕ) + 1), U v (b v) T =
      U (t ((r : ℕ) + 1)) (sol (t ((r : ℕ) + 1))) T - U (t r) (sol (t r)) T :=
  intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (hmesh.mono (Nat.le_succ r))
    (propagated_continuousOn hmesh hU hG r hΛ sol
      (TimeDependentODE.SolvesODE.continuousOn hsol))
    (fun _ hv => duhamel_right_deriv hmesh hU hG r hΛ hsol hv) hint

/-- **Duhamel's formula on a mesh for bounded pieces.** For accretive bounded generator pieces, a
propagator `U` on the mesh, forcing pieces whose propagated forcing `v ↦ U(T, v) b_r(v)` is
integrable on its interval, and every piecewise solution,
`∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv = x(T) - U(T, 0) x(0)`. -/
theorem mesh_duhamel_bounded [CompleteSpace V] (hmesh : IsMesh t M T)
    (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hΛ : ∀ r : Fin M, ∃ Λ : ℝ, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ)
    (b : Fin M → ℝ → V)
    (hint : ∀ r : Fin M,
      IntervalIntegrable (fun v => U v (b r v) T) volume (t r) (t ((r : ℕ) + 1)))
    (sol : ℝ → V) (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) :
    ∑ r : Fin M, ∫ v in t r..t ((r : ℕ) + 1), U v (b r v) T = sol T - U 0 (sol 0) T := by
  have hT : 0 ≤ T := hmesh.last ▸ hmesh.nonneg M
  have hp : ∀ r : Fin M, ∫ v in t r..t ((r : ℕ) + 1), U v (b r v) T =
      U (t ((r : ℕ) + 1)) (sol (t ((r : ℕ) + 1))) T - U (t r) (sol (t r)) T := fun r =>
    piece_duhamel_bounded hmesh hU hG r (hΛ r).choose_spec (hint r) (hsol r)
  simp only [hp]
  rw [Fin.sum_univ_eq_sum_range (fun r => U (t (r + 1)) (sol (t (r + 1))) T -
    U (t r) (sol (t r)) T) M, Finset.sum_range_sub (fun r => U (t r) (sol (t r)) T),
    hmesh.last, hmesh.zero, (hU T ⟨hT, le_rfl⟩ (sol T)).1]

/-- **Continuous pieces satisfy the hypotheses of Duhamel's formula**: continuous generator pieces
are bounded and interval integrable, and with continuous forcing pieces the propagated forcing
`v ↦ U(T, v) b_r(v)` is interval integrable. -/
theorem continuous_pieces_regular (hmesh : IsMesh t M T) (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1))))
    (b : Fin M → ℝ → V) (hbc : ∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1)))) :
    (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) ∧
    (∀ r : Fin M, ∃ Λ : ℝ, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ) ∧
    ∀ r : Fin M, IntervalIntegrable (fun v => U v (b r v) T) volume (t r) (t ((r : ℕ) + 1)) := by
  refine ⟨fun r => (hGc r).intervalIntegrable_of_Icc (hmesh.mono (Nat.le_succ r)),
    fun r => isCompact_Icc.exists_bound_of_continuousOn (hGc r), fun r => ?_⟩
  obtain ⟨Λ, hΛ⟩ := isCompact_Icc.exists_bound_of_continuousOn (hGc r)
  exact (propagated_continuousOn hmesh hU hG r hΛ (b r) (hbc r)).intervalIntegrable_of_Icc
    (hmesh.mono (Nat.le_succ r))

end

end SparseHamiltonian.RepresentedSampleODE
