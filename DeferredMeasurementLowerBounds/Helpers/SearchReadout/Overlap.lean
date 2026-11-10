import DeferredMeasurementLowerBounds.Readout.Density
import UnitaryImplementationExtensions.LowerBound

set_option autoImplicit false

/-!
# Overlaps of final states read through one output register

Two facts behind the search lower bound for measured algorithms
(`DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_sharp`, manuscript
Corollary `hs:cor:unitary`).

* `norm_inner_le_of_reads`: two unit vectors `Ψ, Ψ'` whose decoded parts `L (D† Ψ)`, `L (D† Ψ')`
  (isometries `D`, `L`) have weight at least `1 - δ` in the ranges of two projections `R`, `R'`
  with `‖R v‖² + ‖R' v‖² ≤ ‖v‖²`, `δ ≤ 1/2`, have overlap at most `2 √(δ (1 - δ))`. The proof
  splits `Ψ` into its decoded part and the part outside the range of `D`, and the decoded part
  along `R`; two Cauchy–Schwarz steps reduce the bound to `overlap_real_le`, an inequality for
  two unit vectors of the plane.
* `sel m`: the projection `|m⟩⟨m| ⊗ 1_G` on system ⊗ garbage, which is the readout
  `SparseLowerBounds.Readout.liftObs` of the rank-one projector `|m⟩⟨m|`
  (`liftObs_pure_single`); projections of distinct values carry at most the whole weight
  (`norm_sq_sel_add_le`). `liftObs_reflect` is the readout of a reflection `2 A - 1`.
-/

namespace DeferredMeasurementLowerBounds.SearchReadout

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap
open SparseLowerBounds.Readout
open scoped InnerProduct InnerProductSpace

/-! ### Overlap of two final states -/

section Overlap

variable {A V H : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An isometry preserves inner products. -/
theorem inner_isometry {D : A →L[ℂ] V} (hD : D† ∘L D = 1) (x y : A) :
    ⟪D x, D y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← adjoint_inner_right, ← comp_apply, hD, one_apply_eq_self]

/-- Splitting along the range of an isometry `D`: the decoded part `D† Ψ` and the part outside
the range. -/
theorem inner_eq_isometry_add {D : A →L[ℂ] V} (hD : D† ∘L D = 1) (Ψ Ψ' : V) :
    ⟪Ψ, Ψ'⟫_ℂ = ⟪(D†) Ψ, (D†) Ψ'⟫_ℂ + ⟪Ψ - D ((D†) Ψ), Ψ' - D ((D†) Ψ')⟫_ℂ := by
  have h1 : ⟪D ((D†) Ψ), Ψ'⟫_ℂ = ⟪(D†) Ψ, (D†) Ψ'⟫_ℂ := (adjoint_inner_right D _ Ψ').symm
  have h2 : ⟪Ψ, D ((D†) Ψ')⟫_ℂ = ⟪(D†) Ψ, (D†) Ψ'⟫_ℂ := (adjoint_inner_left D _ Ψ).symm
  rw [inner_sub_left, inner_sub_right, inner_sub_right, h1, h2, inner_isometry hD]
  ring

/-- Pythagoras along the range of an isometry. -/
theorem norm_sq_eq_isometry_add {D : A →L[ℂ] V} (hD : D† ∘L D = 1) (Ψ : V) :
    ‖Ψ‖ ^ 2 = ‖(D†) Ψ‖ ^ 2 + ‖Ψ - D ((D†) Ψ)‖ ^ 2 := by
  have h := inner_eq_isometry_add hD Ψ Ψ
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

/-- Splitting along a star projection. -/
theorem inner_eq_proj_add {R : H →L[ℂ] H} (hR : IsStarProjection R) (v v' : H) :
    ⟪v, v'⟫_ℂ = ⟪R v, R v'⟫_ℂ + ⟪v - R v, v' - R v'⟫_ℂ := by
  have hRR : ∀ w, R (R w) = R w := fun w => by
    show (R * R) w = R w
    rw [hR.isIdempotentElem.eq]
  have hs : ∀ x y, ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ := hR.isSelfAdjoint.isSymmetric
  have hA : ⟪R v, R v'⟫_ℂ = ⟪R v, v'⟫_ℂ := by rw [hs, hRR, ← hs]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, hA, ← hs v v']
  ring

/-- The expectation of a star projection is the squared norm of the projected vector. -/
theorem re_inner_proj {R : H →L[ℂ] H} (hR : IsStarProjection R) (v : H) :
    (⟪v, R v⟫_ℂ).re = ‖R v‖ ^ 2 := by
  have hRR : R (R v) = R v := by
    show (R * R) v = R v
    rw [hR.isIdempotentElem.eq]
  have hs : ∀ x y, ⟪R x, y⟫_ℂ = ⟪x, R y⟫_ℂ := hR.isSelfAdjoint.isSymmetric
  have h1 : ⟪v, R v⟫_ℂ = ⟪R v, R v⟫_ℂ := by
    calc ⟪v, R v⟫_ℂ = ⟪v, R (R v)⟫_ℂ := by rw [hRR]
      _ = ⟪R v, R v⟫_ℂ := (hs v (R v)).symm
  rw [h1]
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (R v)

/-- Cauchy–Schwarz in the plane. -/
theorem add_mul_le_sqrt_mul_sqrt (s t s' t' : ℝ) :
    s * s' + t * t' ≤ Real.sqrt (s ^ 2 + t ^ 2) * Real.sqrt (s' ^ 2 + t' ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (s * t' - t * s')]))

/-- **The real overlap bound**: for unit vectors `(a, c)` and `(b, d)` of the plane with
`a² ≥ 1 - δ` and `b² ≤ δ`, `δ ≤ 1/2`, one has `a b + c d ≤ 2 √(δ (1 - δ))`. -/
theorem overlap_real_le {a b c d δ : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (hac : a ^ 2 + c ^ 2 = 1) (hbd : b ^ 2 + d ^ 2 = 1)
    (ha2 : 1 - δ ≤ a ^ 2) (hb2 : b ^ 2 ≤ δ) :
    a * b + c * d ≤ 2 * Real.sqrt (δ * (1 - δ)) := by
  have hd2 : 1 - δ ≤ d ^ 2 := by linarith
  have hcb : c * b ≤ δ := by nlinarith [sq_nonneg (c - b)]
  have had : 1 - δ ≤ a * d := by
    have h1 : (1 - δ) ^ 2 ≤ (a * d) ^ 2 := by
      rw [mul_pow, sq (1 - δ)]
      exact mul_le_mul ha2 hd2 (by linarith) (sq_nonneg a)
    exact (pow_le_pow_iff_left₀ (by linarith) (mul_nonneg ha hd) two_ne_zero).mp h1
  have hq0 : 0 ≤ 1 - 2 * δ := by linarith
  have hid : (a * b + c * d) ^ 2 + (a * d - c * b) ^ 2 = 1 := by
    have h : (a * b + c * d) ^ 2 + (a * d - c * b) ^ 2 = (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
      ring
    rw [h, hac, hbd, one_mul]
  have hq2 : (1 - 2 * δ) ^ 2 ≤ (a * d - c * b) ^ 2 := pow_le_pow_left₀ hq0 (by linarith) 2
  have hp2 : (a * b + c * d) ^ 2 ≤ (2 * Real.sqrt (δ * (1 - δ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hδ (by linarith))]
    nlinarith
  by_cases hp : a * b + c * d ≤ 0
  · exact hp.trans (by positivity)
  · exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp hp2

/-- **Overlap of two final states read through orthogonal projections.** If two unit vectors
decode, through an isometry `D` and then an isometry `L`, to vectors with weight at least
`1 - δ` in the ranges of `R` and `R'` respectively, where `‖R v‖² + ‖R' v‖² ≤ ‖v‖²`, and
`δ ≤ 1/2`, their overlap is at most `2 √(δ (1 - δ))`. -/
theorem norm_inner_le_of_reads {D : A →L[ℂ] V} (hD : D† ∘L D = 1) {L : A →L[ℂ] H}
    (hL : L† ∘L L = 1) {R R' : H →L[ℂ] H} (hR : IsStarProjection R)
    (hRR' : ∀ v, ‖R v‖ ^ 2 + ‖R' v‖ ^ 2 ≤ ‖v‖ ^ 2) {Ψ Ψ' : V} (hΨ : ‖Ψ‖ = 1)
    (hΨ' : ‖Ψ'‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2)
    (h : 1 - δ ≤ ‖R (L ((D†) Ψ))‖ ^ 2) (h' : 1 - δ ≤ ‖R' (L ((D†) Ψ'))‖ ^ 2) :
    ‖⟪Ψ, Ψ'⟫_ℂ‖ ≤ 2 * Real.sqrt (δ * (1 - δ)) := by
  have hnL : ∀ x, ‖L x‖ = ‖x‖ := L.norm_map_iff_adjoint_comp_self.mpr hL
  have hsplit : ⟪Ψ, Ψ'⟫_ℂ = ⟪R (L ((D†) Ψ)), R (L ((D†) Ψ'))⟫_ℂ +
      ⟪L ((D†) Ψ) - R (L ((D†) Ψ)), L ((D†) Ψ') - R (L ((D†) Ψ'))⟫_ℂ +
      ⟪Ψ - D ((D†) Ψ), Ψ' - D ((D†) Ψ')⟫_ℂ := by
    rw [inner_eq_isometry_add hD, ← inner_isometry hL, ← inner_eq_proj_add hR]
  have hn : ‖L ((D†) Ψ)‖ ^ 2 + ‖Ψ - D ((D†) Ψ)‖ ^ 2 = 1 := by
    rw [hnL, ← norm_sq_eq_isometry_add hD, hΨ, one_pow]
  have hn' : ‖L ((D†) Ψ')‖ ^ 2 + ‖Ψ' - D ((D†) Ψ')‖ ^ 2 = 1 := by
    rw [hnL, ← norm_sq_eq_isometry_add hD, hΨ', one_pow]
  have hpu := UnitaryImplementationExtensions.Search.norm_sq_proj_add hR (L ((D†) Ψ))
  have hpu' := UnitaryImplementationExtensions.Search.norm_sq_proj_add hR (L ((D†) Ψ'))
  have hb2 : ‖R (L ((D†) Ψ'))‖ ^ 2 ≤ δ := by
    have := hRR' (L ((D†) Ψ'))
    nlinarith [sq_nonneg ‖Ψ' - D ((D†) Ψ')‖]
  rw [hsplit, add_assoc]
  refine (norm_add_le _ _).trans ((add_le_add (norm_inner_le_norm _ _)
    ((norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _)
      (norm_inner_le_norm _ _)))).trans ?_)
  refine (add_le_add le_rfl (add_mul_le_sqrt_mul_sqrt _ _ _ _)).trans ?_
  refine overlap_real_le (norm_nonneg _) (Real.sqrt_nonneg _) hδ hδ1 ?_ ?_ h hb2
  · rw [Real.sq_sqrt (by positivity)]
    linarith
  · rw [Real.sq_sqrt (by positivity)]
    linarith

end Overlap

/-! ### Reading one output value -/

section Reading

variable {N : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The projection onto the output value `m`, `|m⟩⟨m| ⊗ 1_G`. -/
def sel (m : Fin N) : SysGarb (Fin N) G →L[ℂ] SysGarb (Fin N) G :=
  Joint.fiber fun i => if i = m then 1 else 0

/-- The projection onto an output value is a star projection. -/
theorem sel_isStarProjection (m : Fin N) : IsStarProjection (sel (G := G) m) := by
  refine ⟨?_, ?_⟩
  · show Joint.fiber _ * Joint.fiber _ = _
    rw [Joint.fiber_mul]
    congr 1
    funext i
    split_ifs <;> simp
  · show star (Joint.fiber _) = _
    rw [Joint.star_fiber]
    congr 1
    funext i
    split_ifs <;> simp

omit [CompleteSpace G] in
/-- The weight of the output value `m`. -/
theorem norm_sq_sel (m : Fin N) (v : SysGarb (Fin N) G) : ‖sel m v‖ ^ 2 = ‖v m‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_eq_single m]
  · simp [sel, Joint.fiber_apply]
  · intro i _ hi
    simp [sel, Joint.fiber_apply, hi]
  · simp

omit [CompleteSpace G] in
/-- Two distinct output values carry at most the whole weight. -/
theorem norm_sq_sel_add_le {m m' : Fin N} (hm : m ≠ m') (v : SysGarb (Fin N) G) :
    ‖sel m v‖ ^ 2 + ‖sel m' v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_sq_sel, norm_sq_sel, PiLp.norm_sq_eq_of_L2]
  have h := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {m, m'})
    fun i _ _ => sq_nonneg ‖v i‖
  rwa [Finset.sum_pair hm] at h

omit [CompleteSpace G] in
/-- The readout of the rank-one projector `|m⟩⟨m|` is the projection onto the value `m`. -/
theorem liftObs_pure_single (m : Fin N) :
    (liftObs (ODEMixedOutput.pureOperator (EuclideanSpace.single m (1 : ℂ))) :
      SysGarb (Fin N) G →L[ℂ] SysGarb (Fin N) G) = sel m := by
  ext Φ i
  rw [liftObs_apply]
  by_cases h : i = m
  · subst h
    simp [sel, Joint.fiber_apply, ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply,
      EuclideanSpace.inner_single_left, ite_smul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  · simp [sel, Joint.fiber_apply, ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply,
      h]

omit [CompleteSpace G] in
/-- The readout of a reflection `2 A - 1`. -/
theorem liftObs_reflect (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    (liftObs ((2 : ℂ) • A - 1) : SysGarb (Fin N) G →L[ℂ] SysGarb (Fin N) G) =
      (2 : ℂ) • liftObs A - 1 := by
  ext Φ i
  rw [sub_apply, smul_apply, PiLp.sub_apply, PiLp.smul_apply, liftObs_apply, liftObs_apply,
    one_apply_eq_self]
  simp [sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum, ite_smul]

end Reading

end

end DeferredMeasurementLowerBounds.SearchReadout
