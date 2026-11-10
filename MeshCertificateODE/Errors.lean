import RepresentedSampleODE.Regular
import TimeDependentExtensions.Mesh.Duhamel

/-!
# Integrated sample errors of operator samples on a mesh

The certificates of the manuscript for time-dependent generators (proof of `ode:thm:time`; Lemma
`ode:lem:gate-select`) bound the *integrated* operator-norm error of the represented samples,
`∑_r ∫_{t_r}^{t_{r+1}} ‖K̃_{k,r} - K_k(u)‖ du`, which covers both the freezing of the generator on
each mesh interval and the representation error of the samples ("More general certificates for the
same integrated sample error may replace Lipschitz bounds").
This file states them for generator pieces `G_r` and operator samples `G̃_r` on any Hilbert space
(the query-level library states them for native sparse data, `GeneralSourceExtensions.Mesh.
sampleError`, `RepresentedSampleODE.dissipativeError`):

* `sampleErr t G G̃ = ∑_r ∫ ‖G_r(u) - G̃_r‖` and `dissErr t G G̃ = ∑_r ∫ ‖Herm(G_r(u) - G̃_r)‖`
  (`dissErr_le_sampleErr` for integrable pieces);
* `pathNeg t G G̃ r`: the average of `‖Herm(G_r(u) - G̃_r)‖` over interval `r`, a negativity bound
  of the sample for accretive integrable pieces (`pathNeg_bound`), with negativity mass the
  dissipative sample error (`negativity_pathNeg`);
* `sampleErr_le_of_lipschitz`: `β_r`-Lipschitz pieces with left-endpoint sample errors `δ_r` have
  `ΔG ≤ ∑_r (β_r Δ_r² / 2 + δ_r Δ_r)` (the Lipschitz bounds of Lemma `ode:lem:gate-select`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive)
open scoped BigOperators InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] {M : ℕ}

/-! ### The errors -/

/-- **The integrated sample error** of operator samples `G̃_r` against generator pieces `G_r` on a
mesh: `ΔG = ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r(u) - G̃_r‖ du`. -/
def sampleErr (t : ℕ → ℝ) (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) : ℝ :=
  ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖G r u - Gt r‖

/-- **The dissipative sample error** `ΔD = ∑_r ∫_{t_r}^{t_{r+1}} ‖Herm(G_r(u) - G̃_r)‖ du`. -/
def dissErr (t : ℕ → ℝ) (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) : ℝ :=
  ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
    ‖ODEHermitianReduction.dissipativePart (G r u - Gt r)‖

/-- **The path negativity** of interval `r`: the average of `‖Herm(G_r(u) - G̃_r)‖` over the
interval (the norm of the sample on an empty interval). -/
def pathNeg (t : ℕ → ℝ) (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (r : Fin M) : ℝ :=
  if 0 < t ((r : ℕ) + 1) - t r then
    (∫ u in t r..t ((r : ℕ) + 1), ‖ODEHermitianReduction.dissipativePart (G r u - Gt r)‖) /
      (t ((r : ℕ) + 1) - t r)
  else ‖Gt r‖

omit [CompleteSpace V] in
theorem sampleErr_nonneg {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) : 0 ≤ sampleErr t G Gt :=
  Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _

theorem dissErr_nonneg {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) : 0 ≤ dissErr t G Gt :=
  Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _

theorem pathNeg_nonneg {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (r : Fin M) :
    0 ≤ pathNeg t G Gt r := by
  unfold pathNeg
  split_ifs with h
  · exact div_nonneg (intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r))
      fun _ _ => norm_nonneg _) h.le
  · exact norm_nonneg _

/-- The real part of a quadratic form is at most the norm of the Hermitian part. -/
theorem re_inner_le_dissipativePart (A : V →L[ℂ] V) (w : V) :
    (inner ℂ w (A w)).re ≤ ‖ODEHermitianReduction.dissipativePart A‖ * ‖w‖ ^ 2 := by
  rw [← ODEHermitianReduction.real_inner_dissipativePart]
  calc (inner ℂ w (ODEHermitianReduction.dissipativePart A w)).re
      ≤ ‖inner ℂ w (ODEHermitianReduction.dissipativePart A w)‖ := Complex.re_le_norm _
    _ ≤ ‖w‖ * ‖ODEHermitianReduction.dissipativePart A w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖ODEHermitianReduction.dissipativePart A‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
    _ = ‖ODEHermitianReduction.dissipativePart A‖ * ‖w‖ ^ 2 := by ring

/-- The norm of the Hermitian part of an integrable operator path minus a constant is
integrable. -/
theorem dissipativePart_intervalIntegrable {G : ℝ → V →L[ℂ] V} {a b : ℝ}
    (hG : IntervalIntegrable G volume a b) (C : V →L[ℂ] V) :
    IntervalIntegrable (fun u => ‖ODEHermitianReduction.dissipativePart (G u - C)‖) volume a b := by
  have h1 : IntervalIntegrable (fun u => G u - C) volume a b := hG.sub intervalIntegrable_const
  have hadj : Continuous (fun A : V →L[ℂ] V => A†) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := V)).continuous
  have hc : Continuous (fun A : V →L[ℂ] V => ‖ODEHermitianReduction.dissipativePart A‖) := by
    simp only [ODEHermitianReduction.dissipativePart, HermitianDilation.hermitianPart]
    exact ((continuous_id.add hadj).const_smul ((2 : ℂ)⁻¹)).norm
  refine h1.norm.mono_fun' (hc.comp_aestronglyMeasurable h1.aestronglyMeasurable_restrict_uIoc) ?_
  filter_upwards with u
  simp only [norm_norm]
  exact ODEHermitianReduction.norm_dissipativePart_le _

/-- **The dissipative sample error is at most the sample error**, for integrable pieces. -/
theorem dissErr_le_sampleErr {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V)
    (hGi : RepresentedSampleODE.RegularPieces t G) : dissErr t G Gt ≤ sampleErr t G Gt := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hab := hmesh.mono (Nat.le_succ r)
  have h1 := dissipativePart_intervalIntegrable (hGi r) (Gt r)
  have h2 : IntervalIntegrable (fun u => ‖G r u - Gt r‖) volume (t r) (t ((r : ℕ) + 1)) :=
    ((hGi r).sub intervalIntegrable_const).norm
  exact intervalIntegral.integral_mono_on hab h1 h2
    (fun u _ => ODEHermitianReduction.norm_dissipativePart_le _)

/-- **The path averages are negativity bounds**: for accretive integrable pieces the samples
satisfy `Re ⟨w, G̃_r w⟩ ≥ -κ_r ‖w‖²` with `κ_r = pathNeg t G G̃ r`. -/
theorem pathNeg_bound {t : ℕ → ℝ} (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGi : RepresentedSampleODE.RegularPieces t G) (r : Fin M) (w : V) :
    -pathNeg t G Gt r * ‖w‖ ^ 2 ≤ (inner ℂ w (Gt r w)).re := by
  unfold pathNeg
  set A := Gt r with hA
  split_ifs with hpos
  · set a := t r
    set b := t ((r : ℕ) + 1)
    have hab : a ≤ b := by linarith
    set f : ℝ → ℝ := fun u => ‖ODEHermitianReduction.dissipativePart (G r u - A)‖ with hf
    have hfint : IntervalIntegrable f volume a b := dissipativePart_intervalIntegrable (hGi r) A
    set c : ℝ := (inner ℂ w (A w)).re with hc
    have key : ∀ u ∈ Icc a b, -(f u * ‖w‖ ^ 2) ≤ c := by
      intro u hu
      have h0 := hG r u hu w
      have h1 := re_inner_le_dissipativePart (G r u - A) w
      have e : (inner ℂ w ((G r u - A) w)).re = (inner ℂ w (G r u w)).re - c := by
        rw [hc, sub_apply, inner_sub_right, Complex.sub_re]
      rw [e] at h1
      simp only [hf]
      linarith
    have hint : ∫ u in a..b, -(f u * ‖w‖ ^ 2) ≤ ∫ u in a..b, c :=
      intervalIntegral.integral_mono_on hab ((hfint.mul_const (‖w‖ ^ 2)).neg)
        intervalIntegrable_const key
    have e1 : ∫ u in a..b, -(f u * ‖w‖ ^ 2) = -((∫ u in a..b, f u) * ‖w‖ ^ 2) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_mul_const]
    have e2 : ∫ u in a..b, c = (b - a) * c := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [e1, e2] at hint
    have hba : 0 < b - a := hpos
    set I : ℝ := ∫ u in a..b, f u with hI
    have e3 : -(I / (b - a)) * ‖w‖ ^ 2 = -(I * ‖w‖ ^ 2) / (b - a) := by ring
    rw [e3, div_le_iff₀ hba]
    linarith [mul_comm c (b - a)]
  · have h := re_inner_le_dissipativePart (-A) w
    rw [neg_apply, inner_neg_right, Complex.neg_re] at h
    have hd : ‖ODEHermitianReduction.dissipativePart (-A)‖ ≤ ‖A‖ :=
      (ODEHermitianReduction.norm_dissipativePart_le _).trans (norm_neg A).le
    have hm := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖w‖)
    linarith

/-- **The negativity mass of the path bounds is the dissipative sample error.** -/
theorem negativity_pathNeg {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) :
    RepresentedSampleODE.negativity t (pathNeg t G Gt) = dissErr t G Gt := by
  unfold RepresentedSampleODE.negativity dissErr
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold pathNeg
  split_ifs with hpos
  · field_simp
  · have h0 : t ((r : ℕ) + 1) - t r = 0 := le_antisymm (not_lt.mp hpos) (hmesh.length_nonneg r)
    have h1 : t ((r : ℕ) + 1) = t r := by linarith
    rw [h0, zero_mul, h1, intervalIntegral.integral_same]

/-! ### Lipschitz pieces -/

omit [CompleteSpace V] in
/-- **Lipschitz pieces** (the Lipschitz bounds of Lemma `ode:lem:gate-select`). If piece `r` is
`β_r`-Lipschitz on its closed interval and its sample error at the left endpoint is at most `δ_r`,
the integrated sample error is at most `∑_r (β_r Δ_r² / 2 + δ_r Δ_r)`. -/
theorem sampleErr_le_of_lipschitz {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (β δ : Fin M → ℝ)
    (hLip : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ w ∈ Icc (t r) (t ((r : ℕ) + 1)),
      ‖G r u - G r w‖ ≤ β r * |u - w|)
    (hδ : ∀ r : Fin M, ‖G r (t r) - Gt r‖ ≤ δ r) :
    sampleErr t G Gt ≤
      ∑ r : Fin M, (β r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 + δ r * (t ((r : ℕ) + 1) - t r)) := by
  unfold sampleErr
  exact Finset.sum_le_sum fun r _ =>
    integral_le_of_lipschitz' (G r) _ (hmesh.mono (Nat.le_succ r)) (hLip r) (hδ r)

end

end SparseHamiltonian.MeshCertificateODE
