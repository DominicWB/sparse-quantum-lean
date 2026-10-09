import SparseLowerBounds.Query.Readout
import SparseLowerBounds.Hamiltonian.Amplitude

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Accuracy, readout correlation and the endpoint form

Manuscript lines 2090-2097 (eq. `hsl:eq:accuracy`) and 2303-2306.

* `corr_of_accurate`: an `ε`-accurate output (observable form of trace
  distance, `Readout.Accurate`) changes the expectation of a Hermitian
  contraction by at most `2ε` (lines 2303-2304), so a signed ideal expectation
  `≥ a` becomes an output correlation `≥ a - 2ε`.
* `endpointReadout`, `accurate_of_endpoint`: "an operator-norm error at most
  `ε` implies eq. `hsl:eq:accuracy`" (lines 2096-2097). For a fixed isometric
  input encoding `ι : ℂ^S → K` (the release's `input`), an endpoint error
  `‖V ∘ ι - ι ∘ U‖ ≤ ε` makes the output `V (ι ψ)`, read through the fixed
  isometry `endpointReadout ι i₀ : K → ℂ^S ⊗ K`, `ε`-accurate for `U ψ`. The
  readout sends `k` to `(ι† k) ⊗ ι|i₀⟩ + |i₀⟩ ⊗ (1 - ι ι†) k`; on the image of
  `ι` it is `ι ψ ↦ ψ ⊗ ι|i₀⟩`.

Proof route for `accurate_of_endpoint` (helpers below, all stated here):

1. `endpointReadout_apply` (componentwise formula) and `inner_endpointReadout`
   (`⟪e k, e k'⟫ = ⟪k, k'⟫`; the cross terms vanish because
   `ι† (1 - ι ι†) = 0`) give `endpointReadout_isometry`.
2. `endpointReadout_apply_iota` (`e (ι ψ) = ψ ⊗ ι|i₀⟩`) and
   `‖ι|i₀⟩‖ = 1` give `inner_endpointReadout_lift`, hence
   `inner_outObs_endpointReadout`: the readout of an encoded vector `ι φ`
   reproduces `⟪φ, M φ⟫` exactly.
3. With `a = V (ι ψ)`, `b = ι (U ψ)`, `L = outObs e M` (`‖L‖ ≤ 1` by
   `norm_outObs_le` and step 1), `abs_inner_sub_inner_le` bounds the error by
   `‖L‖ (‖a‖ + ‖b‖) ‖a - b‖ ≤ 1 · 2 · ε`, since
   `a - b = (V ∘ ι - ι ∘ U) ψ`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open Readout
open scoped InnerProduct InnerProductSpace

variable {S G K : Type*} [Fintype S] [DecidableEq S]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Accuracy gives correlation** (lines 2303-2304): if the output is `ε`-accurate
for `ψ` and a Hermitian contraction `M` has signed ideal expectation
`sgn ⟪ψ, M ψ⟫ ≥ a` with `|sgn| ≤ 1`, the output has signed expectation at
least `a - 2ε`. -/
theorem corr_of_accurate (e : K →L[ℂ] SysGarb S G) (Φ : K) (ψ : EuclideanSpace ℂ S) (ε : ℝ)
    (hacc : Accurate e Φ ψ ε) (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)
    (hM : IsSelfAdjoint M) (hM1 : ‖M‖ ≤ 1) {sgn a : ℝ} (hsgn : |sgn| ≤ 1)
    (ha : a ≤ sgn * (⟪ψ, M ψ⟫_ℂ).re) :
    a - 2 * ε ≤ sgn * (⟪Φ, outObs e M Φ⟫_ℂ).re := by
  -- Proof sketch: `hacc M hM hM1 : |X - Y| ≤ 2ε`; then
  -- `sgn X = sgn Y + sgn (X - Y) ≥ a - |sgn| |X - Y| ≥ a - 2ε` (as in
  -- `Readout.heralded_correlation`).
  have h := hacc M hM hM1
  set X := (⟪Φ, outObs e M Φ⟫_ℂ).re
  set Y := (⟪ψ, M ψ⟫_ℂ).re
  have h3 : |sgn * (X - Y)| ≤ 2 * ε := by
    rw [abs_mul]
    calc |sgn| * |X - Y| ≤ 1 * (2 * ε) := mul_le_mul hsgn h (abs_nonneg _) zero_le_one
      _ = 2 * ε := one_mul _
  have h4 := neg_abs_le (sgn * (X - Y))
  have e1 : sgn * X = sgn * (X - Y) + sgn * Y := by ring
  linarith

/-! ### Expectation of a fixed operator is Lipschitz in the vector -/

omit [CompleteSpace K] in
/-- `⟪a, L a⟫ - ⟪b, L b⟫ = ⟪a - b, L a⟫ + ⟪b, L (a - b)⟫`, so the expectation of a
fixed operator moves by at most `‖L‖ (‖a‖ + ‖b‖) ‖a - b‖`. -/
theorem norm_inner_sub_inner_le (L : K →L[ℂ] K) (a b : K) :
    ‖⟪a, L a⟫_ℂ - ⟪b, L b⟫_ℂ‖ ≤ ‖L‖ * (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have hid : ⟪a, L a⟫_ℂ - ⟪b, L b⟫_ℂ = ⟪a - b, L a⟫_ℂ + ⟪b, L (a - b)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]; ring
  rw [hid]
  calc ‖⟪a - b, L a⟫_ℂ + ⟪b, L (a - b)⟫_ℂ‖
        ≤ ‖⟪a - b, L a⟫_ℂ‖ + ‖⟪b, L (a - b)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ ‖a - b‖ * ‖L a‖ + ‖b‖ * ‖L (a - b)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖a - b‖ * (‖L‖ * ‖a‖) + ‖b‖ * (‖L‖ * ‖a - b‖) := by
        gcongr
        · exact L.le_opNorm a
        · exact L.le_opNorm (a - b)
    _ = ‖L‖ * (‖a‖ + ‖b‖) * ‖a - b‖ := by ring

omit [CompleteSpace K] in
/-- Real-part form of `norm_inner_sub_inner_le`, the form consumed by
`Readout.Accurate` (step 3 of `accurate_of_endpoint`, lines 2096-2097). -/
theorem abs_inner_sub_inner_le (L : K →L[ℂ] K) (a b : K) :
    |(⟪a, L a⟫_ℂ).re - (⟪b, L b⟫_ℂ).re| ≤ ‖L‖ * (‖a‖ + ‖b‖) * ‖a - b‖ := by
  -- Proof sketch: `|Re z - Re w| = |Re (z - w)| ≤ ‖z - w‖`, then `norm_inner_sub_inner_le`.
  rw [← Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans (norm_inner_sub_inner_le L a b)

/-! ### The endpoint readout -/

/-- The endpoint readout `k ↦ (ι† k) ⊗ ι|i₀⟩ + |i₀⟩ ⊗ (1 - ι ι†) k`. -/
def endpointReadout (ι : EuclideanSpace ℂ S →L[ℂ] K) (i₀ : S) : K →L[ℂ] SysGarb S K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i =>
      (EuclideanSpace.proj i ∘L ι†).smulRight (ι (EuclideanSpace.single i₀ 1)) +
        if i = i₀ then 1 - ι ∘L ι† else 0

/-- Componentwise formula for the endpoint readout:
`(e k)_i = (ι† k)_i · ι|i₀⟩ + [i = i₀] (k - ι ι† k)`. -/
theorem endpointReadout_apply (ι : EuclideanSpace ℂ S →L[ℂ] K) (i₀ : S) (k : K) (i : S) :
    endpointReadout ι i₀ k i =
      ((ι†) k) i • ι (EuclideanSpace.single i₀ 1) + if i = i₀ then k - ι ((ι†) k) else 0 := by
  change ((EuclideanSpace.proj i ∘L ι†).smulRight (ι (EuclideanSpace.single i₀ 1)) +
      (if i = i₀ then 1 - ι ∘L ι† else 0)) k = _
  split_ifs <;> simp [ContinuousLinearMap.smulRight_apply]

/-! #### Isometric-encoding helpers -/

namespace Accuracy

omit [DecidableEq S] in
theorem adjoint_apply_iota {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1)
    (x : EuclideanSpace ℂ S) : (ι†) (ι x) = x := by
  simpa using ContinuousLinearMap.ext_iff.mp hι x

omit [DecidableEq S] in
theorem inner_iota {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1)
    (x y : EuclideanSpace ℂ S) : ⟪ι x, ι y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_apply_iota hι]

theorem inner_iota_single {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1) (i₀ : S) :
    ⟪ι (EuclideanSpace.single i₀ 1), ι (EuclideanSpace.single i₀ 1)⟫_ℂ = 1 := by
  rw [inner_iota hι, EuclideanSpace.inner_single_left]
  simp

omit [DecidableEq S] in
theorem inner_iota_compl {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1)
    (x : EuclideanSpace ℂ S) (k : K) : ⟪ι x, k - ι ((ι†) k)⟫_ℂ = 0 := by
  rw [inner_sub_right, inner_iota hι, ContinuousLinearMap.adjoint_inner_right, sub_self]

omit [DecidableEq S] in
theorem inner_compl_iota {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1)
    (x : EuclideanSpace ℂ S) (k : K) : ⟪k - ι ((ι†) k), ι x⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_iota_compl hι, map_zero]

omit [DecidableEq S] in
theorem inner_compl_compl {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1) (k k' : K) :
    ⟪k - ι ((ι†) k), k' - ι ((ι†) k')⟫_ℂ = ⟪k, k'⟫_ℂ - ⟪(ι†) k, (ι†) k'⟫_ℂ := by
  rw [inner_sub_right, inner_compl_iota hι, sub_zero, inner_sub_left,
    ← ContinuousLinearMap.adjoint_inner_right]

omit [DecidableEq S] in
theorem norm_iota_le {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1) : ‖ι‖ ≤ 1 := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self ι
  rw [hι] at h
  have h1 : ‖(1 : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg ι]

/-- Componentwise inner product of two endpoint readouts. -/
theorem inner_endpointReadout_apply {ι : EuclideanSpace ℂ S →L[ℂ] K} (hι : ι† ∘L ι = 1)
    (i₀ : S) (k k' : K) (i : S) :
    ⟪endpointReadout ι i₀ k i, endpointReadout ι i₀ k' i⟫_ℂ =
      ⟪((ι†) k) i, ((ι†) k') i⟫_ℂ +
        if i = i₀ then ⟪k, k'⟫_ℂ - ⟪(ι†) k, (ι†) k'⟫_ℂ else 0 := by
  rw [endpointReadout_apply, endpointReadout_apply, RCLike.inner_apply']
  split_ifs with h
  · subst h
    rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_left,
      inner_smul_right, inner_smul_right, inner_iota_single hι, inner_iota_compl hι,
      inner_compl_iota hι, inner_compl_compl hι]
    ring
  · rw [add_zero, add_zero, add_zero, inner_smul_left, inner_smul_right, inner_iota_single hι]
    ring

end Accuracy

open Accuracy in

/-- The endpoint readout preserves inner products when `ι` is an isometry: the
diagonal terms give `⟪ι† k, ι† k'⟫ ‖ι|i₀⟩‖² + ⟪k, (1 - ι ι†) k'⟫ = ⟪k, k'⟫`,
and the cross terms vanish because `ι† (1 - ι ι†) = 0`. -/
theorem inner_endpointReadout (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1) (i₀ : S)
    (k k' : K) :
    ⟪endpointReadout ι i₀ k, endpointReadout ι i₀ k'⟫_ℂ = ⟪k, k'⟫_ℂ := by
  have hα : ⟪(ι†) k, (ι†) k'⟫_ℂ = ∑ i, ⟪((ι†) k) i, ((ι†) k') i⟫_ℂ := PiLp.inner_apply _ _
  rw [PiLp.inner_apply]
  simp_rw [inner_endpointReadout_apply hι i₀ k k']
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← hα]
  ring

/-- The endpoint readout is an isometry when `ι` is. -/
theorem endpointReadout_isometry (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1) (i₀ : S) :
    (endpointReadout ι i₀)† ∘L endpointReadout ι i₀ = 1 := by
  -- Proof sketch: `ext k; ext_inner_left`, `adjoint_inner_right`, `inner_endpointReadout`.
  ext k
  apply ext_inner_left ℂ
  intro k'
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_endpointReadout ι hι, one_apply_eq_self]

/-- On the image of `ι` the endpoint readout is the product vector
`ι ψ ↦ ψ ⊗ ι|i₀⟩`: component `i` is `ψ i · ι|i₀⟩` (from `endpointReadout_apply`
with `ι† ι ψ = ψ`). -/
theorem endpointReadout_apply_iota (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1)
    (i₀ : S) (ψ : EuclideanSpace ℂ S) (i : S) :
    endpointReadout ι i₀ (ι ψ) i = ψ i • ι (EuclideanSpace.single i₀ 1) := by
  rw [endpointReadout_apply, Accuracy.adjoint_apply_iota hι]
  simp

/-- A system observable read on the product vector `φ ⊗ ι|i₀⟩` gives
`⟪φ, M φ⟫ ‖ι|i₀⟩‖² = ⟪φ, M φ⟫` (`Readout.liftObs_apply`,
`endpointReadout_apply_iota`, and `‖ι|i₀⟩‖ = 1`). -/
theorem inner_endpointReadout_lift (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1)
    (i₀ : S) (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (φ : EuclideanSpace ℂ S) :
    ⟪endpointReadout ι i₀ (ι φ), liftObs M (endpointReadout ι i₀ (ι φ))⟫_ℂ = ⟪φ, M φ⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hMφ : (M φ) i = ∑ i', M (EuclideanSpace.single i' 1) i * φ i' := by
    conv_lhs => rw [← (EuclideanSpace.basisFun S ℂ).sum_repr φ]
    simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, mul_comm]
  rw [liftObs_apply]
  simp_rw [endpointReadout_apply_iota ι hι, smul_smul]
  rw [← Finset.sum_smul, inner_smul_left, inner_smul_right, Accuracy.inner_iota_single hι,
    mul_one, hMφ, RCLike.inner_apply']

/-- **The readout of an encoded vector is exact**: for every system observable
`M`, the workspace observable `outObs (endpointReadout ι i₀) M` has expectation
`⟪φ, M φ⟫` in `ι φ` (`adjoint_inner_right` and `inner_endpointReadout_lift`). -/
theorem inner_outObs_endpointReadout (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1)
    (i₀ : S) (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (φ : EuclideanSpace ℂ S) :
    ⟪ι φ, outObs (endpointReadout ι i₀) M (ι φ)⟫_ℂ = ⟪φ, M φ⟫_ℂ := by
  rw [outObs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply]
  exact inner_endpointReadout_lift ι hι i₀ M φ

/-- **Endpoint error implies accuracy** (lines 2096-2097). If
`‖V ∘ ι - ι ∘ U‖ ≤ ε` for a contraction `V` and an isometric encoding `ι`,
then for every input `ψ` with `‖ψ‖ ≤ 1` and `‖U ψ‖ ≤ 1`, the output `V (ι ψ)`
read through `endpointReadout ι i₀` is `ε`-accurate for `U ψ`. -/
theorem accurate_of_endpoint (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1) (i₀ : S)
    (V : K →L[ℂ] K) (hV : ‖V‖ ≤ 1) (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)
    {ψ : EuclideanSpace ℂ S} (hψ : ‖ψ‖ ≤ 1) (hUψ : ‖U ψ‖ ≤ 1) {ε : ℝ}
    (hε : ‖V ∘L ι - ι ∘L U‖ ≤ ε) :
    Accurate (endpointReadout ι i₀) (V (ι ψ)) (U ψ) ε := by
  -- Proof sketch: fix `M`; rewrite `⟪U ψ, M (U ψ)⟫` as `⟪ι (U ψ), L (ι (U ψ))⟫` with
  -- `L = outObs (endpointReadout ι i₀) M` (`inner_outObs_endpointReadout`);
  -- `‖L‖ ≤ ‖M‖ ≤ 1` (`norm_outObs_le`, `endpointReadout_isometry`);
  -- `‖V (ι ψ)‖ ≤ 1`, `‖ι (U ψ)‖ = ‖U ψ‖ ≤ 1`,
  -- `‖V (ι ψ) - ι (U ψ)‖ = ‖(V ∘L ι - ι ∘L U) ψ‖ ≤ ε ‖ψ‖ ≤ ε`;
  -- conclude with `abs_inner_sub_inner_le`: `≤ 1 · (1 + 1) · ε = 2ε`.
  intro M hM hM1
  rw [← inner_outObs_endpointReadout ι hι i₀ M (U ψ)]
  have hL : ‖outObs (endpointReadout ι i₀) M‖ ≤ 1 :=
    (norm_outObs_le _ (endpointReadout_isometry ι hι i₀) M).trans hM1
  have hι1 := Accuracy.norm_iota_le hι
  have hιψ : ‖ι ψ‖ ≤ 1 :=
    (ι.le_opNorm ψ).trans (by nlinarith [norm_nonneg ι, norm_nonneg ψ])
  have ha : ‖V (ι ψ)‖ ≤ 1 :=
    (V.le_opNorm _).trans (by nlinarith [norm_nonneg V, norm_nonneg (ι ψ)])
  have hb : ‖ι (U ψ)‖ ≤ 1 :=
    (ι.le_opNorm _).trans (by nlinarith [norm_nonneg ι, norm_nonneg (U ψ)])
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hε
  have hd : ‖V (ι ψ) - ι (U ψ)‖ ≤ ε := by
    have hsub : V (ι ψ) - ι (U ψ) = (V ∘L ι - ι ∘L U) ψ := by simp
    rw [hsub]
    calc ‖(V ∘L ι - ι ∘L U) ψ‖ ≤ ‖V ∘L ι - ι ∘L U‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * 1 := mul_le_mul hε hψ (norm_nonneg _) hε0
      _ = ε := mul_one _
  refine (abs_inner_sub_inner_le _ _ _).trans ?_
  calc ‖outObs (endpointReadout ι i₀) M‖ * (‖V (ι ψ)‖ + ‖ι (U ψ)‖) * ‖V (ι ψ) - ι (U ψ)‖
        ≤ 1 * (1 + 1) * ε := by
          apply mul_le_mul _ hd (norm_nonneg _) (by norm_num)
          exact mul_le_mul hL (add_le_add ha hb) (by positivity) zero_le_one
    _ = 2 * ε := by ring

end

end SparseLowerBounds.Hamiltonian
end
