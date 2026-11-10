import MixedOutputODE.PartialTrace

/-!
# Selection from a mixed solver output

A solver output `z` on `s × W` whose reduced state on `s` is within trace distance `δ` of a pure
state `|ŷ⟩⟨ŷ|` is selected by an isometric decoder `V : n → s`, acting as `V ⊗ 1` on the retained
register. If the ideal selection probability `p = ‖V† ŷ‖²` exceeds `2 δ`, then the selected
amplitude has squared norm at least `(p - 2δ) ‖z‖²`, and the reduced selected state is within trace
distance `2δ / (p - 2δ)` of the selected ideal state (`selection`). This is the selection estimate
behind eq. `ode:eq:history-solver-tolerance`, with the explicit constants of the Hölder and triangle
inequalities; they are weaker than the manuscript's `p - δ` and `2δ / p`.
-/

namespace SparseHamiltonian.MixedOutputODE

noncomputable section
open ContinuousLinearMap ODEMixedOutput InnerProductSpace ODEStateNormalization
open scoped InnerProduct BigOperators ComplexConjugate

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A real multiple of a self-adjoint operator is self-adjoint. -/
theorem isSymmetric_real_smul (r : ℝ) {X : E →L[ℂ] E} (hX : X.toLinearMap.IsSymmetric) :
    ((r : ℂ) • X).toLinearMap.IsSymmetric := by
  rw [ContinuousLinearMap.toLinearMap_smul]
  exact hX.smul (Complex.conj_ofReal r)

/-- The pure state of a normalized vector. -/
theorem pure_unitDirection (u : E) (hu : u ≠ 0) :
    pureOperator (unitDirection u) = (((‖u‖ ^ 2)⁻¹ : ℝ) : ℂ) • pureOperator u := by
  have h := bornWeight_pureDirection u
  have hn : (‖u‖ ^ 2 : ℝ) ≠ 0 := by positivity
  rw [← h, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hn, Complex.ofReal_one, one_smul]

theorem tr_pure [FiniteDimensional ℂ E] (u : E) : tr (pureOperator u) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [tr, pureOperator, InnerProductSpace.trace_rankOne, inner_self_complex, Complex.ofReal_pow]

end Generic

variable {n s W : Type*} [Fintype n] [Fintype s] [Fintype W] [DecidableEq W]

set_option maxHeartbeats 2000000 in
/-- **Selection from a mixed output.** -/
theorem selection (z : EuclideanSpace ℂ (s × W)) (hz : z ≠ 0)
    (yhat : EuclideanSpace ℂ s) (V : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ s)
    (hV : V† ∘L V = 1) (δ : ℝ)
    (hsym : (ptrace (pureOperator (unitDirection z)) - pureOperator yhat).toLinearMap.IsSymmetric)
    (hTD : hermitianTraceDistance (ptrace (pureOperator (unitDirection z))) (pureOperator yhat)
      hsym ≤ δ)
    (hp : 2 * δ < ‖(V†) yhat‖ ^ 2) :
    (‖(V†) yhat‖ ^ 2 - 2 * δ) * ‖z‖ ^ 2 ≤ ‖((tensorLeft (W := W) V)†) z‖ ^ 2 ∧
      ∃ h : (ptrace (pureOperator (unitDirection (((tensorLeft (W := W) V)†) z))) -
          pureOperator (unitDirection ((V†) yhat))).toLinearMap.IsSymmetric,
        hermitianTraceDistance (ptrace (pureOperator (unitDirection
            (((tensorLeft (W := W) V)†) z))))
          (pureOperator (unitDirection ((V†) yhat))) h ≤ 2 * δ / (‖(V†) yhat‖ ^ 2 - 2 * δ) := by
  set ρ := ptrace (pureOperator (unitDirection z)) with hρdef
  set σ := pureOperator yhat with hσdef
  set d := ((tensorLeft (W := W) V)†) z with hddef
  set p := ‖(V†) yhat‖ ^ 2 with hpdef
  have hρpos : ρ.IsPositive := ptrace_isPositive (pureOperator_positive _)
  have hσpos : σ.IsPositive := pureOperator_positive _
  have hVn : ‖V‖ ≤ 1 := GeneralODE.Registers.norm_le_one_of_isometry V hV
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hδ : 0 ≤ δ := (hermitianTraceDistance_nonneg _ _ hsym).trans hTD
  -- the compressions
  set ρV := V† ∘L ρ ∘L V with hρVdef
  set σV := V† ∘L σ ∘L V with hσVdef
  have hσV : σV = pureOperator ((V†) yhat) := (pureOperator_adjoint_apply V yhat).symm
  have hρVpos : ρV.IsPositive := hρpos.adjoint_conj V
  have hσVpos : σV.IsPositive := hσpos.adjoint_conj V
  -- the selected probability `a = ‖d‖² / ‖z‖²`
  have hunit : unitDirection z = (((‖z‖)⁻¹ : ℝ) : ℂ) • z := by
    rw [unitDirection, ← Complex.coe_smul]
  have hρV : ρV = ptrace (pureOperator (((tensorLeft (W := W) V)†) (unitDirection z))) := by
    rw [pureOperator_adjoint_apply, ptrace_conj]
  have hd1 : ((tensorLeft (W := W) V)†) (unitDirection z) = (((‖z‖)⁻¹ : ℝ) : ℂ) • d := by
    rw [hunit, map_smul]
  set a := ‖d‖ ^ 2 / ‖z‖ ^ 2 with hadef
  have hρVtr : tr ρV = (a : ℂ) := by
    rw [hρV, tr_ptrace, tr_pure, hd1, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hznorm), hadef]
    congr 1
    field_simp
  have hσVtr : tr σV = (p : ℂ) := by rw [hσV, tr_pure]
  -- `|a - p| ≤ 2 δ`
  have htn : tnorm (ρ - σ) hsym ≤ 2 * δ := by
    rw [hermitianTraceDistance_eq_tnorm] at hTD
    linarith
  have hcyc : tr (V† ∘L (ρ - σ) ∘L V) = tr ((V ∘L V†) ∘L (ρ - σ)) := by
    have h1 : tr (V† ∘L (ρ - σ) ∘L V) = tr ((ρ - σ) ∘L V ∘L V†) := by
      change LinearMap.trace ℂ _ ((V†).toLinearMap ∘ₗ ((ρ - σ) ∘L V).toLinearMap) =
        LinearMap.trace ℂ _ (((ρ - σ) ∘L V).toLinearMap ∘ₗ (V†).toLinearMap)
      exact LinearMap.trace_comp_comm' _ _
    have h2 : tr ((ρ - σ) ∘L V ∘L V†) = tr ((V ∘L V†) ∘L (ρ - σ)) := by
      change LinearMap.trace ℂ _ ((ρ - σ).toLinearMap ∘ₗ (V ∘L V†).toLinearMap) =
        LinearMap.trace ℂ _ ((V ∘L V†).toLinearMap ∘ₗ (ρ - σ).toLinearMap)
      exact LinearMap.trace_comp_comm' _ _
    rw [h1, h2]
  have hVV : ‖V ∘L V†‖ ≤ 1 := by
    have hV' : ‖V†‖ ≤ 1 := by rw [ContinuousLinearMap.adjoint.norm_map]; exact hVn
    calc
      ‖V ∘L V†‖ ≤ ‖V‖ * ‖V†‖ := opNorm_comp_le _ _
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1
  have hdiff : |a - p| ≤ 2 * δ := by
    have hsplit : tr (V† ∘L (ρ - σ) ∘L V) = (a : ℂ) - (p : ℂ) := by
      rw [← hρVtr, ← hσVtr, hρVdef, hσVdef, ← tr_sub]
      congr 1
      rw [sub_comp, comp_sub]
    have hbound : ‖tr ((V ∘L V†) ∘L (ρ - σ))‖ ≤ 2 * δ := by
      calc
        ‖tr ((V ∘L V†) ∘L (ρ - σ))‖ ≤ ‖V ∘L V†‖ * tnorm (ρ - σ) hsym := norm_tr_comp_le _ _ hsym
        _ ≤ 1 * (2 * δ) :=
          mul_le_mul hVV htn (tnorm_nonneg _ _) zero_le_one
        _ = 2 * δ := one_mul _
    rw [← hcyc, hsplit, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hbound
    exact hbound
  have ha_low : p - 2 * δ ≤ a := by
    have := (abs_le.mp hdiff).1
    linarith
  have ha : 0 < a := lt_of_lt_of_le (by linarith) ha_low
  refine ⟨?_, ?_⟩
  · -- the selected amplitude
    have hdz : ‖d‖ ^ 2 = a * ‖z‖ ^ 2 := by
      rw [hadef]
      field_simp
    rw [hdz]
    exact mul_le_mul_of_nonneg_right ha_low (sq_nonneg _)
  · -- the selected state
    have hd0 : d ≠ 0 := by
      intro h0
      have : a = 0 := by rw [hadef, h0, norm_zero]; ring
      linarith
    have hp0 : 0 < p := by linarith
    have hVy0 : (V†) yhat ≠ 0 := by
      intro h0
      rw [hpdef, h0, norm_zero] at hp0
      norm_num at hp0
    -- the two selected states as multiples of the compressions
    have hsel : ptrace (pureOperator (unitDirection d)) = ((a⁻¹ : ℝ) : ℂ) • ρV := by
      have hz' : pureOperator z = ((‖z‖ ^ 2 : ℝ) : ℂ) • pureOperator (unitDirection z) :=
        (bornWeight_pureDirection z).symm
      have hpd : ptrace (pureOperator d) = ((‖z‖ ^ 2 : ℝ) : ℂ) • ρV := by
        rw [hddef, pureOperator_adjoint_apply, ptrace_conj, hz', ptrace_smul, smul_comp,
          comp_smul, ← hρdef]
      rw [pure_unitDirection d hd0, ptrace_smul, hpd, smul_smul, ← Complex.ofReal_mul]
      congr 2
      rw [hadef]
      field_simp
    have hideal : pureOperator (unitDirection ((V†) yhat)) = ((p⁻¹ : ℝ) : ℂ) • σV := by
      rw [pure_unitDirection _ hVy0, hσV]
    -- symmetric pieces
    have hρVs := hρVpos.isSymmetric
    have hσVs := hσVpos.isSymmetric
    have hD : (ρV - σV).toLinearMap.IsSymmetric := hρVs.sub hσVs
    have h1s := isSymmetric_real_smul a⁻¹ hD
    have h2s := isSymmetric_real_smul (a⁻¹ - p⁻¹) hσVs
    have hXs : (((a⁻¹ : ℝ) : ℂ) • (ρV - σV) + (((a⁻¹ - p⁻¹ : ℝ)) : ℂ) • σV).toLinearMap.IsSymmetric :=
      h1s.add h2s
    have hfinal : (ptrace (pureOperator (unitDirection d)) -
        pureOperator (unitDirection ((V†) yhat))).toLinearMap.IsSymmetric :=
      (ptrace_isPositive (pureOperator_positive _)).isSymmetric.sub
        (pureOperator_positive _).isSymmetric
    have hXeq : ptrace (pureOperator (unitDirection d)) -
        pureOperator (unitDirection ((V†) yhat)) =
          ((a⁻¹ : ℝ) : ℂ) • (ρV - σV) + (((a⁻¹ - p⁻¹ : ℝ)) : ℂ) • σV := by
      rw [hsel, hideal, smul_sub, Complex.ofReal_sub, sub_smul]
      abel
    -- the bound
    have hcomp : tnorm (ρV - σV) hD ≤ 2 * δ := by
      have heq : ρV - σV = V† ∘L (ρ - σ) ∘L V := by
        rw [hρVdef, hσVdef, sub_comp, comp_sub]
      have hs' : (V† ∘L (ρ - σ) ∘L V).toLinearMap.IsSymmetric := by rw [← heq]; exact hD
      rw [tnorm_congr heq hD hs']
      exact (tnorm_compress_le V hVn (ρ - σ) hsym hs').trans htn
    have hσt : tnorm σV hσVs ≤ p := by
      have hs' : (pureOperator ((V†) yhat)).toLinearMap.IsSymmetric :=
        (pureOperator_positive _).isSymmetric
      rw [tnorm_congr hσV hσVs hs']
      exact tnorm_pure_le _ hs'
    have hT1 := tnorm_smul_le ((a⁻¹ : ℝ) : ℂ) (ρV - σV) hD h1s
    have hT2 := tnorm_smul_le (((a⁻¹ - p⁻¹ : ℝ)) : ℂ) σV hσVs h2s
    have hT := tnorm_add_le _ _ h1s h2s hXs
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)] at hT1
    rw [Complex.norm_real, Real.norm_eq_abs] at hT2
    have habs : |a⁻¹ - p⁻¹| * p ≤ 2 * δ / a := by
      have he : a⁻¹ - p⁻¹ = (p - a) / (a * p) := by field_simp
      rw [he, abs_div, abs_of_pos (mul_pos ha hp0)]
      have : |p - a| / (a * p) * p = |p - a| / a := by field_simp
      rw [this]
      apply div_le_div_of_nonneg_right _ ha.le
      rw [abs_sub_comm]
      exact hdiff
    refine ⟨hfinal, ?_⟩
    rw [hermitianTraceDistance_eq_tnorm, tnorm_congr hXeq hfinal hXs]
    have hbound : tnorm _ hXs ≤ 4 * δ / a := by
      calc
        tnorm _ hXs ≤ tnorm _ h1s + tnorm _ h2s := hT
        _ ≤ a⁻¹ * tnorm (ρV - σV) hD + |a⁻¹ - p⁻¹| * tnorm σV hσVs := add_le_add hT1 hT2
        _ ≤ a⁻¹ * (2 * δ) + |a⁻¹ - p⁻¹| * p :=
          add_le_add (mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr ha.le))
            (mul_le_mul_of_nonneg_left hσt (abs_nonneg _))
        _ ≤ a⁻¹ * (2 * δ) + 2 * δ / a := add_le_add le_rfl habs
        _ = 4 * δ / a := by field_simp; ring
    have hpa : 0 < p - 2 * δ := by linarith
    calc
      tnorm _ hXs / 2 ≤ 4 * δ / a / 2 := by linarith
      _ = 2 * δ / a := by ring
      _ ≤ 2 * δ / (p - 2 * δ) :=
        div_le_div_of_nonneg_left (by linarith) hpa ha_low

end

end SparseHamiltonian.MixedOutputODE
