import TimeDependentHamiltonian.Continuous.Propagator
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Existence of the time-ordered propagator

For a family `H` of bounded operators that is continuous on `[0, t]`, the
Schrödinger equation `U' = -i H(u) U`, `U(0) = 1`, has a solution on `[0, t]`
(`exists_solvesOn`). The Picard–Lindelöf theorem gives solutions starting from
the identity on intervals of length `h` with `2 Λ h ≤ 1`, where `Λ` bounds
`‖H‖`; consecutive solutions are glued by right multiplication with the
propagator already constructed. A Lipschitz path is continuous, so the
propagator in Theorem `hs:thm:time` exists (`exists_solvesOn_of_lipschitz`).
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap Set
open scoped NNReal

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Local solutions from the identity on short intervals. -/
theorem exists_local_solution (H : ℝ → P →L[ℂ] P) (c h Λ : ℝ) (hh : 0 ≤ h) (hΛ : 0 ≤ Λ)
    (hsmall : 2 * Λ * h ≤ 1) (hcont : ContinuousOn H (Icc c (c + h)))
    (hbound : ∀ u ∈ Icc c (c + h), ‖H u‖ ≤ Λ) :
    ∃ V : ℝ → P →L[ℂ] P, V c = 1 ∧
      ∀ u ∈ Icc c (c + h), HasDerivWithinAt V ((-Complex.I) • (H u * V u)) (Icc c (c + h)) u := by
  let f : ℝ → (P →L[ℂ] P) → (P →L[ℂ] P) := fun u X => (-Complex.I) • (H u * X)
  have hc : c ∈ Icc c (c + h) := ⟨le_rfl, by linarith⟩
  let K : ℝ≥0 := ⟨Λ, hΛ⟩
  let L : ℝ≥0 := ⟨2 * Λ, by positivity⟩
  have hK : (K : ℝ) = Λ := rfl
  have hL : (L : ℝ) = 2 * Λ := rfl
  have hPL : IsPicardLindelof f (⟨c, hc⟩ : Icc c (c + h)) (1 : P →L[ℂ] P) 1 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      apply LipschitzOnWith.of_dist_le_mul
      intro X _ Y _
      rw [dist_eq_norm, dist_eq_norm, hK]
      calc
        ‖f u X - f u Y‖ = ‖H u * (X - Y)‖ := by
          simp only [f, ← smul_sub, ← mul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul]
        _ ≤ ‖H u‖ * ‖X - Y‖ := norm_mul_le _ _
        _ ≤ Λ * ‖X - Y‖ := mul_le_mul_of_nonneg_right (hbound u hu) (norm_nonneg _)
    · intro X _
      exact (hcont.mul continuousOn_const).const_smul (-Complex.I)
    · intro u hu X hX
      have hX2 : ‖X‖ ≤ 2 := by
        have h1 : ‖X - 1‖ ≤ 1 := by simpa [dist_eq_norm] using hX
        calc
          ‖X‖ = ‖(X - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖X - 1‖ + ‖(1 : P →L[ℂ] P)‖ := norm_add_le _ _
          _ ≤ 1 + 1 := add_le_add h1 ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      rw [hL]
      calc
        ‖f u X‖ = ‖H u * X‖ := by simp only [f, norm_smul, norm_neg, Complex.norm_I, one_mul]
        _ ≤ ‖H u‖ * ‖X‖ := norm_mul_le _ _
        _ ≤ Λ * 2 := mul_le_mul (hbound u hu) hX2 (norm_nonneg _) hΛ
        _ = 2 * Λ := by ring
    · change (L : ℝ) * max ((c + h) - c) (c - c) ≤ ((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
      rw [hL, add_sub_cancel_left, sub_self, max_eq_left hh, NNReal.coe_one, NNReal.coe_zero,
        sub_zero]
      linarith
  obtain ⟨V, hV0, hV⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨V, hV0, hV⟩

/-- A continuous family has a propagator from the identity on `[0, t]`. -/
theorem exists_solvesOn (H : ℝ → P →L[ℂ] P) {t : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn H (Icc 0 t)) :
    ∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧ SolvesOn H U 0 t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hcont
  set Λ := max C 0 with hΛdef
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hΛ : ∀ u ∈ Icc 0 t, ‖H u‖ ≤ Λ := fun u hu => (hC u hu).trans (le_max_left _ _)
  set N : ℕ := ⌈2 * Λ * t⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN2 : 2 * Λ * t ≤ N := by
    have := Nat.le_ceil (2 * Λ * t)
    have hcast : ((⌈2 * Λ * t⌉₊ + 1 : ℕ) : ℝ) = (⌈2 * Λ * t⌉₊ : ℝ) + 1 := by push_cast; ring
    rw [hNdef, hcast]
    linarith
  set h : ℝ := t / N with hhdef
  have hh : 0 ≤ h := div_nonneg ht hNR.le
  have hNh : (N : ℝ) * h = t := by rw [hhdef]; field_simp
  have hsmall : 2 * Λ * h ≤ 1 := by
    rw [hhdef, ← mul_div_assoc, div_le_one hNR]
    exact hN2
  let f : ℝ → (P →L[ℂ] P) → (P →L[ℂ] P) := fun u X => (-Complex.I) • (H u * X)
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N → ∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧
      ∀ u ∈ Icc 0 (k * h), HasDerivWithinAt U (f u (U u)) (Icc 0 (k * h)) u := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro hN
        have hsub : Icc 0 (0 + h) ⊆ Icc 0 t := by
          apply Icc_subset_Icc le_rfl
          rw [zero_add, ← hNh]
          have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
          nlinarith
        obtain ⟨V, hV0, hV⟩ := exists_local_solution H 0 h Λ hh hΛ0 hsmall
          (hcont.mono hsub) (fun u hu => hΛ u (hsub hu))
        refine ⟨V, hV0, ?_⟩
        simpa only [Nat.cast_one, one_mul, zero_add] using hV
    | succ k hk ih =>
        intro hN
        obtain ⟨U, hU0, hU⟩ := ih (by omega)
        have hkh : 0 ≤ (k : ℝ) * h := by positivity
        have hk1 : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
        have hsub : Icc (k * h) (k * h + h) ⊆ Icc 0 t := by
          apply Icc_subset_Icc hkh
          rw [← hk1, ← hNh]
          have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith
        obtain ⟨V, hV0, hV⟩ := exists_local_solution H (k * h) h Λ hh hΛ0 hsmall
          (hcont.mono hsub) (fun u hu => hΛ u (hsub hu))
        let W : ℝ → P →L[ℂ] P := fun u => if u ≤ k * h then U u else V u * U (k * h)
        have hWleft : ∀ u ∈ Icc 0 (k * h), W u = U u := by
          intro u hu
          simp only [W, if_pos hu.2]
        have hWright : ∀ u ∈ Icc (k * h) (k * h + h), W u = V u * U (k * h) := by
          intro u hu
          by_cases hle : u ≤ k * h
          · have hu' : u = k * h := le_antisymm hle hu.1
            rw [hu']
            simp [W, hV0]
          · simp only [W, if_neg hle]
        refine ⟨W, by simp only [W, if_pos hkh, hU0], ?_⟩
        intro u hu
        rw [hk1] at hu ⊢
        rw [← Icc_union_Icc_eq_Icc hkh (by linarith : k * h ≤ k * h + h)]
        apply HasDerivWithinAt.union
        · by_cases hmem : u ∈ Icc 0 (k * h)
          · have h1 := (hU u hmem).congr_of_mem hWleft hmem
            rwa [← hWleft u hmem] at h1
          · apply HasFDerivWithinAt.of_notMem_closure
            rwa [closure_Icc]
        · by_cases hmem : u ∈ Icc (k * h) (k * h + h)
          · have h1 := ((hV u hmem).mul_const (U (k * h))).congr_of_mem hWright hmem
            have hval : f u (V u) * U (k * h) = f u (W u) := by
              rw [hWright u hmem]
              simp only [f, smul_mul_assoc, mul_assoc]
            rwa [hval] at h1
          · apply HasFDerivWithinAt.of_notMem_closure
            rwa [closure_Icc]
  obtain ⟨U, hU0, hU⟩ := key N hN1 le_rfl
  refine ⟨U, hU0, ?_⟩
  intro u hu
  rw [← hNh] at hu ⊢
  exact hU u hu

/-- A Lipschitz path of operators has a propagator from the identity. -/
theorem exists_solvesOn_of_lipschitz (H : ℝ → P →L[ℂ] P) {t β : ℝ} (ht : 0 ≤ t)
    (hLip : ∀ u ∈ Icc 0 t, ∀ v ∈ Icc 0 t, ‖H u - H v‖ ≤ β * |u - v|) :
    ∃ U : ℝ → P →L[ℂ] P, U 0 = 1 ∧ SolvesOn H U 0 t := by
  apply exists_solvesOn H ht
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

end

end SparseHamiltonian.TimeDependent
