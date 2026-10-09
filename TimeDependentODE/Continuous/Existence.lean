import TimeDependentODE.Continuous.Solution
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Existence of solutions of the forced linear ODE

For `G` and `b` continuous on `[0, T]`, the equation `x' = -G(u) x + b(u)`
has a solution on `[0, T]` from every initial value (`exists_solvesODE`); no
accretivity is needed. The vector field is affine, so a solution on a short
interval `[c, c + h]` from an arbitrary start value `y` is `Φ(u) y + ψ(u)`,
where the Picard–Lindelöf theorem gives the homogeneous propagator `Φ` from the
identity (`exists_local_propagator`) and the forced solution `ψ` from zero
(`exists_local_forced`) on intervals whose length depends only on the bounds
`Λ ≥ ‖G‖` and `B ≥ ‖b‖`, not on the start value (`exists_local_solvesODE`).
Solutions on consecutive mesh intervals are glued at the mesh points. A
Lipschitz family is continuous, so Lipschitz coefficients also give a solution
(`exists_solvesODE_of_lipschitz`).
-/

namespace SparseHamiltonian.TimeDependentODE

noncomputable section

open ContinuousLinearMap Set
open scoped NNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The homogeneous propagator from the identity on a short interval. -/
theorem exists_local_propagator (G : ℝ → V →L[ℂ] V) (c h Λ : ℝ) (hh : 0 ≤ h) (hΛ : 0 ≤ Λ)
    (hsmall : 2 * Λ * h ≤ 1) (hcont : ContinuousOn G (Icc c (c + h)))
    (hbound : ∀ u ∈ Icc c (c + h), ‖G u‖ ≤ Λ) :
    ∃ Φ : ℝ → V →L[ℂ] V, Φ c = 1 ∧
      ∀ u ∈ Icc c (c + h), HasDerivWithinAt Φ (-(G u * Φ u)) (Icc c (c + h)) u := by
  let f : ℝ → (V →L[ℂ] V) → (V →L[ℂ] V) := fun u X => -(G u * X)
  have hc : c ∈ Icc c (c + h) := ⟨le_rfl, by linarith⟩
  let K : ℝ≥0 := ⟨Λ, hΛ⟩
  let L : ℝ≥0 := ⟨2 * Λ, by positivity⟩
  have hK : (K : ℝ) = Λ := rfl
  have hL : (L : ℝ) = 2 * Λ := rfl
  have hPL : IsPicardLindelof f (⟨c, hc⟩ : Icc c (c + h)) (1 : V →L[ℂ] V) 1 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      apply LipschitzOnWith.of_dist_le_mul
      intro X _ Y _
      rw [dist_eq_norm, dist_eq_norm, hK]
      calc
        ‖f u X - f u Y‖ = ‖G u * (X - Y)‖ := by
          rw [show f u X - f u Y = -(G u * (X - Y)) by simp only [f, mul_sub]; abel, norm_neg]
        _ ≤ ‖G u‖ * ‖X - Y‖ := norm_mul_le _ _
        _ ≤ Λ * ‖X - Y‖ := mul_le_mul_of_nonneg_right (hbound u hu) (norm_nonneg _)
    · intro X _
      exact (hcont.mul continuousOn_const).neg
    · intro u hu X hX
      have hX2 : ‖X‖ ≤ 2 := by
        have h1 : ‖X - 1‖ ≤ 1 := by simpa [dist_eq_norm] using hX
        calc
          ‖X‖ = ‖(X - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖X - 1‖ + ‖(1 : V →L[ℂ] V)‖ := norm_add_le _ _
          _ ≤ 1 + 1 := add_le_add h1 ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      rw [hL]
      calc
        ‖f u X‖ = ‖G u * X‖ := norm_neg _
        _ ≤ ‖G u‖ * ‖X‖ := norm_mul_le _ _
        _ ≤ Λ * 2 := mul_le_mul (hbound u hu) hX2 (norm_nonneg _) hΛ
        _ = 2 * Λ := by ring
    · change (L : ℝ) * max ((c + h) - c) (c - c) ≤ ((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
      rw [hL, add_sub_cancel_left, sub_self, max_eq_left hh, NNReal.coe_one, NNReal.coe_zero,
        sub_zero]
      exact hsmall
  obtain ⟨Φ, hΦ0, hΦ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨Φ, hΦ0, hΦ⟩

/-- The forced solution from zero on a short interval. -/
theorem exists_local_forced (G : ℝ → V →L[ℂ] V) (b : ℝ → V) (c h Λ B : ℝ) (hh : 0 ≤ h)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B) (hsmall : (Λ + B) * h ≤ 1)
    (hGc : ContinuousOn G (Icc c (c + h))) (hbc : ContinuousOn b (Icc c (c + h)))
    (hGb : ∀ u ∈ Icc c (c + h), ‖G u‖ ≤ Λ) (hbb : ∀ u ∈ Icc c (c + h), ‖b u‖ ≤ B) :
    ∃ ψ : ℝ → V, ψ c = 0 ∧
      ∀ u ∈ Icc c (c + h), HasDerivWithinAt ψ (-(G u (ψ u)) + b u) (Icc c (c + h)) u := by
  let f : ℝ → V → V := fun u y => -(G u y) + b u
  have hc : c ∈ Icc c (c + h) := ⟨le_rfl, by linarith⟩
  let K : ℝ≥0 := ⟨Λ, hΛ⟩
  let L : ℝ≥0 := ⟨Λ + B, by positivity⟩
  have hK : (K : ℝ) = Λ := rfl
  have hL : (L : ℝ) = Λ + B := rfl
  have hPL : IsPicardLindelof f (⟨c, hc⟩ : Icc c (c + h)) (0 : V) 1 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu
      apply LipschitzOnWith.of_dist_le_mul
      intro y _ z _
      rw [dist_eq_norm, dist_eq_norm, hK]
      calc
        ‖f u y - f u z‖ = ‖G u (y - z)‖ := by
          rw [show f u y - f u z = -(G u (y - z)) by simp only [f, map_sub]; abel, norm_neg]
        _ ≤ ‖G u‖ * ‖y - z‖ := le_opNorm _ _
        _ ≤ Λ * ‖y - z‖ := mul_le_mul_of_nonneg_right (hGb u hu) (norm_nonneg _)
    · intro y _
      exact (hGc.clm_apply continuousOn_const).neg.add hbc
    · intro u hu y hy
      have hy1 : ‖y‖ ≤ 1 := by simpa using hy
      rw [hL]
      calc
        ‖f u y‖ ≤ ‖-(G u y)‖ + ‖b u‖ := norm_add_le _ _
        _ = ‖G u y‖ + ‖b u‖ := by rw [norm_neg]
        _ ≤ ‖G u‖ * ‖y‖ + B := add_le_add (le_opNorm _ _) (hbb u hu)
        _ ≤ Λ * 1 + B := add_le_add (mul_le_mul (hGb u hu) hy1 (norm_nonneg _) hΛ) le_rfl
        _ = Λ + B := by ring
    · change (L : ℝ) * max ((c + h) - c) (c - c) ≤ ((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
      rw [hL, add_sub_cancel_left, sub_self, max_eq_left hh, NNReal.coe_one, NNReal.coe_zero,
        sub_zero]
      exact hsmall
  obtain ⟨ψ, hψ0, hψ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨ψ, hψ0, hψ⟩

/-- A solution on a short interval from an arbitrary start value: the
propagator applied to the start value plus the forced solution from zero. -/
theorem exists_local_solvesODE (G : ℝ → V →L[ℂ] V) (b : ℝ → V) (c h Λ B : ℝ) (hh : 0 ≤ h)
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B) (hsmall : (2 * Λ + B) * h ≤ 1)
    (hGc : ContinuousOn G (Icc c (c + h))) (hbc : ContinuousOn b (Icc c (c + h)))
    (hGb : ∀ u ∈ Icc c (c + h), ‖G u‖ ≤ Λ) (hbb : ∀ u ∈ Icc c (c + h), ‖b u‖ ≤ B) (y : V) :
    ∃ z : ℝ → V, z c = y ∧ SolvesODE G b z c (c + h) := by
  have hBh : 0 ≤ B * h := mul_nonneg hB hh
  have hΛh : 0 ≤ Λ * h := mul_nonneg hΛ hh
  obtain ⟨Φ, hΦ0, hΦ⟩ := exists_local_propagator G c h Λ hh hΛ (by nlinarith) hGc hGb
  obtain ⟨ψ, hψ0, hψ⟩ :=
    exists_local_forced G b c h Λ B hh hΛ hB (by nlinarith) hGc hbc hGb hbb
  refine ⟨fun u => Φ u y + ψ u, by simp only [hΦ0, hψ0, one_apply_eq_self, add_zero], ?_⟩
  intro u hu
  let ev : (V →L[ℂ] V) →L[ℝ] V := (ContinuousLinearMap.apply ℂ V y).restrictScalars ℝ
  have h1 : HasDerivWithinAt (fun s => Φ s y) ((-(G u * Φ u)) y) (Icc c (c + h)) u :=
    ev.hasFDerivAt.comp_hasDerivWithinAt u (hΦ u hu)
  have h2 := h1.fun_add (hψ u hu)
  have hval : (-(G u * Φ u)) y + (-(G u (ψ u)) + b u) = -(G u (Φ u y + ψ u)) + b u := by
    simp only [neg_apply, mul_apply_eq_comp, map_add, neg_add]
    abel
  rwa [hval] at h2

/-- Existence of the solution for continuous coefficients (Picard–Lindelöf plus gluing). -/
theorem exists_solvesODE (G : ℝ → V →L[ℂ] V) (b : ℝ → V) {T : ℝ} (hT : 0 ≤ T)
    (hGc : ContinuousOn G (Set.Icc 0 T)) (hbc : ContinuousOn b (Set.Icc 0 T)) (x0 : V) :
    ∃ x : ℝ → V, x 0 = x0 ∧ SolvesODE G b x 0 T := by
  obtain ⟨CG, hCG⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hGc
  obtain ⟨Cb, hCb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hbc
  set Λ := max CG 0 with hΛdef
  set B := max Cb 0 with hBdef
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hB0 : 0 ≤ B := le_max_right _ _
  have hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ Λ := fun u hu => (hCG u hu).trans (le_max_left _ _)
  have hB : ∀ u ∈ Icc 0 T, ‖b u‖ ≤ B := fun u hu => (hCb u hu).trans (le_max_left _ _)
  set N : ℕ := ⌈(2 * Λ + B) * T⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN2 : (2 * Λ + B) * T ≤ N := by
    have := Nat.le_ceil ((2 * Λ + B) * T)
    have hcast : ((⌈(2 * Λ + B) * T⌉₊ + 1 : ℕ) : ℝ) = (⌈(2 * Λ + B) * T⌉₊ : ℝ) + 1 := by
      push_cast
      ring
    rw [hNdef, hcast]
    linarith
  set h : ℝ := T / N with hhdef
  have hh : 0 ≤ h := div_nonneg hT hNR.le
  have hNh : (N : ℝ) * h = T := by rw [hhdef]; field_simp
  have hsmall : (2 * Λ + B) * h ≤ 1 := by
    rw [hhdef, ← mul_div_assoc, div_le_one hNR]
    exact hN2
  have key : ∀ k : ℕ, 1 ≤ k → k ≤ N → ∃ x : ℝ → V, x 0 = x0 ∧ SolvesODE G b x 0 (k * h) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro hN
        have hsub : Icc 0 (0 + h) ⊆ Icc 0 T := by
          apply Icc_subset_Icc le_rfl
          rw [zero_add, ← hNh]
          have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN1
          nlinarith
        obtain ⟨z, hz0, hz⟩ := exists_local_solvesODE G b 0 h Λ B hh hΛ0 hB0 hsmall
          (hGc.mono hsub) (hbc.mono hsub) (fun u hu => hΛ u (hsub hu))
          (fun u hu => hB u (hsub hu)) x0
        refine ⟨z, hz0, ?_⟩
        simpa only [Nat.cast_one, one_mul, zero_add] using hz
    | succ k hk ih =>
        intro hN
        obtain ⟨x, hx0, hx⟩ := ih (by omega)
        have hkh : 0 ≤ (k : ℝ) * h := by positivity
        have hk1 : ((k + 1 : ℕ) : ℝ) * h = k * h + h := by push_cast; ring
        have hsub : Icc (k * h) (k * h + h) ⊆ Icc 0 T := by
          apply Icc_subset_Icc hkh
          rw [← hk1, ← hNh]
          have : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
          nlinarith
        obtain ⟨z, hz0, hz⟩ := exists_local_solvesODE G b (k * h) h Λ B hh hΛ0 hB0 hsmall
          (hGc.mono hsub) (hbc.mono hsub) (fun u hu => hΛ u (hsub hu))
          (fun u hu => hB u (hsub hu)) (x (k * h))
        let W : ℝ → V := fun u => if u ≤ k * h then x u else z u
        have hWleft : ∀ u ∈ Icc 0 (k * h), W u = x u := by
          intro u hu
          simp only [W, if_pos hu.2]
        have hWright : ∀ u ∈ Icc (k * h) (k * h + h), W u = z u := by
          intro u hu
          by_cases hle : u ≤ k * h
          · have hu' : u = k * h := le_antisymm hle hu.1
            rw [hu']
            simp [W, hz0]
          · simp only [W, if_neg hle]
        refine ⟨W, by simp only [W, if_pos hkh, hx0], ?_⟩
        intro u hu
        rw [hk1] at hu ⊢
        rw [← Icc_union_Icc_eq_Icc hkh (by linarith : k * h ≤ k * h + h)]
        apply HasDerivWithinAt.union
        · by_cases hmem : u ∈ Icc 0 (k * h)
          · have h1 := (hx u hmem).congr_of_mem hWleft hmem
            rwa [← hWleft u hmem] at h1
          · apply HasFDerivWithinAt.of_notMem_closure
            rwa [closure_Icc]
        · by_cases hmem : u ∈ Icc (k * h) (k * h + h)
          · have h1 := (hz u hmem).congr_of_mem hWright hmem
            rwa [← hWright u hmem] at h1
          · apply HasFDerivWithinAt.of_notMem_closure
            rwa [closure_Icc]
  obtain ⟨x, hx0, hx⟩ := key N hN1 le_rfl
  refine ⟨x, hx0, ?_⟩
  intro u hu
  rw [← hNh] at hu ⊢
  exact hx u hu

/-- A path with a Lipschitz-type modulus `‖f u - f v‖ ≤ β |u - v|` on a set is
continuous on that set. -/
theorem continuousOn_of_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] (f : ℝ → E)
    {s : Set ℝ} {β : ℝ}
    (hf : ∀ u ∈ s, ∀ v ∈ s, ‖f u - f v‖ ≤ β * |u - v|) : ContinuousOn f s := by
  intro u hu
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  by_cases hβ : β ≤ 0
  · refine ⟨1, one_pos, fun v hv _ => ?_⟩
    rw [dist_eq_norm]
    have h := hf v hv u hu
    have : β * |v - u| ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hβ (abs_nonneg _)
    linarith [norm_nonneg (f v - f u)]
  · have hβ' : 0 < β := lt_of_not_ge hβ
    refine ⟨ε / β, div_pos hε hβ', fun v hv hvu => ?_⟩
    rw [dist_eq_norm]
    rw [Real.dist_eq] at hvu
    calc
      ‖f v - f u‖ ≤ β * |v - u| := hf v hv u hu
      _ < β * (ε / β) := mul_lt_mul_of_pos_left hvu hβ'
      _ = ε := by field_simp

theorem exists_solvesODE_of_lipschitz (G : ℝ → V →L[ℂ] V) (b : ℝ → V) {T βG βb : ℝ} (hT : 0 ≤ T)
    (hGLip : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖G u - G v‖ ≤ βG * |u - v|)
    (hbLip : ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖b u - b v‖ ≤ βb * |u - v|) (x0 : V) :
    ∃ x : ℝ → V, x 0 = x0 ∧ SolvesODE G b x 0 T :=
  exists_solvesODE G b hT (continuousOn_of_norm_sub_le G hGLip)
    (continuousOn_of_norm_sub_le b hbLip) x0

end

end SparseHamiltonian.TimeDependentODE
