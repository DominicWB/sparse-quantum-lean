import ODELowerBoundExtensions.Homogeneous.Data
import ODELowerBoundExtensions.Homogeneous.Generator

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The flag-extended joint index exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Proposition `odel:rem:homogeneous`: the explicit solution solves the family

Manuscript: the proof of Proposition `odel:rem:homogeneous`. The closed form `homSol` of
`ODELowerBoundExtensions.Homogeneous.Defs` solves the release's `SolvesODE` on each stage
(`ẋ = -G_k x`, no source), with the clamped ramps of
`SparseLowerBounds.Helpers.Ode.JointFamily.Solution` (`hasDerivWithinAt_ramp_below`,
`hasDerivWithinAt_ramp_mid`, `hasDerivWithinAt_ramp_above`) and the generator actions of
`ODELowerBoundExtensions.Homogeneous.Generator`:

* hidden stage `k` (`[kπ/2, (k+1)π/2]`): only `Φ_a` moves, with slope `(-1)^{j_{ak}}`
  (`hasDerivWithinAt_candPhase_stage`), so `β̇_a = -i(-1)^{j_{ak}} β_a`, `α̇_a = 0`;
* merged pulse (`[nπ/2, nπ/2 + pulseLen n]`): `β̇_a = i β_a`, `α̇_a = 0`;
* `Y` pulse (`[…, … + π/4]`): `α̇_a = -β_a`, `β̇_a = α_a` (rotation by `θ`);
* dissipation (`[…, homBusy M n]`): `α̇_a = -α_a`, `β̇_a = 0`;
* idle (`[homBusy M n, T]`): constant.

`homSol_solves` assembles them with the breakpoints of `ODELowerBoundExtensions.Homogeneous.Data`.
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian Set
open scoped InnerProductSpace

variable {M n μ s : ℕ}

/-! ### Derivatives of the coefficients -/

/-- A clamped ramp vanishes before its start. -/
theorem ramp_eq_zero {c L t : ℝ} (hL : 0 ≤ L) (ht : t ≤ c) : min (max (t - c) 0) L = 0 := by
  rw [max_eq_right (by linarith), min_eq_left hL]

section Deriv

variable {S : Set ℝ} {u : ℝ}

/-- Derivative of the flag-one phase coefficient `e^{-iΦ_a} e^{i clamp}`. -/
theorem hasDerivWithinAt_phaseCoeff (j : Positions M n (2 ^ μ)) (a : Fin M) {Φ' ρ' : ℝ}
    (hΦ : HasDerivWithinAt (candPhase j a) Φ' S u)
    (hρ : HasDerivWithinAt (fun t => min (max (t - n * (Real.pi / 2)) 0) (pulseLen n)) ρ' S u) :
    HasDerivWithinAt (phaseCoeff j a)
      (phaseCoeff j a u * (-Complex.I * (Φ' : ℂ) + Complex.I * (ρ' : ℂ))) S u := by
  have h := ((hΦ.ofReal_comp.const_mul (-Complex.I)).cexp).mul
    ((hρ.ofReal_comp.const_mul Complex.I).cexp)
  refine h.congr_deriv ?_
  simp only [phaseCoeff]
  ring

/-- Derivative of the flag-one coefficient `β_a = sin θ + cos θ · phaseCoeff`. -/
theorem hasDerivWithinAt_homBeta (j : Positions M n (2 ^ μ)) (a : Fin M) {θ' : ℝ} {P' : ℂ}
    (hθ : HasDerivWithinAt (yAngle n) θ' S u) (hP : HasDerivWithinAt (phaseCoeff j a) P' S u) :
    HasDerivWithinAt (homBeta j a)
      ((Real.cos (yAngle n u) : ℂ) * θ' - (Real.sin (yAngle n u) : ℂ) * θ' * phaseCoeff j a u +
        (Real.cos (yAngle n u) : ℂ) * P') S u := by
  have h := (hθ.sin.ofReal_comp).add ((hθ.cos.ofReal_comp).mul hP)
  refine h.congr_deriv ?_
  push_cast
  ring

/-- Derivative of the flag-zero coefficient `α_a = e^{-clamp} (cos θ - sin θ · phaseCoeff)`. -/
theorem hasDerivWithinAt_homAlpha (j : Positions M n (2 ^ μ)) (a : Fin M) {δ' θ' : ℝ} {P' : ℂ}
    (hδ : HasDerivWithinAt (dampTime M n) δ' S u) (hθ : HasDerivWithinAt (yAngle n) θ' S u)
    (hP : HasDerivWithinAt (phaseCoeff j a) P' S u) :
    HasDerivWithinAt (homAlpha j a)
      (-(δ' : ℂ) * homAlpha j a u + (Real.exp (-dampTime M n u) : ℂ) *
        (-(Real.sin (yAngle n u) : ℂ) * θ' - (Real.cos (yAngle n u) : ℂ) * θ' * phaseCoeff j a u -
          (Real.sin (yAngle n u) : ℂ) * P')) S u := by
  have h := ((hδ.neg.exp).ofReal_comp).mul
    ((hθ.cos.ofReal_comp).sub ((hθ.sin.ofReal_comp).mul hP))
  refine h.congr_deriv ?_
  simp only [homAlpha, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply]
  push_cast
  ring

/-- Derivative of `homSol` from those of its coefficients. -/
theorem hasDerivWithinAt_homSol (x : Promised M n (2 ^ μ)) (α' β' : Fin M → ℂ)
    (hα : ∀ a, HasDerivWithinAt (homAlpha x.1 a) (α' a) S u)
    (hβ : ∀ a, HasDerivWithinAt (homBeta x.1 a) (β' a) S u) :
    HasDerivWithinAt (homSol M n μ s x)
      (((Real.sqrt (2 * (M : ℝ)) : ℂ))⁻¹ •
        ∑ a, (α' a • flagCand M μ s false a + β' a • flagCand M μ s true a)) S u := by
  have h := (HasDerivWithinAt.fun_sum fun a (_ : a ∈ Finset.univ) =>
    ((hα a).smul_const (flagCand M μ s false a)).add
      ((hβ a).smul_const (flagCand M μ s true a))).const_smul
        ((Real.sqrt (2 * (M : ℝ)) : ℂ))⁻¹
  exact h

end Deriv

/-- A linear map applied to `homSol`, coefficient by coefficient. -/
theorem map_homSol
    (L : EuclideanSpace ℂ (HomIndex M μ s) →L[ℂ] EuclideanSpace ℂ (HomIndex M μ s))
    (x : Promised M n (2 ^ μ)) (t : ℝ) :
    L (homSol M n μ s x t) = ((Real.sqrt (2 * (M : ℝ)) : ℂ))⁻¹ •
      ∑ a, (homAlpha x.1 a t • L (flagCand M μ s false a) +
        homBeta x.1 a t • L (flagCand M μ s true a)) := by
  simp only [homSol, map_smul, map_sum, map_add]

/-! ### The stages -/

/-- The solution starts at `x₀` (all ramps vanish at `t = 0`). -/
theorem homSol_zero (x : Promised M n (2 ^ μ)) : homSol M n μ s x 0 = homInit M μ s := by
  have hπ := Real.pi_pos
  have hpl := pulseLen_nonneg n
  have hn : (0 : ℝ) ≤ n * (Real.pi / 2) := by positivity
  have hθ : yAngle n 0 = 0 := ramp_eq_zero (by positivity) (by linarith)
  have hδ : dampTime M n 0 = 0 := ramp_eq_zero (homD_nonneg M) (by linarith)
  have hP : ∀ a, phaseCoeff x.1 a 0 = 1 := fun a => by
    rw [phaseCoeff, candPhase_zero, ramp_eq_zero hpl hn]
    simp
  simp only [homSol, homInit, homAlpha, homBeta, hθ, hδ, hP]
  simp

/-- **Hidden stage `k < n`** (Proposition `odel:rem:homogeneous`, eq. `odel:eq:stages` controlled on
flag one). -/
theorem solvesODE_hom_hidden (hμ : 1 ≤ μ) (x : Promised M n (2 ^ μ)) (k : Fin (n + 4))
    (hk : (k : ℕ) < n) :
    TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator (homGen x.1 k))
      (fun _ => 0) (homSol M n μ s x) (((k : ℕ) : ℝ) * (Real.pi / 2))
      ((((k : ℕ) : ℝ) + 1) * (Real.pi / 2)) := by
  have hπ := Real.pi_pos
  have hkn : ((k : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hk
  have hpl := pulseLen_nonneg n
  have hD := homD_nonneg M
  intro u hu
  have hq : (((k : ℕ) : ℝ) + 1) * (Real.pi / 2) ≤ n * (Real.pi / 2) := by nlinarith
  have hθ0 : yAngle n u = 0 := ramp_eq_zero (by positivity) (by linarith [hu.2])
  have hθ : HasDerivWithinAt (yAngle n) 0 _ u :=
    hasDerivWithinAt_ramp_below (by positivity) (by linarith) hu
  have hδ : HasDerivWithinAt (dampTime M n) 0 _ u :=
    hasDerivWithinAt_ramp_below hD (by linarith) hu
  have hP := fun a => hasDerivWithinAt_phaseCoeff x.1 a
    (hasDerivWithinAt_candPhase_stage x.1 a ⟨k, hk⟩ hu) (hasDerivWithinAt_ramp_below hpl hq hu)
  have hd := hasDerivWithinAt_homSol (s := s) x _ _
    (fun a => hasDerivWithinAt_homAlpha x.1 a hδ hθ (hP a))
    (fun a => hasDerivWithinAt_homBeta x.1 a hθ (hP a))
  refine hd.congr_deriv ?_
  show _ = -(SparseStateOverlap.matrixOperator (homGen x.1 k) (homSol M n μ s x u)) + 0
  rw [map_homSol, add_zero, ← smul_neg, ← Finset.sum_neg_distrib]
  simp only [homGen_hidden_true hμ x.1 k hk, homGen_hidden_false x.1 k hk]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  match_scalars <;> simp [homBeta, hθ0]

/-- **The merged phase pulse** (Proposition `odel:rem:homogeneous`). -/
theorem solvesODE_hom_pulse (x : Promised M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n) :
    TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator (homGen x.1 k))
      (fun _ => 0) (homSol M n μ s x) (n * (Real.pi / 2))
      (n * (Real.pi / 2) + pulseLen n) := by
  have hπ := Real.pi_pos
  have hpl := pulseLen_nonneg n
  have hD := homD_nonneg M
  intro u hu
  have hθ0 : yAngle n u = 0 := ramp_eq_zero (by positivity) hu.2
  have hθ : HasDerivWithinAt (yAngle n) 0 _ u :=
    hasDerivWithinAt_ramp_below (by positivity) le_rfl hu
  have hδ : HasDerivWithinAt (dampTime M n) 0 _ u :=
    hasDerivWithinAt_ramp_below hD (by linarith) hu
  have hP := fun a => hasDerivWithinAt_phaseCoeff x.1 a
    (hasDerivWithinAt_candPhase_after x.1 a le_rfl hu) (hasDerivWithinAt_ramp_mid le_rfl le_rfl hu)
  have hd := hasDerivWithinAt_homSol (s := s) x _ _
    (fun a => hasDerivWithinAt_homAlpha x.1 a hδ hθ (hP a))
    (fun a => hasDerivWithinAt_homBeta x.1 a hθ (hP a))
  refine hd.congr_deriv ?_
  show _ = -(SparseStateOverlap.matrixOperator (homGen x.1 k) (homSol M n μ s x u)) + 0
  rw [map_homSol, add_zero, ← smul_neg, ← Finset.sum_neg_distrib]
  simp only [homGen_pulse x.1 k hk]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  match_scalars <;> simp [homBeta, hθ0]

/-- **The `Y` pulse** (Proposition `odel:rem:homogeneous`). -/
theorem solvesODE_hom_y (x : Promised M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 1) :
    TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator (homGen x.1 k))
      (fun _ => 0) (homSol M n μ s x) (n * (Real.pi / 2) + pulseLen n)
      (n * (Real.pi / 2) + pulseLen n + Real.pi / 4) := by
  have hπ := Real.pi_pos
  have hpl := pulseLen_nonneg n
  have hD := homD_nonneg M
  intro u hu
  have hδ0 : dampTime M n u = 0 := ramp_eq_zero hD hu.2
  have hθ : HasDerivWithinAt (yAngle n) 1 _ u := hasDerivWithinAt_ramp_mid le_rfl le_rfl hu
  have hδ : HasDerivWithinAt (dampTime M n) 0 _ u := hasDerivWithinAt_ramp_below hD le_rfl hu
  have hP := fun a => hasDerivWithinAt_phaseCoeff x.1 a
    (hasDerivWithinAt_candPhase_after x.1 a (by linarith) hu)
    (hasDerivWithinAt_ramp_above hpl le_rfl hu)
  have hd := hasDerivWithinAt_homSol (s := s) x _ _
    (fun a => hasDerivWithinAt_homAlpha x.1 a hδ hθ (hP a))
    (fun a => hasDerivWithinAt_homBeta x.1 a hθ (hP a))
  refine hd.congr_deriv ?_
  show _ = -(SparseStateOverlap.matrixOperator (homGen x.1 k) (homSol M n μ s x u)) + 0
  rw [map_homSol, add_zero, ← smul_neg, ← Finset.sum_neg_distrib]
  simp only [homGen_y x.1 k hk, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false,
    if_true]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  match_scalars
  · simp [homAlpha, homBeta, hδ0]
    ring
  · simp [homAlpha, hδ0]

/-- **The dissipation** (Proposition `odel:rem:homogeneous`). -/
theorem solvesODE_hom_damp (x : Promised M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 2) :
    TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator (homGen x.1 k))
      (fun _ => 0) (homSol M n μ s x) (n * (Real.pi / 2) + pulseLen n + Real.pi / 4)
      (homBusy M n) := by
  have hπ := Real.pi_pos
  have hpl := pulseLen_nonneg n
  intro u hu
  have hθ : HasDerivWithinAt (yAngle n) 0 _ u :=
    hasDerivWithinAt_ramp_above (by positivity) le_rfl hu
  have hδ : HasDerivWithinAt (dampTime M n) 1 _ u :=
    hasDerivWithinAt_ramp_mid le_rfl (le_of_eq rfl) hu
  have hP := fun a => hasDerivWithinAt_phaseCoeff x.1 a
    (hasDerivWithinAt_candPhase_after x.1 a (by linarith) hu)
    (hasDerivWithinAt_ramp_above hpl (by linarith) hu)
  have hd := hasDerivWithinAt_homSol (s := s) x _ _
    (fun a => hasDerivWithinAt_homAlpha x.1 a hδ hθ (hP a))
    (fun a => hasDerivWithinAt_homBeta x.1 a hθ (hP a))
  refine hd.congr_deriv ?_
  show _ = -(SparseStateOverlap.matrixOperator (homGen x.1 k) (homSol M n μ s x u)) + 0
  rw [map_homSol, add_zero, ← smul_neg, ← Finset.sum_neg_distrib]
  simp only [homGen_reject x.1 k hk]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  match_scalars <;> simp

/-- **The idle stage** (Proposition `odel:rem:homogeneous`). -/
theorem solvesODE_hom_idle (x : Promised M n (2 ^ μ)) (k : Fin (n + 4)) (hk : (k : ℕ) = n + 3)
    (T : ℝ) :
    TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator (homGen x.1 k))
      (fun _ => 0) (homSol M n μ s x) (homBusy M n) T := by
  have hπ := Real.pi_pos
  have hpl := pulseLen_nonneg n
  have hD := homD_nonneg M
  have hn : (0 : ℝ) ≤ n * (Real.pi / 2) := by positivity
  have hB : homBusy M n = n * (Real.pi / 2) + pulseLen n + Real.pi / 4 + homD M := rfl
  intro u hu
  have hθ : HasDerivWithinAt (yAngle n) 0 _ u :=
    hasDerivWithinAt_ramp_above (by positivity) (by linarith) hu
  have hδ : HasDerivWithinAt (dampTime M n) 0 _ u :=
    hasDerivWithinAt_ramp_above hD (le_of_eq hB.symm) hu
  have hP := fun a => hasDerivWithinAt_phaseCoeff x.1 a
    (hasDerivWithinAt_candPhase_after x.1 a (by linarith) hu)
    (hasDerivWithinAt_ramp_above hpl (by linarith) hu)
  have hd := hasDerivWithinAt_homSol (s := s) x _ _
    (fun a => hasDerivWithinAt_homAlpha x.1 a hδ hθ (hP a))
    (fun a => hasDerivWithinAt_homBeta x.1 a hθ (hP a))
  refine hd.congr_deriv ?_
  show _ = -(SparseStateOverlap.matrixOperator (homGen x.1 k) (homSol M n μ s x u)) + 0
  rw [homGen_idle x.1 k hk, Hamiltonian.matrixOperator_eq_toEuclideanCLM, map_zero]
  simp

/-- **`homSol` solves the homogeneous family** on every input. -/
theorem homSol_solves (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) {T : ℝ} (hT : homBusy M n ≤ T)
    (x : Promised M n (2 ^ μ)) :
    (homFamily M n μ s hμ hμs T hT).Solves x (homSol M n μ s x) := by
  refine ⟨homSol_zero x, fun k => ?_⟩
  have hk4 := k.2
  show TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator (homGen x.1 k))
    (fun _ => 0) (homSol M n μ s x) _ _
  rcases lt_or_ge (k : ℕ) n with h | h
  · rw [homFamily_start_hidden h.le, homFamily_start_hidden (by omega : (k : ℕ) + 1 ≤ n)]
    push_cast
    exact solvesODE_hom_hidden hμ x k h
  · obtain h' | h' | h' | h' :
        (k : ℕ) = n ∨ (k : ℕ) = n + 1 ∨ (k : ℕ) = n + 2 ∨ (k : ℕ) = n + 3 := by omega
    · rw [h', homFamily_start_hidden le_rfl, homFamily_start_y]
      exact solvesODE_hom_pulse x k h'
    · rw [show (k : ℕ) + 1 = n + 2 by omega, h', homFamily_start_y, homFamily_start_damp]
      exact solvesODE_hom_y x k h'
    · rw [show (k : ℕ) + 1 = n + 3 by omega, h', homFamily_start_damp, homFamily_start_idle]
      exact solvesODE_hom_damp x k h'
    · rw [show (k : ℕ) + 1 = n + 4 by omega, h', homFamily_start_idle]
      have hT' : (homFamily M n μ s hμ hμs T hT).start (n + 4) = T := homFamily_T
      rw [hT']
      exact solvesODE_hom_idle x k h' T

end

end ODELowerBoundExtensions.Homogeneous
