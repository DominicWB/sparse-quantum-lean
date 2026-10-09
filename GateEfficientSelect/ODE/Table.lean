import GateEfficientSelect.ODE.Branch

/-!
# LCHS on branch-dependent meshes and the exact target

Above the real axis the ordered product family of the branch of the source label `s` grows at
most like `exp (durB s λD Im z) ≤ exp (T λD Im z)`: the released growth bound
`GateODE.Time.productFamily_norm_le_exp`, with the durations of the branch summing to
`durB s ≤ T`. The released analytic Gaussian grid with growth constant `T λD` therefore
certifies every branch at once (`lchs_errorB`): the padded LCHS sum of the branch evolutions is
within `2 ν` of the dissipative branch propagator `propB s`.

Every branch propagator is a contraction (`propB_norm_le`), so the exact target is at most the
source mass (`targetB_norm_le`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (Label)
open GateODE.Time (TParams)
open GateCircuit.SlotSim (clampAt clampAt_of_lt min_pred_lt evolution_eq_of_lt)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

variable (p : TParams)

/-- The ordered product family of the branch of a source label, for clamped samples. -/
def familyB (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) : ℂ → P →L[ℂ] P :=
  TimeDependentODE.GaussianLCHS.productFamily (clampAt p.M (Hb s)) (clampAt p.M (Lb s))
    (stepB p v s) p.M

theorem familyB_ofReal (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) (w : Fin p.l → Bool) :
    familyB p v Hb Lb s (p.nodeW w : ℂ) = branchUB p v Hb Lb s w := by
  unfold familyB branchUB TimeDependentODE.GaussianLCHS.productFamily
  apply evolution_eq_of_lt
  intro r hr
  rw [clampAt_of_lt p.M (Hb s) hr, clampAt_of_lt p.M (Lb s) hr]

theorem familyB_neg_I (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) : familyB p v Hb Lb s (-Complex.I) = propB p v Hb Lb s := by
  unfold familyB propB TimeDependentODE.GaussianLCHS.productFamily
  apply evolution_eq_of_lt
  intro r hr
  rw [clampAt_of_lt p.M (Hb s) hr, clampAt_of_lt p.M (Lb s) hr]

/-- **Finite LCHS for every source label on its own mesh.** -/
theorem lchs_errorB (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hlamD : 0 ≤ p.lamD) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (hH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r) (hL : ∀ s, ∀ r < p.M, star (Lb s r) = Lb s r)
    (hLn : ∀ s, ∀ r < p.M, ‖Lb s r‖ ≤ p.lamD)
    (hPSD : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re)
    (s : Bool × (Fin p.m → Bool)) :
    ‖(∑ w, p.coeffW w • branchUB p v Hb Lb s w) - propB p v Hb Lb s‖ ≤ 2 * p.nu := by
  have hcl := min_pred_lt p.M_pos
  have hTD : 0 ≤ p.T * p.lamD := mul_nonneg hT hlamD
  have hcert := GateODE.AnalyticLCHS.table_certificate (V := P) (familyB p v Hb Lb)
    (fun s z => TimeDependentODE.GaussianLCHS.productFamily_analyticAt _ _ _ _ z)
    (fun s z hz => TimeDependentODE.GaussianLCHS.productFamily_norm_le_one _ _ _ _
      (fun r => hH s _ (hcl r)) (fun r => hL s _ (hcl r)) (fun r => hPSD s _ (hcl r))
      (fun r => stepB_nonneg p v hv hT s r) z hz)
    (p.T * p.lamD) hTD
    (fun s z hz => (GateODE.Time.productFamily_norm_le_exp _ _ _ p.lamD p.M
      (fun r _ => hH s _ (hcl r)) (fun r _ => hL s _ (hcl r)) (fun r _ => hLn s _ (hcl r))
      (fun r _ => stepB_nonneg p v hv hT s r) z hz).trans (Real.exp_le_exp.mpr (by
        rw [sum_stepB]
        have hsum := durB_le p v hv hT s
        have hc : 0 ≤ p.lamD * z.im := mul_nonneg hlamD hz
        calc durB p v s * (p.lamD * z.im) ≤ p.T * (p.lamD * z.im) :=
              mul_le_mul_of_nonneg_right hsum hc
          _ = p.T * p.lamD * z.im := by ring)))
    p.ratio p.acc (p.ratio_ge hg) (p.acc_pos hε) (p.acc_le_one hεOne)
  have hsum : ∑ w, p.coeffW w • branchUB p v Hb Lb s w =
      ∑ i, GateODE.AnalyticLCHS.coefficients (p.T * p.lamD) p.ratio p.acc i •
        familyB p v Hb Lb s (GateODE.AnalyticLCHS.nodes (p.T * p.lamD) p.ratio p.acc i : ℂ) := by
    rw [← p.coeffW_sum (fun k => familyB p v Hb Lb s (k : ℂ))]
    simp only [familyB_ofReal]
  rw [hsum, ← familyB_neg_I]
  exact hcert.2.2.2 s

/-- Every branch propagator is a contraction. -/
theorem propB_norm_le (hT : 0 ≤ p.T) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool))
    (hH : ∀ r < p.M, star (Hb s r) = Hb s r) (hL : ∀ r < p.M, star (Lb s r) = Lb s r)
    (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re) :
    ‖propB p v Hb Lb s‖ ≤ 1 := by
  have hcl := min_pred_lt p.M_pos
  rw [← familyB_neg_I]
  exact TimeDependentODE.GaussianLCHS.productFamily_norm_le_one _ _ _ _
    (fun r => hH _ (hcl r)) (fun r => hL _ (hcl r)) (fun r => hPSD _ (hcl r))
    (fun r => stepB_nonneg p v hv hT s r) (-Complex.I) (by simp)

/-- The exact target is at most the source mass. -/
theorem targetB_norm_le (hT : 0 ≤ p.T) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (hH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r) (hL : ∀ s, ∀ r < p.M, star (Lb s r) = Lb s r)
    (hPSD : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re)
    (x0 : P) (wq : ℕ → ℝ) (fv : ℕ → P) :
    ‖targetB p v Hb Lb x0 wq fv‖ ≤ p.mass x0 (bsW p wq fv) := by
  unfold targetB GateODE.Time.TParams.mass ODESourceBranches.mass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  have hn := propB_norm_le p hT v hv Hb Lb s (hH s) (hL s) (hPSD s)
  calc ‖propB p v Hb Lb s (p.zsrc x0 (bsW p wq fv) s)‖ ≤
      ‖propB p v Hb Lb s‖ * ‖p.zsrc x0 (bsW p wq fv) s‖ := le_opNorm _ _
    _ ≤ 1 * ‖p.zsrc x0 (bsW p wq fv) s‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = ‖p.zsrc x0 (bsW p wq fv) s‖ := one_mul _

end

end SparseHamiltonian.GateSelect.ODE
