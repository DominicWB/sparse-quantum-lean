import GateEfficientSelect.ODE.Table

/-!
# The time discretisation of every branch on its own mesh

The exact target `targetB = ∑_s propB s (z_s)` of the circuit is compared with the solution
through the source certificate of Theorem `ode:thm:gates` (equation
`ode:eq:gate-source-certificates`): for every source label `s`, `y_s` solves the homogeneous
equation `y' = -G(u) y` on `[startB s, T]` from the source vector `y_s(startB s) = z_s`
(informally `y_s(T) = U(T, startB s) z_s` for the dissipative propagator `U` of the paper, which is
not a Lean object here), and the certificate bounds `‖x(T) - ∑_s y_s(T)‖`.

* `solvesODE_shift`: a solution on `[a, c]` is a solution on `[0, c - a]` of the shifted
  equation.
* `propB_eq`: the branch propagator is the ordered product of the frozen dissipative slot
  propagators on the branch mesh (the released masked propagator with start `0`).
* `branch_disc`: for an accretive `βG`-Lipschitz generator and samples with
  `‖G(addrB s r) - (Lb s r + i Hb s r)‖ ≤ δG`, the branch propagator is within
  `durB s (βG durB s / 2^m + δG) ‖z_s‖` of `y_s(T)` (the released
  `TimeDependentODE.mesh_error` on the shifted interval, without forcing).
* `target_errorB`: hence `‖x(T) - targetB‖ ≤ κ + T (βG T / 2^m + δG) B` for the certificate
  bound `κ` and the source mass `B`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE.Time (TParams gens slot_accretive)
open GateCircuit.SlotSim (clampAt clampAt_of_lt min_pred_lt evolution_eq_of_lt)
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- A solution on `[a, c]` is, shifted by `a`, a solution on `[0, c - a]`. -/
theorem solvesODE_shift {G : ℝ → P →L[ℂ] P} {b y : ℝ → P} {a c : ℝ}
    (h : SolvesODE G b y a c) :
    SolvesODE (fun t => G (a + t)) (fun t => b (a + t)) (fun t => y (a + t)) 0 (c - a) := by
  intro t ht
  have hmaps : Set.MapsTo (fun s : ℝ => a + s) (Set.Icc 0 (c - a)) (Set.Icc a c) := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hg : HasDerivWithinAt (fun s : ℝ => a + s) 1 (Set.Icc 0 (c - a)) t :=
    ((hasDerivAt_id' t).const_add a).hasDerivWithinAt
  have h1 := (h (a + t) (hmaps ht)).scomp t hg hmaps
  simpa only [one_smul, Function.comp_def] using h1

variable (p : TParams)

/-- The branch propagator is the ordered product of the frozen dissipative slot propagators
`exp (-(durB s / 2^m)(Lb s r + i Hb s r))` on the branch mesh. -/
theorem propB_eq (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) :
    propB p v Hb Lb s =
      TimeDependentODE.maskedPropagator (gens (Hb s) (Lb s)) (durB p v s / p.M) 0 p.M := by
  unfold propB TimeDependentODE.maskedPropagator
  rw [TimeDependentODE.GaussianLCHS.productFamily_neg_I]
  congr 1
  funext r
  rw [TimeDependentODE.mask_of_le (Nat.zero_le r), mul_one]
  rfl

/-- **The discretisation of one branch on its own mesh.** -/
theorem branch_disc (hT : 0 ≤ p.T) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (y : ℝ → P)
    (s : Bool × (Fin p.m → Bool)) (βG δG : ℝ) (hβG : 0 ≤ βG)
    (hy : SolvesODE G (fun _ => 0) y (startB p v s) p.T)
    (hG : ∀ u ∈ Set.Icc 0 p.T, Accretive (G u))
    (hGLip : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hGs : ∀ r < p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖ ≤ δG)
    (hH : ∀ r < p.M, star (Hb s r) = Hb s r)
    (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re) :
    ‖y p.T - propB p v Hb Lb s (y (startB p v s))‖ ≤
      durB p v s * (βG * (durB p v s / p.M) + δG) * ‖y (startB p v s)‖ := by
  have hcl := min_pred_lt p.M_pos
  have ha := startB_mem p v hv hT s
  have hu : 0 ≤ durB p v s := durB_nonneg p v hv hT s
  set a := startB p v s with ha_def
  have hdur : durB p v s = p.T - a := rfl
  have hsh := solvesODE_shift hy
  rw [← hdur] at hsh
  have hsub : ∀ t ∈ Set.Icc 0 (durB p v s), a + t ∈ Set.Icc 0 p.T := by
    intro t ht
    exact ⟨by linarith [ht.1, ha.1], by rw [hdur] at ht; linarith [ht.2]⟩
  set Gs := clampAt p.M (gens (Hb s) (Lb s)) with hGs_def
  have hGsacc : ∀ r, Accretive (Gs r) := fun r =>
    slot_accretive _ _ (hH _ (hcl r)) (hPSD _ (hcl r))
  have hΛ : ∀ r < p.M, ‖Gs r‖ ≤ ∑ q ∈ Finset.range p.M, ‖Gs q‖ := fun r hr =>
    Finset.single_le_sum (f := fun q => ‖Gs q‖) (fun q _ => norm_nonneg _)
      (Finset.mem_range.mpr hr)
  have hmesh := TimeDependentODE.mesh_error (G := fun t => G (a + t)) (b := fun _ => 0)
    (x := fun t => y (a + t)) (T := durB p v s) (M := p.M) hsh hu p.M_pos
    (fun t ht => hG _ (hsub t ht)) Gs hGsacc (fun _ => 0) βG δG 0 0 0
    (∑ q ∈ Finset.range p.M, ‖Gs q‖) 0 hβG le_rfl le_rfl
    (Finset.sum_nonneg (fun q _ => norm_nonneg _)) le_rfl
    (fun t ht t' ht' => by
      have h1 := hGLip _ (hsub t ht) _ (hsub t' ht')
      have e : a + t - (a + t') = t - t' := by ring
      rwa [e] at h1)
    (fun r hr => by
      rw [hGs_def, clampAt_of_lt _ _ hr]
      have h1 := hGs r hr
      unfold addrB at h1
      exact h1)
    (fun _ _ _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp) hΛ (fun _ _ => by simp)
  have hrec : TimeDependentODE.recurrence Gs (fun _ => 0) (durB p v s / p.M) (y (a + 0)) p.M =
      propB p v Hb Lb s (y a) := by
    rw [TimeDependentODE.recurrence_eq_sum]
    simp only [smul_zero, map_zero, Finset.sum_const_zero, add_zero]
    rw [propB_eq]
    congr 1
    unfold TimeDependentODE.maskedPropagator
    apply evolution_eq_of_lt
    intro r hr
    rw [hGs_def, clampAt_of_lt _ _ hr]
  have hend : a + durB p v s = p.T := by rw [hdur]; ring
  simp only [hend] at hmesh
  rw [hrec] at hmesh
  have e0 : a + 0 = a := add_zero a
  rw [e0] at hmesh
  calc ‖y p.T - propB p v Hb Lb s (y a)‖ ≤ durB p v s * ((βG * (durB p v s / p.M) + δG) *
        (‖y a‖ + 0 * durB p v s) + 0 * (durB p v s / p.M) + 0 +
        durB p v s / p.M * (∑ q ∈ Finset.range p.M, ‖Gs q‖) * 0) := hmesh
    _ = durB p v s * (βG * (durB p v s / p.M) + δG) * ‖y a‖ := by ring

/-- **The exact target against the solution.** With the source certificate
`‖x(T) - ∑_s y_s(T)‖ ≤ κ`, the exact target of the circuit is within
`κ + T (βG T / 2^m + δG) B` of `x(T)`, where `B` is the source mass. -/
theorem target_errorB (hT : 0 < p.T) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (x : ℝ → P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (wq : ℕ → ℝ) (fv : ℕ → P) (βG δG κ : ℝ)
    (hβG : 0 ≤ βG)
    (hys : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p v s) p.T)
    (hys0 : ∀ s, ys s (startB p v s) = p.zsrc (x 0) (bsW p wq fv) s)
    (hquad : ‖x p.T - ∑ s, ys s p.T‖ ≤ κ)
    (hG : ∀ u ∈ Set.Icc 0 p.T, Accretive (G u))
    (hGLip : ∀ u ∈ Set.Icc 0 p.T, ∀ u' ∈ Set.Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hGs : ∀ s, ∀ r < p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖ ≤ δG)
    (hH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r)
    (hPSD : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re) :
    ‖x p.T - targetB p v Hb Lb (x 0) wq fv‖ ≤
      κ + p.T * (βG * (p.T / p.M) + δG) * p.mass (x 0) (bsW p wq fv) := by
  have hδG : 0 ≤ δG :=
    (norm_nonneg _).trans (hGs (false, fun _ => false) 0 p.M_pos)
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hsplit : x p.T - targetB p v Hb Lb (x 0) wq fv =
      (x p.T - ∑ s, ys s p.T) +
        ∑ s, (ys s p.T - propB p v Hb Lb s (ys s (startB p v s))) := by
    unfold targetB
    simp only [hys0]
    rw [Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  have hbr : ∀ s, ‖ys s p.T - propB p v Hb Lb s (ys s (startB p v s))‖ ≤
      p.T * (βG * (p.T / p.M) + δG) * ‖p.zsrc (x 0) (bsW p wq fv) s‖ := by
    intro s
    rw [hys0]
    have h := branch_disc p hT.le v hv Hb Lb G (ys s) s βG δG hβG (hys s) hG hGLip (hGs s)
      (hH s) (hPSD s)
    rw [hys0] at h
    have hu := durB_nonneg p v hv hT.le s
    have huT := durB_le p v hv hT.le s
    have hk : durB p v s * (βG * (durB p v s / p.M) + δG) ≤ p.T * (βG * (p.T / p.M) + δG) := by
      have h1 : durB p v s / p.M ≤ p.T / p.M := div_le_div_of_nonneg_right huT hMR.le
      have h2 : βG * (durB p v s / p.M) + δG ≤ βG * (p.T / p.M) + δG := by
        have := mul_le_mul_of_nonneg_left h1 hβG
        linarith
      exact mul_le_mul huT h2 (add_nonneg (mul_nonneg hβG (div_nonneg hu hMR.le)) hδG) hT.le
    exact h.trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
  calc ‖(x p.T - ∑ s, ys s p.T) +
        ∑ s, (ys s p.T - propB p v Hb Lb s (ys s (startB p v s)))‖ ≤
      ‖x p.T - ∑ s, ys s p.T‖ +
        ∑ s, ‖ys s p.T - propB p v Hb Lb s (ys s (startB p v s))‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ κ + ∑ s, p.T * (βG * (p.T / p.M) + δG) * ‖p.zsrc (x 0) (bsW p wq fv) s‖ :=
        add_le_add hquad (Finset.sum_le_sum (fun s _ => hbr s))
    _ = κ + p.T * (βG * (p.T / p.M) + δG) * p.mass (x 0) (bsW p wq fv) := by
        rw [← Finset.mul_sum]
        rfl

end

end SparseHamiltonian.GateSelect.ODE
