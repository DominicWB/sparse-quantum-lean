import GateEfficientBinaryNodes.Core
import GateEfficientSelect.ODE.Left

/-!
# The integrated sample-error certificate on branch-dependent meshes

Lemma `ode:lem:gate-select` requires of the represented samples at the addresses
`v_z + r u_z/M` of a branch that "their certified total operator-norm error, integrated over the
selected interval, is at most `δ/16`". The released dissipative solvers on branch-dependent
meshes (`GateSelect.ODE.BInstanceOK`) bound every sample error uniformly by `δG`. Here the
generator samples of the solvers satisfy the integrated certificate instead.

* `sampleErrB p v Hb Lb G s = (u_s/2^m) ∑_{r < 2^m} ‖G(a_r) - (Lb s r + i Hb s r)‖`, with the
  addresses `a_r = addrB p v s r = v_s + r u_s/2^m` and the duration `u_s = durB p v s`: the
  represented-sample error of the branch of `s`, integrated over `[v_s, T]` (the slot-weighted
  sum); `sampleErrB_le_of_uniform`: at most `T δG` under a uniform bound `δG`.
* `homog_discI`: a solution of `y' = -G(u) y` on `[a, c]` against the ordered product of the
  frozen sample propagators on `n` equal slots, within
  `(βG (c-a)²/n + ((c-a)/n) ∑_r ‖G(a + r (c-a)/n) - Gs r‖) ‖y(a)‖` (the released one-step
  estimate `TimeDependentODE.step_error`, slot by slot).
* `branch_discI`, `target_errorBI`: one branch is within `(βG u_s²/2^m + sampleErrB s) ‖z_s‖` of
  its homogeneous solution, and the exact target within `κ + (βG T²/2^m + δI) B` of `x(T)` when
  `sampleErrB s ≤ δI` for every branch.
* `BInstanceOKI`: the conditions of `BInstanceOK` with the uniform sample bound replaced by the
  integrated certificate `sampleErrB s ≤ δI` and the budget by
  `κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`; `BInstanceOK.toI`: every released instance is one,
  with `δI = T δG` and the same budget.
* `native_time_outcomeBI`, `native_ode_time_solverBI`, `native_time_trials_outcomeBI`: the
  guarantees `NOutcome` of the released native protocol and of the native protocol on the
  synthesised preparation, for every instance satisfying `BInstanceOKI`.
* `LInstanceOKI`, `LInstanceOKI.toBI`: the same for the left-endpoint quadrature with the source
  certificate of `GateEfficientQuadrature`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE (Label ClockPromise)
open GateODE.Time (TParams TOracles gens slot_accretive)
open GateSelect.ODE (startB durB addrB branchHB propB bsW targetB BInstanceOK startB_mem
  durB_nonneg durB_le propB_eq maskedPropagator_eq_shift)
open GateQuad (vQ wQ quadMass)
open GatePointerEncoding (wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open Set (Icc)
open scoped InnerProduct BigOperators

/-! ### One homogeneous solution against frozen samples -/

section Homog

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- A solution of the homogeneous equation with an accretive generator does not grow. -/
theorem homog_norm_le {G : ℝ → P →L[ℂ] P} {y : ℝ → P} {a c : ℝ} (hac : a ≤ c)
    (hy : SolvesODE G (fun _ => 0) y a c) (hG : ∀ u ∈ Icc a c, Accretive (G u)) :
    ∀ u ∈ Icc a c, ‖y u‖ ≤ ‖y a‖ := by
  intro u hu
  have hsh := GateSelect.ODE.solvesODE_shift hy
  have h := TimeDependentODE.SolvesODE.norm_le hsh (sub_nonneg.mpr hac)
    (fun t ht => hG (a + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩) 0
    (fun _ _ => by simp) (u - a) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have e1 : a + (u - a) = u := by ring
  have e2 : a + 0 = a := add_zero a
  simp only [e1, e2, zero_mul, add_zero] at h
  exact h

/-- **A homogeneous solution against frozen samples, integrated sample error.** For a solution
of `y' = -G(u) y` on `[a, c]`, an accretive `βG`-Lipschitz generator and accretive samples
`Gs r`, the ordered product of the frozen propagators `exp (-((c - a)/n) Gs r)` on `n` equal
slots is within `(βG (c-a)²/n + ((c-a)/n) ∑_r ‖G(a + r (c-a)/n) - Gs r‖) ‖y(a)‖` of `y(c)`. -/
theorem homog_discI (G : ℝ → P →L[ℂ] P) (y : ℝ → P) (a c : ℝ) (hac : a ≤ c) (n : ℕ)
    (hn : 0 < n) (Gs : ℕ → P →L[ℂ] P) (βG : ℝ) (hβG : 0 ≤ βG)
    (hy : SolvesODE G (fun _ => 0) y a c)
    (hG : ∀ u ∈ Icc a c, Accretive (G u))
    (hGLip : ∀ u ∈ Icc a c, ∀ u' ∈ Icc a c, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hacc : ∀ r < n, Accretive (Gs r)) :
    ‖y c - TimeDependent.evolution (fun r => NormedSpace.exp (((c - a) / n) • (-Gs r))) n
        (y a)‖ ≤
      (βG * (c - a) ^ 2 / n +
        (c - a) / n * ∑ r ∈ Finset.range n, ‖G (a + r * (c - a) / n) - Gs r‖) * ‖y a‖ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set Δ := (c - a) / n with hΔ
  have hΔ0 : 0 ≤ Δ := div_nonneg (sub_nonneg.mpr hac) hnR.le
  set pt : ℕ → ℝ := fun k => a + k * Δ with hpt
  have hpt_eq : ∀ r : ℕ, a + r * (c - a) / n = pt r := by
    intro r
    simp only [hpt, hΔ]
    ring
  have hptn : pt n = c := by
    simp only [hpt, hΔ]
    field_simp
    ring
  have hpt_le : ∀ k ≤ n, pt k ≤ c := by
    intro k hk
    rw [← hptn]
    simp only [hpt]
    have : (k : ℝ) ≤ n := by exact_mod_cast hk
    nlinarith
  have hpt_ge : ∀ k, a ≤ pt k := by
    intro k
    simp only [hpt]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hnorm := homog_norm_le hac hy hG
  set U : ℕ → P →L[ℂ] P := fun r => NormedSpace.exp (Δ • (-Gs r)) with hU
  set δ : ℕ → ℝ := fun r => ‖G (pt r) - Gs r‖ with hδ
  have key : ∀ k ≤ n, ‖y (pt k) - TimeDependent.evolution U k (y a)‖ ≤
      ∑ r ∈ Finset.range k, (βG * Δ + δ r) * Δ * ‖y a‖ := by
    intro k
    induction k with
    | zero =>
        intro _
        simp [hpt]
    | succ k ih =>
        intro hk
        have hkn : k < n := by omega
        have ih' := ih hkn.le
        rw [TimeDependent.evolution_succ, Finset.sum_range_succ]
        have hsplit : y (pt (k + 1)) - (U k * TimeDependent.evolution U k) (y a) =
            (y (pt (k + 1)) - U k (y (pt k))) +
              U k (y (pt k) - TimeDependent.evolution U k (y a)) := by
          change y (pt (k + 1)) - U k (TimeDependent.evolution U k (y a)) = _
          rw [map_sub]
          abel
        rw [hsplit]
        have hle : pt k ≤ pt (k + 1) := by
          simp only [hpt]
          push_cast
          linarith
        have hdiff : pt (k + 1) - pt k = Δ := by
          simp only [hpt]
          push_cast
          ring
        have hstep : ‖y (pt (k + 1)) - U k (y (pt k))‖ ≤ (βG * Δ + δ k) * ‖y a‖ * Δ := by
          have hs := TimeDependentODE.step_error (hy.mono (hpt_ge k) (hpt_le (k + 1) hk)) hle
            (Gs k) (hacc k hkn) 0 ((βG * Δ + δ k) * ‖y a‖) (by
              intro u hu
              have huI : u ∈ Icc a c := ⟨(hpt_ge k).trans hu.1, hu.2.trans (hpt_le (k + 1) hk)⟩
              have hkI : pt k ∈ Icc a c := ⟨hpt_ge k, hpt_le k hkn.le⟩
              have h1 : ‖Gs k - G u‖ ≤ δ k + βG * Δ := by
                calc ‖Gs k - G u‖ = ‖(G (pt k) - G u) - (G (pt k) - Gs k)‖ := by
                      congr 1
                      abel
                  _ ≤ ‖G (pt k) - G u‖ + ‖G (pt k) - Gs k‖ := norm_sub_le _ _
                  _ ≤ βG * |pt k - u| + δ k := add_le_add (hGLip _ hkI _ huI) le_rfl
                  _ ≤ βG * Δ + δ k := by
                      have habs : |pt k - u| ≤ Δ := by
                        rw [abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]
                        linarith [hu.2]
                      have := mul_le_mul_of_nonneg_left habs hβG
                      linarith
                  _ = δ k + βG * Δ := by ring
              have h2 : ‖y u‖ ≤ ‖y a‖ := hnorm u huI
              have hδk : 0 ≤ δ k := norm_nonneg _
              have h3 : ‖Gs k - G u‖ * ‖y u‖ ≤ (βG * Δ + δ k) * ‖y a‖ := by
                calc ‖Gs k - G u‖ * ‖y u‖ ≤ (δ k + βG * Δ) * ‖y a‖ :=
                      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
                  _ = (βG * Δ + δ k) * ‖y a‖ := by ring
              simpa using h3)
          rw [hdiff, smul_zero, add_zero] at hs
          exact hs
        have hEk : ‖U k‖ ≤ 1 :=
          TimeDependentODE.accretive_exp_norm_le_one (Gs k) (hacc k hkn) Δ hΔ0
        calc ‖(y (pt (k + 1)) - U k (y (pt k))) +
              U k (y (pt k) - TimeDependent.evolution U k (y a))‖
            ≤ ‖y (pt (k + 1)) - U k (y (pt k))‖ +
                ‖U k (y (pt k) - TimeDependent.evolution U k (y a))‖ := norm_add_le _ _
          _ ≤ (βG * Δ + δ k) * ‖y a‖ * Δ +
                ‖U k‖ * ‖y (pt k) - TimeDependent.evolution U k (y a)‖ :=
              add_le_add hstep (le_opNorm _ _)
          _ ≤ (βG * Δ + δ k) * ‖y a‖ * Δ +
                1 * ∑ r ∈ Finset.range k, (βG * Δ + δ r) * Δ * ‖y a‖ :=
              add_le_add le_rfl (mul_le_mul hEk ih' (norm_nonneg _) zero_le_one)
          _ = ∑ r ∈ Finset.range k, (βG * Δ + δ r) * Δ * ‖y a‖ +
                (βG * Δ + δ k) * Δ * ‖y a‖ := by ring
  have h := key n le_rfl
  rw [hptn] at h
  have hsum : ∑ r ∈ Finset.range n, (βG * Δ + δ r) * Δ * ‖y a‖ =
      ((n : ℝ) * (βG * Δ * Δ) + Δ * ∑ r ∈ Finset.range n, δ r) * ‖y a‖ := by
    have h1 : ∀ r, (βG * Δ + δ r) * Δ * ‖y a‖ = βG * Δ * Δ * ‖y a‖ + Δ * ‖y a‖ * δ r :=
      fun r => by ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring
  have hn2 : (n : ℝ) * (βG * Δ * Δ) = βG * (c - a) ^ 2 / n := by
    simp only [hΔ]
    field_simp
  have hsumδ : ∑ r ∈ Finset.range n, δ r =
      ∑ r ∈ Finset.range n, ‖G (a + r * (c - a) / n) - Gs r‖ := by
    apply Finset.sum_congr rfl
    intro r _
    simp only [hδ, hpt_eq]
  rw [hsum, hn2, hsumδ] at h
  exact h

end Homog

/-! ### One branch and the exact target -/

section Branch

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable (p : TParams)

/-- **The integrated represented-sample error of a branch**: the errors of the represented slot
generators `Lb s r + i Hb s r` against the generator path at the branch addresses, weighted by
the slot length `u_s/2^m` of the branch of `s` (the error integrated over `[v_s, T]`). -/
def sampleErrB (v : ℕ → ℝ) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P)
    (G : ℝ → P →L[ℂ] P) (s : Bool × (Fin p.m → Bool)) : ℝ :=
  durB p v s / p.M * ∑ r ∈ Finset.range p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖

omit [CompleteSpace P] in
theorem sampleErrB_nonneg (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T) (hT : 0 ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) : 0 ≤ sampleErrB p v Hb Lb G s :=
  mul_nonneg (div_nonneg (durB_nonneg p v hv hT s) (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

omit [CompleteSpace P] in
/-- **The integrated certificate from a uniform bound**: if every sample error of the branch is
at most `δG`, the integrated error is at most `u_s δG ≤ T δG`. -/
theorem sampleErrB_le_of_uniform (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (hT : 0 ≤ p.T) (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P)
    (s : Bool × (Fin p.m → Bool)) (δG : ℝ)
    (h : ∀ r < p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖ ≤ δG) :
    sampleErrB p v Hb Lb G s ≤ p.T * δG := by
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hδ : 0 ≤ δG := (norm_nonneg _).trans (h 0 p.M_pos)
  have hu := durB_nonneg p v hv hT s
  have huT := durB_le p v hv hT s
  have hsum : ∑ r ∈ Finset.range p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖ ≤ p.M * δG := by
    calc ∑ r ∈ Finset.range p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖
        ≤ ∑ _r ∈ Finset.range p.M, δG :=
          Finset.sum_le_sum (fun r hr => h r (Finset.mem_range.mp hr))
      _ = p.M * δG := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold sampleErrB
  calc durB p v s / p.M * ∑ r ∈ Finset.range p.M, ‖G (addrB p v s r) - gens (Hb s) (Lb s) r‖
      ≤ durB p v s / p.M * (p.M * δG) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hu hMR.le)
    _ = durB p v s * δG := by field_simp
    _ ≤ p.T * δG := mul_le_mul_of_nonneg_right huT hδ

/-- **The discretisation of one branch with the integrated certificate.** For the homogeneous
solution `y` of the branch of `s` on `[v_s, T]`, an accretive `βG`-Lipschitz generator and the
represented samples (self-adjoint `Hb`, accretive `Lb`), the branch propagator is within
`(βG u_s²/2^m + sampleErrB s) ‖y(v_s)‖` of `y(T)`. -/
theorem branch_discI (hT : 0 ≤ p.T) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (y : ℝ → P)
    (s : Bool × (Fin p.m → Bool)) (βG : ℝ) (hβG : 0 ≤ βG)
    (hy : SolvesODE G (fun _ => 0) y (startB p v s) p.T)
    (hG : ∀ u ∈ Icc 0 p.T, Accretive (G u))
    (hGLip : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hH : ∀ r < p.M, star (Hb s r) = Hb s r)
    (hPSD : ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re) :
    ‖y p.T - propB p v Hb Lb s (y (startB p v s))‖ ≤
      (βG * durB p v s ^ 2 / p.M + sampleErrB p v Hb Lb G s) * ‖y (startB p v s)‖ := by
  have ha := startB_mem p v hv hT s
  have hsub : ∀ u ∈ Icc (startB p v s) p.T, u ∈ Icc 0 p.T :=
    fun u hu => ⟨ha.1.trans hu.1, hu.2⟩
  have h := homog_discI G y (startB p v s) p.T ha.2 p.M p.M_pos (gens (Hb s) (Lb s)) βG hβG hy
    (fun u hu => hG u (hsub u hu))
    (fun u hu u' hu' => hGLip u (hsub u hu) u' (hsub u' hu'))
    (fun r hr => slot_accretive _ _ (hH r hr) (hPSD r hr))
  have hprop : propB p v Hb Lb s = TimeDependent.evolution
      (fun r => NormedSpace.exp (((p.T - startB p v s) / p.M) • (-gens (Hb s) (Lb s) r))) p.M := by
    rw [propB_eq, maskedPropagator_eq_shift _ _ 0 p.M (Nat.zero_le _)]
    simp only [zero_add, Nat.sub_zero]
    rfl
  rw [hprop]
  exact h

/-- **The exact target against the solution, integrated certificate.** With the source
certificate `‖x_T - ∑_s y_s(T)‖ ≤ κ` and the integrated certificates `sampleErrB s ≤ δI`, the
exact target of the circuit is within `κ + (βG T²/2^m + δI) B` of `x_T`, where `B` is the source
mass. -/
theorem target_errorBI (hT : 0 < p.T) (v : ℕ → ℝ) (hv : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (x0 xT : P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (wq : ℕ → ℝ) (fv : ℕ → P) (βG δI κ : ℝ)
    (hβG : 0 ≤ βG)
    (hys : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p v s) p.T)
    (hys0 : ∀ s, ys s (startB p v s) = p.zsrc x0 (bsW p wq fv) s)
    (hquad : ‖xT - ∑ s, ys s p.T‖ ≤ κ)
    (hG : ∀ u ∈ Icc 0 p.T, Accretive (G u))
    (hGLip : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|)
    (hI : ∀ s, sampleErrB p v Hb Lb G s ≤ δI)
    (hH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r)
    (hPSD : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re) :
    ‖xT - targetB p v Hb Lb x0 wq fv‖ ≤
      κ + (βG * p.T ^ 2 / p.M + δI) * p.mass x0 (bsW p wq fv) := by
  have hMR : (0 : ℝ) < p.M := by exact_mod_cast p.M_pos
  have hsplit : xT - targetB p v Hb Lb x0 wq fv =
      (xT - ∑ s, ys s p.T) +
        ∑ s, (ys s p.T - propB p v Hb Lb s (ys s (startB p v s))) := by
    unfold targetB
    simp only [hys0]
    rw [Finset.sum_sub_distrib]
    abel
  rw [hsplit]
  have hbr : ∀ s, ‖ys s p.T - propB p v Hb Lb s (ys s (startB p v s))‖ ≤
      (βG * p.T ^ 2 / p.M + δI) * ‖p.zsrc x0 (bsW p wq fv) s‖ := by
    intro s
    have h := branch_discI p hT.le v hv Hb Lb G (ys s) s βG hβG (hys s) hG hGLip (hH s)
      (hPSD s)
    rw [hys0] at h ⊢
    have hu := durB_nonneg p v hv hT.le s
    have huT := durB_le p v hv hT.le s
    have hk : βG * durB p v s ^ 2 / p.M + sampleErrB p v Hb Lb G s ≤
        βG * p.T ^ 2 / p.M + δI := by
      have h2 : durB p v s ^ 2 ≤ p.T ^ 2 := pow_le_pow_left₀ hu huT 2
      have h3 : βG * durB p v s ^ 2 / p.M ≤ βG * p.T ^ 2 / p.M :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hβG) hMR.le
      linarith [hI s]
    exact h.trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
  calc ‖(xT - ∑ s, ys s p.T) +
        ∑ s, (ys s p.T - propB p v Hb Lb s (ys s (startB p v s)))‖ ≤
      ‖xT - ∑ s, ys s p.T‖ +
        ∑ s, ‖ys s p.T - propB p v Hb Lb s (ys s (startB p v s))‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ κ + ∑ s, (βG * p.T ^ 2 / p.M + δI) * ‖p.zsrc x0 (bsW p wq fv) s‖ :=
        add_le_add hquad (Finset.sum_le_sum (fun s _ => hbr s))
    _ = κ + (βG * p.T ^ 2 / p.M + δI) * p.mass x0 (bsW p wq fv) := by
        rw [← Finset.mul_sum]
        rfl

end Branch

/-! ### The instance conditions with the integrated certificate -/

section Instance

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable (p : TParams)

/-- **The conditions on an instance with the integrated sample-error certificate**: those of
`GateSelect.ODE.BInstanceOK`, with the uniform sample bound replaced by the integrated
certificate `sampleErrB s ≤ δI` of every branch and the budget by
`κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`. -/
structure BInstanceOKI (v₀ : P) (σ : TOracles p.a p.m p.l P) (v wq : ℕ → ℝ) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δI κ : ℝ) : Prop where
  uj : IsUnitary σ.UJ
  priv : ∀ z, ∀ r < p.M, IsUnitary (σ.D z r)
  clock : ∀ z, ∀ r < p.M, ClockPromise σ.UJ (σ.D z r) (branchHB p v Hb Lb z r) p.Q p.qbar
  selfH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r
  selfL : ∀ s, ∀ r < p.M, star (Lb s r) = Lb s r
  normH : ∀ s, ∀ r < p.M, ‖Hb s r‖ ≤ p.lamH
  normL : ∀ s, ∀ r < p.M, ‖Lb s r‖ ≤ p.lamD
  psd : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re
  nodes : ∀ q < p.M, 0 ≤ v q ∧ v q ≤ p.T
  weights : ∀ q < p.M, 0 ≤ wq q
  load_unitary : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1
  prep : p.WpPromise σ (x 0) (bsW p wq fv)
  init_load : x 0 ≠ 0 → σ.J (false, fun _ => false) v₀ = unitDirection (x 0)
  forcing_load : ∀ w : Fin p.m → Bool, wq (wordValue w) ≠ 0 → fv (wordValue w) ≠ 0 →
    σ.J (true, w) v₀ = unitDirection (fv (wordValue w))
  solves : SolvesODE G b x 0 p.T
  accretive : ∀ u ∈ Icc 0 p.T, Accretive (G u)
  lipG : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleI : ∀ s, sampleErrB p v Hb Lb G s ≤ δI
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p v s) p.T
  branch_init : ∀ s, ys s (startB p v s) = p.zsrc (x 0) (bsW p wq fv) s
  quad : ‖x p.T - ∑ s, ys s p.T‖ ≤ κ
  target_ne : x p.T ≠ 0
  budget : p.mass (x 0) (bsW p wq fv) ≤ p.g * ‖x p.T‖
  disc : κ + (βG * p.T ^ 2 / p.M + δI) * p.mass (x 0) (bsW p wq fv) ≤
    p.ε * p.mass (x 0) (bsW p wq fv) / (2000 * p.g)

variable {p}
variable {v₀ : P} {σ : TOracles p.a p.m p.l P} {v wq : ℕ → ℝ} {fv : ℕ → P}
  {Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P} {b x : ℝ → P}
  {ys : Bool × (Fin p.m → Bool) → ℝ → P}

/-- **Every released instance satisfies the integrated conditions**, with `δI = T δG` and the
same budget `κ + T (βG T/2^m + δG) B`. -/
theorem BInstanceOK.toI (hp : p.PublicOK) {βG δG κ : ℝ}
    (hI : BInstanceOK p v₀ σ v wq fv Hb Lb G b x ys βG δG κ) :
    BInstanceOKI p v₀ σ v wq fv Hb Lb G b x ys βG (p.T * δG) κ where
  uj := hI.uj
  priv := hI.priv
  clock := hI.clock
  selfH := hI.selfH
  selfL := hI.selfL
  normH := hI.normH
  normL := hI.normL
  psd := hI.psd
  nodes := hI.nodes
  weights := hI.weights
  load_unitary := hI.load_unitary
  prep_left := hI.prep_left
  prep_right := hI.prep_right
  prep := hI.prep
  init_load := hI.init_load
  forcing_load := hI.forcing_load
  solves := hI.solves
  accretive := hI.accretive
  lipG := hI.lipG
  βG_nonneg := hI.βG_nonneg
  sampleI s := sampleErrB_le_of_uniform p v hI.nodes hp.T_pos.le Hb Lb G s δG (hI.sampleG s)
  branch_sol := hI.branch_sol
  branch_init := hI.branch_init
  quad := hI.quad
  target_ne := hI.target_ne
  budget := hI.budget
  disc := by
    have h := hI.disc
    have e : p.T * (βG * (p.T / p.M) + δG) = βG * p.T ^ 2 / p.M + p.T * δG := by ring
    rw [e] at h
    exact h

/-- The core conditions of an integrated instance. -/
theorem BInstanceOKI.core {βG δI κ : ℝ}
    (hI : BInstanceOKI p v₀ σ v wq fv Hb Lb G b x ys βG δI κ) :
    BCore p v₀ σ v wq fv Hb Lb (x 0) :=
  ⟨hI.uj, hI.priv, hI.clock, hI.selfH, hI.selfL, hI.normH, hI.normL, hI.psd, hI.nodes,
    hI.weights, hI.load_unitary, hI.prep_left, hI.prep_right, hI.prep, hI.init_load,
    hI.forcing_load⟩

/-- **The target facts under the integrated certificate.** -/
theorem target_factsBI (hp : p.PublicOK) {βG δI κ : ℝ}
    (hI : BInstanceOKI p v₀ σ v wq fv Hb Lb G b x ys βG δI κ) :
    TFacts p v Hb Lb (x 0) wq fv (x p.T) :=
  target_facts_of_error hp v Hb Lb (x 0) wq fv (x p.T) _ hI.target_ne hI.budget
    (target_errorBI p hp.T_pos v hI.nodes Hb Lb G (x 0) (x p.T) ys wq fv βG δI κ hI.βG_nonneg
      hI.branch_sol hI.branch_init hI.quad hI.accretive hI.lipG hI.sampleI hI.selfH hI.psd)
    hI.disc

end Instance

/-! ### The native solver with the integrated certificate -/

section Native

variable {S Zs Z Y J Xa : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]
variable {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **The guarantees for one instance with the integrated certificate** of the native
time-dependent solver on branch-dependent meshes. -/
theorem native_time_outcomeBI (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (σ : TOracles p.a p.m p.l (Reg S ℂ)) (hUJ : σ.UJ = UJop (R := ℂ) UJg)
    (hN : NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) σ.D false)))
    (ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu)
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δI κ : ℝ)
    (hI : BInstanceOKI p (seedV (S := S)) σ v wq fv Hb Lb G b x ys βG δI κ) :
    NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) :=
  native_time_outcomeC p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim σ hUJ hN
    ζs hζs hload hwp hbudget v wq fv Hb Lb (x 0) (x p.T) hI.core (target_factsBI hp hI)
    hI.target_ne

/-- **Native gate-efficient dissipative ODE solver on branch-dependent meshes with the integrated
sample-error certificate** (Theorem `ode:thm:gates`, time-dependent part, with the integrated
represented-sample certificate of Lemma `ode:lem:gate-select`, before finite-set synthesis). The
native protocol of the released `GateNative.native_ode_time_solver` keeps its validity and its
counts of gates, primitive calls and wires; for every instance with primitive oracles `prim`,
label- and slot-selected private Cayley operations `D z r` given natively by `V` (`NativeOK`), a
loading `J s` and a weight preparation `Wp` approximated by the supplied circuits within `ζs`,
the conditions `BInstanceOKI` for `(U_J, D, J, Wp)` and the error budget `24 d ζ + 3 ζs ≤ ν`,
the protocol has the guarantees `NOutcome`: success probability at least `2/3`, every
successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, and a conditional output
within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem native_ode_time_solverBI (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (tnprepC p UJg nd ar loadC wpC) j, i.Valid) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (tnprepC p UJg nd ar loadC wpC) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool,
      ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    Fintype.card (TNW p S Zs Z ar.bT ar.bP ar.A) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
      (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
      (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δI κ ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      BInstanceOKI p (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        v wq fv Hb Lb G b x ys βG δI κ →
      NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har
    loadC hloadV wpC hwpV
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro prim D Jl Wp v wq fv Hb Lb G b x ys βG δI κ ζs hprim hN hζs hload hwp hbudget hI
  exact native_time_outcomeBI p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ rfl hN ζs hζs hload hwp hbudget v wq fv Hb Lb G b x ys βG δI κ
    hI

/-- **The guarantees of the synthesised preparation with the integrated certificate**: under the
hypotheses of `native_time_outcomeBI`, the released native protocol on the synthesised
preparation `synthPrep hS (ν/3) (tnprepC …)` has the guarantees `NOutcome`. -/
theorem native_time_trials_outcomeBI (hS : GateSynth.Synthesis 𝒢 Xa len) (p : TParams)
    (hp : p.PublicOK) (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (σ : TOracles p.a p.m p.l (Reg S ℂ)) (hUJ : σ.UJ = UJop (R := ℂ) UJg)
    (hN : NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) σ.D false)))
    (ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu)
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δI κ : ℝ)
    (hI : BInstanceOKI p (seedV (S := S)) σ v wq fv Hb Lb G b x ys βG δI κ) :
    NOutcome (GateSynthTrials.synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
      p.ε (p.ratio_ge hp.g_ge) prim (x p.T) :=
  native_time_trials_outcomeC hS p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    σ hUJ hN ζs hζs hload hwp hbudget v wq fv Hb Lb (x 0) (x p.T) hI.core (target_factsBI hp hI)
    hI.target_ne

end Native

/-! ### The left-endpoint quadrature -/

section Left

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable (p : TParams)

/-- **The conditions on an instance with the left-endpoint quadrature and the integrated
certificate**: those of `GateQuad.LInstanceOK` (`n ≤ 2^m` nodes `q T/n` with the weights `T/n`,
the source certificate `(Λ b_s + L) T²/(2n) + T δb` proved in `GateEfficientQuadrature`), with
the uniform sample bound replaced by the integrated certificate `sampleErrB s ≤ δI` and the
budget by `(Λ b_s + L) T²/(2n) + T δb + (βG T²/2^m + δI) B_n ≤ ε B_n/(2000 g)`. -/
structure LInstanceOKI (n : ℕ) (v₀ : P) (σ : TOracles p.a p.m p.l P) (fv : ℕ → P)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P) (G : ℝ → P →L[ℂ] P) (b x : ℝ → P)
    (ys : Bool × (Fin p.m → Bool) → ℝ → P) (βG δI Λ L bs δb : ℝ) : Prop where
  n_pos : 0 < n
  n_le : n ≤ p.M
  uj : IsUnitary σ.UJ
  priv : ∀ z, ∀ r < p.M, IsUnitary (σ.D z r)
  clock : ∀ z, ∀ r < p.M,
    ClockPromise σ.UJ (σ.D z r) (branchHB p (vQ p n) Hb Lb z r) p.Q p.qbar
  selfH : ∀ s, ∀ r < p.M, star (Hb s r) = Hb s r
  selfL : ∀ s, ∀ r < p.M, star (Lb s r) = Lb s r
  normH : ∀ s, ∀ r < p.M, ‖Hb s r‖ ≤ p.lamH
  normL : ∀ s, ∀ r < p.M, ‖Lb s r‖ ≤ p.lamD
  psd : ∀ s, ∀ r < p.M, ∀ w : P, 0 ≤ (inner ℂ w (Lb s r w)).re
  load_unitary : ∀ s, IsUnitary (σ.J s)
  prep_left : σ.Wp.conjTranspose * σ.Wp = 1
  prep_right : σ.Wp * σ.Wp.conjTranspose = 1
  prep : p.WpPromise σ (x 0) (bsW p (wQ p n) fv)
  init_load : x 0 ≠ 0 → σ.J (false, fun _ => false) v₀ = unitDirection (x 0)
  forcing_load : ∀ w : Fin p.m → Bool, wordValue w < n → fv (wordValue w) ≠ 0 →
    σ.J (true, w) v₀ = unitDirection (fv (wordValue w))
  solves : SolvesODE G b x 0 p.T
  accretive : ∀ u ∈ Icc 0 p.T, Accretive (G u)
  lipG : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleI : ∀ s, sampleErrB p (vQ p n) Hb Lb G s ≤ δI
  normG : ∀ u ∈ Icc 0 p.T, ‖G u‖ ≤ Λ
  lipb : ∀ u ∈ Icc 0 p.T, ∀ u' ∈ Icc 0 p.T, ‖b u - b u'‖ ≤ L * |u - u'|
  L_nonneg : 0 ≤ L
  sample_norm : ∀ q < n, ‖fv q‖ ≤ bs
  sample_err : ∀ q < n, ‖b (q * p.T / n) - fv q‖ ≤ δb
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB p (vQ p n) s) p.T
  branch_init : ∀ s, ys s (startB p (vQ p n) s) = p.zsrc (x 0) (bsW p (wQ p n) fv) s
  target_ne : x p.T ≠ 0
  budget : quadMass (x 0) fv p.T n ≤ p.g * ‖x p.T‖
  disc : (Λ * bs + L) * p.T ^ 2 / (2 * n) + p.T * δb +
      (βG * p.T ^ 2 / p.M + δI) * quadMass (x 0) fv p.T n ≤
    p.ε * quadMass (x 0) fv p.T n / (2000 * p.g)

variable {p}

/-- **The left-endpoint instance as an integrated instance**, with the certificate
`κ = (Λ b_s + L) T²/(2n) + T δb` of `GateQuad.quad_left`. -/
theorem LInstanceOKI.toBI (hp : p.PublicOK) {n : ℕ} {v₀ : P} {σ : TOracles p.a p.m p.l P}
    {fv : ℕ → P} {Hb Lb : Bool × (Fin p.m → Bool) → ℕ → P →L[ℂ] P} {G : ℝ → P →L[ℂ] P}
    {b x : ℝ → P} {ys : Bool × (Fin p.m → Bool) → ℝ → P} {βG δI Λ L bs δb : ℝ}
    (hI : LInstanceOKI p n v₀ σ fv Hb Lb G b x ys βG δI Λ L bs δb) :
    BInstanceOKI p v₀ σ (vQ p n) (wQ p n) fv Hb Lb G b x ys βG δI
      ((Λ * bs + L) * p.T ^ 2 / (2 * n) + p.T * δb) where
  uj := hI.uj
  priv := hI.priv
  clock := hI.clock
  selfH := hI.selfH
  selfL := hI.selfL
  normH := hI.normH
  normL := hI.normL
  psd := hI.psd
  nodes := GateQuad.vQ_mem p hp.T_pos.le n
  weights := GateQuad.wQ_nonneg p hp.T_pos.le n
  load_unitary := hI.load_unitary
  prep_left := hI.prep_left
  prep_right := hI.prep_right
  prep := hI.prep
  init_load := hI.init_load
  forcing_load := fun w hw hf => hI.forcing_load w (by
    by_contra h
    exact hw (by simp [wQ, h])) hf
  solves := hI.solves
  accretive := hI.accretive
  lipG := hI.lipG
  βG_nonneg := hI.βG_nonneg
  sampleI := hI.sampleI
  branch_sol := hI.branch_sol
  branch_init := hI.branch_init
  quad := GateQuad.quad_left p hp.T_pos hI.n_pos hI.n_le G b x fv ys Λ L δb bs hI.L_nonneg
    hI.solves hI.accretive hI.normG hI.lipb hI.sample_norm hI.sample_err hI.branch_sol
    hI.branch_init
  target_ne := hI.target_ne
  budget := by
    rw [GateQuad.mass_wQ p hp.T_pos hI.n_le]
    exact hI.budget
  disc := by
    rw [GateQuad.mass_wQ p hp.T_pos hI.n_le]
    exact hI.disc

end Left

end

end SparseHamiltonian.GateBinaryNodes
