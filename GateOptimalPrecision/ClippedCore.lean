import LargeSparsityCore.Core

/-!
# The large-sparsity core on an arbitrary finer mesh

Section `gate:sec:core` ("Mesh and filter preparation"): the clipped transducer is run on a mesh
of `J` private slots, `J` the least power of two above the analytic requirement ("This is allowed
by the analytic proof"). The query proof (`LargeSparsityCore.Core.core_implementation`) fixes the
slot count `N_s = steps s τ ε`; every estimate it uses is monotone in the step `w = a/T`:

* the step conditions `w ≤ 1/4` and `w (1 + 2(2/ζ + 4Q₀/3)) ≤ 1/2`;
* the Cayley discretisation error `T w³ = a³/T² ≤ N_s w_s³ ≤ ε/3`;
* the resolvent bounds `CoreFilter.pointBound` (linear and increasing in `w`, `pointBound_mono_w`),
  hence the filter estimate `‖f(D_g)‖ ≤ ε/3` (`filter_estimate_mesh`);
* the catalyst budget `6 a ν ≤ d` (independent of `T`, since `T w = a`).

`core_implementation_mesh` is the abstract core of the query proof for every `T ≥ N_s` slots:
under `Core.CoreData`, the amplified chronological clock with the product filter on `T` slots of
step `a/T` is an isometry with full-output error at most `ε` for `e^{-i a J†KJ}`.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian
open LargeSparsityCore LargeSparsityCore.Parameters LargeSparsityCore.CayleyBlocks
open GlobalResolvent ChronologicalResolvent GlobalColligation
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### Monotonicity in the step -/

theorem pointBound_mono_w {Q₀ sw sm w w' a ip im ζ2 : ℝ} (hww : w ≤ w') :
    CoreFilter.pointBound Q₀ sw sm w a ip im ζ2 ≤ CoreFilter.pointBound Q₀ sw sm w' a ip im ζ2 := by
  unfold CoreFilter.pointBound
  simp only
  have hX : 0 ≤ (sw * (ip + im) + 2 / 3 * (1 + sm)) ^ 2 := sq_nonneg _
  nlinarith

theorem isoBound_mono_w {Q₀ sw sm w w' a ζ g : ℝ} (hww : w ≤ w') :
    CoreFilter.isoBound Q₀ sw sm w a ζ g ≤ CoreFilter.isoBound Q₀ sw sm w' a ζ g :=
  pointBound_mono_w hww

theorem bulkBound_mono_w {Q₀ sw sm w w' a ρ₀ : ℝ} (hww : w ≤ w') :
    CoreFilter.bulkBound Q₀ sw sm w a ρ₀ ≤ CoreFilter.bulkBound Q₀ sw sm w' a ρ₀ :=
  pointBound_mono_w hww

/-- **The filter estimate on a finer mesh**: the right-hand side of `CoreFilter.filter_bound` at
any step `0 ≤ w ≤ w_s` is at most `ε/3`. -/
theorem filter_estimate_mesh {s τ ε : ℝ} (R : Regime s τ ε) {w : ℝ} (hw0 : 0 ≤ w)
    (hw : w ≤ wval s τ ε) :
    2 * (zeta s τ ε * (Fval s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε)
      w (aval s τ ε) (zeta s τ ε)
      (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - zeta s τ ε))) +
    (2 / ((B0 s τ ε : ℝ) * rho0 s τ ε)) ^ mval τ ε * rho0 s τ ε *
      (CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w (aval s τ ε)
        (rho0 s τ ε) *
      (1 + 2 * (zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w
        (aval s τ ε) (zeta s τ ε)
        (‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - zeta s τ ε)))) ≤
      ε / 3 := by
  refine le_trans ?_ R.filter_estimate
  set g := ‖CayleyBlocks.lamp (qval s τ ε) - CayleyBlocks.lamm (qval s τ ε)‖ - zeta s τ ε
  have hζ := R.zeta_pos
  have hg : 0 < g := by have := R.sep; linarith
  have hsw := sw_nonneg s τ ε
  have hsm := sm_nonneg s τ ε
  have hQ : 0 ≤ Q0 s τ ε := by linarith [R.Q0_ge]
  have ha := R.a_pos
  have hF : 0 ≤ Fval s τ ε := by unfold Fval; positivity
  have hρ := R.rho0_pos
  have hI := isoBound_mono_w (Q₀ := Q0 s τ ε) (sw := sw s τ ε) (sm := sm s τ ε)
    (a := aval s τ ε) (ζ := zeta s τ ε) (g := g) hw
  have hB := bulkBound_mono_w (Q₀ := Q0 s τ ε) (sw := sw s τ ε) (sm := sm s τ ε)
    (a := aval s τ ε) (ρ₀ := rho0 s τ ε) hw
  have hI0 : 0 ≤ CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w (aval s τ ε)
      (zeta s τ ε) g :=
    Parameters.pointBound_nonneg hw0 ha.le (inv_nonneg.mpr hζ.le) (inv_nonneg.mpr hg.le) hQ
  have hB0 : 0 ≤ CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w (aval s τ ε)
      (rho0 s τ ε) :=
    Parameters.pointBound_nonneg hw0 ha.le (by positivity) (by positivity) hQ
  have hc : 0 ≤ (2 / ((B0 s τ ε : ℝ) * rho0 s τ ε)) ^ mval τ ε * rho0 s τ ε := by
    have : (0 : ℝ) < B0 s τ ε := by exact_mod_cast R.B0_pos
    positivity
  have h1 : zeta s τ ε * (Fval s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w
      (aval s τ ε) (zeta s τ ε) g) ≤ zeta s τ ε * (Fval s τ ε * CoreFilter.isoBound (Q0 s τ ε)
        (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε) (zeta s τ ε) g) := by
    gcongr
  have h2 : 1 + 2 * (zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w
      (aval s τ ε) (zeta s τ ε) g) ≤ 1 + 2 * (zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε)
        (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε) (zeta s τ ε) g) := by
    gcongr
  have h3 : CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w (aval s τ ε) (rho0 s τ ε) *
      (1 + 2 * (zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) w
        (aval s τ ε) (zeta s τ ε) g)) ≤
      CoreFilter.bulkBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε) (aval s τ ε)
        (rho0 s τ ε) *
      (1 + 2 * (zeta s τ ε * CoreFilter.isoBound (Q0 s τ ε) (sw s τ ε) (sm s τ ε) (wval s τ ε)
        (aval s τ ε) (zeta s τ ε) g)) :=
    mul_le_mul hB h2 (by positivity) (hB0.trans hB)
  have h4 := mul_le_mul_of_nonneg_left h3 hc
  linarith

/-! ### The core on `T ≥ N_s` slots -/

/-- The step of `T` slots. -/
def coreStep (s τ ε : ℝ) (T : ℕ) : ℝ := aval s τ ε / T

theorem coreStep_spec {s τ ε : ℝ} (R : Regime s τ ε) {T : ℕ} (hT : steps s τ ε ≤ T) :
    0 ≤ coreStep s τ ε T ∧ coreStep s τ ε T ≤ wval s τ ε ∧ (T : ℝ) * coreStep s τ ε T =
      aval s τ ε ∧ (T : ℝ) * coreStep s τ ε T ^ 3 ≤ ε / 3 := by
  have hS : (0 : ℝ) < steps s τ ε := by exact_mod_cast steps_pos s τ ε
  have hT' : (steps s τ ε : ℝ) ≤ T := by exact_mod_cast hT
  have hT0 : (0 : ℝ) < T := hS.trans_le hT'
  have ha := R.a_pos
  refine ⟨div_nonneg ha.le hT0.le, ?_, ?_, ?_⟩
  · unfold coreStep wval
    exact div_le_div_of_nonneg_left ha.le hS hT'
  · unfold coreStep; field_simp
  · have hc := R.cubic_le
    have e1 : (T : ℝ) * coreStep s τ ε T ^ 3 = aval s τ ε ^ 3 / (T : ℝ) ^ 2 := by
      unfold coreStep; field_simp
    have e2 : (steps s τ ε : ℝ) * wval s τ ε ^ 3 = aval s τ ε ^ 3 / (steps s τ ε : ℝ) ^ 2 := by
      unfold wval; field_simp
    rw [e1]
    rw [e2] at hc
    refine le_trans ?_ hc
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hS.le hT' 2

theorem small_step_mesh {s τ ε : ℝ} (R : Regime s τ ε) {w : ℝ} (hw : w ≤ wval s τ ε) :
    w * (1 + 2 * (2 / zeta s τ ε + 4 / 3 * Q0 s τ ε)) ≤ 1 / 2 := by
  have h := R.small_step
  have hc : 0 ≤ 1 + 2 * (2 / zeta s τ ε + 4 / 3 * Q0 s τ ε) := by
    have := R.zeta_pos; have := R.Q0_ge; positivity
  exact (mul_le_mul_of_nonneg_right hw hc).trans h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- **The abstract large-sparsity core on `T ≥ N_s` slots.** In the regime and under the
hypotheses `Core.CoreData`, the amplified chronological clock with the product filter on `T` slots
of step `a/T` is an isometry with full-output error at most `ε` for `e^{-i a J†KJ}`. -/
theorem core_implementation_mesh [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε) {K D Pp Pm : V →L[ℂ] V} {J : P →L[ℂ] V}
    (h : Core.CoreData s τ ε K D Pp Pm J) {T : ℕ} (hT : steps s τ ε ≤ T) :
    (Smoothing.clockImplementation (Core.coeff s τ ε) (degree s τ ε) D J (coreStep s τ ε T) T)† ∘L
        Smoothing.clockImplementation (Core.coeff s τ ε) (degree s τ ε) D J (coreStep s τ ε T) T =
      1 ∧
    ‖Smoothing.clockImplementation (Core.coeff s τ ε) (degree s τ ε) D J (coreStep s τ ε T) T -
      SmoothingLCU.output (P := P) (V := BlockOperator.H T V) (Core.coeff s τ ε) (degree s τ ε) ∘L
        NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) • (J† ∘L K ∘L J))‖ ≤ ε := by
  obtain ⟨hw0, hww, hTw, hcub⟩ := coreStep_spec R hT
  set w := coreStep s τ ε T with hwdef
  set H := J† ∘L K ∘L J with hHdef
  have hSelf : star H = H := by
    rw [hHdef, ContinuousLinearMap.star_eq_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
      h.spectral.self.adjoint_eq, comp_assoc]
  have hBoundary : J† ∘L R1 K ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H) := by
    rw [hHdef, R1]
    simp only [smul_comp, comp_smul, add_comp, comp_add, one_comp, h.isometry]
  have hν := R.nu_pos
  set Q := max ‖R1 K‖ (nu s τ ε) with hQdef
  have hQ : 0 < Q := lt_of_lt_of_le hν (le_max_right _ _)
  set b := Real.sqrt (nu s τ ε / 2) with hbdef
  have hEnd : ‖R1 K ∘L J‖ ≤ b := by
    apply Real.le_sqrt_of_sq_le
    have h1 := Core.endpoint_sq_le h.spectral.self J h.isometry
    have h2 := h.second
    have e : nu s τ ε / 2 = (1 + 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s) / 4 := by
      unfold nu
      ring
    rw [e]
    linarith
  have hbq : b ^ 2 ≤ nu s τ ε / 2 := by
    rw [hbdef, Real.sq_sqrt (by positivity)]
  have hdeg : 6 * ((T : ℝ) * w * nu s τ ε) ≤ degree s τ ε := by
    rw [hTw]
    exact R.catalyst_le
  have hfb := CoreFilter.filter_bound h.spectral h.unitary J h.isometry h.bulk_bound h.iso_p
    h.iso_m h.moment R.rho0_mul_Q0 R.zeta_pos R.rho0_pos hw0 (small_step_mesh R hww) R.sep
    R.lamp_inside R.lamm_inside T (B0 s τ ε) (mval τ ε) (pval s τ ε) (kval τ ε)
    R.one_le_B0 R.one_le_p R.one_le_m R.F_lamp R.F_lamm
  rw [hTw] at hfb
  have hfilter := hfb.trans (filter_estimate_mesh R hw0 hww)
  have hε := R.ε_pos
  have hε1 := R.ε_le
  have hwq : w ≤ 1 / 4 := hww.trans (w_le_quarter s τ ε)
  obtain ⟨U, R', hDen, hU, _hUT1, _hUT2, hIso, hErr⟩ :=
    Smoothing.exists_implementation (Core.coeff s τ ε) (degree s τ ε) R.degree_pos (Core.mass R)
      (Core.coeff_sum R) D (R1 K) J H w Q b (nu s τ ε) T hQ hw0 hwq h.unitary h.isometry
      h.spectral.cayley_right h.spectral.cayley_left (le_max_left _ _) hBoundary hSelf h.boundary
      hEnd hbq (le_max_right _ _) hdeg (ε / 3) (by positivity) (by linarith) hfilter
  have hw1 : w ≤ 1 := hwq.trans (by norm_num)
  have hCay := CayleyApproximation.hamiltonian_cayley_error H R' w hw0 hw1 hSelf h.boundary hDen T
  have hTW : ((T : ℂ) * (w : ℂ)) = (aval s τ ε : ℂ) := by exact_mod_cast hTw
  have hTarget : ‖U ^ T - NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) • H)‖ ≤ ε / 3 := by
    have e : -Complex.I * (T : ℂ) * (w : ℂ) = -Complex.I * (aval s τ ε : ℂ) := by
      rw [mul_assoc, hTW]
    rw [hU]
    rw [e] at hCay
    exact hCay.trans hcub
  refine ⟨hIso, ?_⟩
  have := Smoothing.implementation_error_to_target (Core.coeff s τ ε) (degree s τ ε) R.degree_pos
    (Core.mass R) _ (U ^ T) _ _ _ _ (2 * (ε / 3)) (ε / 3) hErr hTarget
  calc _ ≤ 2 * (ε / 3) + ε / 3 := this
    _ = ε := by ring

end

end GateOptimalPrecision
