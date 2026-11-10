import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Positive
import TimeDependentODE.Continuous.Discretisation
import ODELowerBoundExtensions.Psd.Heat
import ODELowerBoundExtensions.Psd.Params

/-!
# The imaginary-time spin-chain amplitude and its rounding

Manuscript: the proof of Theorem `odel:thm:psd` (spin chain `B_n`, eq. `odel:eq:imaginaryamp`;
rounding, eq. `odel:eq:Dpath`, contractive Duhamel comparison).

* The PSD generator `psdCore H = (1 - H)/2` of a Hermitian `H` with `‖H‖ ≤ 1` is positive
  semidefinite with `‖psdCore H‖ ≤ 1` (`posSemidef_psdCore`, `norm_psdCore_le`), hence
  accretive (`accretive_of_posSemidef`), and `‖psdCore H - psdCore H'‖ = ‖H - H'‖/2`.
* `heatEndAmp n c t = ⟨n| e^{-t(1 - B_c)/2} |0⟩` for the path `B_c` with weights `c`
  (the PSD analogue of `Hamiltonian.endAmp`).
* **Eq. `odel:eq:imaginaryamp`**: `⟨n| e^{uB_n} |0⟩ = sinh(u/n)^n` (`heat_neg_spinMatrix_last`;
  route: the explicit vector `f_k(t) = √binom(n,k) cosh(t/n)^{n-k} sinh(t/n)^k` solves
  `f' = B_n f` on all of `ℝ`, `f(0) = |0⟩`, and `heat_apply_eq_of_hasDerivAt`; it is the
  real-time proof of `Hamiltonian.endAmp_scaled` with `cos, -i sin` replaced by `cosh, sinh`), so
  `heatEndAmp n b (2u) = e^{-u} sinh(u/n)^n = a` (`heatEndAmp_spinWeight`).
* **Contractive Duhamel comparison** (proof of Theorem `odel:thm:psd`):
  `‖e^{-tD} - e^{-tD'}‖ ≤ t ‖D - D'‖` for accretive `D, D'` (the release's
  `TimeDependentODE.step_error` with constant generator, no source and `‖x(u)‖ ≤ 1`), so
  `|heatEndAmp n b' (2u) - a| ≤ 2uδ ≤ a/8` and the rounded amplitude is at least `7a/8`
  (`seven_eighths_le_heatEndAmp`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Hamiltonian
open scoped Matrix InnerProductSpace Matrix.Norms.L2Operator ComplexOrder

section Generator

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- A positive semidefinite matrix is an accretive generator (`D ⪰ 0`, Section `odel:sec:main`). -/
theorem accretive_of_posSemidef {D : Matrix S S ℂ} (hD : D.PosSemidef) :
    TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator D) := by
  intro v
  have h := (Matrix.isPositive_toEuclideanLin_iff.2 hD).2 v
  rw [inner_re_symm] at h
  rw [matrixOperator_eq_toEuclideanCLM]
  exact h

/-- `(1 - H)/2 ⪰ 0` for Hermitian `H` with `‖H‖ ≤ 1` (proof of Theorem `odel:thm:psd`). -/
theorem posSemidef_psdCore {H : Matrix S S ℂ} (hH : H.IsHermitian) (h1 : ‖H‖ ≤ 1) :
    (psdCore H).PosSemidef := by
  have h1H : (1 - H).PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanLin_iff]
    refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.2 (Matrix.isHermitian_one.sub hH), fun x => ?_⟩
    have hx : Matrix.toEuclideanLin (1 - H) x = x - Matrix.toEuclideanLin H x := by
      show Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) (1 - H) x = _
      rw [map_sub, map_one]
      rfl
    have hHx : ‖Matrix.toEuclideanLin H x‖ ≤ ‖x‖ := by
      have h := (Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) H).le_opNorm x
      rw [Matrix.l2_opNorm_toEuclideanCLM] at h
      calc ‖Matrix.toEuclideanLin H x‖ = ‖Matrix.toEuclideanCLM (n := S) (𝕜 := ℂ) H x‖ := rfl
        _ ≤ ‖H‖ * ‖x‖ := h
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖x‖ := one_mul _
    rw [hx, inner_sub_left, map_sub, inner_self_eq_norm_sq]
    have hre : RCLike.re (⟪Matrix.toEuclideanLin H x, x⟫_ℂ) ≤ ‖x‖ ^ 2 :=
      (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg x]))
    linarith
  have hhalf : (0 : ℂ) ≤ 1 / 2 := by
    rw [Complex.nonneg_iff]; norm_num
  exact h1H.smul hhalf

/-- `‖(1 - H)/2‖ ≤ 1` for `‖H‖ ≤ 1`. -/
theorem norm_psdCore_le {H : Matrix S S ℂ} (h1 : ‖H‖ ≤ 1) : ‖psdCore H‖ ≤ 1 := by
  have hone : ‖(1 : Matrix S S ℂ)‖ ≤ 1 := by
    rw [Matrix.cstar_norm_def, map_one]
    exact ContinuousLinearMap.norm_id_le
  unfold psdCore
  rw [norm_smul]
  have h2 : ‖(1 : Matrix S S ℂ) - H‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  linarith

/-- `‖psdCore H - psdCore H'‖ = ‖H - H'‖/2`. -/
theorem norm_psdCore_sub (H H' : Matrix S S ℂ) : ‖psdCore H - psdCore H'‖ = ‖H - H'‖ / 2 := by
  unfold psdCore
  rw [← smul_sub, sub_sub_sub_cancel_left, norm_smul, norm_sub_rev]
  have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hn]
  ring

/-- **Contractive Duhamel comparison** (proof of Theorem `odel:thm:psd`): for accretive generators,
`‖e^{-tD} v - e^{-tD'} v‖ ≤ t ‖D - D'‖ ‖v‖` (`TimeDependentODE.step_error`). -/
theorem norm_heat_sub_heat_apply_le {D D' : Matrix S S ℂ}
    (hD : TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator D))
    (hD' : TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator D')) {t : ℝ}
    (ht : 0 ≤ t) (v : EuclideanSpace ℂ S) :
    ‖heat D t v - heat D' t v‖ ≤ t * ‖D - D'‖ * ‖v‖ := by
  have h := TimeDependentODE.step_error (solves_heat D v 0 t) ht
    (SparseStateOverlap.matrixOperator D') hD' 0 (‖D - D'‖ * ‖v‖) (fun u hu => by
      have hop : ‖SparseStateOverlap.matrixOperator D' - SparseStateOverlap.matrixOperator D‖ =
          ‖D - D'‖ := by
        rw [matrixOperator_eq_toEuclideanCLM, matrixOperator_eq_toEuclideanCLM, ← map_sub,
          Matrix.l2_opNorm_toEuclideanCLM, norm_sub_rev]
      have hx : ‖heat D u v‖ ≤ ‖v‖ :=
        ((heat D u).le_opNorm v).trans
          (by simpa using mul_le_mul_of_nonneg_right (norm_heat_le D hD u hu.1) (norm_nonneg v))
      simp only [sub_zero, norm_zero, mul_zero, add_zero, hop]
      exact mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  simp only [sub_zero, smul_zero, add_zero, heat_zero, one_apply_eq_self] at h
  calc ‖heat D t v - heat D' t v‖ ≤ ‖D - D'‖ * ‖v‖ * t := h
    _ = t * ‖D - D'‖ * ‖v‖ := by ring

end Generator

/-! ### The endpoint amplitude of a path -/

/-- The PSD endpoint amplitude `⟨n| e^{-t(1 - B_c)/2} |0⟩` of the path with weights `c`. -/
def heatEndAmp (n : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℂ :=
  heat (psdCore (pathMatrix n c)) t (EuclideanSpace.single 0 1) (Fin.last n)

variable {n : ℕ} {u : ℝ}

/-- The hyperbolic monomial rule: `d/du (C cosh(θ)^p sinh(θ)^q) =
C θ' (p cosh^{p-1} sinh^{q+1} + q cosh^{p+1} sinh^{q-1})` (the imaginary-time analogue of
`Helpers.SpinChain.hasDerivAt_trigMonomial`). -/
theorem hasDerivAt_hypMonomial {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t) (C : ℝ)
    (p q : ℕ) :
    HasDerivAt (fun u : ℝ => (C : ℂ) * ((Real.cosh (θ u) : ℝ) : ℂ) ^ p *
        ((Real.sinh (θ u) : ℝ) : ℂ) ^ q)
      ((C : ℂ) * (θ' : ℂ) *
        ((p : ℂ) * ((Real.cosh (θ t) : ℝ) : ℂ) ^ (p - 1) * ((Real.sinh (θ t) : ℝ) : ℂ) ^ (q + 1) +
          (q : ℂ) * ((Real.cosh (θ t) : ℝ) : ℂ) ^ (p + 1) *
            ((Real.sinh (θ t) : ℝ) : ℂ) ^ (q - 1))) t := by
  have hc : HasDerivAt (fun u => ((Real.cosh (θ u) : ℝ) : ℂ)) ((Real.sinh (θ t) * θ' : ℝ) : ℂ) t :=
    ((Real.hasDerivAt_cosh (θ t)).comp t hθ).ofReal_comp
  have hs : HasDerivAt (fun u => ((Real.sinh (θ u) : ℝ) : ℂ)) ((Real.cosh (θ t) * θ' : ℝ) : ℂ) t :=
    ((Real.hasDerivAt_sinh (θ t)).comp t hθ).ofReal_comp
  have h := ((hc.fun_pow p).const_mul (C : ℂ)).mul (hs.fun_pow q)
  refine h.congr_deriv ?_
  simp only [Complex.ofReal_mul]
  set c : ℂ := ((Real.cosh (θ t) : ℝ) : ℂ)
  set z : ℂ := ((Real.sinh (θ t) : ℝ) : ℂ)
  rw [pow_succ _ q, pow_succ _ p]
  rcases q with _ | q
  · simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, mul_zero, one_mul]
    ring
  · rw [Nat.add_sub_cancel, pow_succ _ q]
    push_cast
    ring

/-- The explicit imaginary-time solution `f_k(t) = √binom(n,k) cosh(t/n)^{n-k} sinh(t/n)^k` of
`f' = B_n f`, `f(0) = |0⟩` (proof of Theorem `odel:thm:psd`; the symmetric-subspace restriction of
`(cosh θ |0⟩ + sinh θ |1⟩)^{⊗n}`, `θ = t/n`). -/
def heatSpinSolution (n : ℕ) (t : ℝ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 fun k =>
    ((Real.sqrt (n.choose (k : ℕ)) : ℝ) : ℂ) * ((Real.cosh (1 * t / n) : ℝ) : ℂ) ^ (n - (k : ℕ)) *
      ((Real.sinh (1 * t / n) : ℝ) : ℂ) ^ (k : ℕ)

/-- The imaginary-time solution starts at `|0⟩`. -/
theorem heatSpinSolution_zero (n : ℕ) : heatSpinSolution n 0 = EuclideanSpace.single 0 1 := by
  ext k
  simp only [heatSpinSolution, PiLp.toLp_apply, mul_zero, zero_div, Real.cosh_zero,
    Real.sinh_zero, Complex.ofReal_one, Complex.ofReal_zero, one_pow, mul_one, PiLp.single_apply]
  by_cases hk : k = 0
  · subst hk
    simp
  · have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
    simp [hk, zero_pow hk']

/-- Its endpoint component is `sinh(t/n)^n`. -/
theorem heatSpinSolution_last (n : ℕ) (t : ℝ) :
    heatSpinSolution n t (Fin.last n) = ((Real.sinh (t / n) ^ n : ℝ) : ℂ) := by
  simp [heatSpinSolution, PiLp.toLp_apply, Fin.val_last, Nat.choose_self]

/-- The imaginary-time solution solves `f' = B_n f = -(-B_n) f` on all of `ℝ` (the ladder
identities `spinWeight_mul_sqrt_choose(_succ)`, through `Helpers.SpinChain.spin_row`). -/
theorem hasDerivAt_heatSpinSolution (t : ℝ) :
    HasDerivAt (heatSpinSolution n)
      (-(SparseStateOverlap.matrixOperator (-spinMatrix n) (heatSpinSolution n t))) t := by
  have hθ : HasDerivAt (fun u : ℝ => 1 * u / n) (1 / n) t := by
    simpa using ((hasDerivAt_id t).const_mul (1 : ℝ)).div_const (n : ℝ)
  have hpi : HasDerivAt (fun u => WithLp.ofLp (heatSpinSolution n u))
      (fun k : Fin (n + 1) => ((Real.sqrt (n.choose (k : ℕ)) : ℝ) : ℂ) * ((1 / n : ℝ) : ℂ) *
        (((n - (k : ℕ) : ℕ) : ℂ) * ((Real.cosh (1 * t / n) : ℝ) : ℂ) ^ (n - (k : ℕ) - 1) *
            ((Real.sinh (1 * t / n) : ℝ) : ℂ) ^ ((k : ℕ) + 1) +
          ((k : ℕ) : ℂ) * ((Real.cosh (1 * t / n) : ℝ) : ℂ) ^ (n - (k : ℕ) + 1) *
            ((Real.sinh (1 * t / n) : ℝ) : ℂ) ^ ((k : ℕ) - 1))) t :=
    hasDerivAt_pi.2 fun k => hasDerivAt_hypMonomial hθ _ _ _
  refine ((PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hpi).congr_deriv ?_
  ext k
  simp only [ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply, PiLp.neg_apply, SparseStateOverlap.matrixOperator_apply, Matrix.neg_apply,
    neg_mul, Finset.sum_neg_distrib, neg_neg, spinMatrix, pathMatrix, Matrix.of_apply,
    ite_mul, zero_mul]
  rw [Helpers.SpinChain.sum_path]
  simp only [heatSpinSolution, PiLp.toLp_apply, dite_eq_ite]
  have h := Helpers.SpinChain.spin_row 1 ((Real.cosh (1 * t / n) : ℝ) : ℂ)
    ((Real.sinh (1 * t / n) : ℝ) : ℂ) (Nat.lt_succ_iff.1 k.isLt)
  have key : ∀ A X R : ℂ, A * -Complex.I * X = -Complex.I * R → A * X = R := by
    intro A X R hAX
    linear_combination Complex.I * hAX + (A * X - R) * Complex.I_sq
  simp only [one_mul] at h ⊢
  exact key _ _ _ h

/-- **Eq. `odel:eq:imaginaryamp`** (proof of Theorem `odel:thm:psd`):
`⟨n| e^{uB_n} |0⟩ = sinh(u/n)^n` for every real `u` (`B_n` is `n⁻¹ Σ_j X_j` on the symmetric
subspace). -/
theorem heat_neg_spinMatrix_last (hn : 1 ≤ n) (u : ℝ) :
    heat (-spinMatrix n) u (EuclideanSpace.single 0 1) (Fin.last n) =
      ((Real.sinh (u / n) ^ n : ℝ) : ℂ) := by
  have _ := hn -- the identity also holds for `n = 0`
  rw [← heatSpinSolution_zero n, heat_apply_eq_of_hasDerivAt _ hasDerivAt_heatSpinSolution u,
    heatSpinSolution_last]

/-- `e^{-u} ⟨n| e^{uB_n} |0⟩ = a`: the ideal PSD amplitude at time `2u` is `psdAmp n u`. -/
theorem heatEndAmp_spinWeight (hn : 1 ≤ n) (u : ℝ) :
    heatEndAmp n (spinWeight n) (2 * u) = (psdAmp n u : ℂ) := by
  unfold heatEndAmp
  rw [heat_psdCore, show 2 * u / 2 = u by ring, smul_apply, PiLp.smul_apply,
    show pathMatrix n (spinWeight n) = spinMatrix n from rfl, heat_neg_spinMatrix_last hn u,
    smul_eq_mul, psdAmp]
  push_cast
  ring

/-- **Rounding** (proof of Theorem `odel:thm:psd`): `|heatEndAmp n b' (2u) - a| ≤ 2uδ ≤ a/8`. -/
theorem norm_heatEndAmp_psdWeight_sub_le (hn : 1 ≤ n) (hu : 0 < u) :
    ‖heatEndAmp n (psdWeight n u) (2 * u) - (psdAmp n u : ℂ)‖ ≤ psdAmp n u / 8 := by
  set D := psdCore (pathMatrix n (psdWeight n u))
  set D' := psdCore (pathMatrix n (spinWeight n))
  have hacc : ∀ c : ℕ → ℝ, ‖pathMatrix n c‖ ≤ 1 →
      TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator (psdCore (pathMatrix n c))) :=
    fun c hc => accretive_of_posSemidef (posSemidef_psdCore (isHermitian_pathMatrix n c) hc)
  have hD := hacc _ (norm_pathMatrix_psdWeight_le n u)
  have hD' := hacc _ (norm_spinMatrix hn).le
  have hv : ‖(EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℂ))‖ = 1 := by simp
  have hdiff : ‖D - D'‖ ≤ psdDelta n u := by
    rw [norm_psdCore_sub, norm_sub_rev]
    linarith [norm_pathMatrix_sub_psdWeight_le hn hu]
  have hδ : psdDelta n u ≤ psdAmp n u / (16 * u) := min_le_right _ _
  have h5 := norm_heat_sub_heat_apply_le hD hD' (by linarith : (0 : ℝ) ≤ 2 * u)
    (EuclideanSpace.single 0 1)
  rw [← heatEndAmp_spinWeight hn u]
  calc ‖heatEndAmp n (psdWeight n u) (2 * u) - heatEndAmp n (spinWeight n) (2 * u)‖
      = ‖(heat D (2 * u) (EuclideanSpace.single 0 1) -
          heat D' (2 * u) (EuclideanSpace.single 0 1)) (Fin.last n)‖ := rfl
    _ ≤ ‖heat D (2 * u) (EuclideanSpace.single 0 1) -
          heat D' (2 * u) (EuclideanSpace.single 0 1)‖ := PiLp.norm_apply_le _ _
    _ ≤ 2 * u * ‖D - D'‖ * 1 := by rw [← hv]; exact h5
    _ ≤ 2 * u * (psdAmp n u / (16 * u)) * 1 := by gcongr; exact hdiff.trans hδ
    _ = psdAmp n u / 8 := by field_simp; ring

/-- The rounded endpoint amplitude is at least `7a/8` (proof of Theorem `odel:thm:psd`). -/
theorem seven_eighths_le_heatEndAmp (hn : 1 ≤ n) (hu : 0 < u) :
    7 * psdAmp n u / 8 ≤ (heatEndAmp n (psdWeight n u) (2 * u)).re := by
  have h := norm_heatEndAmp_psdWeight_sub_le hn hu
  have hre := Complex.abs_re_le_norm (heatEndAmp n (psdWeight n u) (2 * u) - (psdAmp n u : ℂ))
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  have := neg_abs_le ((heatEndAmp n (psdWeight n u) (2 * u)).re - psdAmp n u)
  linarith

end

end ODELowerBoundExtensions.Psd
