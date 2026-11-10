import IntegrablePathSimulation.Propagator.Basic
import IntegrablePathSimulation.Calculus.Product
import IntegrablePathSimulation.Calculus.Gronwall
import SparseHamiltonian.OracleCircuit

set_option autoImplicit false

/-!
# Unitarity of propagators of integrable Hermitian paths

For a path `H` that is self-adjoint at almost every time of `[0, T]`, the propagator is
unitary at every time of `[0, T]`. The adjoint obeys `U* (s) = 1 + ∫_0^s i U*(u) H(u)* du`
(`SolvesIntegralOn.star_eq`); by the product rule for integral equations
(`Calculus.mul_eq_add_integral`)

* `U*(s) U(s) = U*(a) U(a) + ∫_a^s i U* (H* - H) U = U*(a) U(a)` on any interval
  (`SolvesIntegralOn.star_mul_self`); from the identity at `a`, `U(s)` is an isometry and
  `‖U(s)‖ ≤ 1` (`SolvesIntegralOn.norm_apply`, `SolvesIntegralOn.norm_le_one`, and on `[0, T]`
  `IsPropagator.star_mul_self`, `IsPropagator.norm_apply`, `IsPropagator.norm_le_one`);
* `D = U U* - 1` obeys `D(s) = ∫_0^s (-i) (H D - D H)`, hence `‖D s‖ ≤ ∫_0^s 2 ‖H‖ ‖D‖`, and
  `D = 0` by Grönwall's inequality (`IsPropagator.mul_star_self`).

Hence `U(s)` is unitary in the sense of the released `OracleCircuit.IsUnitary`
(`IsPropagator.isUnitary`). The Hilbert space need not be finite dimensional. This is the
unitarity of `U_H(T, 0)` used in Theorem `hs:thm:time` of the manuscript,
for the integrable Hermitian paths of the paragraph after its proof.
-/

namespace IntegrablePathSimulation.Propagator

noncomputable section

open MeasureTheory Set Filter SparseHamiltonian.OracleCircuit
open scoped Topology

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

variable {H U : ℝ → P →L[ℂ] P} {a b T : ℝ}

/-- The adjoint is a real-linear isometry of the bounded operators. -/
theorem exists_linearIsometry_star :
    ∃ L : (P →L[ℂ] P) →ₗᵢ[ℝ] (P →L[ℂ] P), ∀ A, L A = star A :=
  ⟨{ toFun := star
     map_add' := star_add
     map_smul' := fun r A => by
       simp only [RingHom.id_apply]
       rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r A,
         RCLike.real_smul_eq_coe_smul (K := ℂ) r (star A), star_smul]
       simp
     norm_map' := norm_star }, fun _ => rfl⟩

/-- The adjoint commutes with interval integrals of operator-valued functions. -/
theorem star_intervalIntegral (f : ℝ → P →L[ℂ] P) (a b : ℝ) :
    star (∫ u in a..b, f u) = ∫ u in a..b, star (f u) := by
  obtain ⟨L, hL⟩ := exists_linearIsometry_star (P := P)
  have h := L.intervalIntegral_comp_comm (μ := volume) (a := a) (b := b) f
  simp only [hL] at h
  exact h.symm

/-- The adjoint of an interval-integrable operator-valued function is interval integrable. -/
theorem intervalIntegrable_star {f : ℝ → P →L[ℂ] P}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun u => star (f u)) volume a b := by
  obtain ⟨L, hL⟩ := exists_linearIsometry_star (P := P)
  have h1 := L.toContinuousLinearMap.integrable_comp hf.1
  have h2 := L.toContinuousLinearMap.integrable_comp hf.2
  simp only [LinearIsometry.coe_toContinuousLinearMap, hL] at h1 h2
  exact ⟨h1, h2⟩

/-- The adjoint of the integrand `-i A B` is `i B* A*`. -/
theorem star_neg_I_smul_mul (A B : P →L[ℂ] P) :
    star ((-Complex.I) • (A * B)) = Complex.I • (star B * star A) := by
  rw [star_smul, star_mul]
  simp [Complex.conj_I]

/-- The integrand `i U* H*` of the adjoint equation is interval integrable. -/
theorem SolvesIntegralOn.intervalIntegrable_star_rhs (hU : SolvesIntegralOn H U a b) :
    IntervalIntegrable (fun u => Complex.I • (star (U u) * star (H u))) volume a b := by
  have h := intervalIntegrable_star hU.intervalIntegrable_rhs
  simp only [star_neg_I_smul_mul] at h
  exact h

/-- **The adjoint equation**: `U*(s) = U*(a) + ∫_a^s i U*(u) H(u)* du` on `[a, b]`. -/
theorem SolvesIntegralOn.star_eq (hU : SolvesIntegralOn H U a b) :
    ∀ s ∈ Icc a b,
      star (U s) = star (U a) + ∫ u in a..s, Complex.I • (star (U u) * star (H u)) := by
  intro s hs
  rw [hU.2 s hs, star_add, star_intervalIntegral]
  congr 1
  exact intervalIntegral.integral_congr fun u _ => star_neg_I_smul_mul _ _

/-- **Conservation of `U* U`**: for a path that is self-adjoint at almost every time of
`[a, b]`, an integral-sense solution obeys `U(s)* U(s) = U(a)* U(a)` on `[a, b]`. -/
theorem SolvesIntegralOn.star_mul_self (hU : SolvesIntegralOn H U a b)
    (hH : ∀ᵐ u, u ∈ Icc a b → star (H u) = H u) :
    ∀ s ∈ Icc a b, star (U s) * U s = star (U a) * U a := by
  intro s hs
  have hab : a ≤ b := hs.1.trans hs.2
  rw [Calculus.mul_eq_add_integral hab hU.intervalIntegrable_star_rhs hU.intervalIntegrable_rhs
    hU.star_eq hU.2 s hs, add_eq_left]
  have hzero : ∀ᵐ u, u ∈ uIoc a s →
      Complex.I • (star (U u) * star (H u)) * U u + star (U u) * ((-Complex.I) • (H u * U u)) =
        (fun _ => (0 : P →L[ℂ] P)) u := by
    filter_upwards [hH] with u hu hmem
    rw [uIoc_of_le hs.1] at hmem
    rw [hu ⟨hmem.1.le, hmem.2.trans hs.2⟩, smul_mul_assoc, mul_smul_comm, neg_smul, mul_assoc,
      add_neg_cancel]
  rw [intervalIntegral.integral_congr_ae hzero, intervalIntegral.integral_zero]

/-- An integral-sense solution from the identity at `a` of an almost-everywhere self-adjoint
path preserves norms on `[a, b]`. -/
theorem SolvesIntegralOn.norm_apply (hU : SolvesIntegralOn H U a b) (hUa : U a = 1)
    (hH : ∀ᵐ u, u ∈ Icc a b → star (H u) = H u) :
    ∀ s ∈ Icc a b, ∀ v : P, ‖U s v‖ = ‖v‖ := by
  intro s hs v
  have h : star (U s) * U s = 1 := by
    rw [hU.star_mul_self hH s hs, hUa, star_one, one_mul]
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (U s)).mpr h v

/-- An integral-sense solution from the identity at `a` of an almost-everywhere self-adjoint
path is a contraction on `[a, b]`. -/
theorem SolvesIntegralOn.norm_le_one (hU : SolvesIntegralOn H U a b) (hUa : U a = 1)
    (hH : ∀ᵐ u, u ∈ Icc a b → star (H u) = H u) :
    ∀ s ∈ Icc a b, ‖U s‖ ≤ 1 := by
  intro s hs
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [hU.norm_apply hUa hH s hs v, one_mul]

/-- The propagator of an almost-everywhere self-adjoint path is an isometry:
`U(s)* U(s) = 1` on `[0, T]`. -/
theorem IsPropagator.star_mul_self (hU : IsPropagator H U T)
    (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) :
    ∀ s ∈ Icc 0 T, star (U s) * U s = 1 := by
  intro s hs
  rw [hU.2.star_mul_self hH s hs, hU.1, star_one, one_mul]

/-- The propagator of an almost-everywhere self-adjoint, interval-integrable path is
co-isometric: `U(s) U(s)* = 1` on `[0, T]`. -/
theorem IsPropagator.mul_star_self (hU : IsPropagator H U T)
    (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) (hint : IntervalIntegrable H volume 0 T) :
    ∀ s ∈ Icc 0 T, U s * star (U s) = 1 := by
  intro s hs
  have hT : 0 ≤ T := hs.1.trans hs.2
  have hprod := Calculus.mul_eq_add_integral hT hU.2.intervalIntegrable_rhs
    hU.2.intervalIntegrable_star_rhs hU.2.2 hU.2.star_eq
  set D : ℝ → P →L[ℂ] P := fun u => U u * star (U u) - 1 with hD
  have hDc : ContinuousOn D (Icc 0 T) :=
    ((hU.continuousOn hT).mul (continuous_star.comp_continuousOn (hU.continuousOn hT))).sub
      continuousOn_const
  have hDint : ∀ r ∈ Icc 0 T,
      D r = ∫ u in (0 : ℝ)..r, (-Complex.I) • (H u * D u - D u * H u) := by
    intro r hr
    have h := hprod r hr
    rw [hU.1, star_one, mul_one] at h
    simp only [hD, h, add_sub_cancel_left]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hH] with u hu hmem
    rw [uIoc_of_le hr.1] at hmem
    rw [hu ⟨hmem.1.le, hmem.2.trans hr.2⟩]
    simp only [mul_sub, sub_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, mul_assoc,
      smul_sub, neg_smul, neg_mul]
    abel
  have hk : IntervalIntegrable (fun u => 2 * ‖H u‖) volume 0 T := hint.norm.const_mul 2
  have hzero := Calculus.eq_zero_of_norm_le_integral hT hDc hk
    (Eventually.of_forall fun u _ => by positivity) (fun r hr => by
      rw [hDint r hr]
      refine intervalIntegral.norm_integral_le_of_norm_le hr.1
        (Eventually.of_forall fun u _ => ?_) ?_
      · rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
        calc ‖H u * D u - D u * H u‖ ≤ ‖H u * D u‖ + ‖D u * H u‖ := norm_sub_le _ _
          _ ≤ ‖H u‖ * ‖D u‖ + ‖D u‖ * ‖H u‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
          _ = 2 * ‖H u‖ * ‖D u‖ := by ring
      · refine (hk.mono_set ?_).mul_continuousOn ?_
        · rw [uIcc_of_le hr.1, uIcc_of_le hT]
          exact Icc_subset_Icc_right hr.2
        · rw [uIcc_of_le hr.1]
          exact (hDc.mono (Icc_subset_Icc_right hr.2)).norm) s hs
  exact sub_eq_zero.mp hzero

/-- **Unitarity**: the propagator of an almost-everywhere self-adjoint, interval-integrable
path is unitary at every time of `[0, T]`. -/
theorem IsPropagator.isUnitary (hU : IsPropagator H U T)
    (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) (hint : IntervalIntegrable H volume 0 T) :
    ∀ s ∈ Icc 0 T, IsUnitary (U s) :=
  fun s hs => ⟨hU.star_mul_self hH s hs, hU.mul_star_self hH hint s hs⟩

/-- The propagator of an almost-everywhere self-adjoint path preserves norms on `[0, T]`. -/
theorem IsPropagator.norm_apply (hU : IsPropagator H U T)
    (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) :
    ∀ s ∈ Icc 0 T, ∀ v : P, ‖U s v‖ = ‖v‖ :=
  hU.2.norm_apply hU.1 hH

/-- The propagator of an almost-everywhere self-adjoint path is a contraction on `[0, T]`. -/
theorem IsPropagator.norm_le_one (hU : IsPropagator H U T)
    (hH : ∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) :
    ∀ s ∈ Icc 0 T, ‖U s‖ ≤ 1 :=
  hU.2.norm_le_one hU.1 hH

end

end IntegrablePathSimulation.Propagator
