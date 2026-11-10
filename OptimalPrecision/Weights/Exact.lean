import OptimalPrecision.Weights.Profile
import OptimalPrecision.Weights.Dual

/-!
# Exact clock moments (Theorem `opt:thm:weights`, moment identities)

Let `φ(t) = e^{-t} P(t)` be the extraction function `opt:eq:phi`, presented by
its Taylor data `d_i = (c_{2,i} - c_{1,i})/ℓ` at the delay `a = qM`, and let
`ψ = e^{-t} Q(t)` solve `ψ - ψ' = 4φ` (`opt:eq:psi`), i.e. `Q = 4 (1 + x)^{-1} P`
with `x = -∂`. Expanding `Q = ∑_{k ≤ D_*} β_k lag_k` with real `β_k` and putting
`λ_{k+1} = ((k+1)/2)(-1)^k β_k` (`opt:eq:weights`), this file proves

  `∑_{j=1}^n λ_j Ces_j(V R^k ξ^m) = δ_{m0}`   (`0 ≤ m ≤ k < M`),

which is `opt:eq:clock-moments`. The proof is algebraic: the clock profile of
`e^{-aξ} g` is `x^{-2} p(x) P` whenever `g = p(ξ)` (`prof_one_eq`,
`prof_aeval_mul`), and the extraction rule `L(s) = ev_a(s(x) P)` satisfies the
partial-fraction identities of `Resolvent` (`Dual.hyp_mixture`).
-/

namespace OptimalPrecision

noncomputable section

open Nat Finset Filter Complex Polynomial
open scoped Topology Polynomial
open ExpPoly Resolvent Dual Gamma

/-! ### The profile of the constant function -/

theorem coeff_one_fun : coeff (fun _ : ℂ => (1 : ℂ)) = fun i => if i = 0 then 1 else 0 := by
  funext i; rw [coeff_const]

/-- `prof(1) = ¼ (x^{-2} + x^{-1}) ∑_k β_k lag_k`, from `cesPoly_signed`. -/
theorem prof_one (n : ℕ) (β : ℕ → ℝ) :
    prof n β (coeff (fun _ : ℂ => (1 : ℂ))) =
      (1 / 4 : ℂ) • op ((xs : PowerSeries ℂ)⁻¹ ^ 2 + xs⁻¹) (∑ k ∈ range n, (β k : ℂ) • lag k) := by
  have hinner : ∀ l : ℕ, ∑ i ∈ range (l + 1),
      (if i = 0 then (1 : ℂ) else 0) • (lagE (l - i) : ℂ[X]) = lagE l := by
    intro l
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; simp at h
  rw [coeff_one_fun, prof, op_sum_right, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ∑ l ∈ range (k + 1), ((k + 1 - l : ℕ) : ℂ) • ∑ i ∈ range (l + 1),
      (if i = 0 then (1 : ℂ) else 0) • (lagE (l - i) : ℂ[X]) = cesPoly k := by
    unfold cesPoly
    exact Finset.sum_congr rfl fun l _ => by rw [hinner]
  rw [hk, op_smul_right, op_ramp_lag, ← cesPoly_signed]
  simp only [smul_smul]
  congr 1
  ring

/-- **The profile of the constant function** is `x^{-2} P` once `∑ β_k lag_k = 4 (1+x)^{-1} P`. -/
theorem prof_one_eq (n : ℕ) (β : ℕ → ℝ) (P : ℂ[X])
    (hβ : ∑ k ∈ range n, (β k : ℂ) • (lag k : ℂ[X]) = (4 : ℂ) • op (1 + xs)⁻¹ P) :
    prof n β (coeff (fun _ : ℂ => (1 : ℂ))) = op ((xs : PowerSeries ℂ)⁻¹ ^ 2) P := by
  rw [prof_one, hβ, op_smul_right, smul_smul, ← op_mul]
  have h2 : PowerSeries.constantCoeff (1 + xs : PowerSeries ℂ) ≠ 0 := by
    rw [map_add, map_one, constantCoeff_xs]; norm_num
  have hx : (xs : PowerSeries ℂ) * xs⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_xs]; exact one_ne_zero)
  have h1 : (1 + xs : PowerSeries ℂ) * (1 + xs)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ h2
  have hS : ((xs : PowerSeries ℂ)⁻¹ ^ 2 + xs⁻¹) * (1 + xs)⁻¹ = xs⁻¹ ^ 2 := by
    calc ((xs : PowerSeries ℂ)⁻¹ ^ 2 + xs⁻¹) * (1 + xs)⁻¹
        = xs⁻¹ ^ 2 * ((1 + xs) * (1 + xs)⁻¹) + xs⁻¹ * (1 + xs)⁻¹ * (1 - xs * xs⁻¹) := by ring
      _ = xs⁻¹ ^ 2 := by rw [h1, hx]; ring
  rw [hS]
  norm_num

/-! ### The extraction polynomial and the Laguerre coordinates -/

section Data

variable (q : ℝ) (M : ℕ)

/-- Polynomial part of the extraction function `φ = e^{-t} P(t)` over `ℝ`. -/
def PR : ℝ[X] :=
  shifted (q * M) (Real.exp (q * M)) (fun i => (diffR q M).coeff i) (Dstar q M)

/-- Polynomial part of `φ` over `ℂ`. -/
def PC : ℂ[X] :=
  shifted ((q * M : ℝ) : ℂ) (Complex.exp ((q * M : ℝ) : ℂ)) (fun i => (diffC q M).coeff i)
    (Dstar q M)

theorem PR_map : (PR q M).map Complex.ofRealHom = PC q M := by
  rw [PR, shifted_map, PC]
  congr 1
  · rw [Complex.ofRealHom_eq_coe, Complex.ofReal_exp]
  · funext i; rw [diffC, coeff_map]

/-- Polynomial part of `ψ = 4 ∫_0^∞ e^{-v} φ(t+v) dv`, i.e. `Q = 4 (1 + x)^{-1} P`. -/
def QR : ℝ[X] := (4 : ℝ) • op ((1 + xs : PowerSeries ℝ)⁻¹) (PR q M)

theorem natDegree_QR_le : (QR q M).natDegree ≤ Dstar q M :=
  (natDegree_smul_le _ _).trans ((natDegree_op_le _ _).trans (natDegree_shifted_le _ _ _ _))

/-- The real Laguerre coordinates `β_k` of `ψ`. -/
def beta : ℕ → ℝ :=
  Classical.choose (exists_lag_expansion (Dstar q M) (QR q M) (natDegree_QR_le q M))

theorem beta_spec : QR q M = ∑ k ∈ range (Dstar q M + 1), beta q M k • lag k :=
  Classical.choose_spec (exists_lag_expansion (Dstar q M) (QR q M) (natDegree_QR_le q M))

theorem beta_spec_complex :
    ∑ k ∈ range (Dstar q M + 1), (beta q M k : ℂ) • (lag k : ℂ[X]) =
      (4 : ℂ) • op (1 + xs)⁻¹ (PC q M) := by
  have h := congrArg (Polynomial.map Complex.ofRealHom) (beta_spec q M)
  rw [Polynomial.map_sum] at h
  simp only [Polynomial.map_smul, lag_map, QR, op_map, map_inv_powerSeries, map_add, map_one,
    map_xs, PR_map, Complex.ofRealHom_eq_coe] at h
  rw [← h]
  norm_num

end Data

/-! ### The moment identities -/

/-- `R(w) = (1 - ξ²)/(1 + q²ξ²)` (`opt:eq:xi-R`). -/
def Rfun (q : ℝ) (w : ℂ) : ℂ := (1 - xi w ^ 2) / (1 + (q : ℂ) ^ 2 * xi w ^ 2)

theorem xi_zero : xi 0 = 1 := by simp [xi]

theorem one_add_sq_mul_xi_ne_zero_at (q : ℝ) : 1 + (q : ℂ) ^ 2 * xi 0 ^ 2 ≠ 0 := by
  rw [xi_zero, one_pow, mul_one]
  exact_mod_cast (by positivity : (0 : ℝ) < 1 + q ^ 2).ne'

theorem analyticAt_Rfun (q : ℝ) : AnalyticAt ℂ (Rfun q) 0 := by
  have hξ := analyticAt_xi
  exact (analyticAt_const.sub (hξ.pow 2)).div
    (analyticAt_const.add (analyticAt_const.mul (hξ.pow 2))) (one_add_sq_mul_xi_ne_zero_at q)

theorem eventually_den_ne (q : ℝ) : ∀ᶠ w in 𝓝 (0 : ℂ), 1 + (q : ℂ) ^ 2 * xi w ^ 2 ≠ 0 := by
  have hc : ContinuousAt (fun w => 1 + (q : ℂ) ^ 2 * xi w ^ 2) 0 :=
    (analyticAt_const.add (analyticAt_const.mul (analyticAt_xi.pow 2))).continuousAt
  exact hc.eventually_ne (one_add_sq_mul_xi_ne_zero_at q)

theorem aeval_xs_C (c : ℂ) : Polynomial.aeval (xs : PowerSeries ℂ) (C c) = PowerSeries.C c := by
  rw [aeval_C, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- Evaluation of `L` on the expanded resolvent words (`r`-th binomial term). -/
theorem pair_term {q : ℝ} {M : ℕ} (hq : 1 ≤ q) (hM : 1 ≤ M) {k m r : ℕ} (hkM : k < M)
    (hmk : m ≤ k) (hr : r ≤ k) :
    pair (Dstar q M) (diffC q M)
        (xs ^ (2 * r + m) * (xs : PowerSeries ℂ)⁻¹ ^ 2 * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k) =
      if 2 * r + m = 0 then (-cq q)⁻¹ ^ k * (cq q)⁻¹ ^ k else 0 := by
  have h := hyp_mixture hq hM
  have hd₀ : 3 * M ≤ d0 (q * M) := by
    unfold d0
    have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have : (3 * M : ℝ) ≤ 12 * (q * M) := by nlinarith
    exact_mod_cast this.trans (Nat.le_ceil _)
  have hd₀pos : 0 < d0 (q * M) := by omega
  have hx : (xs : PowerSeries ℂ) * xs⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_xs]; exact one_ne_zero)
  rcases Nat.lt_or_ge (2 * r + m) 2 with hj | hj
  · rcases Nat.lt_or_ge (2 * r + m) 1 with hj' | hj'
    · have hz : 2 * r + m = 0 := by omega
      rw [if_pos hz, hz, pow_zero, one_mul]
      exact value_neg_two h hd₀pos (k + k) k k rfl hkM.le hkM.le
    · have hz : 2 * r + m = 1 := by omega
      rw [if_neg (by omega), hz]
      have : xs ^ 1 * (xs : PowerSeries ℂ)⁻¹ ^ 2 * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k =
          u⁻¹ * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k := by
        calc xs ^ 1 * (xs : PowerSeries ℂ)⁻¹ ^ 2 * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k =
            (xs * xs⁻¹) * xs⁻¹ * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k := by ring
          _ = _ := by rw [hx, one_mul]
      rw [this]
      exact vanish_neg_one h hd₀pos (k + k) k k rfl hkM.le hkM.le
  · rw [if_neg (by omega)]
    obtain ⟨j, hj⟩ : ∃ j, 2 * r + m = j + 2 := ⟨2 * r + m - 2, by omega⟩
    have : xs ^ (2 * r + m) * (xs : PowerSeries ℂ)⁻¹ ^ 2 * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k =
        u ^ j * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k := by
      calc xs ^ (2 * r + m) * (xs : PowerSeries ℂ)⁻¹ ^ 2 * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k =
          xs ^ j * (xs * xs⁻¹) ^ 2 * (v (cq q))⁻¹ ^ k * (v' (cq q))⁻¹ ^ k := by rw [hj]; ring
        _ = _ := by rw [hx, one_pow, mul_one]
    rw [this]
    exact vanish_nonneg h j k k (by omega) hkM.le hkM.le

/-- **Exact clock moments** (`opt:eq:clock-moments`). -/
theorem lamSum_moment {q : ℝ} {M : ℕ} (hq : 1 ≤ q) (hM : 1 ≤ M) {k m : ℕ} (hmk : m ≤ k)
    (hkM : k < M) :
    lamSum (Dstar q M + 1) (beta q M)
        (fun w => vt ((q * M : ℝ) : ℂ) w * (Rfun q w ^ k * xi w ^ m)) =
      if m = 0 then 1 else 0 := by
  set n := Dstar q M + 1
  set c := cq q
  set g : ℂ → ℂ := fun w => Rfun q w ^ k * xi w ^ m with hg_def
  have hg : AnalyticAt ℂ g 0 := ((analyticAt_Rfun q).pow k).mul (analyticAt_xi.pow m)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show (0 : ℝ) < q by linarith).ne'
  -- the polynomials `Pc(X) = ((X - c)(X + c))^k` and `Ph(X) = q^{-2k} (1 - X²)^k X^m`
  set s : ℂ := ((q : ℂ) ^ 2)⁻¹ ^ k
  set Pc : ℂ[X] := ((X - C c) * (X + C c)) ^ k
  set Ph : ℂ[X] := C s * (1 - X ^ 2) ^ k * X ^ m
  have hfun : (fun w => Pc.eval (xi w) * g w) =ᶠ[𝓝 0]
      (fun w => Ph.eval (xi w) * (fun _ => (1 : ℂ)) w) := by
    filter_upwards [eventually_den_ne q] with w hw
    simp only [Pc, Ph, hg_def, Rfun, eval_pow, eval_mul, eval_sub, eval_add, eval_X, eval_C,
      eval_one, mul_one]
    have hc2 : c * c = -((q : ℂ) ^ 2)⁻¹ := by
      simp only [c, cq]; linear_combination (1 / (q : ℂ) ^ 2) * Complex.I_sq
    have key : (xi w - c) * (xi w + c) * ((1 - xi w ^ 2) / (1 + (q : ℂ) ^ 2 * xi w ^ 2)) =
        ((q : ℂ) ^ 2)⁻¹ * (1 - xi w ^ 2) := by
      have : (xi w - c) * (xi w + c) = ((q : ℂ) ^ 2)⁻¹ * (1 + (q : ℂ) ^ 2 * xi w ^ 2) := by
        have : (xi w - c) * (xi w + c) = xi w ^ 2 - c * c := by ring
        rw [this, hc2]; field_simp; ring
      rw [this]; field_simp
    calc ((xi w - c) * (xi w + c)) ^ k * (((1 - xi w ^ 2) / (1 + (q : ℂ) ^ 2 * xi w ^ 2)) ^ k *
          xi w ^ m) =
        ((xi w - c) * (xi w + c) * ((1 - xi w ^ 2) / (1 + (q : ℂ) ^ 2 * xi w ^ 2))) ^ k *
          xi w ^ m := by rw [← mul_assoc, ← mul_pow]
      _ = s * (1 - xi w ^ 2) ^ k * xi w ^ m := by rw [key, mul_pow]
  -- profile identities
  have hprofPc := prof_aeval_mul n (beta q M) Pc hg
  have hprofPh := prof_aeval_mul n (beta q M) Ph (g := fun _ => (1 : ℂ)) analyticAt_const
  have hcoeffeq : coeff (fun w => Pc.eval (xi w) * g w) =
      coeff (fun w => Ph.eval (xi w) * (fun _ => (1 : ℂ)) w) := funext (coeff_congr hfun)
  rw [hcoeffeq, hprofPh, prof_one_eq n (beta q M) (PC q M) (beta_spec_complex q M)] at hprofPc
  -- `aeval x Pc = ((x - c)(x + c))^k`
  have hPc : Polynomial.aeval (xs : PowerSeries ℂ) Pc = (v c * v' c) ^ k := by
    simp only [Pc, map_pow, map_mul, map_sub, map_add, aeval_X, aeval_xs_C, v, v', u]
  have hPh : Polynomial.aeval (xs : PowerSeries ℂ) Ph =
      PowerSeries.C s * (1 - xs ^ 2) ^ k * xs ^ m := by
    simp only [Ph, map_pow, map_mul, map_sub, map_one, aeval_X, aeval_xs_C]
  rw [hPc, hPh] at hprofPc
  -- invert `((x - c)(x + c))^k`
  have hvv : (v c)⁻¹ ^ k * (v' c)⁻¹ ^ k * (v c * v' c) ^ k = 1 := by
    have h1 : (v c)⁻¹ * v c = 1 :=
      PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_v]; exact one_sub_cq_ne_zero)
    have h2 : (v' c)⁻¹ * v' c = 1 :=
      PowerSeries.inv_mul_cancel _ (by rw [constantCoeff_v']; exact one_add_cq_ne_zero)
    calc (v c)⁻¹ ^ k * (v' c)⁻¹ ^ k * (v c * v' c) ^ k =
          ((v c)⁻¹ * v c) ^ k * ((v' c)⁻¹ * v' c) ^ k := by
          ring
      _ = 1 := by rw [h1, h2, one_pow, one_mul]
  have hprof : prof n (beta q M) (coeff g) =
      op ((v c)⁻¹ ^ k * (v' c)⁻¹ ^ k * (PowerSeries.C s * (1 - xs ^ 2) ^ k * xs ^ m) *
        (xs : PowerSeries ℂ)⁻¹ ^ 2) (PC q M) := by
    have e1 : prof n (beta q M) (coeff g) = op ((v c)⁻¹ ^ k * (v' c)⁻¹ ^ k)
        (op ((v c * v' c) ^ k) (prof n (beta q M) (coeff g))) := by
      rw [← op_mul, hvv, op_one]
    rw [e1, ← hprofPc]
    simp only [← op_mul]
    congr 1
    ring
  -- the clock is the extraction rule
  have hfun2 : (fun w => vt ((q * M : ℝ) : ℂ) w * (Rfun q w ^ k * xi w ^ m)) =
      fun w => vt ((q * M : ℝ) : ℂ) w * g w := rfl
  rw [hfun2, lamSum_vt_mul n (beta q M) hg, hprof, PC, ev_op_shifted, ← pair_apply]
  -- expand `(1 - x²)^k`
  have hbin : (1 - xs ^ 2 : PowerSeries ℂ) ^ k =
      ∑ r ∈ range (k + 1), PowerSeries.C ((-1 : ℂ) ^ r * (k.choose r : ℂ)) * xs ^ (2 * r) := by
    rw [show (1 - xs ^ 2 : PowerSeries ℂ) = -(xs ^ 2) + 1 by ring, add_pow]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_pow, mul_one, map_mul, map_pow, map_neg, map_one, map_natCast, neg_pow, ← pow_mul]
    ring
  have hW : (v c)⁻¹ ^ k * (v' c)⁻¹ ^ k * (PowerSeries.C s * (1 - xs ^ 2) ^ k * xs ^ m) *
      (xs : PowerSeries ℂ)⁻¹ ^ 2 =
      ∑ r ∈ range (k + 1), PowerSeries.C (s * ((-1 : ℂ) ^ r * (k.choose r : ℂ))) *
        (xs ^ (2 * r + m) * (xs : PowerSeries ℂ)⁻¹ ^ 2 * (v c)⁻¹ ^ k * (v' c)⁻¹ ^ k) := by
    rw [hbin]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [map_mul, pow_add]
    ring
  rw [hW, map_sum]
  simp only [← PowerSeries.smul_eq_C_mul, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single 0]
  · rw [pair_term hq hM hkM hmk (Nat.zero_le k)]
    simp only [mul_zero, zero_add, pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    split_ifs with hm
    · -- `s (-c)^{-k} c^{-k} = 1`
      simp only [s, cq, ← mul_pow]
      rw [← one_pow k]
      congr 1
      field_simp
      rw [Complex.I_sq]
    · exact mul_zero s
  · intro r hr hr0
    rw [pair_term hq hM hkM hmk (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)), if_neg (by omega),
      mul_zero]
  · intro h; simp at h

end

end OptimalPrecision
