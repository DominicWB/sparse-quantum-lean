import SparseLowerBounds.Helpers.Adversary.ProjNorm

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The generic multiplicative adversary

This is the weight-growth argument shared by the proofs of `qlsl:lem:xor`
and `hsl:lem:search`, stated
for an arbitrary single-register weight `w` so that both lower bounds reuse it.

The hidden input `j : Fin n → Fin m` is purified into `n` registers
(`Joint`). The weight is `W = w^{⊗ n}` (`Joint.tensorPow w`). For a
`D_a = 1 - 2|a⟩⟨a|` bound `‖w D_a w⁻¹‖ ≤ λ` with `1 ≤ λ`:

* (i) one one-hot Boolean query multiplies `‖W Ψ‖` by at most `λ`
  (`norm_tensorPow_query`); in the Hadamard basis of the response the query
  is block diagonal with blocks `1` and `D_a` on one hidden register
  (`fiber_oneHotOracle`, proof of Lemma `qlsl:lem:xor` and proof of Lemma `hsl:lem:search`);
* (ii) fixed unitaries do not change `‖W Ψ‖` (`norm_tensorPow_fixed`);
* (iii) a whole program multiplies it by at most `λ^count`, inverse queries
  included (`norm_tensorPow_program`, eq. `qlsl:eq:weightgrowth`);
* (iv) for Hermitian `w`, the parity correlation is controlled by
  `μ = ‖w⁻¹ Z w⁻¹‖`: `|Σ_j σ_j ⟪Ψ_j, M Ψ_j⟫| ≤ μⁿ ‖M‖ ‖W Ψ‖²`
  (`correlation_le`, proof of Lemma `qlsl:lem:xor` and proof of Lemma `hsl:lem:search`);
* (v) the packaged average-correlation bound for a program run on an
  input-independent seed, when `w u = u` (`program_correlation_le`).

The joint state is not normalised by `m^{-n/2}`; instead (v) divides by `mⁿ`.
-/

namespace SparseLowerBounds.Adversary

noncomputable section
open SparseHamiltonian OracleCircuit Joint
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {n m : ℕ}

/-- The query block `D_a = 1 - 2 |a⟩⟨a|` on one hidden-position register. -/
def reflect (a : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun b => if b = a then -1 else 1

/-- The parity observable `Z = Σ_b (-1)^b |b⟩⟨b|` on one hidden register. -/
def parityZ (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.diagonal fun b => (-1) ^ (b : ℕ)

omit [CompleteSpace K] in
/-- Components of a finite sum of joint states. -/
theorem joint_sum_apply {ι : Type*} (s : Finset ι) (f : ι → Joint (Fin n → Fin m) K)
    (j : Fin n → Fin m) : (∑ i ∈ s, f i) j = ∑ i ∈ s, f i j := by
  simpa only [Joint.proj_apply] using map_sum (Joint.proj (K := K) j) f s

omit [CompleteSpace K] in
/-- `W⁻¹ W = 1`. -/
theorem tensorPow_inv_mul (w : Matrix (Fin m) (Fin m) ℂ) (hw : IsUnit w) :
    (tensorPow w⁻¹ * tensorPow w : Joint (Fin n → Fin m) K →L[ℂ] _) = 1 := by
  rw [tensorPow_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det w).mp hw),
    tensorPow_one]

omit [CompleteSpace K] in
/-- `W W⁻¹ = 1`. -/
theorem tensorPow_mul_inv (w : Matrix (Fin m) (Fin m) ℂ) (hw : IsUnit w) :
    (tensorPow w * tensorPow w⁻¹ : Joint (Fin n → Fin m) K →L[ℂ] _) = 1 := by
  rw [tensorPow_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det w).mp hw),
    tensorPow_one]

omit [CompleteSpace K] in
/-- `Z^{⊗ n}` multiplies branch `j` by its parity `σ(j)`. -/
theorem tensorPow_Z_apply (Ψ : Joint (Fin n → Fin m) K) (j : Fin n → Fin m) :
    tensorPow (parityZ m) Ψ j = (parity j : ℂ) • Ψ j := by
  rw [parityZ, tensorPow_diagonal, fiber_apply, smul_apply, one_apply_eq_self, parity_eq_prod]
  push_cast
  rfl

/-- **Block form of a Boolean one-hot query** (proof of Lemma `qlsl:lem:xor`): with
`R = 1 - Σ P`, the joint query is `R ⊗ 1 + Σ_{k,a} P (k,a) ⊗ D_a^{(k)}`, where
`D_a^{(k)}` acts on hidden register `k`. -/
theorem fiber_oneHotOracle (P : ProjFamily K (Fin n × Fin m)) :
    fiber (oneHotOracle P) =
      fiber (fun _ => P.rest) +
        ∑ ka : Fin n × Fin m, fiber (fun _ => P.proj ka) * onReg ka.1 (reflect ka.2) := by
  have hD : ∀ ka : Fin n × Fin m,
      (fiber (fun _ => P.proj ka) * onReg ka.1 (reflect ka.2) :
        Joint (Fin n → Fin m) K →L[ℂ] _) =
      fiber fun j => (if j ka.1 = ka.2 then (-1 : ℂ) else 1) • P.proj ka := by
    intro ka
    rw [reflect, onReg_diagonal, fiber_mul]
    congr 1
    funext j
    simp only [mul_smul_comm, mul_one]
  simp_rw [hD]
  refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun j => ?_
  have h2 : ∀ x : K, ∑ ka : Fin n × Fin m, (if j ka.1 = ka.2 then P.proj ka x else 0) =
      ∑ k, P.proj (k, j k) x := by
    intro x
    rw [Fintype.sum_prod_type]
    simp
  have h1 : ∀ (x : K) (ka : Fin n × Fin m),
      (if j ka.1 = ka.2 then (-1 : ℂ) else 1) • P.proj ka x =
        P.proj ka x - (2 : ℂ) • (if j ka.1 = ka.2 then P.proj ka x else 0) := by
    intro x ka
    split_ifs
    · rw [neg_one_smul, two_smul]; abel
    · simp
  simp only [add_apply, PiLp.add_apply, sum_apply, joint_sum_apply, fiber_apply,
    oneHotOracle_eq, ProjFamily.rest, sub_apply, one_apply_eq_self, smul_apply]
  rw [Finset.sum_congr rfl fun ka _ => h1 (Ψ j) ka, Finset.sum_sub_distrib, ← Finset.smul_sum,
    h2]
  abel

/-- The conjugated query `R ⊗ 1 + Σ P_i ⊗ B_i` has norm at most `λ` when every
`B_i` does and commutes with `P_i ⊗ 1`. -/
theorem norm_block_apply_le (P : ProjFamily K (Fin n × Fin m))
    (B : Fin n × Fin m → Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K)
    {lam : ℝ} (hlam : 1 ≤ lam) (hB : ∀ ka, ‖B ka‖ ≤ lam)
    (hBc : ∀ ka, B ka * fiber (fun _ => P.proj ka) = fiber (fun _ => P.proj ka) * B ka)
    (y : Joint (Fin n → Fin m) K) :
    ‖((fiber (fun _ => P.rest) + ∑ ka, fiber (fun _ => P.proj ka) * B ka :
      Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) y)‖ ≤ lam * ‖y‖ := by
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  have hsum : P.rest + ∑ ka, P.proj ka = 1 := by
    rw [ProjFamily.rest, sub_add_cancel]
  have hpt : ∀ j, ((fiber (fun _ => P.rest) + ∑ ka, fiber (fun _ => P.proj ka) * B ka :
      Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) y) j =
      P.rest (y j) + ∑ ka, P.proj ka ((B ka y) j) := by
    intro j
    rw [add_apply, PiLp.add_apply, fiber_apply, sum_apply, joint_sum_apply]
    rfl
  have hpiece : ∀ ka, ∑ j, ‖P.proj ka ((B ka y) j)‖ ^ 2 ≤
      lam ^ 2 * ∑ j, ‖P.proj ka (y j)‖ ^ 2 := by
    intro ka
    have e1 : ∑ j, ‖P.proj ka ((B ka y) j)‖ ^ 2 =
        ‖B ka (fiber (fun _ => P.proj ka) y)‖ ^ 2 := by
      rw [← mul_apply_eq_comp (B ka), hBc, PiLp.norm_sq_eq_of_L2]
      rfl
    have e2 : ∑ j, ‖P.proj ka (y j)‖ ^ 2 = ‖fiber (fun _ => P.proj ka) y‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      rfl
    rw [e1, e2, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (((B ka).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hB ka) (norm_nonneg _))) 2
  have hdec : ∀ x : K, ‖x‖ ^ 2 = ‖P.rest x‖ ^ 2 + ∑ ka, ‖P.proj ka x‖ ^ 2 := fun x =>
    Helpers.Adversary.norm_sq_eq_add_sum P.rest P.proj P.isStarProjection_rest
      P.isStarProjection hsum x
  have hcomb : ∀ j, ‖P.rest (y j) + ∑ ka, P.proj ka ((B ka y) j)‖ ^ 2 =
      ‖P.rest (y j)‖ ^ 2 + ∑ ka, ‖P.proj ka ((B ka y) j)‖ ^ 2 := fun j =>
    Helpers.Adversary.norm_sq_add_sum_apply P.rest P.proj P.isStarProjection_rest
      P.isStarProjection hsum P.rest_mul_proj P.proj_mul_rest P.orthogonal (y j)
      (fun ka => (B ka y) j)
  have hsq : ‖((fiber (fun _ => P.rest) + ∑ ka, fiber (fun _ => P.proj ka) * B ka :
      Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) y)‖ ^ 2 ≤
      (lam * ‖y‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp_rw [hpt, hcomb]
    rw [Finset.sum_add_distrib, Finset.sum_comm, mul_pow, PiLp.norm_sq_eq_of_L2,
      Finset.sum_congr rfl fun j _ => hdec (y j)]
    rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun j ka => ‖P.proj ka (y j)‖ ^ 2),
      mul_add]
    have hl2 : (1 : ℝ) ≤ lam ^ 2 := one_le_pow₀ hlam
    have hr : ∑ j, ‖P.rest (y j)‖ ^ 2 ≤ lam ^ 2 * ∑ j, ‖P.rest (y j)‖ ^ 2 :=
      le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => by positivity) hl2
    refine add_le_add hr ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun ka _ => hpiece ka
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hlam0 (norm_nonneg _))
    two_ne_zero).mp hsq

/-- Conjugating the joint query by the weight conjugates each block `D_a`. -/
theorem conj_fiber_oneHotOracle (P : ProjFamily K (Fin n × Fin m))
    (w : Matrix (Fin m) (Fin m) ℂ) (hw : IsUnit w) :
    tensorPow w * fiber (oneHotOracle P) * tensorPow w⁻¹ =
      fiber (fun _ => P.rest) +
        ∑ ka : Fin n × Fin m, fiber (fun _ => P.proj ka) * onReg ka.1 (w * reflect ka.2 * w⁻¹) := by
  rw [fiber_oneHotOracle, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  · rw [tensorPow_comm_fiber_const, mul_assoc, tensorPow_mul_inv w hw, mul_one]
  · refine Finset.sum_congr rfl fun ka _ => ?_
    rw [← tensorPow_mul_onReg_mul_tensorPow_inv w hw, ← mul_assoc (tensorPow w),
      tensorPow_comm_fiber_const]
    simp only [mul_assoc]

/-- **(i) One query.** If `‖w D_a w⁻¹‖ ≤ λ` for every position `a` and
`1 ≤ λ`, one one-hot Boolean query multiplies the weighted norm by at most `λ`
(proof of Lemma `qlsl:lem:xor` and proof of Lemma `hsl:lem:search`). -/
theorem norm_tensorPow_query (P : ProjFamily K (Fin n × Fin m))
    (w : Matrix (Fin m) (Fin m) ℂ) (hw : IsUnit w) {lam : ℝ} (hlam : 1 ≤ lam)
    (hD : ∀ a, ‖w * reflect a * w⁻¹‖ ≤ lam) (Ψ : Joint (Fin n → Fin m) K) :
    ‖tensorPow w (fiber (oneHotOracle P) Ψ)‖ ≤ lam * ‖tensorPow w Ψ‖ := by
  have hT : tensorPow w (fiber (oneHotOracle P) Ψ) =
      (tensorPow w * fiber (oneHotOracle P) * tensorPow w⁻¹ :
        Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) (tensorPow w Ψ) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp, ← mul_apply_eq_comp (tensorPow w⁻¹),
      tensorPow_inv_mul w hw, one_apply_eq_self]
  rw [hT, conj_fiber_oneHotOracle P w hw]
  exact norm_block_apply_le P (fun ka => onReg ka.1 (w * reflect ka.2 * w⁻¹)) hlam
    (fun ka => (norm_onReg_le _ _).trans (hD _)) (fun ka => onReg_comm_fiber_const _ _ _) _

/-- **(ii) Fixed gates.** An input-independent unitary commutes with the
weight (`Joint.tensorPow_comm_fiber_const`) and so preserves the weighted
norm (proof of Lemma `qlsl:lem:xor` and proof of Lemma `hsl:lem:search`). -/
theorem norm_tensorPow_fixed (w : Matrix (Fin m) (Fin m) ℂ) (U : K →L[ℂ] K)
    (hU : IsUnitary U) (Ψ : Joint (Fin n → Fin m) K) :
    ‖tensorPow w (fiber (fun _ => U) Ψ)‖ = ‖tensorPow w Ψ‖ := by
  have h : tensorPow w (fiber (fun _ => U) Ψ) = fiber (fun _ => U) (tensorPow w Ψ) := by
    show (tensorPow w * fiber (fun _ => U) : Joint (Fin n → Fin m) K →L[ℂ] _) Ψ =
      (fiber (fun _ => U) * tensorPow w : Joint (Fin n → Fin m) K →L[ℂ] _) Ψ
    rw [tensorPow_comm_fiber_const]
  rw [h]
  exact norm_fiber_apply_of_isometry _ (fun _ => hU.1) _

/-- **(iii) Weight growth, eq. `qlsl:eq:weightgrowth`.** A Boolean one-hot
program multiplies the weighted norm by at most `λ^count`; inverse queries are
counted and obey the same bound, since `star (O_j) = O_j`. -/
theorem norm_tensorPow_program (P : ProjFamily K (Fin n × Fin m))
    (w : Matrix (Fin m) (Fin m) ℂ) (hw : IsUnit w) {lam : ℝ} (hlam : 1 ≤ lam)
    (hD : ∀ a, ‖w * reflect a * w⁻¹‖ ≤ lam) (q : Program (oneHotOracle P))
    (Ψ : Joint (Fin n → Fin m) K) :
    ‖tensorPow w (fiber (fun j => q.eval j) Ψ)‖ ≤ lam ^ q.count * ‖tensorPow w Ψ‖ := by
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  induction q generalizing Ψ with
  | fixed U hU =>
    simp only [Program.eval_fixed, Program.count_fixed, pow_zero, one_mul]
    exact (norm_tensorPow_fixed w U hU Ψ).le
  | query =>
    simp only [Program.eval_query, Program.count_query, pow_one]
    exact norm_tensorPow_query P w hw hlam hD Ψ
  | queryAdjoint =>
    simp only [Program.eval_queryAdjoint, Program.count_queryAdjoint, pow_one,
      star_oneHotOracle]
    exact norm_tensorPow_query P w hw hlam hD Ψ
  | seq p q hp hq =>
    have hfib : fiber (fun j => (Program.seq p q).eval j) Ψ =
        fiber (fun j => p.eval j) (fiber (fun j => q.eval j) Ψ) := rfl
    rw [hfib, Program.count_seq, pow_add]
    calc ‖tensorPow w (fiber (fun j => p.eval j) (fiber (fun j => q.eval j) Ψ))‖
        ≤ lam ^ p.count * ‖tensorPow w (fiber (fun j => q.eval j) Ψ)‖ := hp _
      _ ≤ lam ^ p.count * (lam ^ q.count * ‖tensorPow w Ψ‖) :=
        mul_le_mul_of_nonneg_left (hq Ψ) (pow_nonneg hlam0 _)
      _ = lam ^ p.count * lam ^ q.count * ‖tensorPow w Ψ‖ := by ring

/-- **(iv) Parity correlation.** For a Hermitian invertible weight and any
workspace operator `M`,
`|Σ_j σ_j ⟪Ψ_j, M Ψ_j⟫| ≤ ‖w⁻¹ Z w⁻¹‖ⁿ ‖M‖ ‖W Ψ‖²`; the left side is
`⟪Ψ, (Z^{⊗ n} ⊗ M) Ψ⟫` (proof of Lemma `qlsl:lem:xor` and proof of Lemma `hsl:lem:search`). -/
theorem correlation_le (w : Matrix (Fin m) (Fin m) ℂ) (hwH : w.IsHermitian) (hw : IsUnit w)
    (M : K →L[ℂ] K) (Ψ : Joint (Fin n → Fin m) K) :
    ‖∑ j, (parity j : ℂ) * ⟪Ψ j, M (Ψ j)⟫_ℂ‖ ≤
      ‖w⁻¹ * parityZ m * w⁻¹‖ ^ n * ‖M‖ * ‖tensorPow w Ψ‖ ^ 2 := by
  have hsum : ∑ j, (parity j : ℂ) * ⟪Ψ j, M (Ψ j)⟫_ℂ =
      ⟪Ψ, fiber (fun _ => M) (tensorPow (parityZ m) Ψ)⟫_ℂ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fiber_apply, tensorPow_Z_apply, map_smul, inner_smul_right]
  have hadj : ContinuousLinearMap.adjoint (tensorPow w⁻¹ : Joint (Fin n → Fin m) K →L[ℂ] _) =
      tensorPow w⁻¹ := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_tensorPow, Matrix.conjTranspose_nonsing_inv,
      hwH.eq]
  have key : ∀ y : Joint (Fin n → Fin m) K,
      ‖⟪tensorPow w⁻¹ y, fiber (fun _ => M) (tensorPow (parityZ m) (tensorPow w⁻¹ y))⟫_ℂ‖ ≤
        ‖w⁻¹ * parityZ m * w⁻¹‖ ^ n * ‖M‖ * ‖y‖ ^ 2 := by
    intro y
    have hop : tensorPow w⁻¹ (fiber (fun _ => M) (tensorPow (parityZ m) (tensorPow w⁻¹ y))) =
        (fiber (fun _ => M) * tensorPow (w⁻¹ * parityZ m * w⁻¹) :
          Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) y := by
      rw [← tensorPow_mul, ← tensorPow_mul]
      show (tensorPow w⁻¹ * fiber (fun _ => M) * tensorPow (parityZ m) * tensorPow w⁻¹ :
        Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) y = _
      rw [tensorPow_comm_fiber_const]
      simp only [mul_assoc]
    rw [← ContinuousLinearMap.adjoint_inner_right, hadj, hop]
    have hnorm : ‖(fiber (fun _ => M) * tensorPow (w⁻¹ * parityZ m * w⁻¹) :
        Joint (Fin n → Fin m) K →L[ℂ] _)‖ ≤ ‖M‖ * ‖w⁻¹ * parityZ m * w⁻¹‖ ^ n := by
      have hm := norm_mul_le
        (fiber (fun _ => M) : Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K)
        (tensorPow (w⁻¹ * parityZ m * w⁻¹))
      refine hm.trans ?_
      exact mul_le_mul (norm_fiber_le _ (norm_nonneg M) fun _ => le_rfl)
        (norm_tensorPow_le _) (by positivity) (norm_nonneg M)
    calc ‖⟪y, (fiber (fun _ => M) * tensorPow (w⁻¹ * parityZ m * w⁻¹) :
          Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) y⟫_ℂ‖
        ≤ ‖y‖ * ‖(fiber (fun _ => M) * tensorPow (w⁻¹ * parityZ m * w⁻¹) :
          Joint (Fin n → Fin m) K →L[ℂ] Joint (Fin n → Fin m) K) y‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖y‖ * ((‖M‖ * ‖w⁻¹ * parityZ m * w⁻¹‖ ^ n) * ‖y‖) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))) (norm_nonneg _)
      _ = ‖w⁻¹ * parityZ m * w⁻¹‖ ^ n * ‖M‖ * ‖y‖ ^ 2 := by ring
  have hΨ : tensorPow w⁻¹ (tensorPow w Ψ) = Ψ := by
    rw [← mul_apply_eq_comp, tensorPow_inv_mul w hw, one_apply_eq_self]
  have h := key (tensorPow w Ψ)
  rw [hΨ] at h
  rw [hsum]
  exact h

omit [CompleteSpace K] in
/-- The purified initial state has weighted norm `‖W (Σ_j |j⟩ ⊗ φ)‖² = mⁿ ‖φ‖²`
when `w` fixes the uniform vector, i.e. every row of `w` sums to one
(proof of Lemma `qlsl:lem:xor`: `‖W Ψ₀‖ = 1` after normalisation). -/
theorem norm_tensorPow_const_sq (w : Matrix (Fin m) (Fin m) ℂ)
    (hfix : w *ᵥ (fun _ => 1) = fun _ => 1) (φ : K) :
    ‖(tensorPow w (const φ) : Joint (Fin n → Fin m) K)‖ ^ 2 = (m : ℝ) ^ n * ‖φ‖ ^ 2 := by
  have hrow : ∀ a, ∑ b, w a b = 1 := by
    intro a
    have h := congrFun hfix a
    simpa [Matrix.mulVec, dotProduct] using h
  have hc : (tensorPow w (const φ) : Joint (Fin n → Fin m) K) = const φ := by
    refine PiLp.ext fun j => ?_
    rw [tensorPow_const]
    simp [hrow]
  rw [hc, norm_const_sq]
  simp

/-- **(v) The multiplicative adversary bound.** Let `w` be Hermitian and invertible, fix the uniform
vector `u = m^{-1/2} Σ_b |b⟩` (equivalently `w *ᵥ 1 = 1`), and satisfy `‖w D_a w⁻¹‖ ≤ λ` for every
`a`, with `1 ≤ λ`. Then for every one-hot Boolean program `q` (inverse queries included), every seed
`φ₀` with `‖φ₀‖ ≤ 1` and every workspace operator with `‖M‖ ≤ 1`, the average parity correlation
obeys `|m^{-n} Σ_j σ_j ⟪q_j φ₀, M q_j φ₀⟫| ≤ ‖w⁻¹ Z w⁻¹‖ⁿ λ^{2 count}` (the displayed bounds of the
proof of Lemma `qlsl:lem:xor` and the proof of Lemma `hsl:lem:search`). -/
theorem program_correlation_le (P : ProjFamily K (Fin n × Fin m))
    (w : Matrix (Fin m) (Fin m) ℂ) (hwH : w.IsHermitian) (hw : IsUnit w)
    (hfix : w *ᵥ (fun _ => 1) = fun _ => 1) {lam : ℝ} (hlam : 1 ≤ lam)
    (hD : ∀ a, ‖w * reflect a * w⁻¹‖ ≤ lam) (q : Program (oneHotOracle P))
    (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1) (M : K →L[ℂ] K) (hM : ‖M‖ ≤ 1) :
    ‖((m : ℂ) ^ n)⁻¹ * ∑ j, (parity j : ℂ) * ⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ‖ ≤
      ‖w⁻¹ * parityZ m * w⁻¹‖ ^ n * lam ^ (2 * q.count) := by
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  set μ := ‖w⁻¹ * parityZ m * w⁻¹‖ with hμ
  have hμ0 : 0 ≤ μ := norm_nonneg _
  let Ψ : Joint (Fin n → Fin m) K := fiber (fun j => q.eval j) (const φ₀)
  have h1 : ‖∑ j, (parity j : ℂ) * ⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ‖ ≤
      μ ^ n * ‖M‖ * ‖tensorPow w Ψ‖ ^ 2 := correlation_le w hwH hw M Ψ
  have h2 : ‖tensorPow w Ψ‖ ≤ lam ^ q.count * ‖tensorPow w (const φ₀)‖ :=
    norm_tensorPow_program P w hw hlam hD q (const φ₀)
  have h3 := norm_tensorPow_const_sq (n := n) w hfix φ₀
  have hφ2 : ‖φ₀‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hφ₀
  have h4 : ‖tensorPow w Ψ‖ ^ 2 ≤ lam ^ (2 * q.count) * (m : ℝ) ^ n := by
    calc ‖tensorPow w Ψ‖ ^ 2 ≤ (lam ^ q.count * ‖tensorPow w (const φ₀)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = lam ^ (2 * q.count) * ‖(tensorPow w (const φ₀) : Joint (Fin n → Fin m) K)‖ ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm q.count 2]
      _ = lam ^ (2 * q.count) * ((m : ℝ) ^ n * ‖φ₀‖ ^ 2) := by rw [h3]
      _ ≤ lam ^ (2 * q.count) * ((m : ℝ) ^ n * 1) := by
          gcongr
      _ = lam ^ (2 * q.count) * (m : ℝ) ^ n := by ring
  have h5 : ‖∑ j, (parity j : ℂ) * ⟪q.eval j φ₀, M (q.eval j φ₀)⟫_ℂ‖ ≤
      μ ^ n * lam ^ (2 * q.count) * (m : ℝ) ^ n := by
    calc _ ≤ μ ^ n * ‖M‖ * ‖tensorPow w Ψ‖ ^ 2 := h1
      _ ≤ μ ^ n * 1 * (lam ^ (2 * q.count) * (m : ℝ) ^ n) := by
          gcongr
      _ = μ ^ n * lam ^ (2 * q.count) * (m : ℝ) ^ n := by ring
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hR0 : 0 ≤ μ ^ n * lam ^ (2 * q.count) := mul_nonneg (pow_nonneg hμ0 _) (pow_nonneg hlam0 _)
  rcases eq_or_lt_of_le (pow_nonneg (Nat.cast_nonneg m : (0 : ℝ) ≤ m) n) with hm | hm
  · rw [← hm, inv_zero, zero_mul]
    exact hR0
  · rw [inv_mul_le_iff₀ hm]
    calc _ ≤ μ ^ n * lam ^ (2 * q.count) * (m : ℝ) ^ n := h5
      _ = (m : ℝ) ^ n * (μ ^ n * lam ^ (2 * q.count)) := by ring

end

end SparseLowerBounds.Adversary
end
