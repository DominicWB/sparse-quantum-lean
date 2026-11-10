import DysonFullClass.Target
import DysonFullClass.Perturb

set_option autoImplicit false

/-!
# Acceptance checks for the full-class Dyson comparison

The acceptance checks of the comparison on the full class. Each check is a theorem about the
declarations used by `Theorem.full_dyson_shape` (not about a separate model):

1. **True `A = 0`, represented `C = a I`** (Lean sign: generator `G = -A = 0`, represented
   `C = -a·1`): `growC_not_accretive` (the represented generator is not accretive, so the older
   `Dyson.Valid` premise fails), `zero_true_cell` (the perturbation lemma `Perturb.cell_perturb`
   still applies and gives `‖w - e^{ha} w‖ ≤ ‖w‖ (e^{ha ‖1‖} - 1)`), `exp_growC` and
   `zero_true_sharp` (the represented evolution is `e^{ha}·1`, of norm `e^{ha} > 1`, and the bound
   is attained), `const_error_eq` (on **every** mesh of `[0, T]` the integrated distance is
   `‖C‖ T = a T`: subdividing further cannot certify a smaller `E`; `a` must be chosen with
   `a T ≤ log(1 + δ_m)`).
2. **Node and phase assembly**: the mesh `exMesh` of `[0, 3]` with unequal cells `[0, 1]`,
   `[1, 3]`; `exMesh_widths` (a node `1/2` strictly inside cell `0` uses the partial first cell
   `1/2` and then `2`; the initial node uses `1`, `2`); `meshWidth_end`, `truncated_of_zero`,
   `nodeSeries_end` (a node at `T` has all durations zero and its block is exactly `I`);
   `exPhases` (phases of the negative and non-real coefficients `-1`, `i`; phase one on label `0`
   and on a zero-weight label); `exMass` (zero mass on the unused label, positive total mass);
   `exAssembly` (the assembled vector `y_K` itself, not its norm:
   `y_K = S(0) x₀ - S(1/2) b₁ + i b₂` with `S(u) = nodeSeries`); `cfgProduct_cfg11`,
   `meshNodeProduct_two` (later cells act to the left, for the series and for the product),
   `eLower_eRaise_ne` (a noncommuting pair, for which reversing the product changes it).
3. **The older left-endpoint selection**: `meshWidth_left` (a source at the left endpoint `t_r`
   of cell `r` is propagated through exactly the cells `j ≥ r` over their full length, the older
   source-start mask) and `meshWidth_zero_start`; `left_endpoint_mass` (with weights
   `ω_r = t_{r+1} - t_r` the source mass is the older `MeshSampling.mass r₀ t rb`).
4. **The value word and the factor `N_D`**: `clipData_decode` (the rotation decodes
   `p_η(dec w)` of the same queried word; `Clip.oracles_clipData`: the same row, column and value
   calls), `radialClip_zero` (zero words stay zero, so lists and padding stay valid);
   `numerator_charge` (an additive error `η_p` of the selected vector `y_K/(N_D B_q)` is
   `N_D B_q η_p` on the numerator scale).
-/

namespace DysonFullClass.Examples

noncomputable section
open SparseHamiltonian ContinuousLinearMap Set MeasureTheory NativeSparseBlockEncoding
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshWidth meshNodeProduct)
open SparseHamiltonian.GeneralSourceODE (sources phases startTime)
open ODELowerBoundExtensions.Dyson
open scoped BigOperators InnerProduct Nat

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### 1. True `A = 0`, represented `C = a I` -/

/-- The represented generator of the example in the Lean sign: `C = -a·1` (true `G = -A = 0`). -/
def growC (a : ℝ) : V →L[ℂ] V := -((a : ℂ) • (1 : V →L[ℂ] V))

omit [CompleteSpace V] in
/-- The true generator `0` is accretive. -/
theorem zero_accretive : Accretive (0 : V →L[ℂ] V) := fun v => by simp

omit [CompleteSpace V] in
/-- **The represented generator is not accretive** for `a > 0` on a nonzero space. -/
theorem growC_not_accretive [Nontrivial V] {a : ℝ} (ha : 0 < a) :
    ¬ Accretive (growC (V := V) a) := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 := h v
  have hv' : growC (V := V) a v = -((a : ℂ) • v) := rfl
  have h2 : (inner ℂ v (growC (V := V) a v)).re = -(a * ‖v‖ ^ 2) := by
    rw [hv', inner_neg_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have h3 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h4 : 0 < a * ‖v‖ ^ 2 := by positivity
  linarith

omit [CompleteSpace V] in
/-- `‖C‖ = a` on a nonzero space. -/
theorem norm_growC [Nontrivial V] {a : ℝ} (ha : 0 ≤ a) : ‖growC (V := V) a‖ = a := by
  rw [growC, norm_neg, norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ha]

/-- **The perturbation lemma applies to the non-contractive represented evolution**: for the
true generator `0` (constant solutions) and `C = -a·1`, `‖e^{-hC}‖ ≤ e^{h‖C‖}` and
`‖w - e^{-hC} w‖ ≤ ‖w‖ (e^{h ‖C‖} - 1)`. -/
theorem zero_true_cell (a h : ℝ) (hh : 0 ≤ h) (w : V) :
    ‖NormedSpace.exp (h • (-growC (V := V) a))‖ ≤ Real.exp (h * ‖growC (V := V) a‖) ∧
      ‖w - NormedSpace.exp (h • (-growC (V := V) a)) w‖ ≤
        ‖w‖ * (Real.exp (h * ‖growC (V := V) a‖) - 1) := by
  have hy : SolvesODE (fun _ => (0 : V →L[ℂ] V)) 0 (fun _ => w) 0 h := by
    intro u _
    convert hasDerivWithinAt_const u (Icc (0 : ℝ) h) w using 1
    simp
  have hG : ∀ u ∈ Icc (0 : ℝ) h, Accretive ((fun _ => (0 : V →L[ℂ] V)) u) :=
    fun _ _ => zero_accretive
  have := cell_perturb hy hh hG intervalIntegrable_const (growC a)
  simpa only [zero_sub, norm_neg, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    using this

omit [CompleteSpace V] in
/-- `e^{c·1} = e^c · 1`. -/
theorem exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : V →L[ℂ] V)) = NormedSpace.exp c • (1 : V →L[ℂ] V) := by
  rw [← Algebra.algebraMap_eq_smul_one, ← NormedSpace.algebraMap_exp_comm,
    Algebra.algebraMap_eq_smul_one]

omit [CompleteSpace V] in
/-- **The represented evolution of the example**: `e^{-hC} = e^{ha}·1`. -/
theorem exp_growC (a h : ℝ) :
    NormedSpace.exp (h • (-growC (V := V) a)) = (Real.exp (h * a) : ℂ) • (1 : V →L[ℂ] V) := by
  have e : h • (-growC (V := V) a) = ((h * a : ℝ) : ℂ) • (1 : V →L[ℂ] V) := by
    rw [growC, neg_neg, RCLike.real_smul_eq_coe_smul (K := ℂ) h, smul_smul,
      Complex.ofReal_mul]
    rfl
  rw [e, exp_smul_one, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp]

omit [CompleteSpace V] in
/-- **The bound is attained**: `‖w - e^{-hC} w‖ = ‖w‖ (e^{ha} - 1)`, and `‖e^{-hC}‖ = e^{ha} > 1`
for `h a > 0` on a nonzero space. -/
theorem zero_true_sharp [Nontrivial V] (a h : ℝ) (hah : 0 < h * a) (w : V) :
    ‖w - NormedSpace.exp (h • (-growC (V := V) a)) w‖ = ‖w‖ * (Real.exp (h * a) - 1) ∧
      1 < ‖NormedSpace.exp (h • (-growC (V := V) a))‖ := by
  rw [exp_growC]
  have he : 1 < Real.exp (h * a) := by
    have := Real.add_one_lt_exp (ne_of_gt hah)
    linarith
  refine ⟨?_, ?_⟩
  · have hv : (((Real.exp (h * a) : ℝ) : ℂ) • (1 : V →L[ℂ] V)) w =
        ((Real.exp (h * a) : ℝ) : ℂ) • w := rfl
    rw [hv]
    have : w - ((Real.exp (h * a) : ℝ) : ℂ) • w = ((1 - Real.exp (h * a) : ℝ) : ℂ) • w := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [this, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  · rw [norm_smul, norm_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact he

omit [CompleteSpace V] in
/-- **A constant represented error is not removed by subdivision**: on every mesh of `[0, T]`,
`∑_r ∫_{cell r} ‖0 - C‖ = ‖C‖ T`. -/
theorem const_error_eq {t : ℕ → ℝ} {M : ℕ} {T : ℝ} (hmesh : IsMesh t M T) (C : V →L[ℂ] V) :
    ∑ r : Fin M, ∫ _u in t r..t ((r : ℕ) + 1), ‖(0 : V →L[ℂ] V) - C‖ = ‖C‖ * T := by
  simp only [zero_sub, norm_neg, intervalIntegral.integral_const, smul_eq_mul]
  rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun r => t (r + 1) - t r) M,
    Finset.sum_range_sub (fun r => t r) M, hmesh.last, hmesh.zero]
  ring

/-! ### 2. Node and phase assembly -/

/-- A mesh of `[0, 3]` with the unequal cells `[0, 1]` and `[1, 3]`. -/
def exMesh : ℕ → ℝ := fun k => if k = 0 then 0 else if k = 1 then 1 else 3

theorem exMesh_isMesh : IsMesh exMesh 2 3 := by
  refine ⟨by simp [exMesh], by simp [exMesh], ?_⟩
  intro i j hij
  simp only [exMesh]
  split_ifs <;> first | (exfalso; omega) | norm_num

/-- **Durations of the example**: the node `1/2` strictly inside cell `0` uses `1/2` of cell `0`
and all of cell `1`; the initial node uses `1` and `2` (unequal cells). -/
theorem exMesh_widths :
    meshWidth (1 / 2) exMesh 0 = 1 / 2 ∧ meshWidth (1 / 2) exMesh 1 = 2 ∧
      meshWidth 0 exMesh 0 = 1 ∧ meshWidth 0 exMesh 1 = 2 := by
  simp only [meshWidth, exMesh]
  norm_num

/-- A node at the end of the mesh has all durations zero. -/
theorem meshWidth_end {t : ℕ → ℝ} {M : ℕ} {T : ℝ} (hmesh : IsMesh t M T) {r : ℕ} (hr : r < M) :
    meshWidth T t r = 0 := by
  have h1 : t (r + 1) ≤ T := hmesh.last ▸ hmesh.mono (by omega)
  have h2 : t r ≤ T := hmesh.last ▸ hmesh.mono (by omega)
  simp only [meshWidth, max_eq_left h1, max_eq_left h2, sub_self]

omit [CompleteSpace V] in
/-- The ordered product of identities is the identity. -/
theorem evolution_ones (M : ℕ) : TimeDependent.evolution (fun _ => (1 : V →L[ℂ] V)) M = 1 := by
  induction M with
  | zero => rfl
  | succ M ih => rw [TimeDependent.evolution_succ, ih, one_mul]

omit [CompleteSpace V] in
/-- **The degree-zero block is `I`, all higher degrees vanish at zero duration.** -/
theorem truncated_of_zero {K M : ℕ} {a : ℕ → ℝ} (ha : ∀ r < M, a r = 0) (X : ℕ → V →L[ℂ] V) :
    truncated a X K M = 1 := by
  unfold truncated
  rw [Finset.sum_eq_single (Cfg.zero : Cfg K M)]
  · have hc : coef a (Cfg.zero : Cfg K M) = 1 := by
      simp [coef, Cfg.zero]
    have hp : cfgProduct X (Cfg.zero : Cfg K M) = 1 := by
      unfold cfgProduct
      have hcount : ∀ r, (Cfg.zero : Cfg K M).count r = 0 := fun r => by
        simp [Cfg.count, Cfg.zero]
      simp only [hcount, pow_zero]
      exact evolution_ones M
    rw [hc, hp, one_smul]
  · intro c _ hc
    have hne : ∃ r : Fin M, (c.1 r : ℕ) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hc
      apply Subtype.ext
      funext r
      exact Fin.ext (hall r)
    obtain ⟨r, hr⟩ := hne
    have h0 : coef a c = 0 := by
      unfold coef
      apply Finset.prod_eq_zero (Finset.mem_univ r)
      rw [ha r r.isLt, zero_pow hr, zero_div]
    rw [h0, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CompleteSpace V] in
/-- **The block of a node at `T` is exactly `I`**, at every degree. -/
theorem nodeSeries_end {t : ℕ → ℝ} {M : ℕ} {T : ℝ} (hmesh : IsMesh t M T) (Cs : ℕ → V →L[ℂ] V)
    (K : ℕ) : nodeSeries Cs t K M T = 1 :=
  truncated_of_zero (fun _ hr => meshWidth_end hmesh hr) _

/-- The coefficients of the example: a negative one, a non-real one and a zero one. -/
def exOmega : Fin 3 → ℂ := ![-1, Complex.I, 0]

/-- The nodes of the example: strictly inside cell `0`, at `T = 3`, and an unused one. -/
def exNodes : Fin 3 → ℝ := ![1 / 2, 3, 0]

/-- **Phases of the example**: phase one on label `0`, `-1` and `i` on the negative and
non-real coefficients, phase one on the zero-weight label. -/
theorem exPhases :
    phases exOmega none = 1 ∧ phases exOmega (some 0) = -1 ∧
      phases exOmega (some 1) = Complex.I ∧ phases exOmega (some 2) = 1 := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp [phases, exOmega]
  · simp [phases, exOmega, Complex.norm_I]
  · simp [phases, exOmega]

omit [CompleteSpace V] in
/-- **Masses of the example**: the zero-weight label carries zero mass and the total mass is
`‖x₀‖ + ‖b₁‖ + ‖b₂‖`, positive once `x₀ ≠ 0`. -/
theorem exMass (x₀ : V) (bv : Fin 3 → V) :
    sources x₀ bv exOmega (some 2) = 0 ∧
      ODESourceBranches.mass (sources x₀ bv exOmega) = ‖x₀‖ + ‖bv 0‖ + ‖bv 1‖ ∧
      (x₀ ≠ 0 → 0 < ODESourceBranches.mass (sources x₀ bv exOmega)) := by
  have hm : ODESourceBranches.mass (sources x₀ bv exOmega) = ‖x₀‖ + ‖bv 0‖ + ‖bv 1‖ := by
    simp [ODESourceBranches.mass, Fintype.sum_option, Fin.sum_univ_three, sources, exOmega,
      norm_smul, Complex.norm_I]
    ring
  refine ⟨by simp [sources, exOmega], hm, fun h => ?_⟩
  rw [hm]
  have := norm_pos_iff.mpr h
  positivity

omit [CompleteSpace V] in
/-- **The assembled vector of the example** (the selected numerator `y_K`, not its norm): with
`S(u) = nodeSeries C exMesh K 2 u`, `y_K = S(0) x₀ - S(1/2) b₁ + i b₂` (the node at `T` loads
`i b₂` with identity propagation; the zero-weight label contributes nothing). -/
theorem exAssembly (Cs : ℕ → V →L[ℂ] V) (K : ℕ) (x₀ : V) (bv : Fin 3 → V) :
    ∑ a : Option (Fin 3), nodeSeries Cs exMesh K 2 (startTime exNodes a)
        (sources x₀ bv exOmega a) =
      nodeSeries Cs exMesh K 2 0 x₀ - nodeSeries Cs exMesh K 2 (1 / 2) (bv 0) +
        Complex.I • bv 1 := by
  have hT : nodeSeries Cs exMesh K 2 3 = 1 := nodeSeries_end exMesh_isMesh Cs K
  have h1 : ∀ w : V, (1 : V →L[ℂ] V) w = w := fun w => rfl
  simp only [Fintype.sum_option, Fin.sum_univ_three, startTime, sources, exNodes, exOmega,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, hT, h1, zero_smul, map_zero, add_zero, neg_smul, one_smul, map_neg]
  abel

/-- The configuration with one factor from each of two cells. -/
def cfg11 : Cfg 2 2 := ⟨fun _ => 1, by decide⟩

omit [CompleteSpace V] in
/-- **Later cells act to the left in the series**: the degree-two term with one factor from each
cell is `X₁ X₀`. -/
theorem cfgProduct_cfg11 (X : ℕ → V →L[ℂ] V) : cfgProduct X cfg11 = X 1 * X 0 := by
  have h0 : cfg11.count 0 = 1 := rfl
  have h1 : cfg11.count 1 = 1 := rfl
  rw [cfgProduct, TimeDependent.evolution_succ, TimeDependent.evolution_succ,
    TimeDependent.evolution_zero, h0, h1, pow_one, pow_one, mul_one]

omit [CompleteSpace V] in
/-- **Later cells act to the left in the product**: on two cells
`meshNodeProduct C t 2 u = e^{-w₁(u) C₁} e^{-w₀(u) C₀}`. -/
theorem meshNodeProduct_two (Cs : ℕ → V →L[ℂ] V) (t : ℕ → ℝ) (u : ℝ) :
    meshNodeProduct Cs t 2 u =
      NormedSpace.exp (meshWidth u t 1 • (-Cs 1)) * NormedSpace.exp (meshWidth u t 0 • (-Cs 0)) := by
  rw [meshNodeProduct, TimeDependent.evolution_succ, TimeDependent.evolution_succ,
    TimeDependent.evolution_zero, mul_one]

/-- The raising operator `|0⟩⟨1|` on `ℂ²`. -/
def eRaise : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (innerSL ℂ (EuclideanSpace.single 1 (1 : ℂ))).smulRight (EuclideanSpace.single 0 (1 : ℂ))

/-- The lowering operator `|1⟩⟨0|` on `ℂ²`. -/
def eLower : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (innerSL ℂ (EuclideanSpace.single 0 (1 : ℂ))).smulRight (EuclideanSpace.single 1 (1 : ℂ))

/-- **A noncommuting pair**: `eLower eRaise ≠ eRaise eLower`, so a product with the cells in
reverse order is a different operator. -/
theorem eLower_eRaise_ne : eLower * eRaise ≠ eRaise * eLower := by
  intro h
  have h1 := congrArg (fun F => F (EuclideanSpace.single 1 (1 : ℂ)) 1) h
  simp [eRaise, eLower, EuclideanSpace.inner_single_left] at h1

/-! ### 3. The older left-endpoint selection -/

/-- **The left-endpoint source mask**: a source starting at the left endpoint `t_r` of cell `r`
uses no duration on the earlier cells and the full length of every later cell. -/
theorem meshWidth_left {t : ℕ → ℝ} {M : ℕ} {T : ℝ} (hmesh : IsMesh t M T) (r j : ℕ) :
    meshWidth (t r) t j = if j < r then 0 else t (j + 1) - t j := by
  unfold meshWidth
  split_ifs with h
  · have h1 : t (j + 1) ≤ t r := hmesh.mono (by omega)
    have h2 : t j ≤ t r := hmesh.mono (by omega)
    rw [max_eq_left h1, max_eq_left h2, sub_self]
  · have h1 : t r ≤ t (j + 1) := hmesh.mono (by omega)
    have h2 : t r ≤ t j := hmesh.mono (by omega)
    rw [max_eq_right h1, max_eq_right h2]

/-- The initial node uses the full length of every cell. -/
theorem meshWidth_zero_start {t : ℕ → ℝ} {M : ℕ} {T : ℝ} (hmesh : IsMesh t M T) (j : ℕ) :
    meshWidth 0 t j = t (j + 1) - t j := by
  have h := meshWidth_left hmesh 0 j
  rw [hmesh.zero] at h
  rw [h, if_neg (Nat.not_lt_zero j)]

omit [CompleteSpace V] in
/-- **The older mass convention**: left-endpoint samples `b(t_r)` with the positive weights
`ω_r = t_{r+1} - t_r` have source mass `MeshSampling.mass ‖x₀‖ t ‖b(t_·)‖`. -/
theorem left_endpoint_mass {t : ℕ → ℝ} {M : ℕ} {T : ℝ} (hmesh : IsMesh t M T) (x₀ : V)
    (bv : Fin M → V) :
    ODESourceBranches.mass (sources x₀ bv (fun r => ((t ((r : ℕ) + 1) - t r : ℝ) : ℂ))) =
      MeshSampling.mass ‖x₀‖ t (fun r => ‖bv r‖) := by
  simp only [ODESourceBranches.mass, Fintype.sum_option, sources, MeshSampling.mass, norm_smul,
    Complex.norm_real, Real.norm_eq_abs]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [abs_of_nonneg (sub_nonneg.mpr (hmesh.mono (Nat.le_succ r)))]

/-! ### 4. The value word and the factor `N_D` -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- **The value word through clipping**: the rotation of the clipped data decodes `p_η(dec w)`
from the same queried word `w`. -/
theorem clipData_decode (D : Data X n Z s) (η : ℝ) (hη : 0 < η) (a : n × n) (z : Z) : (clipData D η hη).decode a z = radialClip η (D.decode a z) := rfl

omit [CompleteSpace V] in
/-- **The factor `N_D` on an additive selected-amplitude error**: if the selected vector `a` is
within `η_p` of `y_K/(N_D B_q)`, then `N_D B_q a` is within `N_D B_q η_p` of `y_K`. -/
theorem numerator_charge {N B ηp : ℝ} (hN : 0 < N) (hB : 0 < B) (a y : V)
    (h : ‖a - (((N * B : ℝ) : ℂ))⁻¹ • y‖ ≤ ηp) :
    ‖((N * B : ℝ) : ℂ) • a - y‖ ≤ N * B * ηp := by
  have hNB : 0 < N * B := mul_pos hN hB
  have hc : ((N * B : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNB.ne'
  have e : ((N * B : ℝ) : ℂ) • a - y = ((N * B : ℝ) : ℂ) • (a - (((N * B : ℝ) : ℂ))⁻¹ • y) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hNB]
  exact mul_le_mul_of_nonneg_left h hNB.le

end

end DysonFullClass.Examples
