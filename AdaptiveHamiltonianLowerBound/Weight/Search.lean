import AdaptiveHamiltonianLowerBound.Weight.Kernel
import SparseLowerBounds.Query.SearchWeight

set_option autoImplicit false

/-!
# The search weight on adaptive protocols

The weight of Lemma `hsl:lem:search` is
`w = P_u + a² P_v + a R` on one hidden register `ℂ^m` (`m` even, `a ≥ 1`;
`SparseLowerBounds.SearchWeight.w`). This file supplies the two one-coordinate facts the
kernel-potential argument of `Weight/Kernel.lean` needs, for oracle calls that depend on one
bit `[j c = q₀]` of the hidden input:

* `norm_conj_reflect_sub_le`: `‖w D_b w⁻¹ - D_b‖ ≤ 4√2 a/√m + 4a²/m` for the reflection
  `D_b = 1 - 2|b⟩⟨b|` (from `w D_b w⁻¹ = D_b - 2(e⟨b| + |b⟩f† + e f†)`, proof of Lemma
  `hsl:lem:search`, and `‖e‖, ‖f‖ ≤ √2 a/√m`, proof of Lemma `hsl:lem:search`).
* `norm_act_w_joint_bitOp`: a call acting as `V₁` on the marked position and as `V₀` elsewhere
  (`V₀`, `V₁` norm-preserving) satisfies `‖w Ô η‖ ≤ λ ‖w η‖` with `λ = 1 + 4√2 a/√m + 4a²/m`
  (`searchLam m a`), the display bound of the proof of Lemma `hsl:lem:search`. The call is
  `Ô = A ⊗ 1 + B ⊗ D_b` with `A = (V₀ + V₁)/2`, `B = (V₀ - V₁)/2`, so
  `w Ô w⁻¹ = Ô + B ⊗ (w D_b w⁻¹ - D_b)` and `‖B‖ ≤ 1`.
* `wgrowth_bit`: on all hidden registers the weight `w^{⊗ι}` grows by at most `λ²` under
  such a call (one call costs one growth factor).
* `search_tree_xor`: for every adaptive protocol whose labels have growth `λ^{2 w l}` in both
  directions, `|Σ_j σ_j Re tr(M ρ_j)| ≤ a^{-2n} λ^{2 worstCost} m^n` (`‖w⁻¹ Z w⁻¹‖ ≤ a⁻²`,
  proof of Lemma `hsl:lem:search`).

The numerical forms: `λ ≤ 1 + 12a/√m` for `a ≤ √m` (`searchLam_le_twelve`, proof of Lemma
`hsl:lem:search`) and `λ ≤ 7a²` for `m = 2` (`searchLam_two_le`), used for the precision family.
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder
open scoped Matrix.Norms.L2Operator
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open LinearSystemLowerBound

variable {m : ℕ}

/-- The per-call growth of the search weight, `λ = 1 + 4√2 a/√m + 4a²/m` (proof of Lemma
`hsl:lem:search`). -/
def searchLam (m : ℕ) (a : ℝ) : ℝ := 1 + 4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m

theorem one_le_searchLam (m : ℕ) {a : ℝ} (ha : 0 ≤ a) : 1 ≤ searchLam m a := by
  have h1 : 0 ≤ 4 * Real.sqrt 2 * a / Real.sqrt m := by positivity
  have h2 : 0 ≤ 4 * a ^ 2 / m := by positivity
  unfold searchLam
  linarith

/-- `λ ≤ 1 + 12 a/√m` for `0 ≤ a ≤ √m` (proof of Lemma `hsl:lem:search`). -/
theorem searchLam_le_twelve {a : ℝ} (ha : 0 ≤ a) (ham : a ≤ Real.sqrt m) :
    searchLam m a ≤ 1 + 12 * a / Real.sqrt m :=
  SparseLowerBounds.SearchWeight.fine_le_twelve ha ham

/-- For one hidden bit (`m = 2`), `λ = 1 + 4a + 2a² ≤ 7a²` for `a ≥ 1`. -/
theorem searchLam_two_le {a : ℝ} (ha : 1 ≤ a) : searchLam 2 a ≤ 7 * a ^ 2 := by
  have hs : Real.sqrt ((2 : ℕ) : ℝ) = Real.sqrt 2 := by norm_num
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have e : searchLam 2 a = 1 + 4 * a + 2 * a ^ 2 := by
    unfold searchLam
    rw [hs]
    field_simp
    push_cast
    ring
  rw [e]
  nlinarith

/-- The position parity of the linear-system library is the parity `Z` of the search
weight. -/
theorem parityMat_eq_parityZ (m : ℕ) :
    parityMat m = SparseLowerBounds.Adversary.parityZ m := by
  ext i j
  simp only [parityMat, SparseLowerBounds.Adversary.parityZ, Matrix.diagonal_apply, sgn]
  split_ifs <;> push_cast <;> rfl

/-! ### The conjugated reflection -/

/-- **The query block, difference form**: `‖w D_b w⁻¹ - D_b‖ ≤ 4√2 a/√m + 4a²/m`. -/
theorem norm_conj_reflect_sub_le (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (b : Fin m) :
    ‖SparseLowerBounds.SearchWeight.w m a * SparseLowerBounds.Adversary.reflect b *
        (SparseLowerBounds.SearchWeight.w m a)⁻¹ - SparseLowerBounds.Adversary.reflect b‖ ≤
      4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m := by
  have ha0 : 0 < a := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast Fin.pos b
  rw [SparseLowerBounds.SearchWeight.conj_D_eq hm ha0.ne' b, sub_sub_cancel_left, norm_neg]
  set e := SparseLowerBounds.SearchWeight.eVec m a b
  set f := SparseLowerBounds.SearchWeight.fVec m a b
  have he := SparseLowerBounds.SearchWeight.norm_e_le hm ha b
  have hfs : ‖(WithLp.toLp 2 (star f) : EuclideanSpace ℂ (Fin m))‖ ≤
      Real.sqrt 2 * a / Real.sqrt m := by
    rw [SparseLowerBounds.SearchWeight.norm_toLp_star]
    exact SparseLowerBounds.SearchWeight.norm_f_le hm ha b
  have h1 := SparseLowerBounds.Helpers.SearchWeight.norm_toLp_single b
  set c := Real.sqrt 2 * a / Real.sqrt m with hc
  have hc0 : 0 ≤ c := by positivity
  have hA : ‖Matrix.vecMulVec e (Pi.single b (1 : ℂ) : Fin m → ℂ)‖ ≤ c :=
    (SparseLowerBounds.SearchWeight.norm_vecMulVec_le _ _).trans (by rw [h1, mul_one]; exact he)
  have hB : ‖Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star f)‖ ≤ c :=
    (SparseLowerBounds.SearchWeight.norm_vecMulVec_le _ _).trans (by rw [h1, one_mul]; exact hfs)
  have hC : ‖Matrix.vecMulVec e (star f)‖ ≤ c * c :=
    (SparseLowerBounds.SearchWeight.norm_vecMulVec_le _ _).trans
      (mul_le_mul he hfs (norm_nonneg _) hc0)
  have hcc : c * c = 2 * a ^ 2 / m := by
    rw [hc, ← sq, div_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hm0.le]
  have hsum := norm_add₃_le (a := Matrix.vecMulVec e (Pi.single b (1 : ℂ) : Fin m → ℂ))
    (b := Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star f))
    (c := Matrix.vecMulVec e (star f))
  calc _ ≤ ‖(2 : ℂ)‖ * ‖Matrix.vecMulVec e (Pi.single b (1 : ℂ) : Fin m → ℂ) +
        Matrix.vecMulVec (Pi.single b (1 : ℂ) : Fin m → ℂ) (star f) +
        Matrix.vecMulVec e (star f)‖ := norm_smul_le _ _
    _ ≤ 2 * (c + c + c * c) := by
        rw [Complex.norm_ofNat]
        gcongr
        linarith
    _ = 4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m := by
        rw [mul_add, hcc, hc]
        ring

/-! ### One hidden register -/

section One

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem joint_add_fam {X : Type*} (O : X → V →L[ℂ] V) (ψ φ : Fam X V) :
    joint O (ψ + φ) = joint O ψ + joint O φ := by
  ext j
  simp

theorem act_reflect_apply (q₀ : Fin m) (φ : Fam (Fin m) V) (q : Fin m) :
    act (SparseLowerBounds.Adversary.reflect q₀) φ q =
      (if q = q₀ then (-1 : ℂ) else 1) • φ q := by
  simp only [act_apply, SparseLowerBounds.Adversary.reflect, Matrix.diagonal_apply, ite_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **A single-bit call in reflection form**: `Ô = A ⊗ 1 + B ⊗ D_{q₀}` with
`A = (V₀ + V₁)/2` and `B = (V₀ - V₁)/2`. -/
theorem joint_bitOp_eq (q₀ : Fin m) (V₀ V₁ : V →L[ℂ] V) (φ : Fam (Fin m) V) :
    joint (bitOp q₀ V₀ V₁) φ = joint (fun _ => (1 / 2 : ℂ) • (V₀ + V₁)) φ +
      joint (fun _ => (1 / 2 : ℂ) • (V₀ - V₁))
        (act (SparseLowerBounds.Adversary.reflect q₀) φ) := by
  ext q
  rw [PiLp.add_apply, joint_apply, joint_apply, joint_apply, act_reflect_apply]
  by_cases hq : q = q₀
  · simp only [bitOp, hq, if_true, smul_apply, add_apply, sub_apply, neg_smul, one_smul,
      map_neg]
    module
  · simp only [bitOp, hq, if_false, smul_apply, add_apply, sub_apply, one_smul]
    module

theorem norm_half_sub_le (V₀ V₁ : V →L[ℂ] V) (h₀ : ∀ v, ‖V₀ v‖ = ‖v‖)
    (h₁ : ∀ v, ‖V₁ v‖ = ‖v‖) (v : V) : ‖((1 / 2 : ℂ) • (V₀ - V₁)) v‖ ≤ ‖v‖ := by
  rw [smul_apply, norm_smul, sub_apply]
  have h := norm_sub_le (V₀ v) (V₁ v)
  rw [h₀, h₁] at h
  have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h2]
  linarith

/-- **One-coordinate weight growth of a single-bit call** (proof of Lemma `hsl:lem:search`):
`‖w Ô η‖ ≤ (1 + 4√2 a/√m + 4a²/m) ‖w η‖`. -/
theorem norm_act_w_joint_bitOp (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (q₀ : Fin m)
    (V₀ V₁ : V →L[ℂ] V) (h₀ : ∀ v, ‖V₀ v‖ = ‖v‖) (h₁ : ∀ v, ‖V₁ v‖ = ‖v‖)
    (η : Fam (Fin m) V) :
    ‖act (SparseLowerBounds.SearchWeight.w m a) (joint (bitOp q₀ V₀ V₁) η)‖ ≤
      searchLam m a * ‖act (SparseLowerBounds.SearchWeight.w m a) η‖ := by
  have ha0 : a ≠ 0 := by positivity
  set W := SparseLowerBounds.SearchWeight.w m a with hW
  set D := SparseLowerBounds.Adversary.reflect q₀ with hD
  set B : V →L[ℂ] V := (1 / 2 : ℂ) • (V₀ - V₁) with hB
  set ξ := act W η with hξ
  have hinv : W⁻¹ * W = 1 := by
    rw [hW, SparseLowerBounds.SearchWeight.inv_w hm ha0]
    exact SparseLowerBounds.SearchWeight.wInv_mul_w hm ha0
  have hη : η = act W⁻¹ ξ := by rw [hξ, ← act_mul, hinv, act_one]
  have hconj : act (W * D * W⁻¹) ξ = act W (act D η) := by
    rw [act_mul, act_mul, ← hη]
  have hWD : act W (act D η) = act D ξ + act (W * D * W⁻¹ - D) ξ := by
    rw [act_sub_matrix, hconj]
    abel
  have key : act W (joint (bitOp q₀ V₀ V₁) η) =
      joint (bitOp q₀ V₀ V₁) ξ + joint (fun _ => B) (act (W * D * W⁻¹ - D) ξ) := by
    rw [joint_bitOp_eq, act_add, act_joint_const, act_joint_const, ← hξ, hWD,
      joint_add_fam, joint_bitOp_eq q₀ V₀ V₁ ξ]
    abel
  have hO : ∀ (q : Fin m) v, ‖bitOp q₀ V₀ V₁ q v‖ = ‖v‖ := by
    intro q v
    by_cases h : q = q₀
    · simp only [bitOp, h, if_true, h₁]
    · simp only [bitOp, h, if_false, h₀]
  have hBn : ∀ χ : Fam (Fin m) V, ‖joint (fun _ => B) χ‖ ≤ ‖χ‖ := by
    intro χ
    have h2 : ‖joint (fun _ => B) χ‖ ^ 2 ≤ ‖χ‖ ^ 2 := by
      rw [norm_sq_fam, norm_sq_fam]
      exact Finset.sum_le_sum fun q _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_half_sub_le V₀ V₁ h₀ h₁ (χ q)) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have hdiff := norm_conj_reflect_sub_le hm ha q₀
  rw [key]
  calc ‖joint (bitOp q₀ V₀ V₁) ξ + joint (fun _ => B) (act (W * D * W⁻¹ - D) ξ)‖
      ≤ ‖joint (bitOp q₀ V₀ V₁) ξ‖ + ‖joint (fun _ => B) (act (W * D * W⁻¹ - D) ξ)‖ :=
        norm_add_le _ _
    _ ≤ ‖ξ‖ + ‖W * D * W⁻¹ - D‖ * ‖ξ‖ := by
        rw [norm_joint _ hO]
        exact add_le_add le_rfl ((hBn _).trans (norm_act_le _ _))
    _ ≤ ‖ξ‖ + (4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m) * ‖ξ‖ :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
    _ = searchLam m a * ‖ξ‖ := by
        unfold searchLam
        ring

end One

/-! ### All hidden registers -/

section Growth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Single-bit calls** have growth `λ²` for the search weight `w^{⊗ι}`. -/
theorem wgrowth_bit (hm : Even m) {a : ℝ} (ha : 1 ≤ a) (c : ι) (q₀ : Fin m)
    (V₀ V₁ : K →L[ℂ] K) (h₀ : ∀ v, ‖V₀ v‖ = ‖v‖) (h₁ : ∀ v, ‖V₁ v‖ = ‖v‖) :
    WGrowth (SparseLowerBounds.SearchWeight.w m a)
      (fun j : ι → Fin m => if j c = q₀ then V₁ else V₀) (searchLam m a ^ 2) := by
  intro ψ
  set W := SparseLowerBounds.SearchWeight.w m a
  set O : (ι → Fin m) → K →L[ℂ] K := fun j => if j c = q₀ then V₁ else V₀
  rw [kron_eq_splitMat c, norm_sq_act_splitMat, norm_sq_act_splitMat, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  have hfib : ∀ q', act (kron W) (fiber c (joint O ψ) q') =
      joint (fun _ => bitOp q₀ V₀ V₁ q') (act (kron W) (fiber c ψ q')) := by
    intro q'
    have h : fiber c (joint O ψ) q' = joint (fun _ => bitOp q₀ V₀ V₁ q') (fiber c ψ q') := by
      ext r'
      simp only [fiber_apply, joint_apply, O, splitEquiv_self, bitOp]
    rw [h, act_joint_const]
  have hin : (WithLp.toLp 2 (fun q' => act (kron W) (fiber c (joint O ψ) q') r) :
      Fam (Fin m) K) =
      joint (bitOp q₀ V₀ V₁)
        (WithLp.toLp 2 (fun q' => act (kron W) (fiber c ψ q') r)) := by
    ext q'
    simp only [joint_apply]
    rw [hfib]
    rfl
  rw [hin]
  have h := norm_act_w_joint_bitOp hm ha q₀ V₀ V₁ h₀ h₁
    (WithLp.toLp 2 (fun q' => act (kron W) (fiber c ψ q') r) : Fam (Fin m) K)
  calc _ ≤ (searchLam m a * ‖act W
        (WithLp.toLp 2 (fun q' => act (kron W) (fiber c ψ q') r) :
          Fam (Fin m) K)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by ring

end Growth

/-! ### Adaptive protocols -/

section Trees

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {K F E L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  {O : L → (ι → Fin m) → K →L[ℂ] K}

/-- **Parity bound for adaptive protocols, search weight** (proof of Lemma `hsl:lem:search` for
adaptive protocols): if every label has growth `(λ²)^{w l}` in both directions, then
`|Σ_j σ_j Re tr(M ρ_j)| ≤ a^{-2|ι|} (λ²)^{worstCost} m^{|ι|}` for the heralded outputs `ρ_j` and a
contraction `M`. -/
theorem search_tree_xor (hm : Even m) {a : ℝ} (ha : 1 ≤ a)
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j)) (w : L → ℕ)
    (hO : ∀ l, WGrowth (SparseLowerBounds.SearchWeight.w m a) (O l) ((searchLam m a ^ 2) ^ w l))
    (hO' : ∀ l, WGrowth (SparseLowerBounds.SearchWeight.w m a) (fun j => star (O l j))
      ((searchLam m a ^ 2) ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (T : Tree O F E) :
    |∑ j, parSign j * corr M (T.successDensity j)| ≤
      ((a ^ 2)⁻¹) ^ Fintype.card ι * (searchLam m a ^ 2) ^ T.worstCost w *
        (m : ℝ) ^ Fintype.card ι := by
  have ha0 : a ≠ 0 := by positivity
  have hμ : ‖(SparseLowerBounds.SearchWeight.w m a)⁻¹ * parityMat m *
      (SparseLowerBounds.SearchWeight.w m a)⁻¹‖ ≤ (a ^ 2)⁻¹ := by
    rw [parityMat_eq_parityZ]
    exact SparseLowerBounds.SearchWeight.norm_conj_Z_le hm (by positivity)
  have hC : 1 ≤ searchLam m a ^ 2 := one_le_pow₀ (one_le_searchLam m (by positivity))
  exact wtree_xor _ (SparseLowerBounds.SearchWeight.isHermitian_w m a)
    (SparseLowerBounds.SearchWeight.isUnit_w hm ha0)
    (SparseLowerBounds.SearchWeight.w_mulVec_one hm a) (by positivity) hμ hU w _ hC hO hO'
    M hM T

end Trees

end

end AdaptiveHamiltonianLowerBound
