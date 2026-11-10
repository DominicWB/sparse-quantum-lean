import GateOptimalBinary.ClipIface

/-!
# Edge compressions and the row and column sums of the clipped entries

Tools for the moments of the clipped joint representation (`ClipCore`, `twonorm:eq:joint-moments`,
`twonorm:eq:weights`), with `ρ = η²/μ²`:

* `inner_lift`, `isSelfAdjoint_lift`: the inner products of a lifted edgewise operator are sums
  over the edges;
* `norm_edge_compress_le`: for edgewise operators `G_e` with `0 ≤ Re⟪G_e y, y⟫ ≤ a_e ‖y‖²` and row
  and column sums of `a` at most `W`, the compression by the sparse boundary `J₀` has norm at most
  `W/s` (the weighted edge sums of the query-level proof, `LargeSparsityCore.Native.edge_sum_le`);
* `qop`: a `2 × 2` matrix as an operator on the orientation qubit; `quad_smul_one`,
  `quad_smul_proj`: the quadratic forms of `r I` and of `r Π` for a projection `Π`;
* `cl2_row_le`, `cl2_col_le`: `∑_j |c₂| ≤ βρ`; `cl1_row_le`, `cl1_col_le`: `∑_j |c₁|² ≤ ρ`, for
  rows and columns of Euclidean norm at most `η`.

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary GateOptimalPrecision
open NativeSparseBlockEncoding (Data Query)
open NativeSignedFactor (phase norm_phase)
open LargeSparsityCore.CayleyBlocks (Spectral R1)
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### Lifted edge operators -/

omit [DecidableEq n] in
/-- The inner products of a lifted edgewise operator are sums over the edges. -/
theorem inner_lift (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (w w' : SparseEdgeMoments.OrientedSpace n) :
    inner ℂ (OrientedEdgeCayley.lift G w) w' =
      ∑ e, inner ℂ (G e (OrientedEdgeCayley.regroup w e)) (OrientedEdgeCayley.regroup w' e) := by
  have h := OrientedEdgeCayley.regroup.inner_map_map (OrientedEdgeCayley.lift G w) w'
  rw [← h, OrientedEdgeCayley.regroup_lift, PiLp.inner_apply]
  rfl

omit [DecidableEq n] in
theorem isSelfAdjoint_lift (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (hG : ∀ e, IsSelfAdjoint (G e)) : IsSelfAdjoint (OrientedEdgeCayley.lift G) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro w w'
  change inner ℂ (OrientedEdgeCayley.lift G w) w' = inner ℂ w (OrientedEdgeCayley.lift G w')
  rw [inner_lift, ← inner_conj_symm, inner_lift, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [inner_conj_symm, ← (hG e).adjoint_eq, adjoint_inner_left, (hG e).adjoint_eq]

/-- **The norm of an edge compression by the sparse boundary**: for edgewise operators with
`0 ≤ Re⟪G_e y, y⟫ ≤ a_e ‖y‖²` and row and column sums of `a` at most `W`, the compression by
`J₀ = L J_fixed` has norm at most `W/s`. -/
theorem norm_edge_compress_le {Z : Type*} (D : Data X n Z s) (x : X)
    (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (hGs : ∀ e, IsSelfAdjoint (G e)) (a : n × n → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hG : ∀ e y, 0 ≤ RCLike.re (inner ℂ (G e y) y) ∧
      RCLike.re (inner ℂ (G e y) y) ≤ a e * ‖y‖ ^ 2)
    {W : ℝ} (hW : 0 ≤ W) (hR : ∀ i, ∑ j, a (i, j) ≤ W) (hC : ∀ j, ∑ i, a (i, j) ≤ W) :
    ‖(FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
        ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift G ∘L
          FixedLocatorConjugation.locator D x) ∘L FixedLocatorConjugation.fixedBoundary D.slot‖ ≤
      W / s := by
  have hB := FixedLocatorConjugation.locator_boundary D x
  set B := SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x) with hBdef
  have e : (FixedLocatorConjugation.fixedBoundary D.slot)† ∘L
      ((FixedLocatorConjugation.locator D x)† ∘L OrientedEdgeCayley.lift G ∘L
        FixedLocatorConjugation.locator D x) ∘L FixedLocatorConjugation.fixedBoundary D.slot =
      B† ∘L OrientedEdgeCayley.lift G ∘L B := by
    rw [← hB, adjoint_comp]
    simp only [comp_assoc]
  rw [e]
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hL := isSelfAdjoint_lift G hGs
  refine norm_le_of_re_inner _ ?_ (div_nonneg hW hs.le) ?_
  · change (B† ∘L OrientedEdgeCayley.lift G ∘L B)† = _
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, hL.adjoint_eq, comp_assoc]
  · intro v
    rw [comp_apply, comp_apply, adjoint_inner_left, inner_lift, map_sum]
    have hnn : ∀ e, 0 ≤ RCLike.re (inner ℂ (G e (OrientedEdgeCayley.regroup (B v) e))
        (OrientedEdgeCayley.regroup (B v) e)) := fun e => (hG e _).1
    rw [abs_of_nonneg (Finset.sum_nonneg fun e _ => hnn e)]
    calc ∑ e, RCLike.re (inner ℂ (G e (OrientedEdgeCayley.regroup (B v) e))
          (OrientedEdgeCayley.regroup (B v) e))
        ≤ ∑ e, a e * ‖LargeSparsityCore.Native.yv D x v e‖ ^ 2 :=
          Finset.sum_le_sum fun e _ => (hG e _).2
      _ ≤ W / s * ‖v‖ ^ 2 := LargeSparsityCore.Native.edge_sum_le D x a ha hR hC v

/-! ### Local quadratic forms -/

theorem qop_smul (r : ℂ) (M : Matrix Bool Bool ℂ) : qop (r • M) = r • qop M :=
  map_smul (Matrix.toEuclideanCLM (n := Bool) (𝕜 := ℂ)) r M

theorem qop_one : qop (1 : Matrix Bool Bool ℂ) = 1 :=
  map_one (Matrix.toEuclideanCLM (n := Bool) (𝕜 := ℂ))

theorem qop_mul (M N : Matrix Bool Bool ℂ) : qop (M * N) = qop M * qop N :=
  map_mul (Matrix.toEuclideanCLM (n := Bool) (𝕜 := ℂ)) M N

theorem qop_isSelfAdjoint {M : Matrix Bool Bool ℂ} (hM : Mᴴ = M) : IsSelfAdjoint (qop M) := by
  change star (qop M) = qop M
  rw [qop, ← map_star, Matrix.star_eq_conjTranspose, hM]

/-- A real multiple of the identity. -/
theorem quad_smul_one {r : ℝ} (hr : 0 ≤ r) (y : ExactEdgeCayley.Qubit) :
    0 ≤ RCLike.re (inner ℂ (qop ((r : ℂ) • 1) y) y) ∧
      RCLike.re (inner ℂ (qop ((r : ℂ) • 1) y) y) ≤ r * ‖y‖ ^ 2 := by
  have h : RCLike.re (inner ℂ (qop ((r : ℂ) • 1) y) y) = r * ‖y‖ ^ 2 := by
    rw [qop_smul, qop_one, smul_apply, one_apply_eq_self, inner_smul_left, Complex.conj_ofReal,
      RCLike.re_to_complex, Complex.re_ofReal_mul, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  rw [h]
  exact ⟨by positivity, le_rfl⟩

/-- A real multiple of a projection. -/
theorem quad_smul_proj {r : ℝ} (hr : 0 ≤ r) {P : Matrix Bool Bool ℂ} (hP : Pᴴ = P)
    (hPP : P * P = P) (y : ExactEdgeCayley.Qubit) :
    0 ≤ RCLike.re (inner ℂ (qop ((r : ℂ) • P) y) y) ∧
      RCLike.re (inner ℂ (qop ((r : ℂ) • P) y) y) ≤ r * ‖y‖ ^ 2 := by
  have hsa := qop_isSelfAdjoint hP
  have hq : inner ℂ (qop P y) y = ((‖qop P y‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : qop P y = qop P (qop P y) := by
      conv_lhs => rw [← hPP]
      rw [qop_mul]
      rfl
    conv_lhs => rw [h1]
    rw [← hsa.adjoint_eq, adjoint_inner_left, hsa.adjoint_eq, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hle : ‖qop P y‖ ≤ ‖y‖ := by
    by_cases h0 : ‖qop P y‖ = 0
    · rw [h0]
      exact norm_nonneg _
    · have h2 : ‖qop P y‖ ^ 2 ≤ ‖qop P y‖ * ‖y‖ := by
        have h3 : ((‖qop P y‖ ^ 2 : ℝ) : ℂ) = inner ℂ (qop P y) y := hq.symm
        have h4 : ‖inner ℂ (qop P y) y‖ ≤ ‖qop P y‖ * ‖y‖ := norm_inner_le_norm _ _
        rw [← h3, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h4
        exact h4
      have hpos : 0 < ‖qop P y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  rw [qop_smul, smul_apply, inner_smul_left, Complex.conj_ofReal, hq, ← Complex.ofReal_mul,
    RCLike.re_to_complex, Complex.ofReal_re]
  refine ⟨by positivity, ?_⟩
  have := pow_le_pow_left₀ (norm_nonneg _) hle 2
  nlinarith

/-! ### Row and column sums of the clipped entries -/

/-- `∑_j |c₂| ≤ β ρ` along rows. -/
theorem cl2_row_le (D : Data X n (Cfg (VW b)) s) {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (x : X) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (i : n) :
    ∑ j, ‖cl2 D μ β x (i, j)‖ ≤ β * (η ^ 2 / μ ^ 2) := by
  calc ∑ j, ‖cl2 D μ β x (i, j)‖ ≤ ∑ j, β / μ ^ 2 * ‖D.matrix x i j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        refine (LargeSparsityCore.Native.norm_ccorr_le hμ hβ _).trans (le_of_eq ?_)
        ring
    _ = β / μ ^ 2 * ∑ j, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ β / μ ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left (hrow i) (by positivity)
    _ = β * (η ^ 2 / μ ^ 2) := by ring

/-- `∑_i |c₂| ≤ β ρ` along columns. -/
theorem cl2_col_le (D : Data X n (Cfg (VW b)) s) {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (x : X) (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (j : n) :
    ∑ i, ‖cl2 D μ β x (i, j)‖ ≤ β * (η ^ 2 / μ ^ 2) := by
  calc ∑ i, ‖cl2 D μ β x (i, j)‖ ≤ ∑ i, β / μ ^ 2 * ‖D.matrix x i j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        refine (LargeSparsityCore.Native.norm_ccorr_le hμ hβ _).trans (le_of_eq ?_)
        ring
    _ = β / μ ^ 2 * ∑ i, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ β / μ ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left (hcol j) (by positivity)
    _ = β * (η ^ 2 / μ ^ 2) := by ring

theorem norm_cl1_sq_le (D : Data X n (Cfg (VW b)) s) {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (x : X) (e : n × n) : ‖cl1 D μ β x e‖ ^ 2 ≤ (μ ^ 2)⁻¹ * ‖D.matrix x e.1 e.2‖ ^ 2 := by
  have h1 := LargeSparsityCore.Native.norm_cclip_le hμ hβ (D.matrix x e.1 e.2)
  have h2 : (‖D.matrix x e.1 e.2‖ / μ) ^ 2 = (μ ^ 2)⁻¹ * ‖D.matrix x e.1 e.2‖ ^ 2 := by
    field_simp
  rw [← h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- `∑_j |c₁|² ≤ ρ` along rows. -/
theorem cl1_row_le (D : Data X n (Cfg (VW b)) s) {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (x : X) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (i : n) :
    ∑ j, ‖cl1 D μ β x (i, j)‖ ^ 2 ≤ η ^ 2 / μ ^ 2 := by
  calc ∑ j, ‖cl1 D μ β x (i, j)‖ ^ 2 ≤ ∑ j, (μ ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => norm_cl1_sq_le D hμ hβ x (i, j)
    _ = (μ ^ 2)⁻¹ * ∑ j, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (μ ^ 2)⁻¹ * η ^ 2 := mul_le_mul_of_nonneg_left (hrow i) (by positivity)
    _ = η ^ 2 / μ ^ 2 := by ring

/-- `∑_i |c₁|² ≤ ρ` along columns. -/
theorem cl1_col_le (D : Data X n (Cfg (VW b)) s) {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    (x : X) (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (j : n) :
    ∑ i, ‖cl1 D μ β x (i, j)‖ ^ 2 ≤ η ^ 2 / μ ^ 2 := by
  calc ∑ i, ‖cl1 D μ β x (i, j)‖ ^ 2 ≤ ∑ i, (μ ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => norm_cl1_sq_le D hμ hβ x (i, j)
    _ = (μ ^ 2)⁻¹ * ∑ i, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (μ ^ 2)⁻¹ * η ^ 2 := mul_le_mul_of_nonneg_left (hcol j) (by positivity)
    _ = η ^ 2 / μ ^ 2 := by ring

end

end GateOptimalBinary
