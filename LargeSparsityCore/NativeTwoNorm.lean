import LargeSparsityCore.NativeMoments

set_option autoImplicit false

/-!
# The joint representation at a separate entry scale

Appendix B (the proof of Theorem `hs:thm:two-norm`, paragraph "Large `h` with `τ_ent ≥ Lh`") clips
the entries at the scale `μ` of a supplied entry bound `‖H‖_max ≤ μ`, while the row and column
Euclidean norms are bounded by `η ≥ μ` (`twonorm:eq:clip`). The operators of the joint
representation (`Kop`, `Dop`, `Ppl`, `Pmi`) are those of `NativeOperators` with clipping scale `μ`;
only the moment bounds change: with the ratio `ρ = η²/μ²` every row and column sum of `|c₂|` is at
most `βρ` and of `|c₁|²` at most `ρ` (`twonorm:eq:clip-bounds`), so the moments of `NativeMoments`
acquire the factor `ρ`, which turns the sparsity `s` into the moment parameter `σ = s/ρ = sμ²/η²`
(`twonorm:eq:weights`, `twonorm:eq:joint-moments`). The compression uses only the entry bound
(`compression_of_entry`: `J†KJ = (q/(sμ)) H`).

* `c2_sums_ratio`, `c1_sums_ratio`: the row and column sums.
* `norm_Ppl_input_sq_le_ratio`, `norm_Pmi_input_sq_le_ratio` (`≤ βρ/(2s)`),
  `norm_bulk_input_sq_le_ratio` (`≤ 2q²ρ/s`), `norm_K_input_sq_le_ratio` (`≤ 2q²(1 + β)ρ/s`).
* `Mjoint_eq_of_entry`, `compression_of_entry`.

With `η = μ` (`ρ = 1`) these are the bounds of `NativeMoments`.
-/

namespace LargeSparsityCore.Native

noncomputable section

open ContinuousLinearMap SparseHamiltonian NativeSignedFactor OrientedNativeLayout
open NativeSparseBlockEncoding OracleCircuit CayleyBlocks SparseEdgeMoments
open scoped InnerProduct ComplexConjugate

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-! ### Row and column sums at a separate entry scale -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- With clipping scale `μ` and row and column norms at most `η`, the rows and columns of `|c₂|`
sum to at most `β η²/μ²`. -/
theorem c2_sums_ratio {D : Data X n Z s} {μ η β : ℝ} {x : X} (h : Promise D η x) (hμ : 0 < μ)
    (hβ : 0 ≤ β) :
    (∀ i, ∑ j, ‖c2 D μ β ((i, j), D.table x (i, j))‖ ≤ β * (η ^ 2 / μ ^ 2)) ∧
      (∀ j, ∑ i, ‖c2 D μ β ((i, j), D.table x (i, j))‖ ≤ β * (η ^ 2 / μ ^ 2)) := by
  have hb : ∀ i j, ‖c2 D μ β ((i, j), D.table x (i, j))‖ ≤ β / μ ^ 2 * ‖D.matrix x i j‖ ^ 2 := by
    intro i j
    rw [c2_table]
    refine (norm_ccorr_le hμ hβ _).trans (le_of_eq ?_)
    ring
  have hμ2 : 0 < μ ^ 2 := by positivity
  constructor
  · intro i
    calc ∑ j, ‖c2 D μ β ((i, j), D.table x (i, j))‖ ≤ ∑ j, β / μ ^ 2 * ‖D.matrix x i j‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hb i j
      _ = β / μ ^ 2 * ∑ j, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ β / μ ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left (h.1 i) (by positivity)
      _ = β * (η ^ 2 / μ ^ 2) := by ring
  · intro j
    calc ∑ i, ‖c2 D μ β ((i, j), D.table x (i, j))‖ ≤ ∑ i, β / μ ^ 2 * ‖D.matrix x i j‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hb i j
      _ = β / μ ^ 2 * ∑ i, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ β / μ ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left (h.2 j) (by positivity)
      _ = β * (η ^ 2 / μ ^ 2) := by ring

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- With clipping scale `μ` and row and column norms at most `η`, the rows and columns of `|c₁|²`
sum to at most `η²/μ²`. -/
theorem c1_sums_ratio {D : Data X n Z s} {μ η β : ℝ} {x : X} (h : Promise D η x) (hμ : 0 < μ)
    (hβ : 0 ≤ β) :
    (∀ i, ∑ j, ‖c1 D μ β ((i, j), D.table x (i, j))‖ ^ 2 ≤ η ^ 2 / μ ^ 2) ∧
      (∀ j, ∑ i, ‖c1 D μ β ((i, j), D.table x (i, j))‖ ^ 2 ≤ η ^ 2 / μ ^ 2) := by
  have hb : ∀ i j, ‖c1 D μ β ((i, j), D.table x (i, j))‖ ^ 2 ≤
      (μ ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := by
    intro i j
    rw [c1_table]
    have h1 := norm_cclip_le hμ hβ (D.matrix x i j)
    have h2 : (‖D.matrix x i j‖ / μ) ^ 2 = (μ ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := by
      field_simp
    rw [← h2]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hμ2 : 0 < μ ^ 2 := by positivity
  constructor
  · intro i
    calc ∑ j, ‖c1 D μ β ((i, j), D.table x (i, j))‖ ^ 2 ≤
          ∑ j, (μ ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := Finset.sum_le_sum fun j _ => hb i j
      _ = (μ ^ 2)⁻¹ * ∑ j, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (μ ^ 2)⁻¹ * η ^ 2 := mul_le_mul_of_nonneg_left (h.1 i) (by positivity)
      _ = η ^ 2 / μ ^ 2 := by ring
  · intro j
    calc ∑ i, ‖c1 D μ β ((i, j), D.table x (i, j))‖ ^ 2 ≤
          ∑ i, (μ ^ 2)⁻¹ * ‖D.matrix x i j‖ ^ 2 := Finset.sum_le_sum fun i _ => hb i j
      _ = (μ ^ 2)⁻¹ * ∑ i, ‖D.matrix x i j‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (μ ^ 2)⁻¹ * η ^ 2 := mul_le_mul_of_nonneg_left (h.2 j) (by positivity)
      _ = η ^ 2 / μ ^ 2 := by ring

/-! ### The moments at a separate entry scale -/

/-- **Isolated weight**: `‖P₊ J v‖² ≤ βρ/(2s) ‖v‖²`, `ρ = η²/μ²`. -/
theorem norm_Ppl_input_sq_le_ratio (D : Data X n Z s) {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    {x : X} (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖Ppl D μ β x (Jin D v)‖ ^ 2 ≤ β * (η ^ 2 / μ ^ 2) / (2 * s) * ‖v‖ ^ 2 := by
  have e1 : Ppl D μ β x (Jin D v) = adjoint (U D μ β x) (LamP (U D μ β x (Jin D v))) := rfl
  rw [e1, U_adjoint_norm, LamP]
  refine (norm_dg_input_sq_le D μ β x _ (fun f _ => if f = 0 then 1 else 0) ?_ v).trans ?_
  · intro b a f
    unfold ipl
    split_ifs <;> simp_all
  · have hsum := edge_sum_le D x (fun e => ‖c2 D μ β (e, D.table x e)‖ / 2)
      (fun e => by positivity) (W := β * (η ^ 2 / μ ^ 2) / 2)
      (fun i => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums_ratio hP hμ hβ).1 i) (by norm_num))
      (fun j => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums_ratio hP hμ hβ).2 j) (by norm_num)) v
    have e2 : ∀ e, (∑ f : Fin 3, (if f = 0 then (1 : ℝ) else 0) *
        ‖gflag (c2 D μ β (e, D.table x e)) f‖ ^ 2) = ‖c2 D μ β (e, D.table x e)‖ / 2 := by
      intro e
      rw [Fin.sum_univ_three]
      simp [norm_gflag_zero_sq]
    simp only [e2]
    refine hsum.trans (le_of_eq ?_)
    ring

/-- **Isolated weight**: `‖P₋ J v‖² ≤ βρ/(2s) ‖v‖²`, `ρ = η²/μ²`. -/
theorem norm_Pmi_input_sq_le_ratio (D : Data X n Z s) {μ η β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β)
    {x : X} (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖Pmi D μ β x (Jin D v)‖ ^ 2 ≤ β * (η ^ 2 / μ ^ 2) / (2 * s) * ‖v‖ ^ 2 := by
  have e1 : Pmi D μ β x (Jin D v) = adjoint (U D μ β x) (LamM (U D μ β x (Jin D v))) := rfl
  rw [e1, U_adjoint_norm, LamM]
  refine (norm_dg_input_sq_le D μ β x _ (fun f _ => if f = 0 then 1 else 0) ?_ v).trans ?_
  · intro b a f
    unfold imi
    split_ifs <;> simp_all
  · have hsum := edge_sum_le D x (fun e => ‖c2 D μ β (e, D.table x e)‖ / 2)
      (fun e => by positivity) (W := β * (η ^ 2 / μ ^ 2) / 2)
      (fun i => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums_ratio hP hμ hβ).1 i) (by norm_num))
      (fun j => by
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right ((c2_sums_ratio hP hμ hβ).2 j) (by norm_num)) v
    have e2 : ∀ e, (∑ f : Fin 3, (if f = 0 then (1 : ℝ) else 0) *
        ‖gflag (c2 D μ β (e, D.table x e)) f‖ ^ 2) = ‖c2 D μ β (e, D.table x e)‖ / 2 := by
      intro e
      rw [Fin.sum_univ_three]
      simp [norm_gflag_zero_sq]
    simp only [e2]
    refine hsum.trans (le_of_eq ?_)
    ring

/-- **Bulk second moment**: `‖K P₀ J v‖² ≤ (2q²ρ/s) ‖v‖²`, `ρ = η²/μ²`. -/
theorem norm_bulk_input_sq_le_ratio (D : Data X n Z s) {μ η β : ℝ} (q : ℝ) (hμ : 0 < μ)
    (hβ : 0 ≤ β) {x : X} (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖(Kop D μ β q x ∘L CayleyBlocks.bulk (Ppl D μ β x) (Pmi D μ β x)) (Jin D v)‖ ^ 2 ≤
      2 * q ^ 2 * (η ^ 2 / μ ^ 2) / s * ‖v‖ ^ 2 := by
  rw [Kbulk_eq, comp_apply, comp_apply, U_adjoint_norm]
  refine (norm_dg_input_sq_le D μ β x _
    (fun f a => if f = 2 then 4 * q ^ 2 * ‖c1 D μ β a‖ ^ 2 else 0) ?_ v).trans ?_
  · intro b a f
    have hs : |sgn b| = 1 := by unfold sgn; split_ifs <;> simp
    by_cases hf0 : f = 0
    · subst hf0
      cases b <;> simp [ipl, imi]
    · by_cases hf1 : f = 1
      · subst hf1
        simp [kappa]
      · have hf2 : f = 2 := by omega
        subst hf2
        simp only [kappa, ipl, imi, Fin.isValue, Fin.reduceEq, if_false, and_false, sub_zero,
          mul_one, if_true]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        have : (2 * q * ‖c1 D μ β a‖ * sgn b) ^ 2 = 4 * q ^ 2 * ‖c1 D μ β a‖ ^ 2 * (sgn b) ^ 2 := by
          ring
        rw [this, ← sq_abs (sgn b), hs]
        ring_nf
        exact le_rfl
  · have e2 : ∀ e, (∑ f : Fin 3, (if f = 2 then 4 * q ^ 2 * ‖c1 D μ β (e, D.table x e)‖ ^ 2
        else 0) * ‖gflag (c2 D μ β (e, D.table x e)) f‖ ^ 2) =
        2 * q ^ 2 * ‖c1 D μ β (e, D.table x e)‖ ^ 2 := by
      intro e
      rw [Fin.sum_univ_three]
      simp only [Fin.isValue, Fin.reduceEq, if_false, zero_mul, if_true, norm_gflag_two_sq,
        zero_add]
      ring
    simp only [e2]
    have hsum := edge_sum_le D x (fun e => 2 * q ^ 2 * ‖c1 D μ β (e, D.table x e)‖ ^ 2)
      (fun e => by positivity) (W := 2 * q ^ 2 * (η ^ 2 / μ ^ 2))
      (fun i => by
        rw [← Finset.mul_sum]
        have := (c1_sums_ratio hP hμ hβ).1 i
        exact mul_le_mul_of_nonneg_left this (by positivity))
      (fun j => by
        rw [← Finset.mul_sum]
        have := (c1_sums_ratio hP hμ hβ).2 j
        exact mul_le_mul_of_nonneg_left this (by positivity)) v
    exact hsum

/-- **Full second moment**: `‖K J v‖² ≤ (2q²(1 + β)ρ/s) ‖v‖²`, `ρ = η²/μ²`. -/
theorem norm_K_input_sq_le_ratio (D : Data X n Z s) {μ η β : ℝ} (q : ℝ) (hμ : 0 < μ)
    (hβ : 0 ≤ β) {x : X} (hP : Promise D η x) (v : EuclideanSpace ℂ n) :
    ‖Kop D μ β q x (Jin D v)‖ ^ 2 ≤ 2 * q ^ 2 * (1 + β) * (η ^ 2 / μ ^ 2) / s * ‖v‖ ^ 2 := by
  rw [Kop, comp_apply, comp_apply, U_adjoint_norm, LamK]
  refine (norm_dg_input_sq_le D μ β x _
    (fun f a => if f = 0 then 4 * q ^ 2 else if f = 1 then 0 else
      4 * q ^ 2 * ‖c1 D μ β a‖ ^ 2) ?_ v).trans ?_
  · intro b a f
    have hs : (sgn b) ^ 2 = 1 := by unfold sgn; split_ifs <;> norm_num
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    unfold kappa
    split_ifs
    · have : (2 * q * sgn b) ^ 2 = 4 * q ^ 2 * (sgn b) ^ 2 := by ring
      rw [this, hs, mul_one]
    · simp
    · have : (2 * q * ‖c1 D μ β a‖ * sgn b) ^ 2 = 4 * q ^ 2 * ‖c1 D μ β a‖ ^ 2 * (sgn b) ^ 2 := by
        ring
      rw [this, hs, mul_one]
  · have e2 : ∀ e, (∑ f : Fin 3, (if f = 0 then 4 * q ^ 2 else if f = 1 then 0 else
        4 * q ^ 2 * ‖c1 D μ β (e, D.table x e)‖ ^ 2) *
          ‖gflag (c2 D μ β (e, D.table x e)) f‖ ^ 2) =
        2 * q ^ 2 * (‖c2 D μ β (e, D.table x e)‖ + ‖c1 D μ β (e, D.table x e)‖ ^ 2) := by
      intro e
      rw [Fin.sum_univ_three]
      simp only [Fin.isValue, Fin.reduceEq, if_false, if_true, zero_mul, norm_gflag_two_sq,
        norm_gflag_zero_sq, add_zero]
      ring
    simp only [e2]
    have hρ : 0 ≤ η ^ 2 / μ ^ 2 := by positivity
    have hsum := edge_sum_le D x
      (fun e => 2 * q ^ 2 * (‖c2 D μ β (e, D.table x e)‖ + ‖c1 D μ β (e, D.table x e)‖ ^ 2))
      (fun e => by positivity) (W := 2 * q ^ 2 * (β * (η ^ 2 / μ ^ 2) + η ^ 2 / μ ^ 2))
      (fun i => by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        have h1 := (c2_sums_ratio hP hμ hβ).1 i
        have h2 := (c1_sums_ratio hP hμ hβ).1 i
        exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity))
      (fun j => by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
        have h1 := (c2_sums_ratio hP hμ hβ).2 j
        have h2 := (c1_sums_ratio hP hμ hβ).2 j
        exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)) v
    refine hsum.trans (le_of_eq ?_)
    ring

/-! ### The compression under an entry bound -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem Mjoint_eq_of_entry (D : Data X n Z s) {μ β : ℝ} (hμ : 0 < μ) (hβ : 0 ≤ β) {x : X}
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    Mjoint D μ β x = fun i j => D.matrix x i j * (μ : ℂ)⁻¹ := by
  funext i j
  rw [Mjoint, c1_table, c2_table, cclip_add_ccorr hμ hβ (hent i j), div_eq_mul_inv]

/-- **The joint compression under an entry bound** (`twonorm:eq:joint-moments`):
`J† K J = H/α` with `α = sμ/q`, for entries of modulus at most the clipping scale `μ`. -/
theorem compression_of_entry (D : Data X n Z s) {μ β : ℝ} (q : ℝ) (hμ : 0 < μ) (hβ : 0 < β)
    {x : X} (hH : (D.matrix x).IsHermitian) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) :
    (Jin D)† ∘L Kop D μ β q x ∘L Jin D =
      ((q / (s * μ) : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  set M := Mjoint D μ β x with hMdef
  have hM : M = fun i j => D.matrix x i j * (μ : ℂ)⁻¹ := Mjoint_eq_of_entry D hμ hβ.le hent
  have hMH : M.IsHermitian := by
    rw [hM]
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_mul', hH.apply i j, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  have hrow : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.rowloc x) i j := by
    intro i j h
    apply D.row_covers x i j
    intro h0
    exact h (by simp [hM, h0])
  have hcol : ∀ i j, M i j ≠ 0 → SparseSlotStates.selected (D.colloc x) j i := by
    intro i j h
    apply D.column_covers x i j
    intro h0
    exact h (by simp [hM, h0])
  have hcomp := generator_compression D.slots_pos M hMH (D.rowloc x) (D.colloc x) hrow hcol
  rw [generator, smul_comp, comp_smul] at hcomp
  have hs0 : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast D.slots_pos)
    exact_mod_cast this.ne'
  have hr : (Real.sqrt (s : ℝ) : ℂ) * (Real.sqrt (s : ℝ) : ℂ) = (s : ℂ) := by
    have h : Real.sqrt (s : ℝ) * Real.sqrt (s : ℝ) = (s : ℝ) :=
      Real.mul_self_sqrt (Nat.cast_nonneg s)
    exact_mod_cast h
  have hX : (boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
      boundary (D.rowloc x) (D.colloc x) = (s : ℂ)⁻¹ • SparseStateOverlap.matrixOperator M := by
    calc (boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
          boundary (D.rowloc x) (D.colloc x)
        = (Real.sqrt (s : ℝ) : ℂ)⁻¹ • ((Real.sqrt (s : ℝ) : ℂ) •
            ((boundary (D.rowloc x) (D.colloc x))† ∘L entryGenerator M ∘L
              boundary (D.rowloc x) (D.colloc x))) := by
          rw [smul_smul, inv_mul_cancel₀ hs0, one_smul]
      _ = (s : ℂ)⁻¹ • SparseStateOverlap.matrixOperator M := by
          rw [hcomp, smul_smul, ← mul_inv, hr]
  have hMop : SparseStateOverlap.matrixOperator M =
      (μ : ℂ)⁻¹ • SparseStateOverlap.matrixOperator (D.matrix x) := by
    rw [hM, NativeSignedFactor.matrixOperator_mul_const]
  apply ContinuousLinearMap.ext
  intro v'
  apply ext_inner_left ℂ
  intro v
  rw [comp_apply, comp_apply, adjoint_inner_right, inner_input_K D q hμ hβ x,
    ← adjoint_inner_right, ← comp_apply, ← comp_apply, comp_assoc, ← hMdef, hX, hMop,
    smul_apply, smul_apply, smul_apply, inner_smul_right, inner_smul_right, inner_smul_right,
    ← mul_assoc, ← mul_assoc]
  congr 1
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast D.slots_pos.ne'
  push_cast
  field_simp

end

end LargeSparsityCore.Native
