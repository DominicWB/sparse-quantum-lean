import GeneralSparseODE.Padded

/-!
# The problem on `ℂ^N` inside the index register

The general solvers are stated on the `k`-qubit index register, for the matrix extended by zero to
the index words `≥ N` (`padLift D x`, the lift of `QData.padMat`). This module identifies the
problem on `ℂ^N` inside it. `validEmb N k` embeds `ℂ^N` into the index register (the basis vector
of `i` to the basis vector of the index word `binW k i`); it is an isometry (`norm_validEmb`), with
the restriction `validRes N k` to the valid index words as left inverse and adjoint
(`validRes_validEmb`, `inner_validEmb`). For an operator `A` on `ℂ^N`, `validLift A` is
`validEmb ∘ A ∘ validRes`, and:

* the lift of the matrix extended by zero is the lift of the matrix: `padLift D x =
  validLift (matrixOperator (D.matrix x))` (`padLift_eq`), so `padLift D x ∘ validEmb =
  validEmb ∘ matrixOperator (D.matrix x)` (`padLift_comp_validEmb`);
* **constant coefficients**: from sources `validEmb x₀`, `validEmb b` the solution of
  `x' = -padLift D x · x + validEmb b` is `validEmb` of the solution on `ℂ^N`
  (`solution_padLift_validEmb`); a source component on an invalid index word is decoupled from
  the matrix and evolves by `x_j(t) = x₀_j + t b_j` (`solution_padLift_invalid`);
* **time-dependent coefficients**: a solution of `x' = -G'(t) x + b(t)` on `ℂ^N` embeds to a
  solution for the lifted generator path `validLift ∘ G'` and the embedded forcing
  (`solves_validLift`, from `solves_comp`); the lift is accretive when `G'(t)` is
  (`accretive_validLift`), does not increase distances (`norm_validLift_sub_le`), and its distance
  to the lift `padLift D x` of a sample is at most the distance of `G'(t)` to the sample on `ℂ^N`
  (`norm_validLift_sub_padLift_le`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit
open SparseHamiltonian.GeneralSparseAccess
open GatePointerEncoding (wordValue wordValue_injective)
open scoped InnerProduct ComplexConjugate

/-! ### The embedding of `ℂ^N` -/

section Valid

variable (N k : ℕ)

/-- The matrix of the embedding of `ℂ^N` into the index register. -/
def validMat : Matrix (Cfg (Fin k)) (Fin N) ℂ :=
  fun y i => if wordValue y = i.val then 1 else 0

/-- **The embedding of `ℂ^N` into the index register**: the basis vector of `i` to the basis
vector of the index word `binW k i`. -/
def validEmb : EuclideanSpace ℂ (Fin N) →L[ℂ] Reg (Fin k) ℂ :=
  SparseStateOverlap.matrixOperator (validMat N k)

/-- **The restriction to the valid index words**: the amplitudes of the index words `binW k i`,
`i < N`. -/
def validRes : Reg (Fin k) ℂ →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  SparseStateOverlap.matrixOperator (validMat N k).conjTranspose

/-- **The lift of an operator on `ℂ^N`** to the index register: `validEmb ∘ A ∘ validRes`, zero on
the invalid index words. -/
def validLift (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  validEmb N k ∘L A ∘L validRes N k

variable {N k}

theorem validEmb_apply (v : EuclideanSpace ℂ (Fin N)) (y : Cfg (Fin k)) :
    validEmb N k v y = if h : wordValue y < N then v ⟨wordValue y, h⟩ else 0 := by
  show ∑ i, validMat N k y i * v i = _
  unfold validMat
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨wordValue y, h⟩]
    · simp
    · intro i _ hi
      have hne : wordValue y ≠ i.val := fun e => hi (Fin.ext e.symm)
      rw [if_neg hne, zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro i _
    have hne : wordValue y ≠ i.val := fun e => h (by rw [e]; exact i.isLt)
    rw [if_neg hne, zero_mul]

theorem validRes_apply (hN : N ≤ 2 ^ k) (ψ : Reg (Fin k) ℂ) (i : Fin N) :
    validRes N k ψ i = ψ (binW k i) := by
  show ∑ y, (validMat N k).conjTranspose i y * ψ y = _
  have hi : wordValue (binW k i) = i.val := wordValue_binW (lt_of_lt_of_le i.isLt hN)
  rw [Finset.sum_eq_single (binW k i)]
  · simp [Matrix.conjTranspose_apply, validMat, hi]
  · intro y _ hy
    have hne : wordValue y ≠ i.val := by
      intro e
      apply hy
      rw [← binW_wordValue y, e]
    simp [Matrix.conjTranspose_apply, validMat, hne]
  · intro hn
    exact absurd (Finset.mem_univ _) hn

/-- The sums over the valid index words are the sums over `Fin N`. -/
theorem sum_valid (hN : N ≤ 2 ^ k) (g : Fin N → ℂ) :
    ∑ y : Cfg (Fin k), (if h : wordValue y < N then g ⟨wordValue y, h⟩ else 0) = ∑ i, g i := by
  have hinj : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∀ j ∈ (Finset.univ : Finset (Fin N)),
      binW k i.val = binW k j.val → i = j := by
    intro i _ j _ h
    apply Fin.ext
    have := congrArg wordValue h
    rwa [wordValue_binW (lt_of_lt_of_le i.isLt hN),
      wordValue_binW (lt_of_lt_of_le j.isLt hN)] at this
  have himg : ∑ y ∈ Finset.univ.image (fun i : Fin N => binW k i.val),
      (if h : wordValue y < N then g ⟨wordValue y, h⟩ else 0) = ∑ i, g i := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro i _
    have hi : wordValue (binW k i.val) = i.val := wordValue_binW (lt_of_lt_of_le i.isLt hN)
    have hlt : wordValue (binW k i.val) < N := by rw [hi]; exact i.isLt
    rw [dif_pos hlt]
    congr 1
    exact Fin.ext hi
  rw [← himg]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro y _ hy
  rw [dif_neg]
  intro h
  apply hy
  rw [Finset.mem_image]
  exact ⟨⟨wordValue y, h⟩, Finset.mem_univ _, binW_wordValue y⟩

/-- `validRes` is a left inverse of `validEmb`. -/
theorem validRes_validEmb (hN : N ≤ 2 ^ k) (v : EuclideanSpace ℂ (Fin N)) :
    validRes N k (validEmb N k v) = v := by
  apply PiLp.ext
  intro i
  rw [validRes_apply hN, validEmb_apply]
  have hi : wordValue (binW k i.val) = i.val := wordValue_binW (lt_of_lt_of_le i.isLt hN)
  have hlt : wordValue (binW k i.val) < N := by rw [hi]; exact i.isLt
  rw [dif_pos hlt, show (⟨wordValue (binW k i.val), hlt⟩ : Fin N) = i from Fin.ext hi]

theorem validRes_comp_validEmb (hN : N ≤ 2 ^ k) :
    validRes N k ∘L validEmb N k = ContinuousLinearMap.id ℂ _ :=
  ContinuousLinearMap.ext fun v => validRes_validEmb hN v

/-- **`validRes` is the adjoint of `validEmb`.** -/
theorem inner_validEmb (hN : N ≤ 2 ^ k) (w : Reg (Fin k) ℂ) (u : EuclideanSpace ℂ (Fin N)) :
    inner ℂ w (validEmb N k u) = inner ℂ (validRes N k w) u := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  have e : ∀ y : Cfg (Fin k), inner ℂ (w y) (validEmb N k u y) =
      if h : wordValue y < N then inner ℂ (w (binW k (wordValue y))) (u ⟨wordValue y, h⟩)
        else 0 := by
    intro y
    rw [validEmb_apply]
    split_ifs with h
    · rw [binW_wordValue]
    · exact inner_zero_right _
  simp_rw [e]
  rw [sum_valid hN (fun i => inner ℂ (w (binW k i.val)) (u i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [validRes_apply hN]

/-- **`validEmb` is an isometry.** -/
theorem norm_validEmb (hN : N ≤ 2 ^ k) (v : EuclideanSpace ℂ (Fin N)) :
    ‖validEmb N k v‖ = ‖v‖ := by
  have h : ‖validEmb N k v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), inner_validEmb hN,
      validRes_validEmb hN]
  have h1 := norm_nonneg (validEmb N k v)
  have h2 := norm_nonneg v
  nlinarith [sq_nonneg (‖validEmb N k v‖ - ‖v‖), sq_nonneg (‖validEmb N k v‖ + ‖v‖)]

theorem norm_validRes_le (hN : N ≤ 2 ^ k) (ψ : Reg (Fin k) ℂ) : ‖validRes N k ψ‖ ≤ ‖ψ‖ := by
  have h : ‖validRes N k ψ‖ ^ 2 ≤ ‖ψ‖ * ‖validRes N k ψ‖ := by
    have e : ‖validRes N k ψ‖ ^ 2 = RCLike.re (inner ℂ ψ (validEmb N k (validRes N k ψ))) := by
      rw [inner_validEmb hN, inner_self_eq_norm_sq]
    rw [e]
    calc RCLike.re (inner ℂ ψ (validEmb N k (validRes N k ψ)))
        ≤ ‖inner ℂ ψ (validEmb N k (validRes N k ψ))‖ := RCLike.re_le_norm _
      _ ≤ ‖ψ‖ * ‖validEmb N k (validRes N k ψ)‖ := norm_inner_le_norm _ _
      _ = ‖ψ‖ * ‖validRes N k ψ‖ := by rw [norm_validEmb hN]
  have h0 := norm_nonneg (validRes N k ψ)
  have h1 := norm_nonneg ψ
  nlinarith

theorem opNorm_validEmb_le (hN : N ≤ 2 ^ k) : ‖validEmb N k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [norm_validEmb hN, one_mul]

theorem opNorm_validRes_le (hN : N ≤ 2 ^ k) : ‖validRes N k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => by
    rw [one_mul]
    exact norm_validRes_le hN ψ

/-- The unit direction commutes with the isometry `validEmb`. -/
theorem unitDirection_validEmb (hN : N ≤ 2 ^ k) (v : EuclideanSpace ℂ (Fin N)) :
    ODEStateNormalization.unitDirection (validEmb N k v) =
      validEmb N k (ODEStateNormalization.unitDirection v) := by
  unfold ODEStateNormalization.unitDirection
  rw [norm_validEmb hN, map_smul_of_tower]

/-! ### Lifted operators -/

theorem validLift_comp_validEmb (hN : N ≤ 2 ^ k)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    validLift N k A ∘L validEmb N k = validEmb N k ∘L A := by
  unfold validLift
  rw [comp_assoc, comp_assoc, validRes_comp_validEmb hN, comp_id]

theorem validLift_sub (A B : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    validLift N k (A - B) = validLift N k A - validLift N k B := by
  unfold validLift
  rw [sub_comp, comp_sub]

theorem norm_validLift_le (hN : N ≤ 2 ^ k)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    ‖validLift N k A‖ ≤ ‖A‖ := by
  unfold validLift
  calc ‖validEmb N k ∘L A ∘L validRes N k‖
      ≤ ‖validEmb N k‖ * (‖A‖ * ‖validRes N k‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by
        gcongr
        · exact opNorm_validEmb_le hN
        · exact opNorm_validRes_le hN
    _ = ‖A‖ := by ring

/-- **The lift does not increase distances.** -/
theorem norm_validLift_sub_le (hN : N ≤ 2 ^ k)
    (A B : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    ‖validLift N k A - validLift N k B‖ ≤ ‖A - B‖ := by
  rw [← validLift_sub]
  exact norm_validLift_le hN _

/-- **The lift of an accretive operator is accretive.** -/
theorem accretive_validLift (hN : N ≤ 2 ^ k)
    {A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)}
    (h : TimeDependentODE.Accretive A) : TimeDependentODE.Accretive (validLift N k A) := by
  intro w
  show 0 ≤ (inner ℂ w (validEmb N k (A (validRes N k w)))).re
  rw [inner_validEmb hN]
  exact h (validRes N k w)

end Valid

/-! ### The lift of the matrix extended by zero -/

section PadLift

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- **The lift of the matrix extended by zero is the lift of the matrix on `ℂ^N`.** -/
theorem padLift_eq (x : X) :
    padLift D x = validLift N k (SparseStateOverlap.matrixOperator (D.matrix x)) := by
  unfold padLift
  rw [qlift_refl_matrixOperator]
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [matOp_apply]
  show _ = validEmb N k (SparseStateOverlap.matrixOperator (D.matrix x) (validRes N k ψ)) y
  rw [validEmb_apply]
  by_cases hy : wordValue y < N
  · rw [dif_pos hy, SparseStateOverlap.matrixOperator_apply]
    have e : ∀ y' : Cfg (Fin k), D.padMat x y y' • ψ y' =
        if h : wordValue y' < N then D.matrix x ⟨wordValue y, hy⟩ ⟨wordValue y', h⟩ *
          ψ (binW k (wordValue y')) else 0 := by
      intro y'
      unfold QData.padMat
      by_cases hy' : wordValue y' < N
      · rw [dif_pos ⟨hy, hy'⟩, dif_pos hy', binW_wordValue, smul_eq_mul]
      · rw [dif_neg (fun h => hy' h.2), dif_neg hy', zero_smul]
    simp_rw [e]
    rw [sum_valid D.hN (fun j => D.matrix x ⟨wordValue y, hy⟩ j * ψ (binW k j.val))]
    apply Finset.sum_congr rfl
    intro j _
    rw [validRes_apply D.hN]
  · rw [dif_neg hy]
    apply Finset.sum_eq_zero
    intro y' _
    unfold QData.padMat
    rw [dif_neg (fun h => hy h.1), zero_smul]

theorem padLift_comp_validEmb (x : X) :
    padLift D x ∘L validEmb N k =
      validEmb N k ∘L SparseStateOverlap.matrixOperator (D.matrix x) := by
  rw [padLift_eq, validLift_comp_validEmb D.hN]

/-- **The distance of a lifted operator to the lift of a sample** is at most the distance on
`ℂ^N`. -/
theorem norm_validLift_sub_padLift_le (x : X)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    ‖validLift N k A - padLift D x‖ ≤ ‖A - SparseStateOverlap.matrixOperator (D.matrix x)‖ := by
  rw [padLift_eq]
  exact norm_validLift_sub_le D.hN _ _

/-- **Constant coefficients: the solution from sources in `ℂ^N`** is the embedding of the solution
on `ℂ^N`. -/
theorem solution_padLift_validEmb (x : X) (x0 v : EuclideanSpace ℂ (Fin N)) (t : ℝ) :
    ODEConstantForcing.solution (-padLift D x) (validEmb N k x0) (validEmb N k v) t =
      validEmb N k (ODEConstantForcing.solution
        (-SparseStateOverlap.matrixOperator (D.matrix x)) x0 v t) := by
  apply solution_comp
  rw [neg_comp, comp_neg, padLift_comp_validEmb]

/-- The lift of the matrix extended by zero vanishes on the invalid index words. -/
theorem padLift_apply_invalid (x : X) (ψ : Reg (Fin k) ℂ) {y : Cfg (Fin k)}
    (hy : ¬ wordValue y < N) : padLift D x ψ y = 0 := by
  rw [padLift_eq]
  show validEmb N k _ y = 0
  rw [validEmb_apply, dif_neg hy]

/-- **A source component on an invalid index word evolves freely**: `x_y(t) = x₀_y + t b_y`. -/
theorem solution_padLift_invalid (x : X) (x0 v : Reg (Fin k) ℂ) {y : Cfg (Fin k)}
    (hy : ¬ wordValue y < N) (t : ℝ) :
    ODEConstantForcing.solution (-padLift D x) x0 v t y = x0 y + (t : ℂ) * v y := by
  set F := ODEConstantForcing.solution (-padLift D x) x0 v with hF
  let P : Reg (Fin k) ℂ →L[ℝ] ℂ :=
    ((EuclideanSpace.proj y : EuclideanSpace ℂ (Cfg (Fin k)) →L[ℂ] ℂ)).restrictScalars ℝ
  have hP : ∀ ψ : Reg (Fin k) ℂ, P ψ = ψ y := fun ψ => rfl
  have hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => F u y - (u : ℂ) * v y) 0 u := by
    intro u
    have h1 := P.hasFDerivAt.comp_hasDerivAt u
      (ODEConstantForcing.solution_hasDerivAt (-padLift D x) x0 v u)
    have e1 : P ((-padLift D x) (F u) + v) = v y := by
      rw [hP]
      show -(padLift D x (F u) y) + v y = v y
      rw [padLift_apply_invalid D x _ hy, neg_zero, zero_add]
    rw [e1] at h1
    have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * v y) (((1 : ℝ) : ℂ) * v y) u :=
      ((hasDerivAt_id u).ofReal_comp).mul_const (v y)
    have h3 := h1.sub h2
    simp only [Complex.ofReal_one, one_mul, sub_self] at h3
    exact h3
  have hdiff : Differentiable ℝ (fun u : ℝ => F u y - (u : ℂ) * v y) :=
    fun u => (hd u).differentiableAt
  have h0 : F 0 = x0 := by
    rw [hF]
    exact ODEConstantForcing.solution_zero _ _ _
  have hconst := is_const_of_deriv_eq_zero hdiff (fun u => (hd u).deriv) t 0
  simp only [h0, Complex.ofReal_zero, zero_mul, sub_zero] at hconst
  rw [← hconst]
  ring

end PadLift

/-! ### Time-dependent coefficients along an intertwining map -/

section Solves

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- **A solution along an intertwining map**: if `x` solves `x' = -G(t) x + b(t)` on `[a, c]` and
`G'(t) ∘ L = L ∘ G(t)`, then `L ∘ x` solves `x' = -G'(t) x + L b(t)`. -/
theorem solves_comp (L : V →L[ℂ] W) {G : ℝ → V →L[ℂ] V} {G' : ℝ → W →L[ℂ] W}
    (hG : ∀ u, G' u ∘L L = L ∘L G u) {bf xs : ℝ → V} {a c : ℝ}
    (h : TimeDependentODE.SolvesODE G bf xs a c) :
    TimeDependentODE.SolvesODE G' (fun u => L (bf u)) (fun u => L (xs u)) a c := by
  intro u hu
  have h1 := ((L.restrictScalars ℝ).hasFDerivAt (x := xs u)).comp_hasDerivWithinAt u (h u hu)
  have e : (L.restrictScalars ℝ) (-(G u (xs u)) + bf u) = -(G' u (L (xs u))) + L (bf u) := by
    rw [ContinuousLinearMap.coe_restrictScalars', map_add, map_neg]
    congr 2
    exact (DFunLike.congr_fun (hG u) (xs u)).symm
  rw [e] at h1
  exact h1

end Solves

section SolvesValid

variable {N k : ℕ}

/-- **Time-dependent coefficients: a solution on `ℂ^N`** embeds to a solution for the lifted
generator path and the embedded forcing. -/
theorem solves_validLift (hN : N ≤ 2 ^ k)
    {G : ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)}
    {bf xs : ℝ → EuclideanSpace ℂ (Fin N)} {a c : ℝ}
    (h : TimeDependentODE.SolvesODE G bf xs a c) :
    TimeDependentODE.SolvesODE (fun u => validLift N k (G u)) (fun u => validEmb N k (bf u))
      (fun u => validEmb N k (xs u)) a c :=
  solves_comp (validEmb N k) (fun u => validLift_comp_validEmb hN (G u)) h

end SolvesValid

end

end SparseHamiltonian.GeneralSparseODE
