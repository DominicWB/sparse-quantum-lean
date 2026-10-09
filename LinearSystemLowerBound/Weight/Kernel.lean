import LinearSystemLowerBound.Weight.Growth

/-!
# Kernel potentials and the parity bound

An adaptive protocol performs fresh runs, measures them and branches on the outcomes.  Its
purification over all runs is described, input by input, by the Gram kernel
`G j j' = ⟨Φ_j, Φ_{j'}⟩` of the joint state of the past runs; a fresh run with outputs `v_j`
multiplies the kernel entrywise by `gram v` (Schur/Hadamard product).  Positive semidefinite
kernels factor as `G = BᴴB`, so all estimates reduce to single families.

* `pot G = Re ∑ (WᴴW)_{jj'} G_{jj'}` is the weighted norm of the purified state.
* `pot_hadamard_gram_eq`: `pot (G ⊙ gram v) = ∑_k ‖W (B_k v)‖²` for `G = BᴴB`.
* `pot_growth`: a circuit with weight growth `C` multiplies the potential by at most `C`.
* `gram_split`: a two-outcome measurement with isometric flag `F` splits the kernel.
* `parity_kernel_bound`: `|∑_j (-1)^{F(j)} G_jj Re⟨a_j, M a_j⟩| ≤ 2^{-|ι|} pot (G ⊙ gram a)`
  for even `m` and `‖M‖ ≤ 1` (the paper's `‖W⁻¹ Z^{⊗n} W⁻¹‖ = 2^{-n}`).
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder MatrixOrder
open SparseHamiltonian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The quadratic weight `WᴴW`. -/
def wsq (ι : Type*) [Fintype ι] [DecidableEq ι] (m : ℕ) : Matrix (ι → Fin m) (ι → Fin m) ℂ :=
  (kron (weight m))ᴴ * kron (weight m)

/-- **The potential of a kernel**: the weighted norm of the purified state. -/
def pot (G : Matrix (ι → Fin m) (ι → Fin m) ℂ) : ℝ :=
  (∑ j, ∑ j', wsq ι m j j' * G j j').re

theorem norm_sq_act_eq (A : Matrix (ι → Fin m) (ι → Fin m) ℂ) (φ : Fam (ι → Fin m) K) :
    ‖act A φ‖ ^ 2 = (∑ j, ∑ j', (Aᴴ * A) j j' * ⟪φ j, φ j'⟫_ℂ).re := by
  have h : ‖act A φ‖ ^ 2 = (⟪act A φ, act A φ⟫_ℂ).re := by
    rw [inner_self_cpx]
    norm_cast
  rw [h, inner_act, ← act_mul, inner_fam]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [act_apply, inner_sum, inner_smul_right]

theorem pot_add (G H : Matrix (ι → Fin m) (ι → Fin m) ℂ) : pot (G + H) = pot G + pot H := by
  simp only [pot, Matrix.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]

/-- **Factorisation.**  For `G = BᴴB` the potential of `G ⊙ gram v` is a sum of weighted
norms of single families. -/
theorem pot_hadamard_gram_eq (B : Matrix (ι → Fin m) (ι → Fin m) ℂ) (v : Fam (ι → Fin m) K) :
    pot ((star B * B) ⊙ Matrix.gram ℂ (fun j => v j)) =
      ∑ k, ‖act (kron (weight m)) (scale (B k) v)‖ ^ 2 := by
  set g : (ι → Fin m) → (ι → Fin m) → (ι → Fin m) → ℂ := fun k j j' =>
    wsq ι m j j' * ((starRingEnd ℂ) (B k j) * B k j' * ⟪v j, v j'⟫_ℂ)
  have h : ∀ k, ‖act (kron (weight m)) (scale (B k) v)‖ ^ 2 = (∑ j, ∑ j', g k j j').re := by
    intro k
    rw [norm_sq_act_eq]
    congr 1
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro j' _
    simp only [g, scale_apply, inner_smul_left, inner_smul_right, wsq]
    ring
  have hswap : (∑ k, ∑ j, ∑ j', g k j j') = ∑ j, ∑ j', ∑ k, g k j j' := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_comm]
  simp only [h]
  rw [← Complex.re_sum, hswap, pot]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro j' _
  simp only [g, Matrix.hadamard_apply, Matrix.gram_apply, Matrix.mul_apply, Matrix.star_apply,
    RCLike.star_def, Finset.sum_mul, Finset.mul_sum]

/-- A positive semidefinite kernel factors as `BᴴB`. -/
theorem exists_factor {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef) :
    ∃ B : Matrix (ι → Fin m) (ι → Fin m) ℂ, G = star B * B :=
  CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.nonneg

theorem pot_hadamard_gram_nonneg {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef)
    (v : Fam (ι → Fin m) K) : 0 ≤ pot (G ⊙ Matrix.gram ℂ (fun j => v j)) := by
  obtain ⟨B, rfl⟩ := exists_factor hG
  rw [pot_hadamard_gram_eq]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- The trivial kernel `J` (all entries one): the potential of a fresh, input-independent
state. -/
def onesKernel (ι : Type*) [Fintype ι] (m : ℕ) : Matrix (ι → Fin m) (ι → Fin m) ℂ :=
  Matrix.of fun _ _ => 1

omit [DecidableEq ι] in
theorem onesKernel_posSemidef : (onesKernel ι m).PosSemidef := by
  have h : onesKernel ι m = Matrix.gram ℂ (fun _ : ι → Fin m => (1 : ℂ)) := by
    ext j j'
    simp [onesKernel, Matrix.gram_apply]
  rw [h]
  exact Matrix.posSemidef_gram ℂ _

omit [DecidableEq ι] in
theorem hadamard_gram_posSemidef {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef)
    (v : (ι → Fin m) → K) : (G ⊙ Matrix.gram ℂ v).PosSemidef :=
  hG.hadamard (Matrix.posSemidef_gram ℂ v)

theorem pot_nonneg {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef) : 0 ≤ pot G := by
  have h : G = G ⊙ Matrix.gram ℂ (fun _ : ι → Fin m => (1 : ℂ)) := by
    ext j j'
    simp [Matrix.hadamard_apply, Matrix.gram_apply]
  rw [h]
  exact pot_hadamard_gram_nonneg hG (WithLp.toLp 2 (fun _ => (1 : ℂ)))

omit [Fintype ι] [DecidableEq ι] in
/-- An input-independent unit seed leaves the kernel unchanged. -/
theorem hadamard_gram_const (G : Matrix (ι → Fin m) (ι → Fin m) ℂ) (u : K) (hu : ‖u‖ = 1) :
    G ⊙ Matrix.gram ℂ (fun _ : ι → Fin m => u) = G := by
  ext j j'
  simp [Matrix.hadamard_apply, Matrix.gram_apply, hu]

/-- **Weight growth of the potential.** -/
theorem pot_growth {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef)
    {O : (ι → Fin m) → K →L[ℂ] K} {C : ℝ} (hO : Growth O C) (v : Fam (ι → Fin m) K) :
    pot (G ⊙ Matrix.gram ℂ (fun j => joint O v j)) ≤
      C * pot (G ⊙ Matrix.gram ℂ (fun j => v j)) := by
  obtain ⟨B, rfl⟩ := exists_factor hG
  rw [pot_hadamard_gram_eq, pot_hadamard_gram_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  rw [← joint_scale]
  exact hO _

/-! ### Measurements -/

section Measurement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [Fintype ι] [DecidableEq ι] in
/-- **Measurement split.**  For an isometric flag `F`, the Gram matrix of a family is the sum
of the Gram matrices of its decoded success part `F† v` and its failure part `v - F F† v`. -/
theorem gram_split [CompleteSpace K] (F : E →L[ℂ] K) (hF : F† ∘L F = 1)
    (v : (ι → Fin m) → K) :
    Matrix.gram ℂ v = Matrix.gram ℂ (fun j => (F†) (v j)) +
      Matrix.gram ℂ (fun j => v j - F ((F†) (v j))) := by
  ext j j'
  simp only [Matrix.add_apply, Matrix.gram_apply]
  have hFF : ∀ x : K, (F†) (F ((F†) x)) = (F†) x := by
    intro x
    have := congrArg (fun T : E →L[ℂ] E => T ((F†) x)) hF
    simpa using this
  have e1 : ⟪F ((F†) (v j)), F ((F†) (v j'))⟫_ℂ = ⟪(F†) (v j), (F†) (v j')⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hFF]
  have e2 : ⟪F ((F†) (v j)), v j' - F ((F†) (v j'))⟫_ℂ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, map_sub, hFF, sub_self, inner_zero_right]
  have e3 : ⟪v j - F ((F†) (v j)), F ((F†) (v j'))⟫_ℂ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left, map_sub, hFF, sub_self, inner_zero_left]
  calc ⟪v j, v j'⟫_ℂ = ⟪F ((F†) (v j)) + (v j - F ((F†) (v j))),
        F ((F†) (v j')) + (v j' - F ((F†) (v j')))⟫_ℂ := by simp only [add_sub_cancel]
    _ = _ := by
      rw [inner_add_left, inner_add_right, inner_add_right, e1, e2, e3]
      ring

end Measurement

/-! ### The parity bound -/

section Parity

theorem act_kron_parity_apply (φ : Fam (ι → Fin m) K) (j : ι → Fin m) :
    act (kron (parityMat m)) φ j = (parSign j : ℂ) • φ j := by
  rw [parityMat, kron_diagonal]
  simp [act_apply, Matrix.diagonal_apply, parSign]

theorem kron_weightInv_mul_weight (hm : m ≠ 0) :
    kron (ι := ι) (weightInv m) * kron (weight m) = 1 := by
  rw [kron_mul, weightInv_mul_weight hm, kron_one]

/-- **Parity bound for one family.** -/
theorem parity_bound (hm : Even m) (hm0 : m ≠ 0) (M : K →L[ℂ] K) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (a : Fam (ι → Fin m) K) :
    |∑ j, parSign j * (⟪a j, M (a j)⟫_ℂ).re| ≤
      (1 / 2) ^ Fintype.card ι * ‖act (kron (weight m)) a‖ ^ 2 := by
  set ξ := act (kron (weight m)) a with hξ
  have ha : a = act (kron (weightInv m)) ξ := by
    rw [hξ, ← act_mul, kron_weightInv_mul_weight hm0, act_one]
  set χ := act (kron (parityKernel m)) (joint (fun _ => M) ξ)
  have hsum : ∑ j, parSign j * (⟪a j, M (a j)⟫_ℂ).re = (⟪ξ, χ⟫_ℂ).re := by
    have h1 : ∑ j, parSign j * (⟪a j, M (a j)⟫_ℂ).re =
        (⟪a, act (kron (parityMat m)) (joint (fun _ => M) a)⟫_ℂ).re := by
      rw [inner_fam, Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [act_kron_parity_apply, joint_apply, inner_smul_right, Complex.re_ofReal_mul]
    have h2 : act (kron (parityMat m)) (joint (fun _ => M) a) =
        act (kron (parityMat m)) (act (kron (weightInv m)) (joint (fun _ => M) ξ)) := by
      rw [ha, ← act_joint_const]
    rw [h1, h2]
    conv_lhs => rw [ha]
    rw [inner_act, kron_conjTranspose, weightInv_conjTranspose, ← act_mul, ← act_mul,
      kron_mul, kron_mul]
    rfl
  rw [hsum]
  have hχ : ‖χ‖ ^ 2 ≤ (1 / 4) ^ Fintype.card ι * ‖joint (fun _ => M) ξ‖ ^ 2 :=
    norm_sq_act_kron_le (parityKernel m) (1 / 4) (by norm_num)
      (fun φ => norm_sq_act_parityKernel_le hm hm0 φ) _ ι rfl _
  have hMξ : ‖joint (fun _ => M) ξ‖ ≤ ‖ξ‖ := by
    have h2 : ‖joint (fun _ => M) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
      rw [norm_sq_fam, norm_sq_fam]
      exact Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hM (ξ j)) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2
  have hχ' : ‖χ‖ ≤ (1 / 2) ^ Fintype.card ι * ‖ξ‖ := by
    have hpos : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card ι * ‖ξ‖ := by positivity
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) hpos two_ne_zero).mp
    calc ‖χ‖ ^ 2 ≤ (1 / 4) ^ Fintype.card ι * ‖joint (fun _ => M) ξ‖ ^ 2 := hχ
      _ ≤ (1 / 4) ^ Fintype.card ι * ‖ξ‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) hMξ 2
      _ = ((1 / 2) ^ Fintype.card ι * ‖ξ‖) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]
        norm_num
  calc |(⟪ξ, χ⟫_ℂ).re| ≤ ‖⟪ξ, χ⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖ξ‖ * ‖χ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * ((1 / 2) ^ Fintype.card ι * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left hχ' (norm_nonneg _)
    _ = (1 / 2) ^ Fintype.card ι * ‖ξ‖ ^ 2 := by ring

/-- **Parity bound for a kernel.** -/
theorem parity_kernel_bound (hm : Even m) (hm0 : m ≠ 0) {G : Matrix (ι → Fin m) (ι → Fin m) ℂ}
    (hG : G.PosSemidef) (M : K →L[ℂ] K) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (a : Fam (ι → Fin m) K) :
    |∑ j, parSign j * ((G j j).re * (⟪a j, M (a j)⟫_ℂ).re)| ≤
      (1 / 2) ^ Fintype.card ι * pot (G ⊙ Matrix.gram ℂ (fun j => a j)) := by
  obtain ⟨B, rfl⟩ := exists_factor hG
  rw [pot_hadamard_gram_eq, Finset.mul_sum]
  have hdiag : ∀ j, ((star B * B) j j).re * (⟪a j, M (a j)⟫_ℂ).re =
      ∑ k, (⟪scale (B k) a j, M (scale (B k) a j)⟫_ℂ).re := by
    intro j
    simp only [Matrix.mul_apply, Matrix.star_apply, scale_apply, map_smul, inner_smul_left,
      inner_smul_right, RCLike.star_def]
    rw [Complex.re_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_assoc, Complex.mul_conj', ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hswap : ∑ j, parSign j * (((star B * B) j j).re * (⟪a j, M (a j)⟫_ℂ).re) =
      ∑ k, ∑ j, parSign j * (⟪scale (B k) a j, M (scale (B k) a j)⟫_ℂ).re := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hdiag, Finset.mul_sum]
  rw [hswap]
  calc |∑ k, ∑ j, parSign j * (⟪scale (B k) a j, M (scale (B k) a j)⟫_ℂ).re|
      ≤ ∑ k, |∑ j, parSign j * (⟪scale (B k) a j, M (scale (B k) a j)⟫_ℂ).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun k _ => parity_bound hm hm0 M hM _

end Parity

end

end LinearSystemLowerBound
