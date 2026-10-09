import ODELowerBoundExtensions.Padding.JointDense

/-!
# The densely padded joint family: class and instance facts

Manuscript: end of the proof of Theorem `odel:thm:joint`,
lines 3899-3903 ("Its norm is at most one and its entries are dyadic. It requires no membership
queries and leaves the solution unchanged."). The construction `jointDenseFamily` (dense block
`denseHam = 2^{-B} 1 1ᵀ` on the `Fin s` block, generator `denseGen`) is `Padding/JointDense`.

**What the block preserves.** `jointDenseFamily` has the same durations, sources and initial state
as `SparseLowerBounds.ODE.jointFamily`; its solution is the same `jointSol`, because `jointSol`
vanishes on the block (`jointSol_inr`, so `denseGen` and `jointGen` agree along it,
`jointDenseSol_solves`). It is in the class with `η = 1` and `g = √M`
(`jointDenseFamily_inClass`; the block rows have Euclidean norm `√s 2^{-B} ≤ 1` for `s ≤ 4^B`),
has `D = 0` (`jointDenseFamily_skew`), maximum row and column sparsity exactly `s` at every
stage (`jointDenseFamily_sparsityAttained`), exact dyadic entries `i · v/2^B`
(`jointDenseFamily_dyadic`), public locators, and the block has operator norm `s 2^{-B} ≤ 1` for
`s ≤ 2^B` (`norm_denseHam_le`). The access is a `hardCost` membership program
(`implementsOn_jointDense`); the query lower bound is `Padding/JointTheorem`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds SparseLowerBounds.ODE
open SparseLowerBounds.Hamiltonian (BitTable Word)

variable {M n μ s B : ℕ} {dense : Bool} {hμ : 1 ≤ μ} {hμs : 2 ^ μ ≤ s} {hμB : μ ≤ B} {T : ℝ}
  {hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T}

/-- The block is Hermitian (real symmetric). -/
theorem denseHam_isHermitian : (denseHam M μ s B dense).IsHermitian := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> cases dense <;>
    simp [denseHam, Matrix.conjTranspose_apply]

/-- **At `B = ⌈log₂ s⌉` the dense block is the released padding block**:
`denseHam … (padExp s) true = 0 ⊕ Hamiltonian.padBlock s` (`padBlock s = 2^{-⌈log₂ s⌉} 1 1ᵀ`,
line 2480). -/
theorem denseHam_padExp :
    denseHam M μ s (Hamiltonian.padExp s) true =
      (Matrix.fromBlocks 0 0 0 (Hamiltonian.padBlock s) :
        Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [denseHam, Matrix.fromBlocks_apply₂₂, Hamiltonian.padBlock]

/-- **The block has norm at most one** (line 3902): `‖2^{-B} 1 1ᵀ‖ = s 2^{-B} ≤ 1` for
`s ≤ 2^B`, needed only with the block (`dense = true`); at `B = padExp s` this is the released
`Hamiltonian.norm_padBlock_le` (`denseHam_padExp`). -/
theorem norm_denseHam_le (hsB : dense = true → s ≤ 2 ^ B) :
    ‖SparseStateOverlap.matrixOperator (denseHam M μ s B dense)‖ ≤ 1 :=
  denseBlock_norm_le denseHam_inl_left denseHam_inl_right denseHam_inr_inr
    (denseBlock_card_mul_norm_le hsB)

/-- **The joint solution vanishes on the block**: `x(t)_{inr t'} = 0`. -/
theorem jointSol_inr (x : Promised M n (2 ^ μ)) (t : ℝ) (t' : Fin s) :
    jointSol M n μ s T x t (Sum.inr t') = 0 := by
  simp [jointSol, jointSrc, jointInit, candState_inr]

/-- **The solution is unchanged** (line 3903): `jointSol` solves every instance of the dense
family, since `denseGen` and `jointGen` agree on vectors vanishing on the block. -/
theorem jointDenseSol_solves (x : Promised M n (2 ^ μ)) :
    (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).Solves x (jointSol M n μ s T x) := by
  have h0 := jointSol_solves (M := M) (n := n) (μ := μ) (s := s) (hμ := hμ) (hμs := hμs)
    (T := T) (hT := hT) x
  refine ⟨h0.1, fun k => ?_⟩
  refine solvesODE_congr_apply
    (G := fun _ => (jointFamily M n μ s hμ hμs T hT).gen x k) (fun u _ => ?_) (h0.2 k)
  exact denseBlock_add_I_smul_apply (jointGen x.1 k) (denseHam M μ s B dense) _
    (denseBlock_matrixOperator_eq_zero denseHam_inl_right _ (jointSol_inr x u))

/-- **`D = 0`**: every stage generator of the dense family is `i H` with `H` Hermitian
(`H = H_k + denseHam` on the hidden stages, `denseHam` on the idle and source stages). -/
theorem jointDenseFamily_skew (x : Promised M n (2 ^ μ)) (k : Fin (n + 2)) :
    ∃ H : Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ, H.IsHermitian ∧
      (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).data.matrix (x, k) = Complex.I • H := by
  show ∃ H : Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ, H.IsHermitian ∧
    denseGen M n μ s B dense x.1 k = Complex.I • H
  rw [denseGen, jointGen]
  split_ifs with hk
  · exact ⟨stageHam x.1 ⟨k, hk⟩ + denseHam M μ s B dense,
      (stageHam_isHermitian _ _).add denseHam_isHermitian, (smul_add _ _ _).symm⟩
  · exact ⟨denseHam M μ s B dense, denseHam_isHermitian, zero_add _⟩

/-- **The dense family is in the class** with `η = 1` and `g = √M ≤ ḡ` (the block rows and
columns have squared Euclidean norm `s 4^{-B} ≤ 1` for `s ≤ 4^B`, needed only when
`dense = true`; the class bounds row and column norms only, the operator-norm bound
`s ≤ 2^B` of `norm_denseHam_le` is not needed). -/
theorem jointDenseFamily_inClass (hsB : dense = true → s ≤ 4 ^ B) {gbar : ℝ}
    (hg : Real.sqrt M ≤ gbar) :
    (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).InClass 1 gbar := by
  refine ⟨fun x k => ?_, fun x k i => ?_, fun x k j => ?_, fun x => ?_⟩
  · obtain ⟨H, hH, he⟩ := jointDenseFamily_skew (B := B) (dense := dense) (hμ := hμ) (hμs := hμs)
      (hμB := hμB) (hT := hT) x k
    show TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator
      ((jointDenseFamily M n μ s B dense hμ hμs hμB T hT).data.matrix (x, k)))
    rw [he]
    exact accretive_I_smul hH
  · rw [one_pow]
    show ∑ j, ‖denseGen M n μ s B dense x.1 k i j‖ ^ 2 ≤ 1
    rcases i with a | t
    · simp only [denseGen_apply, denseHam_inl_left, mul_zero, add_zero]
      exact sum_norm_sq_jointGen_row x.1 k _
    · simp only [denseGen_apply, denseJointGen_inr_left, zero_add, norm_mul, Complex.norm_I,
        one_mul]
      rw [denseBlock_sum_norm_sq_row denseHam_inl_right denseHam_inr_inr]
      exact denseBlock_card_mul_norm_sq_le hsB
  · rw [one_pow]
    show ∑ i, ‖denseGen M n μ s B dense x.1 k i j‖ ^ 2 ≤ 1
    rcases j with a | t
    · simp only [denseGen_apply, denseHam_inl_right, mul_zero, add_zero]
      exact sum_norm_sq_jointGen_col x.1 k _
    · simp only [denseGen_apply, denseJointGen_inr_right, zero_add, norm_mul, Complex.norm_I,
        one_mul]
      rw [denseBlock_sum_norm_sq_col denseHam_inl_left denseHam_inr_inr]
      exact denseBlock_card_mul_norm_sq_le hsB
  · have hM : 1 ≤ M := (oddCand x).pos
    have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast hM)
    refine ⟨jointSol M n μ s T x, jointDenseSol_solves x, ?_, ?_⟩
    · rw [jointDenseFamily_T]
      intro h
      have h2 := norm_jointSol_T (s := s) hT x
      rw [h, norm_zero] at h2
      exact absurd h2 (div_pos two_pos hs).ne
    · rw [jointDenseFamily_mass hM, jointDenseFamily_T, norm_jointSol_T hT x, mul_div_assoc',
        le_div_iff₀ hs]
      nlinarith

/-- **Maximum row and column sparsity exactly `s`** (line 3899), at every input and stage: the
block rows and columns have `s` nonzero entries. -/
theorem jointDenseFamily_sparsityAttained (hd : dense = true) :
    SparsityAttained (jointDenseFamily M n μ s B dense hμ hμs hμB T hT) := by
  subst hd
  intro x k
  have hs : 0 < s := lt_of_lt_of_le (Nat.two_pow_pos μ) hμs
  simp only [jointDenseFamily_matrix]
  refine ⟨⟨Sum.inr ⟨0, hs⟩, denseBlock_card_row _ _ (fun a => ?_) (fun t' => ?_)⟩,
    ⟨Sum.inr ⟨0, hs⟩, denseBlock_card_col _ _ (fun a => ?_) (fun t' => ?_)⟩⟩ <;>
    simp [denseGen_apply, denseJointGen_inr_left, denseJointGen_inr_right, denseHam_inl_left,
      denseHam_inl_right, denseHam_inr_inr]

/-- **Exact dyadic entries** (line 3902): every sampled entry is `i · v/2^B`,
`-2^B < v ≤ 2^B`; the block entries are `i · 2^{-B}`. -/
theorem jointDenseFamily_dyadic (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (i j : JointIndex M μ s) :
    ∃ v : ℤ, -(2 : ℤ) ^ B < v ∧ v ≤ 2 ^ B ∧
      (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).data.matrix p i j =
        Complex.I * ((v : ℂ) / 2 ^ B) :=
  stageData_dyadic (hbound := jointDense_word_bound hμ hμB) (hdec := jointDense_decode hμ hμB)
    (hrow := denseGen_row_covers hμs) (hcol := denseGen_col_covers hμs) p i j

/-- **Without the block and at `B = μ` the stored words are the released ones**: the value table of
`jointDenseFamily … μ false` is that of `SparseLowerBounds.ODE.jointFamily` (core words
`2^0 w = w`, block and idle words `0`). -/
theorem jointDenseFamily_table_false :
    (jointDenseFamily M n μ s μ false hμ hμs le_rfl T hT).data.table =
      (jointFamily M n μ s hμ hμs T hT).data.table := by
  funext p a
  change ((stageWord n (jointDenseTable M μ s μ false) (jointDenseIdle M μ s false) p a : ℤ) :
      Word μ) = (if hk : (p.2 : ℕ) < n then
        (((jointTable M μ s).value (stageBits p.1 ⟨p.2, hk⟩) a : ℤ) : Word μ) else 0)
  unfold stageWord
  rcases a with ⟨i, j⟩
  split_ifs with hk
  · rw [BitTable.value, BitTable.value]
    congr 1
    by_cases hij : ∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t'
    · obtain ⟨t, t', rfl, rfl⟩ := hij
      rfl
    · rw [jointDenseTable_word_of_not_block hij, Nat.sub_self, pow_zero, one_mul]
      rfl
  · by_cases hij : ∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t'
    · obtain ⟨t, t', rfl, rfl⟩ := hij
      simp [jointDenseIdle]
    · rw [jointDenseIdle_of_not_block hij, Int.cast_zero]

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024 in
open OracleCircuit in
/-- **The dense family's access is a `hardCost` membership program** (lines 3852-3858, 3903):
`implementsOn_stageData` in the family form of `SparseLowerBounds.ODE.implementsOn_joint`; the
dense block costs no query. -/
theorem implementsOn_jointDense (ι : Type*) [Fintype ι] (l : Query) :
    EncodedOracle.ImplementsOn
      (fun x : Promised M n (2 ^ μ) =>
        (stageBoolean ι M n μ B (jointDenseTable M μ s B dense)).phase (membership x))
      ((jointDenseFamily M n μ s B dense hμ hμs hμB T hT).access ι l)
      (ancillaEmbed (Workspace ι (JointIndex M μ s) (Word B) (n + 2))) (hardCost l) :=
  implementsOn_stageData ι _ _ _ _ _ _ (jointDense_word_bound hμ hμB) (jointDense_decode hμ hμB)
    (denseGen_row_covers hμs) (denseGen_col_covers hμs) l

end

end ODELowerBoundExtensions.Padding
