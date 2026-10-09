import ODELowerBoundExtensions.Padding.StageCompile
import ODELowerBoundExtensions.Padding.Helpers.JointDense.Block
import ODELowerBoundExtensions.Padding.Helpers.JointDense.Words

/-!
# Dense padding of the joint family to maximum sparsity exactly `s`

Manuscript: end of the proof of Theorem `odel:thm:joint`,
lines 3899-3903:

> If maximum sparsity exactly `s` is wanted, append an unoccupied known block with Hamiltonian
> `2^{-⌈log₂ s⌉} 1 1ᵀ` of size `s × s`. Its norm is at most one and its entries are dyadic. It
> requires no membership queries and leaves the solution unchanged.

**Where the block lives.** The index of the joint family is already
`JointIndex M μ s = (Fin M × Bool × Fin 2^μ) ⊕ Fin s`: the manuscript's `2Mm` core indices
followed by an `s`-element block that the released package adds so that the `s` location slots embed
(`SparseLowerBounds.ODE.jointSlot`), on which the joint generator vanishes. That block is the
manuscript's appended unoccupied `s × s` block (dimension `2Mm + s`), and its location lists
(`jointLoc (inr t) = jointSlot`) list exactly the block. The dense padding puts the Hamiltonian
`denseHam = 2^{-B} 1 1ᵀ` on it, at **every** stage (hidden, idle and source), with generator
`denseGen = jointGen + i · denseHam` (`D = 0`). A flag `dense : Bool` switches the block off:
with `dense = false` the generator is `jointGen` itself (`denseGen_false`), so the same
construction, padded by `P` (`Padding/JointPad`), is also the zero padding of the equation of
`jointFamily`; at `B = μ` it stores the released words verbatim (`jointDenseFamily_table_false`).

**Words.** The manuscript's `2^{-⌈log₂ s⌉}` is `2^{-(μ+1)}` when `s` is not a power of two
(`μ = jointMu s = ⌊log₂ s⌋`), which the words `Word μ` of the joint family cannot store. The
padded data therefore use `B ≥ μ` word bits, the core words of `jointTable` multiplied by
`2^{B-μ}` (`jointDenseTable`, same decoded entries) and the block word `1` (`jointDenseIdle` on
the idle and source stages), so the block entries are `i · 2^{-B}`. At `B = ⌈log₂ s⌉ =
Hamiltonian.padExp s` (the parameters of `Padding/JointTheorem`) the block is the released
`Hamiltonian.padBlock s` (line 2480; `denseHam_padExp`), whose facts `norm_padBlock_le`,
`sum_sq_padBlock_le`, `card_padBlock_row` are the case `B = padExp s` of ours.

**Class and instance facts** (the class with `η = 1`, `D = 0`, maximum sparsity exactly `s`,
block norm at most one, dyadic entries, the unchanged solution, the `hardCost` access) are in
`Padding/JointDenseFacts`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds SparseLowerBounds.ODE
open SparseLowerBounds.Hamiltonian (BitTable Word)

/-- **The dense block** `2^{-B} 1 1ᵀ` on the `Fin s` block of `JointIndex M μ s`, zero
elsewhere (line 3900); with `dense = false` the block is zero (no dense padding). -/
def denseHam (M μ s B : ℕ) (dense : Bool) : Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ :=
  Matrix.of fun i j => match i, j with
    | Sum.inr _, Sum.inr _ => if dense then ((2 : ℂ) ^ B)⁻¹ else 0
    | _, _ => 0

/-- **The densely padded generator** of stage `k`: `jointGen j k + i · denseHam` (the joint
generator `jointGen j k` itself when `dense = false`). -/
def denseGen (M n μ s B : ℕ) (dense : Bool) (j : Positions M n (2 ^ μ)) (k : Fin (n + 2)) :
    Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ :=
  jointGen j k + Complex.I • denseHam M μ s B dense

/-- **The dense stage table**: the bits of `jointTable`, its words multiplied by `2^{B-μ}` on
the core, and the known word `1` (entry `i · 2^{-B}`) on the `Fin s` block (`0` when
`dense = false`). -/
def jointDenseTable (M μ s B : ℕ) (dense : Bool) :
    BitTable (Fin M × Fin (2 ^ μ)) (JointIndex M μ s × JointIndex M μ s) where
  addr := (jointTable M μ s).addr
  word ad bit := match ad with
    | (Sum.inr _, Sum.inr _) => if dense then 1 else 0
    | _ => 2 ^ (B - μ) * (jointTable M μ s).word ad bit

/-- **The known words of the idle and source stages**: `1` on the `Fin s` block (`0` when
`dense = false`), `0` elsewhere (the joint generator vanishes on these stages). -/
def jointDenseIdle (M μ s : ℕ) (dense : Bool) : JointIndex M μ s × JointIndex M μ s → ℤ :=
  fun ad => match ad with
  | (Sum.inr _, Sum.inr _) => if dense then 1 else 0
  | _ => 0

variable {M n μ s B : ℕ} {dense : Bool}

/-- A core row of the dense block vanishes. -/
theorem denseHam_inl_left (a : Fin M × Bool × Fin (2 ^ μ)) (j : JointIndex M μ s) :
    denseHam M μ s B dense (Sum.inl a) j = 0 := by
  cases j <;> rfl

/-- A core column of the dense block vanishes. -/
theorem denseHam_inl_right (i : JointIndex M μ s) (a : Fin M × Bool × Fin (2 ^ μ)) :
    denseHam M μ s B dense i (Sum.inl a) = 0 := by
  cases i <;> rfl

/-- An entry of the dense block proper. -/
theorem denseHam_inr_inr (t t' : Fin s) :
    denseHam M μ s B dense (Sum.inr t) (Sum.inr t') = if dense then ((2 : ℂ) ^ B)⁻¹ else 0 :=
  rfl

/-- Entries of the densely padded generator. -/
theorem denseGen_apply (j : Positions M n (2 ^ μ)) (k : Fin (n + 2))
    (i i' : JointIndex M μ s) :
    denseGen M n μ s B dense j k i i' =
      jointGen j k i i' + Complex.I * denseHam M μ s B dense i i' :=
  rfl

/-- Without the block the dense matrix is zero. -/
theorem denseHam_false : denseHam M μ s B false = 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> rfl

/-- **Without the dense block the generator is the joint generator**: `denseGen … false =
jointGen`. -/
theorem denseGen_false (j : Positions M n (2 ^ μ)) (k : Fin (n + 2)) :
    denseGen M n μ s B false j k = jointGen j k := by
  rw [denseGen, denseHam_false, smul_zero, add_zero]

/-- Off the block the dense matrix vanishes. -/
theorem denseHam_of_not_block {i j : JointIndex M μ s}
    (h : ¬∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t') : denseHam M μ s B dense i j = 0 := by
  rcases i with i | t
  · exact denseHam_inl_left i j
  · rcases j with j | t'
    · exact denseHam_inl_right _ j
    · exact absurd ⟨t, t', rfl, rfl⟩ h

/-- Off the block the dense table stores the core words times `2^{B-μ}`. -/
theorem jointDenseTable_word_of_not_block {i j : JointIndex M μ s}
    (h : ¬∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t') (bit : Bool) :
    (jointDenseTable M μ s B dense).word (i, j) bit =
      2 ^ (B - μ) * (jointTable M μ s).word (i, j) bit := by
  rcases i with i | t
  · cases j <;> rfl
  · rcases j with j | t'
    · rfl
    · exact absurd ⟨t, t', rfl, rfl⟩ h

/-- Off the block the idle words vanish. -/
theorem jointDenseIdle_of_not_block {i j : JointIndex M μ s}
    (h : ¬∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t') :
    jointDenseIdle M μ s dense (i, j) = 0 := by
  rcases i with i | t
  · cases j <;> rfl
  · rcases j with j | t'
    · rfl
    · exact absurd ⟨t, t', rfl, rfl⟩ h

/-- Every word of the dense table lies in `(-2^B, 2^B]`. -/
theorem jointDenseTable_word_mem (hμ : 1 ≤ μ) (hμB : μ ≤ B)
    (ad : JointIndex M μ s × JointIndex M μ s) (bit : Bool) :
    -(2 : ℤ) ^ B < (jointDenseTable M μ s B dense).word ad bit ∧
      (jointDenseTable M μ s B dense).word ad bit ≤ 2 ^ B := by
  have hw := jointTable_word_mem (M := M) (s := s) hμ ad bit
  rcases ad with ⟨i | t, j | t'⟩ <;>
    first | exact denseWord_ite_mem B dense | exact denseWord_scale_mem hμB hw.1 hw.2

/-- Every dense stage word lies in `(-2^B, 2^B]`. -/
theorem jointDense_word_bound (hμ : 1 ≤ μ) (hμB : μ ≤ B)
    (p : Promised M n (2 ^ μ) × Fin (n + 2)) (a : JointIndex M μ s × JointIndex M μ s) :
    -(2 : ℤ) ^ B < stageWord n (jointDenseTable M μ s B dense) (jointDenseIdle M μ s dense) p a ∧
      stageWord n (jointDenseTable M μ s B dense) (jointDenseIdle M μ s dense) p a ≤ 2 ^ B := by
  have h0 : -(2 : ℤ) ^ B < 0 ∧ (0 : ℤ) ≤ 2 ^ B := ⟨by simp, by positivity⟩
  unfold stageWord
  split_ifs with hk
  · rw [BitTable.value]
    exact jointDenseTable_word_mem hμ hμB a _
  · rcases a with ⟨i | t, j | t'⟩ <;> first | exact denseWord_ite_mem B dense | exact h0

/-- **The dense words decode to the densely padded generator**: `i · stageWord/2^B =
denseGen`. -/
theorem jointDense_decode (hμ : 1 ≤ μ) (hμB : μ ≤ B)
    (p : Promised M n (2 ^ μ) × Fin (n + 2)) (i j : JointIndex M μ s) :
    Complex.I * ((stageWord n (jointDenseTable M μ s B dense) (jointDenseIdle M μ s dense) p
      (i, j) : ℂ) / 2 ^ B) = denseGen M n μ s B dense p.1.1 p.2 i j := by
  rw [denseGen_apply]
  unfold stageWord
  by_cases hij : ∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t'
  · obtain ⟨t, t', rfl, rfl⟩ := hij
    rw [denseJointGen_inr_left, denseHam_inr_inr]
    have hw : ∀ bit, (jointDenseTable M μ s B dense).word (Sum.inr t, Sum.inr t') bit =
        if dense then 1 else 0 := fun _ => rfl
    have hi : jointDenseIdle M μ s dense (Sum.inr t, Sum.inr t') = if dense then 1 else 0 := rfl
    by_cases hk : (p.2 : ℕ) < n
    · rw [dif_pos hk, BitTable.value, hw]
      cases dense <;> simp
    · rw [dif_neg hk, hi]
      cases dense <;> simp
  · rw [denseHam_of_not_block hij, mul_zero, add_zero]
    split_ifs with hk
    · have hw := jointTable_word_mem (M := M) (s := s) hμ (i, j)
        ((jointTable M μ s).bit (stageBits p.1 ⟨p.2, hk⟩) (i, j))
      have hdec := wordDecode_stage (s := s) hμ p.1 ⟨p.2, hk⟩ i j
      rw [BitTable.value, Hamiltonian.wordDecode_intCast _ hw.1 hw.2] at hdec
      rw [jointGen, dif_pos hk, Matrix.smul_apply, smul_eq_mul, ← hdec, BitTable.value,
        jointDenseTable_word_of_not_block hij, denseWord_scale_decode hμB]
      rfl
    · rw [jointGen, dif_neg hk, jointDenseIdle_of_not_block hij]
      simp

/-- Row cover of the densely padded generator by the joint location lists. -/
theorem denseGen_row_covers (hμs : 2 ^ μ ≤ s) (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (i j : JointIndex M μ s) (h : denseGen M n μ s B dense p.1.1 p.2 i j ≠ 0) :
    j ∈ Set.range (jointLoc M μ s i) := by
  by_cases hij : ∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t'
  · obtain ⟨t, t', rfl, rfl⟩ := hij
    exact ⟨t', rfl⟩
  · rw [denseGen_apply, denseHam_of_not_block hij, mul_zero, add_zero] at h
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (jointGen_row_covers hμs _ _ _ _ h)
    exact ⟨k, hk⟩

/-- Column cover of the densely padded generator by the joint location lists. -/
theorem denseGen_col_covers (hμs : 2 ^ μ ≤ s) (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (i j : JointIndex M μ s) (h : denseGen M n μ s B dense p.1.1 p.2 i j ≠ 0) :
    i ∈ Set.range (jointLoc M μ s j) := by
  by_cases hij : ∃ t t' : Fin s, i = Sum.inr t ∧ j = Sum.inr t'
  · obtain ⟨t, t', rfl, rfl⟩ := hij
    exact ⟨t, rfl⟩
  · rw [denseGen_apply, denseHam_of_not_block hij, mul_zero, add_zero] at h
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (jointGen_col_covers hμs _ _ _ _ h)
    exact ⟨k, hk⟩

variable (M n μ s B dense) in
/-- **The densely padded sampled-time data** (lines 3899-3903): `stageData` with the dense
table, the joint locators and the matrices `denseGen`, words `Word B`. -/
def jointDenseData (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) :
    Data (Promised M n (2 ^ μ) × Fin (n + 2)) (JointIndex M μ s) (Word B) s :=
  stageData M n μ s B (lt_of_lt_of_le (Nat.two_pow_pos μ) hμs) (jointSlot M μ s)
    (jointLoc M μ s) (jointDenseTable M μ s B dense) (jointDenseIdle M μ s dense)
    (fun p => denseGen M n μ s B dense p.1.1 p.2) (jointDense_word_bound hμ hμB)
    (jointDense_decode hμ hμB) (denseGen_row_covers hμs) (denseGen_col_covers hμs)

variable (M n μ s B dense) in
/-- **The densely padded joint family** (lines 3899-3903): the joint family of
`odel:thm:joint` (same durations, sources and initial state as `jointFamily`) with the dense
block added to every stage generator. -/
def jointDenseFamily (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) (T : ℝ)
    (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) :
    Family (Promised M n (2 ^ μ)) (JointIndex M μ s) (Word B) (n + 2) s where
  data := jointDenseData M n μ s B dense hμ hμs hμB
  len := (jointFamily M n μ s hμ hμs T hT).len
  len_nonneg := (jointFamily M n μ s hμ hμs T hT).len_nonneg
  src := (jointFamily M n μ s hμ hμs T hT).src
  init := (jointFamily M n μ s hμ hμs T hT).init

variable {hμ : 1 ≤ μ} {hμs : 2 ^ μ ≤ s} {hμB : μ ≤ B} {T : ℝ}
  {hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T}

/-- The sampled matrices of the dense family are `denseGen`. -/
@[simp] theorem jointDenseFamily_matrix (p : Promised M n (2 ^ μ) × Fin (n + 2)) :
    (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).data.matrix p =
      denseGen M n μ s B dense p.1.1 p.2 :=
  rfl

/-- `T` is unchanged. -/
theorem jointDenseFamily_T : (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).T = T := by
  have h := jointFamily_T (M := M) (n := n) (μ := μ) (s := s) (hμ := hμ) (hμs := hμs) (T := T)
    (hT := hT)
  rw [Family.T_eq_sum] at h ⊢
  exact h

/-- `B = 2` is unchanged (`M ≥ 1`). -/
theorem jointDenseFamily_mass (hM : 1 ≤ M) :
    (jointDenseFamily M n μ s B dense hμ hμs hμB T hT).mass = 2 := by
  have h := jointFamily_mass (n := n) (μ := μ) (s := s) (hμ := hμ) (hμs := hμs) (T := T)
    (hT := hT) hM
  unfold Family.mass at h ⊢
  exact h

end

end ODELowerBoundExtensions.Padding
