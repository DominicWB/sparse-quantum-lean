import ODELowerBoundExtensions.Padding.JointDenseFacts

/-!
# Zero padding of the (densely padded) joint family

Manuscript line 3904 ("Known zero padding permits any
sufficiently large qubit register") and lines 4005-4006 ("Pad dimensions to a common known size
if desired"). The densely padded joint family `jointDenseFamily` (`Padding/JointDense`) is padded
by any finite known register `P`: index `JointIndex M μ s ⊕ P`, matrices `denseGen ⊕ 0_P`
(`LowerBoundRemarks.HamiltonianPadding.padMat`), word table `padTable (jointDenseTable) P`,
idle words `padWords (jointDenseIdle) P`, location lists `padLoc jointSlot jointLoc P` (padding
rows list the slots), initial state and sources extended by zero.

It is a `stageData` family, so its Boolean implementation is `implementsOn_stageData`
(`implementsOn_jointPad`), and it is the zero padding of `jointDenseFamily` in the sense of
`ZeroPad` (`jointPadFamily_zeroPad`); with `dense = false` its equation is the zero padding of the
equation of the released `jointFamily` itself (`jointPadFamily_zeroPad_joint`). `ZeroPad` concerns
equations, not encodings: for a general word length `B ≥ μ` the core words are re-encoded as
`2^{B-μ} w` (same decoded entries); at `B = μ` with `dense = false` the value table is that of
`jointFamily` on the original block and `0` elsewhere (`jointPadFamily_table_inl`,
`jointPadFamily_table_off`), exactly as `HamiltonianPadding.timePadData` keeps the original words.
The padded idle words `padWords W P` are the values of the released `padTable (idleTable W) P`
(`padWords_eq_value`). So
the class facts come from `Padding/ZeroPad`: `T`, `B = 2`, the class with `η = 1` and `g = √M`,
maximum sparsity exactly `s` (`jointPadFamily_inClass`, `jointPadFamily_sparsityAttained`).
Dimension `2Mm + s + |P|` (`card_jointPadIndex`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds SparseLowerBounds.ODE
  LowerBoundRemarks.HamiltonianPadding
open SparseLowerBounds.Hamiltonian (BitTable Word)
open SparseLowerBounds.Hamiltonian.HsInstance (inlOp)

/-- **Padded known words**: the words `W` on the original block, `0` on and next to the padding
block. -/
def padWords {N : Type*} (W : N × N → ℤ) (P : Type*) : (N ⊕ P) × (N ⊕ P) → ℤ := fun a =>
  match a with
  | (Sum.inl i, Sum.inl j) => W (i, j)
  | _ => 0

/-- **The padded idle words are the released padded table**: `padWords W P` is the value of
`LowerBoundRemarks.HamiltonianPadding.padTable (idleTable M μ W) P` under any bits. -/
theorem padWords_eq_value {N : Type*} {M μ : ℕ} (W : N × N → ℤ) (P : Type*)
    (y : Fin M × Fin (2 ^ μ) → Bool) :
    padWords W P = (padTable (idleTable M μ W) P).value y := by
  funext a
  rcases a with ⟨i | p, j | q⟩ <;> rfl

/-- On the original block the padded stage word is the original stage word. -/
theorem stageWord_padTable_inl_inl {N : Type*} [Fintype N] [DecidableEq N] {P : Type*}
    [Fintype P] [DecidableEq P] {M μ : ℕ} (n : ℕ) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N))
    (W : N × N → ℤ) (p : Promised M n (2 ^ μ) × Fin (n + 2)) (i j : N) :
    stageWord n (padTable T P) (padWords W P) p (Sum.inl i, Sum.inl j) =
      stageWord n T W p (i, j) := by
  unfold stageWord
  split_ifs <;> rfl

/-- Off the original block the padded stage word is `0`. -/
theorem stageWord_padTable_off {N : Type*} [Fintype N] [DecidableEq N] {P : Type*}
    [Fintype P] [DecidableEq P] {M μ : ℕ} (n : ℕ) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N))
    (W : N × N → ℤ) (p : Promised M n (2 ^ μ) × Fin (n + 2)) (a : (N ⊕ P) × (N ⊕ P))
    (ha : ∀ i j, a ≠ (Sum.inl i, Sum.inl j)) :
    stageWord n (padTable T P) (padWords W P) p a = 0 := by
  rcases a with ⟨i | q, j | q'⟩
  · exact absurd rfl (ha i j)
  all_goals (unfold stageWord; split_ifs <;> rfl)

variable {M n μ s B : ℕ} {dense : Bool} {P : Type*} [Fintype P] [DecidableEq P]

/-- Every padded stage word lies in `(-2^B, 2^B]`. -/
theorem jointPad_word_bound (hμ : 1 ≤ μ) (hμB : μ ≤ B)
    (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (a : (JointIndex M μ s ⊕ P) × (JointIndex M μ s ⊕ P)) :
    -(2 : ℤ) ^ B < stageWord n (padTable (jointDenseTable M μ s B dense) P)
        (padWords (jointDenseIdle M μ s dense) P) p a ∧
      stageWord n (padTable (jointDenseTable M μ s B dense) P)
        (padWords (jointDenseIdle M μ s dense) P) p a ≤ 2 ^ B := by
  rcases a with ⟨i | q, j | q'⟩
  · rw [stageWord_padTable_inl_inl]
    exact jointDense_word_bound hμ hμB p (i, j)
  all_goals
    rw [stageWord_padTable_off _ _ _ _ _ (fun _ _ h => by cases h)]
    exact ⟨by simp, by positivity⟩

/-- The padded words decode to the padded generator `denseGen ⊕ 0_P`. -/
theorem jointPad_decode (hμ : 1 ≤ μ) (hμB : μ ≤ B) (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (i j : JointIndex M μ s ⊕ P) :
    Complex.I * ((stageWord n (padTable (jointDenseTable M μ s B dense) P)
        (padWords (jointDenseIdle M μ s dense) P) p (i, j) : ℂ) / 2 ^ B) =
      padMat P (denseGen M n μ s B dense p.1.1 p.2) i j := by
  rcases i with i | q <;> rcases j with j | q'
  · rw [stageWord_padTable_inl_inl]
    exact jointDense_decode hμ hμB p i j
  all_goals
    rw [stageWord_padTable_off _ _ _ _ _ (fun _ _ h => by cases h)]
    simp [padMat]

omit [Fintype P] [DecidableEq P] in
/-- Row cover of the padded generator by the padded location lists. -/
theorem jointPad_row_covers (hμs : 2 ^ μ ≤ s) (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (i j : JointIndex M μ s ⊕ P) (h : padMat P (denseGen M n μ s B dense p.1.1 p.2) i j ≠ 0) :
    j ∈ Set.range (padLoc (jointSlot M μ s) (jointLoc M μ s) P i) := by
  exact padLoc_row (H := fun p : Promised M n (2 ^ μ) × Fin (n + 2) =>
    denseGen M n μ s B dense p.1.1 p.2) (fun p i j h => denseGen_row_covers hμs p i j h) P p i j h

omit [Fintype P] [DecidableEq P] in
/-- Column cover of the padded generator by the padded location lists. -/
theorem jointPad_col_covers (hμs : 2 ^ μ ≤ s) (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (i j : JointIndex M μ s ⊕ P) (h : padMat P (denseGen M n μ s B dense p.1.1 p.2) i j ≠ 0) :
    i ∈ Set.range (padLoc (jointSlot M μ s) (jointLoc M μ s) P j) := by
  exact padLoc_col (H := fun p : Promised M n (2 ^ μ) × Fin (n + 2) =>
    denseGen M n μ s B dense p.1.1 p.2) (fun p i j h => denseGen_col_covers hμs p i j h) P p i j h

variable (M n μ s B dense P) in
/-- **The zero-padded dense joint data**: `stageData` on `JointIndex M μ s ⊕ P` with the padded
table, the padded idle words, the padded location lists and the matrices `denseGen ⊕ 0_P`. -/
def jointPadData (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) :
    Data (Promised M n (2 ^ μ) × Fin (n + 2)) (JointIndex M μ s ⊕ P) (Word B) s :=
  stageData M n μ s B (lt_of_lt_of_le (Nat.two_pow_pos μ) hμs)
    ((jointSlot M μ s).trans Function.Embedding.inl) (padLoc (jointSlot M μ s) (jointLoc M μ s) P)
    (padTable (jointDenseTable M μ s B dense) P) (padWords (jointDenseIdle M μ s dense) P)
    (fun p => padMat P (denseGen M n μ s B dense p.1.1 p.2)) (jointPad_word_bound hμ hμB)
    (jointPad_decode hμ hμB) (jointPad_row_covers hμs) (jointPad_col_covers hμs)

variable (M n μ s B dense P) in
/-- **The zero-padded dense joint family** (lines 3904, 4005-4006): `jointDenseFamily` padded by
the known register `P`; initial state and sources extended by zero. -/
def jointPadFamily (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (hμB : μ ≤ B) (T : ℝ)
    (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) :
    Family (Promised M n (2 ^ μ)) (JointIndex M μ s ⊕ P) (Word B) (n + 2) s where
  data := jointPadData M n μ s B dense P hμ hμs hμB
  len := (jointFamily M n μ s hμ hμs T hT).len
  len_nonneg := (jointFamily M n μ s hμ hμs T hT).len_nonneg
  src k := inlOp (JointIndex M μ s) P ((jointFamily M n μ s hμ hμs T hT).src k)
  init := inlOp (JointIndex M μ s) P (jointFamily M n μ s hμ hμs T hT).init

variable {hμ : 1 ≤ μ} {hμs : 2 ^ μ ≤ s} {hμB : μ ≤ B} {T : ℝ}
  {hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T}

/-- The sampled matrices of the padded family are `denseGen ⊕ 0_P`. -/
@[simp] theorem jointPadFamily_matrix (p : Promised M n (2 ^ μ) × Fin (n + 2)) :
    (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).data.matrix p =
      padMat P (denseGen M n μ s B dense p.1.1 p.2) :=
  rfl

/-- **The padded family is the zero padding of the dense family.** -/
theorem jointPadFamily_zeroPad :
    ZeroPad (jointPadFamily M n μ s B dense P hμ hμs hμB T hT)
      (jointDenseFamily M n μ s B dense hμ hμs hμB T hT) := by
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl⟩

/-- **Without the dense block, the padded family is the zero padding of the joint family**
`jointFamily` of `odel:thm:joint` itself, as equations (`ZeroPad`: matrices `jointGen ⊕ 0_P`,
sources and initial state `⊕ 0`); for the words see `jointPadFamily_table_inl`. -/
theorem jointPadFamily_zeroPad_joint :
    ZeroPad (jointPadFamily M n μ s B false P hμ hμs hμB T hT)
      (jointFamily M n μ s hμ hμs T hT) := by
  exact ⟨fun y => congrArg (padMat P) (denseGen_false y.1.1 y.2), fun _ => rfl, fun _ => rfl, rfl⟩

/-- `T` is unchanged. -/
theorem jointPadFamily_T : (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).T = T := by
  exact jointPadFamily_zeroPad.T_eq.trans jointDenseFamily_T

/-- **The padded solution** `x(t) ⊕ 0` solves every instance. -/
theorem jointPadSol_solves (x : Promised M n (2 ^ μ)) :
    (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).Solves x
      (fun t => inlOp (JointIndex M μ s) P (jointSol M n μ s T x t)) := by
  exact jointPadFamily_zeroPad.solves (jointDenseSol_solves x)

/-- **The padded family is in the class** with `η = 1` and `g = √M ≤ ḡ` (`s ≤ 4^B`, i.e. block
rows and columns of squared norm `s 4^{-B} ≤ 1`, is needed only with the dense block). -/
theorem jointPadFamily_inClass (hsB : dense = true → s ≤ 4 ^ B) {gbar : ℝ}
    (hg : Real.sqrt M ≤ gbar) :
    (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).InClass 1 gbar := by
  exact jointPadFamily_zeroPad.inClass (jointDenseFamily_inClass hsB hg)

/-- **Maximum row and column sparsity exactly `s`**, at every input and stage. -/
theorem jointPadFamily_sparsityAttained (hd : dense = true) :
    SparsityAttained (jointPadFamily M n μ s B dense P hμ hμs hμB T hT) := by
  exact jointPadFamily_zeroPad.sparsityAttained (jointDenseFamily_sparsityAttained hd)

/-- **`D = 0`**: every stage generator is `i H` with `H` Hermitian. -/
theorem jointPadFamily_skew (x : Promised M n (2 ^ μ)) (k : Fin (n + 2)) :
    ∃ H : Matrix (JointIndex M μ s ⊕ P) (JointIndex M μ s ⊕ P) ℂ, H.IsHermitian ∧
      (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).data.matrix (x, k) = Complex.I • H := by
  obtain ⟨H, hH, he⟩ := jointDenseFamily_skew (M := M) (n := n) (μ := μ) (s := s) (B := B)
    (dense := dense) (hμ := hμ) (hμs := hμs) (hμB := hμB) (T := T) (hT := hT) x k
  refine ⟨padMat P H, hH.fromBlocks (by simp) (Matrix.isHermitian_zero), ?_⟩
  rw [jointPadFamily_matrix, ← padMat_smul, ← he]
  rfl

/-- **Exact dyadic entries**: every sampled entry is `i · v/2^B`, `-2^B < v ≤ 2^B`. -/
theorem jointPadFamily_dyadic (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (i j : JointIndex M μ s ⊕ P) :
    ∃ v : ℤ, -(2 : ℤ) ^ B < v ∧ v ≤ 2 ^ B ∧
      (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).data.matrix p i j =
        Complex.I * ((v : ℂ) / 2 ^ B) :=
  stageData_dyadic (hbound := jointPad_word_bound hμ hμB) (hdec := jointPad_decode hμ hμB)
    (hrow := jointPad_row_covers hμs) (hcol := jointPad_col_covers hμs) p i j

/-- **At `B = μ` without the block the padded words are the released ones on the original block**: the
value table of `jointPadFamily … μ false P` at `(inl i, inl j)` is that of `jointFamily` at
`(i, j)` (the analogue of `HamiltonianPadding.padTable_value_inl_inl`). -/
theorem jointPadFamily_table_inl (p : Promised M n (2 ^ μ) × Fin (n + 2)) (i j : JointIndex M μ s) :
    (jointPadFamily M n μ s μ false P hμ hμs le_rfl T hT).data.table p (Sum.inl i, Sum.inl j) =
      (jointFamily M n μ s hμ hμs T hT).data.table p (i, j) := by
  have h := congrFun (congrFun (jointDenseFamily_table_false (M := M) (n := n) (μ := μ) (s := s)
    (hμ := hμ) (hμs := hμs) (T := T) (hT := hT)) p) (i, j)
  refine Eq.trans ?_ h
  show ((stageWord n _ _ p (Sum.inl i, Sum.inl j) : ℤ) : Word μ) =
    ((stageWord n _ _ p (i, j) : ℤ) : Word μ)
  rw [stageWord_padTable_inl_inl]

/-- **Off the original block every padded word is `0`**, for every word length and flag. -/
theorem jointPadFamily_table_off (p : Promised M n (2 ^ μ) × Fin (n + 2))
    (a : (JointIndex M μ s ⊕ P) × (JointIndex M μ s ⊕ P))
    (ha : ∀ i j, a ≠ (Sum.inl i, Sum.inl j)) :
    (jointPadFamily M n μ s B dense P hμ hμs hμB T hT).data.table p a = 0 := by
  show ((stageWord n _ _ p a : ℤ) : Word B) = 0
  rw [stageWord_padTable_off _ _ _ _ _ ha, Int.cast_zero]

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024 in
open OracleCircuit in
/-- **The padded family's access is a `hardCost` membership program** (lines 3852-3858, 3904):
`implementsOn_stageData` in the family form of `SparseLowerBounds.ODE.implementsOn_joint`; the
dense block and the padding cost no query. -/
theorem implementsOn_jointPad (ι : Type*) [Fintype ι] (l : Query) :
    EncodedOracle.ImplementsOn
      (fun x : Promised M n (2 ^ μ) =>
        (stageBoolean ι M n μ B (padTable (jointDenseTable M μ s B dense) P)).phase (membership x))
      ((jointPadFamily M n μ s B dense P hμ hμs hμB T hT).access ι l)
      (ancillaEmbed (Workspace ι (JointIndex M μ s ⊕ P) (Word B) (n + 2))) (hardCost l) := by
  exact implementsOn_stageData ι _ _ _ _ _ _ (jointPad_word_bound hμ hμB) (jointPad_decode hμ hμB)
    (jointPad_row_covers hμs) (jointPad_col_covers hμs) l

omit [DecidableEq P] in
/-- The dimension of the padded family: `|JointIndex ⊕ P| = 2 M 2^μ + s + |P|`. -/
theorem card_jointPadIndex :
    Fintype.card (JointIndex M μ s ⊕ P) = M * (2 * 2 ^ μ) + s + Fintype.card P := by
  rw [Fintype.card_sum, card_jointIndex]

end

end ODELowerBoundExtensions.Padding
