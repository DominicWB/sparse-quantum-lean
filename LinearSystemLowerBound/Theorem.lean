import LinearSystemLowerBound.Parameters
import LinearSystemLowerBound.Hard.Data
import LinearSystemLowerBound.Weight.Bias

/-!
# Theorem `qlsl:thm:main`: the linear-system query lower bound

For `κ ≥ 32`, an integer `s ≥ 5` and `0 < ε ≤ 1/64` the hard family has
`n = npar κ ε` marked positions in `Fin m`, `m = mpar s`, and `2n` clock values
(`T = 2n - 1` transitions); its matrices are the real symmetric Hermitian dilations
`A_X = family κ ε s X` with right-hand side `b = rhsVec κ ε s` and normalised solutions
`x_A = target κ ε s X = A_X⁻¹ b / ‖A_X⁻¹ b‖`.

* `family_promise`: `‖A_X‖ ≤ 1`, `A_X` invertible, `‖A_X⁻¹‖ ≤ κ`;
  `family_real_symm`: real symmetric; `family_sparse`: at most `m + 1 ≤ s` possible nonzero
  positions per row and column, independent of `X`; `family_dimension`:
  `s κ ln(1/ε)/32 < N < s κ ln(1/ε)`.
* `exists_access`: native sparse data with these matrices, input-independent location
  oracles and an entry-determined value oracle exist (`hardData`).
* `target_correlation`: the signed decoder correlation of `x_A` is the answer probability
  `p = r^{2n} / (1 + r^{2n})`.
* `lower_bound_of_bias`: the counting step; a protocol over admissible labels whose signed
  decoder correlation is at least `(2/3)(p - 2ε)` on every input makes more than
  `κ √s ln(1/ε) / 1536` weighted native queries.
* `lower_bound_sharp`: every adaptive protocol (`SparseLinearSystems.Protocol.Tree`) over
  admissible oracle labels that, on every input, heralds success with probability at least
  `2/3` and outputs, conditional on success, a state whose reduced state on the output
  register is within trace distance `ε` of `|x_A⟩⟨x_A|`, makes in the worst case more than
  `κ √s ln(1/ε) / 1536` native queries.  The output space is identified with the output
  register and an arbitrary finite garbage register by a fixed isometry, and the reduced
  state is the partial trace over the garbage register.
* `lower_bound`: the paper's conservative constant `κ √s ln(1/ε) / 3072`.
* `lower_bound_sharp_clean`: the case of a clean output (a one-point garbage register).
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder
open SparseHamiltonian SparseLinearSystems.Protocol LinearSystemLowerBound.Hard
  LinearSystemLowerBound.Params LinearSystemLowerBound.Native

instance mpar_neZero (s : ℕ) : NeZero (mpar s) := ⟨pow_ne_zero _ two_ne_zero⟩

/-- Inputs of the hard family: the marked positions. -/
abbrev Inp (κ ε : ℝ) (s : ℕ) := Fin (npar κ ε) → Fin (mpar s)

/-- Indices of the hard family: sector, clock value (`2n` values), gadget position. -/
abbrev Ind (κ ε : ℝ) (s : ℕ) := Idx (2 * npar κ ε - 1) (mpar s)

/-- **The hard matrices** `A_X`. -/
def family (κ ε : ℝ) (s : ℕ) (x : Inp κ ε s) : Matrix (Ind κ ε s) (Ind κ ε s) ℂ :=
  hardMatrix (rpar κ) x

/-- The input-independent right-hand side `b = |false, 0, 0_L⟩`. -/
def rhsVec (κ ε : ℝ) (s : ℕ) : EuclideanSpace ℂ (Ind κ ε s) := rhs

/-- The normalised solution `x_A = A⁻¹ b / ‖A⁻¹ b‖`. -/
def target (κ ε : ℝ) (s : ℕ) (x : Inp κ ε s) : EuclideanSpace ℂ (Ind κ ε s) :=
  ODEStateNormalization.unitDirection
    (Ring.inverse (SparseStateOverlap.matrixOperator (family κ ε s x)) (rhsVec κ ε s))

/-- The decoder observable on the answer region. -/
def decoderOf (κ ε : ℝ) (s : ℕ) :
    EuclideanSpace ℂ (Ind κ ε s) →L[ℂ] EuclideanSpace ℂ (Ind κ ε s) :=
  decoder (npar κ ε) (2 * npar κ ε - 1) (mpar s)

/-! ### Properties of the family -/

theorem clock_count (κ ε : ℝ) (hκ : 32 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    2 * npar κ ε - 1 + 1 = 2 * npar κ ε := by
  have := npar_pos κ ε hκ hε hε1
  omega

/-- **The promise**: `‖A_X‖ ≤ 1`, `A_X` invertible and `‖A_X⁻¹‖ ≤ κ`. -/
theorem family_promise (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (x : Inp κ ε s) :
    ‖SparseStateOverlap.matrixOperator (family κ ε s x)‖ ≤ 1 ∧
      IsUnit (SparseStateOverlap.matrixOperator (family κ ε s x)) ∧
      ‖Ring.inverse (SparseStateOverlap.matrixOperator (family κ ε s x))‖ ≤ κ := by
  have hr0 := rpar_nonneg κ hκ
  have hr1 := rpar_lt_one κ hκ
  refine ⟨(hard_opNorm_le (rpar κ) hr0 x).trans (by linarith), hard_isUnit _ hr0 hr1 x,
    (hard_inverse_norm_le _ hr0 hr1 x).trans (two_div_one_sub_rpar κ hκ)⟩

/-- The hard matrices are real symmetric. -/
theorem family_real_symm (κ ε : ℝ) (s : ℕ) (x : Inp κ ε s) (i j : Ind κ ε s) :
    family κ ε s x i j = family κ ε s x j i ∧ (family κ ε s x i j).im = 0 :=
  ⟨hard_symm _ x i j, hard_im _ x i j⟩

/-- The hard matrices are indefinite. -/
theorem family_indefinite (κ ε : ℝ) (s : ℕ) (x : Inp κ ε s) :
    ∃ v w : EuclideanSpace ℂ (Ind κ ε s),
      0 < (⟪v, SparseStateOverlap.matrixOperator (family κ ε s x) v⟫_ℂ).re ∧
      (⟪w, SparseStateOverlap.matrixOperator (family κ ε s x) w⟫_ℂ).re < 0 := by
  set A := family κ ε s x
  set a : Ind κ ε s := (false, 0, 0)
  set b : Ind κ ε s := (true, 0, 0)
  have hne : a ≠ b := by simp [a, b]
  have hab : A a b = 1 / 2 := by simp [A, a, b, family, hardMatrix, swapM, dil, clock]
  have hba : A b a = 1 / 2 := by simp [A, a, b, family, hardMatrix, swapM, dil, clock]
  have haa : A a a = 0 := by simp [A, a, family, hardMatrix, swapM, dil]
  have hbb : A b b = 0 := by simp [A, b, family, hardMatrix, swapM, dil]
  have hform : ∀ σ : ℝ, (⟪EuclideanSpace.single a (1 : ℂ) + EuclideanSpace.single b (σ : ℂ),
      SparseStateOverlap.matrixOperator A
        (EuclideanSpace.single a (1 : ℂ) + EuclideanSpace.single b (σ : ℂ))⟫_ℂ).re = σ := by
    intro σ
    rw [inner_add_left, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
    simp only [SparseStateOverlap.matrixOperator_apply, PiLp.add_apply,
      PiLp.single_apply, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, hab, hba, haa, hbb]
    simp
    ring
  refine ⟨EuclideanSpace.single a 1 + EuclideanSpace.single b ((1 : ℝ) : ℂ),
    EuclideanSpace.single a 1 + EuclideanSpace.single b ((-1 : ℝ) : ℂ), ?_, ?_⟩
  · rw [hform]; norm_num
  · rw [hform]; norm_num

/-- **Sparsity**: the possible nonzero positions of each row (and, by symmetry, column) form
an input-independent set of at most `m + 1 ≤ s` indices. -/
theorem family_sparse (κ ε : ℝ) (s : ℕ) (hs : 5 ≤ s) (i : Ind κ ε s) :
    (support i).card ≤ s ∧ ∀ (x : Inp κ ε s) (j : Ind κ ε s),
      (family κ ε s x i j ≠ 0 → j ∈ support i) ∧ (family κ ε s x j i ≠ 0 → j ∈ support i) := by
  refine ⟨(card_support_le i).trans (by have := mpar_le s hs; omega), fun x j => ?_⟩
  refine ⟨fun h => hard_support (rpar κ) x i j h, fun h => hard_support (rpar κ) x i j ?_⟩
  rwa [family, hard_symm] at h

/-- **Dimension** `N = 4 n m` with `s κ ln(1/ε) / 32 < N < s κ ln(1/ε)`. -/
theorem family_dimension (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    Fintype.card (Ind κ ε s) = 4 * npar κ ε * mpar s ∧
      s * κ * Real.log (1 / ε) / 32 < Fintype.card (Ind κ ε s) ∧
      (Fintype.card (Ind κ ε s) : ℝ) < s * κ * Real.log (1 / ε) := by
  have hcount := clock_count κ ε hκ hε hε1
  have hcard : Fintype.card (Ind κ ε s) = 4 * npar κ ε * mpar s := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, hcount]
    ring
  refine ⟨hcard, ?_, ?_⟩
  · rw [hcard]
    have hn := npar_gt κ ε hκ hε hε1
    have hm : s - 1 < 2 * mpar s := lt_two_mpar s
    have hm' : (s : ℝ) < 4 * mpar s := by
      have : s < 4 * mpar s := by omega
      exact_mod_cast this
    have hL : 0 < Real.log (1 / ε) := by
      have := L_ge ε hε hε1; have := log_64_gt; linarith
    have hκL : 0 < κ * Real.log (1 / ε) := mul_pos (by linarith) hL
    push_cast
    nlinarith [mul_lt_mul_of_pos_left hm' hκL]
  · rw [hcard]
    have hn := npar_le κ ε hκ hε hε1
    have hR := Rpar_le κ hκ
    have hR16 := sixteen_le_Rpar κ hκ
    have hm := mpar_le s hs
    have hl := log16_le ε hε hε1
    have hL := L_ge ε hε hε1
    have h64 := log_64_gt
    have hlog : Real.log (1 / (16 * ε)) < Real.log (1 / ε) := by
      apply Real.log_lt_log (by positivity)
      rw [div_lt_div_iff₀ (by positivity) hε]
      linarith
    have hn' : (npar κ ε : ℝ) < κ / 4 * Real.log (1 / ε) := by
      calc (npar κ ε : ℝ) ≤ ((Rpar κ - 1 : ℝ) / 2) * Real.log (1 / (16 * ε)) := hn
        _ < (Rpar κ : ℝ) / 2 * Real.log (1 / ε) := by nlinarith
        _ ≤ κ / 4 * Real.log (1 / ε) := by nlinarith
    have hm' : (mpar s : ℝ) < s := by
      have : mpar s < s := by omega
      exact_mod_cast this
    have hm0 : (0 : ℝ) < mpar s := by
      have := four_le_mpar s hs
      have : (4 : ℝ) ≤ mpar s := by exact_mod_cast this
      linarith
    have hLpos : 0 < Real.log (1 / ε) := by linarith
    have hq : (0 : ℝ) < κ / 4 * Real.log (1 / ε) := mul_pos (by linarith) hLpos
    push_cast
    nlinarith [mul_lt_mul_of_pos_right hn' hm0, mul_lt_mul_of_pos_left hm' hq]

theorem rhsVec_norm (κ ε : ℝ) (s : ℕ) (hs : 5 ≤ s) : ‖rhsVec κ ε s‖ = 1 := by
  have h : ‖rhsVec κ ε s‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [rhsVec, rhs, PiLp.toLp_apply, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Bool.true_eq_false, false_and, if_false, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add,
      true_and]
    rw [Finset.sum_eq_single (0 : Fin (2 * npar κ ε - 1 + 1))]
    · simp only [if_true]
      exact sum_logical_sq (mpar_even s hs) 1 (Or.inl rfl)
    · intro t _ ht
      simp [ht]
    · intro h; exact absurd (Finset.mem_univ _) h
  have := norm_nonneg (rhsVec κ ε s)
  nlinarith

/-- The normalised solution is the normalised history state. -/
theorem target_eq (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (x : Inp κ ε s) :
    target κ ε s x = ODEStateNormalization.unitDirection (sol (rpar κ) x) := by
  have hr0 := rpar_nonneg κ hκ
  have hr1 := rpar_lt_one κ hκ
  have hU := hard_isUnit (T := 2 * npar κ ε - 1) (rpar κ) hr0 hr1 x
  have hsol : SparseStateOverlap.matrixOperator (hardMatrix (T := 2 * npar κ ε - 1) (rpar κ) x)
      (sol (rpar κ) x) = rhsVec κ ε s := by
    rw [matrixOperator_eq_act]
    exact hard_mul_sol (mpar_even s hs) (by have := four_le_mpar s hs; omega) (rpar κ) x
  have hinv : Ring.inverse (SparseStateOverlap.matrixOperator
      (hardMatrix (T := 2 * npar κ ε - 1) (rpar κ) x)) (rhsVec κ ε s) = sol (rpar κ) x := by
    rw [← hsol]
    have e := congrArg (fun f : EuclideanSpace ℂ (Ind κ ε s) →L[ℂ] _ => f (sol (rpar κ) x))
      (Ring.inverse_mul_cancel _ hU)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using e
  show ODEStateNormalization.unitDirection (Ring.inverse (SparseStateOverlap.matrixOperator
    (hardMatrix (T := 2 * npar κ ε - 1) (rpar κ) x)) (rhsVec κ ε s)) = _
  rw [hinv]

/-- **Access exists**: native data with the hard matrices, input-independent locators and a
fixed word encoding of the entries. -/
theorem exists_access (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    ∃ D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) (ZMod 8) s,
      D.matrix = family κ ε s ∧ (∀ x x', D.rowOracle x = D.rowOracle x') ∧
      (∀ x x', D.columnOracle x = D.columnOracle x') ∧
      ∃ enc : ℂ → ZMod 8, ∀ x α, D.table x α = enc (D.matrix x α.1 α.2) := by
  have hcount := clock_count κ ε hκ hε hε1
  have hm := mpar_le s hs
  have hm2 := lt_two_mpar s
  have hn := npar_pos κ ε hκ hε hε1
  have hcard : s ≤ Fintype.card (Ind κ ε s) := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, hcount]
    have h1 : s ≤ 2 * mpar s := by omega
    have h2 : 2 * mpar s ≤ 2 * (2 * npar κ ε * mpar s) := by nlinarith
    omega
  have hms : mpar s + 1 ≤ s := by omega
  have hm2' : 2 ≤ mpar s := by have := four_le_mpar s hs; omega
  have hr0 := rpar_nonneg κ hκ
  have hr1 := (rpar_lt_one κ hκ).le
  refine ⟨hardData hcard hms hm2' (rpar κ) hr0 hr1, rfl, fun _ _ => rfl, fun _ _ => rfl,
    enc (rpar κ) (mpar s), fun x α => rfl⟩

/-- The signed decoder correlation of the normalised solution is the answer probability
`p = r^{2n} / (1 + r^{2n})`. -/
theorem target_correlation (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) (x : Inp κ ε s) :
    parSign x * (⟪target κ ε s x, decoderOf κ ε s (target κ ε s x)⟫_ℂ).re =
      answerProb (rpar κ) (npar κ ε) := by
  have hn := npar_pos κ ε hκ hε hε1
  have hcount := clock_count κ ε hκ hε hε1
  rw [target_eq κ ε s hκ hs x, decoderOf,
    answer_correlation (mpar_even s hs) hn hcount (rpar κ)
      (by have := rpar_nonneg κ hκ; have h16 := sixteen_le_Rpar κ hκ
          unfold rpar
          have : 1 / (Rpar κ : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
          linarith) x, ← mul_assoc]
  rcases parSign_pm x with h | h <;> rw [h] <;> ring

/-! ### The lower bound -/

variable {Z : Type*} [Fintype Z] [AddCommGroup Z] {K F L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The counting step.**  For native data of the hard family (input-independent locators,
entry-determined table), every adaptive protocol over admissible oracle labels, with any
output space and any decoder observable of norm at most one, whose signed decoder
correlation is at least `(2/3)(p - 2ε)` on every input (`p` the answer probability), makes in
the worst case more than `κ √s ln(1/ε) / 1536` weighted native queries. -/
theorem lower_bound_of_bias (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] (T : Tree O F E) (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (hbias : ∀ x, 2 / 3 * (answerProb (rpar κ) (npar κ ε) - 2 * ε) ≤
      parSign x * corr M (T.successDensity x)) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w := by
  set n := npar κ ε
  set m := mpar s
  have hn := npar_pos κ ε hκ hε hε1
  have hm4 := four_le_mpar s hs
  have hm0 : m ≠ 0 := by omega
  have hmeven := mpar_even s hs
  -- access conditions
  have hacc : HardAccess D := by
    obtain ⟨enc, henc⟩ := henc
    refine ⟨hrow, hcol, fun α => ?_⟩
    have h := (bitDetermined_hard (T := 2 * n - 1) (n := n) (rpar κ) α.1 α.2).comp (enc α)
    have hfun : (fun x => D.table x α) = fun x => enc α (hardMatrix (rpar κ) x α.1 α.2) := by
      funext x
      rw [henc, hDm]
      rfl
    rw [hfun]
    exact h
  -- weight growth of all labels
  set C := (1 + 2 / Real.sqrt m) ^ 2
  have hC : 1 ≤ C := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt m := by positivity
    nlinarith
  have hgrow := fun l => growth_admissible hm0 D hacc (O l) (w l) (hO l)
  obtain ⟨-, hbias'⟩ := bias_ge κ ε hκ hε hε1
  have hxor := xor_lower_bound_of_bias hmeven hm0 (fun l => (hgrow l).2.2) w C hC
    (fun l => (hgrow l).1) (fun l => (hgrow l).2.1) M hM T _ hbias
  rw [Fintype.card_fin] at hxor
  have hfin : ε ≤ (1 / 2) ^ n * ((1 + 2 / Real.sqrt m) ^ 2) ^ T.worstCost w :=
    hbias'.trans hxor
  have hq := q_bound n m (T.worstCost w) ε hε (by omega) hn (npar_ge_twoL κ ε hκ hε hε1) hfin
  have hngt := npar_gt κ ε hκ hε hε1
  have hsm := sqrt_mpar s hs
  have hL : 0 < Real.log (1 / ε) := by
    have := L_ge ε hε hε1; have := log_64_gt; linarith
  have hκL : 0 < κ * Real.log (1 / ε) / 32 := by positivity
  have h1 : κ * Real.sqrt s * Real.log (1 / ε) / 1536 =
      (κ * Real.log (1 / ε) / 32) * (Real.sqrt s / 2) / 24 := by ring
  rw [h1]
  calc (κ * Real.log (1 / ε) / 32) * (Real.sqrt s / 2) / 24
      < (n : ℝ) * Real.sqrt m / 24 := by
        apply div_lt_div_of_pos_right _ (by norm_num)
        exact mul_lt_mul'' hngt hsm hκL.le (by positivity)
    _ < T.worstCost w := hq

/-- **Theorem `qlsl:thm:main`, sharp form.**  Every adaptive protocol over admissible oracle
labels of native data for the hard family (input-independent locators, entry-determined
table) that heralds success with probability at least `2/3` on every input and outputs,
conditional on success, a state whose reduced state on the output register is within trace
distance `ε` of `|x_A⟩⟨x_A|`, makes in the worst case more than `κ √s ln(1/ε) / 1536` weighted
native queries.  The output space `E` is identified with the output register and a garbage
register `G` by a fixed isometry `V`, and the reduced state is the partial trace over `G`
(`ptrace`). -/
theorem lower_bound_sharp (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)) -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)))
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w := by
  obtain ⟨hpε, -⟩ := bias_ge κ ε hκ hε hε1
  exact lower_bound_of_bias κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO T
    (V.conjStarAlgEquiv.symm (ampl (G := G) (decoderOf κ ε s)))
    (norm_conj_ampl_le V _ (fun v => decoder_norm_le v)) fun x =>
      tree_bias_reduced V T x (decoderOf κ ε s) (fun v => decoder_norm_le v) (target κ ε s x)
        (parSign x) (parSign_pm x) _ ε (target_correlation κ ε s hκ hs hε hε1 x) hpε
        (hT x).1 (hT x).2

/-- **Theorem `qlsl:thm:main`** with the paper's conservative constant:
`Q > κ √s ln(1/ε) / 3072`. -/
theorem lower_bound (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)) -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)))
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 3072 < T.worstCost w := by
  have h := lower_bound_sharp κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO V T hT
  have hL : 0 < Real.log (1 / ε) := by
    have := L_ge ε hε hε1; have := log_64_gt; linarith
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < s))
  have : 0 < κ * Real.sqrt s * Real.log (1 / ε) := by
    have : (0 : ℝ) < κ := by linarith
    positivity
  linarith

/-- **Theorem `qlsl:thm:main` for a clean output**, the case of a one-point garbage register:
the output space is the coordinate space of the hard family, as for the released algorithm of
Theorem `qls:thm:main`. -/
theorem lower_bound_sharp_clean (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    (T : Tree O F (EuclideanSpace ℂ (Ind κ ε s)))
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (T.conditionalDensity x -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (T.conditionalDensity x)
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w := by
  refine lower_bound_sharp κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO unitGarbage T
    fun x => ?_
  rw [ptrace_unitGarbage]
  exact hT x

end

end LinearSystemLowerBound
