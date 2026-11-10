import SparseLowerBounds.Helpers.Ode.JointFamily.Solution

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Encoding the joint problem as a piecewise-constant ODE

Manuscript: the construction before Theorem `odel:thm:joint`.
For `m = 2^μ`, the gadget `U_j = 2|u⟩⟨u| - S^{j+1}`, `(U_j)_{bc} = 2/m - [b - c - 1 = j]`
(`LinearSystems.gadget`, eq. `odel:eq:gadget`), its dilation
`S_j = [[0, U_j], [U_j†, 0]]` (eq. `odel:eq:dilation`) with `S_j² = 1`,
`S_j ω = (-1)^j ω` for `ω = |+⟩ ⊗ v`, `v = m^{-1/2} Σ_z (-1)^z |z⟩`
(`Hamiltonian.alt`, `Hamiltonian.gadget_mulVec_alt`).

**The family** (`jointFamily`, `n + 2` stages, `η = 1`, `D = 0`: `jointFamily_skew`):

* stage `k < n` (length `π/2`): `H_k = ⊕_a S_{j_{ak}}` (`stageHam`), generator
  `G_k = i H_k`, no source (eq. `odel:eq:stages`);
* stage `n` (idle, length `T - 1 - nπ/2 ≥ 0`): `G = 0`, `b = 0` (proof of Theorem `odel:thm:joint`);
* stage `n + 1` (length `1`): `G = 0`, `b = -(-i)^n |u_M, ω⟩` (eq. `odel:eq:force`);
* `x₀ = u_M ⊗ ω`, `u_M = M^{-1/2} Σ_a |a⟩` (`jointInit`).

Index `JointIndex M μ s = (Fin M × Bool × Fin 2^μ) ⊕ Fin s` (core ⊕ zero padding,
so the `s` slots embed in the padding); words `Word μ`, decode `i · valMinAbs/2^μ`
(exact complex dyadic entries, scale `1`, `jointData_dyadic`); input- and
stage-independent location lists with full permutation extensions
(`DataBuilder.rowEquiv`, `permCLM`, `jointData_locators_const`); the stage-`k`
word of address `((a,β,b),(a,¬β,c))` depends only on the membership bit
`(a, k, b - c - 1)` (resp. `(a, k, c - b - 1)`), via the bit table `jointTable`.

**The solution** (`jointSol`) in closed form, no matrix exponential: each
`|a, ω⟩` is an eigenvector of every `H_k`, so
`x(t) = M^{-1/2} Σ_a e^{-iΦ_a(t)} |a, ω⟩ + clamp(t - (T-1), 0, 1) b` with
`Φ_a(t) = Σ_k (-1)^{j_{ak}} clamp(t - kπ/2, 0, π/2)` (`candPhase`); after the
hidden stages it is `(-i)^n M^{-1/2} Σ_a σ_a |a, ω⟩` (eq. `odel:eq:beforeforce`) and
`x(T) = -2(-i)^n M^{-1/2} |a_*, ω⟩`, `B = 2`, `‖x(T)‖ = 2/√M`, `g = √M`
(eq. `odel:eq:cancel`). The half indicator `halfObs` reads which half `a_*`
lies in.

**Layout.** `JointIndex`, `card_jointIndex`, `stageHam`, `jointGen`, `candState`,
`jointInit`, `jointSrc`, `candPhase`, `jointSol`, `jointTarget` and `halfObs` are
defined, with these exact signatures, in `Helpers/Ode/JointFamily/Defs` (imported here),
so that the proof helpers `Helpers/Ode/JointFamily/Eigen` (dilation, eigen relation,
norms, half indicator) and `Helpers/Ode/JointFamily/Solution` (stage derivatives,
endpoints) can use them.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding
open scoped InnerProductSpace

variable {M n μ s : ℕ}

/-- **The bit table**: the word of address `((a,β,b),(a,¬β,c))` is
`2^μ (U_j)_{bc} = 2 - 2^μ [b - c - 1 = j]` (resp. `(U_j)_{cb}`), depending only
on the membership bit `(a, gadgetPos b c)` (resp. `(a, gadgetPos c b)`); all
other words are the known `0`. -/
def jointTable (M μ s : ℕ) :
    Hamiltonian.BitTable (Fin M × Fin (2 ^ μ)) (JointIndex M μ s × JointIndex M μ s) where
  addr ad := match ad with
    | (Sum.inl (a, β, b), Sum.inl (a', β', c)) =>
        if a = a' ∧ β ≠ β' then
          some (a, if β then LinearSystems.gadgetPos c b else LinearSystems.gadgetPos b c)
        else none
    | _ => none
  word ad bit := match ad with
    | (Sum.inl (a, β, _), Sum.inl (a', β', _)) =>
        if a = a' ∧ β ≠ β' then 2 - (if bit then 2 ^ μ else 0) else 0
    | _ => 0

/-- The membership bits of stage `k`: `(a, z) ↦ [j_{ak} = z]`. -/
def stageBits (x : Promised M n (2 ^ μ)) (k : Fin n) : Fin M × Fin (2 ^ μ) → Bool :=
  fun i => membership x (i.1, k, i.2)

/-- The `s` slots are the padding indices. -/
def jointSlot (M μ s : ℕ) : Fin s ↪ JointIndex M μ s := ⟨Sum.inr, Sum.inr_injective⟩

/-- The public location list of a row (and, by symmetry, of a column): core row
`(a, β, b)` lists `(a, ¬β, t)` in slot `t < 2^μ` and padding beyond. -/
def jointLoc (M μ s : ℕ) : JointIndex M μ s → Fin s ↪ JointIndex M μ s
  | Sum.inl (a, β, _) =>
      ⟨fun t => if h : (t : ℕ) < 2 ^ μ then Sum.inl (a, !β, ⟨t, h⟩) else Sum.inr t, by
        intro t t' h
        by_cases ht : (t : ℕ) < 2 ^ μ <;> by_cases ht' : (t' : ℕ) < 2 ^ μ <;>
          simp_all [Fin.ext_iff]⟩
  | Sum.inr _ => jointSlot M μ s

/-- Every word of the stage table lies in `(-2^μ, 2^μ]`. -/
theorem jointTable_word_mem (hμ : 1 ≤ μ) (ad : JointIndex M μ s × JointIndex M μ s)
    (bit : Bool) :
    -(2 : ℤ) ^ μ < (jointTable M μ s).word ad bit ∧ (jointTable M μ s).word ad bit ≤ 2 ^ μ := by
  have h2 : (2 : ℤ) ≤ 2 ^ μ := by exact_mod_cast two_le_two_pow hμ
  rcases ad with ⟨⟨a, β, b⟩ | t, ⟨a', β', c⟩ | t'⟩
  · simp only [jointTable]
    split_ifs <;> constructor <;> linarith
  all_goals (simp only [jointTable]; constructor <;> linarith)

/-- A core entry of `H_k`: `2/2^μ - [pos = j_{ak}]` on the opposite block. -/
theorem stageHam_inl (j : Positions M n (2 ^ μ)) (k : Fin n) (a a' : Fin M) (β β' : Bool)
    (b c : Fin (2 ^ μ)) :
    stageHam (s := s) j k (Sum.inl (a, β, b)) (Sum.inl (a', β', c)) =
      if a = a' ∧ β ≠ β' then (2 / ((2 ^ μ : ℕ) : ℂ)) -
        (if (if β then LinearSystems.gadgetPos c b else LinearSystems.gadgetPos b c) = j a k
          then 1 else 0)
      else 0 := by
  cases β <;> rfl

/-- The stage-`k` words decode to `H_k` (`decoded`, the construction before Theorem
`odel:thm:joint`). -/
theorem wordDecode_stage (hμ : 1 ≤ μ) (x : Promised M n (2 ^ μ)) (k : Fin n)
    (i j : JointIndex M μ s) :
    Hamiltonian.wordDecode μ
        (((jointTable M μ s).value (stageBits x k) (i, j) : ℤ) : Hamiltonian.Word μ) =
      stageHam x.1 k i j := by
  have hb := jointTable_word_mem (M := M) (s := s) hμ (i, j)
    ((jointTable M μ s).bit (stageBits x k) (i, j))
  rw [Hamiltonian.BitTable.value, Hamiltonian.wordDecode_intCast _ hb.1 hb.2]
  rcases i with ⟨a, β, b⟩ | t <;> rcases j with ⟨a', β', c⟩ | t'
  · rw [stageHam_inl]
    by_cases hab : a = a' ∧ β ≠ β'
    · obtain ⟨rfl, hββ⟩ := hab
      by_cases hbit :
          x.1 a k = (if β then LinearSystems.gadgetPos c b else LinearSystems.gadgetPos b c)
      · simp [Hamiltonian.BitTable.bit, jointTable, stageBits, membership, hββ, hbit]
        rw [sub_div, div_self (pow_ne_zero _ two_ne_zero)]
      · simp [Hamiltonian.BitTable.bit, jointTable, stageBits, membership, hββ, hbit,
          Ne.symm hbit]
    · simp [Hamiltonian.BitTable.bit, jointTable, hab]
  all_goals simp [Hamiltonian.BitTable.bit, jointTable, stageHam]

/-- **Decoding the stage table recovers the generator** (`decoded` of `jointData`). -/
theorem jointGen_decoded (hμ : 1 ≤ μ) (x : Promised M n (2 ^ μ)) (k : Fin (n + 2))
    (i j : JointIndex M μ s) :
    Complex.I * Hamiltonian.wordDecode μ (if hk : (k : ℕ) < n then
        (((jointTable M μ s).value (stageBits x ⟨k, hk⟩) (i, j) : ℤ) : Hamiltonian.Word μ)
      else 0) = jointGen x.1 k i j := by
  unfold jointGen
  split_ifs with hk
  · rw [Matrix.smul_apply, smul_eq_mul, wordDecode_stage hμ]
  · simp [Hamiltonian.wordDecode]

theorem jointLoc_inl (hμs : 2 ^ μ ≤ s) (a : Fin M) (β : Bool) (b c : Fin (2 ^ μ)) :
    jointLoc M μ s (Sum.inl (a, β, b)) ⟨c, lt_of_lt_of_le c.2 hμs⟩ = Sum.inl (a, !β, c) := by
  simp [jointLoc]

/-- Row cover: a nonzero entry of row `i` lies in its location list. -/
theorem jointGen_row_covers (hμs : 2 ^ μ ≤ s) (j : Positions M n (2 ^ μ)) (k : Fin (n + 2))
    (i i' : JointIndex M μ s) (h : jointGen j k i i' ≠ 0) :
    i' ∈ Finset.univ.image (jointLoc M μ s i) := by
  obtain ⟨a, β, b, c, rfl, rfl⟩ := jointGen_support h
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, jointLoc_inl hμs a β b c⟩

/-- Column cover: a nonzero entry of column `i'` lies in its location list. -/
theorem jointGen_col_covers (hμs : 2 ^ μ ≤ s) (j : Positions M n (2 ^ μ)) (k : Fin (n + 2))
    (i i' : JointIndex M μ s) (h : jointGen j k i i' ≠ 0) :
    i ∈ Finset.univ.image (jointLoc M μ s i') := by
  obtain ⟨a, β, b, c, rfl, rfl⟩ := jointGen_support h
  refine Finset.mem_image.mpr ⟨⟨b, lt_of_lt_of_le b.2 hμs⟩, Finset.mem_univ _, ?_⟩
  rw [jointLoc_inl hμs, Bool.not_not]

/-- **The hard sampled-time data** (the construction before Theorem `odel:thm:joint`): matrix
`jointGen`, exact words `Word μ` with decode `i · valMinAbs/2^μ` (scale `1`), the stage table of
`jointTable` (`0` on the idle and source stages), input- and stage-independent locators with fixed
permutation extensions. -/
def jointData (M n μ s : ℕ) (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) :
    Data (Promised M n (2 ^ μ) × Fin (n + 2)) (JointIndex M μ s) (Hamiltonian.Word μ) s where
  slot := jointSlot M μ s
  slots_pos := lt_of_lt_of_le (Nat.two_pow_pos μ) hμs
  scale := 1
  scale_pos := one_pos
  matrix p := jointGen p.1.1 p.2
  table p ad :=
    if hk : (p.2 : ℕ) < n then
      (((jointTable M μ s).value (stageBits p.1 ⟨p.2, hk⟩) ad : ℤ) : Hamiltonian.Word μ)
    else 0
  decode _ z := Complex.I * Hamiltonian.wordDecode μ z
  decode_bound _ z := by
    rw [norm_mul, Complex.norm_I, one_mul]; exact Hamiltonian.norm_wordDecode_le μ z
  decoded p i j := jointGen_decoded hμ p.1 p.2 i j
  rowloc _ i k := jointLoc M μ s i k
  colloc _ j k := jointLoc M μ s j k
  row_injective _ i := (jointLoc M μ s i).injective
  column_injective _ j := (jointLoc M μ s j).injective
  row_covers p i j h := jointGen_row_covers hμs p.1.1 p.2 i j h
  column_covers p i j h := jointGen_col_covers hμs p.1.1 p.2 i j h
  rowOracle _ := Hamiltonian.permCLM (Hamiltonian.rowEquiv (jointSlot M μ s) (jointLoc M μ s))
  columnOracle _ := Hamiltonian.permCLM (Hamiltonian.colEquiv (jointSlot M μ s) (jointLoc M μ s))
  row_unitary _ := LookupOracle.permutationUnitary_unitary _
  column_unitary _ := LookupOracle.permutationUnitary_unitary _
  row_valid _ i k := (Hamiltonian.permCLM_single _ _ _).trans (by rw [Hamiltonian.rowEquiv_slot])
  column_valid _ j k :=
    (Hamiltonian.permCLM_single _ _ _).trans (by rw [Hamiltonian.colEquiv_slot])

/-- **The locators are public** (the construction before Theorem `odel:thm:joint` and Section
`odel:sec:main`): the location lists and the location oracles of `jointData` do not depend on the
input or the stage. -/
theorem jointData_locators_const (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s)
    (p p' : Promised M n (2 ^ μ) × Fin (n + 2)) :
    (jointData M n μ s hμ hμs).rowloc p = (jointData M n μ s hμ hμs).rowloc p' ∧
      (jointData M n μ s hμ hμs).colloc p = (jointData M n μ s hμ hμs).colloc p' ∧
      (jointData M n μ s hμ hμs).rowOracle p = (jointData M n μ s hμ hμs).rowOracle p' ∧
      (jointData M n μ s hμ hμs).columnOracle p = (jointData M n μ s hμ hμs).columnOracle p' :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- **Exact dyadic entries** (the construction before Theorem `odel:thm:joint`): every sampled entry
is `i · v/2^μ` with an integer `-2^μ < v ≤ 2^μ`, the word stored in the table. -/
theorem jointData_dyadic (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s)
    (p : Promised M n (2 ^ μ) × Fin (n + 2)) (i j : JointIndex M μ s) :
    ∃ v : ℤ, -(2 : ℤ) ^ μ < v ∧ v ≤ 2 ^ μ ∧
      (jointData M n μ s hμ hμs).matrix p i j = Complex.I * ((v : ℂ) / 2 ^ μ) := by
  rw [← (jointData M n μ s hμ hμs).decoded p i j]
  by_cases hk : (p.2 : ℕ) < n
  · have hb := jointTable_word_mem (M := M) (s := s) hμ (i, j)
      ((jointTable M μ s).bit (stageBits p.1 ⟨p.2, hk⟩) (i, j))
    refine ⟨_, hb.1, hb.2, ?_⟩
    show Complex.I * Hamiltonian.wordDecode μ (dite _ _ _) = _
    rw [dif_pos hk, Hamiltonian.BitTable.value, Hamiltonian.wordDecode_intCast _ hb.1 hb.2]
  · have h2 : (2 : ℤ) ≤ 2 ^ μ := by exact_mod_cast two_le_two_pow hμ
    refine ⟨0, by linarith, by positivity, ?_⟩
    show Complex.I * Hamiltonian.wordDecode μ (dite _ _ _) = _
    rw [dif_neg hk]
    simp [Hamiltonian.wordDecode]

/-- The stage durations: `π/2` for the hidden stages, `T - 1 - nπ/2` for the idle
stage, `1` for the source stage (Section `odel:sec:main` and proof of Theorem `odel:thm:joint`). -/
def jointLen (n : ℕ) (T : ℝ) (k : Fin (n + 2)) : ℝ :=
  if (k : ℕ) < n then Real.pi / 2 else if (k : ℕ) = n then T - 1 - n * (Real.pi / 2) else 1

/-- **The joint ODE family** (Section `odel:sec:main` and proof of Theorem `odel:thm:joint`): `n`
hidden stages, an idle stage and the source stage, on `[0, T]`. -/
def jointFamily (M n μ s : ℕ) (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (T : ℝ)
    (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) :
    Family (Promised M n (2 ^ μ)) (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2) s where
  data := jointData M n μ s hμ hμs
  len := jointLen n T
  len_nonneg k := by
    unfold jointLen
    split_ifs <;> linarith [Real.pi_pos]
  src k := if (k : ℕ) = n + 1 then jointSrc M n μ s else 0
  init := jointInit M μ s

variable {hμ : 1 ≤ μ} {hμs : 2 ^ μ ≤ s} {T : ℝ} {hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T}

theorem jointFamily_lenNat {i : ℕ} (hi : i < n + 2) :
    (jointFamily M n μ s hμ hμs T hT).lenNat i =
      if i < n then Real.pi / 2 else if i = n then T - 1 - n * (Real.pi / 2) else 1 :=
  dif_pos hi

/-- The breakpoints `t_k = kπ/2` of the hidden stages. -/
theorem jointFamily_start_le {i : ℕ} (hi : i ≤ n) :
    (jointFamily M n μ s hμ hμs T hT).start i = i * (Real.pi / 2) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Family.start_succ, ih (by omega), jointFamily_lenNat (by omega), if_pos (by omega)]
    push_cast
    ring

theorem jointFamily_start_idle : (jointFamily M n μ s hμ hμs T hT).start (n + 1) = T - 1 := by
  rw [Family.start_succ, jointFamily_start_le le_rfl, jointFamily_lenNat (by omega),
    if_neg (lt_irrefl n), if_pos rfl]
  ring

theorem jointFamily_start_end : (jointFamily M n μ s hμ hμs T hT).start (n + 2) = T := by
  rw [Family.start_succ, jointFamily_start_idle, jointFamily_lenNat (by omega),
    if_neg (by omega), if_neg (by omega)]
  ring

/-- The family lives on `[0, T]`. -/
theorem jointFamily_T : (jointFamily M n μ s hμ hμs T hT).T = T := by
  rw [Family.T_eq_start, jointFamily_start_end]

/-- `B = ‖x₀‖ + ∫‖b‖ = 2` (eq. `odel:eq:cancel`). -/
theorem jointFamily_mass (hM : 1 ≤ M) : (jointFamily M n μ s hμ hμs T hT).mass = 2 := by
  have h1 : ∑ k : Fin (n + 2), jointLen n T k *
      ‖(if (k : ℕ) = n + 1 then jointSrc M n μ s else 0)‖ = 1 := by
    rw [Finset.sum_eq_single (Fin.last (n + 1))]
    · rw [Fin.val_last, if_pos rfl, norm_jointSrc hM, mul_one, jointLen,
        if_neg (by simp), if_neg (by simp)]
    · intro k _ hk
      rw [if_neg (show ¬((k : ℕ) = n + 1) from fun h => hk (Fin.ext h)), norm_zero, mul_zero]
    · simp
  show ‖jointInit M μ s‖ + ∑ k : Fin (n + 2), jointLen n T k *
      ‖(if (k : ℕ) = n + 1 then jointSrc M n μ s else 0)‖ = 2
  rw [norm_jointInit hM, h1]
  norm_num

/-- **The explicit path solves every instance** (stages: eqs. `odel:eq:stages`,
`odel:eq:force`). -/
theorem jointSol_solves (x : Promised M n (2 ^ μ)) :
    (jointFamily M n μ s hμ hμs T hT).Solves x (jointSol M n μ s T x) := by
  refine ⟨jointSol_zero (one_le_of_time hT) x, fun k => ?_⟩
  rcases lt_trichotomy (k : ℕ) n with h | h | h
  · rw [jointFamily_start_le h.le, jointFamily_start_le (show (k : ℕ) + 1 ≤ n by omega),
      Nat.cast_succ]
    exact solvesODE_hidden hμ hT x k h
  · rw [h, jointFamily_start_le le_rfl, jointFamily_start_idle]
    exact solvesODE_idle x k h
  · have h' : (k : ℕ) = n + 1 := by omega
    rw [h', jointFamily_start_idle, jointFamily_start_end]
    exact solvesODE_source hT x k h'

/-- **Eq. `odel:eq:cancel`**: `x(T) = -2(-i)^n M^{-1/2} |a_*, ω⟩`. -/
theorem jointSol_T (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) (x : Promised M n (2 ^ μ)) :
    jointSol M n μ s T x T =
      ((-2 : ℂ) * (-Complex.I) ^ n / (Real.sqrt M : ℂ)) • candState M μ s (oddCand x) :=
  jointSol_end hT x

/-- `‖x(T)‖ = 2/√M`. -/
theorem norm_jointSol_T (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) (x : Promised M n (2 ^ μ)) :
    ‖jointSol M n μ s T x T‖ = 2 / Real.sqrt M := by
  have h1 : ‖(-2 : ℂ) * (-Complex.I) ^ n‖ = 2 := by simp
  have h2 : ‖((Real.sqrt M : ℝ) : ℂ)‖ = Real.sqrt M := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [jointSol_T hT, norm_smul, norm_candState, mul_one, norm_div, h1, h2]

/-- The normalised solution is `jointTarget`. -/
theorem unitDirection_jointSol_T (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T)
    (x : Promised M n (2 ^ μ)) :
    ODEStateNormalization.unitDirection (jointSol M n μ s T x T) = jointTarget M n μ s x := by
  have hM : (0 : ℝ) < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast (oddCand x).pos)
  have hM' : ((Real.sqrt M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [ODEStateNormalization.unitDirection, norm_jointSol_T hT, jointSol_T hT, jointTarget,
    ← smul_assoc]
  congr 1
  rw [Complex.real_smul]
  push_cast
  field_simp

/-- **The joint family is in the class** with `η = 1`, `D = 0` and `g = √M ≤ ḡ` (Section
`odel:sec:main`, eq. `odel:eq:cancel` and proof of Theorem `odel:thm:joint`). `InClass` certifies
`D ⪰ 0` (accretive generators); `D = 0` itself is `jointFamily_skew`. -/
theorem jointFamily_inClass {gbar : ℝ} (hg : Real.sqrt M ≤ gbar) :
    (jointFamily M n μ s hμ hμs T hT).InClass 1 gbar where
  accretive x k := accretive_jointGen x.1 k
  row_norm x k i := by rw [one_pow]; exact sum_norm_sq_jointGen_row x.1 k i
  col_norm x k j := by rw [one_pow]; exact sum_norm_sq_jointGen_col x.1 k j
  solution x := by
    have hM : 1 ≤ M := (oddCand x).pos
    have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast hM)
    refine ⟨jointSol M n μ s T x, jointSol_solves x, ?_, ?_⟩
    · rw [jointFamily_T]
      intro h
      have h2 := norm_jointSol_T (s := s) hT x
      rw [h, norm_zero] at h2
      exact absurd h2 (div_pos two_pos hs).ne
    · rw [jointFamily_mass hM, jointFamily_T, norm_jointSol_T hT x, mul_div_assoc',
        le_div_iff₀ hs]
      nlinarith

/-- **`D = 0`** (Section `odel:sec:main`): every stage generator of the joint family is
`i H` with `H` Hermitian (`H = H_k` on the hidden stages, `H = 0` on the idle
and source stages), so `-A = D + iH` has `D = 0`, not only `D ⪰ 0`. -/
theorem jointFamily_skew (x : Promised M n (2 ^ μ)) (k : Fin (n + 2)) :
    ∃ H : Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ, H.IsHermitian ∧
      (jointFamily M n μ s hμ hμs T hT).data.matrix (x, k) = Complex.I • H := by
  show ∃ H : Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ, H.IsHermitian ∧
    jointGen x.1 k = Complex.I • H
  unfold jointGen
  split_ifs with hk
  · exact ⟨stageHam x.1 ⟨k, hk⟩, stageHam_isHermitian _ _, rfl⟩
  · exact ⟨0, Matrix.isHermitian_zero, (smul_zero _).symm⟩

/-- The half indicator reads the half of `a_*` on the target. -/
theorem inner_halfObs_jointTarget (x : Promised M n (2 ^ μ)) :
    (⟪jointTarget M n μ s x, halfObs M μ s (jointTarget M n μ s x)⟫_ℂ).re =
      halfSign M (oddCand x) := by
  rw [jointTarget, map_smul, halfObs_candState, inner_smul_left, inner_smul_right,
    inner_smul_right, inner_self_eq_norm_sq_to_K, norm_candState, ← mul_assoc,
    mul_comm ((starRingEnd ℂ) _), Complex.mul_conj', norm_neg_negI_pow]
  simp

end

end SparseLowerBounds.ODE
end
