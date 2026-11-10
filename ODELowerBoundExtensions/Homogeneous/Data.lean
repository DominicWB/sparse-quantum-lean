import ODELowerBoundExtensions.Homogeneous.Table

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The flag-extended joint index exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Proposition `odel:rem:homogeneous`: the sampled-time data and the family

Manuscript: Proposition `odel:rem:homogeneous`, with the encoding of the construction before Theorem
`odel:thm:joint` ("All entries are complex dyadic numbers with public support, public time
dependence of that support and public full locator extensions"). The data follows
`SparseLowerBounds.ODE.jointData`, with the stage tables `homTable` and the per-address decode
`homPhase` of `ODELowerBoundExtensions.Homogeneous.Table`; every entry is an exact complex dyadic
number (`homData_dyadic`).

**Locators** depend on the stage but not on the input (`homData_locators_input_indep`): on the
hidden stages the joint lists `jointLoc` inside the flag block (`hiddenLoc`), on the known stages
lists whose slots `0`, `1` are `(f, i)` and `(!f, i)` (`pulseLoc`). Both are fixed injective lists
with permutation extensions (`Hamiltonian.rowEquiv`, `permCLM`). The stage dependence is forced when
`s = 2^μ` (`s` a power of two): then the joint list already fills all `s` slots, so it cannot also
hold the flag flip `(!f, i)` of the `Y` pulse; for uniformity it is used for every `s`. It is
allowed by the paper (the construction before Theorem `odel:thm:joint`: "public time dependence of
that support"). The cost-`0` argument of `SparseLowerBounds.ODE.Model` for a controlled locator call
(stated there for input- and stage-independent locators) still applies: the time address is a
workspace register, so the locator `Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ L_k` is a fixed gate that does not depend
on the input.

`homFamily` is the family on `[0, T]` for `homBusy M n ≤ T`; it has no source
(`homFamily_src`), so `B = ‖x₀‖` (`homFamily_mass`).
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian NativeSparseBlockEncoding
open scoped InnerProductSpace

variable {M n μ s : ℕ}

/-! ### Location lists -/

/-- The `s` slots are the flag-zero padding indices. -/
def homSlot (M μ s : ℕ) : Fin s ↪ HomIndex M μ s :=
  ⟨fun t => (false, Sum.inr t), by intro t t' h; simpa using h⟩

/-- The hidden-stage location list: the joint list `jointLoc` inside the flag block. -/
def hiddenLoc (M μ s : ℕ) (i : HomIndex M μ s) : Fin s ↪ HomIndex M μ s :=
  (jointLoc M μ s i.2).trans ⟨fun y => (i.1, y), by intro y y' h; simpa using h⟩

/-- The known-stage location list of row `(f, i)`: slot `t` is
`(f xor [t odd], swap(inr 0, i)(inr ⌊t/2⌋))`, so slot `0` is `(f, i)` and slot `1` is
`(!f, i)`. -/
def pulseLocFun (M μ s : ℕ) (hs : 0 < s) (i : HomIndex M μ s) (t : Fin s) : HomIndex M μ s :=
  (Bool.xor i.1 (decide ((t : ℕ) % 2 = 1)),
    Equiv.swap (Sum.inr ⟨0, hs⟩ : JointIndex M μ s) i.2
      (Sum.inr ⟨(t : ℕ) / 2, lt_of_le_of_lt (Nat.div_le_self _ _) t.2⟩))

/-- The known-stage lists are injective. -/
theorem pulseLocFun_injective (hs : 0 < s) (i : HomIndex M μ s) :
    Function.Injective (pulseLocFun M μ s hs i) := by
  intro t t' h
  simp only [pulseLocFun, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' := (Equiv.injective _ h2)
  simp only [Sum.inr.injEq, Fin.mk.injEq] at h2'
  have h1' : decide ((t : ℕ) % 2 = 1) = decide ((t' : ℕ) % 2 = 1) := by
    cases hi : i.1 <;> rw [hi] at h1 <;> simpa using h1
  have hiff := decide_eq_decide.mp h1'
  have hmod : (t : ℕ) % 2 = (t' : ℕ) % 2 := by omega
  ext
  rw [← Nat.div_add_mod (t : ℕ) 2, ← Nat.div_add_mod (t' : ℕ) 2, h2', hmod]

/-- Slot `0` of a known-stage list is the row itself. -/
theorem pulseLocFun_zero (hs : 0 < s) (i : HomIndex M μ s) :
    pulseLocFun M μ s hs i ⟨0, hs⟩ = i := by
  obtain ⟨f, c⟩ := i
  simp [pulseLocFun]

/-- Slot `1` of a known-stage list is the flag flip of the row. -/
theorem pulseLocFun_one (hs : 0 < s) (h1 : 1 < s) (i : HomIndex M μ s) :
    pulseLocFun M μ s hs i ⟨1, h1⟩ = (!i.1, i.2) := by
  obtain ⟨f, c⟩ := i
  simp [pulseLocFun]

/-- **The support of `G_k`**: on a hidden stage it joins `(1, (a, β, b))` to `(1, (a, ¬β, c))`;
on a known stage it is diagonal or a flag flip. -/
theorem homGen_support {j : Positions M n (2 ^ μ)} {k : Fin (n + 4)} {i i' : HomIndex M μ s}
    (h : homGen j k i i' ≠ 0) :
    ((k : ℕ) < n ∧ i.1 = true ∧ i'.1 = true ∧
      ∃ a β b c, i.2 = Sum.inl (a, β, b) ∧ i'.2 = Sum.inl (a, !β, c)) ∨
    (¬ (k : ℕ) < n ∧ (i' = i ∨ i' = (!i.1, i.2))) := by
  obtain ⟨f, c⟩ := i
  obtain ⟨f', c'⟩ := i'
  by_cases hk : (k : ℕ) < n
  · left
    have hgen : homGen j k (f, c) (f', c') = Complex.I *
        (if f = true ∧ f' = true then stageHam (s := s) j ⟨k, hk⟩ c c' else 0) := by
      simp only [homGen, if_neg (show (k : ℕ) ≠ n + 2 by omega), homHam, dif_pos hk,
        Matrix.smul_apply, smul_eq_mul, flagHam, Matrix.of_apply]
    rw [hgen] at h
    by_cases hf : f = true ∧ f' = true
    · rw [if_pos hf] at h
      exact ⟨hk, hf.1, hf.2, stageHam_support (right_ne_zero_of_mul h)⟩
    · rw [if_neg hf, mul_zero] at h
      exact absurd rfl h
  · right
    refine ⟨hk, ?_⟩
    rcases (show (k : ℕ) = n ∨ (k : ℕ) = n + 1 ∨ (k : ℕ) = n + 2 ∨ (k : ℕ) = n + 3 by omega)
      with hk' | hk' | hk' | hk'
    · left
      by_contra hne
      apply h
      simp only [homGen, homHam, pulseHam, hk', lt_irrefl, if_false, if_true,
        Matrix.smul_apply, smul_eq_mul, show n ≠ n + 2 by omega, dif_neg,
        not_false_eq_true]
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hne), mul_zero]
    · by_cases hc : c = c'
      · subst hc
        cases f <;> cases f' <;> simp
      · exfalso; apply h
        simp [homGen, homHam, yHam, hk', hc]
    · left
      by_contra hne
      apply h
      simp only [homGen, rejectProj, hk', if_true]
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hne)]
    · exfalso; apply h
      simp [homGen, homHam, hk']

/-- The known-stage location list as an embedding. -/
def pulseLoc (M μ s : ℕ) (hs : 0 < s) (i : HomIndex M μ s) : Fin s ↪ HomIndex M μ s :=
  ⟨pulseLocFun M μ s hs i, pulseLocFun_injective hs i⟩

/-- **The stage-dependent public location list** (the construction before Theorem `odel:thm:joint`:
"All entries are complex dyadic numbers with public support, public time dependence of that support
and public full locator extensions"). -/
def homLoc (M n μ s : ℕ) (hs : 0 < s) (k : Fin (n + 4)) (i : HomIndex M μ s) :
    Fin s ↪ HomIndex M μ s :=
  if (k : ℕ) < n then hiddenLoc M μ s i else pulseLoc M μ s hs i

/-- Row cover: a nonzero entry of row `i` of `G_k` lies in its stage-`k` location list. -/
theorem homGen_row_covers (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (hs : 0 < s)
    (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (i i' : HomIndex M μ s)
    (h : homGen j k i i' ≠ 0) : i' ∈ Finset.univ.image (homLoc M n μ s hs k i) := by
  have h1s : 1 < s := lt_of_lt_of_le (two_le_two_pow hμ) hμs
  rcases homGen_support h with ⟨hk, hf, hf', a, β, b, c, hi, hi'⟩ | ⟨hk, hii | hii⟩
  · refine Finset.mem_image.mpr ⟨⟨c, lt_of_lt_of_le c.2 hμs⟩, Finset.mem_univ _, ?_⟩
    rw [homLoc, if_pos hk]
    show (i.1, jointLoc M μ s i.2 _) = i'
    rw [hi, jointLoc_inl hμs, hf, ← hf', ← hi']
  · refine Finset.mem_image.mpr ⟨⟨0, hs⟩, Finset.mem_univ _, ?_⟩
    rw [homLoc, if_neg hk, hii]
    exact pulseLocFun_zero hs i
  · refine Finset.mem_image.mpr ⟨⟨1, h1s⟩, Finset.mem_univ _, ?_⟩
    rw [homLoc, if_neg hk, hii]
    exact pulseLocFun_one hs h1s i

/-- Column cover: a nonzero entry of column `i'` of `G_k` lies in its stage-`k` location list. -/
theorem homGen_col_covers (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (hs : 0 < s)
    (j : Positions M n (2 ^ μ)) (k : Fin (n + 4)) (i i' : HomIndex M μ s)
    (h : homGen j k i i' ≠ 0) : i ∈ Finset.univ.image (homLoc M n μ s hs k i') := by
  have h1s : 1 < s := lt_of_lt_of_le (two_le_two_pow hμ) hμs
  rcases homGen_support h with ⟨hk, hf, hf', a, β, b, c, hi, hi'⟩ | ⟨hk, hii | hii⟩
  · refine Finset.mem_image.mpr ⟨⟨b, lt_of_lt_of_le b.2 hμs⟩, Finset.mem_univ _, ?_⟩
    rw [homLoc, if_pos hk]
    show (i'.1, jointLoc M μ s i'.2 _) = i
    rw [hi', jointLoc_inl hμs, Bool.not_not, hf', ← hf, ← hi]
  · refine Finset.mem_image.mpr ⟨⟨0, hs⟩, Finset.mem_univ _, ?_⟩
    rw [homLoc, if_neg hk, hii]
    exact pulseLocFun_zero hs i
  · refine Finset.mem_image.mpr ⟨⟨1, h1s⟩, Finset.mem_univ _, ?_⟩
    rw [homLoc, if_neg hk, hii]
    show pulseLocFun M μ s hs _ _ = i
    rw [pulseLocFun_one hs h1s]
    simp

/-! ### The data -/

/-- **The hard sampled-time data of the homogeneous variant**: matrix `homGen`, exact words
`Word μ` with the per-address decode `homPhase · valMinAbs/2^μ` (scale `1`), the stage tables
`homTable`, stage-dependent input-independent locators with fixed permutation extensions. -/
def homData (M n μ s : ℕ) (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) :
    Data (Promised M n (2 ^ μ) × Fin (n + 4)) (HomIndex M μ s) (Hamiltonian.Word μ) s where
  slot := homSlot M μ s
  slots_pos := lt_of_lt_of_le (Nat.two_pow_pos μ) hμs
  scale := 1
  scale_pos := one_pos
  matrix p := homGen p.1.1 p.2
  table p ad := (((homTable M n μ s p.2).value (homBits p.1 p.2) ad : ℤ) : Hamiltonian.Word μ)
  decode ad z := homPhase ad * Hamiltonian.wordDecode μ z
  decode_bound ad z := homDecode_bound ad z
  decoded p i j := homGen_decoded hμ p.1 p.2 i j
  rowloc p i t := homLoc M n μ s (lt_of_lt_of_le (Nat.two_pow_pos μ) hμs) p.2 i t
  colloc p j t := homLoc M n μ s (lt_of_lt_of_le (Nat.two_pow_pos μ) hμs) p.2 j t
  row_injective p i := (homLoc M n μ s _ p.2 i).injective
  column_injective p j := (homLoc M n μ s _ p.2 j).injective
  row_covers p i j h := homGen_row_covers hμ hμs _ p.1.1 p.2 i j h
  column_covers p i j h := homGen_col_covers hμ hμs _ p.1.1 p.2 i j h
  rowOracle p := Hamiltonian.permCLM (Hamiltonian.rowEquiv (homSlot M μ s)
    (homLoc M n μ s (lt_of_lt_of_le (Nat.two_pow_pos μ) hμs) p.2))
  columnOracle p := Hamiltonian.permCLM (Hamiltonian.colEquiv (homSlot M μ s)
    (homLoc M n μ s (lt_of_lt_of_le (Nat.two_pow_pos μ) hμs) p.2))
  row_unitary _ := LookupOracle.permutationUnitary_unitary _
  column_unitary _ := LookupOracle.permutationUnitary_unitary _
  row_valid _ i k := (Hamiltonian.permCLM_single _ _ _).trans (by rw [Hamiltonian.rowEquiv_slot])
  column_valid _ j k :=
    (Hamiltonian.permCLM_single _ _ _).trans (by rw [Hamiltonian.colEquiv_slot])

/-- **The locators are public** (the construction before Theorem `odel:thm:joint` and Section
`odel:sec:main`): the location lists and location oracles of `homData` depend on the stage but not
on the input. -/
theorem homData_locators_input_indep (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s)
    (p p' : Promised M n (2 ^ μ) × Fin (n + 4)) (hp : p.2 = p'.2) :
    (homData M n μ s hμ hμs).rowloc p = (homData M n μ s hμ hμs).rowloc p' ∧
      (homData M n μ s hμ hμs).colloc p = (homData M n μ s hμ hμs).colloc p' ∧
      (homData M n μ s hμ hμs).rowOracle p = (homData M n μ s hμ hμs).rowOracle p' ∧
      (homData M n μ s hμ hμs).columnOracle p = (homData M n μ s hμ hμs).columnOracle p' := by
  obtain ⟨x, k⟩ := p
  obtain ⟨x', k'⟩ := p'
  dsimp only at hp
  subst hp
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **Exact complex dyadic entries** (the construction before Theorem `odel:thm:joint` and
Proposition `odel:rem:homogeneous`): every sampled entry is `c · v/2^μ` with a unit
`c ∈ {1, -1, i, -i}` and an integer `-2^μ < v ≤ 2^μ`. -/
theorem homData_dyadic (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s)
    (p : Promised M n (2 ^ μ) × Fin (n + 4)) (i i' : HomIndex M μ s) :
    ∃ c : ℂ, ∃ v : ℤ, (c = 1 ∨ c = -1 ∨ c = Complex.I ∨ c = -Complex.I) ∧
      -(2 : ℤ) ^ μ < v ∧ v ≤ 2 ^ μ ∧
      (homData M n μ s hμ hμs).matrix p i i' = c * ((v : ℂ) / 2 ^ μ) := by
  rw [← (homData M n μ s hμ hμs).decoded p i i']
  have hb := homTable_word_mem (M := M) (s := s) hμ p.2 (i, i')
    ((homTable M n μ s p.2).bit (homBits p.1 p.2) (i, i'))
  refine ⟨homPhase (i, i'), _, ?_, hb.1, hb.2, ?_⟩
  · unfold homPhase
    split_ifs <;> simp
  · show homPhase (i, i') * Hamiltonian.wordDecode μ
        ((((homTable M n μ s p.2).value (homBits p.1 p.2) (i, i') : ℤ)) : Hamiltonian.Word μ) = _
    rw [Hamiltonian.BitTable.value, Hamiltonian.wordDecode_intCast _ hb.1 hb.2]

/-! ### The family -/

/-- The stage durations are nonnegative when the busy time fits in `[0, T]`. -/
theorem homLen_nonneg {T : ℝ} (hT : homBusy M n ≤ T) (k : Fin (n + 4)) : 0 ≤ homLen M n T k := by
  unfold homLen
  have := pulseLen_nonneg n
  have := homD_nonneg M
  split_ifs <;> linarith [Real.pi_pos]

/-- **The homogeneous family** (Proposition `odel:rem:homogeneous`): `n` hidden stages, the merged
phase pulse, the `Y` pulse, the dissipation and the idle stage, on `[0, T]`; no source (`b = 0`),
start `x₀ = |+⟩ ⊗ u_M ⊗ ω`. -/
def homFamily (M n μ s : ℕ) (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : homBusy M n ≤ T) :
    Family (Promised M n (2 ^ μ)) (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4) s where
  data := homData M n μ s hμ hμs
  len := homLen M n T
  len_nonneg := homLen_nonneg hT
  src _ := 0
  init := homInit M μ s

variable {hμ : 1 ≤ μ} {hμs : 2 ^ μ ≤ s} {T : ℝ} {hT : homBusy M n ≤ T}

/-- **The family is homogeneous** (Proposition `odel:rem:homogeneous`: `b = 0`): every stage source
vanishes. -/
theorem homFamily_src (k : Fin (n + 4)) : (homFamily M n μ s hμ hμs T hT).src k = 0 := rfl

/-- The stage lengths of `homFamily` indexed by naturals. -/
theorem homFamily_lenNat {i : ℕ} (hi : i < n + 4) :
    (homFamily M n μ s hμ hμs T hT).lenNat i = homLen M n T ⟨i, hi⟩ :=
  dif_pos hi

/-- `B = ‖x₀‖`: the mass of a homogeneous family. -/
theorem homFamily_mass : (homFamily M n μ s hμ hμs T hT).mass = ‖homInit M μ s‖ := by
  simp [Family.mass, homFamily]

/-- The hidden stage `i ≤ n` starts at `iπ/2`. -/
theorem homFamily_start_hidden {i : ℕ} (hi : i ≤ n) :
    (homFamily M n μ s hμ hμs T hT).start i = i * (Real.pi / 2) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Family.start_succ, ih (by omega), homFamily_lenNat (by omega), homLen,
      if_pos (by simp; omega)]
    push_cast
    ring

/-- The `Y` pulse starts at `nπ/2 + pulseLen n`. -/
theorem homFamily_start_y :
    (homFamily M n μ s hμ hμs T hT).start (n + 1) = n * (Real.pi / 2) + pulseLen n := by
  rw [Family.start_succ, homFamily_start_hidden le_rfl, homFamily_lenNat (by omega), homLen,
    if_neg (by simp), if_pos (by simp)]

/-- The dissipation starts at `nπ/2 + pulseLen n + π/4`. -/
theorem homFamily_start_damp :
    (homFamily M n μ s hμ hμs T hT).start (n + 2) =
      n * (Real.pi / 2) + pulseLen n + Real.pi / 4 := by
  rw [Family.start_succ, homFamily_start_y, homFamily_lenNat (by omega), homLen,
    if_neg (by simp), if_neg (by simp), if_pos (by simp)]

/-- The idle stage starts at the busy time. -/
theorem homFamily_start_idle : (homFamily M n μ s hμ hμs T hT).start (n + 3) = homBusy M n := by
  rw [Family.start_succ, homFamily_start_damp, homFamily_lenNat (by omega), homLen,
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (by simp), homBusy]

/-- The family ends at `T` (`F.T = T`); with `T = τ` this is the proof of Proposition
`odel:rem:homogeneous`, "Known idle intervals make `T = τ` exactly". -/
theorem homFamily_T : (homFamily M n μ s hμ hμs T hT).T = T := by
  rw [Family.T_eq_start, Family.start_succ, homFamily_start_idle, homFamily_lenNat (by omega),
    homLen, if_neg (by simp), if_neg (by simp), if_neg (by simp), if_neg (by simp)]
  ring

end

end ODELowerBoundExtensions.Homogeneous
