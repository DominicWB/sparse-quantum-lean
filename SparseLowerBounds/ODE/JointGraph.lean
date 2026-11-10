import SparseLowerBounds.Helpers.Ode.OuterGraph.Halves

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The outer adversary matrix of the joint search-parity problem

Manuscript: the proof of Lemma `odel:lem:outer`. On promised
inputs (`ODE/Promise`), `Γ x x' = 1` (`outerGamma`, `OuterAdj`) when the unique
odd candidates `a = a_*(x)` and `b = a_*(x')` lie in opposite halves (`OppHalf`,
`Helpers/Ode/OuterGraph/Halves`), blocks
`a` and `b` each change along one edge of the inner parity graph
(`Helpers/Ode/OuterGraph/InnerGraph`), and all other blocks agree. With `M`, `m` even and
`d = n (m/2)`:

* `Γ` is nonnegative and symmetric, and joins only inputs with opposite answers
  (`halfSign_oddCand_of_outerGamma_ne_zero`);
* every row sum is at least `D = (M/2) d²` (`outerDeg_le_sum_outerGamma`,
  eq. `odel:eq:outerdegree`): the neighbours of `x` are the triples
  `(b, e₁, e₂)` (`mkNbr`);
* every masked `Γ ∘ Δ_{c,k,z}` has a Schur certificate with constant
  `λ = √(M/2) d √(m/2)` (`outer_schurCert`, eq. `odel:eq:outermask`), with
  weights `μ x = (√(M/2) if a_*(x) = c) (√(m/2) if j_{ck} = z)`
  (`certWeight`). A surviving masked edge changes block `c` at coordinate `k`
  with one endpoint equal to `z` (`survivor`), so the row sums are the four star
  counts of the paper's block-star argument.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open Finset

variable {M n m : ℕ}

/-! ### The outer adjacency -/

/-- **The outer graph** (proof of Lemma `odel:lem:outer`): the odd candidate moves from `a` to
`b` across the halves, blocks `a` and `b` each change along an inner edge, and
all other blocks agree. -/
def OuterAdj (x x' : Promised M n m) : Prop :=
  OppHalf M (oddCand x) (oddCand x') ∧ InnerAdj (x.1 (oddCand x)) (x'.1 (oddCand x)) ∧
    InnerAdj (x.1 (oddCand x')) (x'.1 (oddCand x')) ∧
    ∀ c, c ≠ oddCand x → c ≠ oddCand x' → x.1 c = x'.1 c

instance (x x' : Promised M n m) : Decidable (OuterAdj x x') := by
  unfold OuterAdj; infer_instance

/-- **The outer adversary matrix** `Γ` (proof of Lemma `odel:lem:outer`), with `0/1` entries. -/
def outerGamma (x x' : Promised M n m) : ℝ := if OuterAdj x x' then 1 else 0

theorem OuterAdj.symm {x x' : Promised M n m} (h : OuterAdj x x') : OuterAdj x' x :=
  ⟨h.1.symm, h.2.2.1.symm, h.2.1.symm, fun c hc hc' => (h.2.2.2 c hc' hc).symm⟩

theorem outerGamma_nonneg (x x' : Promised M n m) : 0 ≤ outerGamma x x' := by
  unfold outerGamma; split_ifs <;> norm_num

theorem outerGamma_symm (x x' : Promised M n m) : outerGamma x x' = outerGamma x' x := by
  unfold outerGamma
  by_cases h : OuterAdj x x'
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun h' => h h'.symm]

theorem outerAdj_of_outerGamma_ne_zero {x x' : Promised M n m} (h : outerGamma x x' ≠ 0) :
    OuterAdj x x' := by
  by_contra h'; exact h (if_neg h')

/-- `Γ` joins only inputs with opposite answers (`ans x' = -ans x`). -/
theorem halfSign_oddCand_of_outerGamma_ne_zero (x x' : Promised M n m)
    (h : outerGamma x x' ≠ 0) : halfSign M (oddCand x') = -halfSign M (oddCand x) :=
  halfSign_of_oppHalf (outerAdj_of_outerGamma_ne_zero h).1

/-- Two neighbours of `x` with the same odd candidate and the same two changed
blocks are equal. -/
theorem OuterAdj.ext {x x' x'' : Promised M n m} (h' : OuterAdj x x') (h'' : OuterAdj x x'')
    (hb : oddCand x' = oddCand x'') (ha : x'.1 (oddCand x) = x''.1 (oddCand x))
    (hbb : x'.1 (oddCand x') = x''.1 (oddCand x'')) : x' = x'' := by
  apply Subtype.ext
  funext c
  by_cases hca : c = oddCand x
  · rw [hca]; exact ha
  by_cases hcb : c = oddCand x'
  · rw [hcb]
    calc x'.1 (oddCand x') = x''.1 (oddCand x'') := hbb
      _ = x''.1 (oddCand x') := by rw [hb]
  · rw [← h'.2.2.2 c hca hcb, h''.2.2.2 c hca (hb ▸ hcb)]

/-! ### Neighbours as triples -/

/-- The positions obtained from `x` by replacing block `a_*(x)` by `e₁` and
block `b` by `e₂`. -/
def nbr (x : Promised M n m) (b : Fin M) (e₁ e₂ : Fin n → Fin m) : Positions M n m :=
  Function.update (Function.update x.1 (oddCand x) e₁) b e₂

theorem nbr_self (x : Promised M n m) (b : Fin M) (e₁ e₂ : Fin n → Fin m) :
    nbr x b e₁ e₂ b = e₂ := Function.update_self _ _ _

theorem nbr_old (x : Promised M n m) {b : Fin M} (hb : b ≠ oddCand x) (e₁ e₂ : Fin n → Fin m) :
    nbr x b e₁ e₂ (oddCand x) = e₁ := by
  unfold nbr; rw [Function.update_of_ne hb.symm, Function.update_self]

theorem nbr_other (x : Promised M n m) {b c : Fin M} (hc : c ≠ oddCand x) (hcb : c ≠ b)
    (e₁ e₂ : Fin n → Fin m) : nbr x b e₁ e₂ c = x.1 c := by
  unfold nbr; rw [Function.update_of_ne hcb, Function.update_of_ne hc]

/-- A triple `(b, e₁, e₂)` is a neighbour of `x`: `b` in the opposite half,
`e₁` an inner neighbour of block `a_*(x)`, `e₂` an inner neighbour of block `b`. -/
def ValidTriple (x : Promised M n m) (t : Fin M × (Fin n → Fin m) × (Fin n → Fin m)) : Prop :=
  OppHalf M (oddCand x) t.1 ∧ InnerAdj (x.1 (oddCand x)) t.2.1 ∧ InnerAdj (x.1 t.1) t.2.2

instance (x : Promised M n m) : DecidablePred (ValidTriple x) := fun t => by
  unfold ValidTriple; infer_instance

/-- The parities of blocks `a_*(x)` and `b` flip, so `b` is the unique odd
candidate of the neighbour. -/
theorem isOddCand_nbr_iff (x : Promised M n m) {t : Fin M × (Fin n → Fin m) × (Fin n → Fin m)}
    (ht : ValidTriple x t) (c : Fin M) : IsOddCand (nbr x t.1 t.2.1 t.2.2) c ↔ c = t.1 := by
  obtain ⟨hopp, h1, h2⟩ := ht
  have hb : t.1 ≠ oddCand x := hopp.ne
  have hodd := isOddCand_iff x
  unfold IsOddCand at hodd ⊢
  by_cases hcb : c = t.1
  · subst hcb
    rw [nbr_self]; simp only [iff_true]
    have hev : ¬ Odd (∑ k, (x.1 t.1 k : ℕ)) := fun h => hb ((hodd _).mp h)
    have := h2.sum_mod_ne
    rw [Nat.odd_iff] at hev ⊢; omega
  · simp only [hcb, iff_false]
    by_cases hca : c = oddCand x
    · rw [hca, nbr_old x hb]
      have hod : Odd (∑ k, (x.1 (oddCand x) k : ℕ)) := (hodd _).mpr rfl
      have := h1.sum_mod_ne
      rw [Nat.odd_iff] at hod ⊢; omega
    · rw [nbr_other x hca hcb]
      exact fun h => hca ((hodd c).mp h)

/-- The neighbour of `x` given by a valid triple (and `x` itself otherwise). -/
def mkNbr (x : Promised M n m) (t : Fin M × (Fin n → Fin m) × (Fin n → Fin m)) :
    Promised M n m :=
  if ht : ValidTriple x t then
    ⟨nbr x t.1 t.2.1 t.2.2, t.1, (isOddCand_nbr_iff x ht t.1).mpr rfl,
      fun c hc => (isOddCand_nbr_iff x ht c).mp hc⟩
  else x

theorem mkNbr_val {x : Promised M n m} {t} (ht : ValidTriple x t) :
    (mkNbr x t).1 = nbr x t.1 t.2.1 t.2.2 := by
  unfold mkNbr; rw [dif_pos ht]

theorem oddCand_mkNbr {x : Promised M n m} {t} (ht : ValidTriple x t) :
    oddCand (mkNbr x t) = t.1 :=
  ((isOddCand_iff (mkNbr x t) t.1).mp
    (by rw [mkNbr_val ht]; exact (isOddCand_nbr_iff x ht t.1).mpr rfl)).symm

theorem outerAdj_mkNbr {x : Promised M n m} {t} (ht : ValidTriple x t) :
    OuterAdj x (mkNbr x t) := by
  have hb := oddCand_mkNbr ht
  have hv := mkNbr_val ht
  obtain ⟨hopp, h1, h2⟩ := ht
  refine ⟨by rw [hb]; exact hopp, ?_, ?_, ?_⟩
  · rw [hv, nbr_old x hopp.ne]; exact h1
  · rw [hb, hv, nbr_self]; exact h2
  · intro c hca hcb
    rw [hb] at hcb
    rw [hv, nbr_other x hca hcb]

/-! ### Degree -/

/-- The degree bound `D = (M/2) d²`, `d = n (m/2)` (eq. `odel:eq:outerdegree`). -/
def outerDeg (M n m : ℕ) : ℝ := ((M / 2 : ℕ) : ℝ) * ((n * (m / 2) : ℕ) : ℝ) ^ 2

/-- **Minimum degree** (eq. `odel:eq:outerdegree`): every row sum of `Γ` is at
least `(M/2) d²` (in fact equal). -/
theorem outerDeg_le_sum_outerGamma (hMe : Even M) (hme : Even m) (x : Promised M n m) :
    outerDeg M n m ≤ ∑ x', outerGamma x x' := by
  have hsum := sum_triple_ite (OppHalf M (oddCand x)) (InnerAdj (x.1 (oddCand x)))
    (fun b => InnerAdj (x.1 b)) (1 : ℝ)
  have hcalc : (∑ b, if OppHalf M (oddCand x) b then
      ((univ.filter (InnerAdj (x.1 (oddCand x)))).card : ℝ) *
        (univ.filter (InnerAdj (x.1 b))).card * 1 else 0) = outerDeg M n m := by
    simp_rw [card_innerAdj hme]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_oppHalf hMe, outerDeg]
    ring
  rw [← hcalc, ← hsum]
  refine sum_le_sum_of_injOn_support _ (outerGamma x) (mkNbr x) ?_ ?_
    (outerGamma_nonneg x)
  · rintro ⟨b, e₁, e₂⟩ ⟨b', e₁', e₂'⟩ ht ht' heq
    have hv : ValidTriple x (b, e₁, e₂) := by by_contra h; exact ht (if_neg h)
    have hv' : ValidTriple x (b', e₁', e₂') := by by_contra h; exact ht' (if_neg h)
    have h1 := congrArg oddCand heq
    rw [oddCand_mkNbr hv, oddCand_mkNbr hv'] at h1
    simp only at h1
    subst h1
    have h2 := congrArg (fun y : Promised M n m => y.1 (oddCand x)) heq
    have h3 := congrArg (fun y : Promised M n m => y.1 b) heq
    simp only [mkNbr_val hv, mkNbr_val hv'] at h2 h3
    rw [nbr_old x hv.1.ne, nbr_old x hv'.1.ne] at h2
    rw [nbr_self, nbr_self] at h3
    rw [h2, h3]
  · rintro t ht
    have hv : ValidTriple x t := by by_contra h; exact ht (if_neg h)
    rw [outerGamma, if_pos (outerAdj_mkNbr hv)]; exact (if_pos hv).le

/-! ### Schur certificates for the masked matrices -/

/-- The certificate constant `λ = √(M/2) d √(m/2)`, `d = n (m/2)`, of
eq. `odel:eq:outermask`. -/
def outerLam (M n m : ℕ) : ℝ :=
  Real.sqrt ((M / 2 : ℕ) : ℝ) * ((n * (m / 2) : ℕ) : ℝ) * Real.sqrt ((m / 2 : ℕ) : ℝ)

theorem outerLam_nonneg : 0 ≤ outerLam M n m := by unfold outerLam; positivity

/-- The Schur weights for the query `(c, k, z)`: `√(M/2)` on the sector whose
odd candidate is `c`, times `√(m/2)` on the inputs with `j_{ck} = z` (the star
centres of the masked inner graph). -/
def certWeight (c : Fin M) (k : Fin n) (z : Fin m) (x : Promised M n m) : ℝ :=
  (if oddCand x = c then Real.sqrt ((M / 2 : ℕ) : ℝ) else 1) *
    (if x.1 c k = z then Real.sqrt ((m / 2 : ℕ) : ℝ) else 1)

theorem certWeight_pos (hM : 2 ≤ M) (hm : 2 ≤ m) (c : Fin M) (k : Fin n) (z : Fin m)
    (x : Promised M n m) : 0 < certWeight c k z x := by
  have hM' : (0 : ℝ) < ((M / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M / 2)
  have hm' : (0 : ℝ) < ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m / 2)
  unfold certWeight
  apply mul_pos
  · split_ifs
    · exact Real.sqrt_pos.mpr hM'
    · exact one_pos
  · split_ifs
    · exact Real.sqrt_pos.mpr hm'
    · exact one_pos

/-- A surviving entry of the masked matrix `Γ ∘ Δ_{c,k,z}` is an outer edge
whose endpoints answer the query `(c, k, z)` differently; its value is `1`. -/
theorem survivor {x x' : Promised M n m} {c : Fin M} {k : Fin n} {z : Fin m}
    (h : PositiveAdversary.masked outerGamma membership (c, k, z) x x' ≠ 0) :
    OuterAdj x x' ∧ (x.1 c k = z ↔ ¬ x'.1 c k = z) ∧
      PositiveAdversary.masked outerGamma membership (c, k, z) x x' = 1 := by
  unfold PositiveAdversary.masked at h ⊢
  by_cases hmem : membership x (c, k, z) = membership x' (c, k, z)
  · exact absurd (if_pos hmem) h
  · rw [if_neg hmem] at h ⊢
    have hadj := outerAdj_of_outerGamma_ne_zero h
    refine ⟨hadj, ?_, by rw [outerGamma, if_pos hadj]⟩
    simp only [membership, decide_eq_decide] at hmem
    tauto

/-- A surviving edge changes block `c`, so if `c` is not the odd candidate of
`x` it is the odd candidate of `x'`. -/
theorem oddCand_eq_of_changed {x x' : Promised M n m} {c : Fin M} {k : Fin n}
    (hadj : OuterAdj x x') (hne : x.1 c k ≠ x'.1 c k) (hca : oddCand x ≠ c) :
    oddCand x' = c := by
  by_contra hcb
  exact hne (by rw [hadj.2.2.2 c (Ne.symm hca) (Ne.symm hcb)])

/-- **Row sums through triples**: if every surviving neighbour `x'` of `x`
satisfies `P b`, `Q e₁`, `R b e₂` (with `b = a_*(x')`, `e₁`, `e₂` its blocks at
`a_*(x)` and `b`) and has weight at most `w`, the masked row sum is at most the
triple sum of `w [P ∧ Q ∧ R]`. -/
theorem masked_row_le_triple (c : Fin M) (k : Fin n) (z : Fin m) (x : Promised M n m)
    (P : Fin M → Prop) (Q : (Fin n → Fin m) → Prop) (R : Fin M → (Fin n → Fin m) → Prop)
    [DecidablePred P] [DecidablePred Q] [∀ b, DecidablePred (R b)] {w : ℝ} (hw : 0 ≤ w)
    (hsurv : ∀ x', OuterAdj x x' → (x.1 c k = z ↔ ¬ x'.1 c k = z) →
      P (oddCand x') ∧ Q (x'.1 (oddCand x)) ∧ R (oddCand x') (x'.1 (oddCand x')) ∧
        certWeight c k z x' ≤ w) :
    ∑ x', PositiveAdversary.masked outerGamma membership (c, k, z) x x' * certWeight c k z x' ≤
      ∑ t : Fin M × (Fin n → Fin m) × (Fin n → Fin m),
        (if P t.1 ∧ Q t.2.1 ∧ R t.1 t.2.2 then w else 0) := by
  refine sum_le_sum_of_injOn_support _ _
    (fun x' => (oddCand x', x'.1 (oddCand x), x'.1 (oddCand x'))) ?_ ?_ ?_
  · intro x' x'' h' h'' heq
    have s' := survivor (left_ne_zero_of_mul h')
    have s'' := survivor (left_ne_zero_of_mul h'')
    simp only [Prod.mk.injEq] at heq
    exact OuterAdj.ext s'.1 s''.1 heq.1 heq.2.1 heq.2.2
  · intro x' h'
    obtain ⟨hadj, hiff, h1⟩ := survivor (left_ne_zero_of_mul h')
    obtain ⟨hP, hQ, hR, hw'⟩ := hsurv x' hadj hiff
    rw [h1, one_mul]
    dsimp only
    rw [if_pos ⟨hP, hQ, hR⟩]
    exact hw'
  · intro t
    split_ifs
    · exact hw
    · exact le_rfl

theorem arith_center_same {a b A B D : ℝ} (ha : a ^ 2 = A) (hb : b ^ 2 = B) :
    A * B * D * 1 = a * D * b * (a * b) := by subst ha hb; ring

theorem arith_leaf_same {a b A D : ℝ} (ha : a ^ 2 = A) :
    A * 1 * D * b = a * D * b * (a * 1) := by subst ha; ring

theorem arith_center_opp {a b B D : ℝ} (hb : b ^ 2 = B) :
    1 * D * B * a = a * D * b * (1 * b) := by subst hb; ring

theorem arith_leaf_opp (a b D : ℝ) :
    1 * D * 1 * (a * b) = a * D * b * (1 * 1) := by ring

/-- **Schur certificates** (eq. `odel:eq:outermask`): for `M`,
`m` even, every masked matrix `Γ ∘ Δ_{c,k,z}` has a Schur certificate with
constant `λ = √(M/2) d √(m/2)`, weights `certWeight c k z`. The four row types
(odd candidate `c` or not, `j_{ck} = z` or not) are the centres and leaves of
the block star between sector `c` and the opposite-half sectors; their row sums
are at most (in fact equal to) `λ μ(x)`. -/
theorem outer_schurCert (hM : 2 ≤ M) (hMe : Even M) (hm : 2 ≤ m) (hme : Even m)
    (i : Fin M × Fin n × Fin m) :
    PositiveAdversary.SchurCert outerGamma membership i (outerLam M n m) := by
  obtain ⟨c, k, z⟩ := i
  refine ⟨certWeight c k z, certWeight_pos hM hm c k z, fun x => ?_⟩
  have hsM : Real.sqrt ((M / 2 : ℕ) : ℝ) ^ 2 = ((M / 2 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hsm : Real.sqrt ((m / 2 : ℕ) : ℝ) ^ 2 = ((m / 2 : ℕ) : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  have hcardc : (univ.filter (fun b : Fin M => b = c)).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => by
      rw [(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2]
  have hsM0 := Real.sqrt_nonneg ((M / 2 : ℕ) : ℝ)
  have hsm0 := Real.sqrt_nonneg ((m / 2 : ℕ) : ℝ)
  unfold outerLam
  by_cases hac : oddCand x = c
  · subst hac
    by_cases hz : x.1 (oddCand x) k = z
    · -- centre, odd candidate `c`: `(M/2) (m/2) d` neighbours of weight `1`
      subst hz
      refine (masked_row_le_triple _ k _ x (OppHalf M (oddCand x))
        (fun e => InnerAdj (x.1 (oddCand x)) e ∧ e k ≠ x.1 (oddCand x) k)
        (fun b => InnerAdj (x.1 b)) zero_le_one ?_).trans ?_
      · intro x' hadj hiff
        have hk : ¬ x'.1 (oddCand x) k = x.1 (oddCand x) k := hiff.mp rfl
        refine ⟨hadj.1, ⟨hadj.2.1, hk⟩, hadj.2.2.1, le_of_eq ?_⟩
        rw [certWeight, if_neg hadj.1.ne, if_neg hk, mul_one]
      · refine (sum_triple_ite_le _ _ _ zero_le_one (card_oppHalf hMe _).le
          (card_innerAdj_ne_le hme _ _) (fun b => (card_innerAdj hme _).le)).trans
          (le_of_eq ?_)
        rw [certWeight, if_pos rfl, if_pos rfl]
        exact arith_center_same hsM hsm
    · -- leaf, odd candidate `c`: `(M/2) d` neighbours of weight `√(m/2)`
      refine (masked_row_le_triple _ k z x (OppHalf M (oddCand x))
        (fun e => InnerAdj (x.1 (oddCand x)) e ∧ e k = z)
        (fun b => InnerAdj (x.1 b)) hsm0 ?_).trans ?_
      · intro x' hadj hiff
        have hk : x'.1 (oddCand x) k = z := by by_contra h; exact hz (hiff.mpr h)
        refine ⟨hadj.1, ⟨hadj.2.1, hk⟩, hadj.2.2.1, le_of_eq ?_⟩
        rw [certWeight, if_neg hadj.1.ne, if_pos hk, one_mul]
      · refine (sum_triple_ite_le _ _ _ hsm0 (card_oppHalf hMe _).le
          (card_innerAdj_eq_le _ hz) (fun b => (card_innerAdj hme _).le)).trans (le_of_eq ?_)
        rw [certWeight, if_pos rfl, if_neg hz, Nat.cast_one]
        exact arith_leaf_same hsM
  · by_cases hz : x.1 c k = z
    · -- centre, odd candidate `≠ c`: `d (m/2)` neighbours in sector `c`, weight `√(M/2)`
      subst hz
      refine (masked_row_le_triple c k _ x (fun b => b = c) (InnerAdj (x.1 (oddCand x)))
        (fun _ e => InnerAdj (x.1 c) e ∧ e k ≠ x.1 c k) hsM0 ?_).trans ?_
      · intro x' hadj hiff
        have hk : ¬ x'.1 c k = x.1 c k := hiff.mp rfl
        have hb : oddCand x' = c := oddCand_eq_of_changed hadj (Ne.symm hk) hac
        refine ⟨hb, hadj.2.1, ?_, le_of_eq ?_⟩
        · show InnerAdj (x.1 c) (x'.1 (oddCand x')) ∧ x'.1 (oddCand x') k ≠ x.1 c k
          have h2 := hadj.2.2.1
          rw [hb] at h2 ⊢
          exact ⟨h2, hk⟩
        · rw [certWeight, if_pos hb, if_neg hk, mul_one]
      · refine (sum_triple_ite_le _ _ _ hsM0 hcardc (card_innerAdj hme _).le
          (fun _ => card_innerAdj_ne_le hme _ _)).trans (le_of_eq ?_)
        rw [certWeight, if_neg hac, if_pos rfl, Nat.cast_one]
        exact arith_center_opp hsm
    · -- leaf, odd candidate `≠ c`: `d` neighbours of weight `√(M/2) √(m/2)`
      refine (masked_row_le_triple c k z x (fun b => b = c) (InnerAdj (x.1 (oddCand x)))
        (fun _ e => InnerAdj (x.1 c) e ∧ e k = z) (mul_nonneg hsM0 hsm0) ?_).trans ?_
      · intro x' hadj hiff
        have hk : x'.1 c k = z := by by_contra h; exact hz (hiff.mpr h)
        have hb : oddCand x' = c := oddCand_eq_of_changed hadj (by rw [hk]; exact hz) hac
        refine ⟨hb, hadj.2.1, ?_, le_of_eq ?_⟩
        · show InnerAdj (x.1 c) (x'.1 (oddCand x')) ∧ x'.1 (oddCand x') k = z
          have h2 := hadj.2.2.1
          rw [hb] at h2 ⊢
          exact ⟨h2, hk⟩
        · rw [certWeight, if_pos hb, if_pos hk]
      · refine (sum_triple_ite_le _ _ _ (mul_nonneg hsM0 hsm0) hcardc
          (card_innerAdj hme _).le (fun _ => card_innerAdj_eq_le _ hz)).trans (le_of_eq ?_)
        rw [certWeight, if_neg hac, if_neg hz, Nat.cast_one]
        exact arith_leaf_opp _ _ _

end

end SparseLowerBounds.ODE
end
