import DeferredMeasurementLowerBounds.Deferral.Schedule

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Aligned merge of schedules

The deferral of an instrument (proof of Lemma `qlsl:lem:xor`: "padding to their worst-case
query count") merges the schedules of its continuations. Each continuation acts on its own sector of
the first record register (`liftProgram`): a known unitary controlled by the record is unitary
(`conj_masked_unitary`) and lifting keeps the weight (`cost_liftProgram`).

The schedules of the subtrees are aligned slot by slot (`align`): the `j`-th counted calls of all
branches form one pattern, and a branch with fewer counted calls has no call in the later slots
(padding, `slotPad`, `segPad`). The merged program acts on the sector of outcome `j` as the
program of the `j`-th subtree (`eval_align`), and the number of slots is the largest number of
slots of a subtree (`len_align`).
-/

namespace DeferredMeasurementLowerBounds.Deferral

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

namespace Sched

variable {O : L → X → K →L[ℂ] K} {counted : L → Prop}

variable {W k : ℕ}

/-- A known unitary controlled by the first record register is unitary. -/
theorem conj_masked_unitary (v : Option (Fin W)) {U : Joint (Rec W k) K →L[ℂ] Joint (Rec W k) K}
    (hU : IsUnitary U) :
    IsUnitary ((split W k K).symm.conjStarAlgEquiv
      (MaskedProgram.masked (fun v' => decide (v' = v)) U)) :=
  (MaskedProgram.masked_unitary _ U hU).transport _

/-- A program acting on the records whose first register holds `v`. -/
def liftProgram (v : Option (Fin W)) :
    MultiOracleCircuit.Program (selFamily O counted (Rec W k)) →
      MultiOracleCircuit.Program (selFamily O counted (Rec W (k + 1)))
  | .fixed _ hU => .fixed _ (conj_masked_unitary v hU)
  | .query c => .query (liftLabel v c)
  | .queryAdjoint c => .queryAdjoint (liftLabel v c)
  | .seq p q => .seq (liftProgram v p) (liftProgram v q)

/-- The lifted program is the program controlled by the first register. -/
theorem eval_liftProgram (v : Option (Fin W))
    (p : MultiOracleCircuit.Program (selFamily O counted (Rec W k))) (x : X) :
    (liftProgram v p).eval x = (split W k K).symm.conjStarAlgEquiv
      (MaskedProgram.masked (fun v' => decide (v' = v)) (p.eval x)) := by
  induction p with
  | fixed U hU => rfl
  | query c => exact selFamily_liftLabel O counted v c x
  | queryAdjoint c =>
    change star (selFamily O counted (Rec W (k + 1)) (liftLabel v c) x) = _
    rw [selFamily_liftLabel, ← map_star, MultiOracleCircuit.Program.eval_queryAdjoint,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
      MaskedProgram.masked_adjoint]
  | seq p q hp hq =>
    simp only [liftProgram, MultiOracleCircuit.Program.eval_seq, hp, hq,
      MaskedProgram.masked_mul, map_mul]

/-- Lifting keeps the weight. -/
theorem cost_liftProgram (v : Option (Fin W))
    (p : MultiOracleCircuit.Program (selFamily O counted (Rec W k))) :
    (liftProgram v p).cost selWeight = p.cost selWeight := by
  induction p with
  | fixed U hU => rfl
  | query c => exact selWeight_liftLabel v c
  | queryAdjoint c => exact selWeight_liftLabel v c
  | seq p q hp hq => simp only [liftProgram, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- The segment `j` of a schedule, padded by the identity after the last segment. -/
def segPad {R : Type*} [Fintype R] (S : Sched O counted R) (j : ℕ) :
    MultiOracleCircuit.Program (selFamily O counted R) :=
  if j ≤ S.len then S.seg j else MultiOracleCircuit.Program.identity

/-- The slot `j` of a schedule, padded by the empty pattern after the last slot. -/
def slotPad {R : Type*} [Fintype R] (S : Sched O counted R) (j : ℕ) : Pat {l // counted l} R :=
  if j < S.len then S.slot j else fun _ => none

/-- The aligned slot: the record's first register selects the subtree. -/
def alignSlot {n : ℕ} (S : Fin n → Sched O counted (Rec W k)) (j : ℕ) :
    Pat {l // counted l} (Rec W (k + 1)) :=
  fun r => match r 0 with
    | none => none
    | some v => if h : v.val < n then slotPad (S ⟨v.val, h⟩) j (Fin.tail r) else none

/-- **Aligned merge** of the schedules of the outcomes `j < n ≤ W` of an instrument. -/
def align {n : ℕ} (hn : n ≤ W) (S : Fin n → Sched O counted (Rec W k)) :
    Sched O counted (Rec W (k + 1)) where
  len := Finset.univ.sup fun i => (S i).len
  seg j := seqAll (List.ofFn fun i : Fin n => liftProgram (some (Fin.castLE hn i)) (segPad (S i) j))
  slot j := alignSlot S j
  seg_free j := by
    rw [cost_seqAll]
    apply List.sum_eq_zero
    intro c hc
    simp only [List.map_ofFn, List.mem_ofFn, Function.comp_apply] at hc
    obtain ⟨i, rfl⟩ := hc
    rw [cost_liftProgram]
    unfold segPad
    split_ifs
    · exact (S i).seg_free j
    · rfl

/-- The aligned merge has as many slots as its longest schedule. -/
theorem len_align {n : ℕ} (hn : n ≤ W) (S : Fin n → Sched O counted (Rec W k)) :
    (align hn S).len = Finset.univ.sup fun i => (S i).len := rfl

/-! ### Evaluation of the aligned merge -/

/-- The family on the first record register that applies `F i` at the value `some i` of an
outcome `i < n` and the identity at the fresh value and at values that are not outcomes. -/
def sect {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}
    (F : Fin n → H →L[ℂ] H) : Option (Fin W) → H →L[ℂ] H
  | none => 1
  | some v => if h : v.val < n then F ⟨v.val, h⟩ else 1

omit [InnerProductSpace ℂ K] [CompleteSpace K] in
/-- The sector family is multiplicative. -/
theorem sect_mul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}
    (F G : Fin n → H →L[ℂ] H) (v : Option (Fin W)) :
    sect F v * sect G v = sect (fun i => F i * G i) v := by
  cases v with
  | none => exact mul_one 1
  | some v =>
    simp only [sect]
    split_ifs
    · rfl
    · exact mul_one 1

/-- A list product of factors all equal to one except possibly one is that factor. -/
theorem prod_ofFn_eq_single {M : Type*} [Monoid M] :
    ∀ {n : ℕ} (f : Fin n → M) (i₀ : Fin n), (∀ i, i ≠ i₀ → f i = 1) →
      (List.ofFn f).prod = f i₀
  | 0, _, i₀, _ => i₀.elim0
  | n + 1, f, i₀, hf => by
    rw [List.ofFn_succ, List.prod_cons]
    revert hf
    refine Fin.cases ?_ (fun j => ?_) i₀
    · intro hf
      rw [List.prod_eq_one, mul_one]
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hf _ (Fin.succ_ne_zero i)
    · intro hf
      rw [hf 0 (Fin.succ_ne_zero j).symm, one_mul]
      exact prod_ofFn_eq_single (fun i => f i.succ) j
        (fun i hi => hf _ (fun h => hi (Fin.succ_injective _ h)))

/-- Coordinates of an operator conjugated by the separation of the first register. -/
theorem conj_fiber_apply (F : Option (Fin W) → Joint (Rec W k) K →L[ℂ] Joint (Rec W k) K)
    (Ψ : Joint (Rec W (k + 1)) K) (v : Option (Fin W)) (r : Rec W k) :
    (split W k K).symm.conjStarAlgEquiv (Joint.fiber F) Ψ (Fin.cons v r) =
      F v (split W k K Ψ v) r := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
    ← split_apply, LinearIsometryEquiv.apply_symm_apply, Joint.fiber_apply]

/-- Products of conjugated fibers. -/
theorem prod_conj_fiber {n : ℕ}
    (G : Fin n → Option (Fin W) → Joint (Rec W k) K →L[ℂ] Joint (Rec W k) K) :
    (List.ofFn fun i => (split W k K).symm.conjStarAlgEquiv (Joint.fiber (G i))).prod =
      (split W k K).symm.conjStarAlgEquiv
        (Joint.fiber fun v => (List.ofFn fun i => G i v).prod) := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.prod_nil, Joint.fiber_one, map_one]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, ih, ← map_mul, Joint.fiber_mul]

/-- The product over the outcomes of the factors acting at one register value. -/
theorem prod_ofFn_ite {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ}
    (hn : n ≤ W) (F : Fin n → H →L[ℂ] H) (v : Option (Fin W)) :
    (List.ofFn fun i : Fin n => if v = some (Fin.castLE hn i) then F i else 1).prod =
      sect F v := by
  cases v with
  | none =>
    rw [List.prod_eq_one]
    · rfl
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp
  | some v =>
    simp only [sect]
    split_ifs with h
    · rw [prod_ofFn_eq_single _ ⟨v.val, h⟩]
      · exact if_pos (congrArg some (Fin.ext rfl))
      · intro i hi
        rw [if_neg]
        intro hv
        exact hi (Fin.ext (by simpa using (congrArg Fin.val (Option.some_injective _ hv)).symm))
    · rw [List.prod_eq_one]
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      rw [if_neg]
      intro hv
      exact h (by rw [Option.some_injective _ hv]; exact i.isLt)

/-- A merged free segment acts on the sector of outcome `i` as the padded segment of the `i`-th
schedule. -/
theorem eval_align_seg {n : ℕ} (hn : n ≤ W) (S : Fin n → Sched O counted (Rec W k)) (j : ℕ)
    (x : X) : ((align hn S).seg j).eval x = (split W k K).symm.conjStarAlgEquiv
      (Joint.fiber (sect fun i => (segPad (S i) j).eval x)) := by
  change (seqAll (List.ofFn fun i : Fin n =>
    liftProgram (some (Fin.castLE hn i)) (segPad (S i) j))).eval x = _
  rw [eval_seqAll, List.map_ofFn]
  simp only [Function.comp_def, eval_liftProgram, masked_eq_fiber, decide_eq_true_eq]
  rw [prod_conj_fiber]
  congr 2
  funext v
  exact prod_ofFn_ite hn _ v

/-- A merged slot acts on the sector of outcome `i` as the padded slot of the `i`-th schedule. -/
theorem selFamily_alignSlot {n : ℕ} (S : Fin n → Sched O counted (Rec W k)) (j : ℕ) (x : X) :
    selFamily O counted (Rec W (k + 1)) (.inl (alignSlot S j)) x =
      (split W k K).symm.conjStarAlgEquiv (Joint.fiber
        (sect fun i => selFamily O counted (Rec W k) (.inl (slotPad (S i) j)) x)) := by
  ext Ψ r : 2
  obtain ⟨v, r, rfl⟩ : ∃ v r', r = Fin.cons v r' :=
    ⟨r 0, Fin.tail r, (Fin.cons_self_tail r).symm⟩
  rw [conj_fiber_apply]
  change callOpt _ (alignSlot S j (Fin.cons v r)) x (Ψ (Fin.cons v r)) = _
  cases v with
  | none =>
    change callOpt _ none x _ = (1 : Joint (Rec W k) K →L[ℂ] Joint (Rec W k) K) _ r
    rw [one_apply_eq_self, split_apply]
    rfl
  | some v =>
    simp only [alignSlot, Fin.cons_zero, Fin.tail_cons, sect]
    split_ifs
    · change _ = callOpt _ _ x _
      exact congrArg _ (split_apply W k Ψ (some v) r).symm
    · change callOpt _ none x _ = (1 : Joint (Rec W k) K →L[ℂ] Joint (Rec W k) K) _ r
      rw [one_apply_eq_self, split_apply]
      rfl

/-- The padded evaluation of a schedule up to segment `j`. -/
def padEval {R : Type*} [Fintype R] (S : Sched O counted R) (x : X) :
    ℕ → (Joint R K →L[ℂ] Joint R K)
  | 0 => (segPad S 0).eval x
  | j + 1 => (segPad S (j + 1)).eval x *
      (selFamily O counted R (.inl (slotPad S j)) x * padEval S x j)

/-- Up to the last segment the padded evaluation is the evaluation. -/
theorem padEval_eq_go {R : Type*} [Fintype R] (S : Sched O counted R) (x : X) :
    ∀ j, j ≤ S.len → padEval S x j = (S.go j).eval x := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [padEval, segPad, if_pos (Nat.zero_le _), go]
  | succ j ih =>
    intro hj
    simp only [padEval, segPad, slotPad, if_pos hj, if_pos (Nat.lt_of_succ_le hj),
      ih (Nat.le_of_succ_le hj), go, MultiOracleCircuit.Program.eval_seq,
      MultiOracleCircuit.Program.eval_query]

/-- After the last segment the padded evaluation is the program. -/
theorem padEval_eq_prog {R : Type*} [Fintype R] (S : Sched O counted R) (x : X) (j : ℕ)
    (hj : S.len ≤ j) : padEval S x j = S.prog.eval x := by
  induction j, hj using Nat.le_induction with
  | base => exact padEval_eq_go S x _ le_rfl
  | succ j hj ih =>
    have h1 : ¬ j + 1 ≤ S.len := by omega
    have h2 : ¬ j < S.len := by omega
    have h3 : selFamily O counted R (.inl (fun _ => none)) x = 1 := by
      change Joint.fiber (fun _ => (1 : K →L[ℂ] K)) = 1
      exact Joint.fiber_one
    simp only [padEval, segPad, slotPad, if_neg h1, if_neg h2, h3, ih,
      MultiOracleCircuit.Program.eval_identity, one_mul]

/-- The merged program up to segment `j` acts on each sector as the padded evaluation. -/
theorem eval_align_go {n : ℕ} (hn : n ≤ W) (S : Fin n → Sched O counted (Rec W k)) (x : X) :
    ∀ j, ((align hn S).go j).eval x = (split W k K).symm.conjStarAlgEquiv
      (Joint.fiber (sect fun i => padEval (S i) x j)) := by
  intro j
  induction j with
  | zero => exact eval_align_seg hn S 0 x
  | succ j ih =>
    change ((align hn S).seg (j + 1)).eval x * (selFamily O counted (Rec W (k + 1))
      (.inl (alignSlot S j)) x * ((align hn S).go j).eval x) = _
    rw [eval_align_seg, selFamily_alignSlot, ih, ← map_mul, ← map_mul, Joint.fiber_mul,
      Joint.fiber_mul]
    congr 2
    funext v
    rw [sect_mul, sect_mul]
    rfl

/-- **The merged program acts on the sector of outcome `j` as the `j`-th schedule** and as the
identity on the fresh value and on values that are not outcomes. -/
theorem eval_align {n : ℕ} (hn : n ≤ W) (S : Fin n → Sched O counted (Rec W k)) (x : X) :
    (align hn S).prog.eval x = (split W k K).symm.conjStarAlgEquiv
      (Joint.fiber fun v : Option (Fin W) => match v with
        | none => 1
        | some v => if h : v.val < n then (S ⟨v.val, h⟩).prog.eval x else 1) := by
  rw [show (align hn S).prog = (align hn S).go (align hn S).len from rfl, eval_align_go]
  congr 2
  funext v
  cases v with
  | none => rfl
  | some v =>
    simp only [sect]
    split_ifs with h
    · exact padEval_eq_prog _ x _ (Finset.le_sup (f := fun i => (S i).len) (Finset.mem_univ _))
    · rfl

end Sched

end

end DeferredMeasurementLowerBounds.Deferral
