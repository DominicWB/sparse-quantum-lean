import SparseHamiltonian.ParallelOracle

/-!
# Explicit local schedule for coherent reuse

The finite reuse map is a chronological composition of one local interaction
per public slot. Coordinate insertion and projection are fixed independently
of the four blocks of the local interaction.
-/

namespace SparseHamiltonian.ReuseSchedule

noncomputable section

open ContinuousLinearMap
open ChronologicalResolvent FiniteChronologicalInverse ChronologicalCatalyst
open GlobalColligation CoherentReuse
open scoped BigOperators InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

abbrev Space (n : ℕ) (P V : Type*) [NormedAddCommGroup P]
    [NormedAddCommGroup V] := WithLp 2 (V × BlockOperator.H n P)

/-- Extract the shared register and one public coordinate. -/
def slotProjection {n : ℕ} (r : Fin n) :
    Space n P V →L[ℂ] WithLp 2 (V × P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ V P).symm.toContinuousLinearMap ∘L
    (WithLp.fstL 2 ℂ V (BlockOperator.H n P)).prod
      (PiLp.proj 2 (fun _ : Fin n => P) r ∘L WithLp.sndL 2 ℂ V (BlockOperator.H n P))

/-- Insert a selected public coordinate, leaving the remaining slots zero. -/
def slotEmbedding {n : ℕ} (r : Fin n) :
    WithLp 2 (V × P) →L[ℂ] Space n P V :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ V (BlockOperator.H n P)).symm.toContinuousLinearMap ∘L
    (WithLp.fstL 2 ℂ V P).prod
      ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => P)).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi (fun j : Fin n =>
          if j = r then WithLp.sndL 2 ℂ V P else 0))

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem slotProjection_apply {n : ℕ} (r : Fin n) (x : Space n P V) :
    slotProjection r x = WithLp.toLp 2 (x.fst, x.snd r) := rfl

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem slotEmbedding_fst {n : ℕ} (r : Fin n) (x : WithLp 2 (V × P)) :
    (slotEmbedding r x).fst = x.fst := rfl

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem slotEmbedding_snd {n : ℕ} (r j : Fin n) (x : WithLp 2 (V × P)) :
    (slotEmbedding r x).snd j = if j = r then x.snd else 0 := by
  change (if j = r then WithLp.sndL 2 ℂ V P else (0 : WithLp 2 (V × P) →L[ℂ] P)) x = _
  split_ifs <;> rfl

/-- Insertion and extraction are actual Hilbert adjoints. -/
theorem slotEmbedding_adjoint {n : ℕ} (r : Fin n) :
    (slotEmbedding r : WithLp 2 (V × P) →L[ℂ] Space n P V)† = slotProjection r := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [adjoint_inner_left, slotProjection_apply]
  change inner ℂ x.fst y.fst + (∑ j : Fin n, inner ℂ (x.snd j) ((slotEmbedding r y).snd j)) =
    inner ℂ x.fst y.fst + inner ℂ (x.snd r) y.snd
  simp_rw [slotEmbedding_snd]
  congr 1
  rw [Finset.sum_eq_single r]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

/-- The coordinate embedding is isometric. -/
theorem slotEmbedding_adjoint_comp {n : ℕ} (r : Fin n) :
    (slotEmbedding r : WithLp 2 (V × P) →L[ℂ] Space n P V)† ∘L slotEmbedding r = 1 := by
  rw [slotEmbedding_adjoint]
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · rfl
  · simp

/-- Lift one use of the local block to a chosen public slot. -/
def slotInteraction (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) {n : ℕ} (r : Fin n) :
    Space n P V →L[ℂ] Space n P V :=
  1 + slotEmbedding r ∘L (blockMap D C B A - 1) ∘L slotProjection r

/-- One interaction is the local block on the embedded subspace and identity
on its orthogonal complement. -/
theorem slotInteraction_eq_lift (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) {n : ℕ} (r : Fin n) :
    slotInteraction A B C D r =
      1 + slotEmbedding r ∘L (blockMap D C B A - 1) ∘L (slotEmbedding r)† := by
  rw [slotEmbedding_adjoint]
  rfl

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem slotInteraction_fst (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) {n : ℕ} (r : Fin n) (x : Space n P V) :
    (slotInteraction A B C D r x).fst = D x.fst + C (x.snd r) := by
  change x.fst + ((D x.fst + C (x.snd r)) - x.fst) = _
  abel

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem slotInteraction_snd (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) {n : ℕ} (r j : Fin n) (x : Space n P V) :
    (slotInteraction A B C D r x).snd j =
      if j = r then A (x.snd r) + B x.fst else x.snd j := by
  change x.snd j + (slotEmbedding r ((blockMap D C B A - 1) (slotProjection r x))).snd j = _
  rw [slotEmbedding_snd]
  split_ifs with h
  · subst j
    change x.snd r + ((B x.fst + A (x.snd r)) - x.snd r) = _
    abel
  · exact add_zero _

omit [CompleteSpace P] [CompleteSpace V] in
/-- The lifted interaction preserves the norm by the local energy law. -/
theorem slotInteraction_norm (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    {n : ℕ} (r : Fin n) (x : Space n P V) :
    ‖slotInteraction A B C D r x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  have hin := Finset.add_sum_erase Finset.univ
    (fun j : Fin n => ‖x.snd j‖ ^ 2) (Finset.mem_univ r)
  have hout := Finset.add_sum_erase Finset.univ
    (fun j : Fin n => ‖(slotInteraction A B C D r x).snd j‖ ^ 2) (Finset.mem_univ r)
  have hrest : (∑ j ∈ Finset.univ.erase r, ‖(slotInteraction A B C D r x).snd j‖ ^ 2) =
      ∑ j ∈ Finset.univ.erase r, ‖x.snd j‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [slotInteraction_snd, if_neg (Finset.mem_erase.mp hj).1]
  rw [← hin, ← hout, hrest, slotInteraction_fst, slotInteraction_snd, if_pos rfl]
  linarith [hStep (x.snd r) x.fst]

/-- Each scheduled interaction is an isometry. -/
theorem slotInteraction_adjoint_comp (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    {n : ℕ} (r : Fin n) :
    (slotInteraction A B C D r)† ∘L slotInteraction A B C D r = 1 :=
  (slotInteraction A B C D r).norm_map_iff_adjoint_comp_self.mp
    (slotInteraction_norm A B C D hStep r)

/-- In finite dimensions each scheduled interaction is two-sided unitary. -/
theorem slotInteraction_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    {n : ℕ} (r : Fin n) :
    (slotInteraction A B C D r)† ∘L slotInteraction A B C D r = 1 ∧
      slotInteraction A B C D r ∘L (slotInteraction A B C D r)† = 1 :=
  ⟨slotInteraction_adjoint_comp A B C D hStep r,
    coisometry_of_norm_preserving (slotInteraction A B C D r)
      (slotInteraction_norm A B C D hStep r)⟩

/-- A list of the actual local interactions, in temporal order. -/
def localSchedule (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    List (Space n P V →L[ℂ] Space n P V) :=
  List.ofFn (fun r : Fin n => slotInteraction A B C D r)

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem localSchedule_length (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    (localSchedule A B C D n).length = n := by
  simp [localSchedule]

/-- The first `k` interactions, extended constantly after the last slot. -/
def schedulePrefix (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    ℕ → (Space n P V →L[ℂ] Space n P V)
  | 0 => 1
  | k + 1 => if h : k < n then slotInteraction A B C D ⟨k, h⟩ ∘L schedulePrefix A B C D n k
      else schedulePrefix A B C D n k

omit [CompleteSpace P] [CompleteSpace V] in
/-- Each schedulePrefix carries exactly the solved shared-register recurrence and has
modified precisely the slots preceding the current time. -/
theorem schedulePrefix_apply (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n k : ℕ) (hk : k ≤ n) (x : Space n P V) :
    (schedulePrefix A B C D n k x).fst = publicState D C (extendSequence x.snd) x.fst k ∧
    ∀ j : Fin n, (schedulePrefix A B C D n k x).snd j =
      if (j : ℕ) < k then A (x.snd j) + B (publicState D C (extendSequence x.snd) x.fst j)
      else x.snd j := by
  induction k with
  | zero => simp [schedulePrefix]
  | succ k ih =>
      have hkn : k < n := by omega
      obtain ⟨hf, hs⟩ := ih (by omega)
      simp only [schedulePrefix, dif_pos hkn, comp_apply]
      constructor
      · rw [slotInteraction_fst, hf, hs]
        simp only [lt_self_iff_false, ↓reduceIte]
        rw [publicState_succ]
        simp [extendSequence, hkn]
      · intro j
        rw [slotInteraction_snd, hf]
        by_cases hj : j = ⟨k, hkn⟩
        · subst j
          rw [if_pos rfl, hs]
          simp
        · rw [if_neg hj, hs]
          have hjv : (j : ℕ) ≠ k := by
            intro heq
            apply hj
            exact Fin.ext heq
          have hiff : (j : ℕ) < k + 1 ↔ (j : ℕ) < k := by omega
          simp only [hiff]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The actual full reuse operator equals the explicit sequence of `n` local
interactions. No reuse or query-cost formula is assumed. -/
theorem schedulePrefix_eq_fullReuse (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    schedulePrefix A B C D n n = fullReuse A B C D n := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · have hf := (schedulePrefix_apply A B C D n n le_rfl x).1
    simpa only [fullReuse, blockMap_apply, WithLp.fst, publicState,
      publicExit_apply] using hf
  · apply PiLp.ext
    intro j
    have hs := (schedulePrefix_apply A B C D n n le_rfl x).2 j
    rw [if_pos j.isLt] at hs
    change (schedulePrefix A B C D n n x).snd j = (fullReuse A B C D n x).snd j
    rw [hs]
    change _ = (stackedResponse B D n x.fst + chronologicalOperator A B D C n x.snd) j
    have hc := chronologicalOperator_apply A B D C (extendSequence x.snd) j
    change chronologicalOperator A B D C n (restrictSequence n (extendSequence x.snd)) j = _ at hc
    rw [restrict_extend] at hc
    simp only [PiLp.add_apply, stackedResponse_apply, hc, chronologicalPrivateState,
      extendSequence_apply, publicState, map_add]
    abel

end

end SparseHamiltonian.ReuseSchedule
