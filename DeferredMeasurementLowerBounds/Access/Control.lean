import DeferredMeasurementLowerBounds.Deferral.Selection
import AdaptiveODELowerBound.Access.Control

set_option autoImplicit false

/-!
# Record-selected calls from controlled calls

Some access models of the package grant one label per call, with its inverse, controlled and
controlled-inverse forms (`AdaptiveODELowerBound.Access.callFamily`, Section `odel:sec:main`:
"including inverses, controls and coherent time addresses where needed"), but no call that applies
different labels or directions on different branches. For a base family `B : L₀ → X → V →L[ℂ] V` and
a spectator register `J`, the target family `ctrlTarget B J` is the call family of the spectator
lift `1_J ⊗ B` on control ⊗ `ℂ^J ⊗ V`, and the encoding is the package's active embedding
`v ↦ |1⟩ ⊗ v` (`AdaptiveODELowerBound.Access.activeEmbed`).

* A masked call (label `l₀` in direction `b` on the records of a set `S`, identity elsewhere) is
  one controlled call of `l₀` between two known control flips of the records outside `S`
  (`sectorFlip`, `masked_by_ctrl`): those records move to the idle control sector and back.
* A pattern `σ : J → Option (L₀ × Bool)` is the product of its masked calls, one per used label
  and direction (`selCircuit`, `selCircuit_eval`).
* When a label has an inverse by a known conjugation, `B l₀† = N B l₀ N†` (`InverseConj`), the
  forward and inverse branches of `l₀` share one controlled call, `N` being applied on the
  inverse branches only. The count of label `l₀` is `dirCount`: one controlled call if `l₀` is
  used and has such a conjugation, otherwise one per used direction, so at most two
  (`dirCount_le_two`). A pattern costs the sum of these counts over its labels
  (`selCircuit_cost`): different branches may call different labels in one aligned slot, and
  calls of independent labels cannot share one controlled call.
* **The constant loss.** When every call of a pattern uses one label `l₀`, the pattern costs at
  most two calls of `l₀`, and at most one when `l₀` has an inverse by conjugation
  (`selCircuit_cost_single`). With one counted label the worst-case count therefore drops by at
  most a factor two, and only when an aligned slot has branch-dependent directions of a label
  without a conjugation; with several counted labels a slot can need one or two controlled calls
  for every counted label it uses.
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open AdaptiveODELowerBound.Access (CallForm callFamily formOp ctrlOp activeEmbed)
open scoped InnerProduct

variable {X L₀ V J : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [Fintype J]

/-! ### Masked calls -/

/-- The target family: the call forms of the spectator lift `1_J ⊗ B`. -/
abbrev ctrlTarget (B : L₀ → X → V →L[ℂ] V) (J : Type*) [Fintype J] :
    L₀ × CallForm → X → Joint Bool (Joint J V) →L[ℂ] Joint Bool (Joint J V) :=
  callFamily (fun l x => Joint.fiber (J := J) fun _ => B l x)

/-- The control flip of the records `j` with `S j = true`, a known permutation. -/
def sectorFlip (S : J → Bool) : Joint Bool (Joint J V) →L[ℂ] Joint Bool (Joint J V) :=
  Joint.mk fun d =>
    Joint.fiber (fun j => if S j then (0 : V →L[ℂ] V) else 1) ∘L Joint.proj d +
      Joint.fiber (fun j => if S j then (1 : V →L[ℂ] V) else 0) ∘L Joint.proj (!d)

omit [CompleteSpace V] in
/-- Coordinates of the control flip. -/
theorem sectorFlip_apply (S : J → Bool) (Ψ : Joint Bool (Joint J V)) (d : Bool) (j : J) :
    sectorFlip S Ψ d j = if S j then Ψ (!d) j else Ψ d j := by
  simp only [sectorFlip, Joint.mk_apply, add_apply, comp_apply, PiLp.add_apply,
    Joint.proj_apply, Joint.fiber_apply]
  cases S j <;> simp

/-- The control flip is unitary. -/
theorem sectorFlip_unitary (S : J → Bool) : IsUnitary (sectorFlip (V := V) S) := by
  have hsq : sectorFlip (V := V) S * sectorFlip S = 1 := by
    ext Ψ d j
    change sectorFlip S (sectorFlip S Ψ) d j = Ψ d j
    rw [sectorFlip_apply, sectorFlip_apply, sectorFlip_apply]
    cases S j <;> simp
  have hstar : star (sectorFlip (V := V) S) = sectorFlip S := by
    rw [star_eq_adjoint, eq_comm, eq_adjoint_iff]
    intro Φ Ψ
    simp only [PiLp.inner_apply, Fintype.sum_bool, sectorFlip_apply, Bool.not_true,
      Bool.not_false]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases S j
    · simp
    · simp only [if_true]
      exact add_comm _ _
  exact ⟨by rw [hstar, hsq], by rw [hstar, hsq]⟩

/-- **A masked call is one controlled call between two control flips**, on the active sector. -/
theorem masked_by_ctrl (U : V →L[ℂ] V) (S : J → Bool) :
    (sectorFlip (fun j => !S j) * ctrlOp (Joint.fiber (J := J) fun _ => U) *
        sectorFlip (fun j => !S j)) ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L MaskedProgram.masked S U := by
  ext v d j
  cases d <;> cases h : S j <;>
    simp [sectorFlip_apply, ctrlOp, AdaptiveODELowerBound.Access.activeEmbed_apply, h]

/-- **Inverse by a known conjugation**: `B l₀† = N (B l₀) N†` for a known unitary `N`. -/
structure InverseConj (B : L₀ → X → V →L[ℂ] V) (l₀ : L₀) where
  /-- The conjugating unitary. -/
  conj : V →L[ℂ] V
  unitary : IsUnitary conj
  star_eq : ∀ x, star (B l₀ x) = conj * B l₀ x * star conj

/-- Calls of a label in one direction on the records of a pattern. -/
def patSet (σ : Pat L₀ J) (l₀ : L₀) (b : Bool) [DecidableEq L₀] : J → Bool :=
  fun j => decide (σ j = some (l₀, b))

/-- The number of controlled calls of label `l₀` used for the pattern `σ`. -/
def dirCount [DecidableEq L₀] {B : L₀ → X → V →L[ℂ] V}
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (l₀ : L₀) : ℕ :=
  if (N l₀).isSome then (if ∃ j b, σ j = some (l₀, b) then 1 else 0)
  else (if ∃ j, σ j = some (l₀, false) then 1 else 0) +
    (if ∃ j, σ j = some (l₀, true) then 1 else 0)

/-- At most two controlled calls per label. -/
theorem dirCount_le_two [DecidableEq L₀] {B : L₀ → X → V →L[ℂ] V}
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (l₀ : L₀) :
    dirCount N σ l₀ ≤ 2 := by
  unfold dirCount
  split_ifs <;> simp

/-- One controlled call per label with an inverse by conjugation. -/
theorem dirCount_le_one [DecidableEq L₀] {B : L₀ → X → V →L[ℂ] V}
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (l₀ : L₀)
    (h : (N l₀).isSome) : dirCount N σ l₀ ≤ 1 := by
  unfold dirCount
  rw [if_pos h]
  split_ifs <;> simp

/-- An unused label needs no call. -/
theorem dirCount_eq_zero [DecidableEq L₀] {B : L₀ → X → V →L[ℂ] V}
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (l₀ : L₀)
    (h : ∀ j b, σ j ≠ some (l₀, b)) : dirCount N σ l₀ = 0 := by
  have h1 : ¬ ∃ j b, σ j = some (l₀, b) := fun ⟨j, b, hj⟩ => h j b hj
  have h2 : ∀ b, ¬ ∃ j, σ j = some (l₀, b) := fun b ⟨j, hj⟩ => h j b hj
  unfold dirCount
  rw [if_neg h1, if_neg (h2 false), if_neg (h2 true)]
  simp

/-- The masked call of `l₀` in direction `b` on the records of `S`: one controlled call between
two control flips of the other records. -/
def maskedCall (B : L₀ → X → V →L[ℂ] V) (l₀ : L₀) (b : Bool) (S : J → Bool) :
    MultiOracleCircuit.Program (ctrlTarget B J) :=
  .seq (.fixed _ (sectorFlip_unitary fun j => !S j))
    (.seq (.query (l₀, if b then .controlledInverse else .controlled))
      (.fixed _ (sectorFlip_unitary fun j => !S j)))

/-- A known unitary applied on the records of `S` in both control sectors is unitary. -/
theorem maskedUnitary_unitary {U : V →L[ℂ] V} (hU : IsUnitary U) (S : J → Bool) :
    IsUnitary (Joint.fiber fun _ : Bool => MaskedProgram.masked S U) :=
  PhaseCircuit.isUnitary_fiber _ fun _ => MaskedProgram.masked_unitary S U hU

/-- The controlled calls of one label for the pattern `σ`. -/
def labelCircuit [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (l₀ : L₀) :
    MultiOracleCircuit.Program (ctrlTarget B J) :=
  match N l₀ with
  | some c =>
      if ∃ j b, σ j = some (l₀, b) then
        .seq (.fixed _ (maskedUnitary_unitary c.unitary (patSet σ l₀ true)))
          (.seq (maskedCall B l₀ false fun j => patSet σ l₀ false j || patSet σ l₀ true j)
            (.fixed _ (maskedUnitary_unitary c.unitary.adjoint (patSet σ l₀ true))))
      else MultiOracleCircuit.Program.identity
  | none =>
      .seq (if ∃ j, σ j = some (l₀, true) then maskedCall B l₀ true (patSet σ l₀ true)
          else MultiOracleCircuit.Program.identity)
        (if ∃ j, σ j = some (l₀, false) then maskedCall B l₀ false (patSet σ l₀ false)
          else MultiOracleCircuit.Program.identity)

/-- **The controlled-call circuit of a pattern**: for every used label, its masked calls by
controlled calls between control flips, sharing one call when the label has an inverse by
conjugation. -/
def selCircuit [Fintype L₀] [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) :
    MultiOracleCircuit.Program (ctrlTarget B J) :=
  seqAll ((Finset.univ : Finset L₀).toList.map (labelCircuit B N σ))

/-! ### Action on the active sector -/

/-- An operator applied in both control sectors intertwines the active embedding. -/
theorem fiber_const_comp_activeEmbed {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (U : W →L[ℂ] W) :
    Joint.fiber (fun _ : Bool => U) ∘L activeEmbed W = activeEmbed W ∘L U := by
  ext v d
  cases d <;> simp [AdaptiveODELowerBound.Access.activeEmbed_apply]

/-- A fixed unitary applied in both control sectors intertwines the active embedding. -/
theorem fixed_comp_activeEmbed {L' : Type*} {O : L' → X → Joint Bool (Joint J V) →L[ℂ]
    Joint Bool (Joint J V)} (U : Joint J V →L[ℂ] Joint J V)
    (hU : IsUnitary (Joint.fiber fun _ : Bool => U)) (x : X) :
    (MultiOracleCircuit.Program.fixed (O := O) _ hU).eval x ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L U :=
  fiber_const_comp_activeEmbed U

/-- Sequential composition of programs that act on the active sector as `G` and `H`. -/
theorem seq_comp_activeEmbed {L' : Type*} {O : L' → X → Joint Bool (Joint J V) →L[ℂ]
    Joint Bool (Joint J V)} {p q : MultiOracleCircuit.Program O} {x : X}
    {G H : Joint J V →L[ℂ] Joint J V}
    (hp : p.eval x ∘L activeEmbed (Joint J V) = activeEmbed (Joint J V) ∘L G)
    (hq : q.eval x ∘L activeEmbed (Joint J V) = activeEmbed (Joint J V) ∘L H) :
    (MultiOracleCircuit.Program.seq p q).eval x ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L (G * H) := by
  rw [MultiOracleCircuit.Program.eval_seq, mul_def, mul_def, comp_assoc, hq, ← comp_assoc, hp,
    comp_assoc]

/-- A masked call acts on the active sector as the masked query. -/
theorem maskedCall_eval (B : L₀ → X → V →L[ℂ] V) (l₀ : L₀) (b : Bool) (S : J → Bool) (x : X) :
    (maskedCall B l₀ b S).eval x ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L MaskedProgram.masked S (queryOp B l₀ b x) := by
  rw [← masked_by_ctrl]
  congr 1
  simp only [maskedCall, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
    MultiOracleCircuit.Program.eval_query, ← mul_assoc]
  cases b <;> simp [queryOp, ctrlTarget, callFamily, formOp, Joint.star_fiber]

/-- An optional masked call on the records of a pattern acts as the masked query. -/
theorem optCall_eval [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V) (σ : Pat L₀ J) (l₀ : L₀)
    (b : Bool) (x : X) :
    (if ∃ j, σ j = some (l₀, b) then maskedCall B l₀ b (patSet σ l₀ b)
        else MultiOracleCircuit.Program.identity).eval x ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L MaskedProgram.masked (patSet σ l₀ b) (queryOp B l₀ b x) := by
  split_ifs with h
  · exact maskedCall_eval B l₀ b _ x
  · have hS : patSet σ l₀ b = fun _ => false :=
      funext fun j => by simpa [patSet] using fun hj => h ⟨j, hj⟩
    rw [hS, masked_eq_fiber]
    simp only [Bool.false_eq_true, if_false, Joint.fiber_one,
      MultiOracleCircuit.Program.eval_identity]
    ext v
    rfl

/-- The factor of label `l₀` on record `j`: the call of `σ j` if it uses `l₀`, else the
identity. -/
def labelFactor [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V) (σ : Pat L₀ J) (l₀ : L₀) (x : X)
    (j : J) : V →L[ℂ] V :=
  if ∃ b, σ j = some (l₀, b) then callOpt B (σ j) x else 1

/-- The controlled calls of one label act on the active sector as its factors. -/
theorem labelCircuit_eval [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (l₀ : L₀) (x : X) :
    (labelCircuit B N σ l₀).eval x ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L Joint.fiber (labelFactor B σ l₀ x) := by
  unfold labelCircuit
  split
  · rename_i c _
    split_ifs with h
    · rw [seq_comp_activeEmbed (fixed_comp_activeEmbed _ _ x)
        (seq_comp_activeEmbed (maskedCall_eval B l₀ false _ x) (fixed_comp_activeEmbed _ _ x)),
        masked_eq_fiber, masked_eq_fiber, masked_eq_fiber, Joint.fiber_mul, Joint.fiber_mul]
      congr 2
      funext j
      unfold labelFactor patSet
      rcases hσ : σ j with _ | ⟨l, b⟩
      · simp
      · by_cases hl : l = l₀
        · subst hl
          cases b
          · simp [callOpt, queryOp]
          · simp [callOpt, queryOp, c.star_eq x, mul_assoc]
        · simp [hl]
    · have hF : labelFactor B σ l₀ x = fun _ => 1 :=
        funext fun j => if_neg fun ⟨b, hb⟩ => h ⟨j, b, hb⟩
      rw [hF, Joint.fiber_one, MultiOracleCircuit.Program.eval_identity]
      ext v
      rfl
  · rw [seq_comp_activeEmbed (optCall_eval B σ l₀ true x) (optCall_eval B σ l₀ false x),
      masked_eq_fiber, masked_eq_fiber, Joint.fiber_mul]
    congr 2
    funext j
    unfold labelFactor patSet
    rcases hσ : σ j with _ | ⟨l, b⟩
    · simp
    · by_cases hl : l = l₀
      · subst hl
        cases b <;> simp [callOpt]
      · simp [hl]

/-- The controlled calls of a list of labels act on the active sector as the product of their
factors. -/
theorem seqAll_labelCircuit_eval [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (x : X) (ls : List L₀) :
    (seqAll (ls.map (labelCircuit B N σ))).eval x ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L
        Joint.fiber (fun j => (ls.map fun l => labelFactor B σ l x j).prod) := by
  induction ls with
  | nil =>
      simp only [List.map_nil, List.prod_nil, Joint.fiber_one]
      rfl
  | cons l ls ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [← Joint.fiber_mul]
      exact seq_comp_activeEmbed (labelCircuit_eval B N σ l x) ih

/-- The weighted count of a masked call. -/
theorem maskedCall_cost (B : L₀ → X → V →L[ℂ] V) (l₀ : L₀) (b : Bool) (S : J → Bool)
    (w : L₀ → ℕ) : (maskedCall B l₀ b S).cost (fun c => w c.1) = w l₀ := by
  simp [maskedCall]

/-- The weighted count of the controlled calls of one label. -/
theorem labelCircuit_cost [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (l₀ : L₀) (w : L₀ → ℕ) :
    (labelCircuit B N σ l₀).cost (fun c => w c.1) = w l₀ * dirCount N σ l₀ := by
  unfold labelCircuit dirCount
  split
  · rename_i c heq
    simp only [heq, Option.isSome_some, if_true]
    split_ifs <;> simp [maskedCall_cost]
  · rename_i heq
    simp only [heq, Option.isSome_none, Bool.false_eq_true, if_false]
    split_ifs <;> simp [maskedCall_cost, mul_two]

/-- The weighted count of a list composition of label circuits. -/
theorem seqAll_labelCircuit_cost [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (w : L₀ → ℕ) (ls : List L₀) :
    (seqAll (ls.map (labelCircuit B N σ))).cost (fun c => w c.1) =
      (ls.map fun l => w l * dirCount N σ l).sum := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
      simp only [List.map_cons, List.sum_cons, ← ih, ← labelCircuit_cost B N σ l w]
      rfl

/-- **The circuit acts on the active sector as the pattern.** -/
theorem selCircuit_eval [Fintype L₀] [DecidableEq L₀] {B : L₀ → X → V →L[ℂ] V}
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (x : X) :
    (selCircuit B N σ).eval x ∘L activeEmbed (Joint J V) =
      activeEmbed (Joint J V) ∘L patOp B σ x := by
  unfold selCircuit patOp
  rw [seqAll_labelCircuit_eval]
  congr 2
  funext j
  rcases hσ : σ j with _ | ⟨l₁, b⟩
  · refine List.prod_eq_one fun F hF => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hF
    simp [labelFactor, hσ]
  · rw [List.prod_map_eq_pow_single l₁ _ fun l hl _ => by simp [labelFactor, hσ, Ne.symm hl],
      List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_univ _)),
      pow_one]
    simp [labelFactor, hσ]

/-- **The weighted count of the circuit**: `dirCount` controlled calls of every label. -/
theorem selCircuit_cost [Fintype L₀] [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (w : L₀ → ℕ) :
    (selCircuit B N σ).cost (fun c => w c.1) ≤ ∑ l₀, w l₀ * dirCount N σ l₀ := by
  unfold selCircuit
  rw [seqAll_labelCircuit_cost, Finset.sum_map_toList]

/-- **A pattern of one label** costs `dirCount` calls of that label: at most two
(`dirCount_le_two`), at most one with an inverse by conjugation (`dirCount_le_one`). -/
theorem selCircuit_cost_single [Fintype L₀] [DecidableEq L₀] (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (σ : Pat L₀ J) (w : L₀ → ℕ) (l₀ : L₀)
    (hσ : ∀ j l b, σ j = some (l, b) → l = l₀) :
    (selCircuit B N σ).cost (fun c => w c.1) ≤ w l₀ * dirCount N σ l₀ := by
  refine (selCircuit_cost B N σ w).trans (le_of_eq (Finset.sum_eq_single l₀ (fun l _ hl => ?_)
    fun h => absurd (Finset.mem_univ _) h))
  rw [dirCount_eq_zero N σ l fun j b hj => hl (hσ j l b hj), mul_zero]

end

end DeferredMeasurementLowerBounds.Access
