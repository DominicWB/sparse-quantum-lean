import DeferredMeasurementLowerBounds.Access.Control
import DeferredMeasurementLowerBounds.Access.Transport

set_option autoImplicit false

/-!
# Deferral over single-label controlled calls

Manuscript lines 5185-5186 ("controlled queries and adaptive algorithms after coherent
purification and padding to their worst-case query count") and lines 3669-3673 (calls with
"their inverses and controls").

For a measured algorithm over a base family `B` of unitary labels, the deferred labels compile to
controlled calls of the spectator lift `1_R ⊗ B` (`ctrlCircuits`), acting on the active sector
of control ⊗ records ⊗ workspace as the deferred labels (`ctrlCircuits_eval`, encoding
`AdaptiveODELowerBound.Access.activeEmbed`). The compiled protocol `ctrlTree` therefore has the
success mass and the conditional output of the measured algorithm
(`Access.successMass_compiledTree`, `Access.conditionalDensity_compiledTree`).

**The constant loss, for one counted label `l₀`**: the compiled protocol makes at most twice the
worst-case number of calls of `l₀` of the measured algorithm (`worstCost_ctrlTree`), and at most
that number when the inverse of `l₀` is a known conjugation of `l₀` (`worstCost_ctrlTree_conj`).
The factor two arises only when an aligned slot calls `l₀` in both directions on different
branches. In `worstCost_ctrlTree` and `worstCost_ctrlTree_conj` the labels other than `l₀` are
uncounted (weight zero).

**Several counted labels**: one aligned slot may call different counted labels on different
branches, and calls of independent labels cannot share one controlled call, so a slot costs up
to two controlled calls of every counted label (`ctrlCircuits_cost_le_card`); the compiled
protocol `ctrlTreeOf` makes at most `2 · #{counted labels}` times the worst-case number of
counted calls (`worstCost_ctrlTreeOf`). No corollary of the library uses this access model: the
native, phase and sampled-time accesses lose no constant.
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open SparseLinearSystems.Protocol
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open AdaptiveODELowerBound.Access (activeEmbed activeEmbed_isometry)

variable {X L₀ V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Fintype L₀] [DecidableEq L₀]

/-- The pattern of base labels of a deferred label. -/
def basePat {counted : L₀ → Prop} {R : Type*} : SelLabel counted R → Pat L₀ R
  | .inl π => fun r => (π r).map fun lb => (lb.1.1, lb.2)
  | .inr π => fun r => (π r).map fun lb => (lb.1.1, lb.2)

/-- **The circuits of the deferred labels**: controlled calls of the base labels. -/
def ctrlCircuits (B : L₀ → X → V →L[ℂ] V) (N : (l₀ : L₀) → Option (InverseConj B l₀))
    (counted : L₀ → Prop) (R : Type*) [Fintype R] :
    SelLabel counted R → MultiOracleCircuit.Program (ctrlTarget B R) :=
  fun c => selCircuit B N (basePat c)

/-- The circuits act on the active sector as the deferred labels. -/
theorem ctrlCircuits_eval {B : L₀ → X → V →L[ℂ] V}
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (counted : L₀ → Prop) (R : Type*) [Fintype R]
    (c : SelLabel counted R) (x : X) :
    (ctrlCircuits B N counted R c).eval x ∘L activeEmbed (Joint R V) =
      activeEmbed (Joint R V) ∘L selFamily B counted R c x := by
  unfold ctrlCircuits
  rw [selCircuit_eval]
  congr 1
  cases c with
  | inl π =>
      unfold selFamily patOp
      congr 1
      funext r
      dsimp only [basePat]
      rcases π r with _ | ⟨l, b⟩ <;> rfl
  | inr π =>
      unfold selFamily patOp
      congr 1
      funext r
      dsimp only [basePat]
      rcases π r with _ | ⟨l, b⟩ <;> rfl

/-- With one counted label `l₀`, a deferred label costs at most two calls of `l₀` per unit of
selection weight. -/
theorem ctrlCircuits_cost (B : L₀ → X → V →L[ℂ] V) (N : (l₀ : L₀) → Option (InverseConj B l₀))
    (l₀ : L₀) (R : Type*) [Fintype R] (c : SelLabel (· = l₀) R) :
    (ctrlCircuits B N (· = l₀) R c).cost (fun c' => countWeight (· = l₀) c'.1) ≤
      2 * selWeight c := by
  cases c with
  | inl π =>
      refine (selCircuit_cost_single B N (basePat (.inl π)) (countWeight (· = l₀)) l₀ ?_).trans ?_
      · intro j l b h
        simp only [basePat, Option.map_eq_some_iff] at h
        obtain ⟨⟨⟨l', hl'⟩, b'⟩, -, hlb⟩ := h
        obtain ⟨rfl, -⟩ := Prod.mk.inj hlb
        exact hl'
      · rw [countWeight, if_pos rfl, one_mul]
        exact (dirCount_le_two N _ l₀).trans (by simp [selWeight])
  | inr π =>
      refine (selCircuit_cost B N (basePat (.inr π)) _).trans (le_of_eq_of_le ?_ (Nat.zero_le _))
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = l₀
      · subst hl
        rw [dirCount_eq_zero N _ l, mul_zero]
        intro j b h
        simp only [basePat, Option.map_eq_some_iff] at h
        obtain ⟨⟨⟨l', hl'⟩, b'⟩, -, hlb⟩ := h
        exact hl' (Prod.mk.inj hlb).1
      · simp [countWeight, hl]

/-- With one counted label `l₀` whose inverse is a known conjugation, a deferred label costs at
most its selection weight. -/
theorem ctrlCircuits_cost_conj (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (l₀ : L₀) (h : (N l₀).isSome) (R : Type*)
    [Fintype R] (c : SelLabel (· = l₀) R) :
    (ctrlCircuits B N (· = l₀) R c).cost (fun c' => countWeight (· = l₀) c'.1) ≤
      selWeight c := by
  cases c with
  | inl π =>
      refine (selCircuit_cost_single B N (basePat (.inl π)) (countWeight (· = l₀)) l₀ ?_).trans ?_
      · intro j l b h
        simp only [basePat, Option.map_eq_some_iff] at h
        obtain ⟨⟨⟨l', hl'⟩, b'⟩, -, hlb⟩ := h
        obtain ⟨rfl, -⟩ := Prod.mk.inj hlb
        exact hl'
      · rw [countWeight, if_pos rfl, one_mul]
        exact (dirCount_le_one N _ l₀ h).trans (by simp [selWeight])
  | inr π =>
      refine (selCircuit_cost B N (basePat (.inr π)) _).trans (le_of_eq_of_le ?_ (Nat.zero_le _))
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l = l₀
      · subst hl
        rw [dirCount_eq_zero N _ l, mul_zero]
        intro j b h
        simp only [basePat, Option.map_eq_some_iff] at h
        obtain ⟨⟨⟨l', hl'⟩, b'⟩, -, hlb⟩ := h
        exact hl' (Prod.mk.inj hlb).1
      · simp [countWeight, hl]

/-- **The deferred protocol over controlled calls** of a measured algorithm with the counted
label `l₀`, with flag space `Fl`. -/
abbrev ctrlTree (Fl : Type*) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    (B : L₀ → X → V →L[ℂ] V) (N : (l₀ : L₀) → Option (InverseConj B l₀)) (l₀ : L₀)
    (M : Measured B E) (φ : V) (hφ : ‖φ‖ = 1) :
    Tree (ctrlTarget B (DRec M)) Fl (Joint (DOut M) E) :=
  compiledTree (· = l₀) Fl M φ hφ (activeEmbed (Joint (DRec M) V)) activeEmbed_isometry
    (ctrlCircuits B N (· = l₀) (DRec M))

variable {Fl : Type*} [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]

/-- **At most twice the worst-case number of calls of `l₀`** (controlled queries after coherent
purification, proof of Lemma `qlsl:lem:xor`). -/
theorem worstCost_ctrlTree (B : L₀ → X → V →L[ℂ] V) (N : (l₀ : L₀) → Option (InverseConj B l₀))
    (l₀ : L₀) (M : Measured B E) {φ : V} (hφ : ‖φ‖ = 1) :
    (ctrlTree Fl B N l₀ M φ hφ).worstCost (fun c => countWeight (· = l₀) c.1) ≤
      2 * M.worstCost (countWeight (· = l₀)) :=
  worstCost_compiledTree_mul M hφ _ _ _ _ 2 (ctrlCircuits_cost B N l₀ _)

/-- **No loss when the inverse of `l₀` is a known conjugation.** -/
theorem worstCost_ctrlTree_conj (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (l₀ : L₀) (h : (N l₀).isSome) (M : Measured B E)
    {φ : V} (hφ : ‖φ‖ = 1) :
    (ctrlTree Fl B N l₀ M φ hφ).worstCost (fun c => countWeight (· = l₀) c.1) ≤
      M.worstCost (countWeight (· = l₀)) :=
  worstCost_compiledTree M hφ _ _ _ _ (ctrlCircuits_cost_conj B N l₀ h _)

/-! ### Several counted labels -/

/-- With any set of counted labels, a deferred label costs at most two calls of every counted
label per unit of selection weight, so at most `2 · #{counted labels}` counted calls. -/
theorem ctrlCircuits_cost_le_card (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (counted : L₀ → Prop) [DecidablePred counted]
    (R : Type*) [Fintype R] (c : SelLabel counted R) :
    (ctrlCircuits B N counted R c).cost (fun c' => countWeight counted c'.1) ≤
      2 * Fintype.card {l // counted l} * selWeight c := by
  cases c with
  | inl π =>
      refine (selCircuit_cost B N (basePat (.inl π)) (countWeight counted)).trans ?_
      have hsum : ∑ l, countWeight counted l = Fintype.card {l // counted l} := by
        rw [Fintype.card_subtype, Finset.card_filter]
        rfl
      calc ∑ l, countWeight counted l * dirCount N (basePat (.inl π)) l
          ≤ ∑ l, countWeight counted l * 2 :=
            Finset.sum_le_sum fun l _ => Nat.mul_le_mul_left _ (dirCount_le_two N _ l)
        _ = 2 * Fintype.card {l // counted l} * selWeight (Sum.inl π : SelLabel counted R) := by
            rw [← Finset.sum_mul, hsum, selWeight, mul_one, mul_comm]
  | inr π =>
      refine (selCircuit_cost B N (basePat (.inr π)) _).trans (le_of_eq_of_le ?_ (Nat.zero_le _))
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : counted l
      · rw [dirCount_eq_zero N _ l, mul_zero]
        intro j b h
        simp only [basePat, Option.map_eq_some_iff] at h
        obtain ⟨⟨⟨l', hl'⟩, b'⟩, -, hlb⟩ := h
        obtain ⟨rfl, -⟩ := Prod.mk.inj hlb
        exact hl' hl
      · simp [countWeight, hl]

/-- **The deferred protocol over controlled calls** of a measured algorithm with any set of
counted labels, with flag space `Fl`. -/
abbrev ctrlTreeOf (Fl : Type*) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] (B : L₀ → X → V →L[ℂ] V) (N : (l₀ : L₀) → Option (InverseConj B l₀))
    (counted : L₀ → Prop) [DecidablePred counted] (M : Measured B E) (φ : V) (hφ : ‖φ‖ = 1) :
    Tree (ctrlTarget B (DRec M)) Fl (Joint (DOut M) E) :=
  compiledTree counted Fl M φ hφ (activeEmbed (Joint (DRec M) V)) activeEmbed_isometry
    (ctrlCircuits B N counted (DRec M))

/-- **Several counted labels**: the compiled protocol makes at most `2 · #{counted labels}`
times the worst-case number of counted calls of the measured algorithm. -/
theorem worstCost_ctrlTreeOf (B : L₀ → X → V →L[ℂ] V)
    (N : (l₀ : L₀) → Option (InverseConj B l₀)) (counted : L₀ → Prop) [DecidablePred counted]
    (M : Measured B E) {φ : V} (hφ : ‖φ‖ = 1) :
    (ctrlTreeOf Fl B N counted M φ hφ).worstCost (fun c => countWeight counted c.1) ≤
      2 * Fintype.card {l // counted l} * M.worstCost (countWeight counted) :=
  worstCost_compiledTree_mul M hφ _ _ _ _ _ (ctrlCircuits_cost_le_card B N counted _)

end

end DeferredMeasurementLowerBounds.Access
