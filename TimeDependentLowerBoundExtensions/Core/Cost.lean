import TimeDependentLowerBoundExtensions.Core.Masked

set_option autoImplicit false

/-!
# Boolean cost of labelled native calls

The certified families of this library weight each native label by the Boolean cost
`SparseLowerBounds.hardCost` (two per value query, none per location query), while
`hsl:thm:main` counts value queries (`AdaptiveHamiltonianLowerBound.Access.valueWeight`). For
programs whose labels pair a native label with any further datum (a call form, a literal list
of controls), this module records:

* `hardCost_eq_two_mul`: `hardCost = 2 · valueWeight` on native labels;
* `cost_hardCost_fst`: the Boolean cost of a program is twice its number of value calls;
* `cost_valueWeight_fst_le_count`: value calls are calls;
* `max_calls_of_hardCost`: the Boolean max form `2 Y ≤ max(cost_T, cost_M, cost_P)` gives
  `Y ≤ max(Q_T, Q_M, Q_P)` for the numbers of value calls and for the numbers of calls.
-/

namespace TimeDependentLowerBoundExtensions.Core

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding
open SparseLowerBounds
open AdaptiveHamiltonianLowerBound.Access (valueWeight)

/-- The Boolean cost of a native label is twice its value-call weight. -/
theorem hardCost_eq_two_mul (l : Query) : hardCost l = 2 * valueWeight l := by
  cases l <;> rfl

section Cost

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {L' X : Type*} {O : Query × L' → X → V →L[ℂ] V}

/-- **Boolean cost of a labelled program**: with the weight `hardCost` of the native label of
each call, the cost of a program is twice its number of value calls (the labelled form of
`SparseLowerBounds.cost_hardCost`). -/
theorem cost_hardCost_fst (p : MultiOracleCircuit.Program O) :
    p.cost (fun c => hardCost c.1) = 2 * p.cost (fun c => valueWeight c.1) := by
  induction p with
  | fixed U hU => rfl
  | query l => exact hardCost_eq_two_mul l.1
  | queryAdjoint l => exact hardCost_eq_two_mul l.1
  | seq p t hp ht => simp only [MultiOracleCircuit.Program.cost_seq, hp, ht, Nat.mul_add]

/-- **Value calls are calls**: the value-call weight of a labelled program is at most its
number of calls. -/
theorem cost_valueWeight_fst_le_count (p : MultiOracleCircuit.Program O) :
    p.cost (fun c => valueWeight c.1) ≤ p.count :=
  calc p.cost (fun c => valueWeight c.1) ≤ p.cost (fun _ => 1) :=
        p.cost_mono fun c => by show valueWeight c.1 ≤ 1; cases c.1 <;> decide
    _ = p.count := by simp

end Cost

/-- **From the Boolean-cost max form to value calls and calls**: the Boolean bound
`2 Y ≤ max(cost_T, cost_M, cost_P)` with weight `hardCost` on the native labels of three
labelled programs gives `Y ≤ max(Q_T, Q_M, Q_P)` for the numbers of value calls and for the
numbers of calls. -/
theorem max_calls_of_hardCost {KT KM KP LT LM LP XT XM XP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    {OT : Query × LT → XT → KT →L[ℂ] KT} {OM : Query × LM → XM → KM →L[ℂ] KM}
    {OP : Query × LP → XP → KP →L[ℂ] KP} (pT : MultiOracleCircuit.Program OT)
    (pM : MultiOracleCircuit.Program OM) (pP : MultiOracleCircuit.Program OP) {Y : ℝ}
    (h2 : 2 * Y ≤ max (pT.cost (fun c => hardCost c.1) : ℝ)
      (max (pM.cost (fun c => hardCost c.1) : ℝ) (pP.cost (fun c => hardCost c.1)))) :
    Y ≤ max (pT.cost (fun c => valueWeight c.1) : ℝ)
        (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) ∧
      Y ≤ max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  rw [cost_hardCost_fst pT, cost_hardCost_fst pM, cost_hardCost_fst pP] at h2
  push_cast at h2
  rw [← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at h2
  have hQ : Y ≤ max (pT.cost (fun c => valueWeight c.1) : ℝ)
      (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) := by
    linarith
  refine ⟨hQ, hQ.trans (max_le_max ?_ (max_le_max ?_ ?_))⟩ <;>
    exact_mod_cast cost_valueWeight_fst_le_count _

end

end TimeDependentLowerBoundExtensions.Core
