import SparseODE.ODENativeSimulation

/-!
# One native query schedule for all tagged Cayley parameters

The common-shape compiler checks the complete circuit syntax, including every
query label, inverse direction and composition. Erasing the actual native
Cayley circuit is independent of its public real parameters. This proves
coherent selection of those circuits at exactly the cost of one branch.

-/

namespace SparseHamiltonian.CommonQueryShape

noncomputable section
open OracleCircuit
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000

/-- Fixed gates are erased; all query labels, directions and syntax remain. -/
inductive Shape (L : Type*) where
  | fixed
  | query (label : L)
  | queryAdjoint (label : L)
  | seq (p q : Shape L)

namespace Shape

def count {L : Type*} : Shape L → ℕ
  | .fixed => 0
  | .query _ => 1
  | .queryAdjoint _ => 1
  | .seq p q => p.count + q.count

def cost {L : Type*} (w : L → ℕ) : Shape L → ℕ
  | .fixed => 0
  | .query l => w l
  | .queryAdjoint l => w l
  | .seq p q => p.cost w + q.cost w

end Shape

variable {ι L X K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- Erasure never inspects an unknown input or a fixed gate's matrix. -/
def erase : MultiOracleCircuit.Program O → Shape L
  | .fixed _ _ => .fixed
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (erase p) (erase q)

@[simp] theorem erase_count (p : MultiOracleCircuit.Program O) :
    (erase p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [erase, Shape.count, MultiOracleCircuit.Program.count_seq, hp, hq]

@[simp] theorem erase_cost (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (erase p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
    simp only [erase, Shape.cost, MultiOracleCircuit.Program.cost_seq, hp, hq]

private theorem fixed_cases (p : MultiOracleCircuit.Program O)
    (h : erase p = .fixed) :
    ∃ (U : K →L[ℂ] K) (hU : IsUnitary U), p = .fixed U hU := by
  cases p with
  | fixed U hU => exact ⟨U, hU, rfl⟩
  | query l => cases h
  | queryAdjoint l => cases h
  | seq p q => cases h

private theorem query_cases (p : MultiOracleCircuit.Program O) (l : L)
    (h : erase p = .query l) : p = .query l := by
  cases p with
  | fixed U hU => cases h
  | query k =>
    have hk : k = l := by simpa only [erase, Shape.query.injEq] using h
    subst k
    rfl
  | queryAdjoint k => cases h
  | seq p q => cases h

private theorem queryAdjoint_cases (p : MultiOracleCircuit.Program O) (l : L)
    (h : erase p = .queryAdjoint l) : p = .queryAdjoint l := by
  cases p with
  | fixed U hU => cases h
  | query k => cases h
  | queryAdjoint k =>
    have hk : k = l := by simpa only [erase, Shape.queryAdjoint.injEq] using h
    subst k
    rfl
  | seq p q => cases h

private theorem seq_cases (p : MultiOracleCircuit.Program O) (a b : Shape L)
    (h : erase p = .seq a b) :
    ∃ p₁ p₂ : MultiOracleCircuit.Program O,
      p = .seq p₁ p₂ ∧ erase p₁ = a ∧ erase p₂ = b := by
  cases p with
  | fixed U hU => cases h
  | query l => cases h
  | queryAdjoint l => cases h
  | seq p q =>
    have hpq : erase p = a ∧ erase q = b := by
      simpa only [erase, Shape.seq.injEq] using h
    exact ⟨p, q, rfl, hpq.1, hpq.2⟩

/-- A common complete syntax gives an actual branch-dependent gate schedule.
The count and cost claims also hold when the branch type is empty. -/
theorem exists_schedule (a : Shape L) :
    ∀ (p : ι → MultiOracleCircuit.Program O),
      (∀ i, erase (p i) = a) →
      ∃ q : CoherentQuerySchedule.Schedule ι L K,
        (∀ i, q.branch O i = p i) ∧ q.count = a.count ∧
          ∀ w : L → ℕ, q.cost w = a.cost w := by
  classical
  induction a with
  | fixed =>
    intro p hp
    choose U hU hEq using fun i => fixed_cases (p i) (hp i)
    refine ⟨.fixed U hU, ?_, rfl, fun _ => rfl⟩
    intro i
    exact (hEq i).symm
  | query l =>
    intro p hp
    refine ⟨.query l, ?_, rfl, fun _ => rfl⟩
    intro i
    exact (query_cases (p i) l (hp i)).symm
  | queryAdjoint l =>
    intro p hp
    refine ⟨.queryAdjoint l, ?_, rfl, fun _ => rfl⟩
    intro i
    exact (queryAdjoint_cases (p i) l (hp i)).symm
  | seq a b ha hb =>
    intro p hp
    choose p₁ p₂ hEq h₁ h₂ using fun i => seq_cases (p i) a b (hp i)
    obtain ⟨q₁, hq₁, hc₁, hw₁⟩ := ha p₁ h₁
    obtain ⟨q₂, hq₂, hc₂, hw₂⟩ := hb p₂ h₂
    refine ⟨.seq q₁ q₂, ?_, ?_, ?_⟩
    · intro i
      change .seq (q₁.branch O i) (q₂.branch O i) = p i
      rw [hq₁ i, hq₂ i, ← hEq i]
    · change q₁.count + q₂.count = a.count + b.count
      rw [hc₁, hc₂]
    · intro w
      change q₁.cost w + q₂.cost w = a.cost w + b.cost w
      rw [hw₁, hw₂]

/-- Choose only public fixed gates; no unknown input appears in the schedule. -/
def schedule (a : Shape L) (p : ι → MultiOracleCircuit.Program O)
    (hp : ∀ i, erase (p i) = a) : CoherentQuerySchedule.Schedule ι L K :=
  Classical.choose (exists_schedule a p hp)

theorem branch_schedule (a : Shape L) (p : ι → MultiOracleCircuit.Program O)
    (hp : ∀ i, erase (p i) = a) (i : ι) :
    (schedule a p hp).branch O i = p i :=
  (Classical.choose_spec (exists_schedule a p hp)).1 i

theorem schedule_count (a : Shape L) (p : ι → MultiOracleCircuit.Program O)
    (hp : ∀ i, erase (p i) = a) : (schedule a p hp).count = a.count :=
  (Classical.choose_spec (exists_schedule a p hp)).2.1

theorem schedule_cost (a : Shape L) (p : ι → MultiOracleCircuit.Program O)
    (hp : ∀ i, erase (p i) = a) (w : L → ℕ) :
    (schedule a p hp).cost w = a.cost w :=
  (Classical.choose_spec (exists_schedule a p hp)).2.2 w

end
end SparseHamiltonian.CommonQueryShape
