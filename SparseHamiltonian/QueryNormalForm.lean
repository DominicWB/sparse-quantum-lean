import SparseHamiltonian.ClockQuery

/-!
# Oracle normal form with one query per link

Every uniform oracle program can be written using exactly one fixed gate before
each oracle letter, followed by one final fixed gate.  Composing normal forms
merges adjacent fixed gates, so the number of links is the number of queries
plus one, independently of the number of free gates in the original syntax.
-/

namespace SparseHamiltonian.QueryNormalForm

open OracleCircuit

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*}

/-- A fixed gate has no input parameter. -/
abbrev FixedGate (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] := {U : K →L[ℂ] K // IsUnitary U}

/-- The Boolean records whether the query is inverted.  The final fixed gate
is retained even for a zero-query program. -/
inductive NormalForm (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] where
  | done (U : FixedGate K)
  | step (U : FixedGate K) (inverse : Bool) (rest : NormalForm K)

namespace NormalForm

/-- Number of oracle letters. -/
def count : NormalForm K → ℕ
  | .done _ => 0
  | .step _ _ p => p.count + 1

/-- Choose the oracle or its adjoint without changing the fixed gates. -/
def queryOperator (O : X → K →L[ℂ] K) (inverse : Bool) (x : X) : K →L[ℂ] K :=
  if inverse then star (O x) else O x

/-- Evaluate the alternating normal form in multiplication order. -/
def eval (O : X → K →L[ℂ] K) : NormalForm K → X → K →L[ℂ] K
  | .done U, _ => U.val
  | .step U b p, x => U.val * queryOperator O b x * p.eval O x

/-- Absorb an additional fixed gate into the first fixed gate. -/
def premul (U : FixedGate K) : NormalForm K → NormalForm K
  | .done V => .done ⟨U.val * V.val, U.property.mul V.property⟩
  | .step V b p => .step ⟨U.val * V.val, U.property.mul V.property⟩ b p

@[simp] theorem count_premul (U : FixedGate K) (p : NormalForm K) :
    (p.premul U).count = p.count := by
  cases p <;> rfl

@[simp] theorem eval_premul (O : X → K →L[ℂ] K) (U : FixedGate K)
    (p : NormalForm K) (x : X) :
    (p.premul U).eval O x = U.val * p.eval O x := by
  cases p <;> simp only [premul, eval, mul_assoc]

/-- Multiply two normal forms, merging the adjacent fixed gates. -/
def append : NormalForm K → NormalForm K → NormalForm K
  | .done U, q => q.premul U
  | .step U b p, q => .step U b (p.append q)

@[simp] theorem count_append (p q : NormalForm K) :
    (p.append q).count = p.count + q.count := by
  induction p with
  | done U => simp only [append, count_premul, count, zero_add]
  | step U b p hp => simp only [append, count, hp]; omega

@[simp] theorem eval_append (O : X → K →L[ℂ] K) (p q : NormalForm K) (x : X) :
    (p.append q).eval O x = p.eval O x * q.eval O x := by
  induction p with
  | done U => simp only [append, eval_premul, eval]
  | step U b p hp => simp only [append, eval, hp, mul_assoc]

/-- A query letter as a program. -/
def queryProgram (O : X → K →L[ℂ] K) (inverse : Bool) : Program O :=
  if inverse then .queryAdjoint else .query

@[simp] theorem eval_queryProgram (O : X → K →L[ℂ] K) (b : Bool) (x : X) :
    (queryProgram O b).eval x = queryOperator O b x := by
  cases b <;> rfl

@[simp] theorem count_queryProgram (O : X → K →L[ℂ] K) (b : Bool) :
    (queryProgram O b).count = 1 := by
  cases b <;> rfl

/-- A link executes at most one oracle letter.  The trailing link is fixed. -/
def links (O : X → K →L[ℂ] K) : NormalForm K → List (Program O)
  | .done U => [.fixed U.val U.property]
  | .step U b p => .seq (.fixed U.val U.property) (queryProgram O b) :: p.links O

@[simp] theorem length_links (O : X → K →L[ℂ] K) (p : NormalForm K) :
    (p.links O).length = p.count + 1 := by
  induction p with
  | done U => rfl
  | step U b p hp => simp only [links, List.length_cons, count, hp]

/-- Every link has at most one query, including when the program has no queries. -/
theorem count_link_le_one (O : X → K →L[ℂ] K) (p : NormalForm K)
    (l : Program O) (hl : l ∈ p.links O) : l.count ≤ 1 := by
  induction p with
  | done U => simp only [links, List.mem_singleton] at hl; subst l; simp
  | step U b p hp =>
      simp only [links, List.mem_cons] at hl
      rcases hl with rfl | hl
      · simp
      · exact hp hl

/-- The link decomposition has the same semantics as the normal form. -/
@[simp] theorem prod_links (O : X → K →L[ℂ] K) (p : NormalForm K) (x : X) :
    ((p.links O).map (fun l => l.eval x)).prod = p.eval O x := by
  induction p with
  | done U => simp [links, eval]
  | step U b p hp => simp only [links, List.map_cons, List.prod_cons,
      Program.eval_seq, Program.eval_fixed, eval_queryProgram, hp, eval]

/-- The total number of calls is unchanged by combining fixed gates. -/
@[simp] theorem sum_counts_links (O : X → K →L[ℂ] K) (p : NormalForm K) :
    ((p.links O).map Program.count).sum = p.count := by
  induction p with
  | done U => simp [links, count]
  | step U b p hp => simp only [links, List.map_cons, List.sum_cons,
      Program.count_seq, Program.count_fixed, count_queryProgram, zero_add, hp, count,
      Nat.add_comm]

/-- The independent fixed gates in multiplication order. -/
def fixedGates : NormalForm K → List (FixedGate K)
  | .done U => [U]
  | .step U _ p => U :: p.fixedGates

@[simp] theorem length_fixedGates (p : NormalForm K) :
    p.fixedGates.length = p.count + 1 := by
  induction p with
  | done U => rfl
  | step U b p hp => simp only [fixedGates, List.length_cons, hp, count]

/-- Exactly one direction is recorded for each actual query. -/
def directions : NormalForm K → List Bool
  | .done _ => []
  | .step _ b p => b :: p.directions

@[simp] theorem length_directions (p : NormalForm K) :
    p.directions.length = p.count := by
  induction p with
  | done U => rfl
  | step U b p hp => simp only [directions, List.length_cons, hp, count]

end NormalForm

/-- Normalisation is performed once on syntax and does not depend on the unknown
oracle input. -/
def normalize {O : X → K →L[ℂ] K} : Program O → NormalForm K
  | .fixed U hU => .done ⟨U, hU⟩
  | .query => .step ⟨1, isUnitary_one⟩ false (.done ⟨1, isUnitary_one⟩)
  | .queryAdjoint => .step ⟨1, isUnitary_one⟩ true (.done ⟨1, isUnitary_one⟩)
  | .seq p q => (normalize p).append (normalize q)

@[simp] theorem count_normalize {O : X → K →L[ℂ] K} (p : Program O) :
    (normalize p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [normalize, NormalForm.count_append, hp, hq, Program.count_seq]

@[simp] theorem eval_normalize {O : X → K →L[ℂ] K} (p : Program O) (x : X) :
    (normalize p).eval O x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => simp [normalize, NormalForm.eval, NormalForm.queryOperator]
  | queryAdjoint => simp [normalize, NormalForm.eval, NormalForm.queryOperator]
  | seq p q hp hq => simp only [normalize, NormalForm.eval_append, hp, hq, Program.eval_seq]

/-- Uniform exact link decomposition with query-count clock length. -/
theorem exists_query_links {O : X → K →L[ℂ] K} (p : Program O) :
    ∃ ls : List (Program O), ls.length = p.count + 1 ∧
      (∀ l ∈ ls, l.count ≤ 1) ∧
      (∀ x, (ls.map (fun l => l.eval x)).prod = p.eval x) ∧
      (ls.map Program.count).sum = p.count := by
  refine ⟨(normalize p).links O, ?_, ?_, ?_, ?_⟩
  · simp
  · exact (normalize p).count_link_le_one O
  · intro x; simp
  · simp

end

end SparseHamiltonian.QueryNormalForm
