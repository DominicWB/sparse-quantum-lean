import SparseHamiltonian.ActualAmplifiedBandResources

/-!
# One-query links for explicitly labeled native programs

Normalization keeps each query's primitive label and polarity. Adjacent fixed
gates are combined, so the number of clock links is the original query count
plus one. No selected-oracle primitive is introduced.
-/
namespace SparseHamiltonian.MultiQueryNormalForm

noncomputable section
open OracleCircuit QueryNormalForm

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- A native query letter records a fixed label and inverse flag. -/
inductive NormalForm (K L : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] where
  | done (U : FixedGate K)
  | step (U : FixedGate K) (label : L) (inverse : Bool) (rest : NormalForm K L)

namespace NormalForm

def count : NormalForm K L → ℕ
  | .done _ => 0
  | .step _ _ _ p => p.count + 1

def queryOperator (O : L → X → K →L[ℂ] K) (l : L) (inverse : Bool) (x : X) : K →L[ℂ] K :=
  if inverse then star (O l x) else O l x

def eval (O : L → X → K →L[ℂ] K) : NormalForm K L → X → K →L[ℂ] K
  | .done U, _ => U.val
  | .step U l b p, x => U.val * queryOperator O l b x * p.eval O x

def premul (U : FixedGate K) : NormalForm K L → NormalForm K L
  | .done V => .done ⟨U.val * V.val, U.property.mul V.property⟩
  | .step V l b p => .step ⟨U.val * V.val, U.property.mul V.property⟩ l b p

@[simp] theorem count_premul (U : FixedGate K) (p : NormalForm K L) :
    (p.premul U).count = p.count := by cases p <;> rfl

@[simp] theorem eval_premul (O : L → X → K →L[ℂ] K) (U : FixedGate K)
    (p : NormalForm K L) (x : X) :
    (p.premul U).eval O x = U.val * p.eval O x := by
  cases p <;> simp only [premul, eval, mul_assoc]

def append : NormalForm K L → NormalForm K L → NormalForm K L
  | .done U, q => q.premul U
  | .step U l b p, q => .step U l b (p.append q)

@[simp] theorem count_append (p q : NormalForm K L) :
    (p.append q).count = p.count + q.count := by
  induction p with
  | done U => simp only [append, count_premul, count, zero_add]
  | step U l b p hp => simp only [append, count, hp]; omega

@[simp] theorem eval_append (O : L → X → K →L[ℂ] K) (p q : NormalForm K L) (x : X) :
    (p.append q).eval O x = p.eval O x * q.eval O x := by
  induction p with
  | done U => simp only [append, eval_premul, eval]
  | step U l b p hp => simp only [append, eval, hp, mul_assoc]

end NormalForm

/-- This conversion reads syntax, never the unknown oracle input. -/
def normalize {O : L → X → K →L[ℂ] K} : MultiOracleCircuit.Program O → NormalForm K L
  | .fixed U hU => .done ⟨U,hU⟩
  | .query l => .step ⟨1,isUnitary_one⟩ l false (.done ⟨1,isUnitary_one⟩)
  | .queryAdjoint l => .step ⟨1,isUnitary_one⟩ l true (.done ⟨1,isUnitary_one⟩)
  | .seq p q => (normalize p).append (normalize q)

@[simp] theorem count_normalize {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) :
    (normalize p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [normalize, NormalForm.count_append, hp, hq,
      MultiOracleCircuit.Program.count_seq]

@[simp] theorem eval_normalize {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) (x : X) :
    (normalize p).eval O x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query l => simp [normalize, NormalForm.eval, NormalForm.queryOperator]
  | queryAdjoint l => simp [normalize, NormalForm.eval, NormalForm.queryOperator]
  | seq p q hp hq => simp only [normalize, NormalForm.eval_append, hp, hq,
      MultiOracleCircuit.Program.eval_seq]

/-- Fixed gate and optional native query for one clock link. -/
abbrev LinkData (K L : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] := FixedGate K × Option (L × Bool)

def identityData : LinkData K L := (⟨1,isUnitary_one⟩,none)

def dataLinks : NormalForm K L → List (LinkData K L)
  | .done U => [(U,none)]
  | .step U l b p => (U,some (l,b)) :: dataLinks p

@[simp] theorem length_dataLinks (p : NormalForm K L) :
    (dataLinks p).length = p.count + 1 := by
  induction p with
  | done U => rfl
  | step U l b p hp => simp only [dataLinks, List.length_cons, hp, NormalForm.count]

/-- An optional letter, including an exactly inactive branch. -/
def optionalQuery (O : L → X → K →L[ℂ] K) (c : Option (L × Bool)) (x : X) : K →L[ℂ] K :=
  match c with
  | none => 1
  | some (l,b) => NormalForm.queryOperator O l b x

def optionalProgram (O : L → X → K →L[ℂ] K) (c : Option (L × Bool)) : MultiOracleCircuit.Program O :=
  match c with
  | none => .identity
  | some (l,b) => if b then .queryAdjoint l else .query l

@[simp] theorem optionalProgram_eval (O : L → X → K →L[ℂ] K) (c : Option (L × Bool)) (x : X) :
    (optionalProgram O c).eval x = optionalQuery O c x := by
  cases c with
  | none => rfl
  | some c => rcases c with ⟨l,b⟩; cases b <;> rfl

/-- Optional native letters are unitary solely from the original primitive promises. -/
theorem optionalQuery_unitary (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (c : Option (L × Bool)) (x : X) :
    IsUnitary (optionalQuery O c x) := by
  rw [← optionalProgram_eval]
  exact (optionalProgram O c).eval_unitary hO x

/-- Actual one-letter link program. -/
def dataProgram (O : L → X → K →L[ℂ] K) (a : LinkData K L) : MultiOracleCircuit.Program O :=
  .seq (.fixed a.1.val a.1.property) (optionalProgram O a.2)

@[simp] theorem dataProgram_eval (O : L → X → K →L[ℂ] K) (a : LinkData K L) (x : X) :
    (dataProgram O a).eval x = a.1.val * optionalQuery O a.2 x := by
  simp [dataProgram]

/-- The product of extracted links is exactly the original normal form. -/
theorem prod_dataLinks (O : L → X → K →L[ℂ] K) (p : NormalForm K L) (x : X) :
    ((dataLinks p).map (fun a => (dataProgram O a).eval x)).prod = p.eval O x := by
  induction p with
  | done U => simp [dataLinks, optionalQuery, NormalForm.eval]
  | step U l b p hp =>
    simp only [dataLinks, List.map_cons, List.prod_cons, hp]
    rw [dataProgram_eval]
    rfl

end
end SparseHamiltonian.MultiQueryNormalForm
