import SparseHamiltonian.NativeDyadicEncoding

/-!
# Selected native letters from a finite sequence of ordinary labeled calls

Each cell selects at most one native label and direction. Every label is visited
once in a fixed order, using a forward mask and an inverse mask. The proved
three-query masking construction compiles these visits into six original
calls per native label. No coherent SELECT oracle is assumed.
-/
namespace SparseHamiltonian.NativeMultiSelected

noncomputable section
open ContinuousLinearMap OracleCircuit MultiQueryNormalForm
open scoped InnerProduct BigOperators
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {ι B X L : Type*} [Fintype ι] [Fintype B] [DecidableEq B]
  [Fintype L] [DecidableEq L]

/-- Fixed cell mask for one explicit native label and direction. -/
def mask (choice : ι → Option (L × Bool)) (letter : L × Bool) (i : ι) : Bool :=
  decide (choice i = some letter)

abbrev sourceOracle (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : ι → Option (L × Bool)) :=
  NativeMaskedProgram.logicalOracle F Prod.fst (mask choice)

/-- Visit both polarities of a single fixed native label. -/
def sourceLetter (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : ι → Option (L × Bool)) (l : L) : MultiOracleCircuit.Program (sourceOracle F choice) :=
  .seq (.query (l,false)) (.queryAdjoint (l,true))

/-- A fixed finite traversal of the native vocabulary. -/
def sourceProgram (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : ι → Option (L × Bool)) : List L → MultiOracleCircuit.Program (sourceOracle F choice)
  | [] => .identity
  | l :: ls => .seq (sourceLetter F choice l) (sourceProgram F choice ls)

omit [DecidableEq B] [Fintype L] in
/-- The same six original calls are charged separately for every label. -/
theorem source_cost (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : ι → Option (L × Bool)) (ls : List L) (w : L → ℕ) :
    (sourceProgram F choice ls).cost (fun lb => 3 * w lb.1) =
      6 * (ls.map w).sum := by
  induction ls with
  | nil => simp [sourceProgram]
  | cons l ls ih =>
    simp only [sourceProgram, MultiOracleCircuit.Program.cost_seq, sourceLetter,
      MultiOracleCircuit.Program.cost_query, MultiOracleCircuit.Program.cost_queryAdjoint,
      ih, List.map_cons, List.sum_cons]
    omega

omit [Fintype ι] [Fintype L] [DecidableEq B] in
/-- Ideal effect of visiting only a selected subset of native labels. -/
def effect (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (ls : List L) (c : Option (L × Bool)) (x : X) :
    EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B :=
  match c with
  | none => 1
  | some (l,b) => if l ∈ ls then NormalForm.queryOperator F l b x else 1

omit [Fintype ι] [Fintype L] [DecidableEq B] in
theorem effect_cons (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (l : L) (ls : List L) (hl : l ∉ ls) (c : Option (L × Bool)) (x : X) :
    effect F (l :: ls) c x = effect F [l] c x * effect F ls c x := by
  cases c with
  | none => simp [effect]
  | some c =>
    rcases c with ⟨k,b⟩
    by_cases h : k = l
    · subst k; simp [effect, hl]
    · simp [effect, h]

omit [Fintype L] [DecidableEq B] in
/-- Pointwise action of one forward/inverse masked visit. -/
theorem sourceLetter_apply
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : ι → Option (L × Bool)) (l : L) (x : X)
    (v : NativeMaskedOracle.Logical ι B) (i : ι) :
    (sourceLetter F choice l).eval x v i = effect F [l] (choice i) x (v i) := by
  change (MaskedProgram.masked (mask choice (l,false)) (F l x) *
    star (MaskedProgram.masked (mask choice (l,true)) (F l x))) v i = _
  rw [show star (MaskedProgram.masked (mask choice (l,true)) (F l x)) =
    MaskedProgram.masked (mask choice (l,true)) (star (F l x)) from
      MaskedProgram.masked_adjoint _ _]
  cases h : choice i with
  | none => simp [MaskedProgram.masked_apply, mask, h, effect]
  | some c =>
    rcases c with ⟨k,b⟩
    by_cases hk : k = l
    · subst k; cases b <;> simp [MaskedProgram.masked_apply, mask, h, effect,
        NormalForm.queryOperator]
    · cases b <;> simp [MaskedProgram.masked_apply, mask, h, effect, hk]

omit [Fintype L] [DecidableEq B] in
/-- Every cell experiences at most one native letter in a duplicate-free traversal. -/
theorem sourceProgram_apply
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : ι → Option (L × Bool)) (ls : List L) (hn : ls.Nodup) (x : X)
    (v : NativeMaskedOracle.Logical ι B) (i : ι) :
    (sourceProgram F choice ls).eval x v i = effect F ls (choice i) x (v i) := by
  induction ls with
  | nil => cases h : choice i <;> simp [sourceProgram, effect]
  | cons l ls ih =>
    rcases List.nodup_cons.mp hn with ⟨hl,ht⟩
    change (sourceLetter F choice l).eval x ((sourceProgram F choice ls).eval x v) i = _
    rw [sourceLetter_apply, ih ht, effect_cons F l ls hl]
    rfl

/-- The concrete physical selected-query program uses a fixed traversal order. -/
def program (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (choice : ι → Option (L × Bool)) :
    MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F) :=
  NativeMaskedProgram.compile F a Prod.fst (mask choice)
    (sourceProgram F choice (Finset.univ.toList))

/-- Exact weighted primitive cost, independent of the cell register size. -/
@[simp] theorem program_cost
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (choice : ι → Option (L × Bool)) (w : L → ℕ) :
    (program F a choice).cost w = 6 * ∑ l, w l := by
  rw [program, NativeMaskedProgram.compile_cost, source_cost]
  simp

/-- Six ordinary native calls per primitive label. -/
@[simp] theorem program_count
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (choice : ι → Option (L × Bool)) :
    (program F a choice).count = 6 * Fintype.card L := by
  have h := program_cost F a choice (fun _ => 1)
  simpa using h

/-- Full coherent clean-output correctness of native selected access. -/
theorem program_intertwines
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (choice : ι → Option (L × Bool)) (x : X) :
    (program F a choice).eval x ∘L (NativeMaskedOracle.input (ι := ι) a).toContinuousLinearMap =
      (NativeMaskedOracle.input a).toContinuousLinearMap ∘L
        WeightedClock.diagonal (fun i => optionalQuery F (choice i) x) := by
  rw [program, NativeMaskedProgram.compile_eval F hF a image hvalid]
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rw [sourceProgram_apply F choice _ (Finset.nodup_toList _)]
  cases h : choice i with
  | none => simp [effect, optionalQuery, h]
  | some c => rcases c with ⟨l,b⟩; simp [effect, optionalQuery, h]

/-- The implementing program is unitary on the whole physical workspace. -/
theorem program_unitary
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (choice : ι → Option (L × Bool)) (x : X) :
    IsUnitary ((program F a choice).eval x) :=
  (program F a choice).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y) x

end
end SparseHamiltonian.NativeMultiSelected
