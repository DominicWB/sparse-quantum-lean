import DeferredMeasurementLowerBounds.Model.Measured
import DeferredMeasurementLowerBounds.Deferral.Registers
import SparseHamiltonian.MaskedProgram

set_option autoImplicit false

/-!
# Record-selected calls

After deferral, the classical control of a measured algorithm is a function of the record
registers. A **call pattern** `π : R → Option (L × Bool)` assigns to every record value `r` either
no call or one call of a label in one direction; its operator `patOp O π x` is the record-diagonal
`Σ_r |r⟩⟨r| ⊗ O(π r)` (`Joint.fiber`), the identity on records without a call. Different records
may call different labels and directions in the same step: this is how the aligned calls of
different branches are merged into one call.

The deferred program is a program over the **selection family** `selFamily O counted R`: its
labels are the call patterns of counted labels (`.inl`, weight one, `selWeight`) and of the other
labels (`.inr`, weight zero). Patterns are lifted to one more record register by
`liftPat v`: the pattern acts on the records whose first register holds `v`. `seqAll` composes a
list of programs.
-/

namespace DeferredMeasurementLowerBounds.Deferral

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The operator of an optional call: identity, or one call in the given direction. -/
def callOpt (O : L → X → K →L[ℂ] K) : Option (L × Bool) → X → K →L[ℂ] K
  | none, _ => 1
  | some (l, b), x => queryOp O l b x

/-- Optional calls of unitary labels are unitary. -/
theorem callOpt_unitary {O : L → X → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x))
    (c : Option (L × Bool)) (x : X) : IsUnitary (callOpt O c x) := by
  rcases c with _ | ⟨l, b⟩
  · exact isUnitary_one
  · exact queryOp_unitary hO l b x

/-- A mask is the record-diagonal operator of its branches. -/
theorem masked_eq_fiber {J V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [Fintype J] (S : J → Bool) (U : V →L[ℂ] V) :
    MaskedProgram.masked S U = Joint.fiber fun j => if S j then U else 1 := by
  ext v j
  rw [MaskedProgram.masked_apply, Joint.fiber_apply]
  split_ifs <;> rfl

/-- A call pattern on the record values `R`. -/
abbrev Pat (L R : Type*) : Type _ := R → Option (L × Bool)

/-- The record-diagonal operator of a call pattern. -/
def patOp (O : L → X → K →L[ℂ] K) {R : Type*} [Fintype R] (π : Pat L R) (x : X) :
    Joint R K →L[ℂ] Joint R K :=
  Joint.fiber fun r => callOpt O (π r) x

/-- Pattern operators of unitary labels are unitary. -/
theorem patOp_unitary {O : L → X → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x)) {R : Type*}
    [Fintype R] (π : Pat L R) (x : X) : IsUnitary (patOp O π x) := by
  have hF : ∀ r, IsUnitary (callOpt O (π r) x) := fun r => callOpt_unitary hO (π r) x
  constructor
  · rw [patOp, Joint.star_fiber, Joint.fiber_mul,
      show (fun r => star (callOpt O (π r) x) * callOpt O (π r) x) =
        fun _ => (1 : K →L[ℂ] K) from funext fun r => (hF r).1, Joint.fiber_one]
  · rw [patOp, Joint.star_fiber, Joint.fiber_mul,
      show (fun r => callOpt O (π r) x * star (callOpt O (π r) x)) =
        fun _ => (1 : K →L[ℂ] K) from funext fun r => (hF r).2, Joint.fiber_one]

/-- Labels of the selection family: patterns of counted labels and patterns of the others. -/
abbrev SelLabel (counted : L → Prop) (R : Type*) : Type _ :=
  Pat {l // counted l} R ⊕ Pat {l // ¬ counted l} R

/-- **The selection family** on `Joint R K`. -/
def selFamily (O : L → X → K →L[ℂ] K) (counted : L → Prop) (R : Type*) [Fintype R] :
    SelLabel counted R → X → Joint R K →L[ℂ] Joint R K
  | .inl π, x => patOp (fun l : {l // counted l} => O l.1) π x
  | .inr π, x => patOp (fun l : {l // ¬ counted l} => O l.1) π x

/-- Counted patterns have weight one, the others weight zero. -/
def selWeight {counted : L → Prop} {R : Type*} : SelLabel counted R → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- The selection family of unitary labels is unitary. -/
theorem selFamily_unitary {O : L → X → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x))
    (counted : L → Prop) (R : Type*) [Fintype R] (c : SelLabel counted R) (x : X) :
    IsUnitary (selFamily O counted R c x) := by
  rcases c with π | π
  · exact patOp_unitary (O := fun l : {l // counted l} => O l.1) (fun l x => hO l.1 x) π x
  · exact patOp_unitary (O := fun l : {l // ¬ counted l} => O l.1) (fun l x => hO l.1 x) π x

/-- Sequential composition of a list of programs (the head runs last). -/
def seqAll {L' K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    {O : L' → X → K' →L[ℂ] K'} :
    List (MultiOracleCircuit.Program O) → MultiOracleCircuit.Program O
  | [] => MultiOracleCircuit.Program.identity
  | p :: ps => .seq p (seqAll ps)

/-- The evaluation of a list composition is the product of the evaluations. -/
theorem eval_seqAll {L' K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] {O : L' → X → K' →L[ℂ] K'} (ps : List (MultiOracleCircuit.Program O))
    (x : X) : (seqAll ps).eval x = (ps.map fun p => p.eval x).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [seqAll, MultiOracleCircuit.Program.eval_seq, ih, List.map_cons, List.prod_cons]

/-- The weighted cost of a list composition is the sum of the costs. -/
theorem cost_seqAll {L' K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    [CompleteSpace K'] {O : L' → X → K' →L[ℂ] K'} (ps : List (MultiOracleCircuit.Program O))
    (w : L' → ℕ) : (seqAll ps).cost w = (ps.map fun p => p.cost w).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [seqAll, MultiOracleCircuit.Program.cost_seq, ih, List.map_cons, List.sum_cons]

/-! ### Lifting patterns to one more record register -/

/-- The pattern acting on the records whose first register holds `v`. -/
def liftPat {W k : ℕ} (v : Option (Fin W)) {L' : Type*} (π : Pat L' (Rec W k)) :
    Pat L' (Rec W (k + 1)) :=
  fun r => if r 0 = v then π (Fin.tail r) else none

omit [CompleteSpace K] in
/-- Coordinates of the inverse separation of the first record register. -/
theorem split_symm_coord {W k : ℕ} (Φ : Joint (Option (Fin W)) (Joint (Rec W k) K))
    (v : Option (Fin W)) (r : Rec W k) : (split W k K).symm Φ (Fin.cons v r) = Φ v r := by
  rw [← split_apply, LinearIsometryEquiv.apply_symm_apply]

/-- A lifted pattern is the pattern controlled by the first register. -/
theorem patOp_liftPat {W k : ℕ} (O : L → X → K →L[ℂ] K) (v : Option (Fin W))
    (π : Pat L (Rec W k)) (x : X) :
    patOp O (liftPat v π) x = (split W k K).symm.conjStarAlgEquiv
      (MaskedProgram.masked (fun v' => decide (v' = v)) (patOp O π x)) := by
  ext Ψ r
  rw [← Fin.cons_self_tail r, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    split_symm_coord, MaskedProgram.masked_apply, LinearIsometryEquiv.symm_symm]
  simp only [patOp, Joint.fiber_apply, liftPat, Fin.cons_zero, Fin.tail_cons, decide_eq_true_eq]
  split_ifs with h
  · rfl
  · rfl

/-- Lift a label of the selection family. -/
def liftLabel {W k : ℕ} (v : Option (Fin W)) {counted : L → Prop} :
    SelLabel counted (Rec W k) → SelLabel counted (Rec W (k + 1))
  | .inl π => .inl (liftPat v π)
  | .inr π => .inr (liftPat v π)

/-- Lifting keeps the weight. -/
@[simp] theorem selWeight_liftLabel {W k : ℕ} (v : Option (Fin W)) {counted : L → Prop}
    (c : SelLabel counted (Rec W k)) : selWeight (liftLabel v c) = selWeight c := by
  rcases c with π | π <;> rfl

/-- The lifted label is the label controlled by the first register. -/
theorem selFamily_liftLabel {W k : ℕ} (O : L → X → K →L[ℂ] K) (counted : L → Prop)
    (v : Option (Fin W)) (c : SelLabel counted (Rec W k)) (x : X) :
    selFamily O counted (Rec W (k + 1)) (liftLabel v c) x = (split W k K).symm.conjStarAlgEquiv
      (MaskedProgram.masked (fun v' => decide (v' = v)) (selFamily O counted (Rec W k) c x)) := by
  rcases c with π | π
  · exact patOp_liftPat _ v π x
  · exact patOp_liftPat _ v π x

end

end DeferredMeasurementLowerBounds.Deferral
