import SparseHamiltonian.NativeMaskedOracle

/-!
# Six ordinary native queries implement one distributed clock step

The forward, inverse and inactive letters are extracted from the original
program syntax. Two disjoint fixed masks implement the selected letters using
the native three-query control construction. Fixed link gates and the phased
clock shift add no queries. This proves a native analogue of the lookup clock
step without assuming inverse tables or coherent native SELECT access.
-/
namespace SparseHamiltonian.NativeProgramClock

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockLinks QueryClockStep ClockStepQuery
open scoped InnerProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {ι B X : Type*} [Fintype ι] [Fintype B] [DecidableEq B]

/-- Query direction and bypass are fixed classical data. -/
def forwardMask (choice : ι → Option Bool) (i : ι) : Bool :=
  decide (choice i = some false)

def inverseMask (choice : ι → Option Bool) (i : ι) : Bool :=
  decide (choice i = some true)

omit [Fintype ι] in
/-- The two masks cannot activate simultaneously. -/
theorem masks_disjoint (choice : ι → Option Bool) (i : ι) :
    forwardMask choice i = true → inverseMask choice i = false := by
  cases h : choice i with
  | none => simp [forwardMask, h]
  | some b => cases b <;> simp [forwardMask, inverseMask, h]

omit [DecidableEq B] in
/-- Optional arbitrary native calls decompose into a forward and inverse mask. -/
theorem optional_factor
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : ι → Option Bool) (x : X) :
    WeightedClock.diagonal (fun i => optionalQuery F (choice i) x) =
      MaskedProgram.masked (forwardMask choice) (F x) *
        star (MaskedProgram.masked (inverseMask choice) (F x)) := by
  rw [show star (MaskedProgram.masked (inverseMask choice) (F x)) =
    MaskedProgram.masked (inverseMask choice) (star (F x)) from
      MaskedProgram.masked_adjoint _ _]
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  cases h : choice i with
  | none => simp [MaskedProgram.masked_apply, forwardMask, inverseMask, h, optionalQuery]
  | some b => cases b <;>
      simp [MaskedProgram.masked_apply, forwardMask, inverseMask, h, optionalQuery,
        QueryNormalForm.NormalForm.queryOperator]

/-- Six ordinary native calls realize all optional calls on a common clean
subspace, independently of the number or arrangement of branches. -/
theorem optional_six_queries
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (choice : ι → Option Bool) :
    EncodedOracle.ImplementsOn (NativeMaskedOracle.oracle (ι := ι) F)
      (fun x => WeightedClock.diagonal (fun i => optionalQuery F (choice i) x))
      (NativeMaskedOracle.input a).toContinuousLinearMap 6 := by
  have hp := NativeMaskedOracle.three_query_mask F hF a image hvalid (forwardMask choice)
  have hm := NativeMaskedOracle.three_query_inverse_mask F hF a image hvalid (inverseMask choice)
  exact (hp.mul hm).congr (fun x => (optional_factor F choice x).symm)

variable (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)

/-- Syntax-derived polarity, with a bypass at the return slot. -/
def clockChoice (p : Program F) : Fin (p.count + 1 + 1) → Option Bool :=
  Fin.lastCases none (fun j : Fin (p.count + 1) => (clockLinkData p j.val).2)

omit [DecidableEq B] in
/-- The generic optional native action is exactly the existing program-clock
selected-query operator, including the padded return slot. -/
theorem selected_eq_optional (p : Program F) (x : X) :
    selectedQueries p x =
      WeightedClock.diagonal (fun i => optionalQuery F (clockChoice F p i) x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [selectedQueries, paddedSelect, clockChoice, optionalQuery]
  · simp [selectedQueries, paddedSelect, clockChoice]

/-- The selected native letters cost six ordinary native calls in total. -/
theorem selected_six_queries (p : Program F)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1) :
    EncodedOracle.ImplementsOn
      (NativeMaskedOracle.oracle (ι := Fin (p.count + 1 + 1)) F)
      (selectedQueries p) (NativeMaskedOracle.input a).toContinuousLinearMap 6 :=
  (optional_six_queries F hF a image hvalid (clockChoice F p)).congr
    (fun x => (selected_eq_optional F p x).symm)

/-- One complete step of the genuine distributed involution clock. The count
is constant even when the original program has arbitrarily many native calls. -/
theorem programClock_six_queries (p : Program F)
    (hF : ∀ x, IsUnitary (F x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v)
    (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1) :
    EncodedOracle.ImplementsOn
      (NativeMaskedOracle.oracle (ι := Fin (p.count + 1 + 1)) F)
      (programClock p hF hInv)
      (NativeMaskedOracle.input a).toContinuousLinearMap 6 := by
  let E := (NativeMaskedOracle.input (ι := Fin (p.count + 1 + 1)) a).toContinuousLinearMap
  have hE : E† ∘L E = 1 := (NativeMaskedOracle.input (ι := Fin (p.count + 1 + 1)) a).adjoint_comp_self
  have hs := EncodedOracle.ImplementsOn.fixed
    (O := NativeMaskedOracle.oracle (ι := Fin (p.count + 1 + 1)) F) hE
    (phasedShift (V := EuclideanSpace ℂ B) (p.count + 1)) (phasedShift_unitary _)
  have hg := EncodedOracle.ImplementsOn.fixed
    (O := NativeMaskedOracle.oracle (ι := Fin (p.count + 1 + 1)) F) hE
    (paddedSelect (p.count + 1) (fun j => (clockLinkData p j.val).1.val))
    (paddedSelect_unitary _ _ (fun j => (clockLinkData p j.val).1.property))
  have h := hs.mul (hg.mul (selected_six_queries F p hF a image hvalid))
  exact h.congr (fun x => (programClock_factor p hF hInv x).symm)

end
end SparseHamiltonian.NativeProgramClock
