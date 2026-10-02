import SparseHamiltonian.NativeProgramClock

/-!
# Native clock queries across every active chronological copy

One fixed physical native oracle and one fixed clean encoding serve all reuse
steps. Chronological copies, unequal reuse branches and public bypass cells
are spectators of the same native query. Completed branches use no logical
query. Fixed clock routing adds no native calls.
-/
namespace SparseHamiltonian.NativeActiveClock

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockLinks
open NativeMaskedOracle NativeProgramClock ReuseLayerFactorization ActiveClockAlgebra
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

variable {C B X : Type*} [Fintype C] [Fintype B] [DecidableEq B]

/-- Turn off private calls on completed branches and on every public bypass. -/
def activeChoice (choice : C → Option Bool) (T d r : ℕ) :
    ActiveRegisterLayout.Label C T d → Option Bool
  | .inl ((i,_),c) => if r < ReuseWeights.length d i then choice c else none
  | .inr _ => none

/-- The one physical native oracle is independent of the reuse index and mask. -/
abbrev oracle (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (T d : ℕ) :=
  NativeMaskedOracle.oracle (ι := ActiveRegisterLayout.Label C T d) F

/-- Fixed flattening followed by the same clean native-control ancillas. -/
def input (a : B) (T d : ℕ) :
    ActiveRegisterLayout.Space (EuclideanSpace ℂ B) C T d →ₗᵢ[ℂ]
      Physical (ActiveRegisterLayout.Label C T d) B :=
  (NativeMaskedOracle.input a).comp
    (ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d).toLinearIsometry

omit [DecidableEq B] in
/-- Regrouping exposes only fixed optional native letters on the active cells. -/
theorem layout_active_optional
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (choice : C → Option Bool) (T d r : ℕ) (x : X) :
    (ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d).conjStarAlgEquiv
      (activeClock (P := EuclideanSpace ℂ B)
        (WeightedClock.diagonal (fun c => optionalQuery F (choice c) x)) T d r) =
      WeightedClock.diagonal (fun i => optionalQuery F (activeChoice choice T d r i) x) := by
  rw [ActiveRegisterLayout.layout_activeClock]
  congr 1
  funext i
  rcases i with ⟨⟨j,t⟩,c⟩ | ⟨j,k⟩
  · by_cases h : r < ReuseWeights.length d j <;>
      simp [ActiveRegisterLayout.mask, activeChoice, h, optionalQuery]
  · simp [ActiveRegisterLayout.mask, activeChoice, optionalQuery]

/-- All unfinished private clock cells share six ordinary native calls. The
full coherent clean output is correct, including the public bypass cells. -/
theorem active_optional_six_queries
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (choice : C → Option Bool) (T d r : ℕ) :
    EncodedOracle.ImplementsOn (oracle (C := C) F T d)
      (fun x => activeClock (P := EuclideanSpace ℂ B)
        (WeightedClock.diagonal (fun c => optionalQuery F (choice c) x)) T d r)
      (input (C := C) a T d).toContinuousLinearMap 6 := by
  obtain ⟨p, hp, hcount⟩ := optional_six_queries F hF a image hvalid (activeChoice choice T d r)
  refine ⟨p, fun x => ?_, hcount⟩
  let e := ActiveRegisterLayout.layout (EuclideanSpace ℂ B) C T d
  let E := (NativeMaskedOracle.input (ι := ActiveRegisterLayout.Label C T d) a).toContinuousLinearMap
  change p.eval x ∘L (E ∘L e.toContinuousLinearMap) =
    (E ∘L e.toContinuousLinearMap) ∘L _
  rw [← comp_assoc, hp x, comp_assoc, comp_assoc]
  congr 1
  dsimp only
  rw [← layout_active_optional F choice T d r x]
  apply ContinuousLinearMap.ext
  intro v
  change e (activeClock (P := EuclideanSpace ℂ B)
      (WeightedClock.diagonal (fun c => optionalQuery F (choice c) x)) T d r
        (e.symm (e v))) =
    e (activeClock (P := EuclideanSpace ℂ B)
      (WeightedClock.diagonal (fun c => optionalQuery F (choice c) x)) T d r v)
  rw [e.symm_apply_apply]

/-- An arbitrary fixed clock routing unitary adds no native calls. Both the
logical encoding and the physical oracle remain common to all reuse indices. -/
theorem active_fixed_optional_six_queries
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (G : Logical C B →L[ℂ] Logical C B) (hG : IsUnitary G)
    (choice : C → Option Bool) (T d r : ℕ) :
    EncodedOracle.ImplementsOn (oracle (C := C) F T d)
      (fun x => activeClock (P := EuclideanSpace ℂ B)
        (G ∘L WeightedClock.diagonal (fun c => optionalQuery F (choice c) x)) T d r)
      (input (C := C) a T d).toContinuousLinearMap 6 := by
  have hFixed := EncodedOracle.ImplementsOn.fixed
    (O := oracle (C := C) F T d) (input (C := C) a T d).adjoint_comp_self
    (activeClock (P := EuclideanSpace ℂ B) G T d r) (activeClock_unitary G hG T d r)
  exact (hFixed.mul (active_optional_six_queries F hF a image hvalid choice T d r)).congr
    (fun x => (activeClock_comp G _ T d r).symm)

/-- Apply the native active adapter to the actual syntax-derived clock. -/
theorem programClock_active_six_queries
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : Program F) (hF : ∀ x, IsUnitary (F x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v)
    (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (T d r : ℕ) :
    EncodedOracle.ImplementsOn
      (oracle (C := Fin (p.count + 1 + 1)) F T d)
      (fun x => activeClock (P := EuclideanSpace ℂ B)
        (QueryClockStep.programClock p hF hInv x) T d r)
      (input (C := Fin (p.count + 1 + 1)) a T d).toContinuousLinearMap 6 := by
  let G := ClockStepQuery.phasedShift (V := EuclideanSpace ℂ B) (p.count + 1) ∘L
    ClockStepQuery.paddedSelect (p.count + 1) (fun j => (clockLinkData p j.val).1.val)
  have hG : IsUnitary G :=
    (ClockStepQuery.phasedShift_unitary (p.count + 1)).mul
      (ClockStepQuery.paddedSelect_unitary _ _ (fun j => (clockLinkData p j.val).1.property))
  have h := active_fixed_optional_six_queries F hF a image hvalid G hG (clockChoice F p) T d r
  apply h.congr
  intro x
  congr 1
  rw [← selected_eq_optional F p x, QueryClockStep.programClock_factor]
  exact ContinuousLinearMap.comp_assoc _ _ _

/-- One physical native oracle and one fixed encoding supply every reuse step. -/
theorem all_programClock_active_six_queries
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (p : Program F) (hF : ∀ x, IsUnitary (F x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v)
    (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (T d : ℕ) :
    (∀ x, IsUnitary (oracle (C := Fin (p.count + 1 + 1)) F T d x)) ∧
      ∀ r, EncodedOracle.ImplementsOn
        (oracle (C := Fin (p.count + 1 + 1)) F T d)
        (fun x => activeClock (P := EuclideanSpace ℂ B)
          (QueryClockStep.programClock p hF hInv x) T d r)
        (input (C := Fin (p.count + 1 + 1)) a T d).toContinuousLinearMap 6 :=
  ⟨NativeMaskedOracle.oracle_unitary F hF,
    programClock_active_six_queries F p hF hInv a image hvalid T d⟩

end
end SparseHamiltonian.NativeActiveClock
