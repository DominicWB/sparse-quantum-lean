import SparseHamiltonian.ProgramClockBounds

/-!
# Two ordinary queries for an active parallel program clock

The complete reuse workspace is regrouped by a fixed Hilbert equivalence.
Private clock cells, chronological copies, and public bypass cells become
spectator labels of the same ordinary lookup. A single signed mask activates
only unfinished private branches. The mask changes with the reuse step, but
the physical lookup oracle and register layout do not.
-/

namespace SparseHamiltonian.ActiveLookupClock

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockLinks QueryClockStep ClockStepQuery
open MaskedLookupCurry LookupClockStep ReuseLayerFactorization ActiveClockAlgebra

variable {X A Z : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- One ordinary lookup on the fully regrouped reuse workspace. Only known
register types determine its layout, and no activation mask is part of it. -/
def ordinaryOracle (C : Type*) [Fintype C] (f : X → A → Z) (T d : ℕ) (x : X) :
    ActiveRegisterLayout.Space (Payload A Z) C T d →L[ℂ]
      ActiveRegisterLayout.Space (Payload A Z) C T d :=
  (ActiveRegisterLayout.layout (Payload A Z) C T d).symm.conjStarAlgEquiv
    (MaskedLookupCurry.oracle (I := ActiveRegisterLayout.Label C T d) f x)

/-- The common physical query is unitary on the whole workspace. -/
theorem ordinaryOracle_unitary (C : Type*) [Fintype C] (f : X → A → Z)
    (T d : ℕ) (x : X) : IsUnitary (ordinaryOracle C f T d x) :=
  (MaskedLookupCurry.oracle_unitary f x).transport
    (ActiveRegisterLayout.layout (Payload A Z) C T d).symm

/-- Extend any fixed signed mask by zero on bypass cells and completed branches. -/
def activeSignedMask {C : Type*} (m : C → ℤ) (T d r : ℕ) :
    ActiveRegisterLayout.Label C T d → ℤ
  | .inl ((i, _), j) => if r < ReuseWeights.length d i then m j else 0
  | .inr _ => 0

/-- Fixed regrouping identifies an active signed diagonal with one mask. -/
theorem layout_activeSigned {C : Type*} [Fintype C] (f : X → A → Z)
    (m : C → ℤ) (T d r : ℕ) (x : X) :
    (ActiveRegisterLayout.layout (Payload A Z) C T d).conjStarAlgEquiv
      (activeClock (P := Payload A Z)
        (WeightedClock.diagonal (fun c => localSigned (m c) f x)) T d r) =
      WeightedClock.diagonal (fun i => localSigned (activeSignedMask m T d r i) f x) := by
  rw [ActiveRegisterLayout.layout_activeClock]
  congr 1
  funext i
  rcases i with ⟨⟨i, t⟩, j⟩ | ⟨i, j⟩
  · by_cases h : r < ReuseWeights.length d i <;>
      simp [ActiveRegisterLayout.mask, activeSignedMask, h]
  · simp [ActiveRegisterLayout.mask, activeSignedMask]

/-- Signed clock queries across every unfinished branch and chronological copy
have a full-space two-query implementation using the same ordinary oracle. -/
theorem active_signed_two_queries {C : Type*} [Fintype C] (f : X → A → Z)
    (m : C → ℤ) (T d r : ℕ) :
    Implements (ordinaryOracle C f T d)
      (fun x => activeClock (P := Payload A Z)
        (WeightedClock.diagonal (fun c => localSigned (m c) f x)) T d r) 2 := by
  let e := ActiveRegisterLayout.layout (Payload A Z) C T d
  have h := (diagonal_two_queries (activeSignedMask m T d r) f).transport e.symm
  apply h.congr
  intro x
  rw [← layout_activeSigned f m T d r x]
  exact e.conjStarAlgEquiv.symm_apply_apply _

/-- A fixed unitary clock factor adds no queries to the active signed SELECT.
The same two-query primitive works for every reuse index and arbitrary finite
clock labels, including dependent labels for clocks of unequal lengths. -/
theorem activeClock_fixed_signed_two_queries {C : Type*} [Fintype C]
    (f : X → A → Z)
    (F : PiLp 2 (fun _ : C => Payload A Z) →L[ℂ] PiLp 2 (fun _ : C => Payload A Z))
    (hF : IsUnitary F) (m : C → ℤ) (T d r : ℕ) :
    Implements (ordinaryOracle C f T d)
      (fun x => activeClock (P := Payload A Z)
        (F ∘L WeightedClock.diagonal (fun c => localSigned (m c) f x)) T d r) 2 := by
  have hFixed := Implements.fixed (O := ordinaryOracle C f T d)
    (activeClock (P := Payload A Z) F T d r) (activeClock_unitary F hF T d r)
  have h := hFixed.mul (active_signed_two_queries f m T d r)
  simpa only [Nat.zero_add] using h.congr
    (fun x => (activeClock_comp F (WeightedClock.diagonal (fun c => localSigned (m c) f x))
      T d r).symm)

/-- The actual full reuse workspace for one program clock. -/
abbrev Space (f : X → A → Z) (p : Program (localSigned 1 f)) (T d : ℕ) :=
  ActiveRegisterLayout.Space (Payload A Z) (Fin (p.count + 1 + 1)) T d

/-- The common primitive lookup, in the actual reuse-register layout.
It is independent of the reuse step and all activation masks. -/
def commonOracle (f : X → A → Z) (p : Program (localSigned 1 f)) (T d : ℕ) (x : X) :
    Space f p T d →L[ℂ] Space f p T d :=
  (ActiveRegisterLayout.layout (Payload A Z) (Fin (p.count + 1 + 1)) T d).symm.conjStarAlgEquiv
    (MaskedLookupCurry.oracle
      (I := ActiveRegisterLayout.Label (Fin (p.count + 1 + 1)) T d) f x)

/-- The supplied physical oracle is genuinely unitary on every register state. -/
theorem commonOracle_unitary (f : X → A → Z) (p : Program (localSigned 1 f))
    (T d : ℕ) (x : X) : IsUnitary (commonOracle f p T d x) :=
  (MaskedLookupCurry.oracle_unitary f x).transport
    (ActiveRegisterLayout.layout (Payload A Z) (Fin (p.count + 1 + 1)) T d).symm

/-- Clock-query polarities on unfinished private branches; every bypass cell
and every completed branch has zero query weight. -/
def signedMask (f : X → A → Z) (p : Program (localSigned 1 f)) (T d r : ℕ) :
    ActiveRegisterLayout.Label (Fin (p.count + 1 + 1)) T d → ℤ
  | .inl ((i, _), j) => if r < ReuseWeights.length d i then clockMask f p j else 0
  | .inr _ => 0

/-- Regrouping identifies the only input-dependent factor with one signed mask. -/
theorem layout_selectedQueries (f : X → A → Z) (p : Program (localSigned 1 f))
    (T d r : ℕ) (x : X) :
    (ActiveRegisterLayout.layout (Payload A Z) (Fin (p.count + 1 + 1)) T d).conjStarAlgEquiv
      (activeClock (P := Payload A Z) (selectedQueries p x) T d r) =
      WeightedClock.diagonal (fun i => localSigned (signedMask f p T d r i) f x) := by
  rw [← signed_diagonal_eq_selected f p x,
    ActiveRegisterLayout.layout_activeClock]
  congr 1
  funext i
  rcases i with ⟨⟨i, t⟩, j⟩ | ⟨i, j⟩
  · by_cases h : r < ReuseWeights.length d i <;>
      simp [ActiveRegisterLayout.mask, signedMask, h]
  · simp [ActiveRegisterLayout.mask, signedMask]

/-- All selected forward/inverse letters on all active chronological copies
cost two calls to the same ordinary lookup. -/
theorem active_selectedQueries_two_queries (f : X → A → Z)
    (p : Program (localSigned 1 f)) (T d r : ℕ) :
    Implements (commonOracle f p T d)
      (fun x => activeClock (P := Payload A Z) (selectedQueries p x) T d r) 2 := by
  let e := ActiveRegisterLayout.layout (Payload A Z) (Fin (p.count + 1 + 1)) T d
  have h := (diagonal_two_queries (signedMask f p T d r) f).transport e.symm
  apply h.congr
  intro x
  rw [← layout_selectedQueries f p T d r x]
  exact e.conjStarAlgEquiv.symm_apply_apply _

/-- All fixed clock-link gates and the phased cyclic shift combined. -/
def fixedClockGate (f : X → A → Z) (p : Program (localSigned 1 f)) :
    ClockOperators.H (p.count + 1) (Payload A Z) →L[ℂ]
      ClockOperators.H (p.count + 1) (Payload A Z) :=
  phasedShift (p.count + 1) ∘L
    paddedSelect (p.count + 1) (fun j => (clockLinkData p j.val).1.val)

/-- The compiled fixed clock factor is a table-independent unitary gate. -/
theorem fixedClockGate_unitary (f : X → A → Z) (p : Program (localSigned 1 f)) :
    IsUnitary (fixedClockGate f p) :=
  (phasedShift_unitary (p.count + 1)).mul
    (paddedSelect_unitary (p.count + 1) _ (fun j => (clockLinkData p j.val).1.property))

/-- The active parallel clock is a fixed active gate followed by the single
selected-query factor, even for completed branches. -/
theorem activeClock_factor (f : X → A → Z) (p : Program (localSigned 1 f))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (T d r : ℕ) (x : X) :
    activeClock (P := Payload A Z) (programClock p (localSigned_unitary 1 f) hInv x) T d r =
      activeClock (P := Payload A Z) (fixedClockGate f p) T d r ∘L
        activeClock (P := Payload A Z) (selectedQueries p x) T d r := by
  rw [← activeClock_comp]
  congr 1
  rw [programClock_factor]
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

/-- Every active clock step has a two-query implementation using a common
ordinary lookup oracle independent of the reuse index. -/
theorem activeClock_two_queries (f : X → A → Z) (p : Program (localSigned 1 f))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (T d r : ℕ) :
    Implements (commonOracle f p T d)
      (fun x => activeClock (P := Payload A Z)
        (programClock p (localSigned_unitary 1 f) hInv x) T d r) 2 := by
  have hFixed := Implements.fixed (O := commonOracle f p T d)
    (activeClock (P := Payload A Z) (fixedClockGate f p) T d r)
    (activeClock_unitary (fixedClockGate f p) (fixedClockGate_unitary f p) T d r)
  have h := hFixed.mul (active_selectedQueries_two_queries f p T d r)
  simpa only [Nat.zero_add] using h.congr
    (fun x => (activeClock_factor f p hInv T d r x).symm)

/-- A single physical oracle supplies every active step required by synchronized
reuse. Each witness circuit is uniform over all unknown oracle inputs. -/
theorem all_activeClock_two_queries (f : X → A → Z) (p : Program (localSigned 1 f))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (T d : ℕ) :
    (∀ x, IsUnitary (commonOracle f p T d x)) ∧
      ∀ r, Implements (commonOracle f p T d)
        (fun x => activeClock (P := Payload A Z)
          (programClock p (localSigned_unitary 1 f) hInv x) T d r) 2 :=
  ⟨commonOracle_unitary f p T d, activeClock_two_queries f p hInv T d⟩

end
end SparseHamiltonian.ActiveLookupClock
