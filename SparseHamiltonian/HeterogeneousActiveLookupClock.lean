import SparseHamiltonian.HeterogeneousLookupClock

/-!
# Active reuse of heterogeneous program clocks with two ordinary queries

The signed query masks for unequal program clocks share one physical oracle
across every chronological copy and reuse step. Completed branches and public
bypass cells are inactive; their scratch can be arbitrary. The original program
counts affect the register layout but do not multiply the cost of one step.
-/

namespace SparseHamiltonian.HeterogeneousActiveLookupClock

noncomputable section
open ContinuousLinearMap OracleCircuit MaskedLookupCurry HeterogeneousLookupClock
open ReuseLayerFactorization

variable {X I A Z : Type*} [Fintype I] [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- The ordinary oracle common to every active step of the whole clock family. -/
def commonOracle (f : X → A → Z) (p : I → Program (localSigned 1 f)) (T d : ℕ) (x : X) :
    ActiveRegisterLayout.Space (Payload A Z) (Slot f p) T d →L[ℂ]
      ActiveRegisterLayout.Space (Payload A Z) (Slot f p) T d :=
  ActiveLookupClock.ordinaryOracle (Slot f p) f T d x

/-- The common physical oracle is a unitary on the entire reuse workspace. -/
theorem commonOracle_unitary (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (T d : ℕ) (x : X) : IsUnitary (commonOracle f p T d x) :=
  ActiveLookupClock.ordinaryOracle_unitary (Slot f p) f T d x

/-- Each active heterogeneous clock layer costs two ordinary queries under the
same physical oracle, independent of the reuse index or program lengths. -/
theorem activeClock_two_queries (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (T d r : ℕ) :
    Implements (commonOracle f p T d)
      (fun x => activeClock (P := Payload A Z) (flatFamilyClock f p hInv x) T d r) 2 := by
  have h := ActiveLookupClock.activeClock_fixed_signed_two_queries f
    (flatFixed f p) (flatFixed_unitary f p) (mask f p) T d r
  apply h.congr
  intro x
  rw [flatFamilyClock_factor]
  rfl

/-- One unitary physical oracle simultaneously supplies all active-step certificates. -/
theorem all_activeClock_two_queries (f : X → A → Z)
    (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (T d : ℕ) :
    (∀ x, IsUnitary (commonOracle f p T d x)) ∧
      ∀ r, Implements (commonOracle f p T d)
        (fun x => activeClock (P := Payload A Z) (flatFamilyClock f p hInv x) T d r) 2 :=
  ⟨commonOracle_unitary f p T d, activeClock_two_queries f p hInv T d⟩

end
end SparseHamiltonian.HeterogeneousActiveLookupClock
