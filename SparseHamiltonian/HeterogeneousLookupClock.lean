import SparseHamiltonian.ActiveLookupClock

/-!
# Two-query SELECT for heterogeneous program clocks

Each branch can have a different original program and query count. A fixed
Hilbert-space flattening exposes the disjoint union of their actual clock slots
as the spectator label of one ordinary lookup. All signed query letters are
implemented simultaneously using two calls to that oracle. The remaining
selected link gates and phased shifts are fixed, table-independent unitaries.
-/

namespace SparseHamiltonian.HeterogeneousLookupClock

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockLinks QueryClockStep ClockStepQuery
open MaskedLookupCurry
open scoped InnerProduct

variable {X I A Z : Type*} [Fintype I] [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- The heterogeneous direct sum of the actual, unpadded program clocks. -/
abbrev Space (f : X → A → Z) (p : I → Program (localSigned 1 f)) :=
  PiLp 2 (fun i => ClockOperators.H ((p i).count + 1) (Payload A Z))

/-- One ordinary oracle spectator register contains branch and local clock slot. -/
abbrev Slot (f : X → A → Z) (p : I → Program (localSigned 1 f)) :=
  Sigma (fun i => Fin ((p i).count + 1 + 1))

/-- Regroup the actual unequal clock registers into one disjoint-union label.
This equivalence depends only on the program syntax, not the unknown input. -/
def flatten (f : X → A → Z) (p : I → Program (localSigned 1 f)) :
    Space f p ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Slot f p => Payload A Z) :=
  (LinearIsometryEquiv.piLpCurry ℂ 2
    (fun i (_ : Fin ((p i).count + 1 + 1)) => Payload A Z)).symm

@[simp] theorem flatten_apply (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (v : Space f p) (i : I) (j : Fin ((p i).count + 1 + 1)) :
    flatten f p v ⟨i, j⟩ = v i j := rfl

@[simp] theorem flatten_symm_apply (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (v : PiLp 2 (fun _ : Slot f p => Payload A Z))
    (i : I) (j : Fin ((p i).count + 1 + 1)) :
    (flatten f p).symm v i j = v ⟨i, j⟩ := rfl

/-- One common ordinary scratch lookup in the native heterogeneous clock layout. -/
def oracle (f : X → A → Z) (p : I → Program (localSigned 1 f)) (x : X) :
    Space f p →L[ℂ] Space f p :=
  (flatten f p).symm.conjStarAlgEquiv
    (MaskedLookupCurry.oracle (I := Slot f p) f x)

/-- The branch, local slot and target are spectators of this ordinary query. -/
@[simp] theorem oracle_apply (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (x : X) (v : Space f p) (i : I) (j : Fin ((p i).count + 1 + 1))
    (a : A) (z y : Z) :
    oracle f p x v i j ((a, z), y) = v i j ((a, z), y - f x a) := rfl

/-- The native oracle satisfies both unitary identities. -/
theorem oracle_unitary (f : X → A → Z) (p : I → Program (localSigned 1 f)) (x : X) :
    IsUnitary (oracle f p x) :=
  (MaskedLookupCurry.oracle_unitary (I := Slot f p) f x).transport (flatten f p).symm

/-- The one signed mask includes every actual slot of every branch. -/
def mask (f : X → A → Z) (p : I → Program (localSigned 1 f)) (s : Slot f p) : ℤ :=
  LookupClockStep.clockMask f (p s.1) s.2

/-- The literal direct-sum SELECT of the query letters in every program clock. -/
def selected (f : X → A → Z) (p : I → Program (localSigned 1 f)) (x : X) :
    Space f p →L[ℂ] Space f p :=
  WeightedClock.diagonal (fun i => selectedQueries (p i) x)

/-- Each branch of the signed mask is exactly its syntax-derived query SELECT. -/
theorem signed_diagonal_eq_selected (f : X → A → Z)
    (p : I → Program (localSigned 1 f)) (x : X) :
    (flatten f p).symm.conjStarAlgEquiv
      (WeightedClock.diagonal (fun s => localSigned (mask f p s) f x)) = selected f p x := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  apply PiLp.ext
  intro j
  change localSigned (mask f p ⟨i, j⟩) f x (v i j) = selectedQueries (p i) x (v i) j
  have h := congrArg
    (fun U : ClockOperators.H ((p i).count + 1) (Payload A Z) →L[ℂ]
      ClockOperators.H ((p i).count + 1) (Payload A Z) => U (v i) j)
    (LookupClockStep.signed_diagonal_eq_selected f (p i) x)
  exact h

/-- Heterogeneous selected query letters cost two calls to one common oracle. -/
theorem selected_two_queries (f : X → A → Z) (p : I → Program (localSigned 1 f)) :
    Implements (oracle f p) (selected f p) 2 := by
  have h := (diagonal_two_queries (mask f p) f).transport (flatten f p).symm
  exact h.congr fun x => signed_diagonal_eq_selected f p x

section DiagonalUnitary
variable {J : Type*} [Fintype J] {V : J → Type*}
  [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℂ (V j)]
  [∀ j, CompleteSpace (V j)]

/-- A direct sum of genuine unitaries is a genuine unitary, even with unequal spaces. -/
theorem diagonal_unitary (U : ∀ j, V j →L[ℂ] V j) (hU : ∀ j, IsUnitary (U j)) :
    IsUnitary (WeightedClock.diagonal U) := by
  constructor
  · exact WeightedClock.diagonal_isometry U (fun j => (hU j).1)
  · change WeightedClock.diagonal U ∘L (WeightedClock.diagonal U)† = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    have hRight : ∀ j, U j ∘L (U j)† = 1 := fun j => (hU j).2
    simp only [hRight, WeightedClock.diagonal_one]

end DiagonalUnitary

/-- Fixed phased shifts and the selected fixed link gates, combined in each branch. -/
def fixedGate (f : X → A → Z) (p : I → Program (localSigned 1 f)) :
    Space f p →L[ℂ] Space f p :=
  WeightedClock.diagonal (fun i =>
    phasedShift ((p i).count + 1) *
      paddedSelect ((p i).count + 1) (fun j => (clockLinkData (p i) j.val).1.val))

/-- Every non-query operation used in the family-clock implementation is fixed and unitary. -/
theorem fixedGate_unitary (f : X → A → Z) (p : I → Program (localSigned 1 f)) :
    IsUnitary (fixedGate f p) := by
  apply diagonal_unitary
  intro i
  apply (phasedShift_unitary _).mul
  apply paddedSelect_unitary
  intro j
  exact (clockLinkData (p i) j.val).1.property

/-- The actual distributed program clock in each heterogeneous branch. -/
def familyClock (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (x : X) :
    Space f p →L[ℂ] Space f p :=
  WeightedClock.diagonal (fun i => programClock (p i) (localSigned_unitary 1 f) (hInv i) x)

omit [Fintype I] in
/-- The factorization uses only fixed gates and the explicit signed lookup SELECT. -/
theorem familyClock_factor (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (x : X) :
    familyClock f p hInv x = fixedGate f p * selected f p x := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  have h := congrArg
    (fun U : ClockOperators.H ((p i).count + 1) (Payload A Z) →L[ℂ]
      ClockOperators.H ((p i).count + 1) (Payload A Z) => U (v i))
    (programClock_factor (p i) (localSigned_unitary 1 f) (hInv i) x)
  exact h

/-- SELECT of all heterogeneous distributed clocks needs two ordinary queries.
No maximum program length or number of branches multiplies this cost. -/
theorem familyClock_two_queries (f : X → A → Z)
    (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) :
    Implements (oracle f p) (familyClock f p hInv) 2 := by
  have h := (Implements.fixed (O := oracle f p) (fixedGate f p) (fixedGate_unitary f p)).mul
    (selected_two_queries f p)
  exact h.congr fun x => (familyClock_factor f p hInv x).symm

/-- The direct-sum clock remains unitary under the concrete query implementation. -/
theorem familyClock_unitary (f : X → A → Z)
    (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (x : X) :
    IsUnitary (familyClock f p hInv x) :=
  (familyClock_two_queries f p hInv).unitary (oracle_unitary f p) x

/-- The selected query family in the disjoint-union clock layout. -/
theorem flatten_selected (f : X → A → Z) (p : I → Program (localSigned 1 f)) (x : X) :
    (flatten f p).conjStarAlgEquiv (selected f p x) =
      WeightedClock.diagonal (fun s => localSigned (mask f p s) f x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  rintro ⟨i, j⟩
  have h := congrArg
    (fun U : ClockOperators.H ((p i).count + 1) (Payload A Z) →L[ℂ]
      ClockOperators.H ((p i).count + 1) (Payload A Z) => U ((flatten f p).symm v i) j)
    (LookupClockStep.signed_diagonal_eq_selected f (p i) x)
  exact h.symm

/-- The fixed family gate in the single spectator-register layout. -/
def flatFixed (f : X → A → Z) (p : I → Program (localSigned 1 f)) :
    PiLp 2 (fun _ : Slot f p => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : Slot f p => Payload A Z) :=
  (flatten f p).conjStarAlgEquiv (fixedGate f p)

/-- The flattened fixed family gate is a table-independent unitary. -/
theorem flatFixed_unitary (f : X → A → Z) (p : I → Program (localSigned 1 f)) :
    IsUnitary (flatFixed f p) := (fixedGate_unitary f p).transport (flatten f p)

/-- The actual family of distributed clocks in the single spectator-register layout. -/
def flatFamilyClock (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (x : X) :
    PiLp 2 (fun _ : Slot f p => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : Slot f p => Payload A Z) :=
  (flatten f p).conjStarAlgEquiv (familyClock f p hInv x)

/-- A heterogeneous family is one explicit signed lookup SELECT followed by
one fixed unitary containing every phased shift and fixed link gate. -/
theorem flatFamilyClock_factor (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (x : X) :
    flatFamilyClock f p hInv x = flatFixed f p *
      WeightedClock.diagonal (fun s => localSigned (mask f p s) f x) := by
  unfold flatFamilyClock flatFixed
  rw [familyClock_factor, map_mul, flatten_selected]

/-- Flattening exposes exactly the ordinary common lookup from `MaskedLookupCurry`. -/
theorem flatten_oracle (f : X → A → Z) (p : I → Program (localSigned 1 f)) (x : X) :
    (flatten f p).conjStarAlgEquiv (oracle f p x) =
      MaskedLookupCurry.oracle (I := Slot f p) f x := by
  ext v s a
  rfl

/-- The same two-query certificate directly over an ordinary lookup with the
single spectator label `Sigma i (Fin ((p i).count + 2))`. -/
theorem flat_familyClock_two_queries (f : X → A → Z)
    (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) :
    Implements (MaskedLookupCurry.oracle (I := Slot f p) f)
      (fun x => (flatten f p).conjStarAlgEquiv (familyClock f p hInv x)) 2 := by
  have h := (familyClock_two_queries f p hInv).transport (flatten f p)
  have hOracle : (fun x => (flatten f p).conjStarAlgEquiv (oracle f p x)) =
      MaskedLookupCurry.oracle (I := Slot f p) f := funext (flatten_oracle f p)
  rw [hOracle] at h
  exact h

end
end SparseHamiltonian.HeterogeneousLookupClock
