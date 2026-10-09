import UnitaryImplementationExtensions.LowerBound

set_option autoImplicit false

/-!
# The entry oracles of the search family as Boolean phase oracles

The hard instances of the lower half of corollary `hs:cor:unitary` of the
manuscript (lines 1647-1666; the reduction to unstructured search at lines
1711-1718) are the search unitaries
`UnitaryImplementationExtensions.SearchFamily.searchMatrix N m`, whose entry
oracle "uses one query to the search oracle". This module records that fact in
the form used by the adaptive lower bounds: each entry oracle of the search
family is the Boolean phase oracle of the marked strings
`Search.markedString c m` for a fixed position map `c`.

* `lookup_eq_phase_marked`: the ordinary reversible entry lookup with an
  arbitrary payload `V`, positions `(j, k)`, `c (j, k) = j + k`
  (`lookupPosition`, from `PhaseBridge.lookup_eq_phase`).
* `entry_oracle_eq_phase_marked`: the released entry oracle of the upper bound,
  `UnitaryEntryOracle.oracle (searchData N) γ η t ε`, for all parameters, with
  `c a = a.1.2 + a.2.2` (`entryPosition`, from `LiftPhase.oracle_eq_phase`).
* `implementsOn_phase_of_entry`, `implementsOn_phase_of_lookup`: a label
  implemented by `q` entry calls on an encoding is implemented by `q` phase
  queries on the same encoding.

Finite-dimensionality is needed only where a space serves as the workspace or
the output space of an adaptive protocol (lossless purification), never for the
encoding target of an oracle. The workspace of the released entry oracle,
`UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε`, is finite-dimensional
by instance search with `synthInstance.maxSize` raised (as in this module; the
default limit fails), so it serves as the workspace of the one-label corollaries.
-/

namespace AdaptiveUnitaryLowerBound.Oracles

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open ContinuousLinearMap
open scoped InnerProduct
set_option synthInstance.maxSize 8192

/-- The position map of the ordinary entry lookup: entry `(j, k)` is marked for
instance `m` iff `j + k = m`. -/
def lookupPosition (N : ℕ) (a : Fin N × Fin N) : Fin N := a.1 + a.2

/-- The position map of the released entry oracle: the flagged entry address
`a` is marked for instance `m` iff the sum of its two index coordinates is `m`. -/
def entryPosition (N : ℕ)
    (a : UnitaryEntryData.Index (Fin N) × UnitaryEntryData.Index (Fin N)) : Fin N :=
  a.1.2 + a.2.2

/-- **The ordinary entry lookup of the search family is a search phase oracle.** -/
theorem lookup_eq_phase_marked (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (N : ℕ) (m : Fin N) :
    LookupControlledGate.oracle (K := V) (searchTable N) m =
      (PhaseBridge.xorFamily (Fin N × Fin N) V).phase
        (Search.markedString (lookupPosition N) m) := by
  refine (PhaseBridge.lookup_eq_phase (searchTable N) m).trans (congrArg _ (funext fun a => ?_))
  simp [Search.markedString, lookupPosition, searchTable_eq_one_iff]

/-- **The released entry oracle of the search family is a search phase oracle**,
for all parameters of the oracle. -/
theorem entry_oracle_eq_phase_marked (N : ℕ) (γ η t ε : ℝ) (m : Fin N) :
    UnitaryEntryOracle.oracle (searchData N) γ η t ε m =
      (LiftPhase.entryFamily (n := Fin N) γ η t ε).phase
        (Search.markedString (entryPosition N) m) := by
  refine (LiftPhase.oracle_eq_phase (searchData N) γ η t ε m).trans
    (congrArg _ (funext fun a => ?_))
  change decide (searchTable N m (a.1.2, a.2.2) = 1) = decide (a.1.2 + a.2.2 = m)
  simp [searchTable_eq_one_iff]

/-- A label implemented by `q` calls of the released entry oracle of the search
family on an encoding is implemented by `q` queries of its search phase oracle
on the same encoding: `entry_oracle_eq_phase_marked` rewritten into the oracle
argument of `EncodedOracle.ImplementsOn`. -/
theorem implementsOn_phase_of_entry (N : ℕ) (γ η t ε : ℝ) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {F : Fin N → W →L[ℂ] W}
    {Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε} {q : ℕ}
    (h : EncodedOracle.ImplementsOn (UnitaryEntryOracle.oracle (searchData N) γ η t ε)
      F Enc q) :
    EncodedOracle.ImplementsOn
      (fun m => (LiftPhase.entryFamily (n := Fin N) γ η t ε).phase
        (Search.markedString (entryPosition N) m)) F Enc q := by
  have hfun : UnitaryEntryOracle.oracle (searchData N) γ η t ε = fun m =>
      (LiftPhase.entryFamily (n := Fin N) γ η t ε).phase
        (Search.markedString (entryPosition N) m) :=
    funext (entry_oracle_eq_phase_marked N γ η t ε)
  rw [hfun] at h
  exact h

/-- A label implemented by `q` calls of the ordinary entry lookup of the search
family on an encoding is implemented by `q` queries of its search phase oracle
on the same encoding: `lookup_eq_phase_marked` rewritten into the oracle
argument of `EncodedOracle.ImplementsOn`. -/
theorem implementsOn_phase_of_lookup (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (N : ℕ) {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {F : Fin N → W →L[ℂ] W}
    {Enc : W →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => V)} {q : ℕ}
    (h : EncodedOracle.ImplementsOn
      (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) F Enc q) :
    EncodedOracle.ImplementsOn
      (fun m => (PhaseBridge.xorFamily (Fin N × Fin N) V).phase
        (Search.markedString (lookupPosition N) m)) F Enc q := by
  have hfun : (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) = fun m =>
      (PhaseBridge.xorFamily (Fin N × Fin N) V).phase
        (Search.markedString (lookupPosition N) m) :=
    funext (lookup_eq_phase_marked V N)
  rw [hfun] at h
  exact h

end
end AdaptiveUnitaryLowerBound.Oracles
