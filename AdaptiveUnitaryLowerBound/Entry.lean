import AdaptiveUnitaryLowerBound.Theorem

set_option autoImplicit false

/-!
# Heralded and unheralded adaptive algorithms over the released entry oracle

The lower half of the last sentence of corollary `hs:cor:unitary` of the
manuscript (reduction in the proof of Corollary `hs:cor:unitary`) for adaptive
algorithms whose only oracle is the released entry oracle of the search family
(`entryOracles`: one label, `UnitaryEntryOracle.oracle (searchData N) γ η t ε`
for any parameters, on its own workspace), with the count of entry calls
(`T.worstCost (fun _ => 1)`; the entry oracle is a Boolean phase oracle,
`Oracles.entry_oracle_eq_phase_marked`, hence its own inverse, so inverse calls
are plain calls), and for algorithms over its four call forms
(`AdaptiveODELowerBound.Access.callFamily`: the call, its inverse, its
controlled form and its controlled inverse, each counted once).
Accuracy is `AdaptiveHamiltonianLowerBound.DensityAccurate` of the conditional
output for `U_m |0⟩`, with `ε₀ ≤ 1/2`.

* Heralded output, success probability at least `2/3` on every instance (the
  convention of the package's adaptive lower bounds): `heralded_tree`,
  `heralded_calls_tree`, `(1 - 2ε₀)² sqrt (N - 1) ≤ 9 Q`.
* Unheralded output, the case of success probability one: `unheralded_tree`,
  `unheralded_calls_tree`, `(1 - 2ε₀)² sqrt (N - 1) ≤ 4 Q`.

The access facts of the one-label family (`entryOracles_unitary`,
`one_isometry`, `entryOracles_implementsOn`) instantiate
`Theorem.implementation_count_ge_tree` and
`Theorem.implementation_count_ge_calls_tree` with the identity encoding.

At every fixed `ε₀ < 1/2` both are `Ω(√N)`; at `ε₀ = 1/2` they are empty (here `ε₀` is
trace-distance accuracy). For unitary programs with the manuscript's operator-norm
error the whole range `0 < ε ≤ 1/2` is covered: over the entry oracle itself by
the non-adaptive `UnitaryImplementationExtensions.LowerBound.implementation_count_ge`,
and over its four call forms by `calls_program_of_error`,
`(1 - 2ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) ≤ 2 Q` for `ε₀ ≤ 1`.
-/

namespace AdaptiveUnitaryLowerBound.Entry

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

variable {E Fl G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The released entry oracle of the search family as a one-label family. -/
abbrev entryOracles (N : ℕ) (γ η t ε : ℝ) :
    Unit → Fin N → UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε →L[ℂ]
      UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε :=
  fun _ => UnitaryEntryOracle.oracle (searchData N) γ η t ε

/-- The one-label family `entryOracles` is unitary on every instance. -/
theorem entryOracles_unitary (N : ℕ) (γ η t ε : ℝ) (l : Unit) (m : Fin N) :
    OracleCircuit.IsUnitary (entryOracles N γ η t ε l m) :=
  UnitaryEntryOracle.oracle_unitary (searchData N) γ η t ε m

/-- The identity is an isometric encoding of the workspace of the released
entry oracle. -/
theorem one_isometry (N : ℕ) (γ η t ε : ℝ) :
    (1 : UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε →L[ℂ]
      UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)† ∘L
      (1 : UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε →L[ℂ]
        UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε) = 1 := by
  ext v; simp

/-- The label of `entryOracles` is one call of the released entry oracle on the
identity encoding. -/
theorem entryOracles_implementsOn (N : ℕ) (γ η t ε : ℝ) (l : Unit) :
    EncodedOracle.ImplementsOn (UnitaryEntryOracle.oracle (searchData N) γ η t ε)
      (entryOracles N γ η t ε l) 1 1 :=
  ⟨.query, fun _ => by ext v; rfl, le_rfl⟩

/-- The constant of the heralded bounds: `((2/3) a)² s ≤ 4 Q` gives
`a² s ≤ 9 Q`. -/
theorem le_nine_of_two_thirds {a s Q : ℝ} (h : (2 / 3 * a) ^ 2 * s ≤ 4 * Q) :
    a ^ 2 * s ≤ 9 * Q := by
  have e : (2 / 3 * a) ^ 2 * s = 4 / 9 * (a ^ 2 * s) := by ring
  linarith

/-- **Heralded adaptive algorithms** (Corollary `hs:cor:unitary`, last
sentence). Every adaptive protocol over the released entry oracle of the search
family that on every instance `m` succeeds with probability at least `2/3` and
outputs, conditionally on success, an `ε₀`-accurate copy of `U_m |0⟩`
(`ε₀ ≤ 1/2`) makes at least `(1 - 2ε₀)² sqrt (N - 1) / 9` entry calls in the
worst case. -/
theorem heralded_tree {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (entryOracles N γ η t ε) Fl E) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, 2 / 3 ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (1 - 2 * ε₀) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 9 * T.worstCost (fun _ => 1) :=
  le_nine_of_two_thirds (Theorem.implementation_count_ge_tree hN γ η t ε 1
    (one_isometry N γ η t ε) (entryOracles_unitary N γ η t ε) (fun _ => 1)
    (entryOracles_implementsOn N γ η t ε) T e he (s₀ := 2 / 3) (by norm_num) hε₀ hsucc hacc)

/-- **Unheralded adaptive algorithms** (Corollary `hs:cor:unitary`, last
sentence). Every adaptive protocol over the released entry oracle of the search
family whose output is always accepted (success probability one) and is
`ε₀`-accurate for `U_m |0⟩` on every instance `m` (`ε₀ ≤ 1/2`) makes at least
`(1 - 2ε₀)² sqrt (N - 1) / 4` entry calls in the worst case. -/
theorem unheralded_tree {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (entryOracles N γ η t ε) Fl E) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, T.successMass m = 1)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (1 - 2 * ε₀) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * T.worstCost (fun _ => 1) := by
  simpa only [one_mul] using Theorem.implementation_count_ge_tree hN γ η t ε 1
    (one_isometry N γ η t ε) (entryOracles_unitary N γ η t ε) (fun _ => 1)
    (entryOracles_implementsOn N γ η t ε) T e he (s₀ := 1) one_pos hε₀
    (fun m => (hsucc m).ge) hacc

/-- **Heralded adaptive algorithms with controlled and controlled-inverse
calls** (Corollary `hs:cor:unitary`, last sentence). The bound of
`heralded_tree` for adaptive protocols over the four call forms of the released
entry oracle, each call counted once. -/
theorem heralded_calls_tree {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (AdaptiveODELowerBound.Access.callFamily (entryOracles N γ η t ε)) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, 2 / 3 ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (1 - 2 * ε₀) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 9 * T.worstCost (fun _ => 1) :=
  le_nine_of_two_thirds (Theorem.implementation_count_ge_calls_tree hN γ η t ε 1
    (one_isometry N γ η t ε) (entryOracles_unitary N γ η t ε) (fun _ => 1)
    (entryOracles_implementsOn N γ η t ε) T e he (s₀ := 2 / 3) (by norm_num) hε₀ hsucc hacc)

/-- **Unheralded adaptive algorithms with controlled and controlled-inverse
calls** (Corollary `hs:cor:unitary`, last sentence). The bound of
`unheralded_tree` for adaptive protocols over the four call forms of the
released entry oracle, each call counted once. -/
theorem unheralded_calls_tree {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (AdaptiveODELowerBound.Access.callFamily (entryOracles N γ η t ε)) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, T.successMass m = 1)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (1 - 2 * ε₀) ^ 2 * Real.sqrt ((N : ℝ) - 1) ≤ 4 * T.worstCost (fun _ => 1) := by
  simpa only [one_mul] using Theorem.implementation_count_ge_calls_tree hN γ η t ε 1
    (one_isometry N γ η t ε) (entryOracles_unitary N γ η t ε) (fun _ => 1)
    (entryOracles_implementsOn N γ η t ε) T e he (s₀ := 1) one_pos hε₀
    (fun m => (hsucc m).ge) hacc

/-- **Unitary programs with controlled and controlled-inverse calls and the
manuscript's operator-norm error** (Corollary `hs:cor:unitary`, last sentence).
Every program over the four call forms of the released entry oracle of the
search family that implements every search unitary `U_m` on an isometric
encoding `J` into the controlled workspace with operator-norm error at most
`ε₀ ≤ 1` makes at least `(1 - 2ε₀ sqrt (1 - ε₀²/4)) sqrt (N - 1) / 2` calls,
each call counted once. The factor is positive on the corollary's whole range
`0 < ε₀ ≤ 1/2`. -/
theorem calls_program_of_error {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program
      (AdaptiveODELowerBound.Access.callFamily (entryOracles N γ η t ε)))
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1)
    (hErr : ∀ m, ‖p.eval m ∘L J - J ∘L
      SparseStateOverlap.matrixOperator (searchMatrix N m)‖ ≤ ε₀) :
    (1 - 2 * ε₀ * Real.sqrt (1 - ε₀ ^ 2 / 4)) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * p.cost (fun _ => 1) :=
  Theorem.implementation_count_ge_calls_program_of_error hN γ η t ε 1
    (one_isometry N γ η t ε) (entryOracles_unitary N γ η t ε) (fun _ => 1)
    (entryOracles_implementsOn N γ η t ε) p J hJ hε₀ hErr

end
end AdaptiveUnitaryLowerBound.Entry
