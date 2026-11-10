import MeasuredUnitaryLowerBound.Endpoint.Tree
import AdaptiveUnitaryLowerBound.Entry

set_option autoImplicit false

/-!
# Entry-call counts at trace-distance error `1/2`

The trace-distance form of the endpoint `ε = 1/2` of the error range `0 < ε ≤ 1/2` of Corollary
`hs:cor:unitary` of the manuscript, for adaptive protocols whose only oracle is the released entry
oracle of the search family (`AdaptiveUnitaryLowerBound.Entry.entryOracles`), with plain calls or
with the four call forms (`AdaptiveODELowerBound.Access.callFamily`, Section `hsl:sec:main`: with
inverses and the controls of Lemma `access:lem:control`); the cost is the number of entry calls in
the worst case.

* `unheralded_tree_half`, `unheralded_calls_tree_half`: success probability one,
  `(N - 2)² ≤ 16 (N - 1) √(N - 1) Q`;
* `heralded_tree_half`, `heralded_calls_tree_half`: success probability at least `2/3`,
  `(N - 2)² ≤ 36 (N - 1) √(N - 1) Q`;
* `sqrt_le_of_half`: for `N ≥ 3`, `(N - 2)² ≤ C (N - 1) √(N - 1) Q` gives `√(N - 1) ≤ 4 C Q`;
  `unheralded_tree_sqrt` (`√(N - 1) ≤ 64 Q`) and `heralded_tree_sqrt` (`√(N - 1) ≤ 144 Q`)
  are the `Ω(√N)` half of `Θ(√N)` at the endpoint, and `unheralded_calls_tree_sqrt`,
  `heralded_calls_tree_sqrt` are the same over the four call forms.
-/

namespace MeasuredUnitaryLowerBound.Adaptive

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveUnitaryLowerBound.Entry (entryOracles)
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192

variable {E Fl G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **From the endpoint form to `√N`**: for `N ≥ 3`, `(N - 2)² ≤ C (N - 1) √(N - 1) Q`
implies `√(N - 1) ≤ 4 C Q` (since `N - 2 ≥ (N - 1)/2`). -/
theorem sqrt_le_of_half {N : ℕ} (hN : 3 ≤ N) {C Q : ℝ}
    (h : ((N : ℝ) - 2) ^ 2 ≤ C * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * Q) :
    Real.sqrt ((N : ℝ) - 1) ≤ 4 * C * Q := by
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hquart : ((N : ℝ) - 1) ^ 2 / 4 ≤ ((N : ℝ) - 2) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (N : ℝ) - 3)
      (by linarith : (0 : ℝ) ≤ 3 * (N : ℝ) - 5)]
  have hs : 0 < Real.sqrt ((N : ℝ) - 1) := Real.sqrt_pos.2 ha
  have hsq : Real.sqrt ((N : ℝ) - 1) ^ 2 = (N : ℝ) - 1 := Real.sq_sqrt ha.le
  set s := Real.sqrt ((N : ℝ) - 1) with hs_def
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ((N : ℝ) - 1) * s := mul_pos ha hs
  have h2 := mul_lt_mul_of_pos_right hlt hpos
  have h3 : s * (((N : ℝ) - 1) * s) = ((N : ℝ) - 1) ^ 2 := by
    rw [show s * (((N : ℝ) - 1) * s) = ((N : ℝ) - 1) * s ^ 2 by ring, hsq]; ring
  nlinarith

/-- **Unheralded adaptive algorithms at trace distance `1/2`** (Corollary `hs:cor:unitary`,
trace-distance form of the endpoint `ε = 1/2`).
Every adaptive protocol over the released entry oracle of the search
family whose output is always accepted and within trace distance `1/2` of `U_m |0⟩` on every
instance `m` satisfies `(N - 2)² ≤ 16 (N - 1) √(N - 1) Q`, `Q` its worst-case number of entry
calls. -/
theorem unheralded_tree_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (entryOracles N γ η t ε) Fl E) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) (hsucc : ∀ m, T.successMass m = 1)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    ((N : ℝ) - 2) ^ 2 ≤
      16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) := by
  have h := implementation_count_ge_tree_endpoint hN γ η t ε 1
    (AdaptiveUnitaryLowerBound.Entry.one_isometry N γ η t ε)
    (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ η t ε) (fun _ => 1)
    (AdaptiveUnitaryLowerBound.Entry.entryOracles_implementsOn N γ η t ε) T e he
    (s₀ := 1) (ε₀ := 1 / 2) one_pos le_rfl (fun m => (hsucc m).ge) hacc
  nlinarith [h]

/-- **Heralded adaptive algorithms at trace distance `1/2`**: success probability at least
`2/3` on every instance and conditional output within trace distance `1/2` of `U_m |0⟩` give
`(N - 2)² ≤ 36 (N - 1) √(N - 1) Q`. -/
theorem heralded_tree_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (entryOracles N γ η t ε) Fl E) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) (hsucc : ∀ m, 2 / 3 ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    ((N : ℝ) - 2) ^ 2 ≤
      36 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) := by
  have h := implementation_count_ge_tree_endpoint hN γ η t ε 1
    (AdaptiveUnitaryLowerBound.Entry.one_isometry N γ η t ε)
    (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ η t ε) (fun _ => 1)
    (AdaptiveUnitaryLowerBound.Entry.entryOracles_implementsOn N γ η t ε) T e he
    (s₀ := 2 / 3) (ε₀ := 1 / 2) (by norm_num) le_rfl hsucc hacc
  nlinarith [h]

/-- **Unheralded adaptive algorithms with controlled and controlled-inverse calls at trace
distance `1/2`**: the bound of `unheralded_tree_half` over the four call forms of the released
entry oracle, each call counted once. -/
theorem unheralded_calls_tree_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (AdaptiveODELowerBound.Access.callFamily (entryOracles N γ η t ε)) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) (hsucc : ∀ m, T.successMass m = 1)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    ((N : ℝ) - 2) ^ 2 ≤
      16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) := by
  have h : (1 * ((N : ℝ) * (1 - 1 / 2) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) :=
    implementation_count_ge_calls_tree_endpoint hN γ η t ε 1
      (AdaptiveUnitaryLowerBound.Entry.one_isometry N γ η t ε)
      (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ η t ε) (fun _ => 1)
      (AdaptiveUnitaryLowerBound.Entry.entryOracles_implementsOn N γ η t ε) T e he
      (s₀ := 1) (ε₀ := 1 / 2) one_pos le_rfl (fun m => (hsucc m).ge) hacc
  nlinarith [h]

/-- **Heralded adaptive algorithms with controlled and controlled-inverse calls at trace
distance `1/2`**: the bound of `heralded_tree_half` over the four call forms of the released
entry oracle, each call counted once. -/
theorem heralded_calls_tree_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (T : Tree (AdaptiveODELowerBound.Access.callFamily (entryOracles N γ η t ε)) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) (hsucc : ∀ m, 2 / 3 ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    ((N : ℝ) - 2) ^ 2 ≤
      36 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) := by
  have h : (2 / 3 * ((N : ℝ) * (1 - 1 / 2) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun _ => 1) :=
    implementation_count_ge_calls_tree_endpoint hN γ η t ε 1
      (AdaptiveUnitaryLowerBound.Entry.one_isometry N γ η t ε)
      (AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary N γ η t ε) (fun _ => 1)
      (AdaptiveUnitaryLowerBound.Entry.entryOracles_implementsOn N γ η t ε) T e he
      (s₀ := 2 / 3) (ε₀ := 1 / 2) (by norm_num) le_rfl hsucc hacc
  nlinarith [h]

/-- **`Ω(√N)` at trace distance `1/2`, unheralded** (Corollary `hs:cor:unitary`, last
sentence, trace-distance form of the endpoint `ε = 1/2`):
under the hypotheses of `unheralded_tree_half` with
`N ≥ 3`, `√(N - 1) ≤ 64 Q`. -/
theorem unheralded_tree_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N) (γ η t ε : ℝ)
    (T : Tree (entryOracles N γ η t ε) Fl E) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) (hsucc : ∀ m, T.successMass m = 1)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    Real.sqrt ((N : ℝ) - 1) ≤ 64 * T.worstCost (fun _ => 1) := by
  have h := sqrt_le_of_half hN
    (unheralded_tree_half (by omega) γ η t ε T e he hsucc hacc)
  linarith

/-- **`Ω(√N)` at trace distance `1/2`, heralded**: under the hypotheses of
`heralded_tree_half` with `N ≥ 3`, `√(N - 1) ≤ 144 Q`. -/
theorem heralded_tree_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N) (γ η t ε : ℝ)
    (T : Tree (entryOracles N γ η t ε) Fl E) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) (hsucc : ∀ m, 2 / 3 ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    Real.sqrt ((N : ℝ) - 1) ≤ 144 * T.worstCost (fun _ => 1) := by
  have h := sqrt_le_of_half hN
    (heralded_tree_half (by omega) γ η t ε T e he hsucc hacc)
  linarith

/-- **`Ω(√N)` at trace distance `1/2`, unheralded, over the four call forms**: under the
hypotheses of `unheralded_calls_tree_half` with `N ≥ 3`, `√(N - 1) ≤ 64 Q`. -/
theorem unheralded_calls_tree_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N) (γ η t ε : ℝ)
    (T : Tree (AdaptiveODELowerBound.Access.callFamily (entryOracles N γ η t ε)) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) (hsucc : ∀ m, T.successMass m = 1)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    Real.sqrt ((N : ℝ) - 1) ≤ 64 * T.worstCost (fun _ => 1) := by
  have h := sqrt_le_of_half hN
    (unheralded_calls_tree_half (by omega) γ η t ε T e he hsucc hacc)
  linarith

/-- **`Ω(√N)` at trace distance `1/2`, heralded, over the four call forms**: under the
hypotheses of `heralded_calls_tree_half` with `N ≥ 3`, `√(N - 1) ≤ 144 Q`. -/
theorem heralded_calls_tree_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N) (γ η t ε : ℝ)
    (T : Tree (AdaptiveODELowerBound.Access.callFamily (entryOracles N γ η t ε)) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) (hsucc : ∀ m, 2 / 3 ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1))
        (1 / 2)) :
    Real.sqrt ((N : ℝ) - 1) ≤ 144 * T.worstCost (fun _ => 1) := by
  have h := sqrt_le_of_half hN
    (heralded_calls_tree_half (by omega) γ η t ε T e he hsucc hacc)
  linarith

end
end MeasuredUnitaryLowerBound.Adaptive
