import MeasuredUnitaryLowerBound.Endpoint.Measured
import DeferredMeasurementLowerBounds.Access.ControlTree

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# Measured algorithms over controlled and controlled-inverse entry calls

Corollary `hs:cor:unitary` of the manuscript (lines 1647-1666,
trace-distance form of the error range `0 < ε ≤ 1/2`,
inverse calls counted) for measured algorithms (`DeferredMeasurementLowerBounds.Model.Measured`,
closing sentence of the proof of `hsl:lem:precision`, lines 2363-2364: purification and
deferred measurement) whose oracle calls are the four call
forms of the oracle: plain, inverse, controlled and controlled-inverse
(`AdaptiveODELowerBound.Access.callFamily`; line 2080: "with inverses and coherent controls").

The deferral of such an algorithm is compiled into controlled calls of the spectator lift of the
call forms (`DeferredMeasurementLowerBounds.Access.ctrlTreeOf`, encoding
`AdaptiveODELowerBound.Access.activeEmbed`), an adaptive protocol with the success probability and
conditional output of the measured algorithm and at most `2 · 4 = 8` times its worst-case number
of calls (`DeferredMeasurementLowerBounds.Access.worstCost_ctrlTreeOf`, four counted labels). Every
label of that protocol is one query of a Boolean phase oracle of the marked strings on an
isometric encoding (`implementsOn_ctrlTarget`:
`AdaptiveODELowerBound.Access.implementsOn_callFamily` twice, around
`SparseLowerBounds.Adaptive.Access.implementsOn_spectate`), so
`Adaptive.tree_search_count_ge_endpoint` applies:

  `(p₀ (N (1 - ε₀) - 1))² ≤ 32 (N - 1) √(N - 1) Q`

for success probability at least `p₀ > 0` and conditional trace distance `ε₀ ≤ 1/2`, `Q` the
worst-case number of calls of the measured algorithm, each call form counted once.

* `fintypeCallForm` (a scoped instance), `card_callForm`: the four call forms.
* `implementsOn_ctrlTarget`: the labels of the compiled protocol as phase queries.
* `search_count_ge_measured_calls_endpoint`: the generic form, finite-dimensional oracle space.
* `implementation_count_ge_measured_calls_endpoint`: the released entry oracle, on the input
  `J|0⟩` of an isometric encoding into the controlled workspace.
* `implementation_count_ge_measured_calls_half`, `implementation_count_ge_measured_calls_sqrt`:
  implementations with success probability one and trace distance `1/2` on every unit input:
  `(N - 2)² ≤ 128 (N - 1) √(N - 1) Q`, and `√(N - 1) ≤ 512 Q` for `N ≥ 3`.
-/

namespace MeasuredUnitaryLowerBound.Calls

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open SparseLowerBounds.Readout
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open UnitaryImplementationExtensions.Search (markedString)
open DeferredMeasurementLowerBounds.Model
open AdaptiveODELowerBound.Access (CallForm callFamily callBoolean callEncoding)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace

/-- The four call forms form a finite type. The instance is scoped to the namespace
`MeasuredUnitaryLowerBound.Calls`, so it does not reach other importers. -/
scoped instance fintypeCallForm : Fintype CallForm :=
  ⟨{.plain, .inverse, .controlled, .controlledInverse}, fun f => by cases f <;> simp⟩

/-- There are four call forms. -/
theorem card_callForm : Fintype.card CallForm = 4 := by
  rfl

/-- **The labels of the compiled protocol are phase queries.** For a Boolean phase oracle
`x ↦ P.phase (y x)` and a spectator register `J`, every call form of the spectator lift of every
call form of the oracle (`DeferredMeasurementLowerBounds.Access.ctrlTarget`) is implemented by one
query of the Boolean phase oracle of `callBoolean ((callBoolean P).spectate J)` on the isometric
encoding `callEncoding (jointMap J (callEncoding 1))`. -/
theorem implementsOn_ctrlTarget {K I X : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [Fintype I] (P : ProjFamily K I) (y : X → I → Bool) (J : Type*)
    [Fintype J] (c' : (Unit × CallForm) × CallForm) :
    EncodedOracle.ImplementsOn
      (fun x => (callBoolean ((callBoolean P).spectate J)).phase (y x))
      (DeferredMeasurementLowerBounds.Access.ctrlTarget
        (callFamily (fun (_ : Unit) x => P.phase (y x))) J c')
      (callEncoding (SparseLowerBounds.Adaptive.Access.jointMap J
        (callEncoding (1 : K →L[ℂ] K)))) 1 := by
  rcases c' with ⟨⟨u, f⟩, f'⟩
  have hu₀ : ∀ (l : Unit) (x : X),
      IsUnitary ((fun (_ : Unit) x => P.phase (y x)) l x) := fun _ x => P.isUnitary_phase (y x)
  have hq : ∀ l : Unit, EncodedOracle.ImplementsOn (fun x => P.phase (y x))
      ((fun (_ : Unit) x => P.phase (y x)) l) 1 ((fun _ => 1) l) :=
    fun _ => ⟨.query, fun _ => by ext; rfl, le_rfl⟩
  have hQ : (fun x => ((callBoolean P).spectate J).phase (y x)) =
      fun x => Joint.fiber (fun _ : J => (callBoolean P).phase (y x)) :=
    funext fun x => Hamiltonian.HsRelease.phase_spectate J (callBoolean P) (y x)
  have h2 : ∀ l : Unit × CallForm, EncodedOracle.ImplementsOn
      (fun x => ((callBoolean P).spectate J).phase (y x))
      (fun x => Joint.fiber (fun _ : J => callFamily (fun (_ : Unit) x => P.phase (y x)) l x))
      (Adaptive.Access.jointMap J (callEncoding (1 : K →L[ℂ] K))) ((fun _ => 1) l) := by
    intro l
    rw [hQ]
    exact Adaptive.Access.implementsOn_spectate J
      (AdaptiveODELowerBound.Access.implementsOn_callFamily P y 1 _ hu₀ (fun _ => 1) hq l)
  exact AdaptiveODELowerBound.Access.implementsOn_callFamily ((callBoolean P).spectate J) y
    (Adaptive.Access.jointMap J (callEncoding (1 : K →L[ℂ] K)))
    (fun l x => Joint.fiber (fun _ : J => callFamily (fun (_ : Unit) x => P.phase (y x)) l x))
    (fun l x => PhaseCircuit.isUnitary_fiber _ fun _ =>
      AdaptiveODELowerBound.Access.callFamily_unitary hu₀ l x)
    (fun _ => 1) h2 ((u, f), f')

/-- **Search for measured algorithms over the call forms, up to trace distance `1/2`.** A
measured algorithm over the four call forms of the phase oracle of the marked strings of `c`, on
a finite-dimensional oracle space, that on every instance `m` succeeds with probability at least
`p₀ > 0` and whose conditional output, read through the isometry `e`, is within trace distance
`ε₀ ≤ 1/2` of `|m⟩`, satisfies `(p₀ (N (1 - ε₀) - 1))² ≤ 32 (N - 1) √(N - 1) Q`, `Q` its
worst-case number of calls, each call form counted once. -/
theorem search_count_ge_measured_calls_endpoint {N : ℕ} (hN : 2 ≤ N) {K I : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [FiniteDimensional ℂ K]
    [Fintype I] (P : ProjFamily K I) (c : I → Fin N) {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : Unit → Fin N → K →L[ℂ] K} (hO : ∀ m, O () m = P.phase (markedString c m))
    (M : Measured (callFamily O) E) {φ : Joint Bool K} (hφ : ‖φ‖ = 1)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {p₀ ε₀ : ℝ} (hp₀ : 0 < p₀)
    (hε₀ : ε₀ ≤ 1 / 2)
    (hher : ∀ m, p₀ ≤ M.successMass m φ ∧
      DensityAccurate e (M.conditionalDensity m φ) (EuclideanSpace.single m (1 : ℂ)) ε₀) :
    (p₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  classical
  have hOeq : O = fun _ m => P.phase (markedString c m) :=
    funext fun u => funext fun m => by cases u; exact hO m
  subst hOeq
  have hu₀ : ∀ (l : Unit) (m : Fin N),
      IsUnitary ((fun (_ : Unit) m => P.phase (markedString c m)) l m) :=
    fun _ m => P.isUnitary_phase _
  have hB := AdaptiveODELowerBound.Access.callFamily_unitary hu₀
  have hO'' : ∀ l m, IsUnitary (DeferredMeasurementLowerBounds.Access.ctrlTarget
      (callFamily fun (_ : Unit) m => P.phase (markedString c m))
      (DeferredMeasurementLowerBounds.Deferral.DRec M) l m) :=
    AdaptiveODELowerBound.Access.callFamily_unitary fun l m =>
      PhaseCircuit.isUnitary_fiber _ fun _ => hB l m
  have hone : (1 : K →L[ℂ] K)† ∘L (1 : K →L[ℂ] K) = 1 := by
    rw [ContinuousLinearMap.adjoint_one]; ext; rfl
  have hEnc := AdaptiveODELowerBound.Access.callEncoding_isometry _
    (Adaptive.Access.jointMap_isometry (DeferredMeasurementLowerBounds.Deferral.DRec M) _
      (AdaptiveODELowerBound.Access.callEncoding_isometry _ hone))
  have hcirc := DeferredMeasurementLowerBounds.Access.ctrlCircuits_eval
    (B := callFamily fun (_ : Unit) m => P.phase (markedString c m)) (fun _ => none)
    (fun _ => True) (DeferredMeasurementLowerBounds.Deferral.DRec M)
  have key := MeasuredUnitaryLowerBound.Adaptive.tree_search_count_ge_endpoint hN
    (callBoolean ((callBoolean P).spectate (DeferredMeasurementLowerBounds.Deferral.DRec M)))
    c _ hEnc hO'' (fun _ => 1)
    (fun l => implementsOn_ctrlTarget P (markedString c)
      (DeferredMeasurementLowerBounds.Deferral.DRec M) l)
    (DeferredMeasurementLowerBounds.Access.ctrlTreeOf ℂ
      (callFamily fun (_ : Unit) m => P.phase (markedString c m)) (fun _ => none)
      (fun _ => True) M φ hφ)
    (DeferredMeasurementLowerBounds.Readout.liftReadout
      (DeferredMeasurementLowerBounds.Deferral.DOut M) e)
    (DeferredMeasurementLowerBounds.Readout.liftReadout_isometry he) hp₀ hε₀
    (fun m => by
      rw [DeferredMeasurementLowerBounds.Access.successMass_compiledTree hB hO'' M hφ _ _ _
        hcirc m]
      exact (hher m).1)
    (fun m => by
      rw [DeferredMeasurementLowerBounds.Access.conditionalDensity_compiledTree hB hO'' M hφ _ _ _
        hcirc m]
      apply DeferredMeasurementLowerBounds.Readout.densityAccurate_liftReadout
      rw [DeferredMeasurementLowerBounds.Deferral.sum_pure_amplitude]
      exact (hher m).2)
  have hcost : (DeferredMeasurementLowerBounds.Access.ctrlTreeOf ℂ
      (callFamily fun (_ : Unit) m => P.phase (markedString c m)) (fun _ => none)
      (fun _ => True) M φ hφ).worstCost (fun _ => 1) ≤ 8 * M.worstCost (fun _ => 1) := by
    have hc := DeferredMeasurementLowerBounds.Access.worstCost_ctrlTreeOf (Fl := ℂ)
      (callFamily fun (_ : Unit) m => P.phase (markedString c m)) (fun _ => none)
      (fun _ => True) M hφ
    have hcard : Fintype.card {l : Unit × CallForm // True} = 4 := by
      rw [Fintype.card_subtype, Finset.filter_true, Finset.card_univ, Fintype.card_prod,
        Fintype.card_unit, card_callForm]
    have hcw : countWeight (fun _ : Unit × CallForm => True) = fun _ => 1 :=
      funext fun _ => if_pos trivial
    rw [hcw, hcard] at hc
    exact hc
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hA : 0 ≤ 4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hN1)) (Real.sqrt_nonneg _)
  have hcost' : ((DeferredMeasurementLowerBounds.Access.ctrlTreeOf ℂ
      (callFamily fun (_ : Unit) m => P.phase (markedString c m)) (fun _ => none)
      (fun _ => True) M φ hφ).worstCost (fun _ => 1) : ℝ) ≤
      8 * (M.worstCost (fun _ => 1) : ℝ) := by exact_mod_cast hcost
  calc _ ≤ _ := key
    _ ≤ 4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * (8 * (M.worstCost (fun _ => 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcost' hA
    _ = _ := by ring

/-- **The lower half of `hs:cor:unitary` for measured algorithms with controlled and
controlled-inverse entry calls, up to trace distance `1/2`**: a measured algorithm over the four
call forms of the released entry oracle of the search family that, on the input `J|0⟩` of an
isometric encoding `J` into the controlled workspace and every instance `m`, succeeds with
probability at least `p₀ > 0` and has conditional output within trace distance `ε₀ ≤ 1/2` of
`U_m |0⟩`, satisfies `(p₀ (N (1 - ε₀) - 1))² ≤ 32 (N - 1) √(N - 1) Q`, `Q` its worst-case
number of entry calls, each call form counted once. -/
theorem implementation_count_ge_measured_calls_endpoint {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ) {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (callFamily (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε)) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {p₀ ε₀ : ℝ}
    (hp₀ : 0 < p₀) (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, p₀ ≤ M.successMass m (J (EuclideanSpace.single 0 1)) ∧
      DensityAccurate e (M.conditionalDensity m (J (EuclideanSpace.single 0 1)))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (p₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      32 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  have hJ0 : ‖J (EuclideanSpace.single 0 (1 : ℂ))‖ = 1 := by
    rw [(J.norm_map_iff_adjoint_comp_self.mpr hJ), PiLp.norm_single, norm_one]
  refine search_count_ge_measured_calls_endpoint hN (LiftPhase.entryFamily (n := Fin N) γ η t ε)
    (AdaptiveUnitaryLowerBound.Oracles.entryPosition N)
    (fun m => AdaptiveUnitaryLowerBound.Oracles.entry_oracle_eq_phase_marked N γ η t ε m) M hJ0
    e he hp₀ hε₀ (fun m => ?_)
  have h := himpl m
  rwa [searchMatrix_single_zero N m] at h

/-- **Measured implementations over the call forms at trace distance `1/2`**: a measured
algorithm over the four call forms of the released entry oracle that implements every `U_m` on
an isometric encoding `J` into the controlled workspace (success probability one and output
within trace distance `1/2` of `U_m ψ` for every unit input `ψ`) satisfies
`(N - 2)² ≤ 128 (N - 1) √(N - 1) Q`. -/
theorem implementation_count_ge_measured_calls_half {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ) {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (callFamily (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε)) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate e (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2)) :
    ((N : ℝ) - 2) ^ 2 ≤
      128 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  have h1 : ‖(EuclideanSpace.single 0 (1 : ℂ) : EuclideanSpace ℂ (Fin N))‖ = 1 := by
    rw [PiLp.norm_single, norm_one]
  have h := implementation_count_ge_measured_calls_endpoint hN γ η t ε M J hJ e he
    (p₀ := 1) (ε₀ := 1 / 2) one_pos le_rfl
    (fun m => ⟨(himpl m _ h1).1.ge, (himpl m _ h1).2⟩)
  linear_combination 4 * h

/-- **`Ω(√N)` for measured implementations over the call forms at trace distance `1/2`**: under
the hypotheses of `implementation_count_ge_measured_calls_half` with `N ≥ 3`,
`√(N - 1) ≤ 512 Q`. -/
theorem implementation_count_ge_measured_calls_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N)
    (γ η t ε : ℝ) {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (callFamily (AdaptiveUnitaryLowerBound.Entry.entryOracles N γ η t ε)) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ]
      Joint Bool (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate e (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2)) :
    Real.sqrt ((N : ℝ) - 1) ≤ 512 * M.worstCost (fun _ => 1) := by
  have h := MeasuredUnitaryLowerBound.Adaptive.sqrt_le_of_half hN
    (implementation_count_ge_measured_calls_half (by omega) γ η t ε M J hJ e he himpl)
  linarith

end
end MeasuredUnitaryLowerBound.Calls
