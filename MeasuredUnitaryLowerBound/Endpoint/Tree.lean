import MeasuredUnitaryLowerBound.Reading
import AdaptiveUnitaryLowerBound.Lookup

set_option autoImplicit false

/-!
# The trace-distance endpoint `ε = 1/2` for adaptive algorithms

Corollary `hs:cor:unitary` of the manuscript (lines 1647-1666) allows any error
`0 < ε ≤ 1/2` and ends: "At fixed constant error, the worst-case query complexity is
`Θ(√N)`" (lines 1664-1665), with the lower half from the reduction to unstructured search
(lines 1711-1718) and inverse calls counted (line 1662). Adaptive algorithms and coherent
controls follow the lower-bound setting of the manuscript (line 2080: "with inverses and
coherent controls"; the closing sentence of the proof of `hsl:lem:precision`, lines 2363-2364:
"Randomised or adaptive algorithms are covered by
purification and deferred measurement").

The manuscript measures the error in operator norm (`hs:eq:unitaryerror`, lines 1652-1654);
accuracy here is trace distance (`AdaptiveHamiltonianLowerBound.DensityAccurate`), the
package's notion for adaptive, heralded and measured algorithms. For a unitary program,
operator-norm error `ε` gives trace distance at most `ε`
(`SparseLowerBounds.Hamiltonian.accurate_of_endpoint`), so the bounds here contain the
operator-norm endpoint, which
`AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error` covers for unitary
programs; the new content is the trace-distance endpoint for adaptive, heralded and measured
algorithms.

`AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_tree` gives
`(s₀ (1 - 2ε₀))² √(N - 1) ≤ 4 Q`, which is empty at trace-distance error `ε₀ = 1/2`. The bounds
here use the summed pair gaps of `Global.tree_count_ge_of_reads` with the read values of
`Reading.tree_read_bound`, and hold on the whole range `ε₀ ≤ 1/2`:

  `(s₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) Q`,

so `(s₀ (N - 2))² ≤ 16 (N - 1) √(N - 1) Q` at `ε₀ = 1/2`, an `Ω(√N)` bound for `N ≥ 3`. For
`N = 2` it is empty, as it must be: a protocol without queries whose output is maximally mixed
is within trace distance `1/2` of both targets.

**Algorithms and accuracy** are those of `AdaptiveUnitaryLowerBound`: adaptive protocols
`SparseLinearSystems.Protocol.Tree` over labels implemented by `w l` oracle calls on an
isometric encoding (inverse calls included), on finite-dimensional workspace and output spaces;
success probability at least `s₀ > 0` on every instance and conditional output, read through an
isometry `e`, within trace distance `ε₀` of `U_m |0⟩`
(`AdaptiveHamiltonianLowerBound.DensityAccurate`). The call forms
(`AdaptiveODELowerBound.Access.callFamily`) add the inverse, controlled and controlled-inverse
form of every label at the weight of the label.

* `tree_search_count_ge_endpoint`: the generic form for Boolean phase oracles of marked strings.
* `implementation_count_ge_tree_endpoint`, `implementation_count_ge_calls_tree_endpoint`: the
  released entry oracle `UnitaryEntryOracle.oracle (searchData N) γ η t ε`.
* `entry_count_ge_tree_endpoint`, `entry_count_ge_calls_tree_endpoint`: the ordinary entry
  lookup with any payload.
* `implementation_count_ge_program_endpoint`: one program on a unit seed with accurate output
  (`SparseLowerBounds.Readout.Accurate`), `s₀ = 1`.
-/

namespace MeasuredUnitaryLowerBound.Adaptive

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open scoped InnerProduct InnerProductSpace
set_option synthInstance.maxSize 8192

variable {E W Fl L B I G V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Unstructured search for adaptive protocols up to trace distance `1/2`.** If every label
of a unitary family over the instances `Fin N`, `N ≥ 2`, on a finite-dimensional workspace is
implemented on the isometric encoding `Enc` by at most `w l` queries of the phase oracle of the
marked strings of `c`, and on every instance `m` the protocol succeeds with probability at
least `s₀ > 0` and its conditional output, read through the isometry `e`, is within trace
distance `ε₀ ≤ 1/2` of `|m⟩`, then `(s₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) worstCost_w(T)`. -/
theorem tree_search_count_ge_endpoint [Fintype I] [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ E] {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I)
    (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m) (EuclideanSpace.single m 1) ε₀) :
    (s₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost w := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : 0 ≤ s₀ * ((N : ℝ) * (1 - ε₀) - 1) := by
    apply mul_nonneg hs₀.le
    nlinarith [mul_nonneg (sub_nonneg.2 hN') (by linarith : (0 : ℝ) ≤ 1 / 2 - ε₀)]
  exact Global.tree_count_ge_of_reads hN P c Enc hEnc hO w hw T
    (fun y => outObs e (ODEMixedOutput.pureOperator (EuclideanSpace.single y (1 : ℂ))))
    (fun x x' _ => Reading.norm_outObs_pure_sub_le e he x x') hb
    (fun x => Reading.tree_read_bound hN hO T e he hs₀ hε₀ x (hsucc x) (hacc x))

/-- **Lower half of `Θ(√N)` up to trace distance `1/2`, released entry oracle** (Corollary
`hs:cor:unitary`, last sentence, trace-distance form of its error range `0 < ε ≤ 1/2`).
Every adaptive protocol over
labels implemented by at most `w l` calls of the released entry oracle of the search family on
an isometric encoding, on a finite-dimensional workspace, that on every instance `m` succeeds
with probability at least `s₀ > 0` and outputs, conditionally on success, a state within trace
distance `ε₀ ≤ 1/2` of `U_m |0⟩`, satisfies
`(s₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) worstCost_w(T)`. -/
theorem implementation_count_ge_tree_endpoint [FiniteDimensional ℂ W] [FiniteDimensional ℂ E]
    {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost w := by
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (EuclideanSpace.single m 1) ε₀ :=
    fun m => by simpa only [searchMatrix_single_zero] using hacc m
  exact tree_search_count_ge_endpoint hN (LiftPhase.entryFamily (n := Fin N) γ η t ε)
    (AdaptiveUnitaryLowerBound.Oracles.entryPosition N) Enc hEnc hO w
    (fun l => AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_entry N γ η t ε (hw l))
    T e he hs₀ hε₀ hsucc hacc'

/-- **The endpoint bound with controlled and controlled-inverse calls, released entry
oracle**: the bound of `implementation_count_ge_tree_endpoint` for adaptive protocols over the
call family of `O`, every label in its plain, inverse, controlled and controlled-inverse forms,
each counted with the weight of the label. -/
theorem implementation_count_ge_calls_tree_endpoint [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ E] {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (T : Tree (AdaptiveODELowerBound.Access.callFamily O) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun c => w c.1) := by
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (EuclideanSpace.single m 1) ε₀ :=
    fun m => by simpa only [searchMatrix_single_zero] using hacc m
  have hw' := fun l =>
    AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_entry N γ η t ε (hw l)
  exact tree_search_count_ge_endpoint hN
    (AdaptiveODELowerBound.Access.callBoolean (LiftPhase.entryFamily (n := Fin N) γ η t ε))
    (AdaptiveUnitaryLowerBound.Oracles.entryPosition N)
    (AdaptiveODELowerBound.Access.callEncoding Enc)
    (AdaptiveODELowerBound.Access.callEncoding_isometry Enc hEnc)
    (AdaptiveODELowerBound.Access.callFamily_unitary hO) (fun c => w c.1)
    (fun c => AdaptiveODELowerBound.Access.implementsOn_callFamily
      (LiftPhase.entryFamily (n := Fin N) γ η t ε)
      (Search.markedString (AdaptiveUnitaryLowerBound.Oracles.entryPosition N)) Enc O hO w hw' c)
    T e he hs₀ hε₀ hsucc hacc'

/-- **The endpoint bound, ordinary entry lookup** (any payload `V`): the bound of
`implementation_count_ge_tree_endpoint` for labels implemented by calls of the reversible entry
lookup of the search family. -/
theorem entry_count_ge_tree_endpoint [FiniteDimensional ℂ W] [FiniteDimensional ℂ E] {N : ℕ}
    [NeZero N] (hN : 2 ≤ N)
    (Enc : W →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => V)) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost w := by
  have hw' : ∀ l, EncodedOracle.ImplementsOn
      (fun m => (PhaseBridge.xorFamily (Fin N × Fin N) V).phase
        (Search.markedString (AdaptiveUnitaryLowerBound.Oracles.lookupPosition N) m))
      (O l) Enc (w l) := fun l =>
    AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_lookup V N (hw l)
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (EuclideanSpace.single m 1) ε₀ :=
    fun m => by simpa only [searchMatrix_single_zero] using hacc m
  exact tree_search_count_ge_endpoint hN (PhaseBridge.xorFamily (Fin N × Fin N) V)
    (AdaptiveUnitaryLowerBound.Oracles.lookupPosition N) Enc hEnc hO w hw' T e he hs₀ hε₀
    hsucc hacc'

/-- **The endpoint bound over the call forms of the ordinary entry lookup** (any payload `V`). -/
theorem entry_count_ge_calls_tree_endpoint [FiniteDimensional ℂ W] [FiniteDimensional ℂ E]
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (Enc : W →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => V)) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (fun m => LookupControlledGate.oracle (K := V) (searchTable N) m) (O l) Enc (w l))
    (T : Tree (AdaptiveODELowerBound.Access.callFamily O) Fl E)
    (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hsucc : ∀ m, s₀ ≤ T.successMass m)
    (hacc : ∀ m, DensityAccurate e (T.conditionalDensity m)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (s₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost (fun c => w c.1) := by
  have hw' : ∀ l, EncodedOracle.ImplementsOn
      (fun m => (PhaseBridge.xorFamily (Fin N × Fin N) V).phase
        (Search.markedString (AdaptiveUnitaryLowerBound.Oracles.lookupPosition N) m))
      (O l) Enc (w l) := fun l =>
    AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_lookup V N (hw l)
  have hacc' : ∀ m, DensityAccurate e (T.conditionalDensity m) (EuclideanSpace.single m 1) ε₀ :=
    fun m => by simpa only [searchMatrix_single_zero] using hacc m
  exact tree_search_count_ge_endpoint hN
    (AdaptiveODELowerBound.Access.callBoolean (PhaseBridge.xorFamily (Fin N × Fin N) V))
    (AdaptiveUnitaryLowerBound.Oracles.lookupPosition N)
    (AdaptiveODELowerBound.Access.callEncoding Enc)
    (AdaptiveODELowerBound.Access.callEncoding_isometry Enc hEnc)
    (AdaptiveODELowerBound.Access.callFamily_unitary hO) (fun c => w c.1)
    (fun c => AdaptiveODELowerBound.Access.implementsOn_callFamily
      (PhaseBridge.xorFamily (Fin N × Fin N) V)
      (Search.markedString (AdaptiveUnitaryLowerBound.Oracles.lookupPosition N)) Enc O hO w hw' c)
    T e he hs₀ hε₀ hsucc hacc'

/-- **The program form up to trace distance `1/2`.** A single program over `O` (labels as in
`implementation_count_ge_tree_endpoint`) run on a unit seed `φ₀`, whose output on every instance
`m`, read through the isometry `e`, is `ε₀`-accurate for `U_m |0⟩` (`ε₀ ≤ 1/2`), satisfies
`(N (1 - ε₀) - 1)² ≤ 4 (N - 1) √(N - 1) cost_w(p)`. -/
theorem implementation_count_ge_program_endpoint [FiniteDimensional ℂ W] {N : ℕ} [NeZero N]
    (hN : 2 ≤ N) (γ η t ε : ℝ)
    (Enc : W →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn
      (UnitaryEntryOracle.oracle (searchData N) γ η t ε) (O l) Enc (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : W) (hφ₀ : ‖φ₀‖ = 1)
    (e : W →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ} (hε₀ : ε₀ ≤ 1 / 2)
    (hacc : ∀ m, Accurate e (p.eval m φ₀)
      (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    ((N : ℝ) * (1 - ε₀) - 1) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * p.cost w := by
  have hU := fun m => MultiOracleCircuit.Program.eval_unitary p hO m
  have h := implementation_count_ge_tree_endpoint (E := W) (Fl := ℂ) hN γ η t ε Enc hEnc hO w
    hw (AdaptiveHamiltonianLowerBound.Single.tree ℂ p φ₀ hφ₀) e he (s₀ := 1) one_pos hε₀
    (fun m => (AdaptiveHamiltonianLowerBound.Single.successMass_tree p φ₀ hφ₀ m (hU m)).ge)
    (fun m => by
      rw [AdaptiveHamiltonianLowerBound.Single.conditionalDensity_tree p φ₀ hφ₀ m (hU m),
        AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
      exact hacc m)
  rw [AdaptiveHamiltonianLowerBound.Single.worstCost_tree, one_mul] at h
  exact h

end
end MeasuredUnitaryLowerBound.Adaptive
