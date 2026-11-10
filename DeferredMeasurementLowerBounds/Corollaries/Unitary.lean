import DeferredMeasurementLowerBounds.Access.Phase
import DeferredMeasurementLowerBounds.Corollaries.UnitaryReadout
import UnitaryImplementationExtensions.LowerBound

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# The unitary lower half of `hs:cor:unitary` for measured algorithms

Manuscript Corollary `hs:cor:unitary` (`0 < ε ≤ 1/2`, "the constant-error worst-case complexity is
`Θ(√N)`") and the end of the proof of Lemma `hsl:lem:precision` (purification and deferred
measurement). The lower half for unitary circuits is `UnitaryImplementationExtensions.LowerBound`;
here it is extended to **measured algorithms** (`Model.Measured`) that implement the search
unitaries `U_m` (`UnitaryImplementationExtensions.SearchFamily.searchMatrix`).

* `search_count_ge_measured_sharp`: for a Boolean phase oracle `P.phase (markedString c m)` of
  any projection family, a measured algorithm whose output, read through an isometry onto
  `ℂ^N ⊗ G`, shows `m` jointly with the success herald with probability at least `1 - δ`,
  `δ ≤ 1/2`, on every instance `m`, makes at least `(1 - 2 √(δ (1 - δ))) √(N - 1) / 2` calls in
  the worst case over all transcripts. The deferred program is a single-family program over the
  controlled spectated phase oracle; its final states on two instances, split into the decoded
  output read through the lifted readout and the part outside the output, have overlap at most
  `2 √(δ (1 - δ))`, and `UnitaryImplementationExtensions.Search.count_ge` applies.
  `search_count_ge_measured` is the same with the constant `1 - 2 √δ` of
  `UnitaryImplementationExtensions.Search.search_count_ge`, for every `δ ≥ 0`.
* `search_count_ge_measured_heralded`: the same with heralded success: if on every instance the
  success probability is at least `p₀` and the conditional output is within trace distance
  `ε₀ ≤ 1` of `|m⟩`, with `p₀ (1 - ε₀) ≥ 1/2`, the bound holds with `δ = 1 - p₀ (1 - ε₀)`
  (the heralded read probability is the success probability times the conditional one,
  `readProb_successDensity`).
* `entry_count_ge_measured` (ordinary entry lookup with any payload, the class of
  `UnitaryImplementationExtensions.LowerBound.entry_count_ge`) and
  `implementation_count_ge_measured` (the released entry oracle of the upper bound): a measured
  algorithm that implements every `U_m` on an isometric input encoding, in the sense that for
  every unit input `ψ` it succeeds with probability one and outputs a state within trace
  distance `ε₀ ≤ 1/2` of `U_m ψ` (`DensityAccurate`), makes at least
  `(1 - 2 √(ε₀ (1 - ε₀))) √(N - 1) / 2` entry calls, inverse calls included. The factor is
  positive for every fixed `ε₀ < 1/2`; only the input `|0⟩` is used.
* `entry_count_ge_measured_heralded`, `implementation_count_ge_measured_heralded`: the general
  forms on the single input `J|0⟩`, with success probability at least `p₀` and conditional
  trace distance `ε₀` from `U_m |0⟩ = |m⟩`, `p₀ (1 - ε₀) ≥ 1/2`; the two statements above are
  the case `p₀ = 1`.

A measured algorithm has no operator to compare with `U_m`, so accuracy is per-input trace
distance of the conditional output. The operator-norm statements for unitary programs remain
`UnitaryImplementationExtensions.LowerBound.entry_count_ge` and `implementation_count_ge`, with
their sharper factor `1 - 2 ε₀ √(1 - ε₀²/4)`. For unitary programs, operator-norm error `ε`
gives per-input trace distance `ε` through `SparseLowerBounds.Hamiltonian.accurate_of_endpoint`
and `AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff` (constant `ε`, not the sharp
`ε √(1 - ε²/4)`); a named operator-norm form of the measured bound is not stated here.
-/

namespace DeferredMeasurementLowerBounds.Corollaries

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open SparseLowerBounds.Readout
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open UnitaryImplementationExtensions.Search (markedString)
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open DeferredMeasurementLowerBounds.Access DeferredMeasurementLowerBounds.Readout
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace
open AdaptiveODELowerBound.Access (ctrlFamily activeEmbed activeEmbed_isometry)
open DeferredMeasurementLowerBounds.SearchReadout

/-- **Search lower bound for measured algorithms, sharp form** (the search reduction of Corollary
`hs:cor:unitary`). A measured algorithm over the phase oracle of the marked strings that reads `m`
jointly with the success herald with probability at least `1 - δ`, `δ ≤ 1/2`, on every instance
makes at least `(1 - 2 √(δ (1 - δ))) √(N - 1) / 2` calls in the worst case. -/
theorem search_count_ge_measured_sharp {N : ℕ} (hN : 2 ≤ N) {K I : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I]
    (P : ProjFamily K I) (c : I → Fin N) {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : Unit → Fin N → K →L[ℂ] K} (hO : ∀ m, O () m = P.phase (markedString c m))
    (M : Measured O E) {φ : K}
    (hφ : ‖φ‖ = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδ1 : δ ≤ 1 / 2) (hread : ∀ m, 1 - δ ≤ readProb e m (M.successDensity m φ)) :
    (1 - 2 * Real.sqrt (δ * (1 - δ))) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * M.worstCost (fun _ => 1) := by
  obtain rfl : O = fun _ m => P.phase (markedString c m) :=
    funext fun u => funext fun m => by cases u; exact hO m
  have hEnc := activeEmbed_isometry (B := Joint (DRec M) K)
  let p := compiledProgram (fun _ : Unit => True) M (activeEmbed (Joint (DRec M) K)) hEnc
    (phaseCircuits P (fun m => markedString c m))
  let q : OracleCircuit.Program
      (fun m : Fin N => (ctrlFamily (P.spectate (DRec M))).phase (markedString c m)) :=
    p.compile (fun _ => OracleCircuit.Program.query)
  have hq : ∀ m, q.eval m = p.eval m := fun m =>
    MultiOracleCircuit.Program.eval_compile p _ (fun _ _ => rfl) m
  have hφ₀ : ‖activeEmbed (Joint (DRec M) K) (deferredSeed M φ)‖ = 1 := by
    rw [((activeEmbed (Joint (DRec M) K)).norm_map_iff_adjoint_comp_self.mpr hEnc) _,
      norm_deferredSeed M hφ]
  have hunit : ∀ m, ‖q.eval m (activeEmbed (Joint (DRec M) K) (deferredSeed M φ))‖ = 1 :=
    fun m => by
      rw [PositiveAdversary.norm_map_of_isUnitary
        (q.eval_unitary (fun x => (ctrlFamily (P.spectate (DRec M))).isUnitary_phase _) m), hφ₀]
  have hD : (activeEmbed (Joint (DRec M) K) ∘L deferredOutput M)† ∘L
      (activeEmbed (Joint (DRec M) K) ∘L deferredOutput M) = 1 := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc ((activeEmbed (Joint (DRec M) K))†)
      (activeEmbed (Joint (DRec M) K)) (deferredOutput M), hEnc,
      show (1 : Joint (DRec M) K →L[ℂ] Joint (DRec M) K) ∘L deferredOutput M = deferredOutput M
        from ContinuousLinearMap.id_comp _, deferredOutput_isometry]
  have hamp : ∀ m, ((activeEmbed (Joint (DRec M) K) ∘L deferredOutput M)†)
      (q.eval m (activeEmbed (Joint (DRec M) K) (deferredSeed M φ))) =
        amplitude (fun _ : Unit => True) M m φ := fun m => by
    rw [hq]
    exact amplitude_compiled (fun _ _ => P.isUnitary_phase _)
      (fun _ _ => (ctrlFamily (P.spectate (DRec M))).isUnitary_phase _) M φ _ hEnc _
      (phaseCircuits_eval P _) m
  have hreads : ∀ m, 1 - δ ≤ ‖sel m (liftReadout (DOut M) e
      (((activeEmbed (Joint (DRec M) K) ∘L deferredOutput M)†)
        (q.eval m (activeEmbed (Joint (DRec M) K) (deferredSeed M φ)))))‖ ^ 2 := fun m => by
    rw [hamp, norm_sq_sel_liftReadout, sum_pure_amplitude]
    exact hread m
  have hκ : 0 ≤ 1 - 2 * Real.sqrt (δ * (1 - δ)) := by
    have h0 : 0 ≤ δ * (1 - δ) := mul_nonneg hδ (by linarith)
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (δ * (1 - δ)), sq_nonneg (δ - 1 / 2)]
  have hsep : ∀ m m', m ≠ m' →
      ‖⟪q.eval m (activeEmbed (Joint (DRec M) K) (deferredSeed M φ)),
        q.eval m' (activeEmbed (Joint (DRec M) K) (deferredSeed M φ))⟫_ℂ‖ ≤
        ‖activeEmbed (Joint (DRec M) K) (deferredSeed M φ)‖ ^ 2 -
          (1 - 2 * Real.sqrt (δ * (1 - δ))) := by
    intro m m' hmm
    rw [hφ₀, one_pow, sub_sub_cancel]
    exact norm_inner_le_of_reads hD (liftReadout_isometry he) (sel_isStarProjection m)
      (norm_sq_sel_add_le hmm) (hunit m) (hunit m') hδ hδ1 (hreads m) (hreads m')
  have hcount : q.count ≤ M.worstCost (fun _ => 1) := by
    show (p.compile _).count ≤ _
    rw [MultiOracleCircuit.Program.count_compile]
    simp only [OracleCircuit.Program.count_query]
    rw [MultiOracleCircuit.Program.cost_const, mul_one]
    show (EncodedLabeledProgram.compile _ hEnc _
      (deferredProgram (fun _ : Unit => True) M)).count ≤ _
    rw [EncodedLabeledProgram.compile_count]
    calc _ ≤ (deferredProgram (fun _ : Unit => True) M).cost selWeight :=
          MultiOracleCircuit.Program.cost_mono _ (phaseCircuits_count P _)
      _ ≤ M.worstCost (countWeight fun _ : Unit => True) := cost_deferredProgram M
      _ = M.worstCost (fun _ => 1) := by
          rw [show countWeight (fun _ : Unit => True) = fun _ => 1 from
            funext fun _ => if_pos trivial]
  have key := Search.count_ge hN (ctrlFamily (P.spectate (DRec M))) c
    (O := fun m => (ctrlFamily (P.spectate (DRec M))).phase (markedString c m))
    (fun m => rfl) q _ hφ₀.le hκ hsep
  calc _ ≤ 2 * (q.count : ℝ) := key
    _ ≤ 2 * (M.worstCost (fun _ => 1) : ℝ) := by
        gcongr

/-- **Search lower bound for measured algorithms**, with the constant of
`UnitaryImplementationExtensions.Search.search_count_ge`: a measured algorithm over the phase
oracle of the marked strings that reads `m` jointly with the success herald with probability at
least `1 - δ` on every instance makes at least `(1 - 2 √δ) √(N - 1) / 2` calls in the worst
case. -/
theorem search_count_ge_measured {N : ℕ} (hN : 2 ≤ N) {K I : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I] (P : ProjFamily K I) (c : I → Fin N)
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : Unit → Fin N → K →L[ℂ] K} (hO : ∀ m, O () m = P.phase (markedString c m))
    (M : Measured O E) {φ : K}
    (hφ : ‖φ‖ = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hread : ∀ m, 1 - δ ≤ readProb e m (M.successDensity m φ)) :
    (1 - 2 * Real.sqrt δ) * Real.sqrt ((N : ℝ) - 1) ≤ 2 * M.worstCost (fun _ => 1) := by
  by_cases hδ1 : δ ≤ 1 / 2
  · refine le_trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      (search_count_ge_measured_sharp hN P c hO M hφ e he hδ hδ1 hread)
    have : Real.sqrt (δ * (1 - δ)) ≤ Real.sqrt δ := Real.sqrt_le_sqrt (by nlinarith)
    linarith
  · push Not at hδ1
    have hs : 1 - 2 * Real.sqrt δ < 0 := by
      nlinarith [Real.sq_sqrt hδ, Real.sqrt_nonneg δ]
    exact (mul_nonpos_of_nonpos_of_nonneg hs.le (Real.sqrt_nonneg _)).trans (by positivity)

/-- **Search lower bound for measured algorithms, heralded form.** A measured algorithm over the
phase oracle of the marked strings that, on every instance `m`, succeeds with probability at
least `p₀` and whose conditional output is within trace distance `ε₀ ≤ 1` of `|m⟩`, with
`p₀ (1 - ε₀) ≥ 1/2`, makes at least `(1 - 2 √(δ (1 - δ))) √(N - 1) / 2` calls in the worst case,
`δ = 1 - p₀ (1 - ε₀)`. -/
theorem search_count_ge_measured_heralded {N : ℕ} (hN : 2 ≤ N) {K I : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I]
    (P : ProjFamily K I) (c : I → Fin N) {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : Unit → Fin N → K →L[ℂ] K} (hO : ∀ m, O () m = P.phase (markedString c m))
    (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) {p₀ ε₀ : ℝ} (hε₀1 : ε₀ ≤ 1) (hp : 1 / 2 ≤ p₀ * (1 - ε₀))
    (hher : ∀ m, p₀ ≤ M.successMass m φ ∧
      DensityAccurate e (M.conditionalDensity m φ) (EuclideanSpace.single m (1 : ℂ)) ε₀) :
    (1 - 2 * Real.sqrt ((1 - p₀ * (1 - ε₀)) * (p₀ * (1 - ε₀)))) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * M.worstCost (fun _ => 1) := by
  have hread : ∀ m, p₀ * (1 - ε₀) ≤ readProb e m (M.successDensity m φ) := fun m =>
    le_readProb_of_heralded M m φ e he m hε₀1 (by linarith) (hher m).1 (hher m).2
  by_cases ha : p₀ * (1 - ε₀) ≤ 1
  · have key := search_count_ge_measured_sharp hN P c hO M hφ e he (δ := 1 - p₀ * (1 - ε₀))
      (by linarith) (by linarith) fun m => by rw [sub_sub_cancel]; exact hread m
    rwa [sub_sub_cancel] at key
  · push Not at ha
    have key := search_count_ge_measured_sharp hN P c hO M hφ e he (δ := 0) le_rfl
      (by norm_num) fun m => by linarith [hread m]
    have h0 : Real.sqrt ((1 - p₀ * (1 - ε₀)) * (p₀ * (1 - ε₀))) = 0 :=
      Real.sqrt_eq_zero'.mpr (by nlinarith)
    rw [h0]
    simpa using key

/-- **The lower half of `hs:cor:unitary` for measured algorithms, ordinary entry lookup,
heralded form.** A measured algorithm over the reversible entry lookup of the search family (any
payload `W`) that, on the input `J|0⟩` of an isometric encoding `J` and every instance `m`,
succeeds with probability at least `p₀` and has conditional output within trace distance
`ε₀ ≤ 1` of `U_m |0⟩`, with `p₀ (1 - ε₀) ≥ 1/2`, makes at least
`(1 - 2 √(δ (1 - δ))) √(N - 1) / 2` entry calls, inverse calls included, in the worst case,
`δ = 1 - p₀ (1 - ε₀)`. -/
theorem entry_count_ge_measured_heralded {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {N : ℕ} [NeZero N] (hN : 2 ≤ N) {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      LookupControlledGate.oracle (K := W) (searchTable N) m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => W))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {p₀ ε₀ : ℝ}
    (hε₀1 : ε₀ ≤ 1) (hp : 1 / 2 ≤ p₀ * (1 - ε₀))
    (himpl : ∀ m, p₀ ≤ M.successMass m (J (EuclideanSpace.single 0 1)) ∧
      DensityAccurate e (M.conditionalDensity m (J (EuclideanSpace.single 0 1)))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (1 - 2 * Real.sqrt ((1 - p₀ * (1 - ε₀)) * (p₀ * (1 - ε₀)))) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * M.worstCost (fun _ => 1) := by
  have hJ0 : ‖J (EuclideanSpace.single 0 (1 : ℂ))‖ = 1 := by
    rw [(J.norm_map_iff_adjoint_comp_self.mpr hJ), PiLp.norm_single, norm_one]
  refine search_count_ge_measured_heralded hN (PhaseBridge.xorFamily (Fin N × Fin N) W)
    (fun a => a.1 + a.2) (fun m => ?_) M hJ0 e he hε₀1 hp fun m => ?_
  · refine (PhaseBridge.lookup_eq_phase (searchTable N) m).trans
      (congrArg _ (funext fun a => ?_))
    simp [Search.markedString, searchTable_eq_one_iff]
  · obtain ⟨hmass, hacc⟩ := himpl m
    rw [searchMatrix_single_zero] at hacc
    exact ⟨hmass, hacc⟩

/-- **The lower half of `hs:cor:unitary` for measured algorithms, ordinary entry lookup.** A
measured algorithm over the reversible entry lookup of the search family (any payload `W`) that
implements every `U_m` on an isometric encoding `J` (success probability one and output within
trace distance `ε₀ ≤ 1/2` of `U_m ψ` for every unit input `ψ`) makes at least
`(1 - 2 √(ε₀ (1 - ε₀))) √(N - 1) / 2` entry calls, inverse calls included, in the worst case. -/
theorem entry_count_ge_measured {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {N : ℕ} [NeZero N] (hN : 2 ≤ N) {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      LookupControlledGate.oracle (K := W) (searchTable N) m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => W))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ}
    (hε₀1 : ε₀ ≤ 1 / 2)
    (himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate e (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) ε₀) :
    (1 - 2 * Real.sqrt (ε₀ * (1 - ε₀))) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * M.worstCost (fun _ => 1) := by
  have key := entry_count_ge_measured_heralded hN M J hJ e he (p₀ := 1) (by linarith)
    (by linarith) fun m => by
      obtain ⟨hmass, hacc⟩ := himpl m (EuclideanSpace.single 0 1)
        (by rw [PiLp.norm_single, norm_one])
      exact ⟨hmass.ge, hacc⟩
  simpa only [one_mul, sub_sub_cancel] using key

/-- **The lower half of `hs:cor:unitary` for measured algorithms, released entry oracle,
heralded form**: the bound of `entry_count_ge_measured_heralded` over the oracle
`UnitaryEntryOracle.oracle (searchData N) γ η t ε` of the upper bound, for all parameters. -/
theorem implementation_count_ge_measured_heralded {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ) {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {p₀ ε₀ : ℝ}
    (hε₀1 : ε₀ ≤ 1) (hp : 1 / 2 ≤ p₀ * (1 - ε₀))
    (himpl : ∀ m, p₀ ≤ M.successMass m (J (EuclideanSpace.single 0 1)) ∧
      DensityAccurate e (M.conditionalDensity m (J (EuclideanSpace.single 0 1)))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (1 - 2 * Real.sqrt ((1 - p₀ * (1 - ε₀)) * (p₀ * (1 - ε₀)))) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * M.worstCost (fun _ => 1) := by
  have hJ0 : ‖J (EuclideanSpace.single 0 (1 : ℂ))‖ = 1 := by
    rw [(J.norm_map_iff_adjoint_comp_self.mpr hJ), PiLp.norm_single, norm_one]
  refine search_count_ge_measured_heralded hN (LiftPhase.entryFamily (n := Fin N) γ η t ε)
    (fun a => a.1.2 + a.2.2) (fun m => ?_) M hJ0 e he hε₀1 hp fun m => ?_
  · refine (LiftPhase.oracle_eq_phase (searchData N) γ η t ε m).trans
      (congrArg _ (funext fun a => ?_))
    change decide (searchTable N m (a.1.2, a.2.2) = 1) = decide (a.1.2 + a.2.2 = m)
    simp [searchTable_eq_one_iff]
  · obtain ⟨hmass, hacc⟩ := himpl m
    rw [searchMatrix_single_zero] at hacc
    exact ⟨hmass, hacc⟩

/-- **The lower half of `hs:cor:unitary` for measured algorithms, released entry oracle**: the
same bound over the oracle `UnitaryEntryOracle.oracle (searchData N) γ η t ε` of the upper
bound, for all parameters. -/
theorem implementation_count_ge_measured {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {ε₀ : ℝ}
    (hε₀1 : ε₀ ≤ 1 / 2)
    (himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate e (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) ε₀) :
    (1 - 2 * Real.sqrt (ε₀ * (1 - ε₀))) * Real.sqrt ((N : ℝ) - 1) ≤
      2 * M.worstCost (fun _ => 1) := by
  have key := implementation_count_ge_measured_heralded hN γ η t ε M J hJ e he (p₀ := 1)
    (by linarith) (by linarith) fun m => by
      obtain ⟨hmass, hacc⟩ := himpl m (EuclideanSpace.single 0 1)
        (by rw [PiLp.norm_single, norm_one])
      exact ⟨hmass.ge, hacc⟩
  simpa only [one_mul, sub_sub_cancel] using key

end

end DeferredMeasurementLowerBounds.Corollaries
