import MeasuredUnitaryLowerBound.Endpoint.Entry
import DeferredMeasurementLowerBounds.Corollaries.Unitary

set_option autoImplicit false
set_option synthInstance.maxSize 8192

/-!
# The trace-distance endpoint `ε = 1/2` for algorithms with measurements inside a run

Corollary `hs:cor:unitary` of the manuscript (trace-distance form of the error range `0 < ε ≤ 1/2`,
"including inverse calls", "`Θ(√N)`") for measured algorithms
(`DeferredMeasurementLowerBounds.Model.Measured`: measurements, resets and classical control inside
a run; "Purification and deferred measurement include adaptive and randomised algorithms", the
closing sentence of the proof of `hsl:lem:precision`). The released bounds
`DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_heralded` and
`implementation_count_ge_measured` need `p₀ (1 - ε₀) > 1/2` for a positive factor, hence miss
`ε₀ = 1/2`. Here the deferral of the measured algorithm is compiled, as in
`DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_sharp`, into one program over
the controlled spectated phase oracle (`DeferredMeasurementLowerBounds.Access.phaseCircuits`,
`DeferredMeasurementLowerBounds.Access.compiledProgram`), whose decoded final vectors read the
output values with the probabilities `readProb` of the measured algorithm; the summed pair gaps of
`Global.program_count_ge_of_reads` with `Reading.measured_read_bound` then give, for success
probability at least `p₀ > 0` and conditional trace distance `ε₀ ≤ 1/2`,

  `(p₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) Q`,

`Q` the worst-case number of oracle calls over all transcripts, inverse calls included.

* `search_count_ge_measured_endpoint`: the generic form for a Boolean phase oracle of marked
  strings;
* `implementation_count_ge_measured_endpoint` (released entry oracle) and
  `entry_count_ge_measured_endpoint` (ordinary entry lookup, any payload): on the input `J|0⟩`
  of an isometric encoding;
* `implementation_count_ge_measured_half`, `implementation_count_ge_measured_sqrt`: algorithms
  that implement every `U_m` with success probability one and trace distance `1/2` on every unit
  input: `(N - 2)² ≤ 16 (N - 1) √(N - 1) Q`, and `√(N - 1) ≤ 64 Q` for `N ≥ 3`.

No finite dimension of the oracle workspace is needed; the output space is finite-dimensional,
as in the released measured bounds.
-/

namespace MeasuredUnitaryLowerBound.Deferred

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open SparseLowerBounds.Readout
open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open UnitaryImplementationExtensions.Search (markedString)
open DeferredMeasurementLowerBounds.Model
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace
open DeferredMeasurementLowerBounds.Deferral DeferredMeasurementLowerBounds.Access
open DeferredMeasurementLowerBounds.Readout
open DeferredMeasurementLowerBounds.Corollaries (readProb norm_sq_sel_liftReadout)
open AdaptiveODELowerBound.Access (ctrlFamily activeEmbed activeEmbed_isometry)
open DeferredMeasurementLowerBounds.SearchReadout (sel sel_isStarProjection re_inner_proj)

/-- The difference of two output-value projections is a contraction. -/
theorem norm_sel_sub_le {N : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (x x' : Fin N) : ‖sel (G := G) x - sel x'‖ ≤ 1 := by
  have h : sel (G := G) x - sel x' = Joint.fiber fun i =>
      (if i = x then (1 : G →L[ℂ] G) else 0) - (if i = x' then 1 else 0) := by
    ext Ψ i
    rfl
  rw [h]
  refine Joint.norm_fiber_le _ zero_le_one fun i => ?_
  split_ifs
  · simp
  · rw [sub_zero]; exact ContinuousLinearMap.norm_id_le
  · rw [zero_sub, norm_neg]; exact ContinuousLinearMap.norm_id_le
  · simp

set_option maxHeartbeats 1600000 in
/-- **Search for measured algorithms up to trace distance `1/2`.** A measured algorithm over
the phase oracle of the marked strings of `c` that, on every instance `m`, succeeds with
probability at least `p₀ > 0` and whose conditional output, read through the isometry `e`, is
within trace distance `ε₀ ≤ 1/2` of `|m⟩`, satisfies
`(p₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) Q`, `Q` its worst-case number of calls. -/
theorem search_count_ge_measured_endpoint {N : ℕ} (hN : 2 ≤ N) {K I : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [Fintype I]
    (P : ProjFamily K I) (c : I → Fin N) {E G : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    {O : Unit → Fin N → K →L[ℂ] K} (hO : ∀ m, O () m = P.phase (markedString c m))
    (M : Measured O E) {φ : K} (hφ : ‖φ‖ = 1) (e : E →L[ℂ] SysGarb (Fin N) G)
    (he : e† ∘L e = 1) {p₀ ε₀ : ℝ} (hp₀ : 0 < p₀) (hε₀ : ε₀ ≤ 1 / 2)
    (hher : ∀ m, p₀ ≤ M.successMass m φ ∧
      DensityAccurate e (M.conditionalDensity m φ) (EuclideanSpace.single m (1 : ℂ)) ε₀) :
    (p₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  obtain rfl : O = fun _ m => P.phase (markedString c m) :=
    funext fun u => funext fun m => by cases u; exact hO m
  have hEnc := activeEmbed_isometry (B := Joint (DRec M) K)
  set Ac := activeEmbed (Joint (DRec M) K)
  let p := compiledProgram (fun _ : Unit => True) M Ac hEnc
    (phaseCircuits P (fun m => markedString c m))
  have hφ₀ : ‖Ac (deferredSeed M φ)‖ = 1 := by
    rw [(Ac.norm_map_iff_adjoint_comp_self.mpr hEnc) _, norm_deferredSeed M hφ]
  have hD : (Ac ∘L deferredOutput M)† ∘L (Ac ∘L deferredOutput M) = 1 := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc (Ac†) Ac (deferredOutput M), hEnc,
      show (1 : Joint (DRec M) K →L[ℂ] Joint (DRec M) K) ∘L deferredOutput M = deferredOutput M
        from ContinuousLinearMap.id_comp _, deferredOutput_isometry]
  have hamp : ∀ m, ((Ac ∘L deferredOutput M)†) (p.eval m (Ac (deferredSeed M φ))) =
      amplitude (fun _ : Unit => True) M m φ := fun m =>
    amplitude_compiled (fun _ _ => P.isUnitary_phase _)
      (fun _ _ => (ctrlFamily (P.spectate (DRec M))).isUnitary_phase _) M φ _ hEnc _
      (phaseCircuits_eval P _) m
  set Gm := liftReadout (DOut M) e ∘L (Ac ∘L deferredOutput M)†
  have hG : ‖Gm‖ ≤ 1 := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_one₀
      (GeneralODE.Registers.norm_le_one_of_isometry _ (liftReadout_isometry he)) (norm_nonneg _)
      (GeneralODE.Registers.norm_le_one_of_isometry _ hD)
  let R : Fin N → _ := fun y => Gm† ∘L sel y ∘L Gm
  have hR : ∀ x x', x ≠ x' → ‖R x - R x'‖ ≤ 1 := by
    intro x x' _
    have h : R x - R x' = Gm† ∘L ((sel x - sel x') ∘L Gm) := by
      simp only [R, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    rw [h]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact mul_le_one₀ hG (norm_nonneg _) ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_one₀ (norm_sel_sub_le x x') (norm_nonneg _) hG))
  have hRe : ∀ x y, (⟪p.eval x (Ac (deferredSeed M φ)),
      R y (p.eval x (Ac (deferredSeed M φ)))⟫_ℂ).re =
        readProb e y (M.successDensity x φ) := by
    intro x y
    show (⟪_, (Gm†) (sel y (Gm _))⟫_ℂ).re = _
    rw [ContinuousLinearMap.adjoint_inner_right, re_inner_proj (sel_isStarProjection y)]
    show ‖sel y (liftReadout (DOut M) e (((Ac ∘L deferredOutput M)†)
      (p.eval x (Ac (deferredSeed M φ)))))‖ ^ 2 = _
    rw [hamp, norm_sq_sel_liftReadout, sum_pure_amplitude]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : 0 ≤ p₀ * ((N : ℝ) * (1 - ε₀) - 1) := mul_nonneg hp₀.le (by nlinarith)
  have key := Global.program_count_ge_of_reads hN (ctrlFamily (P.spectate (DRec M))) c 1
    (by ext v; simp) (fun _ _ => (ctrlFamily (P.spectate (DRec M))).isUnitary_phase _)
    (fun _ => 1) (fun _ => ⟨.query, fun _ => by ext v; rfl, le_rfl⟩) p _ hφ₀ R hR hb
    (fun x => by
      simp only [hRe]
      exact Reading.measured_read_bound hN M φ e he hp₀ hε₀ x (hher x).1 (hher x).2)
  have hcount : p.cost (fun _ => 1) ≤ M.worstCost (fun _ => 1) := by
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
  have hc : 0 ≤ 4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) :=
    mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  exact key.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcount) hc)

/-- **The lower half of `hs:cor:unitary` for measured algorithms up to trace distance `1/2`,
released entry oracle**: a measured algorithm over `UnitaryEntryOracle.oracle (searchData N) γ η
t ε` that, on the input `J|0⟩` of an isometric encoding `J` and every instance `m`, succeeds
with probability at least `p₀ > 0` and has conditional output within trace distance
`ε₀ ≤ 1/2` of `U_m |0⟩`, satisfies `(p₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) Q`, `Q` its
worst-case number of entry calls, inverse calls included. -/
theorem implementation_count_ge_measured_endpoint {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (γ η t ε : ℝ) {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {p₀ ε₀ : ℝ}
    (hp₀ : 0 < p₀) (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, p₀ ≤ M.successMass m (J (EuclideanSpace.single 0 1)) ∧
      DensityAccurate e (M.conditionalDensity m (J (EuclideanSpace.single 0 1)))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (p₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  have hJ0 : ‖J (EuclideanSpace.single 0 (1 : ℂ))‖ = 1 := by
    rw [(J.norm_map_iff_adjoint_comp_self.mpr hJ), PiLp.norm_single, norm_one]
  refine search_count_ge_measured_endpoint hN (LiftPhase.entryFamily (n := Fin N) γ η t ε)
    (fun a => a.1.2 + a.2.2) (fun m => ?_) M hJ0 e he hp₀ hε₀ fun m => ?_
  · refine (LiftPhase.oracle_eq_phase (searchData N) γ η t ε m).trans
      (congrArg _ (funext fun a => ?_))
    change decide (searchTable N m (a.1.2, a.2.2) = 1) = decide (a.1.2 + a.2.2 = m)
    simp [searchTable_eq_one_iff]
  · obtain ⟨hmass, hacc⟩ := himpl m
    rw [searchMatrix_single_zero] at hacc
    exact ⟨hmass, hacc⟩

/-- **The same up to trace distance `1/2`, ordinary entry lookup** (any payload `W`). -/
theorem entry_count_ge_measured_endpoint {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] {N : ℕ} [NeZero N] (hN : 2 ≤ N) {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      LookupControlledGate.oracle (K := W) (searchTable N) m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] PiLp 2 (fun _ : (Fin N × Fin N) × ZMod 2 => W))
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1) {p₀ ε₀ : ℝ}
    (hp₀ : 0 < p₀) (hε₀ : ε₀ ≤ 1 / 2)
    (himpl : ∀ m, p₀ ≤ M.successMass m (J (EuclideanSpace.single 0 1)) ∧
      DensityAccurate e (M.conditionalDensity m (J (EuclideanSpace.single 0 1)))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) (EuclideanSpace.single 0 1)) ε₀) :
    (p₀ * ((N : ℝ) * (1 - ε₀) - 1)) ^ 2 ≤
      4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  have hJ0 : ‖J (EuclideanSpace.single 0 (1 : ℂ))‖ = 1 := by
    rw [(J.norm_map_iff_adjoint_comp_self.mpr hJ), PiLp.norm_single, norm_one]
  refine search_count_ge_measured_endpoint hN (PhaseBridge.xorFamily (Fin N × Fin N) W)
    (fun a => a.1 + a.2) (fun m => ?_) M hJ0 e he hp₀ hε₀ fun m => ?_
  · refine (PhaseBridge.lookup_eq_phase (searchTable N) m).trans
      (congrArg _ (funext fun a => ?_))
    simp [Search.markedString, searchTable_eq_one_iff]
  · obtain ⟨hmass, hacc⟩ := himpl m
    rw [searchMatrix_single_zero] at hacc
    exact ⟨hmass, hacc⟩

/-- **Measured implementations at trace distance `1/2`, released entry oracle** (Corollary
`hs:cor:unitary`, trace-distance form of the endpoint `ε = 1/2`):
a measured algorithm that implements every `U_m`
on an isometric encoding `J` (success probability one and output within trace distance `1/2`
of `U_m ψ` for every unit input `ψ`) satisfies `(N - 2)² ≤ 16 (N - 1) √(N - 1) Q`. -/
theorem implementation_count_ge_measured_half {N : ℕ} [NeZero N] (hN : 2 ≤ N) (γ η t ε : ℝ)
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate e (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2)) :
    ((N : ℝ) - 2) ^ 2 ≤
      16 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * M.worstCost (fun _ => 1) := by
  have key := implementation_count_ge_measured_endpoint hN γ η t ε M J hJ e he (p₀ := 1)
    (ε₀ := 1 / 2) one_pos le_rfl fun m => by
      obtain ⟨hmass, hacc⟩ := himpl m (EuclideanSpace.single 0 1)
        (by rw [PiLp.norm_single, norm_one])
      exact ⟨hmass.ge, hacc⟩
  have h4 := mul_le_mul_of_nonneg_left key (by norm_num : (0 : ℝ) ≤ 4)
  calc ((N : ℝ) - 2) ^ 2 = 4 * (1 * ((N : ℝ) * (1 - 1 / 2) - 1)) ^ 2 := by ring
    _ ≤ _ := h4
    _ = _ := by ring

/-- **`Ω(√N)` for measured implementations at trace distance `1/2`**: under the hypotheses of
`implementation_count_ge_measured_half` with `N ≥ 3`, `√(N - 1) ≤ 64 Q`. -/
theorem implementation_count_ge_measured_sqrt {N : ℕ} [NeZero N] (hN : 3 ≤ N) (γ η t ε : ℝ)
    {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ η t ε m) E)
    (J : EuclideanSpace ℂ (Fin N) →L[ℂ] UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε)
    (hJ : J† ∘L J = 1) (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (himpl : ∀ m (ψ : EuclideanSpace ℂ (Fin N)), ‖ψ‖ = 1 → M.successMass m (J ψ) = 1 ∧
      DensityAccurate e (M.conditionalDensity m (J ψ))
        (SparseStateOverlap.matrixOperator (searchMatrix N m) ψ) (1 / 2)) :
    Real.sqrt ((N : ℝ) - 1) ≤ 64 * M.worstCost (fun _ => 1) := by
  have h := Adaptive.sqrt_le_of_half hN
    (implementation_count_ge_measured_half (by omega) γ η t ε M J hJ e he himpl)
  linarith

end
end MeasuredUnitaryLowerBound.Deferred
