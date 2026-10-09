import DeferredMeasurementLowerBounds.Deferral.Theorem
import DeferredMeasurementLowerBounds.Model.Embed
import DeferredMeasurementLowerBounds.Corollaries.LinearSystem
import DeferredMeasurementLowerBounds.Corollaries.Unitary
import LinearSystemLowerBound.Matching

set_option autoImplicit false

/-!
# Non-vacuity of the deferral and of the measured lower bounds

* `deferral_midRun`: `Deferral.deferral` applies to a measured algorithm with a genuine
  measurement in the middle of a run followed by a classically controlled oracle call
  (`midRun`: a two-outcome projective measurement, on outcome `1` one call of a phase oracle);
  the deferred program makes at most one counted call.
* `released_linear_system_measured`: the released algorithm of Theorem `qls:thm:main`
  (`SparseLinearSystems.Endpoint.algorithm`), as a measured algorithm (`Model.ofTree`), meets
  every hypothesis of `Corollaries.lower_bound_sharp_measured` on the hard family of Theorem
  `qlsl:thm:main`, so its worst-case count lies between `κ √s ln(1/ε)/1536` and
  `4·10¹² √s κ ln(1/ε)` (the measured form of `LinearSystemLowerBound.upper_meets_lower`).
* `released_unitary_measured`: the released circuit of
  `UnitaryImplementationExtensions.LowerBound.theta_of_error` at error `1/4`, run as a measured
  algorithm, meets every hypothesis of `Corollaries.implementation_count_ge_measured`; both
  halves of `Θ(√N)` (Corollary `hs:cor:unitary`, last sentence) hold for it in one oracle
  model.
-/

namespace DeferredMeasurementLowerBounds.NonVacuity

open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open scoped InnerProduct InnerProductSpace

noncomputable section

/-! ### A measurement inside a run followed by a classically controlled call -/

/-- The two-dimensional workspace of `midRun`: one record register with one value besides the
fresh one. -/
abbrev MidRunSpace : Type := Joint (Rec 1 1) ℂ

/-- A phase oracle `x ↦ (-1)^x` on `MidRunSpace`. -/
def midRunOracle : Unit → Bool → MidRunSpace →L[ℂ] MidRunSpace := fun _ x => if x then -1 else 1

/-- The phase oracle is unitary. -/
theorem midRunOracle_unitary : ∀ l x, IsUnitary (midRunOracle l x) := by
  intro l x
  cases x <;> simp [midRunOracle, IsUnitary]

/-- The isometry `ℂ → MidRunSpace` onto the fresh value. -/
def freshVec : ℂ →L[ℂ] MidRunSpace := freshInj 1 1

/-- **A measured algorithm with a measurement inside a run**: measure
`{G G†, 1 - G G†}` (`G = freshVec`); on outcome `0` output at once, on outcome `1` call the
oracle and then output (a classically controlled call). -/
def midRun : Measured midRunOracle ℂ :=
  .instrument 2 (heraldKraus freshVec) (heraldKraus_complete (freshInj_isometry 1 1))
    (fun i => if i = 0 then .output freshVec (freshInj_isometry 1 1)
      else .call () false (.output freshVec (freshInj_isometry 1 1)))

/-- `midRun` makes at most one call. -/
theorem midRun_worstCost : midRun.worstCost (countWeight fun _ : Unit => True) = 1 := by
  rw [midRun, worstCost_herald freshVec (freshInj_isometry 1 1)]
  simp [Measured.worstCost, countWeight]

/-- The initial vector `freshVec 1` is a unit vector. -/
theorem freshVec_unit : ‖freshVec (1 : ℂ)‖ = 1 := by
  rw [(freshVec.norm_map_iff_adjoint_comp_self.mpr (freshInj_isometry 1 1)) 1, norm_one]

/-- **Deferral of a measurement inside a run** (purification and deferred measurement, proofs of
Lemmas `hsl:lem:precision` and `qlsl:lem:xor`): `Deferral.deferral` applied to `midRun` gives a
unitary program over the record-selected calls with the same success mass and heralded output
and at most one counted call. -/
theorem deferral_midRun : ∃ (R J : Type) (_ : Fintype R) (_ : Fintype J)
    (p : MultiOracleCircuit.Program (selFamily midRunOracle (fun _ : Unit => True) R))
    (seed : Joint R MidRunSpace) (out : Joint J ℂ →L[ℂ] Joint R MidRunSpace),
    ‖seed‖ = 1 ∧ out† ∘L out = 1 ∧ (∀ x, IsUnitary (p.eval x)) ∧ p.cost selWeight ≤ 1 ∧
    ∀ x, ∑ j, ODEMixedOutput.pureOperator (((out†) (p.eval x seed)) j) =
        midRun.successDensity x (freshVec 1) ∧
      ‖(out†) (p.eval x seed)‖ ^ 2 = midRun.successMass x (freshVec 1) := by
  obtain ⟨R, J, hR, hJ, p, seed, out, h1, h2, h3, h4, h5⟩ :=
    deferral (counted := fun _ : Unit => True) midRunOracle_unitary midRun freshVec_unit
  exact ⟨R, J, hR, hJ, p, seed, out, h1, h2, h3, h4.trans_eq midRun_worstCost, h5⟩

end

/-! ### The released linear-system algorithm as a measured algorithm -/

section LinearSystem

open LinearSystemLowerBound LinearSystemLowerBound.Hard LinearSystemLowerBound.Params
  LinearSystemLowerBound.Native

set_option synthInstance.maxSize 8192 in
/-- **The released algorithm of Theorem `qls:thm:main` as a measured algorithm** (Theorem
`qlsl:thm:main` for measured algorithms is not vacuous): on the hard family, the released
algorithm, translated by `Model.ofTree` and started from a unit vector, meets every hypothesis
of `Corollaries.lower_bound_sharp_measured`, and its worst-case number of matrix-oracle calls
lies between `κ √s ln(1/ε)/1536` and the released `4·10¹² √s κ ln(1/ε)`. -/
theorem released_linear_system_measured (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    ∃ (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) (ZMod 8) s)
      (φ : SparseLinearSystems.Step.Phys (Ind κ ε s) (ZMod 8)
        (SparseLinearSystems.Endpoint.Tw s κ ε)),
      ‖φ‖ = 1 ∧
      κ * Real.sqrt s * Real.log (1 / ε) / 1536 <
        ((ofTree (SparseLinearSystems.Endpoint.algorithm D (fun _ => 1) (rhsVec κ ε s) κ
          ε)).worstCost SparseLinearSystems.Step.wMat : ℝ) ∧
      ((ofTree (SparseLinearSystems.Endpoint.algorithm D (fun _ => 1) (rhsVec κ ε s) κ
          ε)).worstCost SparseLinearSystems.Step.wMat : ℝ) ≤
        4 * 10 ^ 12 * Real.sqrt s * κ * Real.log (1 / ε) := by
  obtain ⟨D, hDm, hrow, hcol, enc, henc⟩ := exists_access κ ε s hκ hs hε hε1
  have hprom : ∀ x, SparseLinearSystems.Endpoint.Promise D κ x := by
    intro x
    obtain ⟨h1, h2, h3⟩ := family_promise κ ε s hκ x
    refine ⟨?_, ?_, ?_⟩
    · change ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1
      rw [hDm]; exact h1
    · change IsUnit (SparseStateOverlap.matrixOperator (D.matrix x))
      rw [hDm]; exact h2
    · change ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ κ
      rw [hDm]; exact h3
  have hsol : ∀ x, SparseLinearSystems.Endpoint.solutionState D (fun _ => 1) (rhsVec κ ε s) x =
      target κ ε s x := by
    intro x
    change ODEStateNormalization.unitDirection (Ring.inverse
      (SparseStateOverlap.matrixOperator (D.matrix x)) ((1 : EuclideanSpace ℂ (Ind κ ε s) →L[ℂ] _)
        (rhsVec κ ε s))) = _
    rw [hDm]
    rfl
  have hUb : ∀ x : Inp κ ε s,
      OracleCircuit.IsUnitary
        (1 : EuclideanSpace ℂ (Ind κ ε s) →L[ℂ] EuclideanSpace ℂ (Ind κ ε s)) :=
    fun _ => OracleCircuit.isUnitary_one
  obtain ⟨hup, -, hguar⟩ := SparseLinearSystems.Endpoint.main D (fun _ => 1) hUb (rhsVec κ ε s)
    (rhsVec_norm κ ε s hs) κ ε (by linarith) hε (by linarith)
  have hO := SparseLinearSystems.Step.physOracle_unitary D (fun _ => 1) hUb
    (SparseLinearSystems.Endpoint.Tw s κ ε)
  obtain ⟨φ, hφ⟩ := exists_unit_of_successMass_pos
    (SparseLinearSystems.Endpoint.algorithm D (fun _ => 1) (rhsVec κ ε s) κ ε) default
    (by have := (hguar default (hprom default)).2.1; linarith)
  refine ⟨D, φ, hφ, ?_, ?_⟩
  · refine DeferredMeasurementLowerBounds.Corollaries.lower_bound_sharp_measured κ ε s hκ hs hε
      hε1 D hDm hrow hcol ⟨fun _ => enc, henc⟩ _ SparseLinearSystems.Step.wMat
      (physOracle_admissible D (fun _ => 1) hUb (fun _ _ => rfl) _) unitGarbage _ φ hφ
      fun x => ?_
    obtain ⟨-, hsucc, -, hd⟩ := hguar x (hprom x)
    rw [hsol x] at hd
    rw [successMass_ofTree hO _ x hφ, conditionalDensity_ofTree hO _ x hφ, ptrace_unitGarbage]
    exact ⟨hsucc, hd⟩
  · rw [worstCost_ofTree]
    exact hup

end LinearSystem

/-! ### The released unitary circuit as a measured algorithm -/

section Unitary

open UnitaryImplementationExtensions UnitaryImplementationExtensions.SearchFamily
open AdaptiveHamiltonianLowerBound (DensityAccurate)

set_option synthInstance.maxSize 8192 in
/-- **The released unitary circuit as a measured algorithm** (the lower half of the last
sentence of Corollary `hs:cor:unitary` for measured algorithms is not vacuous): the released
circuit of `UnitaryImplementationExtensions.LowerBound.theta_of_error` at error `1/4`, followed
by the trivial output, meets every hypothesis of `Corollaries.implementation_count_ge_measured`,
and its worst-case number of entry calls lies between `(1 - 2√(3/16)) √(N - 1)/2` and the
released upper bound. -/
theorem released_unitary_measured {N : ℕ} [NeZero N] (hN : 2 ≤ N) :
    ∃ (γ : ℝ) (M : Measured (fun (_ : Unit) (m : Fin N) =>
        UnitaryEntryOracle.oracle (searchData N) γ 1 (Real.pi / 2) (1 / 4) m)
        (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4))),
      (1 - 2 * Real.sqrt ((1 / 4 : ℝ) * (1 - 1 / 4))) * Real.sqrt ((N : ℝ) - 1) ≤
        2 * M.worstCost (fun _ => 1) ∧
      (M.worstCost (fun _ => 1) : ℝ) ≤ General.exactConstant *
        (Real.sqrt (Real.log (1 / (1 / 4 : ℝ))) + Real.log (1 / (1 / 4 : ℝ))) *
          Real.sqrt (N : ℝ) := by
  obtain ⟨⟨γ, -, -, p, hcount, hinput, hact⟩, -, -⟩ :=
    LowerBound.theta_of_error hN (1 / 4) (by norm_num) (by norm_num)
  have h1 : ContinuousLinearMap.adjoint
      (1 : UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4) →L[ℂ]
        UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4)) = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hout : ContinuousLinearMap.adjoint
      (1 : UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4) →L[ℂ]
        UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4)) ∘L
        (1 : UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4) →L[ℂ]
          UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4)) = 1 := by
    rw [h1]
    rfl
  let M : Measured (fun (_ : Unit) (m : Fin N) =>
      UnitaryEntryOracle.oracle (searchData N) γ 1 (Real.pi / 2) (1 / 4) m)
      (UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ 1 (Real.pi / 2) (1 / 4)) :=
    ofProgram (MultiOracleCircuit.Program.embed () p) (.output 1 hout)
  have hcost : M.worstCost (fun _ => 1) = p.count := by
    simp only [M, worstCost_ofProgram, worstCost_output, MultiOracleCircuit.Program.cost_embed,
      mul_one, add_zero]
  refine ⟨γ, M, ?_, ?_⟩
  · have key := DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured hN γ 1
      (Real.pi / 2) (1 / 4) M (General.input (searchData N) γ (1 / 4)) hinput
      (Hamiltonian.endpointReadout (General.input (searchData N) γ (1 / 4)) 0)
      (Hamiltonian.endpointReadout_isometry _ hinput 0) (ε₀ := 1 / 4) (by norm_num)
      fun m ψ hψ => by
        have hU := (hact m).1
        have hΦ : ‖p.eval m (General.input (searchData N) γ (1 / 4) ψ)‖ = 1 := by
          rw [PositiveAdversary.norm_map_of_isUnitary hU,
            (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr hinput, hψ]
        have hmass : M.successMass m (General.input (searchData N) γ (1 / 4) ψ) = 1 := by
          simp only [M, successMass_ofProgram, successMass_output, h1, one_apply_eq_self,
            MultiOracleCircuit.Program.eval_embed, hΦ, one_pow]
        refine ⟨hmass, ?_⟩
        have hdens : M.conditionalDensity m (General.input (searchData N) γ (1 / 4) ψ) =
            ODEMixedOutput.pureOperator (p.eval m (General.input (searchData N) γ (1 / 4) ψ)) := by
          rw [Measured.conditionalDensity, hmass]
          simp only [M, successDensity_ofProgram, successDensity_output, h1, one_apply_eq_self,
            MultiOracleCircuit.Program.eval_embed, inv_one, Complex.ofReal_one, one_smul]
        rw [hdens, AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff]
        exact Hamiltonian.accurate_of_endpoint _ hinput 0 (p.eval m) hU.norm_le_one _ hψ.le
          (by rw [PositiveAdversary.norm_map_of_isUnitary (searchMatrix_unitary N m), hψ])
          (hact m).2
    rwa [hcost] at key ⊢
  · rw [hcost]
    exact hcount

end Unitary

end DeferredMeasurementLowerBounds.NonVacuity
