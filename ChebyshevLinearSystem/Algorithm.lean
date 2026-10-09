import ChebyshevLinearSystem.Run
import ChebyshevFilter.Facts
import SparseLinearSystems.Endpoint.Algorithm

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# The algorithm of Theorem `qls:thm:main` with the positive Chebyshev filter

All parameters are public: they depend on the sparsity `s`, the condition bound `κ` and the
accuracy `ε` only. The stages, candidates, repetitions and attempts are those of the released
protocol (`Endpoint.stagesM`, `Endpoint.sig`, `Endpoint.reps`, `1000` final attempts); only
the filter changes:

* stage `j` tests use the Chebyshev filter at `b(σ_j)` (`Augmented.bLow`) of degree
  `d_j = d_{σ_j}(1/100)` (`dTest`, `ChebyshevFilter.augDegree`), as in eq. `qls:eq:filtercost`;
* the final preparation uses `σ = 0`, the filter at `b(1/κ)` and the degree
  `d_0(ε/1000)` at the public gap `g = 1/κ` (`dFin`): one direct Chebyshev filter with target
  `δ = ε/1000`, as in the manuscript;
* one counter register of `T + 1` values, `T = 2 (d_fin + Σ_{j ≤ m} d_j)` (`Tc`), carries the
  LCU circuit of every run (`Register.lean`).

`testRun j r` is one fresh test of candidate `r` at stage `j`; `finalLeaf r` is the final
repeat at the estimate `r`; `algorithm` is the complete adaptive protocol over the released
physical oracle family (native sparse primitives and the controlled source preparation).
-/

namespace ChebyshevLinearSystem

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk
  Step Augmented ChebyshevFilter Protocol Endpoint
open scoped InnerProduct

/-! ### Public parameters -/

/-- Test filter degree `d_j = d_{σ_j}(1/100)` (equation `qls:eq:filtercost`). -/
def dTest (s : ℕ) (j : ℕ) : ℕ := augDegree (s : ℝ) (sig j) (1 / 100)

/-- Final filter degree `d_0(ε/1000)` at the public gap `g = 1/κ`. -/
def dFin (s : ℕ) (κ ε : ℝ) : ℕ := augDegree (s : ℝ) (1 / κ) (ε / 1000)

/-- The counter register size `T = 2 (d_fin + Σ_{j ≤ m} d_j)`. -/
def Tc (s : ℕ) (κ ε : ℝ) : ℕ :=
  2 * (dFin s κ ε + ∑ j ∈ Finset.range (stagesM κ + 1), dTest s j)

theorem test_fits (s : ℕ) (κ ε : ℝ) (j : ℕ) : 2 * dTest s (stageOf κ j) ≤ Tc s κ ε := by
  have h := Finset.single_le_sum (f := fun j => dTest s j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (show stageOf κ j < stagesM κ + 1 by
      have := stageOf_le κ j
      omega))
  unfold Tc
  omega

theorem final_fits (s : ℕ) (κ ε : ℝ) : 2 * dFin s κ ε ≤ Tc s κ ε := by
  unfold Tc
  omega

/-- `b = χ / √(1 + χ²) ∈ (-1, 1)` for every `s` and `g`. -/
theorem bLow_mem (s g : ℝ) : bLow s g ∈ Set.Ioo (-1 : ℝ) 1 := by
  have hpos : 0 < Real.sqrt (1 + chi s g ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have habs : |chi s g| < Real.sqrt (1 + chi s g ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  refine ⟨?_, bLow_lt_one s g⟩
  rw [bLow, lt_div_iff₀ hpos]
  linarith [neg_abs_le (chi s g)]

/-! ### The algorithm -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **The Chebyshev run of the augmented walk** (equations `qls:eq:cheberror` and
`qls:eq:filtercost`): under the hypotheses of the released gap theorem `Facts.gapO`
(`0 < g ≤ g_σ`), the run of `d_σ(δ)` signed steps with the filter at `b(g)` has success block
within `δ` of the eigenvalue-one projector `P_{σ,r}` of `W_{σ,r}(x)`, on every counter
register with `2 d_σ(δ) ≤ T`. -/
theorem augmented_run (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Facts.Aop D x‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Facts.Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1)
    (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (hr : 1 / 8 ≤ r) (g : ℝ) (hg0 : 0 < g)
    (hg : g ≤ RegularizationGap.gap κ σ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {T : ℕ}
    (hT : 2 * augDegree (s : ℝ) g δ ≤ T) :
    ‖((testFlag D (bLow (s : ℝ) g) T (augDegree (s : ℝ) g δ))†) ∘L
        ((runPhys D Ub sv T σ r (augDegree (s : ℝ) g δ)).eval x ∘L
          testFlag D (bLow (s : ℝ) g) T (augDegree (s : ℝ) g δ)) -
      UnitaryFilter.fixedProj (WwO D Ub sv σ r x)‖ ≤ δ := by
  rw [run_success_block D Ub hUb sv (bLow_mem _ _) hT σ r x]
  exact (augmented_filter D x hA1 κ hκ hlow Ub sv hb σ hσ₀ hσ₁ r hr g hg0 hg hδ0 hδ1).1

/-- **One fresh test** of candidate `r` at stage `j`: the `d_j` signed steps of the Chebyshev
filter on the seed `ψ ⊗ J e`, then the coefficient flag. -/
def testRun (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) (j : ℕ) (r : ℝ) : TestRun (physOracle D Ub (Tc s κ ε)) (PrivO n) where
  circuit := runPhys D Ub sv (Tc s κ ε) (sig (stageOf κ j)) r (dTest s (stageOf κ j))
  seed := seedVec D (bLow (s : ℝ) (sig (stageOf κ j))) (Tc s κ ε) (dTest s (stageOf κ j))
  seed_unit := seedVec_norm D (bLow_mem _ _) (test_fits s κ ε j)
  flag := testFlag D (bLow (s : ℝ) (sig (stageOf κ j))) (Tc s κ ε) (dTest s (stageOf κ j))
  flag_isometry := testFlag_isometry D (bLow_mem _ _) (test_fits s κ ε j)

/-- The final circuit at estimate `r`: the `d_0(ε/1000)` signed steps at `σ = 0`. -/
def finalCircuit (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε r : ℝ) : MultiOracleCircuit.Program (physOracle D Ub (Tc s κ ε)) :=
  runPhys D Ub sv (Tc s κ ε) 0 r (dFin s κ ε)

/-- **The final leaf**: at most `1000` fresh attempts, stopping at the first heralded
success; the output register holds the solution coordinates. -/
def finalLeaf (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) (r : ℝ) : ODERepeatProtocol.Protocol (physOracle D Ub (Tc s κ ε)) V0 :=
  ODERepeatProtocol.Protocol.repeatTrials
    (single (finalCircuit D Ub sv κ ε r)
      (seedVec D (bLow (s : ℝ) (1 / κ)) (Tc s κ ε) (dFin s κ ε))
      (seedVec_norm D (bLow_mem _ _) (final_fits s κ ε))
      (finalOutput D (bLow (s : ℝ) (1 / κ)) (Tc s κ ε) (dFin s κ ε))
      (finalOutput_isometry D (bLow_mem _ _) (final_fits s κ ε))) 1000

/-- **The complete algorithm of Theorem `qls:thm:main` with the positive Chebyshev filter**:
the released norm estimator (stages, candidates, repetitions) and final repeat, with the
Chebyshev LCU runs of signed walk steps. -/
def algorithm (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) : Tree (physOracle D Ub (Tc s κ ε)) (PrivO n) V0 :=
  Estimator.algorithm (testRun D Ub sv κ ε) (finalLeaf D Ub sv κ ε) (reps κ ε) (stagesM κ) κ

/-! ### Semantics of the runs -/

theorem testRun_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε : ℝ) (j : ℕ) (r : ℝ) (x : X) :
    IsUnitary ((testRun D Ub sv κ ε j r).circuit.eval x) :=
  runPhys_unitary D Ub hUb sv _ _ _ _ x

/-- The test success probability is the squared norm of the Chebyshev-filtered seed. -/
theorem testRun_probability (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε : ℝ) (j : ℕ) (r : ℝ)
    (x : X) :
    (testRun D Ub sv κ ε j r).probability x =
      ‖filterOp (WwO D Ub sv (sig (stageOf κ j)) r x) (bLow (s : ℝ) (sig (stageOf κ j)))
        (dTest s (stageOf κ j)) ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 := by
  show ‖((testFlag D (bLow (s : ℝ) (sig (stageOf κ j))) (Tc s κ ε) (dTest s (stageOf κ j)))†)
    ((runPhys D Ub sv (Tc s κ ε) (sig (stageOf κ j)) r (dTest s (stageOf κ j))).eval x
      (seedVec D (bLow (s : ℝ) (sig (stageOf κ j))) (Tc s κ ε) (dTest s (stageOf κ j))))‖ ^ 2 =
    _
  rw [test_amplitude D Ub hUb sv (bLow_mem _ _) (test_fits s κ ε j)]

theorem finalCircuit_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    IsUnitary ((finalCircuit D Ub sv κ ε r).eval x) :=
  runPhys_unitary D Ub hUb sv _ _ _ _ x

/-- The decoded amplitude of one final attempt. -/
def finalAmp (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε r : ℝ) (x : X) : V0 :=
  ((finalOutput D (bLow (s : ℝ) (1 / κ)) (Tc s κ ε) (dFin s κ ε))†)
    ((finalCircuit D Ub sv κ ε r).eval x
      (seedVec D (bLow (s : ℝ) (1 / κ)) (Tc s κ ε) (dFin s κ ε)))

/-- The decoded final amplitude is `S† J† F(W_{0,r}) J e` with the final Chebyshev filter. -/
theorem finalAmp_eq (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    finalAmp D Ub sv κ ε r x =
      (solEmb†) (((JwO D).toContinuousLinearMap†)
        (filterOp (WwO D Ub sv 0 r x) (bLow (s : ℝ) (1 / κ)) (dFin s κ ε)
          ((JwO D).toContinuousLinearMap eVec))) := by
  rw [finalAmp, finalCircuit, final_amplitude D Ub hUb sv (bLow_mem _ _) (final_fits s κ ε) 0 r x]

theorem finalLeaf_successMass (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε r : ℝ) (x : X) :
    (finalLeaf D Ub sv κ ε r).successMass x = 1 - (1 - ‖finalAmp D Ub sv κ ε r x‖ ^ 2) ^ 1000 :=
  single_successMass _ _ _ _ _ x 1000

theorem finalLeaf_leafDir (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (κ ε r : ℝ) (x : X) :
    leafDir x (finalLeaf D Ub sv κ ε r) =
      ODEStateNormalization.unitDirection (finalAmp D Ub sv κ ε r x) :=
  leafDir_single _ _ _ _ _ x 999

theorem finalLeaf_spec (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    0 ≤ (finalLeaf D Ub sv κ ε r).successMass x ∧ (finalLeaf D Ub sv κ ε r).successMass x ≤ 1 ∧
      ((finalLeaf D Ub sv κ ε r).successMass x ≠ 0 →
        ‖leafDir x (finalLeaf D Ub sv κ ε r)‖ = 1) ∧
      (finalLeaf D Ub sv κ ε r).successDensity x =
        (((finalLeaf D Ub sv κ ε r).successMass x : ℝ) : ℂ) •
          ODEMixedOutput.pureOperator (leafDir x (finalLeaf D Ub sv κ ε r)) := by
  rw [finalLeaf_leafDir]
  exact single_leaf_spec _ _ _ _ _ x (finalCircuit_unitary D Ub hUb sv κ ε r x) 1000

theorem finalAmp_norm_sq_le (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    ‖finalAmp D Ub sv κ ε r x‖ ^ 2 ≤ 1 :=
  ((single (finalCircuit D Ub sv κ ε r)
      (seedVec D (bLow (s : ℝ) (1 / κ)) (Tc s κ ε) (dFin s κ ε))
      (seedVec_norm D (bLow_mem _ _) (final_fits s κ ε))
      (finalOutput D (bLow (s : ℝ) (1 / κ)) (Tc s κ ε) (dFin s κ ε))
      (finalOutput_isometry D (bLow_mem _ _) (final_fits s κ ε))).probability_bounds x
    (fun _ => finalCircuit_unitary D Ub hUb sv κ ε r x) ⟨0, Nat.one_pos⟩).2

end

end ChebyshevLinearSystem
