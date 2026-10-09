import ChebyshevLinearSystemFinite.Runs
import ChebyshevLinearSystemFinite.Estimator
import ChebyshevLinearSystemFinite.Facts

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# The finite-degree protocol and its implementations

The finite-degree protocol is the released Chebyshev protocol (`ChebyshevLinearSystem.algorithm`:
the released estimator stages, candidates, repetitions and `1000` final attempts, Chebyshev LCU
runs of signed walk steps) with the degrees of equation `qls:eq:finitedegree`:

* `testRunF j r`: a test of candidate `r` at stage `j`, the filter at `b(σ_j)` of degree
  `d^fin_j = d_{σ_j}(1/100) + 1` (`dTestF`) on the seed `ψ ⊗ J e`, measuring the coefficient
  flag;
* `finalRunF r`: a final attempt at the estimate `r`, the filter at `b(1/κ)` of degree
  `d^fin_fin = d_0(ε/1000) + 1` (`dFinF`), decoding the walk boundary and the solution
  coordinates (a `TestRun` whose flag is the output isometry);
* one counter register of `TcF s κ ε + 1` values.

These are the *ideal* runs (exact known gates). `implAlgorithm κ ε test fin` is the protocol
with the classical control of the released estimator and arbitrary implemented runs: the tests
`test j r` and the final attempts `fin r`, repeated at most `1000` times
(`repeatLeaf`). `algorithmF` is the finite-degree protocol with exact gates.

Semantics of the ideal runs (from the released `ChebyshevLinearSystem` run layer):
`testRunF_amp` (the success vector is `F_{b,d}(W_{σ_j,r}) J e`), `finalRunF_amp` (the decoded
amplitude is `S† J† F_{b,d}(W_{0,r}) J e`), and their costs.
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk
  Step Augmented ChebyshevFilter Protocol Endpoint ChebyshevLinearSystem
open scoped InnerProduct

/-! ### The protocol with implemented runs -/

section Generic

variable {K E F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

/-- **The protocol with implemented runs**: the classical control of the released estimator
(`Estimator.algorithm`: `m = ⌈log₂ ⌈κ⌉⌉` stages, five candidates per stage, `n_j` fresh runs
per candidate, the thresholds and the clipping) with the implemented test runs `test j r`, and
the final leaf of at most `1000` fresh implemented final attempts `fin r`. -/
def implAlgorithm (κ ε : ℝ) (test : ℕ → ℝ → TestRun O F) (fin : ℝ → TestRun O E) :
    Protocol.Tree O F E :=
  Estimator.algorithm test (fun r => repeatLeaf (fin r) 1000) (reps κ ε) (stagesM κ) κ

end Generic

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-! ### The ideal runs of the finite-degree protocol -/

/-- **The ideal test run** of candidate `r` at stage `j` of the finite-degree protocol: the
`d^fin_j = d_{σ_j}(1/100) + 1` signed steps of the Chebyshev filter at `b(σ_j)` on the seed
`ψ ⊗ J e`, then the coefficient flag. -/
def testRunF (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) (j : ℕ) (r : ℝ) : TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n) where
  circuit := runPhys D Ub sv (TcF s κ ε) (sig (stageOf κ j)) r (dTestF s (stageOf κ j))
  seed := seedVec D (bLow (s : ℝ) (sig (stageOf κ j))) (TcF s κ ε) (dTestF s (stageOf κ j))
  seed_unit := seedVec_norm D (bLow_mem _ _) (testF_fits s κ ε j)
  flag := testFlag D (bLow (s : ℝ) (sig (stageOf κ j))) (TcF s κ ε) (dTestF s (stageOf κ j))
  flag_isometry := testFlag_isometry D (bLow_mem _ _) (testF_fits s κ ε j)

/-- **The ideal final attempt** at the estimate `r`: the `d^fin_fin = d_0(ε/1000) + 1` signed
steps at `σ = 0` with the filter at `b(1/κ)`, on the seed `ψ ⊗ J e`; its flag is the output
isometry `y ↦ E (ψ ⊗ J (S y))`. -/
def finalRunF (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε r : ℝ) : TestRun (physOracle D Ub (TcF s κ ε)) V0 where
  circuit := runPhys D Ub sv (TcF s κ ε) 0 r (dFinF s κ ε)
  seed := seedVec D (bLow (s : ℝ) (1 / κ)) (TcF s κ ε) (dFinF s κ ε)
  seed_unit := seedVec_norm D (bLow_mem _ _) (finalF_fits s κ ε)
  flag := finalOutput D (bLow (s : ℝ) (1 / κ)) (TcF s κ ε) (dFinF s κ ε)
  flag_isometry := finalOutput_isometry D (bLow_mem _ _) (finalF_fits s κ ε)

/-- **The finite-degree algorithm with exact gates**. -/
def algorithmF (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) : Protocol.Tree (physOracle D Ub (TcF s κ ε)) (PrivO n) V0 :=
  implAlgorithm κ ε (testRunF D Ub sv κ ε) (finalRunF D Ub sv κ ε)

/-! ### Semantics of the ideal runs -/

/-- The success vector of the ideal test is the Chebyshev-filtered seed
`F_{b,d}(W_{σ_j,r}) J e` of degree `d^fin_j`. -/
theorem testRunF_amp (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε : ℝ) (j : ℕ) (r : ℝ) (x : X) :
    amp (testRunF D Ub sv κ ε j r) x =
      filterOp (WwO D Ub sv (sig (stageOf κ j)) r x) (bLow (s : ℝ) (sig (stageOf κ j)))
        (dTestF s (stageOf κ j)) ((JwO D).toContinuousLinearMap eVec) := by
  unfold amp testRunF
  dsimp only
  rw [test_amplitude D Ub hUb sv (bLow_mem _ _) (testF_fits s κ ε j)]

/-- The decoded amplitude of the ideal final attempt is `S† J† F_{b,d}(W_{0,r}) J e` with the
final filter of degree `d^fin_fin`. -/
theorem finalRunF_amp (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    amp (finalRunF D Ub sv κ ε r) x =
      (solEmb†) (((JwO D).toContinuousLinearMap†)
        (filterOp (WwO D Ub sv 0 r x) (bLow (s : ℝ) (1 / κ)) (dFinF s κ ε)
          ((JwO D).toContinuousLinearMap eVec))) := by
  unfold amp finalRunF
  dsimp only
  rw [final_amplitude D Ub hUb sv (bLow_mem _ _) (finalF_fits s κ ε)]

/-- An ideal test makes `54 d^fin_j` matrix-oracle and `2 d^fin_j` source calls: its weighted
cost is `d^fin_j` times the cost of one signed step. -/
theorem testRunF_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ) (j : ℕ) (r : ℝ) (w : Lbl → ℕ) (c : ℕ)
    (hc : ∀ σ r d, (runPhys D Ub sv (TcF s κ ε) σ r d).cost w = d * c) :
    (testRunF D Ub sv κ ε j r).circuit.cost w = dTestF s (stageOf κ j) * c := by
  unfold testRunF
  exact hc _ _ _

/-- An ideal final attempt has weighted cost `d^fin_fin` times the cost of one signed step. -/
theorem finalRunF_cost (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε r : ℝ) (w : Lbl → ℕ) (c : ℕ)
    (hc : ∀ σ r d, (runPhys D Ub sv (TcF s κ ε) σ r d).cost w = d * c) :
    (finalRunF D Ub sv κ ε r).circuit.cost w = dFinF s κ ε * c := by
  unfold finalRunF
  exact hc _ _ _

end

end ChebyshevLinearSystemFinite
