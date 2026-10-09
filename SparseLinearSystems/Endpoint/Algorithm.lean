import SparseLinearSystems.Circuit.Facts
import SparseLinearSystems.Protocol.Estimator
import SparseLinearSystems.Protocol.Leaf
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The complete algorithm of Theorem `qls:thm:main`

All parameters are public: they depend on the sparsity `s`, the condition
bound `κ` and the accuracy `ε` only.

* `stagesM κ = ⌈log₂ ⌈κ⌉⌉` estimation stages, `σ_j = 2^{-j}`;
* test filters `f_{N_j}(W)` with `N_j = ⌈100 / b(σ_j)⌉` (`T_j = N_j - 1` walk
  steps), `n_j = ⌈4 log(2/ζ_j)/t²⌉` fresh runs per candidate with
  `ζ_j = (ε/5000) 2^{-(m-j)}`;
* the final filter `f_{N}(W)^k` at `σ = 0`, `N = ⌈100 / b(1/κ)⌉`,
  `k = ⌈log₁₀₀ ⌈1000/ε⌉⌉`, and `1000` fresh attempts;
* one counter register of `T + 1` values, `T = T_fin + Σ_{j ≤ m} T_j`.

`testRun j r` is one fresh test of candidate `r` at stage `j`; `finalLeaf r`
is the final repeat at the estimate `r`; `algorithm` is the complete adaptive
protocol over the physical oracle family (native sparse primitives and the
controlled source preparation).
-/

namespace SparseLinearSystems.Endpoint

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
  Cells Step Run Facts Protocol
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-! ### Public parameters -/

/-- The number of estimation stages `m = ⌈log₂ κ⌉`. -/
def stagesM (κ : ℝ) : ℕ := Nat.clog 2 ⌈κ⌉₊

/-- `σ_j = 2^{-j}`. -/
def sig (j : ℕ) : ℝ := (1 / 2) ^ j

theorem sig_nonneg (j : ℕ) : 0 ≤ sig j := by unfold sig; positivity

theorem sig_pos (j : ℕ) : 0 < sig j := by unfold sig; positivity

theorem sig_le_one (j : ℕ) : sig j ≤ 1 := by
  unfold sig
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem sig_succ (j : ℕ) : sig (j + 1) = sig j / 2 := by
  unfold sig
  rw [pow_succ]
  ring

/-- Test filter length `N_j = ⌈100 / b(σ_j)⌉` (at least one). -/
def Ntest (s : ℕ) (j : ℕ) : ℕ := max 1 ⌈100 / bLow (s : ℝ) (sig j)⌉₊

/-- Test walk steps `T_j = N_j - 1`. -/
def Ttest (s : ℕ) (j : ℕ) : ℕ := Ntest s j - 1

/-- Per-test failure budget `ζ_j = (ε/5000) 2^{-(m-j)}`. -/
def zeta (κ ε : ℝ) (j : ℕ) : ℝ := ε / 5000 * (1 / 2) ^ (stagesM κ - j)

/-- Fresh runs per candidate, `n_j = ⌈4 log(2/ζ_j)/t²⌉`. -/
def reps (κ ε : ℝ) (j : ℕ) : ℕ := ⌈4 * Real.log (2 / zeta κ ε j) / Estimator.tAcc ^ 2⌉₊

/-- Final filter length `N = ⌈100 / b(1/κ)⌉` (at least one). -/
def Nfin (s : ℕ) (κ : ℝ) : ℕ := max 1 ⌈100 / bLow (s : ℝ) (1 / κ)⌉₊

/-- Final filter power `k = ⌈log₁₀₀ ⌈1000/ε⌉⌉`. -/
def kfin (ε : ℝ) : ℕ := Nat.clog 100 ⌈1000 / ε⌉₊

/-- Final walk steps `k (N - 1)`. -/
def Tfin (s : ℕ) (κ ε : ℝ) : ℕ := kfin ε * (Nfin s κ - 1)

/-- The counter register size. -/
def Tw (s : ℕ) (κ ε : ℝ) : ℕ := Tfin s κ ε + ∑ j ∈ Finset.range (stagesM κ + 1), Ttest s j

/-- Stage indices are clamped to `[0, m]`; only `1, …, m` are ever used. -/
def stageOf (κ : ℝ) (j : ℕ) : ℕ := min j (stagesM κ)

theorem stageOf_le (κ : ℝ) (j : ℕ) : stageOf κ j ≤ stagesM κ := min_le_right _ _

theorem stageOf_of_le (κ : ℝ) (j : ℕ) (h : j ≤ stagesM κ) : stageOf κ j = j := min_eq_left h

theorem Ntest_pos (s : ℕ) (j : ℕ) : 0 < Ntest s j := lt_max_of_lt_left one_pos

theorem Ntest_spec (s : ℕ) (hs : 0 < s) (j : ℕ) : 100 ≤ (Ntest s j : ℝ) * bLow (s : ℝ) (sig j) := by
  have hb := bLow_pos (s : ℝ) (sig j) (by exact_mod_cast hs) (sig_pos j)
  have h1 := Nat.le_ceil (100 / bLow (s : ℝ) (sig j))
  have h2 : (⌈100 / bLow (s : ℝ) (sig j)⌉₊ : ℝ) ≤ Ntest s j := by
    exact_mod_cast le_max_right _ _
  rw [div_le_iff₀ hb] at h1
  nlinarith

theorem Nfin_pos (s : ℕ) (κ : ℝ) : 0 < Nfin s κ := lt_max_of_lt_left one_pos

theorem Nfin_spec (s : ℕ) (hs : 0 < s) (κ : ℝ) (hκ : 1 ≤ κ) :
    100 ≤ (Nfin s κ : ℝ) * bLow (s : ℝ) (1 / κ) := by
  have hb := bLow_pos (s : ℝ) (1 / κ) (by exact_mod_cast hs) (by positivity)
  have h1 := Nat.le_ceil (100 / bLow (s : ℝ) (1 / κ))
  have h2 : (⌈100 / bLow (s : ℝ) (1 / κ)⌉₊ : ℝ) ≤ Nfin s κ := by
    exact_mod_cast le_max_right _ _
  rw [div_le_iff₀ hb] at h1
  nlinarith

theorem Ttest_le_Tw (s : ℕ) (κ ε : ℝ) (j : ℕ) (hj : j ≤ stagesM κ) : Ttest s j ≤ Tw s κ ε := by
  unfold Tw
  have := Finset.single_le_sum (f := fun j => Ttest s j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (show j < stagesM κ + 1 by omega))
  omega

theorem Tfin_le_Tw (s : ℕ) (κ ε : ℝ) : Tfin s κ ε ≤ Tw s κ ε := Nat.le_add_right _ _

theorem test_degree (s : ℕ) (j : ℕ) : 1 * (Ntest s j - 1) ≤ Ttest s j := by
  unfold Ttest; omega

theorem final_degree (s : ℕ) (κ ε : ℝ) : kfin ε * (Nfin s κ - 1) ≤ Tfin s κ ε := le_rfl

theorem kappa_le_pow (κ : ℝ) : κ ≤ 2 ^ stagesM κ := by
  have h1 := Nat.le_ceil κ
  have h2 := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈κ⌉₊
  calc κ ≤ ⌈κ⌉₊ := h1
    _ ≤ ((2 ^ stagesM κ : ℕ) : ℝ) := by exact_mod_cast h2
    _ = 2 ^ stagesM κ := by push_cast; rfl

theorem sig_stages_le (κ : ℝ) (hκ : 1 ≤ κ) : sig (stagesM κ) ≤ 1 / κ := by
  have h := kappa_le_pow κ
  have hκ0 : 0 < κ := by linarith
  unfold sig
  rw [one_div_pow, one_div_le_one_div (by positivity) hκ0]
  exact h

theorem zeta_pos (κ ε : ℝ) (hε : 0 < ε) (j : ℕ) : 0 < zeta κ ε j := by
  unfold zeta; positivity

theorem reps_spec (κ ε : ℝ) (j : ℕ) :
    4 * Real.log (2 / zeta κ ε j) / Estimator.tAcc ^ 2 ≤ reps κ ε j :=
  Nat.le_ceil _

/-- The total failure budget `Σ_j 5 ζ_j ≤ ε / 500`. -/
theorem sum_zeta_le (κ ε : ℝ) (hε : 0 < ε) :
    ∑ q ∈ Finset.range (stagesM κ), 5 * zeta κ ε (stagesM κ - q) ≤ ε / 500 := by
  have h : ∀ q ∈ Finset.range (stagesM κ), 5 * zeta κ ε (stagesM κ - q) =
      ε / 1000 * (1 / 2) ^ q := by
    intro q hq
    have hq' : q ≤ stagesM κ := (Finset.mem_range.mp hq).le
    unfold zeta
    rw [show stagesM κ - (stagesM κ - q) = q by omega]
    ring
  rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
  have hgeo : ∑ q ∈ Finset.range (stagesM κ), (1 / 2 : ℝ) ^ q ≤ 2 :=
    sum_geometric_two_le _
  have : ε / 1000 * ∑ q ∈ Finset.range (stagesM κ), (1 / 2 : ℝ) ^ q ≤ ε / 1000 * 2 :=
    mul_le_mul_of_nonneg_left hgeo (by positivity)
  linarith

/-- The final filter error `100^{-k} ≤ ε / 1000`. -/
theorem kfin_spec (ε : ℝ) (hε : 0 < ε) : (1 / 100 : ℝ) ^ kfin ε ≤ ε / 1000 := by
  have h1 := Nat.le_ceil (1000 / ε)
  have h2 := Nat.le_pow_clog (by norm_num : 1 < 100) ⌈1000 / ε⌉₊
  have h3 : 1000 / ε ≤ (100 : ℝ) ^ kfin ε := by
    calc 1000 / ε ≤ ⌈1000 / ε⌉₊ := h1
      _ ≤ (((100 ^ kfin ε : ℕ)) : ℝ) := by exact_mod_cast h2
      _ = (100 : ℝ) ^ kfin ε := by push_cast; rfl
  rw [one_div_pow]
  rw [div_le_iff₀ hε] at h3
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-! ### The algorithm -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

theorem test_fits (s : ℕ) (κ ε : ℝ) (j : ℕ) :
    1 * (Ntest s (stageOf κ j) - 1) ≤ Tw s κ ε :=
  (test_degree s _).trans (Ttest_le_Tw s κ ε _ (stageOf_le κ j))

theorem final_fits (s : ℕ) (κ ε : ℝ) : kfin ε * (Nfin s κ - 1) ≤ Tw s κ ε :=
  (final_degree s κ ε).trans (Tfin_le_Tw s κ ε)

/-- **One fresh test** of candidate `r` at stage `j`: `T_j` counter-controlled
walk steps on the seed `ψ ⊗ J e`, then the counter flag. -/
def testRun (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) (j : ℕ) (r : ℝ) : TestRun (physOracle D Ub (Tw s κ ε)) (PrivO n) where
  circuit := runPhys D Ub sv (Tw s κ ε) (sig (stageOf κ j)) r (Ttest s (stageOf κ j))
  seed := seedVec D (Ntest s (stageOf κ j)) 1 (Tw s κ ε)
  seed_unit := seedVec_norm D _ 1 _ (Ntest_pos s _) (test_fits s κ ε j)
  flag := testFlag D (Ntest s (stageOf κ j)) 1 (Tw s κ ε)
  flag_isometry := testFlag_isometry D _ 1 _ (Ntest_pos s _) (test_fits s κ ε j)

/-- The final circuit at estimate `r`: `k (N - 1)` walk steps at `σ = 0`. -/
def finalCircuit (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε r : ℝ) : MultiOracleCircuit.Program (physOracle D Ub (Tw s κ ε)) :=
  runPhys D Ub sv (Tw s κ ε) 0 r (Tfin s κ ε)

/-- **The final leaf**: at most `1000` fresh attempts, stopping at the first
heralded success; the output register holds the solution coordinates. -/
def finalLeaf (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) (r : ℝ) : ODERepeatProtocol.Protocol (physOracle D Ub (Tw s κ ε)) V0 :=
  ODERepeatProtocol.Protocol.repeatTrials
    (single (finalCircuit D Ub sv κ ε r) (seedVec D (Nfin s κ) (kfin ε) (Tw s κ ε))
      (seedVec_norm D _ _ _ (Nfin_pos s κ) (final_fits s κ ε))
      (finalOutput D (Nfin s κ) (kfin ε) (Tw s κ ε))
      (finalOutput_isometry D _ _ _ (Nfin_pos s κ) (final_fits s κ ε))) 1000

/-- **The complete algorithm of Theorem `qls:thm:main`.** -/
def algorithm (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) : Tree (physOracle D Ub (Tw s κ ε)) (PrivO n) V0 :=
  Estimator.algorithm (testRun D Ub sv κ ε) (finalLeaf D Ub sv κ ε) (reps κ ε) (stagesM κ) κ

/-! ### Semantics of the runs -/

theorem testRun_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε : ℝ) (j : ℕ) (r : ℝ) (x : X) :
    IsUnitary ((testRun D Ub sv κ ε j r).circuit.eval x) :=
  runPhys_unitary D Ub hUb sv _ _ _ _ x

theorem testRun_probability (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε : ℝ) (j : ℕ) (r : ℝ) (x : X) :
    (testRun D Ub sv κ ε j r).probability x =
      ‖UnitaryFilter.filter (WwO D Ub sv (sig (stageOf κ j)) r x) (Ntest s (stageOf κ j)) 1
        ((JwO D).toContinuousLinearMap eVec)‖ ^ 2 := by
  show ‖((testFlag D (Ntest s (stageOf κ j)) 1 (Tw s κ ε))†)
    ((runPhys D Ub sv (Tw s κ ε) (sig (stageOf κ j)) r (Ttest s (stageOf κ j))).eval x
      (seedVec D (Ntest s (stageOf κ j)) 1 (Tw s κ ε)))‖ ^ 2 = _
  rw [test_amplitudeO D Ub hUb sv _ 1 _ _ (test_degree s _) (Ttest_le_Tw s κ ε _ (stageOf_le κ j)),
    LinearIsometry.coe_toContinuousLinearMap]

theorem finalCircuit_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (Ub : X → V0 →L[ℂ] V0) (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    IsUnitary ((finalCircuit D Ub sv κ ε r).eval x) :=
  runPhys_unitary D Ub hUb sv _ _ _ _ x

/-- The decoded amplitude of one final attempt. -/
theorem final_amp (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    ((finalOutput D (Nfin s κ) (kfin ε) (Tw s κ ε))†)
        ((finalCircuit D Ub sv κ ε r).eval x (seedVec D (Nfin s κ) (kfin ε) (Tw s κ ε))) =
      (solEmb†) (((JwO D).toContinuousLinearMap†)
        (UnitaryFilter.filter (WwO D Ub sv 0 r x) (Nfin s κ) (kfin ε)
          ((JwO D).toContinuousLinearMap eVec))) := by
  rw [finalCircuit, final_amplitudeO D Ub hUb sv _ _ _ _ (final_degree s κ ε) (Tfin_le_Tw s κ ε),
    LinearIsometry.coe_toContinuousLinearMap]

/-! ### The final leaf -/

/-- The decoded amplitude of one final attempt. -/
def finalAmp (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε r : ℝ) (x : X) : V0 :=
  ((finalOutput D (Nfin s κ) (kfin ε) (Tw s κ ε))†)
    ((finalCircuit D Ub sv κ ε r).eval x (seedVec D (Nfin s κ) (kfin ε) (Tw s κ ε)))

theorem finalAmp_eq (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (κ ε r : ℝ) (x : X) :
    finalAmp D Ub sv κ ε r x =
      (solEmb†) (((JwO D).toContinuousLinearMap†)
        (UnitaryFilter.filter (WwO D Ub sv 0 r x) (Nfin s κ) (kfin ε)
          ((JwO D).toContinuousLinearMap eVec))) :=
  final_amp D Ub hUb sv κ ε r x

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
  ((single (finalCircuit D Ub sv κ ε r) (seedVec D (Nfin s κ) (kfin ε) (Tw s κ ε))
      (seedVec_norm D _ _ _ (Nfin_pos s κ) (final_fits s κ ε))
      (finalOutput D (Nfin s κ) (kfin ε) (Tw s κ ε))
      (finalOutput_isometry D _ _ _ (Nfin_pos s κ) (final_fits s κ ε))).probability_bounds x
    (fun _ => finalCircuit_unitary D Ub hUb sv κ ε r x) ⟨0, Nat.one_pos⟩).2

end

end SparseLinearSystems.Endpoint
