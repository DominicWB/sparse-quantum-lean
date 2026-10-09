import ChebyshevLinearSystemFinite.Main

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# The allocation of the finite-gate budget

The manuscript's example allocation (after equation `qls:eq:bernoulli`): prepare the coefficient
state within Euclidean distance `η` and unprepare with its actual circuit adjoint; implement
every signed step within `ρ` in operator norm, so that telescoping bounds the contribution of
the `d^fin` signed steps by `d^fin ρ`; no extra matrix queries.

* `allocRun`: an implemented run of `d` signed steps: the released logical run
  (`ChebyshevLinearSystem.runLog`) compiled (`EncodedLabeledProgram.compile`) with implemented
  signed steps `st l` in place of the released `signedStepProg l`; the seed `E (S (J e))` and
  the flag `E ∘ S ∘ G` with one implemented coefficient preparation `S` (an isometry, for
  example `v ↦ ψ' ⊗ v` for a prepared coefficient state `ψ'`), unprepared by its adjoint, and
  the output isometry `G` (`G = 1` for tests, `G = J S_sol` for final attempts, `outJ`).
* `allocRun_approx`: if every implemented signed step is a known-gate approximation within `ρ`
  of the released signed step (`GateApprox`) and `‖S - ψ_{b,d} ⊗ ·‖ ≤ η`, the implemented run
  is within `d ρ + 2η` of the ideal run (`GateApprox.compile`: telescoping over the `d` signed
  steps; the seed and the flag within `η` each).
* `allocAlgorithm`: the finite-degree protocol with one implementation `st` of the signed
  steps, one coefficient preparation `St j` per stage and one `Sf` for the final attempts.
* `main_alloc`: Theorem `qls:thm:main` for `allocAlgorithm` under the explicit requirements
  `ρ ≤ ε/(10¹⁰ s^{3/2} κ³ log(1/ε))` and `η ≤ ε/(10⁷ s κ²)`, through `main`.
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk
  Step Augmented ChebyshevFilter Protocol Endpoint ChebyshevLinearSystem CounterFilter
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-! ### Implemented runs -/

/-- **An implemented Chebyshev run** of `d` signed steps at `(σ, r)`: the released logical run
compiled with implemented signed steps `st` (in place of `signedStepProg`), the seed
`E (S (J e))` prepared by an implemented coefficient preparation `S` (an isometry), and the flag
`E ∘ S ∘ G`, unpreparing with the adjoint of the same `S`, for an output isometry `G`. -/
def allocRun {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0) (T : ℕ)
    (st : SLbl T → MultiOracleCircuit.Program (physOracle D Ub T))
    (S : PrivO n →L[ℂ] Ctr T (PrivO n)) (hS : (S†) ∘L S = 1)
    (G : F →L[ℂ] PrivO n) (hG : (G†) ∘L G = 1) (σ r : ℝ) (d : ℕ) :
    TestRun (physOracle D Ub T) F where
  circuit := EncodedLabeledProgram.compile (E D T) (E_isometry D T) st (runLog D Ub sv T σ r d d)
  seed := E D T (S (JwO D eVec))
  seed_unit := by
    rw [Run.E_norm, S.norm_map_iff_adjoint_comp_self.mpr hS, LinearIsometry.norm_map,
      Run.norm_eVec]
  flag := E D T ∘L (S ∘L G)
  flag_isometry := NativeSparseAttenuation.isometry_comp _ _
    (NativeSparseAttenuation.isometry_comp _ _ hG hS) (E_isometry D T)

/-- **The allocation for one run**: implemented signed steps within `ρ` (known-gate
approximations of the released signed steps) and a coefficient preparation within `η` give an
implementation of the ideal run within `d ρ + 2η`. -/
theorem allocRun_approx {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (T : ℕ) (t : TestRun (physOracle D Ub T) F) (b σ r : ℝ) (d : ℕ)
    (G : F →L[ℂ] PrivO n) (hG : (G†) ∘L G = 1)
    (hcirc : t.circuit = runPhys D Ub sv T σ r d) (hseed : t.seed = seedVec D b T d)
    (hflag : t.flag = E D T ∘L (seedT b T d ∘L G))
    (st : SLbl T → MultiOracleCircuit.Program (physOracle D Ub T)) {ρ : ℝ}
    (hst : ∀ l, GateApprox (signedStepProg D Ub sv T l) (st l) ρ)
    (S : PrivO n →L[ℂ] Ctr T (PrivO n)) (hS : (S†) ∘L S = 1) {η : ℝ}
    (hSη : ‖S - seedT b T d‖ ≤ η) :
    RunApprox t (allocRun D Ub sv T st S hS G hG σ r d) (d * ρ + 2 * η) := by
  have hE1 := LabeledSimulationTransfer.isometry_norm_le_one (E D T) (E_isometry D T)
  have hG1 := LabeledSimulationTransfer.isometry_norm_le_one G hG
  have hη : 0 ≤ η := le_trans (norm_nonneg (S - seedT b T d)) hSη
  refine ⟨d * ρ, η, η, ?_, ?_, ?_, by linarith⟩
  · rw [hcirc]
    have h := GateApprox.compile (E D T) (E_isometry D T) (signedStepProg D Ub sv T) st hst
      (runLog D Ub sv T σ r d d)
    rwa [runLog_count] at h
  · rw [hseed]
    show ‖E D T (S (JwO D eVec)) - E D T (seedT b T d (JwO D eVec))‖ ≤ η
    set A : PrivO n →L[ℂ] Ctr T (PrivO n) := S - seedT b T d with hA
    have hAv : S (JwO D eVec) - seedT b T d (JwO D eVec) = A (JwO D eVec) := by
      rw [hA, sub_apply]
    rw [← map_sub, Run.E_norm, hAv]
    calc ‖A (JwO D eVec)‖ ≤ ‖A‖ * ‖JwO D eVec‖ := le_opNorm _ _
      _ = ‖A‖ := by rw [LinearIsometry.norm_map, Run.norm_eVec, mul_one]
      _ ≤ η := hSη
  · rw [hflag]
    show ‖E D T ∘L (S ∘L G) - E D T ∘L (seedT b T d ∘L G)‖ ≤ η
    rw [← comp_sub, ← sub_comp]
    calc ‖E D T ∘L ((S - seedT b T d) ∘L G)‖ ≤ ‖E D T‖ * (‖S - seedT b T d‖ * ‖G‖) :=
          (opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (η * 1) :=
          mul_le_mul hE1 (mul_le_mul hSη hG1 (norm_nonneg _) hη) (by positivity) zero_le_one
      _ = η := by ring

omit [DecidableEq n] in
/-- The output isometry of tests is the identity. -/
theorem one_isometry : ((1 : PrivO n →L[ℂ] PrivO n)†) ∘L (1 : PrivO n →L[ℂ] PrivO n) = 1 := by
  rw [WalkGap.adjoint_one']
  rfl

/-- The output isometry `J S_sol` of final attempts. -/
def outJ (D : NativeSparseBlockEncoding.Data X n Z s) : V0 →L[ℂ] PrivO n :=
  (JwO D).toContinuousLinearMap ∘L solEmb

theorem outJ_isometry (D : NativeSparseBlockEncoding.Data X n Z s) : ((outJ D)†) ∘L outJ D = 1 :=
  NativeSparseAttenuation.isometry_comp _ _ solEmb_isometry (LinearIsometry.adjoint_comp_self _)

/-- **An implemented test** of candidate `r` at stage `j` of the finite-degree protocol. -/
def allocTest (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) (st : SLbl (TcF s κ ε) → MultiOracleCircuit.Program (physOracle D Ub (TcF s κ ε)))
    (S : PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hS : (S†) ∘L S = 1) (j : ℕ) (r : ℝ) :
    TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n) :=
  allocRun D Ub sv (TcF s κ ε) st S hS 1 one_isometry (sig (stageOf κ j)) r
    (dTestF s (stageOf κ j))

/-- **An implemented final attempt** at the estimate `r` of the finite-degree protocol. -/
def allocFinal (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0) (sv : V0)
    (κ ε : ℝ) (st : SLbl (TcF s κ ε) → MultiOracleCircuit.Program (physOracle D Ub (TcF s κ ε)))
    (S : PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hS : (S†) ∘L S = 1) (r : ℝ) :
    TestRun (physOracle D Ub (TcF s κ ε)) V0 :=
  allocRun D Ub sv (TcF s κ ε) st S hS (outJ D) (outJ_isometry D) 0 r (dFinF s κ ε)

/-- The allocation for a test of the finite-degree protocol: within `d^fin_j ρ + 2η`. -/
theorem allocTest_approx (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ)
    (st : SLbl (TcF s κ ε) → MultiOracleCircuit.Program (physOracle D Ub (TcF s κ ε))) {ρ : ℝ}
    (hst : ∀ l, GateApprox (signedStepProg D Ub sv (TcF s κ ε) l) (st l) ρ)
    (S : PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hS : (S†) ∘L S = 1) {η : ℝ} (j : ℕ) (r : ℝ)
    (hSη : ‖S - seedT (bLow (s : ℝ) (sig (stageOf κ j))) (TcF s κ ε) (dTestF s (stageOf κ j))‖ ≤
      η) :
    RunApprox (testRunF D Ub sv κ ε j r) (allocTest D Ub sv κ ε st S hS j r)
      (dTestF s (stageOf κ j) * ρ + 2 * η) :=
  allocRun_approx D Ub sv (TcF s κ ε) (testRunF D Ub sv κ ε j r)
    (bLow (s : ℝ) (sig (stageOf κ j))) (sig (stageOf κ j)) r (dTestF s (stageOf κ j)) 1
    one_isometry (by unfold testRunF; rfl) (by unfold testRunF; rfl)
    (by unfold testRunF; exact ContinuousLinearMap.ext fun _ => rfl) st hst S hS hSη

/-- The allocation for a final attempt of the finite-degree protocol: within
`d^fin_fin ρ + 2η`. -/
theorem allocFinal_approx (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ)
    (st : SLbl (TcF s κ ε) → MultiOracleCircuit.Program (physOracle D Ub (TcF s κ ε))) {ρ : ℝ}
    (hst : ∀ l, GateApprox (signedStepProg D Ub sv (TcF s κ ε) l) (st l) ρ)
    (S : PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hS : (S†) ∘L S = 1) {η : ℝ} (r : ℝ)
    (hSη : ‖S - seedT (bLow (s : ℝ) (1 / κ)) (TcF s κ ε) (dFinF s κ ε)‖ ≤ η) :
    RunApprox (finalRunF D Ub sv κ ε r) (allocFinal D Ub sv κ ε st S hS r)
      (dFinF s κ ε * ρ + 2 * η) :=
  allocRun_approx D Ub sv (TcF s κ ε) (finalRunF D Ub sv κ ε r) (bLow (s : ℝ) (1 / κ)) 0 r
    (dFinF s κ ε) (outJ D) (outJ_isometry D) (by unfold finalRunF; rfl)
    (by unfold finalRunF; rfl)
    (by unfold finalRunF; exact ContinuousLinearMap.ext fun _ => rfl) st hst S hS hSη

/-- **The protocol with implemented signed steps and coefficient preparations**: one
implementation `st` of all signed steps, one coefficient preparation `St j` for the tests at
stage `j` and one `Sf` for the final attempts; the classical control is unchanged. -/
def allocAlgorithm (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (κ ε : ℝ)
    (st : SLbl (TcF s κ ε) → MultiOracleCircuit.Program (physOracle D Ub (TcF s κ ε)))
    (St : ℕ → PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hSt : ∀ j, ((St j)†) ∘L St j = 1)
    (Sf : PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hSf : (Sf†) ∘L Sf = 1) :
    Protocol.Tree (physOracle D Ub (TcF s κ ε)) (PrivO n) V0 :=
  implAlgorithm κ ε (fun j r => allocTest D Ub sv κ ε st (St (stageOf κ j)) (hSt _) j r)
    (allocFinal D Ub sv κ ε st Sf hSf)

/-! ### Explicit requirements -/

/-- The allocation arithmetic for tests: `ρ ≤ ε/(10¹⁰ s^{3/2} κ³ log(1/ε))` and
`η ≤ ε/(10⁷ s κ²)` give `d^fin_j ρ + 2η ≤ e_test` at every stage. -/
theorem alloc_test_arith (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) (j : ℕ) {ρ η : ℝ}
    (hρ : ρ ≤ ε / (10 ^ 10 * (s : ℝ) * Real.sqrt s * κ ^ 3 * Real.log (1 / ε)))
    (hη : η ≤ ε / (10 ^ 7 * (s : ℝ) * κ ^ 2)) :
    dTestF s (stageOf κ j) * ρ + 2 * η ≤ eTest s (stageOf κ j) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : 1 ≤ Real.sqrt (s : ℝ) := Real.one_le_sqrt.mpr hs1
  have hκ0 : 0 < κ := by linarith
  have hL := two_le_logInv ε hε hε1
  have hd : (dTestF s (stageOf κ j) : ℝ) ≤ 224 * (Real.sqrt s * κ) := by
    have h1 := (dTestF_lt s hs (stageOf κ j)).le
    have h2 := two_pow_stageOf_le κ hκ j
    calc (dTestF s (stageOf κ j) : ℝ) ≤ 112 * Real.sqrt s * 2 ^ stageOf κ j := h1
      _ ≤ 112 * Real.sqrt s * (2 * κ) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 224 * (Real.sqrt s * κ) := by ring
  have he := eTest_ge_uniform s hs κ hκ j
  generalize hdj : (dTestF s (stageOf κ j) : ℝ) = d at hd ⊢
  generalize heT : eTest s (stageOf κ j) = e at he ⊢
  generalize Real.log (1 / ε) = L at hL hρ
  have hQ : 0 < (s : ℝ) * κ ^ 2 := by positivity
  have hR : 1 ≤ Real.sqrt s * κ := by nlinarith
  have hρ' : ρ * (10 ^ 10 * (((s : ℝ) * κ ^ 2) * (Real.sqrt s * κ) * L)) ≤ ε := by
    rw [show (10 ^ 10 * (s : ℝ) * Real.sqrt s * κ ^ 3 * L) =
      10 ^ 10 * (((s : ℝ) * κ ^ 2) * (Real.sqrt s * κ) * L) by ring,
      le_div_iff₀ (by positivity)] at hρ
    exact hρ
  have hη' : η * (10 ^ 7 * ((s : ℝ) * κ ^ 2)) ≤ ε := by
    rw [show (10 ^ 7 * (s : ℝ) * κ ^ 2) = 10 ^ 7 * ((s : ℝ) * κ ^ 2) by ring,
      le_div_iff₀ (by positivity)] at hη
    exact hη
  have he' : 1 / 36000000 ≤ e * ((s : ℝ) * κ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right he hQ.le
    have e1 : 1 / (36 * 10 ^ 6 * (s : ℝ) * κ ^ 2) * ((s : ℝ) * κ ^ 2) = 1 / 36000000 := by
      field_simp
      norm_num
    linarith
  generalize (s : ℝ) * κ ^ 2 = Q at hQ hρ' hη' he'
  generalize Real.sqrt s * κ = R at hR hd hρ'
  have key : (d * ρ + 2 * η) * Q ≤ e * Q := by
    rcases le_or_gt ρ 0 with hρ0 | hρ0
    · have hd0 : 0 ≤ d := by rw [← hdj]; positivity
      have h1 : d * ρ * Q ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hd0 hρ0) hQ.le
      nlinarith
    · have h1 : d * ρ * Q ≤ 224 * R * ρ * Q := by
        have := mul_le_mul_of_nonneg_right hd (mul_nonneg hρ0.le hQ.le)
        nlinarith
      have h2 : 2 * (ρ * Q * R) ≤ ρ * Q * R * L := by
        have := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ ρ * Q * R)
        nlinarith
      nlinarith
  exact le_of_mul_le_mul_right key hQ

/-- The allocation arithmetic for final attempts: the same `ρ` and `η` give
`d^fin_fin ρ + 2η ≤ e_fin`. -/
theorem alloc_final_arith (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) {ρ η : ℝ}
    (hρ : ρ ≤ ε / (10 ^ 10 * (s : ℝ) * Real.sqrt s * κ ^ 3 * Real.log (1 / ε)))
    (hη : η ≤ ε / (10 ^ 7 * (s : ℝ) * κ ^ 2)) :
    dFinF s κ ε * ρ + 2 * η ≤ eFin s κ ε := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsq : 1 ≤ Real.sqrt (s : ℝ) := Real.one_le_sqrt.mpr hs1
  have hκ0 : 0 < κ := by linarith
  have hL := two_le_logInv ε hε hε1
  have hd : (dFinF s κ ε : ℝ) ≤ 168 * ((Real.sqrt s * κ) * Real.log (1 / ε)) := by
    have := dFinF_le s hs κ ε hκ hε hε1
    linarith
  have he := eFin_ge s hs κ ε hκ hε hε1
  generalize hdj : (dFinF s κ ε : ℝ) = d at hd ⊢
  generalize heT : eFin s κ ε = e at he ⊢
  generalize Real.log (1 / ε) = L at hL hρ hd
  have hQ : 0 < (s : ℝ) * κ ^ 2 := by positivity
  have hR : 1 ≤ Real.sqrt s * κ := by nlinarith
  have hρ' : ρ * (10 ^ 10 * (((s : ℝ) * κ ^ 2) * (Real.sqrt s * κ) * L)) ≤ ε := by
    rw [show (10 ^ 10 * (s : ℝ) * Real.sqrt s * κ ^ 3 * L) =
      10 ^ 10 * (((s : ℝ) * κ ^ 2) * (Real.sqrt s * κ) * L) by ring,
      le_div_iff₀ (by positivity)] at hρ
    exact hρ
  have hη' : η * (10 ^ 7 * ((s : ℝ) * κ ^ 2)) ≤ ε := by
    rw [show (10 ^ 7 * (s : ℝ) * κ ^ 2) = 10 ^ 7 * ((s : ℝ) * κ ^ 2) by ring,
      le_div_iff₀ (by positivity)] at hη
    exact hη
  have he' : ε / 900000 ≤ e * ((s : ℝ) * κ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right he hQ.le
    have e1 : ε / (9 * 10 ^ 5 * (s : ℝ) * κ ^ 2) * ((s : ℝ) * κ ^ 2) = ε / 900000 := by
      field_simp
      norm_num
    linarith
  generalize (s : ℝ) * κ ^ 2 = Q at hQ hρ' hη' he'
  generalize Real.sqrt s * κ = R at hR hd hρ'
  have key : (d * ρ + 2 * η) * Q ≤ e * Q := by
    rcases le_or_gt ρ 0 with hρ0 | hρ0
    · have hd0 : 0 ≤ d := by rw [← hdj]; positivity
      have h1 : d * ρ * Q ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hd0 hρ0) hQ.le
      nlinarith
    · have h1 : d * ρ * Q ≤ 168 * (ρ * Q * R * L) := by
        have := mul_le_mul_of_nonneg_right hd (mul_nonneg hρ0.le hQ.le)
        nlinarith
      nlinarith
  exact le_of_mul_le_mul_right key hQ

/-- **Theorem `qls:thm:main` with the manuscript's allocation of the finite-gate budget**: one
implementation `st` of the signed steps, each a known-gate approximation within
`ρ ≤ ε/(10¹⁰ s^{3/2} κ³ log(1/ε))` of the released signed step (same oracle calls), and
coefficient preparations `St j` (tests at stage `j`) and `Sf` (final attempts), each an isometry
within `η ≤ ε/(10⁷ s κ²)` of the ideal coefficient seed and unprepared by its adjoint. Then the
conclusions of `main` hold for `allocAlgorithm`. -/
theorem main_alloc (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (st : SLbl (TcF s κ ε) → MultiOracleCircuit.Program (physOracle D Ub (TcF s κ ε))) {ρ : ℝ}
    (hst : ∀ l, GateApprox (signedStepProg D Ub sv (TcF s κ ε) l) (st l) ρ)
    (hρ : ρ ≤ ε / (10 ^ 10 * (s : ℝ) * Real.sqrt s * κ ^ 3 * Real.log (1 / ε)))
    (St : ℕ → PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hSt : ∀ j, ((St j)†) ∘L St j = 1)
    (Sf : PrivO n →L[ℂ] Ctr (TcF s κ ε) (PrivO n)) (hSf : (Sf†) ∘L Sf = 1) {η : ℝ}
    (hη : η ≤ ε / (10 ^ 7 * (s : ℝ) * κ ^ 2))
    (hStη : ∀ j, j ≤ stagesM κ →
      ‖St j - seedT (bLow (s : ℝ) (sig j)) (TcF s κ ε) (dTestF s j)‖ ≤ η)
    (hSfη : ‖Sf - seedT (bLow (s : ℝ) (1 / κ)) (TcF s κ ε) (dFinF s κ ε)‖ ≤ η) :
    ((allocAlgorithm D Ub sv κ ε st St hSt Sf hSf).worstCost wMat : ℝ) ≤
        27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((allocAlgorithm D Ub sv κ ε st St hSt Sf hSf).worstCost wSrc : ℝ) ≤
        10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (allocAlgorithm D Ub sv κ ε st St hSt Sf hSf).RunsUnitary x ∧
        2 / 3 ≤ (allocAlgorithm D Ub sv κ ε st St hSt Sf hSf).successMass x ∧
        ODEMixedOutput.IsDensity
          ((allocAlgorithm D Ub sv κ ε st St hSt Sf hSf).conditionalDensity x) ∧
        ∃ h : ((allocAlgorithm D Ub sv κ ε st St hSt Sf hSf).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance
            ((allocAlgorithm D Ub sv κ ε st St hSt Sf hSf).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  main D Ub hUb sv hsv κ ε hκ hε hε1 _ _
    (fun j r => (allocTest_approx D Ub sv κ ε st hst (St (stageOf κ j)) (hSt _) j r
      (hStη _ (stageOf_le κ j))).mono (alloc_test_arith s D.slots_pos κ ε hκ hε hε1 j hρ hη))
    (fun r => (allocFinal_approx D Ub sv κ ε st hst Sf hSf r hSfη).mono
      (alloc_final_arith s D.slots_pos κ ε hκ hε hε1 hρ hη))

end

end ChebyshevLinearSystemFinite
