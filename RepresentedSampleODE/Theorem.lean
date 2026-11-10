import RepresentedSampleODE.Target

/-!
# `ode:thm:time` on a mesh with represented samples of any sign

`GeneralSourceExtensions.Mesh.mesh_propagated_solver` requires every represented sample to have a
positive semidefinite dissipative part (hypothesis `hPSD`): the Gaussian LCHS table is applied to
the product family of the represented samples, which must be contractive on the lower half-plane.
The manuscript (proof of `ode:thm:time`, eq. `ode:eq:timedisc` and the paragraph after it) instead
asks the represented branches
only for the moment and norm promises and certified approximation errors. This file removes the
positivity requirement:

* the public SELECT program and the public Gaussian table are those of the released solver;
* for an instance with negativity bounds `κ_r` (`Re ⟨w, G̃_r w⟩ ≥ -κ_r ‖w‖²`) the table is applied
  to the *repaired* family (`robustFamily`), which is contractive, and the represented SELECT
  branches differ from the repaired branches at the public nodes `|k| ≤ R` by at most
  `2 R (Λ_κ + ΔR)` (`tableFamily_sub_robustFamily`);
* the repaired target is within `(ΔG + 2 Λ_κ + 2 ΔR) B_q` of the propagated source sum
  (`robust_target_error`).

`robust_propagated_solver` is the released solver for every instance satisfying `RobustBudget`:
`ζ + c_q (ΔG + 2 Λ_κ + 2 ΔR) ≤ ε / (2000 ḡ)` and `6 R (Λ_κ + ΔR) ≤ ν`. For positive samples one
may take `κ = 0`; the budgets are then the released one with the rounding term doubled and
`6 R ΔR ≤ ν` (both void when `ΔR = 0`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions SparseHamiltonian.GeneralSourceExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients retarget)
open SparseHamiltonian.GeneralSourceODE (startTime sources phases phases_norm mass_sources
  phased_isometry phased_prepares nodeTable)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale sampleError refinementError
  meshDurations meshDurations_nonneg meshDurations_le meshTable tableFamily IsMeshPropagator
  sampleError_nonneg refinementError_nonneg meshScale_nonneg branchEvolution_eq_tableFamily)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- **The budget of an instance with represented samples of any sign.** Negativity bounds
`κ_r ≥ 0` of the represented samples, `Re ⟨w, G̃_r w⟩ ≥ -κ_r ‖w‖²`, with negativity mass
`Λ_κ = ∑_r (t_{r+1} - t_r) κ_r`, the target budget `ζ + c_q (ΔG + 2 Λ_κ + 2 ΔR) ≤ ε / (2000 ḡ)`
and the branch budget `6 R (Λ_κ + ΔR) ≤ ν` at the LCHS frequency radius `R` and precision `ν`.
For positive semidefinite samples one may take `κ = 0`, so `Λ_κ = 0`. -/
def RobustBudget (D : Data (X × Fin M) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (T : ℝ) (N : ℕ)
    (cq gbar ε ζ : ℝ) : Prop :=
  ∃ κ : Fin M → ℝ, (∀ r, 0 ≤ κ r) ∧
    (∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re) ∧
    ζ + cq * (sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N) ≤
      ε / (2000 * gbar) ∧
    6 * radius (cq * gbar) ε * (negativity t κ + refinementError D t T N) ≤
      precision (cq * gbar) ε

/-- **One public trial family on a mesh** (two counted source interfaces), chosen before every
unknown instance, as `GeneralSourceExtensions.Mesh.MeshPropagatedOutcome` with the budget
`RobustBudget` in place of the positivity of the represented dissipative parts and the budget
`ζ + c_q (ΔG + ΔR) ≤ ε / (2000 ḡ)`, and without the classical piecewise solution (`SolvesODE`),
which the proof does not use: only `x(0)`, `x(T)` and the certificate in terms of them enter. -/
def RobustPropagatedOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T (cq * gbar) ε) n Z m M N d)
    (_hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J (phases ω))),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget D x t G T N cq gbar ε ζ →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input D hM (Sum.inr false) m N d
          (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients D T (cq * gbar) ε)) seed))
        (MeshNative.input D hM (Sum.inr false) m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε


set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, represented samples of
any sign** (two counted source interfaces). Under uniform sparse energy bounds `η_H`, `η_D`, the
slot conditions `8 s ρ T ≤ N` and `3 (√(2s) ρ T)³ ≤ ν N²` at the
amplification ratio `2 c_q ḡ`, and public nodes in `[0, T]`, one public trial family satisfies the
released complete certificate for every instance whose pieces are accretive and
interval-integrable, whose propagator is `U`, whose supplied weight and loading oracles prepare the
source weights and directions, whose coefficient mass is at most `c_q B`, whose propagated source
sum is within `ζ B` of the solution, whose solution is nonzero with `B ≤ ḡ ‖x(T)‖`, and which
satisfies `RobustBudget` (negativity bounds `κ` of its represented samples with
`ζ + c_q (ΔG + 2 Λ_κ + 2 ΔR) ≤ ε / (2000 ḡ)` and `6 R (Λ_κ + ΔR) ≤ ν`). No positivity of the
represented dissipative parts is assumed: the analysis runs on their positive repairs. -/
theorem robust_propagated_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RobustPropagatedOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed := by
  set g : ℝ := cq * gbar with hgdef
  have hg1 : 1 ≤ g := by nlinarith
  have hg' : 1 ≤ ratio g := by unfold ratio; linarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
  have hε'Half : accuracy ε ≤ 1 / 2 := by unfold accuracy; linarith
  have hν : 0 < precision g ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  have hνOne : precision g ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth _ _ hg' hε'One).trans
      (by norm_num)
  have hR : 0 ≤ radius g ε := ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
  let σ : ℕ → Fin M := pieceOf t T N hM
  have hu0 : ∀ a r, 0 ≤ meshDurations t T v a r := meshDurations_nonneg hmesh hT.le v
  have huT : ∀ a r, meshDurations t T v a r ≤ T := meshDurations_le hmesh hT.le v
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, hNodes, hMass, -⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun _ : Unit => fun _ : ℂ => (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (fun _ _ => analyticAt_const) (fun _ _ _ => norm_one_op_le)
    (lipschitz D T) hL (fun _ k l => by
      rw [sub_self, norm_zero]
      exact mul_nonneg hL (abs_nonneg _))
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- One public SELECT program on `N` slots for the public node and duration tables.
  let i0 : Index D T g ε := Sum.inr false
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    MeshSelect.select (ι := GeneralSourceODE.Native.Label (Index D T g ε) m) D hM σ hN
      (GeneralSourceODE.Native.dummy hM i0 m) etaH etaD (radius g ε) T (precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD hClock hCayley
  have hk : ∀ a, |nodeTable D T g ε m a| ≤ radius g ε := fun a =>
    ODECoefficientPadding.paddedNodes_bound _ _ hR hNodes a.2
  have hu : ∀ (a : GeneralSourceODE.Native.Label (Index D T g ε) m) (r : Fin M),
      0 ≤ meshTable t T v a r := fun a r => hu0 a.1 r
  have huT' : ∀ (a : GeneralSourceODE.Native.Label (Index D T g ε) m) (r : Fin M),
      meshTable t T v a r ≤ T := fun a r => huT a.1 r
  obtain ⟨p, hCount, hE, hAct⟩ := hTables (nodeTable D T g ε m) (meshTable t T v) hk hu huT'
  let d := TimeDependentODE.Select.degree (s : ℝ) γ (etaH + radius g ε * etaD) T
    (precision g ε) N
  let E : GeneralSourceODE.Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T g ε) n Z m M N d :=
    MeshSelect.alignedInput D hM σ (GeneralSourceODE.Native.dummy hM i0 m) N γ
      (etaH + radius g ε * etaD) T (precision g ε)
  have hEiso : E† ∘L E = 1 := hE
  let pN : MultiOracleCircuit.Program
      (MeshNative.matrixOracle (ι := Index D T g ε) D m N d) := p
  let c := lchsCoefficients D T g ε
  have hcpos : 0 < ODECoherentLCU.coefficientMass c := by
    change 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε)
    rw [hc]
    norm_num
  have hsc : 0 < ODECoherentLCU.coefficientMass
      (GeneralSourceODE.Compiled.seedCoefficients (N := m) c) := by
    rw [GeneralSourceODE.Compiled.seedCoefficients_mass]
    exact hcpos
  have hSeedUnit := ODECompiledSource.seed_unit E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc seed hSeed
  have hOutput := ODECompiledSource.output_isometry E
    (GeneralSourceODE.Compiled.seedCoefficients c) hEiso hsc
  let q := MeshNative.publicTrials D hM i0 m N d pN Pw J (phases ω) E hEiso c seed
    hSeedUnit hOutput
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) :=
    ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T (ratio g) (accuracy ε)
      (Nat.cast_nonneg s) hH hDiss hT.le hg' hε' hε'One hCount
  have hOracle := MeshNative.physicalOracle_unitary (ι := Index D T g ε) D m N d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  refine ⟨d, E, hEiso, q, fun j y => (q j).eval_unitary hOracle y, ?_⟩
  intro x G b sol bv U ζ hG hGint hU hW hLoad₀ hLoad hMassB hCert hTarget hB hRobust
  obtain ⟨κ, hκ, hneg, hBudget, hBranch⟩ := hRobust
  -- The repaired target.
  let z := sources (sol 0) bv ω
  let y := robustTarget D hM t T N v x κ (sol 0) bv ω
  set Bs := meshScale sol b t with hBs
  have hTargetErr := robust_target_error D hM x κ hκ hneg hmesh hT.le hN G hG hGint U hU v hv ω
    (sol 0) bv
  set K : ℝ := sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N with hK
  have hK0 : 0 ≤ K := by
    have h1 := sampleError_nonneg D x hmesh G
    have h2 := negativity_nonneg hmesh hκ
    have h3 := refinementError_nonneg D t T N
    rw [hK]
    linarith
  have hBs0 : 0 ≤ Bs := meshScale_nonneg hmesh sol b
  have hErr : ‖sol T - y‖ ≤ (ζ + cq * K) * Bs := by
    have hsplit : sol T - y =
        (sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T) +
          ((U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y) := by
      abel
    rw [hsplit]
    have hMassK : K * ODESourceBranches.mass z ≤ cq * K * Bs := by
      calc
        K * ODESourceBranches.mass z ≤ K * (cq * Bs) := mul_le_mul_of_nonneg_left hMassB hK0
        _ = cq * K * Bs := by ring
    calc
      _ ≤ ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ := norm_add_le _ _
      _ ≤ ζ * Bs + K * ODESourceBranches.mass z := add_le_add hCert hTargetErr
      _ ≤ ζ * Bs + cq * K * Bs := add_le_add le_rfl hMassK
      _ = (ζ + cq * K) * Bs := by ring
  have hErrBudget : (ζ + cq * K) * Bs ≤ ε * Bs / (2000 * gbar) := by
    have h := mul_le_mul_of_nonneg_right hBudget hBs0
    calc
      (ζ + cq * K) * Bs ≤ ε / (2000 * gbar) * Bs := h
      _ = ε * Bs / (2000 * gbar) := by ring
  obtain ⟨hy, hBy, hDir⟩ := TimeDependentODE.Sampling.target_budget (sol T) y Bs gbar ε _ hg
    hε hεOne hTarget hB hErr hErrBudget
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    robustTarget_norm_le D hM hmesh hT.le N v x κ hκ hneg (sol 0) bv ω
  have hz : 0 < ODESourceBranches.mass z := ODESourceBranches.mass_pos_of_solution z y hy hNorm
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    have hcq0 : 0 ≤ cq := by linarith
    calc
      ODESourceBranches.mass z ≤ cq * Bs := hMassB
      _ ≤ cq * (2 * gbar * ‖y‖) := mul_le_mul_of_nonneg_left hBy hcq0
      _ = ratio g * ‖y‖ := by rw [hgdef]; unfold ratio; ring
  -- Hypotheses of the released actual-source certificate.
  have hJph : ∀ a, (GeneralSourceODE.Compiled.phased (J x) (phases ω) a)† ∘L
      GeneralSourceODE.Compiled.phased (J x) (phases ω) a = 1 :=
    phased_isometry (J x) (hJ x) ω
  have hPrep := phased_prepares (J x) (sol 0) bv ω seed hLoad₀ hLoad
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin m) × Index D T g ε =>
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) :=
    (hAct x).2
  -- The Gaussian table on the repaired family of this instance.
  obtain ⟨-, -, -, hApproxR⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun a' : Option (Fin m) => robustFamily D σ N (meshDurations t T v) x κ a')
    (fun a' z' => robustFamily_analyticAt D σ N _ x κ a' z')
    (fun a' z' hz => robustFamily_norm_le_one D σ N _ hu0 x κ hκ hneg a' z' hz)
    (lipschitz D T) hL (fun a' k l => robustFamily_lipschitz D σ hN _ hu0 huT x κ hκ a' k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  -- The represented SELECT branches as the Gaussian table sum of the represented family.
  have hsum : ∀ a', (∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) =
        ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
            (accuracy ε) j •
          tableFamily D σ N (meshDurations t T v) x a'
            (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
              ℂ) := by
    intro a'
    have hbr : ∀ i, MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
        (meshTable t T v) x (a', i) =
          tableFamily D σ N (meshDurations t T v) x a' (nodeTable D T g ε m (a', i) : ℂ) :=
      fun i => branchEvolution_eq_tableFamily D σ N (meshDurations t T v) x
        (nodeTable D T g ε m) a' i
    simp only [hbr]
    exact TimeDependentODE.Sampling.padded_sum _ _ _
  -- The per-label targets: the branch sum corrected by the repaired-family table error.
  let Rsum : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun a' =>
    ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
      robustFamily D σ N (meshDurations t T v) x κ a'
        (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j : ℂ)
  let Bsum : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun a' =>
    ∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)
  let Sx : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun a' =>
    Bsum a' - (Rsum a' - robustFamily D σ N (meshDurations t T v) x κ a' (-Complex.I))
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) -
        Sx a'‖ ≤ 2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have e : (∑ i, lchsCoefficients D T g ε i •
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε m) (meshTable t T v) x (a', i)) -
          Sx a' = Rsum a' - robustFamily D σ N (meshDurations t T v) x κ a' (-Complex.I) := by
      simp only [Sx, Bsum]
      abel
    rw [e]
    exact hApproxR a'
  -- The branch comparison: the represented and repaired table sums agree within `ν`.
  have hNodesG : ∀ j, |TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g)
      (accuracy ε) j| ≤ radius g ε := hNodes
  have hBR : ∀ a', ‖Bsum a' - Rsum a'‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have e : Bsum a' - Rsum a' =
        ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
          (tableFamily D σ N (meshDurations t T v) x a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
                ℂ) -
            robustFamily D σ N (meshDurations t T v) x κ a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
                ℂ)) := by
      simp only [Bsum, Rsum, hsum a', smul_sub, Finset.sum_sub_distrib]
    rw [e]
    set W : ℝ := 2 * radius g ε * (negativity t κ + refinementError D t T N) with hW
    have hterm : ∀ j, ‖TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
        (accuracy ε) j • (tableFamily D σ N (meshDurations t T v) x a'
            (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
              ℂ) -
          robustFamily D σ N (meshDurations t T v) x κ a'
            (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j :
              ℂ))‖ ≤
        ‖TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j‖ *
          W := by
      intro j
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h := tableFamily_sub_robustFamily D hM hmesh hT hN v x κ hκ a'
        (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j)
      refine h.trans ?_
      have hΛ0 : 0 ≤ negativity t κ + refinementError D t T N :=
        add_nonneg (negativity_nonneg hmesh hκ) (refinementError_nonneg D t T N)
      rw [hW]
      have := hNodesG j
      nlinarith
    have hW0 : 0 ≤ W := by
      rw [hW]
      exact mul_nonneg (mul_nonneg (by norm_num) hR)
        (add_nonneg (negativity_nonneg hmesh hκ) (refinementError_nonneg D t T N))
    calc _ ≤ ∑ j, ‖TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
            (accuracy ε) j‖ * W :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
      _ = ODECoherentLCU.coefficientMass (TimeDependentODE.GaussianLCHS.coefficients
            (lipschitz D T) (ratio g) (accuracy ε)) * W := by
          rw [ODECoherentLCU.coefficientMass, Finset.sum_mul]
      _ ≤ 3 * W := mul_le_mul_of_nonneg_right hMass hW0
      _ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
          rw [hW]
          have h6 := hBranch
          change 6 * radius g ε * (negativity t κ + refinementError D t T N) ≤
            ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) at h6
          linarith
  have hQuad : ‖(∑ a', Sx a' (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have e : (∑ a', Sx a' (z a')) - y = ∑ a', (Bsum a' - Rsum a') (z a') := by
      simp only [y, robustTarget, Sx, sub_apply, Finset.sum_sub_distrib]
      abel
    rw [e, ODESourceBranches.mass, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
    exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hBR a') (norm_nonneg _))
  have hCertS : ODEActualSourceError.Certificate E z c
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g)
        (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (GeneralSourceODE.Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x)
      (hAct x).1
      (fun a' i => MeshSelect.branchEvolution D σ N (nodeTable D T g ε m)
        (meshTable t T v) x (a', i))
      Sx y (ratio g)
      (accuracy ε) hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := MeshNative.trial_certificate D hM i0 m N d pN Pw hPw J hJ (phases ω)
    (phases_norm ω) E hEiso z c hcpos seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hz hW hCertS hq hSeedUnit hOutput
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary hOracle x) hε.le hTarget hFinal

end

end SparseHamiltonian.RepresentedSampleODE

