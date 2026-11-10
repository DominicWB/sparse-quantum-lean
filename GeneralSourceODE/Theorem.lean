import GeneralSourceODE.Native
import GeneralSourceODE.Target
import GeneralSourceODE.Duhamel
import GeneralSourceODE.Oracles
import TimeDependentODE.Theorem

/-!
# Time-dependent sparse ODE solver with the general source interface

`ode:thm:time` with the source access of
`ode:eq:source-interface-mass` and `ode:eq:source-interface-preparation`.
The input supplies public nodes `v_i ∈ [0, T]` and complex coefficients
`ω_i` (`1 ≤ i ≤ m`), independent of the `M` time samples of the matrix
oracle. The actual source vectors are `x₀` on label `0` and `ω_i b(v_i)` on
label `i`; their absolute mass is `B_q = ‖x₀‖ + ∑ |ω_i| ‖b(v_i)‖`.

The supplied preparations are a weight oracle `P_w` on the source label,
with `P_w |0⟩ = ∑_a √(‖z_a‖ / B_q) |a⟩` (`Compiled.WeightPrep`), and a
label-controlled loading oracle `U_load` that prepares the directions
`x₀ / ‖x₀‖` and `b(v_i) / ‖b(v_i)‖` from the seed. The public phases
`ω_i / |ω_i|` are applied separately (`phases`). One counted source call is
`phase ∘ U_load ∘ (P_w ⊗ 1)`, the other is the label unpreparation
`P_w† ⊗ 1`; the seed and the output encoding are public, so neither `B_q`
nor the source norms enter the circuit.

The certificate hypotheses are those of the manuscript: the coefficient mass
obeys `B_q ≤ c_q B` with `B = ‖x₀‖ + ∫₀ᵀ ‖b‖`, and the propagated source sum
approximates the solution, `‖x(T) - U(T,0)x₀ - ∑ ω_i U(T, v_i) b(v_i)‖ ≤ ζ B`.
By Duhamel's formula this is the certificate on the propagated vector
integral; `GeneralSourceODE.Duhamel` proves that formula, and `solver` states
the certificate with the integral itself. Here `U t w` is the homogeneous
solution on `[t, T]` with value `w` at `t`.

For every valid instance, the one public trial family satisfies the released
complete four-attempt certificate (`ODECompleteTrial.Certificate`) at the
amplification ratio `g' = 2 c_q ḡ`: conditional trace distance at most `ε`,
success probability at least `2/3`, at most
`1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` primitive matrix queries and at most
`40 g'` calls of each counted source interface (`propagated_solver`).
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open TimeDependentODE
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 4000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The source scale `B = ‖x₀‖ + ∫₀ᵀ ‖b‖` of the manuscript. -/
def sourceScale {V : Type*} [NormedAddCommGroup V] (sol b : ℝ → V) (T : ℝ) : ℝ :=
  ‖sol 0‖ + ∫ u in (0 : ℝ)..T, ‖b u‖

/-- Public SELECT node table on the general labels. -/
def nodeTable (D : Data (X × Fin M) n Z s) (T g ε : ℝ) (m : ℕ) :
    Native.Label (Index D T g ε) m → ℝ :=
  fun a => lchsNodes D T g ε a.2

/-- One public circuit family, chosen before every unknown instance: matrix
input, generator and forcing paths, solution, propagator and source data.
The weight and loading oracles are supplied (as functions of the unknown
instance); the nodes, coefficients and phases are public. The source
certificate is stated for the propagated source sum. -/
def PropagatedOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      Native.MatrixSpace (Index D T (cq * gbar) ε) n Z m M d)
    (_hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (Native.physicalOracle (ι := Index D T (cq * gbar) ε) D m d Pw J (phases ω))),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (Native.input D hM (Sum.inr false) m d
          (ODECompiledSource.seed E
            (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed))
        (Native.input D hM (Sum.inr false) m d ∘L
          ODECompiledSource.output E
            (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

/-- **Time-dependent dissipative sparse ODE solver with the general source
interface (`ode:thm:time`).** Under uniform sparse energy bounds `η_H`,
`η_D`, positivity of every sampled dissipative part, the public mesh
conditions at the amplification ratio `2 c_q ḡ`, and public nodes in
`[0, T]`, one public trial family satisfies the released complete
certificate for every instance whose generator path is accretive and
Lipschitz with sample errors `δ_G`, whose supplied weight and loading
oracles prepare the source weights and directions, whose coefficient mass is
at most `c_q B`, whose propagated source sum is within `ζ B` of the solution,
whose solution is nonzero with `B ≤ ḡ ‖x(T)‖`, and whose combined budget
`ζ + c_q T (β_G T/M + δ_G)` is at most `ε / (2000 ḡ)`. No implementation,
simulation, LCHS or success premise is assumed; the source quadrature enters
only through the certificate `ζ B`. -/
theorem propagated_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    PropagatedOutcome D hM etaH etaD T gbar cq ε v ω Pw J seed := by
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
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, hNodes, hMass, hApprox⟩ := GaussianLCHS.table_certificate
    (fun y : X × Option (Fin m) => family D hM T v y.1 y.2)
    (fun y z => family_analyticAt D hM T v y.1 y.2 z)
    (fun y z hz => family_norm_le_one D hM T hT.le v hPSD y.1 y.2 z hz)
    (lipschitz D T) hL (fun y k l => family_lipschitz D hM T hT.le v y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- One public SELECT program for the public node and duration tables.
  let i0 : Index D T g ε := Sum.inr false
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    Select.select (ι := Native.Label (Index D T g ε) m) D hM
      (Native.dummy hM i0 m) etaH etaD (radius g ε) T (precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD hMesh hCayley
  have hk : ∀ a, |nodeTable D T g ε m a| ≤ radius g ε := fun a =>
    ODECoefficientPadding.paddedNodes_bound _ _ hR hNodes a.2
  have hu : ∀ (a : Native.Label (Index D T g ε) m) (r : Fin M),
      0 ≤ durationTable T v a r := fun a r => durations_nonneg hT.le v a.1 r
  have huT : ∀ (a : Native.Label (Index D T g ε) m) (r : Fin M),
      durationTable T v a r ≤ T := fun a r => durations_le hT.le hM v a.1 r
  obtain ⟨p, hCount, hE, hAct⟩ := hTables (nodeTable D T g ε m) (durationTable T v) hk hu huT
  let d := Select.degree (s : ℝ) γ (etaH + radius g ε * etaD) T (precision g ε) M
  let E : Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      Native.MatrixSpace (Index D T g ε) n Z m M d :=
    Select.alignedInput D hM (Native.dummy hM i0 m) γ (etaH + radius g ε * etaD) T
      (precision g ε)
  have hEiso : E† ∘L E = 1 := hE
  let pN : MultiOracleCircuit.Program
      (Native.matrixOracle (ι := Index D T g ε) D m d) := p
  let c := lchsCoefficients D T g ε
  have hcpos : 0 < ODECoherentLCU.coefficientMass c := by
    change 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε)
    rw [hc]
    norm_num
  have hsc : 0 < ODECoherentLCU.coefficientMass (Compiled.seedCoefficients (N := m) c) := by
    rw [Compiled.seedCoefficients_mass]
    exact hcpos
  have hSeedUnit := ODECompiledSource.seed_unit E (Compiled.seedCoefficients c) hEiso hsc
    seed hSeed
  have hOutput := ODECompiledSource.output_isometry E (Compiled.seedCoefficients c) hEiso hsc
  let q := Native.publicTrials D hM i0 m d pN Pw J (phases ω) E hEiso c seed
    hSeedUnit hOutput
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) :=
    ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T (ratio g) (accuracy ε)
      (Nat.cast_nonneg s) hH hDiss hT.le hg' hε' hε'One hCount
  have hOracle := Native.physicalOracle_unitary (ι := Index D T g ε) D m d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  refine ⟨d, E, hEiso, q, fun j y => (q j).eval_unitary hOracle y, ?_⟩
  intro x G b sol U βG δG ζ hβG hG hGLip hGs _hsol hU hW hLoad₀ hLoad hMassB hCert
    hTarget hB hBudget
  -- The propagated target of the represented samples.
  let Gs := Sampling.generator D hM x
  have hGsAcc : ∀ r, Accretive (Gs r) := Sampling.generator_accretive D hM hPSD x
  let bv : Fin m → EuclideanSpace ℂ n := fun i => b (v i)
  let z := sources (sol 0) bv ω
  let y := nodeTarget Gs T M v (sol 0) bv ω
  set Bs := sourceScale sol b T with hBs
  have hδG : 0 ≤ δG := (norm_nonneg _).trans (hGs ⟨0, hM⟩)
  have hGs' : ∀ r < M, ‖G (r * T / M) - Gs r‖ ≤ δG := by
    intro r hr
    have hidx : TimeDependent.Sampled.sampleIndex hM r = ⟨r, hr⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hr)
    change ‖G (r * T / M) - SparseStateOverlap.matrixOperator
      (D.matrix (x, TimeDependent.Sampled.sampleIndex hM r))‖ ≤ δG
    rw [hidx]
    exact hGs ⟨r, hr⟩
  have hTargetErr := target_error hT.le hM v hv ω G hG Gs hGsAcc βG δG hβG hδG hGLip hGs'
    U hU (sol 0) bv
  set K : ℝ := βG * (T / M) + δG with hK
  have hK0 : 0 ≤ K := add_nonneg (mul_nonneg hβG (div_nonneg hT.le hMR.le)) hδG
  have hBs0 : 0 ≤ Bs :=
    add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg hT.le fun u _ => norm_nonneg _)
  have hErr : ‖sol T - y‖ ≤ (ζ + cq * (T * K)) * Bs := by
    have hsplit : sol T - y =
        (sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T) +
          ((U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y) := by
      simp only [bv]
      abel
    rw [hsplit]
    have hMassK : T * K * ODESourceBranches.mass z ≤ cq * (T * K) * Bs := by
      have hTK : 0 ≤ T * K := mul_nonneg hT.le hK0
      calc
        T * K * ODESourceBranches.mass z ≤ T * K * (cq * Bs) :=
          mul_le_mul_of_nonneg_left hMassB hTK
        _ = cq * (T * K) * Bs := by ring
    calc
      _ ≤ ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ := norm_add_le _ _
      _ ≤ ζ * Bs + T * K * ODESourceBranches.mass z := add_le_add hCert hTargetErr
      _ ≤ ζ * Bs + cq * (T * K) * Bs := add_le_add le_rfl hMassK
      _ = (ζ + cq * (T * K)) * Bs := by ring
  have hErrBudget : (ζ + cq * (T * K)) * Bs ≤ ε * Bs / (2000 * gbar) := by
    have h := mul_le_mul_of_nonneg_right hBudget hBs0
    calc
      (ζ + cq * (T * K)) * Bs ≤ ε / (2000 * gbar) * Bs := h
      _ = ε * Bs / (2000 * gbar) := by ring
  obtain ⟨hy, hBy, hDir⟩ := Sampling.target_budget (sol T) y Bs gbar ε _ hg hε hεOne
    hTarget hB hErr hErrBudget
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    nodeTarget_norm_le Gs hGsAcc hT.le M v (sol 0) bv ω
  have hz : 0 < ODESourceBranches.mass z := ODESourceBranches.mass_pos_of_solution z y hy hNorm
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    have hcq0 : 0 ≤ cq := by linarith
    calc
      ODESourceBranches.mass z ≤ cq * Bs := hMassB
      _ ≤ cq * (2 * gbar * ‖y‖) := mul_le_mul_of_nonneg_left hBy hcq0
      _ = ratio g * ‖y‖ := by rw [hgdef]; unfold ratio; ring
  -- Hypotheses of the released actual-source certificate.
  have hJph : ∀ a, (Compiled.phased (J x) (phases ω) a)† ∘L
      Compiled.phased (J x) (phases ω) a = 1 :=
    phased_isometry (J x) (hJ x) ω
  have hPrep := phased_prepares (J x) (sol 0) bv ω seed hLoad₀ hLoad
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin m) × Index D T g ε =>
        Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) :=
    (hAct x).2
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x (a', i)) -
        family D hM T v x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x (a', i)) =
          ∑ j, GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
            family D hM T v x a'
              (GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j : ℂ) := by
      simp only [branchEvolution_eq_family]
      exact Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', family D hM T v x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', family D hM T v x a' (-Complex.I) (z a')) = y := by
      apply Finset.sum_congr rfl
      intro a' _
      rw [family_neg_I]
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCertS : ODEActualSourceError.Certificate E z c
      (Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g) (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x) (hAct x).1
      (fun a' i => Select.branchEvolution D hM (nodeTable D T g ε m)
        (durationTable T v) x (a', i))
      (fun a' => family D hM T v x a' (-Complex.I)) y (ratio g) (accuracy ε)
      hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := Native.trial_certificate D hM i0 m d pN Pw hPw J hJ (phases ω)
    (phases_norm ω) E hEiso z c hcpos seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hz hW hCertS hq hSeedUnit hOutput
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary hOracle x) hε.le hTarget hFinal


/-- One public trial family over the actual oracles `P_w`, `U_load`, `P_w†` and
the coherent sampled-time matrix oracle, chosen before every unknown
instance. The algorithm is four fresh trials of this family. The source
certificate is the manuscript's bound on the propagated vector integral. -/
def Outcome (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ) (t : ODERepeatProtocol.TrialFamily
      (Oracles.actualOracle (ι := Index D T (cq * gbar) ε) D m d Pw J) (EuclideanSpace ℂ n)),
    t.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((t.circuit j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      ContinuousOn b (Icc 0 T) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      Oracles.ActualCertificate (ODERepeatProtocol.Protocol.repeatTrials t 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

/-- **Time-dependent dissipative sparse ODE solver with the general source
interface (`ode:thm:time`), on the actual oracles.** Under the hypotheses of
`propagated_solver`, one public family of trial circuits over the coherent
sampled-time matrix oracle and the supplied `P_w`, `U_load` and `P_w†` gives,
by four fresh trials, the normalized solution `x(T)/‖x(T)‖` with conditional
trace distance at most `ε` and success probability at least `2/3`, for every
instance whose generator path is accretive and Lipschitz, whose forcing is
continuous, whose supplied preparations act as in
`ode:eq:source-interface-preparation`, whose coefficient mass is at most
`c_q B`, whose propagated vector integral is certified,
`‖∫₀ᵀ U(T,v) b(v) dv - ∑ ω_i U(T, v_i) b(v_i)‖ ≤ ζ B`, whose solution is
nonzero with `B ≤ ḡ ‖x(T)‖`, and whose budget `ζ + c_q T (β_G T/M + δ_G)` is at
most `ε / (2000 ḡ)`. With `g' = 2 c_q ḡ`, it uses at most
`1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and at most `40 g'` calls
of each of `P_w`, `U_load` and `P_w†` in every history. -/
theorem solver (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    Outcome D etaH etaD T gbar cq ε v ω Pw J seed := by
  obtain ⟨d, E, hE, q, _hUnit, hCert⟩ := propagated_solver D hM etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hρ hMesh hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ
    seed hSeed
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    have hL : 0 ≤ lipschitz D T :=
      mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    obtain ⟨-, -, hMass, -⟩ := GaussianLCHS.table_certificate
      (fun y : X × Option (Fin m) => family D hM T v y.1 y.2)
      (fun y z => family_analyticAt D hM T v y.1 y.2 z)
      (fun y z hz => family_norm_le_one D hM T hT.le v hPSD y.1 y.2 z hz)
      (lipschitz D T) hL (fun y k l => family_lipschitz D hM T hT.le v y.1 y.2 k l)
      (ratio (cq * gbar)) (accuracy ε) hg1 hε' hε'One
    have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) = 3 :=
      ODECoefficientPadding.coefficientMass_eq _ 3 hMass
    rw [hc]
    norm_num
  -- The public seed and output flag on the primitive workspace.
  have hψ := Native.seed_unit D hM (Sum.inr false) m d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos seed hSeed
  have hF := Native.output_isometry D hM (Sum.inr false) m d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos
  -- The trial family over the actual oracles.
  let q' := Oracles.actualTrials D m d Pw J (phases ω) (phases_norm ω) q
  have hEval : ∀ j x, (q' j).eval x = (q j).eval x := fun j x =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (Oracles.implementation_eval D m d Pw J (phases ω) (phases_norm ω)) x
  have hActual := Oracles.actualOracle_unitary (ι := Index D T (cq * gbar) ε) D m d hPw hJ
  refine ⟨d, ODERepeatProtocol.ofCircuits q'
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _ hψ _ hF, rfl,
    fun j y => (q' j.val).eval_unitary hActual y, ?_⟩
  intro x G b sol U βG δG ζ hβG hG hGLip hGs hbc hsol hU hW hLoad₀ hLoad hMassB hInt
    hTarget hB hBudget
  -- Duhamel's formula turns the vector-integral certificate into the
  -- propagated-sum certificate.
  have hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ ‖G 0‖ + βG * T := by
    intro u hu
    have h := hGLip u hu 0 ⟨le_rfl, hT.le⟩
    rw [sub_zero, abs_of_nonneg hu.1] at h
    calc
      ‖G u‖ = ‖G 0 + (G u - G 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G 0‖ + ‖G u - G 0‖ := norm_add_le _ _
      _ ≤ ‖G 0‖ + βG * T := add_le_add le_rfl (h.trans (mul_le_mul_of_nonneg_left hu.2 hβG))
  have hD := duhamel hT.le hU hG _ hΛ hbc hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
      ζ * sourceScale sol b T := by
    rw [← hD]
    exact hInt
  have hC := hCert x G b sol U βG δG ζ hβG hG hGLip hGs hsol hU hW hLoad₀ hLoad hMassB
    hCertP hTarget hB hBudget
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ),
      (q' j).cost w = (q j).cost (fun l =>
        (Oracles.implementation D m d Pw J (phases ω) (phases_norm ω) l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  exact Oracles.actual_certificate hC q' hMpos hψ hF (fun j => hEval j x)
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_matrix D m d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_weight D m d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_load D m d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_unweight D m d Pw J _ _)))
    (fun j => by
      rw [hCost, funext (Oracles.implementation_source D m d Pw J _ _), Oracles.cost_add,
        NativeHermitianDilation.cost_scale])

end

end SparseHamiltonian.GeneralSourceODE
