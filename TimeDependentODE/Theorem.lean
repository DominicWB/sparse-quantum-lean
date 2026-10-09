import TimeDependentODE.Solver.Target
import TimeDependentODE.Native.Source
import SparseODE.ODECompleteSuccess
import SparseODE.ODEFinitePropagator

/-!
# Time-dependent dissipative sparse ODE solver (`ode:thm:time`)

The coherent time-indexed sparse oracle supplies, for each unknown instance
`x` and each sample `r < M`, the represented generator
`G̃_r = D.matrix (x, r)` of `x' = -G(u) x + b(u)` on a uniform mesh of `[0, T]`.
The supplied source interfaces prepare the initial direction (`J₀ x`) and,
coherently in the quadrature label, the forcing-sample directions
(`Jb x r`). Their norms `r₀` and `rb r` are public; the source mass is
`B = r₀ + (T/M) ∑ rb r`, the left-endpoint quadrature of
`‖x₀‖ + ∫ ‖b‖`.

One public trial family, encoding, seed and output flag are selected before
the matrix input, the generator and forcing paths, the solution and both
source directions (`Outcome`). For every valid instance the released
complete four-attempt protocol (`ODECompleteTrial.Certificate`) prepares the
normalized solution `x(T) / ‖x(T)‖` with conditional trace-distance error at
most `ε` and success probability at least `2/3`, with at most

  `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`,  `g' = 2 g`,

primitive coherent sampled-time matrix queries, and at most `80 g'`
source-preparation calls, counted separately (`solver`). Here
`Θ = T η_H + T η_D ℓ` and `ℓ = log (10000 g' / (ε / 2))`, exactly as in the
time-independent solver; neither the mesh size `M` nor the regularity
constants enter the query count.

The construction is the time-independent one with three replacements:
the native SELECT is the coherent sampled-time SELECT
(`Select.select`), each LCHS branch is the ordered product of its slot
evolutions (`Sampling.family`), and the source register loads the initial
state together with all `M` forcing samples, each propagated from its own
start slot. The Gaussian LCHS table is certified for all these products at
once (`GaussianLCHS.table_certificate`). The discretised target equals the
exponential left-endpoint recurrence, whose certified distance from the
solution is controlled by the public relative budget
`discretisation ≤ ε B / (2000 g)` (`Sampling.discretisation_error`,
`Sampling.target_budget`).
-/

namespace SparseHamiltonian.TimeDependentODE

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

/-- Internal amplification ratio: the discretised target retains half of the
solution norm. -/
def ratio (g : ℝ) : ℝ := 2 * g

/-- Internal source-certificate precision: the other half of the direction
error is reserved for the discretisation. -/
def accuracy (ε : ℝ) : ℝ := ε / 2

/-- Public LCHS frequency radius. -/
def radius (g ε : ℝ) : ℝ := ImprovedODEQueryBudget.radius (ratio g) (accuracy ε)

/-- Public SELECT precision. -/
def precision (g ε : ℝ) : ℝ := ImprovedODEQueryBudget.precision (ratio g) (accuracy ε)

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- Public real-axis Lipschitz constant of all LCHS product families. -/
def lipschitz (D : Data (X × Fin M) n Z s) (T : ℝ) : ℝ := T * ((s : ℝ) * D.scale)

/-- LCHS labels: the public Gaussian grid and two padding labels. -/
abbrev Index (D : Data (X × Fin M) n Z s) (T g ε : ℝ) :=
  Fin (GaussianLCHS.gridSize (lipschitz D T) (ratio g) (accuracy ε)) ⊕ Bool

/-- Public LCHS coefficients, padded to absolute mass three. -/
def lchsCoefficients (D : Data (X × Fin M) n Z s) (T g ε : ℝ) : Index D T g ε → ℂ :=
  ODECoefficientPadding.paddedCoefficient
    (GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε)) 3

/-- Public LCHS nodes; the padding labels use frequency zero. -/
def lchsNodes (D : Data (X × Fin M) n Z s) (T g ε : ℝ) : Index D T g ε → ℝ :=
  ODECoefficientPadding.paddedNodes (GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε))

/-- Public SELECT node table. -/
def nodeTable (D : Data (X × Fin M) n Z s) (T g ε : ℝ) :
    NativeSource.Label (Index D T g ε) M → ℝ :=
  fun a => lchsNodes D T g ε a.2

/-- Public joint source/LCHS coefficients. -/
def coefficients (D : Data (X × Fin M) n Z s) (T g ε r₀ : ℝ) (rb : Fin M → ℝ) :
    NativeSource.Label (Index D T g ε) M → ℂ :=
  PublicSource.coefficients r₀ T rb (lchsCoefficients D T g ε)

/-- A trial certificate transfers to any target of nearby direction; only the
direction error changes. -/
theorem retarget {P R X L : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {V : (L ⊕ Bool) → X → R →L[ℂ] R}
    {q : ℕ → MultiOracleCircuit.Program V} {N : ℕ} {ψ : R} {F : P →L[ℂ] R} {x : X}
    {target target' : P} {s' Θ ell g η δ η' : ℝ}
    (h : ODEPrimitiveSourceJoin.TrialCertificate q N ψ F x target s' Θ ell g η)
    (hδ : ‖ODEStateNormalization.unitDirection target -
      ODEStateNormalization.unitDirection target'‖ ≤ δ) (hη : η + δ ≤ η') :
    ODEPrimitiveSourceJoin.TrialCertificate q N ψ F x target' s' Θ ell g η' :=
  { h with
    direction_error := fun j hj hne => by
      obtain ⟨ω, hω, hd⟩ := h.direction_error j hj hne
      exact ⟨ω, hω, ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add hd hδ)).trans hη⟩ }

/-- One public circuit family, chosen before every unknown instance: matrix
input, generator and forcing paths, solution and both source directions. -/
def Outcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (etaH etaD T g ε r₀ : ℝ)
    (rb : Fin M → ℝ) (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : NativeSource.SourceSpace (Index D T g ε) n M →L[ℂ]
      NativeSource.MatrixSpace (Index D T g ε) n Z M d)
    (q : ℕ → MultiOracleCircuit.Program
      (NativeSource.physicalOracle (ι := Index D T g ε) D d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n)
      (βG δG βb δb bmax : ℝ), 0 ≤ βG → 0 ≤ βb →
      (∀ u ∈ Set.Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖G u - G v‖ ≤ βG * |u - v|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      (∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T, ‖b u - b v‖ ≤ βb * |u - v|) →
      (∀ r : Fin M, ‖b ((r : ℕ) * T / M) - bs r‖ ≤ δb) →
      (∀ u ∈ Set.Icc 0 T, ‖b u‖ ≤ bmax) →
      SolvesODE G b sol 0 T →
      ‖sol 0‖ = r₀ → (∀ r, ‖bs r‖ = rb r) →
      (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) →
      sol T ≠ 0 →
      PublicSource.mass r₀ T rb ≤ g * ‖sol T‖ →
      Sampling.discretisation D T βG δG βb δb bmax r₀ ≤
        ε * PublicSource.mass r₀ T rb / (2000 * g) →
      ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations (ratio g))
        (NativeSource.input D hM (Sum.inr false) d
          (ODECompiledSource.seed E (coefficients D T g ε r₀ rb) seed))
        (NativeSource.input D hM (Sum.inr false) d ∘L
          ODECompiledSource.output E (coefficients D T g ε r₀ rb))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) ε

/-- **Time-dependent dissipative sparse ODE solver (`ode:thm:time`).**
Under uniform sparse energy bounds `η_H`, `η_D`, positivity of every sampled
dissipative part, the public mesh conditions and a positive public source
mass, one public trial family satisfies the released complete certificate for
every instance whose generator path is accretive and Lipschitz, whose forcing
path is bounded and Lipschitz, whose samples are within `δG`, `δb` of the
represented ones, whose source norms are the public ones, whose solution is
nonzero with `B ≤ g ‖x(T)‖`, and whose certified discretisation error is at
most `ε B / (2000 g)`. No implementation, simulation, LCHS, quadrature or
success premise is assumed. -/
theorem solver (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius g ε * etaD)
    (hMesh : 8 * s * ((etaH + radius g ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * ((etaH + radius g ε * etaD) * T)) ^ 3 ≤
      precision g ε * (M : ℝ) ^ 2)
    (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < PublicSource.mass r₀ T rb)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    Outcome D hM etaH etaD T g ε r₀ rb J₀ Jb seed := by
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
  have hh : 0 < T / M := div_pos hT hMR
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, hNodes, hMass, hApprox⟩ := GaussianLCHS.table_certificate
    (fun y : X × Option (Fin M) => Sampling.family D hM T y.1 y.2)
    (fun y z => Sampling.family_analyticAt D hM T y.1 y.2 z)
    (fun y z hz => Sampling.family_norm_le_one D hM T hT.le hPSD y.1 y.2 z hz)
    (lipschitz D T) hL (fun y k l => Sampling.family_lipschitz D hM T hT.le y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- One public SELECT program for the public node and duration tables.
  let i0 : Index D T g ε := Sum.inr false
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    Select.select (ι := NativeSource.Label (Index D T g ε) M) D hM
      (NativeSource.dummy hM i0) etaH etaD (radius g ε) T (precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD hMesh hCayley
  have hk : ∀ a, |nodeTable D T g ε a| ≤ radius g ε := fun a =>
    ODECoefficientPadding.paddedNodes_bound _ _ hR hNodes a.2
  have hu : ∀ (a : NativeSource.Label (Index D T g ε) M) (r : Fin M),
      0 ≤ Sampling.durationTable T a r := fun a r =>
    mul_nonneg hT.le (mask_nonneg (Sampling.start a.1) (r : ℕ))
  have huT : ∀ (a : NativeSource.Label (Index D T g ε) M) (r : Fin M),
      Sampling.durationTable T a r ≤ T := by
    intro a r
    have hm : mask (Sampling.start a.1) (r : ℕ) ≤ 1 := by
      unfold mask
      split_ifs <;> norm_num
    calc
      Sampling.durationTable T a r = T * mask (Sampling.start a.1) (r : ℕ) := rfl
      _ ≤ T * 1 := mul_le_mul_of_nonneg_left hm hT.le
      _ = T := mul_one T
  obtain ⟨p, hCount, hE, hAct⟩ := hTables (nodeTable D T g ε) (Sampling.durationTable T) hk hu huT
  let d := Select.degree (s : ℝ) γ (etaH + radius g ε * etaD) T (precision g ε) M
  let E : NativeSource.SourceSpace (Index D T g ε) n M →L[ℂ]
      NativeSource.MatrixSpace (Index D T g ε) n Z M d :=
    Select.alignedInput D hM (NativeSource.dummy hM i0) γ (etaH + radius g ε * etaD) T
      (precision g ε)
  have hEiso : E† ∘L E = 1 := hE
  let pN : MultiOracleCircuit.Program (NativeSource.matrixOracle (ι := Index D T g ε) D d) := p
  let a := coefficients D T g ε r₀ rb
  have ha : 0 < ODECoherentLCU.coefficientMass a := by
    rw [show a = PublicSource.coefficients r₀ T rb (lchsCoefficients D T g ε) from rfl,
      PublicSource.coefficients_mass r₀ T rb h₀ hT.le hb hB _ hc]
    norm_num
  let q := NativeSource.publicTrials D hM i0 d pN J₀ Jb E hEiso a seed
    (ODECompiledSource.seed_unit E a hEiso ha seed hSeed)
    (ODECompiledSource.output_isometry E a hEiso ha)
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) :=
    ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T (ratio g) (accuracy ε)
      (Nat.cast_nonneg s) hH hDiss hT.le hg' hε' hε'One hCount
  refine ⟨d, E, q, fun j y => (q j).eval_unitary
    (NativeSource.physicalOracle_unitary D d J₀ Jb hJ₀ hJb) y, ?_⟩
  intro x G b sol bs βG δG βb δb bmax hβG hβb hG hGLip hGs hbLip hbs hbB hsol h0 hbn
    hInitial hForcing hTarget hBudget hDisc
  -- The discretised target of the represented samples.
  let Gs := Sampling.generator D hM x
  let z := Sampling.sources (sol 0) (T / M) bs
  let y := Sampling.target Gs (T / M) (sol 0) bs
  have hErr := Sampling.discretisation_error D hM hPSD x T hT.le G b sol bs βG δG βb δb bmax
    hβG hβb hG hGLip hGs hbLip hbs hbB hsol
  rw [h0] at hErr
  obtain ⟨hy, hBy, hDir⟩ := Sampling.target_budget (sol T) y (PublicSource.mass r₀ T rb)
    g ε _ hg hε hεOne hTarget hBudget hErr hDisc
  have hzNorm : ∀ a', ‖z a'‖ = PublicSource.norms r₀ T rb a' :=
    Sampling.sources_norm (sol 0) T hT.le bs r₀ rb h0 hbn
  have hMassZ : ODESourceBranches.mass z = PublicSource.mass r₀ T rb :=
    PublicSource.mass_eq z r₀ T rb hzNorm
  have hCoeff : ODEActualSourceError.coefficients z (lchsCoefficients D T g ε) = a :=
    PublicSource.actual_coefficients_eq z r₀ T rb hzNorm _
  -- Hypotheses of the released actual-source certificate.
  have hJ : ∀ a', (SourceTD.branchTD (J₀ x) (Jb x) a')† ∘L
      SourceTD.branchTD (J₀ x) (Jb x) a' = 1 := by
    intro a'
    cases a' with
    | none => exact (hJ₀ x).1
    | some r => exact (hJb x r).1
  have hPrep : ∀ a', z a' ≠ 0 →
      SourceTD.branchTD (J₀ x) (Jb x) a' seed = ODEStateNormalization.unitDirection (z a') := by
    intro a' hz
    cases a' with
    | none => exact hInitial hz
    | some r =>
        have hbr : bs r ≠ 0 := by
          intro h
          apply hz
          change (T / M) • bs r = 0
          rw [h, smul_zero]
        change Jb x r seed = ODEStateNormalization.unitDirection ((T / M) • bs r)
        rw [Sampling.unitDirection_smul (T / M) hh (bs r)]
        exact hForcing r hbr
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    Sampling.target_norm_le Gs (Sampling.generator_accretive D hM hPSD x) (T / M) hh.le
      (sol 0) bs
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    rw [hMassZ]
    unfold ratio
    exact hBy
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin M) × Index D T g ε =>
        Select.branchEvolution D hM (nodeTable D T g ε) (Sampling.durationTable T) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) :=
    (hAct x).2
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      Select.branchEvolution D hM (nodeTable D T g ε) (Sampling.durationTable T) x (a', i)) -
        Sampling.family D hM T x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        Select.branchEvolution D hM (nodeTable D T g ε) (Sampling.durationTable T) x (a', i)) =
          ∑ j, GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
            Sampling.family D hM T x a'
              (GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j : ℂ) := by
      simp only [Sampling.branchEvolution_eq_family]
      exact Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', Sampling.family D hM T x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', Sampling.family D hM T x a' (-Complex.I) (z a')) = y := by
      apply Finset.sum_congr rfl
      intro a' _
      rw [Sampling.family_neg_I]
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCert : ODEActualSourceError.Certificate E z (lchsCoefficients D T g ε)
      (SourceTD.branchTD (J₀ x) (Jb x)) (pN.eval x) seed y (ratio g) (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z (lchsCoefficients D T g ε) hc
      (SourceTD.branchTD (J₀ x) (Jb x)) hJ seed hSeed hPrep (pN.eval x) (hAct x).1
      (fun a' i => Select.branchEvolution D hM (nodeTable D T g ε)
        (Sampling.durationTable T) x (a', i))
      (fun a' => Sampling.family D hM T x a' (-Complex.I)) y (ratio g) (accuracy ε)
      hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := NativeSource.coefficient_trial_certificate D hM i0 d pN J₀ Jb hJ₀ hJb
    E hEiso z (lchsCoefficients D T g ε) seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hCert hq a ha hCoeff
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary (NativeSource.physicalOracle_unitary D d J₀ Jb hJ₀ hJb) x)
    hε.le hTarget hFinal

end

end SparseHamiltonian.TimeDependentODE
