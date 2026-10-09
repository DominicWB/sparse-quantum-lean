import TimeDependentExtensions.ODE.Target
import TimeDependentExtensions.ODE.Source
import TimeDependentODE.Theorem

set_option autoImplicit false

/-!
# Time-dependent dissipative sparse ODE solver on general meshes (`ode:thm:time`)

The generalisations of Theorem `ode:thm:time` in its proof and the paragraph after
`hs:thm:time`: an arbitrary mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` with breakpoints of the generator and
of the forcing at the mesh points (one piece `G_r`, `b_r` per interval, with one-sided
derivatives of the solution there), integrated sample-error certificates, the left-endpoint
source quadrature on the mesh with forcing samples certified by an integral (any `b̃_r`, for
example interval averages), and coherent start times of the source branches at the mesh
points.

The coherent time-indexed sparse oracle supplies one represented generator
`G̃_r = D.matrix (x, r)` per interval; the source interfaces prepare the initial direction and,
coherently in the label, the forcing directions. The source mass is
`B = r₀ + ∑_q Δ_q rb q`, `Δ_q = t_{q+1} - t_q` (`MeshSampling.mass`). The SELECT runs on `N`
slots of length `T / N`; slot `k` reads the sample of its interval (`pieceOf`), and the
forcing of interval `q` starts at the first slot of that interval through the released public
duration table.

`solver`: under the public slot conditions `8 s ρ T ≤ N` and `3 (√(2s) ρ T)³ ≤ ν N²` (the
released mesh conditions with `N` in place of `M`), one public trial family satisfies the
released complete certificate for every instance whose pieces are accretive and
interval-integrable, whose forcing is bounded by `b_max`, whose source norms are the public
ones, whose solution is nonzero with `B ≤ g ‖x(T)‖`, and whose certified error

  `(r₀ + b_max T) ∑_r ∫ ‖G_r - G̃_r‖ + ∑_r ∫ ‖b_r - b̃_r‖ + publicError`

is at most `ε B / (2000 g)`; `publicError = s Λ (∑_q Δ_q² rb q / 2 + M (T / N) B)` collects
the source quadrature and the refinement into slots (`Λ = D.scale`). The query counts are
those of the released `TimeDependentODE.solver`; neither `M`, `N`, the mesh nor the
certificates enter them.
-/

namespace TimeDependentExtensions

namespace ODE

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory
open SparseHamiltonian.TimeDependentODE (ratio accuracy radius precision lipschitz Index
  lchsCoefficients nodeTable retarget SolvesODE Accretive mask mask_nonneg)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- Public joint source/LCHS coefficients on the mesh. -/
def coefficients (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T g ε r₀ : ℝ) (rb : Fin M → ℝ) :
    TimeDependentODE.NativeSource.Label (Index D T g ε) M → ℂ :=
  MeshSampling.coefficients r₀ t rb (lchsCoefficients D T g ε)

/-- The public part of the certified discretisation error: the left-endpoint source
quadrature on the mesh and the refinement of the mesh into `N` slots. -/
def publicError (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (T : ℝ) (N : ℕ) (r₀ : ℝ)
    (rb : Fin M → ℝ) : ℝ :=
  (s : ℝ) * D.scale * ((∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 +
    M * (T / N) * MeshSampling.mass r₀ t rb)

/-- One public circuit family, chosen before every unknown instance: matrix input, generator
and forcing pieces, solution and both source directions. -/
def Outcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : TimeDependentODE.NativeSource.SourceSpace (Index D T g ε) n M →L[ℂ]
      MeshSource.MatrixSpace (Index D T g ε) n Z M N d)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshSource.physicalOracle (ι := Index D T g ε) D N d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      ‖sol 0‖ = r₀ → (∀ r, ‖bs r‖ = rb r) →
      (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) →
      sol T ≠ 0 →
      MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖ →
      (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
          publicError D t T N r₀ rb ≤ ε * MeshSampling.mass r₀ t rb / (2000 * g) →
      ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations (ratio g))
        (MeshSource.input D hM (Sum.inr false) N d
          (ODECompiledSource.seed E (coefficients D t T g ε r₀ rb) seed))
        (MeshSource.input D hM (Sum.inr false) N d ∘L
          ODECompiledSource.output E (coefficients D t T g ε r₀ rb))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) ε

set_option maxRecDepth 8192 in
/-- **Theorem `ode:thm:time` on general meshes, with breakpoints, integrated certificates
and the nonuniform source quadrature.** Under uniform sparse energy bounds `η_H`, `η_D`,
positivity of every sampled dissipative part, the public slot conditions and a positive public
source mass, one public trial family satisfies the released complete certificate for every
valid instance (`Outcome`). No implementation, simulation, LCHS, quadrature or success premise
is assumed. -/
theorem solver (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ} (hN : 0 < N)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius g ε * etaD)
    (hClock : 8 * s * ((etaH + radius g ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * ((etaH + radius g ε * etaD) * T)) ^ 3 ≤
      precision g ε * (N : ℝ) ^ 2)
    (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < MeshSampling.mass r₀ t rb)
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
    Outcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed := by
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
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT.le (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, hNodes, hMass, hApprox⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (fun y : X × Option (Fin M) => MeshSampling.family D σ N T y.1 y.2)
    (fun y z => MeshSampling.family_analyticAt D σ N T y.1 y.2 z)
    (fun y z hz => MeshSampling.family_norm_le_one D σ N T hT.le hPSD y.1 y.2 z hz)
    (lipschitz D T) hL
    (fun y k l => MeshSampling.family_lipschitz D σ hN T hT.le y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- One public SELECT program on `N` slots for the public node and duration tables.
  let i0 : Index D T g ε := Sum.inr false
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    MeshSelect.select (ι := TimeDependentODE.NativeSource.Label (Index D T g ε) M) D hM σ hN
      (TimeDependentODE.NativeSource.dummy hM i0) etaH etaD (radius g ε) T (precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD hClock hCayley
  have hk : ∀ a, |nodeTable D T g ε a| ≤ radius g ε := fun a =>
    ODECoefficientPadding.paddedNodes_bound _ _ hR hNodes a.2
  have hu : ∀ (a : TimeDependentODE.NativeSource.Label (Index D T g ε) M) (r : Fin M),
      0 ≤ TimeDependentODE.Sampling.durationTable T a r := fun a r =>
    mul_nonneg hT.le (mask_nonneg (TimeDependentODE.Sampling.start a.1) (r : ℕ))
  have huT : ∀ (a : TimeDependentODE.NativeSource.Label (Index D T g ε) M) (r : Fin M),
      TimeDependentODE.Sampling.durationTable T a r ≤ T := by
    intro a r
    have hm : mask (TimeDependentODE.Sampling.start a.1) (r : ℕ) ≤ 1 := by
      unfold mask
      split_ifs <;> norm_num
    calc
      TimeDependentODE.Sampling.durationTable T a r =
          T * mask (TimeDependentODE.Sampling.start a.1) (r : ℕ) := rfl
      _ ≤ T * 1 := mul_le_mul_of_nonneg_left hm hT.le
      _ = T := mul_one T
  obtain ⟨p, hCount, hE, hAct⟩ :=
    hTables (nodeTable D T g ε) (TimeDependentODE.Sampling.durationTable T) hk hu huT
  let d := TimeDependentODE.Select.degree (s : ℝ) γ (etaH + radius g ε * etaD) T
    (precision g ε) N
  let E : TimeDependentODE.NativeSource.SourceSpace (Index D T g ε) n M →L[ℂ]
      MeshSource.MatrixSpace (Index D T g ε) n Z M N d :=
    MeshSelect.alignedInput D hM σ (TimeDependentODE.NativeSource.dummy hM i0) N γ
      (etaH + radius g ε * etaD) T (precision g ε)
  have hEiso : E† ∘L E = 1 := hE
  let pN : MultiOracleCircuit.Program (MeshSource.matrixOracle (ι := Index D T g ε) D N d) := p
  let a := coefficients D t T g ε r₀ rb
  have ha : 0 < ODECoherentLCU.coefficientMass a := by
    rw [show a = MeshSampling.coefficients r₀ t rb (lchsCoefficients D T g ε) from rfl,
      MeshSampling.coefficients_mass r₀ t rb h₀ hmesh.mono hb hB _ hc]
    norm_num
  let q := MeshSource.publicTrials D hM i0 N d pN J₀ Jb E hEiso a seed
    (ODECompiledSource.seed_unit E a hEiso ha seed hSeed)
    (ODECompiledSource.output_isometry E a hEiso ha)
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) :=
    ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T (ratio g) (accuracy ε)
      (Nat.cast_nonneg s) hH hDiss hT.le hg' hε' hε'One hCount
  refine ⟨d, E, q, fun j y => (q j).eval_unitary
    (MeshSource.physicalOracle_unitary D N d J₀ Jb hJ₀ hJb) y, ?_⟩
  intro x G b sol bs bmax hG hGint hbint hbB hsol h0 hbn hInitial hForcing hTarget hBudget
    hDisc
  have hbmax : 0 ≤ bmax :=
    (norm_nonneg _).trans (hbB ⟨0, hM⟩ (t 0) ⟨le_rfl, hmesh.mono (Nat.zero_le 1)⟩)
  -- The discretised target of the represented samples.
  let z := MeshSampling.sources (sol 0) t bs
  let y := MeshSampling.target D hM t T N x (sol 0) bs
  have hzNorm : ∀ a', ‖z a'‖ = MeshSampling.norms r₀ t rb a' :=
    MeshSampling.sources_norm (sol 0) t hmesh.mono bs r₀ rb h0 hbn
  have hMassZ : ODESourceBranches.mass z = MeshSampling.mass r₀ t rb :=
    MeshSampling.mass_eq z r₀ t rb hzNorm
  have hErr : ‖sol T - y‖ ≤ (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
        ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
      (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        publicError D t T N r₀ rb := by
    have h := MeshSampling.target_error D hM hPSD x hmesh hT hN G b sol bs bmax hbmax hG
      hGint hbint hbB hsol
    have hsum : ∑ a', ‖MeshSampling.sources (sol 0) t bs a'‖ = MeshSampling.mass r₀ t rb := by
      rw [← hMassZ]
      rfl
    rw [hsum, h0] at h
    simp only [hbn] at h
    exact h
  obtain ⟨hy, hBy, hDir⟩ := TimeDependentODE.Sampling.target_budget (sol T) y
    (MeshSampling.mass r₀ t rb) g ε _ hg hε hεOne hTarget hBudget hErr hDisc
  have hCoeff : ODEActualSourceError.coefficients z (lchsCoefficients D T g ε) = a :=
    MeshSampling.actual_coefficients_eq z r₀ t rb hzNorm _
  -- Hypotheses of the released actual-source certificate.
  have hJ : ∀ a', (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a')† ∘L
      TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a' = 1 := by
    intro a'
    cases a' with
    | none => exact (hJ₀ x).1
    | some r => exact (hJb x r).1
  have hPrep : ∀ a', z a' ≠ 0 →
      TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a' seed =
        ODEStateNormalization.unitDirection (z a') := by
    intro a' hz
    cases a' with
    | none => exact hInitial hz
    | some r =>
        have hbr : bs r ≠ 0 := by
          intro h
          apply hz
          change (t ((r : ℕ) + 1) - t r) • bs r = 0
          rw [h, smul_zero]
        have hΔ : 0 < t ((r : ℕ) + 1) - t r := by
          rcases (hmesh.length_nonneg r).lt_or_eq with h | h
          · exact h
          · exfalso
            apply hz
            change (t ((r : ℕ) + 1) - t r) • bs r = 0
            rw [← h, zero_smul]
        change Jb x r seed = ODEStateNormalization.unitDirection
          ((t ((r : ℕ) + 1) - t r) • bs r)
        rw [TimeDependentODE.Sampling.unitDirection_smul _ hΔ (bs r)]
        exact hForcing r hbr
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    MeshSampling.target_norm_le D hM t T hT.le N hPSD x (sol 0) bs
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    rw [hMassZ]
    unfold ratio
    exact hBy
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin M) × Index D T g ε =>
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε)
          (TimeDependentODE.Sampling.durationTable T) x (a'.1, a'.2))‖ ≤
        ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) :=
    (hAct x).2
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      MeshSelect.branchEvolution D σ N (nodeTable D T g ε)
        (TimeDependentODE.Sampling.durationTable T) x (a', i)) -
        MeshSampling.family D σ N T x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        MeshSelect.branchEvolution D σ N (nodeTable D T g ε)
          (TimeDependentODE.Sampling.durationTable T) x (a', i)) =
          ∑ j, TimeDependentODE.GaussianLCHS.coefficients (lipschitz D T) (ratio g)
              (accuracy ε) j •
            MeshSampling.family D σ N T x a'
              (TimeDependentODE.GaussianLCHS.nodes (lipschitz D T) (ratio g)
                (accuracy ε) j : ℂ) := by
      simp only [MeshSampling.branchEvolution_eq_family]
      exact TimeDependentODE.Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', MeshSampling.family D σ N T x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    rw [show (∑ a', MeshSampling.family D σ N T x a' (-Complex.I) (z a')) = y from rfl,
      sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCert : ODEActualSourceError.Certificate E z (lchsCoefficients D T g ε)
      (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x)) (pN.eval x) seed y (ratio g)
        (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z (lchsCoefficients D T g ε) hc
      (TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x)) hJ seed hSeed hPrep (pN.eval x)
      (hAct x).1
      (fun a' i => MeshSelect.branchEvolution D σ N (nodeTable D T g ε)
        (TimeDependentODE.Sampling.durationTable T) x (a', i))
      (fun a' => MeshSampling.family D σ N T x a' (-Complex.I)) y (ratio g) (accuracy ε)
      hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := MeshSource.coefficient_trial_certificate D hM i0 N d pN J₀ Jb hJ₀ hJb
    E hEiso z (lchsCoefficients D T g ε) seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hCert hq a ha hCoeff
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary (MeshSource.physicalOracle_unitary D N d J₀ Jb hJ₀ hJb) x)
    hε.le hTarget hFinal

end

end ODE

end TimeDependentExtensions
