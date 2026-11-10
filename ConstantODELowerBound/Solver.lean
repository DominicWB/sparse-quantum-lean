import ConstantODELowerBound.Protocol

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released constant-coefficient solver on a one-stage family of the class

Theorem `ode:thm:main` and Section `odel:sec:main` ("the lower bounds apply to the upper bounds of
the preceding section"). This module runs the released solver
`SparseHamiltonian.ODECompleteEndpoint.solver` on `constData F` of a one-stage family `F` of the
class (`g ≤ ḡ`, any row and column bound `η`: the norm information enters only through the split
bounds) with time `T = τ > 0`, promise parameter `g = ḡ`, split bounds `η_H`, `η_D` on the Hermitian
and dissipative parts of the generator, initial norm `r₀ = ‖x₀‖`, forcing norm `r_b = ‖b‖`, any unit
seed and any unitary source interfaces mapping the seed to `x₀/‖x₀‖` and `b/‖b‖`.

* `exists_constProtocol`: the solver's public branch is the positive-time branch
  (`ODECompleteEndpoint.PositiveOutcome`) since `T > 0` and `η_H + R η_D > 0`; it gives a
  released protocol (`Protocol.ConstProtocol`) over the released oracle with branch register
  `RunIndex F τ ḡ ε = Fin gridSize ⊕ Bool` and mesh size `runMesh F τ ḡ ε`, with
  `Θ = theta(τ η_H, τ η_D, ḡ, ε)` and `ℓ = logBudget(ḡ, ε) = log(10⁴ ḡ/ε)`.
* `constProtocol_of_certificate`: every certificate family of that branch on `constData F` (any
  slot count, degree, circuit family, iteration count, seeded input and output map, with the
  universally quantified certificate of `ODECompleteEndpoint.PositiveOutcome`) gives a released
  protocol over the released oracle, so the protocol of every output of the branch is one.

The certificate's target is the released explicit solution, which is the endpoint of every
solution of the family (`Solution.endpoint_eq_constSolution`); the solver's promise
`(r₀ + T r_b)/‖x(T)‖ ≤ g` is the class promise `B ≤ ḡ ‖x(T)‖` (`Solution.oneStage_mass`); the
solver's `D ⪰ 0` is accretivity (`Solution.dissipativePart_nonneg_of_accretive`).
-/

namespace ConstantODELowerBound.Solver

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open ODELowerBoundExtensions.Release (SysOp)
open ConstantODELowerBound.Oracle ConstantODELowerBound.Protocol

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- The branch register of the released run at time `τ`, promise `ḡ` and accuracy `ε`: the LCHS
grid index and the source flag, `Fin gridSize ⊕ Bool`. -/
abbrev RunIndex (F : Family X N Z 1 s) (τ gbar ε : ℝ) : Type :=
  Fin (ODEPublicGaussianEndpoint.gridSize (constData F) τ gbar ε) ⊕ Bool

/-- The mesh size of the released run, `meshSize(constData F, τ, precision(ḡ, ε))`. -/
abbrev runMesh (F : Family X N Z 1 s) (τ gbar ε : ℝ) : ℕ :=
  ODEPublicSourceMesh.meshSize (constData F) τ (ImprovedODEQueryBudget.precision gbar ε)

/-- **The released constant-coefficient solver on a one-stage family of the class** (Theorem
`ode:thm:main`, `ODECompleteEndpoint.solver`): for a one-stage family in the class (any `η`,
`g ≤ ḡ`) with `T = τ > 0`, `0 < ε ≤ 1/2`, split bounds `η_H, η_D ≥ 0` with
`η_H + R(ḡ, ε) η_D > 0` on the Hermitian and dissipative parts of every generator, unitary source
interfaces and a unit seed mapped to `x₀/‖x₀‖` and `b/‖b‖`, the solver gives a slot count, a
degree and a released protocol with `Θ = theta(τ η_H, τ η_D, ḡ, ε)`, `ℓ = logBudget(ḡ, ε)` and
`g = ḡ`. -/
theorem exists_constProtocol (F : Family X N Z 1 s) {η τ gbar ε etaH etaD : ℝ}
    (hF : F.InClass η gbar) (hT : F.T = τ) (hτ : 0 < τ) (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hpos : 0 < etaH + ImprovedODEQueryBudget.radius gbar ε * etaD)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, 0)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (J₀ Jb : X → SysOp N) (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (seed : EuclideanSpace ℂ N)
    (hseed : ‖seed‖ = 1)
    (hJ₀s : F.init ≠ 0 → ∀ x, J₀ x seed = ODEStateNormalization.unitDirection F.init)
    (hJbs : F.src 0 ≠ 0 → ∀ x, Jb x seed = ODEStateNormalization.unitDirection (F.src 0)) :
    ∃ (Tsl d : ℕ) (p : ODERepeatProtocol.Protocol
        (constOracle F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) Tsl d J₀ Jb)
        (EuclideanSpace ℂ N)),
      ConstProtocol F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) Tsl d J₀ Jb p
        (ImprovedODEQueryBudget.theta (τ * etaH) (τ * etaD) gbar ε)
        (ImprovedODEQueryBudget.logBudget gbar ε) gbar ε := by
  by_cases hX : Nonempty X
  swap
  · exact ⟨0, 0, .abort, fun _ => MultiOracleCircuit.Program.identity, 0, 0, 0,
      fun x => (hX ⟨x⟩).elim⟩
  obtain ⟨x₀⟩ := hX
  obtain ⟨sol₀, hs₀, hne₀, hmass₀⟩ := hF.solution x₀
  have hTarget : ∀ {x : X} {sol : ℝ → EuclideanSpace ℂ N}, F.Solves x sol →
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator (constData F) x) F.init
        (F.src 0) τ = sol F.T := by
    intro x sol hs
    rw [Solution.endpoint_eq_constSolution F hs, hT]
  have hMass : ‖F.init‖ + τ * ‖F.src 0‖ = F.mass := by
    rw [Solution.oneStage_mass, hT]
  have hPSD : ∀ (x : X) (w : EuclideanSpace ℂ N), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart ((constData F).matrix x)) w)).re :=
    fun x w => Solution.dissipativePart_nonneg_of_accretive (hF.accretive x 0) w
  have hOut := ODECompleteEndpoint.solver (constData F) etaH etaD τ gbar ε ‖F.init‖ ‖F.src 0‖
    hH hDiss hτ.le hε hε2 hrH hcH hrD hcD hPSD J₀ Jb hJ₀
    hJb seed hseed x₀ F.init (F.src 0) rfl rfl
    (by rw [hTarget hs₀]; exact hne₀)
    (by
      rw [hTarget hs₀, hMass, div_le_iff₀ (norm_pos_iff.mpr hne₀)]
      exact hmass₀)
  rcases hOut with ⟨hT0, -⟩ | ⟨-, hE, -⟩ | ⟨-, -, hPos⟩
  · exact absurd hT0 hτ.ne'
  · exact absurd hE hpos.ne'
  obtain ⟨Tsl, d, E, q, -, hC⟩ := hPos
  have key : ∀ x sol, F.Solves x sol →
      ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations gbar)
        (ODEFinalNativeSource.input (constData F) (Sum.inr false) (runMesh F τ gbar ε) Tsl d
          (ODECompiledSource.seed E
            (ODESourcePublicNorms.publicCoefficients ‖F.init‖ ‖F.src 0‖ τ (runMesh F τ gbar ε)
              (ODECoefficientPadding.paddedCoefficient
                (ODEPublicGaussianEndpoint.coefficients (constData F) τ gbar ε) 3)) seed))
        (ODEFinalNativeSource.input (constData F) (Sum.inr false) (runMesh F τ gbar ε) Tsl d ∘L
          ODECompiledSource.output E
            (ODESourcePublicNorms.publicCoefficients ‖F.init‖ ‖F.src 0‖ τ (runMesh F τ gbar ε)
              (ODECoefficientPadding.paddedCoefficient
                (ODEPublicGaussianEndpoint.coefficients (constData F) τ gbar ε) 3)))
        x (sol F.T) (s : ℝ) (ImprovedODEQueryBudget.theta (τ * etaH) (τ * etaD) gbar ε)
        (ImprovedODEQueryBudget.logBudget gbar ε) gbar ε := by
    intro x sol hs
    obtain ⟨sol', hs', hne, hmass⟩ := hF.solution x
    have h1 := hC F.init (F.src 0) x rfl rfl (fun h => hJ₀s h x) (fun h => hJbs h x)
      (by rw [hTarget hs']; exact hne) (by rw [hTarget hs', hMass]; exact hmass)
    rwa [hTarget hs] at h1
  exact ⟨Tsl, d, ODECompleteTrial.algorithm (key x₀ sol₀ hs₀).trial, q, _, _, _,
    fun x sol hs => ⟨key x sol hs, rfl⟩⟩

/-- **Every certificate family of the released solver's positive-time branch gives a released
protocol** (Theorem `ode:thm:main`, the branch `ODECompleteEndpoint.PositiveOutcome` of
`ODECompleteEndpoint.solver` on `constData F`): let `F` be a one-stage family in the class (any
`η`, `g ≤ ḡ`) with `T = τ`, and let the source interfaces map a seed to `x₀/‖x₀‖` and `b/‖b‖`.
Let a slot count `Tsl`, a degree `d`, a circuit family `q` over
`constOracle F (RunIndex F τ ḡ ε) (runMesh F τ ḡ ε) Tsl d J₀ Jb`, an iteration count `M`, a
seeded input `ψ` and an output map `Fo` carry the released complete certificate
(`ODECompleteTrial.Certificate`, parameters `Θ`, `ℓ`, `g = ḡ`, `ε`) for every input and every
pair of source vectors of norms `r₀ = ‖x₀‖`, `r_b = ‖b‖` that meets the solver's premises
(target the explicit solution at `T = τ`), exactly as in the body of
`ODECompleteEndpoint.PositiveOutcome`. Then the four-attempt protocol
`ODECompleteTrial.algorithm` of this family (the certificate at any solved input; the protocol
does not depend on the input) is a released protocol (`Protocol.ConstProtocol`) with the same
`Θ`, `ℓ`, `g = ḡ` and `ε`. Every witness `(Tsl, d, E, q)` of the positive-time branch, with
its iteration count, seeded input and output map, is such a family, so the protocol of every
output of that branch is a released protocol; `exists_constProtocol` shows that the released
solver takes that branch, under its hypotheses. -/
theorem constProtocol_of_certificate (F : Family X N Z 1 s) {η τ gbar ε Θ ell : ℝ}
    (hF : F.InClass η gbar) (hT : F.T = τ) {J₀ Jb : X → SysOp N} {seed : EuclideanSpace ℂ N}
    (hJ₀s : F.init ≠ 0 → ∀ x, J₀ x seed = ODEStateNormalization.unitDirection F.init)
    (hJbs : F.src 0 ≠ 0 → ∀ x, Jb x seed = ODEStateNormalization.unitDirection (F.src 0))
    {Tsl d M : ℕ}
    {q : ℕ → MultiOracleCircuit.Program
      (constOracle F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) Tsl d J₀ Jb)}
    {ψ : ODEFinalNativeSource.Physical (RunIndex F τ gbar ε) N Z (runMesh F τ gbar ε) Tsl d}
    {Fo : EuclideanSpace ℂ N →L[ℂ]
      ODEFinalNativeSource.Physical (RunIndex F τ gbar ε) N Z (runMesh F τ gbar ε) Tsl d}
    (hC : ∀ (v b : EuclideanSpace ℂ N) (x : X), ‖v‖ = ‖F.init‖ → ‖b‖ = ‖F.src 0‖ →
      (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
      (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator (constData F) x) v b τ ≠ 0 →
      ‖F.init‖ + τ * ‖F.src 0‖ ≤
        gbar * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator (constData F) x) v b τ‖ →
      ODECompleteTrial.Certificate q M ψ Fo x
        (ODEConstantForcing.solution (ODEPublicSourceMesh.generator (constData F) x) v b τ)
        (s : ℝ) Θ ell gbar ε)
    {x₀ : X} {sol₀ : ℝ → EuclideanSpace ℂ N} (hs₀ : F.Solves x₀ sol₀) :
    ∃ hC₀ : ODECompleteTrial.Certificate q M ψ Fo x₀ (sol₀ F.T) (s : ℝ) Θ ell gbar ε,
      ConstProtocol F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) Tsl d J₀ Jb
        (ODECompleteTrial.algorithm hC₀.trial) Θ ell gbar ε := by
  have hTarget : ∀ {x : X} {sol : ℝ → EuclideanSpace ℂ N}, F.Solves x sol →
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator (constData F) x) F.init
        (F.src 0) τ = sol F.T := by
    intro x sol hs
    rw [Solution.endpoint_eq_constSolution F hs, hT]
  have hMass : ‖F.init‖ + τ * ‖F.src 0‖ = F.mass := by
    rw [Solution.oneStage_mass, hT]
  have key : ∀ x sol, F.Solves x sol →
      ODECompleteTrial.Certificate q M ψ Fo x (sol F.T) (s : ℝ) Θ ell gbar ε := by
    intro x sol hs
    obtain ⟨sol', hs', hne, hmass⟩ := hF.solution x
    have h1 := hC F.init (F.src 0) x rfl rfl (fun h => hJ₀s h x) (fun h => hJbs h x)
      (by rw [hTarget hs']; exact hne) (by rw [hTarget hs', hMass]; exact hmass)
    rwa [hTarget hs] at h1
  exact ⟨key x₀ sol₀ hs₀, q, M, ψ, Fo, fun x sol hs => ⟨key x sol hs, rfl⟩⟩

end

end ConstantODELowerBound.Solver
