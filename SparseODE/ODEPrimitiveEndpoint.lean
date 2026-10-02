import SparseODE.ODENativeSourceCertificateContinuation2

namespace SparseHamiltonian.ODEPrimitiveEndpoint

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The complete implemented-trial conclusion at a fixed physical schedule.
The schedule and encoding are ordinary declaration parameters, so the native
workspace instances are elaborated before this predicate is used under the
endpoint's existential scale and universal source quantifiers. This definition
contains exactly the trial-family existence, global unitarity, and full
success/error/query certificate; it makes no additional assumption. -/
def TrialOutcome (D : Data X n Z s) (i0 : ι) (N Tslots d : ℕ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (E : ODEFinalNativeSource.SourceSpace ι n N →L[ℂ]
      ODEFinalNativeSource.MatrixSpace ι n Z N Tslots d)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (v target : EuclideanSpace ℂ n) (x : X) (Θ ell g ε : ℝ) : Prop :=
  ∃ q : ℕ → MultiOracleCircuit.Program
      (K := ODEFinalNativeSource.Physical ι n Z N Tslots d)
      (X := X) (L := Query ⊕ Bool)
      (ODEFinalNativeSource.physicalOracle (ι := ι) D N Tslots d J₀ Jb),
    (∀ (j : ℕ) (y : X), IsUnitary ((q j).eval y)) ∧
    ODEPrimitiveSourceJoin.TrialCertificate
      (P := EuclideanSpace ℂ n)
      (R := ODEFinalNativeSource.Physical ι n Z N Tslots d)
      (X := X) (L := Query) q
      (ODEGroverAverage.chosenIterations g)
      (ODEFinalNativeSource.seed D i0 N Tslots d E z c v)
      (ODEFinalNativeSource.output D i0 N Tslots d E z c)
      x target (s : ℝ) Θ ell g (ε / 500)

/-- Specialise the implemented-trial conclusion to the simulator's exact
public schedule and canonical encoding. The parameters are ordinary values;
there are no local schedule lets or additional correctness hypotheses. -/
def OutcomeAtScale (D : Data X n Z s) (i0 : ι) (N : ℕ) (γ ρ T ν : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (z : Option (Fin N) → EuclideanSpace ℂ n) (c : ι → ℂ)
    (v target : EuclideanSpace ℂ n) (x : X) (Θ ell g ε : ℝ) : Prop :=
  TrialOutcome D i0 N
    (ODENativeSimulation.slots (s : ℝ) γ ρ T ν)
    (ODENativeSimulation.degree (s : ℝ) γ ρ T ν) J₀ Jb
    (ODENativeSourceCertificate.encoding (σ := Option (Fin N)) (ι := ι)
      D (none, i0) γ ρ T ν) z c v target x Θ ell g ε

/-- End-to-end primitive implementation conditional only on the explicit
finite LCHS and source-quadrature estimates, together with the ordinary input
promises. The encoding and schedule are chosen before the node/duration table.
The trial certificate gives mean success at least one quarter, public error
at most `ε/500` up to global phase, the improved matrix-query bound with
constant `318504960`, and at most `10*g` calls of each source interface.
No simulation accuracy, source-error certificate, native-control promise or
query-count premise is assumed. -/
theorem native_ode_trials (D : Data X n Z s) (i0 : ι) (N : ℕ)
    (etaH etaD T g ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD)
    (hT : 0 < T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let R := ImprovedODEQueryBudget.radius g ε
    let ν := ImprovedODEQueryBudget.precision g ε
    let ρ := etaH + R * etaD
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ k u : Option (Fin N) × ι → ℝ,
        (∀ a, |k a| ≤ R) → (∀ a, 0 ≤ u a) → (∀ a, u a ≤ T) →
        ∀ c : ι → ℂ, ODECoherentLCU.coefficientMass c = 3 →
          ∀ J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
            (∀ x, IsUnitary (J₀ x)) → (∀ x, IsUnitary (Jb x)) →
            ∀ z : Option (Fin N) → EuclideanSpace ℂ n,
              ∀ v : EuclideanSpace ℂ n, ‖v‖ = 1 →
                ∀ x : X, ∀ target : EuclideanSpace ℂ n,
                  ∀ S : Option (Fin N) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
                    (∀ a, z a ≠ 0 → ODESourcePreparations.branch (J₀ x) (Jb x) N a v =
                      ODEStateNormalization.unitDirection (z a)) →
                    target ≠ 0 → ‖target‖ ≤ ODESourceBranches.mass z →
                    ODESourceBranches.mass z ≤ g * ‖target‖ →
                    (∀ a, ‖(∑ i, c i • ODENativeLCU.branchEvolution D k u x (a, i)) -
                      S a‖ ≤ 2 * ν) →
                    ‖(∑ a, S a (z a)) - target‖ ≤ ν * ODESourceBranches.mass z →
                    OutcomeAtScale D i0 N γ ρ T ν J₀ Jb z c v target x
                      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
                      (ImprovedODEQueryBudget.logBudget g ε) g ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    ODENativeSourceCertificate.native_source_certificate_with_isometry
      (σ := Option (Fin N)) D (none, i0) etaH etaD T g ε
      hH hDiss hρ hT hg hε hεHalf hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hE, _hUnitary, hCertificate⟩ := hTables k u hk hu huT
  intro c hc J₀ Jb hJ₀ hJb z v hv x target S hPrep hTarget hNorm hBudget hLCHS hQuadrature
  let ρ : ℝ := etaH + ImprovedODEQueryBudget.radius g ε * etaD
  let ν : ℝ := ImprovedODEQueryBudget.precision g ε
  let Tslots : ℕ := ODENativeSimulation.slots (s : ℝ) γ ρ T ν
  let d : ℕ := ODENativeSimulation.degree (s : ℝ) γ ρ T ν
  let E : ODEFinalNativeSource.SourceSpace ι n N →L[ℂ]
      ODEFinalNativeSource.MatrixSpace ι n Z N Tslots d :=
    ODENativeSourceCertificate.encoding (σ := Option (Fin N)) (ι := ι) D (none, i0) γ ρ T ν
  have hEncoding : E† ∘L E = 1 := hE
  let pNative : MultiOracleCircuit.Program
      (K := ODEFinalNativeSource.MatrixSpace ι n Z N Tslots d)
      (X := X) (L := Query)
      (ODEFinalNativeSource.matrixOracle (ι := ι) D N Tslots d) := p
  have hBranch : ∀ a : Option (Fin N),
      (ODESourcePreparations.branch (J₀ x) (Jb x) N a)† ∘L
        ODESourcePreparations.branch (J₀ x) (Jb x) N a = 1 :=
    ODESourcePreparations.branch_isometry (J₀ x) (Jb x) N (hJ₀ x).1 (hJb x).1
  have hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N) (pNative.eval x) v target g ε :=
    hCertificate c hc z (ODESourcePreparations.branch (J₀ x) (Jb x) N)
      hBranch v hv hPrep x target S hTarget hNorm hBudget hLCHS hQuadrature
  let q : ℕ → MultiOracleCircuit.Program
      (K := ODEFinalNativeSource.Physical ι n Z N Tslots d)
      (X := X) (L := Query ⊕ Bool)
      (ODEFinalNativeSource.physicalOracle (ι := ι) D N Tslots d J₀ Jb) :=
    ODEFinalNativeSource.trials D i0 N Tslots d pNative J₀ Jb hJ₀ hJb E hEncoding
      z c v target g ε x hCert
  change TrialOutcome D i0 N Tslots d J₀ Jb E z c v target x
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
    (ImprovedODEQueryBudget.logBudget g ε) g ε
  unfold TrialOutcome
  refine ⟨q, ?_, ?_⟩
  · intro j y
    exact (q j).eval_unitary
      (ODEFinalNativeSource.physicalOracle_unitary (ι := ι) D N Tslots d J₀ Jb hJ₀ hJb) y
  · exact ODEFinalNativeSource.primitive_source_certificate D i0 N Tslots d pNative
      J₀ Jb hJ₀ hJb E hEncoding z c v target
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
      (ImprovedODEQueryBudget.logBudget g ε) g ε hg x hCert hCount

end
end SparseHamiltonian.ODEPrimitiveEndpoint
