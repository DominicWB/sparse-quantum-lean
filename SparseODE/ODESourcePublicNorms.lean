import SparseODE.ODEMainEndpoint

/-!
# Public source coefficients for an arbitrary forcing mesh

The normalized joint coefficients depend on the initial and forcing vectors
only through their supplied norms. These identities allow one coefficient
state, output embedding and amplification circuit to be fixed before the
unknown source directions. The mesh cardinality is arbitrary and positive.

-/

namespace SparseHamiltonian.ODESourcePublicNorms

noncomputable section
open ContinuousLinearMap
open scoped BigOperators

variable {σ ι P : Type*} [Fintype σ] [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- Norms alone determine the total unpropagated source mass. -/
theorem mass_eq_of_norms_eq (z₁ z₂ : σ → P)
    (hNorm : ∀ a, ‖z₁ a‖ = ‖z₂ a‖) :
    ODESourceBranches.mass z₁ = ODESourceBranches.mass z₂ := by
  unfold ODESourceBranches.mass
  exact Finset.sum_congr rfl (fun a _ => hNorm a)

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- Norms alone determine every source-loading probability, including when
all branches vanish. No positive-mass premise is needed for equality. -/
theorem probability_eq_of_norms_eq (z₁ z₂ : σ → P)
    (hNorm : ∀ a, ‖z₁ a‖ = ‖z₂ a‖) :
    ODESourceBranches.probability z₁ = ODESourceBranches.probability z₂ := by
  funext a
  unfold ODESourceBranches.probability
  rw [hNorm a, mass_eq_of_norms_eq z₁ z₂ hNorm]

omit [Fintype ι] [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- The joint source/frequency coefficients have no source-direction
information beyond the list of branch norms. -/
theorem coefficients_eq_of_norms_eq (z₁ z₂ : σ → P) (c : ι → ℂ)
    (hNorm : ∀ a, ‖z₁ a‖ = ‖z₂ a‖) :
    ODEActualSourceError.coefficients z₁ c =
      ODEActualSourceError.coefficients z₂ c := by
  unfold ODEActualSourceError.coefficients
  exact congrArg (fun w : σ → ℝ => ODESourceCoefficients.productCoeff w c)
    (probability_eq_of_norms_eq z₁ z₂ hNorm)

/-- Source probabilities expressed using only the known norms and public
quadrature. The forcing labels retain their individual mesh weights. -/
def publicProbability (r₀ rb T : ℝ) (N : ℕ) : Option (Fin N) → ℝ
  | none => r₀ / (r₀ + T * rb)
  | some i => (ODESourceQuadrature.weight T N i * rb) / (r₀ + T * rb)

/-- The complete coefficient table can be fixed before either source
vector's direction is specified. -/
def publicCoefficients (r₀ rb T : ℝ) (N : ℕ) (c : ι → ℂ) :
    Option (Fin N) × ι → ℂ :=
  ODESourceCoefficients.productCoeff (publicProbability r₀ rb T N) c

theorem publicProbability_nonneg (r₀ rb T : ℝ) (N : ℕ)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hT : 0 ≤ T) :
    ∀ a, 0 ≤ publicProbability r₀ rb T N a := by
  have hB : 0 ≤ r₀ + T * rb := add_nonneg h₀ (mul_nonneg hT hb)
  intro a
  cases a with
  | none => exact div_nonneg h₀ hB
  | some i =>
      exact div_nonneg
        (mul_nonneg (ODESourceQuadrature.weight_nonneg T hT N i) hb) hB

theorem sum_publicProbability (r₀ rb T : ℝ) (N : ℕ)
    (hN : 0 < N) (hB : 0 < r₀ + T * rb) :
    (∑ a, publicProbability r₀ rb T N a) = 1 := by
  rw [Fintype.sum_option]
  simp only [publicProbability]
  rw [← Finset.sum_div, ← Finset.sum_mul,
    ODESourceQuadrature.sum_weights T N hN, ← add_div, div_self hB.ne']

/-- Public coefficient mass is exactly three, independently of source
mesh size and source directions. -/
theorem publicCoefficients_mass (r₀ rb T : ℝ) (N : ℕ)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hT : 0 ≤ T)
    (hN : 0 < N) (hB : 0 < r₀ + T * rb)
    (c : ι → ℂ) (hc : ODECoherentLCU.coefficientMass c = 3) :
    ODECoherentLCU.coefficientMass (publicCoefficients r₀ rb T N c) = 3 := by
  rw [publicCoefficients, ODESourceCoefficients.coefficientMass_product
    (publicProbability r₀ rb T N) c
    (publicProbability_nonneg r₀ rb T N h₀ hb hT),
    sum_publicProbability r₀ rb T N hN hB, one_mul, hc]

omit [CompleteSpace P] in
/-- On every valid source mesh the actual norm probabilities equal the
public values computed from the two supplied source norms. -/
theorem actual_probability_eq (v b : P) (r₀ rb T : ℝ) (N : ℕ)
    (hT : 0 ≤ T) (hN : 0 < N) (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb) :
    ODESourceBranches.probability (ODESourceBranches.sourceVector v b T N) =
      publicProbability r₀ rb T N := by
  have hmass : ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) =
      r₀ + T * rb := by
    rw [ODESourceBranches.mass_sourceVector v b T hT N hN, hv, hb]
  funext a
  cases a with
  | none =>
      simp only [ODESourceBranches.probability, ODESourceBranches.sourceVector,
        publicProbability, hmass, hv]
  | some i =>
      simp only [ODESourceBranches.probability, ODESourceBranches.sourceVector,
        publicProbability, hmass, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ODESourceQuadrature.weight_nonneg T hT N i), hb]

omit [Fintype ι] [CompleteSpace P] in
/-- The actual joint coefficient table agrees exactly with the public
norm-only table for every positive forcing mesh cardinality. -/
theorem actual_coefficients_eq (v b : P) (r₀ rb T : ℝ) (N : ℕ)
    (hT : 0 ≤ T) (hN : 0 < N) (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb)
    (c : ι → ℂ) :
    ODEActualSourceError.coefficients (ODESourceBranches.sourceVector v b T N) c =
      publicCoefficients r₀ rb T N c := by
  unfold ODEActualSourceError.coefficients publicCoefficients
  exact congrArg (fun w : Option (Fin N) → ℝ =>
    ODESourceCoefficients.productCoeff w c)
    (actual_probability_eq v b r₀ rb T N hT hN hv hb)

omit [Fintype ι] [CompleteSpace P] in
/-- Changing both source directions while keeping their supplied norms
fixed leaves the whole coefficient table unchanged. -/
theorem source_coefficients_eq (v₁ b₁ v₂ b₂ : P) (T : ℝ) (N : ℕ)
    (hT : 0 ≤ T) (hN : 0 < N) (hv : ‖v₁‖ = ‖v₂‖) (hb : ‖b₁‖ = ‖b₂‖)
    (c : ι → ℂ) :
    ODEActualSourceError.coefficients (ODESourceBranches.sourceVector v₁ b₁ T N) c =
      ODEActualSourceError.coefficients (ODESourceBranches.sourceVector v₂ b₂ T N) c := by
  exact (actual_coefficients_eq v₁ b₁ ‖v₂‖ ‖b₂‖ T N hT hN hv hb c).trans
    (actual_coefficients_eq v₂ b₂ ‖v₂‖ ‖b₂‖ T N hT hN rfl rfl c).symm

end
end SparseHamiltonian.ODESourcePublicNorms
