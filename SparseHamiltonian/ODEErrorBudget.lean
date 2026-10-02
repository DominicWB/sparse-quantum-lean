import SparseHamiltonian.ODEHermitianReduction

/-!
# Finite LCHS and inhomogeneous ODE error budgets

These are analytic error estimates for explicit finite sums of bounded operators
and vectors. They neither postulate a quantum implementation of a controlled
propagator nor hide the error of a source quadrature. Those implementation and
quadrature obligations remain explicit hypotheses.
-/

namespace SparseHamiltonian.ODEErrorBudget

noncomputable section
open scoped BigOperators
open ContinuousLinearMap

section LinearCombination

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Branch errors in a finite complex linear combination add with absolute
coefficient weights. This also applies to bounded operators. -/
theorem lcu_error_le (c : ι → ℂ) (U V : ι → E) (e : ι → ℝ)
    (hError : ∀ i, ‖U i - V i‖ ≤ e i) :
    ‖(∑ i, c i • U i) - ∑ i, c i • V i‖ ≤ ∑ i, ‖c i‖ * e i := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖c i • U i - c i • V i‖ := norm_sum_le _ _
    _ = ∑ i, ‖c i‖ * ‖U i - V i‖ := by
      simp only [← smul_sub, norm_smul]
    _ ≤ ∑ i, ‖c i‖ * e i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hError i) (norm_nonneg _)

/-- A uniform branch tolerance is multiplied by the coefficient one-norm. -/
theorem lcu_uniform_error_le (c : ι → ℂ) (U V : ι → E) (δ : ℝ)
    (hError : ∀ i, ‖U i - V i‖ ≤ δ) :
    ‖(∑ i, c i • U i) - ∑ i, c i • V i‖ ≤ (∑ i, ‖c i‖) * δ := by
  simpa only [Finset.sum_mul] using lcu_error_le c U V (fun _ => δ) hError

/-- A certified LCHS approximation and imperfect Hamiltonian branches combine
additively, with the coefficient normalization exposed in the estimate. -/
theorem lchs_simulation_error_le (c : ι → ℂ) (U V : ι → E) (S : E)
    (α ν δ : ℝ) (hδ : 0 ≤ δ) (hCoeff : ∑ i, ‖c i‖ ≤ α)
    (hLCHS : ‖(∑ i, c i • U i) - S‖ ≤ ν)
    (hSimulation : ∀ i, ‖V i - U i‖ ≤ δ) :
    ‖(∑ i, c i • V i) - S‖ ≤ ν + α * δ := by
  have hBranch : ‖(∑ i, c i • V i) - ∑ i, c i • U i‖ ≤ α * δ :=
    (lcu_uniform_error_le c V U δ hSimulation).trans
      (mul_le_mul_of_nonneg_right hCoeff hδ)
  calc
    _ ≤ ‖(∑ i, c i • V i) - ∑ i, c i • U i‖ +
        ‖(∑ i, c i • U i) - S‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ α * δ + ν := add_le_add hBranch hLCHS
    _ = ν + α * δ := by ring

end LinearCombination

section Source

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The finite source budget, including the initial state. -/
def sourceBudget (x₀ : E) (w : ι → ℝ) (b : ι → E) : ℝ :=
  ‖x₀‖ + ∑ i, w i * ‖b i‖

omit [NormedSpace ℂ E] in
/-- The source budget is nonnegative for nonnegative quadrature weights. -/
theorem sourceBudget_nonneg (x₀ : E) (w : ι → ℝ) (b : ι → E)
    (hw : ∀ i, 0 ≤ w i) : 0 ≤ sourceBudget x₀ w b :=
  add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
    mul_nonneg (hw i) (norm_nonneg _))

/-- An explicit finite variation-of-constants approximation. -/
def finiteDuhamel (U₀ : E →L[ℂ] E) (U : ι → E →L[ℂ] E)
    (x₀ : E) (w : ι → ℝ) (b : ι → E) : E :=
  U₀ x₀ + ∑ i, (w i : ℂ) • U i (b i)

/-- Operator errors act on each source with its actual norm. -/
theorem applied_error_le (U V : E →L[ℂ] E) (x : E) (δ : ℝ)
    (hError : ‖U - V‖ ≤ δ) : ‖U x - V x‖ ≤ δ * ‖x‖ := by
  calc
    _ = ‖(U - V) x‖ := rfl
    _ ≤ ‖U - V‖ * ‖x‖ := (U - V).le_opNorm x
    _ ≤ δ * ‖x‖ := mul_le_mul_of_nonneg_right hError (norm_nonneg _)

/-- Inhomogeneous propagation error is bounded by the source budget. The
number of source nodes does not appear except through that budget. -/
theorem finiteDuhamel_error_le (U₀ V₀ : E →L[ℂ] E)
    (U V : ι → E →L[ℂ] E) (x₀ : E) (w : ι → ℝ) (b : ι → E)
    (δ : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hInitial : ‖U₀ - V₀‖ ≤ δ) (hSource : ∀ i, ‖U i - V i‖ ≤ δ) :
    ‖finiteDuhamel U₀ U x₀ w b - finiteDuhamel V₀ V x₀ w b‖ ≤
      δ * sourceBudget x₀ w b := by
  have hSum := lcu_error_le (fun i => (w i : ℂ))
    (fun i => U i (b i)) (fun i => V i (b i))
    (fun i => δ * ‖b i‖) (fun i => applied_error_le _ _ _ _ (hSource i))
  have hSum' :
      ‖(∑ i, (w i : ℂ) • U i (b i)) - ∑ i, (w i : ℂ) • V i (b i)‖ ≤
        δ * ∑ i, w i * ‖b i‖ := by
    calc
      _ ≤ ∑ i, ‖(w i : ℂ)‖ * (δ * ‖b i‖) := hSum
      _ = δ * ∑ i, w i * ‖b i‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw _),
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  calc
    _ = ‖(U₀ x₀ - V₀ x₀) +
        ((∑ i, (w i : ℂ) • U i (b i)) - ∑ i, (w i : ℂ) • V i (b i))‖ := by
      congr 1
      unfold finiteDuhamel
      abel
    _ ≤ ‖U₀ x₀ - V₀ x₀‖ +
        ‖(∑ i, (w i : ℂ) • U i (b i)) - ∑ i, (w i : ℂ) • V i (b i)‖ :=
      norm_add_le _ _
    _ ≤ δ * ‖x₀‖ + δ * ∑ i, w i * ‖b i‖ :=
      add_le_add (applied_error_le _ _ _ _ hInitial) hSum'
    _ = δ * sourceBudget x₀ w b := by unfold sourceBudget; ring

/-- A separate, certified source quadrature error is added exactly once. -/
theorem source_quadrature_error_le (U₀ V₀ : E →L[ℂ] E)
    (U V : ι → E →L[ℂ] E) (x₀ x : E) (w : ι → ℝ) (b : ι → E)
    (δ q : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hInitial : ‖U₀ - V₀‖ ≤ δ) (hSource : ∀ i, ‖U i - V i‖ ≤ δ)
    (hQuadrature : ‖finiteDuhamel V₀ V x₀ w b - x‖ ≤ q) :
    ‖finiteDuhamel U₀ U x₀ w b - x‖ ≤ δ * sourceBudget x₀ w b + q := by
  exact (norm_sub_le_norm_sub_add_norm_sub _ (finiteDuhamel V₀ V x₀ w b) _).trans
    (add_le_add (finiteDuhamel_error_le U₀ V₀ U V x₀ w b δ hw hInitial hSource)
      hQuadrature)

/-- Three sources of error: certified LCHS approximation, Hamiltonian branch
simulation, and certified source quadrature. This theorem does not infer a
quadrature certificate from regularity assumptions. -/
theorem lchs_source_error_le {κ : Type*} [Fintype κ]
    (c : κ → ℂ) (U₀ V₀ : κ → E →L[ℂ] E)
    (U V : ι → κ → E →L[ℂ] E)
    (S₀ : E →L[ℂ] E) (S : ι → E →L[ℂ] E)
    (x₀ x : E) (w : ι → ℝ) (b : ι → E) (α ν δ q : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hδ : 0 ≤ δ) (hCoeff : ∑ k, ‖c k‖ ≤ α)
    (hLCHS₀ : ‖(∑ k, c k • U₀ k) - S₀‖ ≤ ν)
    (hLCHS : ∀ i, ‖(∑ k, c k • U i k) - S i‖ ≤ ν)
    (hSimulation₀ : ∀ k, ‖V₀ k - U₀ k‖ ≤ δ)
    (hSimulation : ∀ i k, ‖V i k - U i k‖ ≤ δ)
    (hQuadrature : ‖finiteDuhamel S₀ S x₀ w b - x‖ ≤ q) :
    ‖finiteDuhamel (∑ k, c k • V₀ k) (fun i => ∑ k, c k • V i k) x₀ w b - x‖ ≤
      (ν + α * δ) * sourceBudget x₀ w b + q := by
  exact source_quadrature_error_le _ _ _ _ _ _ _ _ _ _ hw
    (lchs_simulation_error_le c U₀ V₀ S₀ α ν δ hδ hCoeff hLCHS₀ hSimulation₀)
    (fun i => lchs_simulation_error_le c (U i) (V i) (S i) α ν δ hδ hCoeff
      (hLCHS i) (hSimulation i)) hQuadrature

/-- With coefficient norm at most three, common LCHS/simulation tolerance,
and source quadrature at most that tolerance times the source budget, the
combined vector error is at most five times the common tolerance budget. -/
theorem common_tolerance_error_le {κ : Type*} [Fintype κ]
    (c : κ → ℂ) (U₀ V₀ : κ → E →L[ℂ] E)
    (U V : ι → κ → E →L[ℂ] E)
    (S₀ : E →L[ℂ] E) (S : ι → E →L[ℂ] E)
    (x₀ x : E) (w : ι → ℝ) (b : ι → E) (ν : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hν : 0 ≤ ν) (hCoeff : ∑ k, ‖c k‖ ≤ 3)
    (hLCHS₀ : ‖(∑ k, c k • U₀ k) - S₀‖ ≤ ν)
    (hLCHS : ∀ i, ‖(∑ k, c k • U i k) - S i‖ ≤ ν)
    (hSimulation₀ : ∀ k, ‖V₀ k - U₀ k‖ ≤ ν)
    (hSimulation : ∀ i k, ‖V i k - U i k‖ ≤ ν)
    (hQuadrature : ‖finiteDuhamel S₀ S x₀ w b - x‖ ≤ ν * sourceBudget x₀ w b) :
    ‖finiteDuhamel (∑ k, c k • V₀ k) (fun i => ∑ k, c k • V i k) x₀ w b - x‖ ≤
      5 * ν * sourceBudget x₀ w b := by
  calc
    _ ≤ (ν + 3 * ν) * sourceBudget x₀ w b + ν * sourceBudget x₀ w b :=
      lchs_source_error_le c U₀ V₀ U V S₀ S x₀ x w b 3 ν ν
        (ν * sourceBudget x₀ w b) hw hν hCoeff hLCHS₀ hLCHS hSimulation₀
        hSimulation hQuadrature
    _ = 5 * ν * sourceBudget x₀ w b := by ring

end Source
end
end SparseHamiltonian.ODEErrorBudget
