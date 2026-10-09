import SparseLowerBounds.Hamiltonian.Assembly

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The Schrödinger flow `exp(-iτX)`

Helper module of group spin-chain (`SparseLowerBounds.Hamiltonian.SpinChain`).
For a bounded operator `X` on a complex Hilbert space `V` (in use,
`EuclideanSpace ℂ S`; the lemmas are stated generically because rewriting with
module lemmas is unreliable on the `WithLp` instance path), the curve
`τ ↦ exp((-i τ) • X)` (the release's endpoint form of `evolve`): real-parameter
form, flow property, derivative, unitarity for self-adjoint `X`, and uniqueness
of solutions of `f' = -iXf`.
-/

namespace SparseLowerBounds.Helpers.SpinChain

noncomputable section
open scoped InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- `ℚ`-algebra structure on operators, needed by Mathlib's exponential lemmas
(`NormedSpace.exp` itself does not depend on it). -/
local instance instNormedAlgebraRatCLM : NormedAlgebra ℚ (V →L[ℂ] V) :=
  .restrictScalars ℚ ℂ _

variable (X : V →L[ℂ] V)

omit [CompleteSpace V] in
/-- Product rule over `ℝ` for a curve of `ℂ`-linear operators applied to a curve
of vectors. -/
theorem hasDerivAt_clm_apply_real
    {F : ℝ → (V →L[ℂ] V)}
    {F' : V →L[ℂ] V}
    {f : ℝ → V} {f' : V} {t : ℝ}
    (hF : HasDerivAt F F' t) (hf : HasDerivAt f f' t) :
    HasDerivAt (fun u => F u (f u)) (F' (f t) + F t f') t := by
  have h1 : HasDerivAt (fun u => (F u).restrictScalars ℝ) (F'.restrictScalars ℝ) t :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hF
  exact h1.clm_apply hf

omit [CompleteSpace V] in
theorem flow_eq_exp_smul (τ : ℝ) :
    NormedSpace.exp ((-Complex.I * (τ : ℂ)) • X) = NormedSpace.exp (τ • ((-Complex.I) • X)) := by
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  rfl

omit [CompleteSpace V] in
/-- Rescaling the generator by a real `a` rescales time. -/
theorem flow_smul (a τ : ℝ) :
    NormedSpace.exp ((-Complex.I * (τ : ℂ)) • ((a : ℂ) • X)) =
      NormedSpace.exp ((-Complex.I * ((a * τ : ℝ) : ℂ)) • X) := by
  congr 1
  rw [smul_smul]
  congr 1
  push_cast
  ring

omit [CompleteSpace V] in
theorem flow_zero : NormedSpace.exp ((-Complex.I * ((0 : ℝ) : ℂ)) • X) = 1 := by
  rw [Complex.ofReal_zero, mul_zero, zero_smul, NormedSpace.exp_zero]

theorem flow_add (s t : ℝ) :
    NormedSpace.exp ((-Complex.I * ((s + t : ℝ) : ℂ)) • X) =
      NormedSpace.exp ((-Complex.I * (s : ℂ)) • X) * NormedSpace.exp ((-Complex.I * (t : ℂ)) • X) := by
  rw [← NormedSpace.exp_add_of_commute (((Commute.refl X).smul_left _).smul_right _)]
  congr 1
  push_cast
  rw [mul_add, add_smul]

theorem hasDerivAt_flow (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((-Complex.I * (u : ℂ)) • X))
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • X) * ((-Complex.I) • X)) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := V →L[ℂ] V) ((-Complex.I) • X) t
  rw [← flow_eq_exp_smul] at h
  have hfun : (fun u : ℝ => NormedSpace.exp (u • ((-Complex.I) • X))) =
      fun u : ℝ => NormedSpace.exp ((-Complex.I * (u : ℂ)) • X) :=
    funext fun u => (flow_eq_exp_smul X u).symm
  rw [hfun] at h
  exact h

theorem flow_mem_unitary (hX : star X = X) (τ : ℝ) :
    NormedSpace.exp ((-Complex.I * (τ : ℂ)) • X) ∈
      unitary (V →L[ℂ] V) := by
  refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (𝔸 := V →L[ℂ] V) ?_
  refine IsSelfAdjoint.smul_mem_skewAdjoint ?_ hX
  rw [skewAdjoint.mem_iff]
  simp [Complex.conj_ofReal]

theorem hasDerivAt_flow_neg_apply {f : ℝ → V}
    (hf : ∀ t, HasDerivAt f ((-Complex.I) • X (f t)) t) (t : ℝ) :
    HasDerivAt (fun u : ℝ => NormedSpace.exp ((-Complex.I * ((-u : ℝ) : ℂ)) • X) (f u)) 0 t := by
  have hF : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-Complex.I * ((-u : ℝ) : ℂ)) • X))
      ((-1 : ℝ) • (NormedSpace.exp ((-Complex.I * ((-t : ℝ) : ℂ)) • X) * ((-Complex.I) • X))) t :=
    (hasDerivAt_flow X (-t)).scomp t (hasDerivAt_neg t)
  have := hasDerivAt_clm_apply_real hF (hf t)
  convert this using 1
  simp

theorem flow_apply_eq_of_hasDerivAt {f : ℝ → V}
    (hf : ∀ t, HasDerivAt f ((-Complex.I) • X (f t)) t) (τ : ℝ) :
    NormedSpace.exp ((-Complex.I * (τ : ℂ)) • X) (f 0) = f τ := by
  have hd := hasDerivAt_flow_neg_apply X hf
  have hconst := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) τ 0
  have h0 : ((-(0 : ℝ) : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by rw [neg_zero]
  rw [h0, flow_zero] at hconst
  have h2 : NormedSpace.exp ((-Complex.I * (τ : ℂ)) • X) *
      NormedSpace.exp ((-Complex.I * ((-τ : ℝ) : ℂ)) • X) = 1 := by
    rw [← flow_add, add_neg_cancel, flow_zero]
  calc NormedSpace.exp ((-Complex.I * (τ : ℂ)) • X) (f 0)
      = NormedSpace.exp ((-Complex.I * (τ : ℂ)) • X)
          (NormedSpace.exp ((-Complex.I * ((-τ : ℝ) : ℂ)) • X) (f τ)) := by
        rw [hconst]; rfl
    _ = (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • X) *
          NormedSpace.exp ((-Complex.I * ((-τ : ℝ) : ℂ)) • X)) (f τ) := rfl
    _ = f τ := by rw [h2]; rfl

end

end SparseLowerBounds.Helpers.SpinChain
end
