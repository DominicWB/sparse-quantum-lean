import SparseLowerBounds.ODE.Parameters

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Definitions of the joint ODE instance (helper of `ODE/JointInstance`)

Manuscript lines 3800-3858. The index type, the hidden stage Hamiltonians, the
candidate states, the explicit solution and the decision observable of the
joint family, with the signatures and bodies of the `ODE/JointInstance`
interface. They live here so that the proof helpers `Helpers/Ode/JointFamily/Eigen`
and `Helpers/Ode/JointFamily/Solution` can use them; `ODE/JointInstance` imports
this module, so every name is available there unchanged.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding
open scoped InnerProductSpace

/-- The ODE index of the joint family: core `(candidate a, dilation bit β,
position)` ⊕ `s` known zero padding indices. -/
abbrev JointIndex (M μ s : ℕ) : Type := (Fin M × Bool × Fin (2 ^ μ)) ⊕ Fin s

variable {M n μ s : ℕ}

/-- `|JointIndex| = 2 M 2^μ + s` (dimension `O(ḡ² s)`, line 3867). -/
theorem card_jointIndex : Fintype.card (JointIndex M μ s) = M * (2 * 2 ^ μ) + s := by
  simp

/-- **The hidden stage Hamiltonian** `H_k = ⊕_a S_{j_{ak}}` (eq. `odel:eq:stages`),
`S_j = [[0, U_j], [U_j†, 0]]`, `U_j = LinearSystems.gadget (2^μ) j` (real).

Each block `S_j` is the Hermitian dilation `LinearSystems.dilation (gadget j)`
(`LinearSystems/OpenClock`, `isHermitian_dilation`, `dilation_mulVec_sectorVec`)
with the sector index `Bool` instead of `Fin 2` (`false ↔ 0`, `true ↔ 1`); the
`Bool` index is kept because the stage table `jointTable` and the locators
`jointLoc` flip the sector by `!β`. The joint index adds the candidate `a` and
the zero padding, so `H_k` is a direct sum of reindexed dilations plus a zero
block, not literally `dilation`; its Hermiticity and eigen relation are proved
directly (`Helpers/Ode/JointFamily/Eigen`) from the gadget facts of `LinearSystems/Gadget` and
`Hamiltonian/Gadget`. -/
def stageHam (j : Positions M n (2 ^ μ)) (k : Fin n) :
    Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ :=
  Matrix.of fun i i' => match i, i' with
    | Sum.inl (a, β, b), Sum.inl (a', β', c) =>
        if a = a' ∧ β ≠ β' then
          (if β then LinearSystems.gadget (2 ^ μ) (j a k) c b
            else LinearSystems.gadget (2 ^ μ) (j a k) b c)
        else 0
    | _, _ => 0

/-- **The generator of stage `k`**: `G_k = i H_k` for the hidden stages `k < n`,
`0` for the idle and source stages. -/
def jointGen (j : Positions M n (2 ^ μ)) (k : Fin (n + 2)) :
    Matrix (JointIndex M μ s) (JointIndex M μ s) ℂ :=
  if hk : (k : ℕ) < n then Complex.I • stageHam j ⟨k, hk⟩ else 0

/-- `|a, ω⟩ = |a⟩ ⊗ |+⟩ ⊗ v` (eq. `odel:eq:dilation`). -/
def candState (M μ s : ℕ) (a : Fin M) : EuclideanSpace ℂ (JointIndex M μ s) :=
  WithLp.toLp 2 fun i => match i with
    | Sum.inl (a', _, c) => if a' = a then ((Real.sqrt 2 : ℂ))⁻¹ * Hamiltonian.alt (2 ^ μ) c else 0
    | Sum.inr _ => 0

/-- `x₀ = u_M ⊗ ω`, `u_M = M^{-1/2} Σ_a |a⟩` (lines 3831-3832). -/
def jointInit (M μ s : ℕ) : EuclideanSpace ℂ (JointIndex M μ s) :=
  ((Real.sqrt M : ℂ))⁻¹ • ∑ a, candState M μ s a

/-- The known source `b = -(-i)^n |u_M, ω⟩` of the final stage (eq. `odel:eq:force`). -/
def jointSrc (M n μ s : ℕ) : EuclideanSpace ℂ (JointIndex M μ s) :=
  (-(-Complex.I) ^ n) • jointInit M μ s

/-- The accumulated phase of candidate `a`:
`Φ_a(t) = Σ_k (-1)^{j_{ak}} clamp(t - kπ/2, 0, π/2)`. -/
def candPhase (j : Positions M n (2 ^ μ)) (a : Fin M) (t : ℝ) : ℝ :=
  ∑ k : Fin n, (-1 : ℝ) ^ (j a k : ℕ) * min (max (t - k * (Real.pi / 2)) 0) (Real.pi / 2)

/-- **The explicit solution** `x(t) = M^{-1/2} Σ_a e^{-iΦ_a(t)} |a, ω⟩ +
clamp(t - (T - 1), 0, 1) b`. -/
def jointSol (M n μ s : ℕ) (T : ℝ) (x : Promised M n (2 ^ μ)) (t : ℝ) :
    EuclideanSpace ℂ (JointIndex M μ s) :=
  ∑ a, (((Real.sqrt M : ℂ))⁻¹ * Complex.exp (-Complex.I * (candPhase x.1 a t : ℂ))) •
      candState M μ s a +
    ((min (max (t - (T - 1)) 0) 1 : ℝ) : ℂ) • jointSrc M n μ s

/-- **The target** `x(T)/‖x(T)‖ = -(-i)^n |a_*, ω⟩`. -/
def jointTarget (M n μ s : ℕ) (x : Promised M n (2 ^ μ)) : EuclideanSpace ℂ (JointIndex M μ s) :=
  (-(-Complex.I) ^ n) • candState M μ s (oddCand x)

/-- **The half indicator** `Σ_a halfSign(a) |a⟩⟨a| ⊗ 1` (padding: `0`), the
decision observable of lines 3887-3888. -/
def halfObs (M μ s : ℕ) :
    EuclideanSpace ℂ (JointIndex M μ s) →L[ℂ] EuclideanSpace ℂ (JointIndex M μ s) :=
  SparseStateOverlap.matrixOperator (Matrix.diagonal fun i => match i with
    | Sum.inl (a, _, _) => (halfSign M a : ℂ)
    | Sum.inr _ => 0)

end

end SparseLowerBounds.ODE
end
