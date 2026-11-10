import SparseHamiltonian.FiniteReferenceLift

/-!
# Manuscript quantities and output-error notions

The expressions of the manuscript's bounds and the error notions of its theorems, written once
so that the conformance theorems can quote them. Every definition is a plain formula; the
equation labels are those of the manuscript.

* `logInv ε = log(1/ε)` (the manuscript's `L`); `hRatio τ ε = log(e + L/τ)` (its `h`, eq.
  `hsl:eq:parameters`); `hslR τ ε = L/h` (its `r`, eqs. `hsl:eq:parameters` and
  `odel:eq:precision`).
* `mainBound`: the three-term query expression of eqs. `hs:eq:mainbound` and `hs:eq:timebound`.
* `optimalBound`: eq. `hs:eq:optimal-bound` (and the shape of eq. `hsl:eq:main`).
* `twoNormBound`: eq. `hs:eq:two-norm-bound` (the query scale `Q_μ` of eq. `gate:eq:query-scale`).
* `unitaryBound`, `unitaryOptimalBound`: eqs. `hs:eq:unitarybound` and
  `hs:eq:unitary-optimal-bound`.
* `FullOutputError A J V ε`: eq. `hs:eq:fullerror`, the error of the circuit `A` on the clean
  encoding `J` of every normalised input, all work registers included;
  `ReferenceOutputError`: the same with an untouched finite reference register of any dimension.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian

/-- `L = log(1/ε)`. -/
def logInv (ε : ℝ) : ℝ := Real.log (1 / ε)

/-- `h = log(e + L/τ)` (eq. `hsl:eq:parameters`). -/
def hRatio (τ ε : ℝ) : ℝ := Real.log (Real.exp 1 + logInv ε / τ)

/-- `r = L/h` (eqs. `hsl:eq:parameters` and `odel:eq:precision`). -/
def hslR (τ ε : ℝ) : ℝ := logInv ε / hRatio τ ε

/-- Eqs. `hs:eq:mainbound` and `hs:eq:timebound`: `√s τ + √(s τ L) + L`. -/
def mainBound (s τ ε : ℝ) : ℝ :=
  Real.sqrt s * τ + Real.sqrt (s * τ * logInv ε) + logInv ε

/-- Eq. `hs:eq:optimal-bound`: `√s τ + √(s τ L / h) + L / h`, `h = log(e + L/τ)`. -/
def optimalBound (s τ ε : ℝ) : ℝ :=
  Real.sqrt s * τ + Real.sqrt (s * τ * logInv ε / hRatio τ ε) + logInv ε / hRatio τ ε

/-- Eq. `hs:eq:two-norm-bound` (and the query scale `Q_μ` of eq. `gate:eq:query-scale`):
`√s η|t| + √(s μ|t| L / log(e + μL/(η²|t|))) + L / log(e + μL/(η²|t|))`. -/
def twoNormBound (s η μ t ε : ℝ) : ℝ :=
  Real.sqrt s * η * |t| +
    Real.sqrt (s * μ * |t| * logInv ε /
      Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|))) +
    logInv ε / Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|))

/-- Eq. `hs:eq:unitarybound`: `√(N L) + L / log(e + L/N)`. -/
def unitaryBound (N ε : ℝ) : ℝ :=
  Real.sqrt (N * logInv ε) + logInv ε / Real.log (Real.exp 1 + logInv ε / N)

/-- Eq. `hs:eq:unitary-optimal-bound`: `√(N L / log(e + L)) + L / log(e + L)`. -/
def unitaryOptimalBound (N ε : ℝ) : ℝ :=
  Real.sqrt (N * logInv ε / Real.log (Real.exp 1 + logInv ε)) +
    logInv ε / Real.log (Real.exp 1 + logInv ε)

section Errors

variable {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Full-output error** (eq. `hs:eq:fullerror`): for every normalised input `ψ`, the circuit
`A` applied to the clean encoding `J ψ` (input and clean work registers) is within `ε` of the
clean encoding of `V ψ`; every work register is part of the output. -/
def FullOutputError (A : K →L[ℂ] K) (J : P →L[ℂ] K) (V : P →L[ℂ] P) (ε : ℝ) : Prop :=
  ∀ ψ : P, ‖ψ‖ = 1 → ‖A (J ψ) - J (V ψ)‖ ≤ ε

/-- **Full-output error with an untouched reference**: the same for every normalised, possibly
entangled, state of the system and a finite reference register `R`, on which nothing acts. -/
def ReferenceOutputError (R : Type) [Fintype R] (A : K →L[ℂ] K) (J : P →L[ℂ] K)
    (V : P →L[ℂ] P) (ε : ℝ) : Prop :=
  ∀ ψ : PiLp 2 (fun _ : R => P), ‖ψ‖ = 1 →
    ‖FiniteReferenceLift.lift A (FiniteReferenceLift.lift J ψ) -
      FiniteReferenceLift.lift J (FiniteReferenceLift.lift V ψ)‖ ≤ ε

/-- An operator-norm bound gives the full-output error. -/
theorem fullOutputError_of_norm {A : K →L[ℂ] K} {J : P →L[ℂ] K} {V : P →L[ℂ] P} {ε : ℝ}
    (h : ‖A ∘L J - J ∘L V‖ ≤ ε) : FullOutputError A J V ε := by
  intro ψ hψ
  have h1 : A (J ψ) - J (V ψ) = (A ∘L J - J ∘L V) ψ := rfl
  rw [h1]
  calc ‖(A ∘L J - J ∘L V) ψ‖ ≤ ‖A ∘L J - J ∘L V‖ * ‖ψ‖ := le_opNorm _ _
    _ = ‖A ∘L J - J ∘L V‖ := by rw [hψ, mul_one]
    _ ≤ ε := h

/-- An operator-norm bound gives the full-output error with every untouched finite
reference. -/
theorem referenceOutputError_of_norm {A : K →L[ℂ] K} {J : P →L[ℂ] K} {V : P →L[ℂ] P} {ε : ℝ}
    (h : ‖A ∘L J - J ∘L V‖ ≤ ε) (R : Type) [Fintype R] : ReferenceOutputError R A J V ε := by
  intro ψ hψ
  simpa only [hψ, mul_one] using FiniteReferenceLift.same_embedding_error_le A J V ε h ψ

end Errors

end

end ManuscriptConformance
