import ConstantODELowerBound.Oracle
import SparseLowerBounds.ODE.Uniqueness

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# One-stage families as constant-coefficient equations of Theorem `ode:thm:main`

Manuscript lines 4094-4097 (eq. `odel:eq:ode`, `-A = D + iH`, `D ⪰ 0`) and 3013-3033 (Theorem
`ode:thm:main`: `A`, `b` time independent, `B = ‖x₀‖ + T‖b‖`, `g = B/‖x(T)‖`, split bounds
`η_H`, `η_D` on the Hermitian and dissipative parts). A one-stage family of the ODE model
(`SparseLowerBounds.ODE.Family X N Z 1 s`) is a constant-coefficient equation: on input `x` the
released solver's generator `ODEPublicSourceMesh.generator (constData F) x = -G_0(x)` and the
released explicit solution `ODEConstantForcing.solution` solve the family's instance.

* `oneStage_T`, `oneStage_mass`: `T = len 0`, `B = ‖x₀‖ + T ‖b‖`.
* `constSolution_solves`: `t ↦ solution(-G_0(x), x₀, b_0, t)` solves instance `x`
  (`ODEConstantForcing.solution_hasDerivAt`); `endpoint_eq_constSolution`: hence every solution
  ends at it (`Family.solves_endpoint_unique`).
* `hamiltonianPart_of_isHermitian`, `dissipativePart_of_isHermitian`: for a Hermitian matrix
  `M` (the PSD generators `D_X`), `η_H`-part `0` and `η_D`-part `M`;
  `dissipativePart_nonneg_of_accretive`: an accretive generator has a positive semidefinite
  dissipative part, the solver's hypothesis `D ⪰ 0`.
-/

namespace ConstantODELowerBound.Solution

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open ConstantODELowerBound.Oracle
open scoped InnerProduct InnerProductSpace

variable {X N Z : Type} [Fintype N] [DecidableEq N] {s : ℕ}

/-- The final time of a one-stage family is the length of its stage. -/
theorem oneStage_T (F : Family X N Z 1 s) : F.T = F.len 0 := by
  rw [Family.T_eq_sum, Fin.sum_univ_one]

/-- The source mass of a one-stage family is `‖x₀‖ + T ‖b‖`. -/
theorem oneStage_mass (F : Family X N Z 1 s) : F.mass = ‖F.init‖ + F.T * ‖F.src 0‖ := by
  rw [Family.mass, Fin.sum_univ_one, oneStage_T]

/-- The released constant-coefficient generator of `constData F` is `-G_0(x)`. -/
theorem generator_constData (F : Family X N Z 1 s) (x : X) :
    ODEPublicSourceMesh.generator (constData F) x = -F.gen x 0 := rfl

/-- **The released explicit solution solves the one-stage instance**: `t ↦ solution(-G_0(x), x₀,
b_0, t)` starts at `x₀` and satisfies `ẋ = -G_0(x) x + b_0` on the stage. -/
theorem constSolution_solves (F : Family X N Z 1 s) (x : X) :
    F.Solves x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator (constData F) x)
      F.init (F.src 0)) := by
  refine ⟨ODEConstantForcing.solution_zero _ _ _, fun k => ?_⟩
  obtain rfl : k = 0 := Subsingleton.elim _ _
  intro u _
  have hd := ODEConstantForcing.solution_hasDerivAt
    (ODEPublicSourceMesh.generator (constData F) x) F.init (F.src 0) u
  refine (hd.congr_deriv ?_).hasDerivWithinAt
  rw [generator_constData, neg_apply]

/-- **Every solution of a one-stage instance ends at the released explicit solution.** -/
theorem endpoint_eq_constSolution (F : Family X N Z 1 s) {x : X} {sol : ℝ → EuclideanSpace ℂ N}
    (hs : F.Solves x sol) :
    sol F.T = ODEConstantForcing.solution (ODEPublicSourceMesh.generator (constData F) x)
      F.init (F.src 0) F.T :=
  F.solves_endpoint_unique hs (constSolution_solves F x)

omit [Fintype N] [DecidableEq N] in
/-- The Hermitian (imaginary) part of a Hermitian matrix is `0`. -/
theorem hamiltonianPart_of_isHermitian {M : Matrix N N ℂ} (hM : M.IsHermitian) :
    ODEMatrixEnergy.hamiltonianPart M = 0 := by
  ext i j
  rw [ODEMatrixEnergy.hamiltonianPart_apply, hM.apply i j, sub_self, mul_zero, Matrix.zero_apply]

omit [Fintype N] [DecidableEq N] in
/-- The dissipative (real) part of a Hermitian matrix is the matrix itself. -/
theorem dissipativePart_of_isHermitian {M : Matrix N N ℂ} (hM : M.IsHermitian) :
    ODEMatrixEnergy.dissipativePart M = M := by
  ext i j
  rw [ODEMatrixEnergy.dissipativePart_apply, hM.apply i j]
  ring

omit [DecidableEq N] in
/-- **An accretive generator has a positive semidefinite dissipative part**: if
`0 ≤ Re ⟪v, M v⟫` for all `v`, then `0 ≤ Re ⟪w, ((M + M†)/2) w⟫` for all `w` (the solver's
hypothesis `D ⪰ 0`). -/
theorem dissipativePart_nonneg_of_accretive {M : Matrix N N ℂ}
    (hM : TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator M))
    (w : EuclideanSpace ℂ N) :
    0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart M) w)).re := by
  rw [ODEMatrixEnergy.matrixOperator_dissipativePart,
    ODEHermitianReduction.real_inner_dissipativePart]
  exact hM w

end

end ConstantODELowerBound.Solution
