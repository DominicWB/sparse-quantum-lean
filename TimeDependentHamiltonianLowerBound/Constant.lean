import TimeDependentHamiltonian.Corollaries
import IntegrablePathSimulation.Propagator.Classical
import IntegrablePathSimulation.Propagator.Uniqueness
import SparseLowerBounds.Hamiltonian.SpinChain

set_option autoImplicit false

/-!
# Constant time-indexed data, constant paths and their propagators

The paragraph "Regularity and coherent parameters" after Theorem `hs:thm:time` ends: "The
lower bound in Theorem `hsl:thm:main` also applies to this class, since its time-independent
hard instances satisfy the new assumptions with `β = δ_val = 0`." This module gives the
embedding of time-independent native sparse data `D : Data X N Z s` into the time-dependent
access model of `hs:thm:time` (equation `hs:eq:timeaccess`).

* `constData D M : Data (X × Fin M) N Z s`: every sample `r < M` is the instance itself (the
  fields of `D` read at the first component, as the released one-stage ODE data
  `SparseLowerBounds.ODE.hamData`, outside this library's imports, here without the factor
  `i`).
* The native primitives of the sample `(x, r)` are those of `x` (`oracles_constData`,
  `cayley_constData`, by `rfl`), so the released coherent sampled-time oracle
  `∑_r |r⟩⟨r| ⊗ O_r` (`TimeDependent.sampledOracle`) is the native Cayley-layout oracle of `D`
  acting with an untouched spectator time register (`sampledOracle_constData`, also `rfl`):
  `timeIndexed (fun _ => F)` is literally `LookupFromBasisOracle.spectator (S := Fin M) F`.
* `constPath D x u = D.matrix x`, the constant path of instance `x`.
* `constProp H u = exp(-iuH)`: it solves `U' = -iHU` on every interval (`solvesOn_constProp`),
  starts at the identity (`constProp_zero`) and is a propagator in the integral sense
  (`isPropagator_constProp`); every classical or integral-sense propagator of the constant
  path on `[0, T]` equals it at `T` (`propagator_eq_constProp`, `isPropagator_eq_constProp`,
  from the released uniqueness `IntegrablePathSimulation.Propagator.IsPropagator.eqOn`). The
  released lower-bound target `SparseLowerBounds.Hamiltonian.evolve H τ` is `constProp` by
  definition (`evolve_eq_constProp`).
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding
open MeasureTheory Set

/-! ### Constant time-indexed data -/

section Data

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}

/-- **Constant time-indexed data**: the sample `(x, r)` is the time-independent instance `x`,
for every `r < M` (same slots, scale, decoder, words, locators and locator oracles). -/
def constData (D : Data X N Z s) (M : ℕ) : Data (X × Fin M) N Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix p := D.matrix p.1
  table p := D.table p.1
  decode := D.decode
  decode_bound := D.decode_bound
  decoded p := D.decoded p.1
  rowloc p := D.rowloc p.1
  colloc p := D.colloc p.1
  row_injective p := D.row_injective p.1
  column_injective p := D.column_injective p.1
  row_covers p := D.row_covers p.1
  column_covers p := D.column_covers p.1
  rowOracle p := D.rowOracle p.1
  columnOracle p := D.columnOracle p.1
  row_unitary p := D.row_unitary p.1
  column_unitary p := D.column_unitary p.1
  row_valid p := D.row_valid p.1
  column_valid p := D.column_valid p.1

/-- Every sample of the constant data is the instance: `H̃_r = H_x`. -/
@[simp] theorem constData_matrix (D : Data X N Z s) (M : ℕ) (x : X) (r : Fin M) :
    (constData D M).matrix (x, r) = D.matrix x := rfl

/-- The words of every sample are those of the instance. -/
@[simp] theorem constData_table (D : Data X N Z s) (M : ℕ) (x : X) (r : Fin M) :
    (constData D M).table (x, r) = D.table x := rfl

/-- The row location oracle of every sample is that of the instance. -/
theorem constData_rowOracle (D : Data X N Z s) (M : ℕ) (x : X) (r : Fin M) :
    (constData D M).rowOracle (x, r) = D.rowOracle x := rfl

/-- The column location oracle of every sample is that of the instance. -/
theorem constData_columnOracle (D : Data X N Z s) (M : ℕ) (x : X) (r : Fin M) :
    (constData D M).columnOracle (x, r) = D.columnOracle x := rfl

/-- Hermitian instances give Hermitian samples. -/
theorem constData_hermitian (D : Data X N Z s) (M : ℕ) (hH : ∀ x, (D.matrix x).IsHermitian)
    (y : X × Fin M) : ((constData D M).matrix y).IsHermitian :=
  hH y.1

/-- Row norms at most `η` give samples with row norms at most `η`. -/
theorem constData_row (D : Data X N Z s) (M : ℕ) {η : ℝ}
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (y : X × Fin M) (i : N) :
    ∑ j, ‖(constData D M).matrix y i j‖ ^ 2 ≤ η ^ 2 :=
  hrow y.1 i

/-- Column norms at most `η` give samples with column norms at most `η`. -/
theorem constData_col (D : Data X N Z s) (M : ℕ) {η : ℝ}
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (y : X × Fin M) (j : N) :
    ∑ i, ‖(constData D M).matrix y i j‖ ^ 2 ≤ η ^ 2 :=
  hcol y.1 j

variable [Fintype Z] [AddCommGroup Z]

/-- **The native primitives of a sample are those of the instance** (they read only words,
locators and locator oracles). -/
theorem oracles_constData (D : Data X N Z s) (M : ℕ) (l : Query) (x : X) (r : Fin M) :
    oracles (constData D M) l (x, r) = oracles D l x := by
  cases l <;> rfl

/-- The released native Cayley-layout oracle of a sample is that of the instance. -/
theorem cayley_constData (D : Data X N Z s) (M : ℕ) (l : Query) (x : X) (r : Fin M) :
    NativeCayleyProgram.oracle (constData D M) l (x, r) = NativeCayleyProgram.oracle D l x := by
  cases l <;> rfl

/-- **The coherent sampled-time oracle of constant data is a spectator form** (equation
`hs:eq:timeaccess`): `∑_r |r⟩⟨r| ⊗ O_r = 1_{Fin M} ⊗ O` with `O` the native Cayley-layout
oracle of the instance, the time register being an untouched spectator. -/
theorem sampledOracle_constData (D : Data X N Z s) (M : ℕ) (l : Query) (x : X) :
    TimeDependent.sampledOracle (constData D M) l x =
      LookupFromBasisOracle.spectator (S := Fin M) (NativeCayleyProgram.oracle D l x) := by
  cases l <;> rfl

end Data

/-! ### The constant path -/

section Path

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}

/-- **The constant path** of instance `x`: `H(u) = D.matrix x` at every time. -/
def constPath (D : Data X N Z s) : X → ℝ → Matrix N N ℂ := fun x _ => D.matrix x

/-- The constant path at every time is the instance. -/
@[simp] theorem constPath_apply (D : Data X N Z s) (x : X) (u : ℝ) :
    constPath D x u = D.matrix x := rfl

end Path

/-! ### The propagator of a constant path -/

section Propagator

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The propagator of the constant path** `H(u) = H`: `U(u) = exp(-iuH)`. -/
def constProp (H : P →L[ℂ] P) (u : ℝ) : P →L[ℂ] P :=
  NormedSpace.exp ((-Complex.I * (u : ℂ)) • H)

omit [CompleteSpace P] in
/-- The constant propagator starts at the identity. -/
theorem constProp_zero (H : P →L[ℂ] P) : constProp H 0 = 1 := by
  rw [constProp, Complex.ofReal_zero, mul_zero, zero_smul, NormedSpace.exp_zero]

omit [CompleteSpace P] in
/-- `exp(-iuH) = exp(u • (-iH))`. -/
theorem constProp_eq_exp_smul (H : P →L[ℂ] P) (u : ℝ) :
    constProp H u = NormedSpace.exp (u • ((-Complex.I) • H)) := by
  rw [constProp]
  congr 1
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, mul_comm]
  rfl

/-- The constant propagator solves `U' = -iHU` at every time. -/
theorem hasDerivAt_constProp (H : P →L[ℂ] P) (u : ℝ) :
    HasDerivAt (constProp H) ((-Complex.I) • (H * constProp H u)) u := by
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) ((-Complex.I) • H) u
  have hfun : (fun v : ℝ => NormedSpace.exp (v • ((-Complex.I) • H))) = constProp H :=
    funext fun v => (constProp_eq_exp_smul H v).symm
  rw [hfun, ← constProp_eq_exp_smul, smul_mul_assoc] at h
  exact h

/-- **The constant propagator solves the Schrödinger equation on every interval**
(`TimeDependent.SolvesOn`, the propagator notion of `hs:thm:time`). -/
theorem solvesOn_constProp (H : P →L[ℂ] P) (a b : ℝ) :
    TimeDependent.SolvesOn (fun _ => H) (constProp H) a b :=
  fun u _ => (hasDerivAt_constProp H u).hasDerivWithinAt

/-- **The constant propagator is a propagator in the integral sense**
(`IntegrablePathSimulation.Propagator.IsPropagator`, the propagator notion for integrable
paths). -/
theorem isPropagator_constProp (H : P →L[ℂ] P) {T : ℝ} (hT : 0 ≤ T) :
    IntegrablePathSimulation.Propagator.IsPropagator (fun _ => H) (constProp H) T :=
  IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn hT (constProp_zero H)
    (solvesOn_constProp H 0 T) intervalIntegrable_const

/-- **Every integral-sense propagator of the constant path on `[0, T]` is `exp(-iTH)` at `T`**
(released uniqueness `IntegrablePathSimulation.Propagator.IsPropagator.eqOn`). -/
theorem isPropagator_eq_constProp {H : P →L[ℂ] P} {U : ℝ → P →L[ℂ] P} {T : ℝ} (hT : 0 ≤ T)
    (hU : IntegrablePathSimulation.Propagator.IsPropagator (fun _ => H) U T) :
    U T = constProp H T :=
  hU.eqOn hT intervalIntegrable_const (isPropagator_constProp H hT) T ⟨hT, le_rfl⟩

/-- **Every classical propagator of the constant path on `[0, T]` is `exp(-iTH)` at `T`**: a
solution of `U' = -iHU` on `[0, T]` with `U 0 = 1` is an integral-sense propagator. -/
theorem propagator_eq_constProp {H : P →L[ℂ] P} {U : ℝ → P →L[ℂ] P} {T : ℝ} (hT : 0 ≤ T)
    (hU0 : U 0 = 1) (hU : TimeDependent.SolvesOn (fun _ => H) U 0 T) :
    U T = constProp H T :=
  isPropagator_eq_constProp hT
    (IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn hT hU0 hU
      intervalIntegrable_const)

end Propagator

/-! ### The constant path of native data -/

section ConstPath

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}

/-- The propagator `exp(-iuH_x)` solves the constant path of instance `x` on every interval. -/
theorem solvesOn_constPath (D : Data X N Z s) (x : X) (a b : ℝ) :
    TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (constPath D x u))
      (constProp (SparseStateOverlap.matrixOperator (D.matrix x))) a b :=
  solvesOn_constProp _ a b

/-- The propagator `exp(-iuH_x)` is an integral-sense propagator of the constant path. -/
theorem isPropagator_constPath (D : Data X N Z s) (x : X) {T : ℝ} (hT : 0 ≤ T) :
    IntegrablePathSimulation.Propagator.IsPropagator
      (fun u => SparseStateOverlap.matrixOperator (constPath D x u))
      (constProp (SparseStateOverlap.matrixOperator (D.matrix x))) T :=
  isPropagator_constProp _ hT

/-- Every classical propagator of the constant path of `x` on `[0, T]` is `exp(-iTH_x)` at
`T`. -/
theorem propagator_constPath_eq (D : Data X N Z s) (x : X)
    {U : ℝ → EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N} {T : ℝ} (hT : 0 ≤ T) (hU0 : U 0 = 1)
    (hU : TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (constPath D x u))
      U 0 T) :
    U T = constProp (SparseStateOverlap.matrixOperator (D.matrix x)) T :=
  propagator_eq_constProp (H := SparseStateOverlap.matrixOperator (D.matrix x)) hT hU0 hU

/-- Every integral-sense propagator of the constant path of `x` on `[0, T]` is `exp(-iTH_x)` at
`T`. -/
theorem isPropagator_constPath_eq (D : Data X N Z s) (x : X)
    {U : ℝ → EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N} {T : ℝ} (hT : 0 ≤ T)
    (hU : IntegrablePathSimulation.Propagator.IsPropagator
      (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U T) :
    U T = constProp (SparseStateOverlap.matrixOperator (D.matrix x)) T :=
  isPropagator_eq_constProp (H := SparseStateOverlap.matrixOperator (D.matrix x)) hT hU

end ConstPath

/-- The released lower-bound target `exp(-iτH)` is the constant propagator at time `τ`. -/
theorem evolve_eq_constProp {S : Type*} [Fintype S] [DecidableEq S] (H : Matrix S S ℂ) (τ : ℝ) :
    SparseLowerBounds.Hamiltonian.evolve H τ =
      constProp (SparseStateOverlap.matrixOperator H) τ := rfl

end

end TimeDependentHamiltonianLowerBound
