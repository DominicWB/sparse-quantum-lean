import SparseLowerBounds.ODE.Uniqueness
import SparseLowerBounds.Hamiltonian.Amplitude

/-!
# The dissipative flow `e^{-tD}` of a matrix generator

Helper of Theorem `odel:thm:psd`. The homogeneous equation
`ẋ = -D x` of the PSD families has the solution `x(t) = e^{-tD} x₀`; in the release's
convention (`TimeDependentODE.SolvesODE`, generator
`G = D`) this is `heat D t x₀ = exp(t • (-D)) x₀`, the exponential of
`TimeDependentODE.accretive_exp_norm_le_one`.

* `heat`, `norm_heat_le` (contraction for accretive `D`), `heat_zero`;
* `heat_eq_evolve`: `e^{-tD} = e^{-it(-iD)}`, the Hamiltonian lower bound's `evolve` of the
  matrix `-iD`. Through it every real-time identity of the released package (which hold for all real times)
  transfers to the dissipative flow for **every real `t`**;
* `solves_heat`: `t ↦ heat D t x₀` solves `ẋ = -D x` on every interval;
  `heat_apply_eq_of_solves`: every solution on `[0, T]` from `x₀` equals it (the release's
  uniqueness `SparseLowerBounds.ODE.solvesODE_const_eqOn`); `heat_apply_eq_of_hasDerivAt`:
  the global form (from `Hamiltonian.evolve_apply_eq_of_hasDerivAt`);
* block and gauge transport, for every real `t`: `heat_fullMatrix_coreVec`,
  `heat_fullMatrix_refZero` (the reference vertex `r₀` of `Hamiltonian.fullMatrix` has eigenvalue
  zero, proof of Theorem `odel:thm:psd`), `heat_unitary_conj` (common gauge, proof of Theorem
  `odel:thm:psd`), `inner_chainVec_heat_kronecker`;
* `psdCore H = (1 - H)/2` (eq. `odel:eq:Dpath`) and `heat_psdCore`:
  `e^{-t(1-H)/2} = e^{-t/2} e^{(t/2) H}`, the imaginary-time form used with `u = τ/2`
  (eq. `odel:eq:imaginaryamp`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Hamiltonian
open scoped Matrix InnerProductSpace

section Flow

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The dissipative flow** `e^{-tD} = exp(t • (-D))` of a matrix generator `D`, in the
form of the release's `TimeDependentODE.accretive_exp_norm_le_one`. -/
def heat (D : Matrix S S ℂ) (t : ℝ) : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S :=
  NormedSpace.exp (t • -(SparseStateOverlap.matrixOperator D))

omit [DecidableEq S] in
/-- `e^{-tD}` is a contraction for `t ≥ 0` when `D` is accretive. -/
theorem norm_heat_le (D : Matrix S S ℂ)
    (hD : TimeDependentODE.Accretive (SparseStateOverlap.matrixOperator D)) (t : ℝ)
    (ht : 0 ≤ t) : ‖heat D t‖ ≤ 1 :=
  TimeDependentODE.accretive_exp_norm_le_one _ hD t ht

omit [DecidableEq S] in
/-- The real scalar action on operators is the complex action of the real number:
`t • X = (t : ℂ) • X`. -/
theorem heat_real_smul (t : ℝ) (X : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    t • X = (t : ℂ) • X := by
  ext v i
  simp

omit [DecidableEq S] in
/-- `e^{-0·D} = 1`. -/
theorem heat_zero (D : Matrix S S ℂ) : heat D 0 = 1 := by
  have h0 : (0 : ℝ) • -SparseStateOverlap.matrixOperator D = 0 := by
    ext v i
    simp
  rw [heat, h0]
  letI : NormedAlgebra ℚ (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :=
    .restrictScalars ℚ ℂ _
  exact NormedSpace.exp_zero

/-- **Bridge to the Schrödinger flow**: `e^{-tD} = e^{-it(-iD)}`, i.e. `heat D t` is the
Hamiltonian lower bound's `evolve` of the (non-Hermitian) matrix `-iD`, for every real `t`. -/
theorem heat_eq_evolve (D : Matrix S S ℂ) (t : ℝ) : heat D t = evolve (-Complex.I • D) t := by
  unfold heat evolve
  congr 1
  rw [ODEMatrixEnergy.matrixOperator_smul, smul_smul,
    show -Complex.I * (t : ℂ) * -Complex.I = -(t : ℂ) by
      linear_combination (t : ℂ) * Complex.I_sq,
    heat_real_smul, smul_neg]
  exact (neg_smul _ _).symm

/-- The derivative of the dissipative flow: `d/dt e^{-tD} x₀ = -D e^{-tD} x₀`, for every
real `t`. -/
theorem hasDerivAt_heat_apply (D : Matrix S S ℂ) (x₀ : EuclideanSpace ℂ S) (t : ℝ) :
    HasDerivAt (fun u : ℝ => heat D u x₀)
      (-(SparseStateOverlap.matrixOperator D (heat D t x₀))) t := by
  have h := HsInstance.hasDerivAt_evolve_apply (-Complex.I • D) x₀ t
  simp only [← heat_eq_evolve] at h
  convert h using 1
  rw [ODEMatrixEnergy.matrixOperator_smul]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_smul, neg_mul_neg, Complex.I_mul_I,
    neg_one_smul]

/-- **The flow solves the ODE**: `t ↦ e^{-tD} x₀` satisfies the release's `SolvesODE` with
generator `D` and no source, on every interval. -/
theorem solves_heat (D : Matrix S S ℂ) (x₀ : EuclideanSpace ℂ S) (a c : ℝ) :
    TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator D) (fun _ => 0)
      (fun t => heat D t x₀) a c := by
  intro u _
  simpa using (hasDerivAt_heat_apply D x₀ u).hasDerivWithinAt

/-- **Uniqueness**: a solution of `ẋ = -D x` on `[0, T]` starting at `x₀` is `e^{-tD} x₀`. -/
theorem heat_apply_eq_of_solves (D : Matrix S S ℂ) {f : ℝ → EuclideanSpace ℂ S} {T : ℝ}
    (hf : TimeDependentODE.SolvesODE (fun _ => SparseStateOverlap.matrixOperator D)
      (fun _ => 0) f 0 T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    heat D t (f 0) = f t := by
  have h0 : heat D 0 (f 0) = f 0 := by rw [heat_zero]; rfl
  exact SparseLowerBounds.ODE.solvesODE_const_eqOn (SparseStateOverlap.matrixOperator D) 0
    (solves_heat D (f 0) 0 T) hf h0 ht

/-- **Global uniqueness**: a curve with `f' = -D f` on all of `ℝ` is `f(t) = e^{-tD} f(0)` for
every real `t`. -/
theorem heat_apply_eq_of_hasDerivAt (D : Matrix S S ℂ) {f : ℝ → EuclideanSpace ℂ S}
    (hf : ∀ t, HasDerivAt f (-(SparseStateOverlap.matrixOperator D (f t))) t) (t : ℝ) :
    heat D t (f 0) = f t := by
  rw [heat_eq_evolve]
  refine evolve_apply_eq_of_hasDerivAt (-Complex.I • D) (fun u => ?_) t
  convert hf u using 1
  rw [ODEMatrixEnergy.matrixOperator_smul]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_smul, neg_mul_neg, Complex.I_mul_I,
    neg_one_smul]

/-- **Unitary similarity**: `e^{-t U K U†} = U e^{-tK} U†` for every real `t`. -/
theorem heat_unitary_conj {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (K : Matrix S S ℂ) (t : ℝ) :
    heat (U * K * Uᴴ) t =
      SparseStateOverlap.matrixOperator U ∘L heat K t ∘L SparseStateOverlap.matrixOperator Uᴴ := by
  rw [heat_eq_evolve, heat_eq_evolve, ← evolve_unitary_conj hU]
  congr 1
  rw [Matrix.mul_smul, Matrix.smul_mul]

end Flow

section Core

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **The PSD generator of a path block** `D = (I - H)/2` (eq. `odel:eq:Dpath`). -/
def psdCore (H : Matrix S S ℂ) : Matrix S S ℂ := (1 / 2 : ℂ) • (1 - H)

/-- `psdCore` commutes with unitary similarity: `(1 - U K U†)/2 = U ((1 - K)/2) U†`. -/
theorem psdCore_unitary_conj {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (K : Matrix S S ℂ) : psdCore (U * K * Uᴴ) = U * psdCore K * Uᴴ := by
  have hUU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hU
  unfold psdCore
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUU]

/-- **Imaginary-time form** (eq. `odel:eq:imaginaryamp` and eq. `odel:eq:Dpath`):
`e^{-t(1-H)/2} = e^{-t/2} e^{(t/2) H}`, the second factor written `heat (-H) (t/2)`. -/
theorem heat_psdCore (H : Matrix S S ℂ) (t : ℝ) :
    heat (psdCore H) t = ((Real.exp (-(t / 2)) : ℝ) : ℂ) • heat (-H) (t / 2) := by
  letI : NormedAlgebra ℚ (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :=
    .restrictScalars ℚ ℂ _
  set A := SparseStateOverlap.matrixOperator H
  have hcore : SparseStateOverlap.matrixOperator (psdCore H) = (1 / 2 : ℂ) • (1 - A) := by
    rw [psdCore, ODEMatrixEnergy.matrixOperator_smul, SparseValuePrecision.matrixOperator_sub,
      Helpers.Chains.mO_one]
  have harg : t • -SparseStateOverlap.matrixOperator (psdCore H) =
      algebraMap ℂ (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) ((-(t / 2) : ℝ) : ℂ) +
        (t / 2) • A := by
    rw [hcore, Algebra.algebraMap_eq_smul_one, heat_real_smul,
      heat_real_smul (t / 2)]
    push_cast
    module
  have hneg : SparseStateOverlap.matrixOperator (-H) = -A := by
    ext v i
    simp [A, SparseStateOverlap.matrixOperator_apply]
  unfold heat
  rw [harg, NormedSpace.exp_add_of_commute (Algebra.commute_algebraMap_left _ _),
    ← NormedSpace.algebraMap_exp_comm, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp,
    ← Algebra.smul_def, hneg, neg_neg]

end Core

section Blocks

variable {C : Type} [Fintype C] [DecidableEq C] {s : ℕ}

/-- The core block flows on its own: `e^{-t fullMatrix H s}` maps `coreVec v` to
`coreVec (e^{-tH} v)`, for every real `t`. -/
theorem heat_fullMatrix_coreVec (H : Matrix C C ℂ) (s : ℕ) (t : ℝ) (v : EuclideanSpace ℂ C) :
    heat (fullMatrix H s) t (coreVec (s := s) v) = coreVec (heat H t v) := by
  rw [heat_eq_evolve, heat_eq_evolve]
  have hM : -Complex.I • fullMatrix H s = Matrix.fromBlocks (-Complex.I • H) 0 0
      (-Complex.I • Matrix.fromBlocks refBlock 0 0 (padBlock s)) := by
    rw [fullMatrix, Matrix.fromBlocks_smul, smul_zero, smul_zero]
  have h0 : (WithLp.toLp 2 fun c => (coreVec (s := s) v) (Sum.inl c) : EuclideanSpace ℂ C) =
      v := rfl
  have h1 : (WithLp.toLp 2 fun r => (coreVec (s := s) v) (Sum.inr r) :
      EuclideanSpace ℂ (Fin 2 ⊕ Fin s)) = 0 := by
    ext r; simp [coreVec]
  rw [hM, evolve_fromBlocks_zero, h0, h1, map_zero]
  ext i
  rcases i with c | r <;> simp [coreVec]

/-- **`r₀` is a fixed vertex of eigenvalue zero** (proof of Theorem `odel:thm:psd`):
`e^{-t fullMatrix H s} |r₀⟩ = |r₀⟩` for every real `t`. -/
theorem heat_fullMatrix_refZero (H : Matrix C C ℂ) (s : ℕ) (t : ℝ) :
    heat (fullMatrix H s) t (EuclideanSpace.single refZero 1) =
      EuclideanSpace.single (refZero : FullIndex C s) 1 := by
  have hcol : ∀ i, fullMatrix H s i (refZero : FullIndex C s) = 0 := by
    intro i
    rcases i with c | k | p
    · simp [fullMatrix, refZero]
    · fin_cases k <;> simp [fullMatrix, refZero, refBlock]
    · simp [fullMatrix, refZero]
  rw [heat_eq_evolve]
  refine HsInstance.evolve_apply_of_matrixOperator_eq_zero _ _ ?_ t
  ext i
  simp [SparseStateOverlap.matrixOperator_apply, hcol]

end Blocks

/-- The ungauged amplitude: `⟨k, v| e^{-t(B ⊗ I)} |k', v⟩ = ⟨k| e^{-tB} |k'⟩` for `m > 0`
and every real `t`. -/
theorem inner_chainVec_heat_kronecker {n m : ℕ} (hm0 : 0 < m)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (t : ℝ) (k k' : Fin (n + 1)) :
    ⟪chainVec n m k, heat (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) t
        (chainVec n m k')⟫_ℂ =
      heat B t (EuclideanSpace.single k' 1) k := by
  rw [heat_eq_evolve, heat_eq_evolve,
    show -Complex.I • Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ) =
      Matrix.kronecker (-Complex.I • B) 1 from (Matrix.smul_kronecker _ _ _).symm]
  exact Helpers.Chains.inner_cvec_evolve_kronecker hm0 (-Complex.I • B) t k k'

end

end ODELowerBoundExtensions.Psd
