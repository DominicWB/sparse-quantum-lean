import SparseODE.ODEFixedTaggedMoments

/-!
# The four-sector private Cayley operation of the dissipative solver

The released query-level construction (`ODETaggedMoments`, `ODEFixedTaggedMoments`) represents a
Hermitian branch `K` of the generator `M` by two tagged copies of the original support, with the
public boundary `J` of weight `p = 2s`. For the LCHS branch `K = H + k D` (`H`, `D` the Hamiltonian
and dissipative parts of `M`, `k` an LCHS node) we place the two summands in two sectors, the
*part* bit outside the tagged private space:

* `gen4 = √2 (K₀(H) ⊕ K₀(k D))`, `bdry4 = (J ⊕ J)/√2`, the Cayley action `act4` and its explicit
  denominator inverse `inv4`, sector by sector;
* `bdry4` is an isometry, `gen4` is self-adjoint with `‖gen4‖ ≤ √(4s)` and
  `‖gen4 bdry4‖ ≤ 1` when the row and column energies of `H` and `k D` are at most `ρ_H²` and
  `ρ_D²` with `ρ_H² + ρ_D² ≤ ρ²` (`gen4_norm`, `gen4_bdry4_norm`), and the compression is
  `bdry4† gen4 bdry4 = (ρ √(4s))⁻¹ (H + k D)` (`compression4`). So the four sectors behave as the
  two-tag construction with `p = 4s`.
* the clock promises of the resolvent at one (`res4`).

Every value of the sector construction is a multiple of a single original entry combination with
an integer (Gaussian) numerator, so its phase is computable exactly from the stored bits and the
label; this is the reason for the separation of `H` and `k D`.

The locator without coordinate exchanges (`tagSwap`, `locS`, `swap_locator`, `actS`, `actS_eq`,
`action_eq_locS`, `act4_eq_loc4`) is in `Swap.lean`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open ContinuousLinearMap OracleCircuit CayleyClockInterface
open NativeSparseBlockEncoding (Data)
open scoped InnerProduct

/-! ### Block-diagonal operators on a doubled space -/

section Diag

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The block-diagonal operator on `Double E`. -/
abbrev dg (A : Bool → E →L[ℂ] E) :
    HermitianDilation.Double E →L[ℂ] HermitianDilation.Double E :=
  WeightedClock.diagonal A

omit [CompleteSpace E] in
theorem dg_mul (A B : Bool → E →L[ℂ] E) : dg A * dg B = dg (fun p => A p * B p) := by
  ext v p
  rfl

omit [CompleteSpace E] in
theorem dg_one : dg (fun _ : Bool => (1 : E →L[ℂ] E)) = 1 :=
  WeightedClock.diagonal_one

omit [CompleteSpace E] in
theorem dg_add (A B : Bool → E →L[ℂ] E) : dg A + dg B = dg (fun p => A p + B p) := by
  ext v p
  rfl

omit [CompleteSpace E] in
theorem dg_sub (A B : Bool → E →L[ℂ] E) : dg A - dg B = dg (fun p => A p - B p) := by
  ext v p
  rfl

omit [CompleteSpace E] in
theorem dg_smul (c : ℂ) (A : Bool → E →L[ℂ] E) : c • dg A = dg (fun p => c • A p) := by
  ext v p
  rfl

omit [CompleteSpace E] in
theorem smul_one_eq_dg (c : ℂ) :
    c • (1 : HermitianDilation.Double E →L[ℂ] HermitianDilation.Double E) =
      dg (fun _ => c • (1 : E →L[ℂ] E)) := by
  ext v p
  rfl

theorem dg_adjoint (A : Bool → E →L[ℂ] E) : (dg A)† = dg (fun p => (A p)†) :=
  WeightedClock.diagonal_adjoint A

theorem dg_unitary (A : Bool → E →L[ℂ] E) (hA : ∀ p, IsUnitary (A p)) : IsUnitary (dg A) :=
  CoherentQuerySchedule.diagonal_unitary A hA

end Diag

/-! ### The two parts of an LCHS branch -/

section Parts

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian matrix of a sector: the Hamiltonian part `H` (`false`) or `k` times the
dissipative part `D` (`true`) of `M`. -/
def partK (M : Matrix n n ℂ) (k : ℝ) (p : Bool) : Matrix n n ℂ :=
  if p then (k : ℂ) • ODEMatrixEnergy.dissipativePart M else ODEMatrixEnergy.hamiltonianPart M

omit [Fintype n] [DecidableEq n] in
@[simp] theorem partK_false (M : Matrix n n ℂ) (k : ℝ) :
    partK M k false = ODEMatrixEnergy.hamiltonianPart M := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem partK_true (M : Matrix n n ℂ) (k : ℝ) :
    partK M k true = (k : ℂ) • ODEMatrixEnergy.dissipativePart M := rfl

omit [Fintype n] [DecidableEq n] in
theorem partK_isHermitian (M : Matrix n n ℂ) (k : ℝ) (p : Bool) : (partK M k p).IsHermitian := by
  cases p
  · exact ODEMatrixEnergy.hamiltonianPart_isHermitian M
  · apply Matrix.IsHermitian.ext
    intro i j
    have h := (ODEMatrixEnergy.dissipativePart_isHermitian M).apply i j
    simp only [partK_true, Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
      Complex.conj_ofReal]
    rw [← Complex.star_def, h]

omit [Fintype n] [DecidableEq n] in
theorem partK_eq_zero (M : Matrix n n ℂ) (k : ℝ) (p : Bool) (i j : n) (hij : M i j = 0)
    (hji : M j i = 0) : partK M k p i j = 0 := by
  cases p <;> simp [partK, hij, hji]

omit [Fintype n] [DecidableEq n] in
theorem partK_add (M : Matrix n n ℂ) (k : ℝ) :
    partK M k false + partK M k true = ODEMatrixEnergy.lchsHamiltonian M k := rfl

/-- The energy bound of a sector. -/
def rhoP (k ηH ηD : ℝ) (p : Bool) : ℝ := if p then |k| * ηD else ηH

omit [DecidableEq n] in
theorem partK_row_energy (M : Matrix n n ℂ) (k ηH ηD : ℝ)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart M i j‖ ^ 2 ≤ ηH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart M i j‖ ^ 2 ≤ ηD ^ 2) (p : Bool) (i : n) :
    ∑ j, ‖partK M k p i j‖ ^ 2 ≤ rhoP k ηH ηD p ^ 2 := by
  cases p
  · exact hrH i
  · simp only [partK_true, rhoP, if_true, Matrix.smul_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, ← Finset.mul_sum, sq_abs]
    exact mul_le_mul_of_nonneg_left (hrD i) (sq_nonneg k)

omit [DecidableEq n] in
theorem partK_col_energy (M : Matrix n n ℂ) (k ηH ηD : ℝ)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart M i j‖ ^ 2 ≤ ηH ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart M i j‖ ^ 2 ≤ ηD ^ 2) (p : Bool) (j : n) :
    ∑ i, ‖partK M k p i j‖ ^ 2 ≤ rhoP k ηH ηD p ^ 2 := by
  cases p
  · exact hcH j
  · simp only [partK_true, rhoP, if_true, Matrix.smul_apply, smul_eq_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, ← Finset.mul_sum, sq_abs]
    exact mul_le_mul_of_nonneg_left (hcD j) (sq_nonneg k)

theorem rhoP_le (k ηH ηD R : ℝ) (hH : 0 ≤ ηH) (hD : 0 ≤ ηD) (hk : |k| ≤ R) (p : Bool) :
    rhoP k ηH ηD p ≤ ηH + R * ηD := by
  have hR : 0 ≤ R := (abs_nonneg k).trans hk
  cases p
  · simp only [rhoP, Bool.false_eq_true, if_false]
    nlinarith
  · simp only [rhoP, if_true]
    nlinarith [mul_le_mul_of_nonneg_right hk hD]

theorem rhoP_nonneg (k ηH ηD : ℝ) (hH : 0 ≤ ηH) (hD : 0 ≤ ηD) (p : Bool) :
    0 ≤ rhoP k ηH ηD p := by
  cases p
  · exact hH
  · exact mul_nonneg (abs_nonneg k) hD

theorem rhoP_sq_sum_le (k ηH ηD R : ℝ) (hH : 0 ≤ ηH) (hD : 0 ≤ ηD) (hk : |k| ≤ R) :
    rhoP k ηH ηD false ^ 2 + rhoP k ηH ηD true ^ 2 ≤ (ηH + R * ηD) ^ 2 := by
  have hR : 0 ≤ R := (abs_nonneg k).trans hk
  simp only [rhoP, Bool.false_eq_true, if_false, if_true]
  have h1 : |k| * ηD ≤ R * ηD := mul_le_mul_of_nonneg_right hk hD
  have h2 : 0 ≤ |k| * ηD := mul_nonneg (abs_nonneg k) hD
  nlinarith

end Parts

/-! ### Scalars -/

theorem sqrt_two_mul_sqrt (s : ℕ) :
    Real.sqrt 2 * Real.sqrt (2 * (s : ℝ)) = Real.sqrt (4 * (s : ℝ)) := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← mul_assoc]
  norm_num

theorem scalar4 (ρ : ℝ) (s : ℕ) :
    ((1 / 2 : ℝ) : ℂ) * (((Real.sqrt 2 : ℝ) : ℂ) * ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹) =
      ((ρ : ℂ) * (Real.sqrt (4 * (s : ℝ)) : ℂ))⁻¹ := by
  have h2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hinv : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_div_assoc, h2]
    norm_num
  have h4 : (Real.sqrt (4 * (s : ℝ)) : ℂ) =
      (Real.sqrt 2 : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ) := by
    rw [← sqrt_two_mul_sqrt]
    push_cast
    ring
  rw [h4, mul_inv, mul_inv, mul_inv, hinv]
  push_cast
  ring

/-! ### The four sectors -/

section Four

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The four-sector private space: the part bit outside the tagged private space. -/
abbrev Space4 (n : Type*) [Fintype n] :=
  HermitianDilation.Double (ODETaggedMoments.PrivateSpace n)

/-- **The four-sector generator** `√2 (K₀(H) ⊕ K₀(k D))` at the node `k` and scale `ρ`. -/
def gen4 (D : Data X n Z s) (x : X) (k ρ : ℝ) : Space4 n →L[ℂ] Space4 n :=
  dg (fun p => ((Real.sqrt 2 : ℝ) : ℂ) •
    ODEFixedTaggedMoments.generator D x (partK (D.matrix x) k p) ρ)

/-- The explicit inverse of the Cayley denominator at the Cayley parameter `γ`. -/
def inv4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) : Space4 n →L[ℂ] Space4 n :=
  dg (fun p => ODEFixedTaggedMoments.inverse D x (partK (D.matrix x) k p) ρ (Real.sqrt 2 * γ))

/-- **The four-sector Cayley action** at the Cayley parameter `γ`. -/
def act4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) : Space4 n →L[ℂ] Space4 n :=
  dg (fun p => ODEFixedTaggedMoments.action D x (partK (D.matrix x) k p) ρ (Real.sqrt 2 * γ))

/-- **The four-sector boundary** `(J ⊕ J)/√2`, independent of the input. -/
def bdry4 (D : Data X n Z s) : EuclideanSpace ℂ n →L[ℂ] Space4 n :=
  WeightedClock.boundary (fun _ : Bool => (1 / 2 : ℝ)) (fun _ => ODEFixedTaggedMoments.boundary D)

theorem scaled_gen4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    scaled (gen4 D x k ρ) γ = dg (fun p =>
      scaled (ODEFixedTaggedMoments.generator D x (partK (D.matrix x) k p) ρ)
        (Real.sqrt 2 * γ)) := by
  unfold scaled gen4
  rw [dg_smul]
  congr 1
  funext p
  rw [smul_smul]
  congr 1
  push_cast
  ring

theorem inv4_right (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    (scaled (gen4 D x k ρ) γ - Complex.I • (1 : Space4 n →L[ℂ] Space4 n)) *
      inv4 D x k ρ γ = 1 := by
  rw [scaled_gen4, smul_one_eq_dg, dg_sub, inv4, dg_mul]
  refine (congrArg dg (funext fun p => ?_)).trans dg_one
  exact ODEFixedTaggedMoments.inverse_right D x _ ρ _

theorem inv4_left (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    inv4 D x k ρ γ *
      (scaled (gen4 D x k ρ) γ - Complex.I • (1 : Space4 n →L[ℂ] Space4 n)) = 1 := by
  rw [scaled_gen4, smul_one_eq_dg, dg_sub, inv4, dg_mul]
  refine (congrArg dg (funext fun p => ?_)).trans dg_one
  exact ODEFixedTaggedMoments.inverse_left D x _ ρ _

theorem act4_eq_cayley (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    act4 D x k ρ γ = ImprovedCayleyMoments.cayleyAction (scaled (gen4 D x k ρ) γ)
      (inv4 D x k ρ γ) := by
  rw [ImprovedCayleyMoments.cayleyAction, scaled_gen4, smul_one_eq_dg, dg_add, inv4, dg_mul, act4]
  congr 1
  funext p
  rw [ODEFixedTaggedMoments.action_eq_cayley]
  rfl

theorem act4_unitary (D : Data X n Z s) (x : X) (k ρ γ : ℝ) : IsUnitary (act4 D x k ρ γ) :=
  dg_unitary _ (fun _ => ODEFixedTaggedMoments.action_unitary D x _ ρ _)

theorem gen4_adjoint (D : Data X n Z s) (x : X) (k ρ : ℝ) :
    (gen4 D x k ρ)† = gen4 D x k ρ := by
  rw [gen4, dg_adjoint]
  congr 1
  funext p
  rw [map_smulₛₗ, Complex.conj_ofReal, ODEFixedTaggedMoments.generator_adjoint]

theorem gen4_star (D : Data X n Z s) (x : X) (k ρ : ℝ) : star (gen4 D x k ρ) = gen4 D x k ρ := by
  rw [star_eq_adjoint, gen4_adjoint]

theorem bdry4_isometry (D : Data X n Z s) : (bdry4 D)† ∘L bdry4 D = 1 :=
  WeightedClock.boundary_isometry _ (fun _ => by norm_num)
    (by simp only [Fintype.sum_bool]; norm_num)
    _ (fun _ => ODEFixedTaggedMoments.boundary_isometry D)

/-- **The full-space norm** of the four-sector generator is at most `√(4s)`. -/
theorem gen4_norm (D : Data X n Z s) (x : X) (k ρ : ℝ) (hρ : 0 < ρ)
    (hent : ∀ p i j, ‖partK (D.matrix x) k p i j‖ ≤ ρ) :
    ‖gen4 D x k ρ‖ ≤ Real.sqrt (4 * (s : ℝ)) := by
  apply WeightedClock.norm_diagonal_le _ _ (Real.sqrt_nonneg _)
  intro p
  have h1 : ‖ODEFixedTaggedMoments.generator D x (partK (D.matrix x) k p) ρ‖ ≤
      Real.sqrt (2 * (s : ℝ)) :=
    (UnitaryCayleyTransport.conjugate_norm_le _ (ODETaggedLocators.locator_unitary D x) _).trans
      (ODETaggedMoments.generator_norm_le _ _ _ ρ hρ (hent p))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    ← sqrt_two_mul_sqrt]
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

/-- One sector applied to the boundary, with its own energy bound `ρp`. -/
theorem sector_bdry_sq (D : Data X n Z s) (x : X) (K : Matrix n n ℂ) (ρ ρp : ℝ) (hρ : 0 < ρ)
    (hr : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ ρp ^ 2) (hc : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ ρp ^ 2)
    (v : EuclideanSpace ℂ n) :
    ‖ODEFixedTaggedMoments.generator D x K ρ (ODEFixedTaggedMoments.boundary D v)‖ ^ 2 ≤
      ρp ^ 2 / ρ ^ 2 * ‖v‖ ^ 2 := by
  have hU := ODETaggedLocators.locator_unitary D x
  have h1 : ODEFixedTaggedMoments.generator D x K ρ (ODEFixedTaggedMoments.boundary D v) =
      ((ODETaggedLocators.locator D x)†) (ODETaggedMoments.generator (D.matrix x) K s ρ
        (ODETaggedMoments.boundary (D.rowloc x) (D.colloc x) v)) := by
    have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] ODETaggedMoments.PrivateSpace n => T v)
      (UnitaryCayleyTransport.conjugate_comp (ODETaggedLocators.locator D x)
        (ODETaggedMoments.generator (D.matrix x) K s ρ) (ODETaggedLocators.fixedBoundary D.slot))
    have hb : (ODETaggedLocators.locator D x) ((ODETaggedLocators.fixedBoundary D.slot) v) =
        ODETaggedMoments.boundary (D.rowloc x) (D.colloc x) v := by
      rw [← comp_apply, ODETaggedLocators.locator_boundary]
    simp only [comp_apply] at h
    rw [hb] at h
    exact h
  have hiso : ∀ w, ‖((ODETaggedLocators.locator D x)†) w‖ = ‖w‖ := by
    intro w
    have h2 : ((ODETaggedLocators.locator D x)†)† ∘L (ODETaggedLocators.locator D x)† = 1 := by
      rw [adjoint_adjoint]
      have := hU.2
      rwa [star_eq_adjoint, mul_def] at this
    exact (((ODETaggedLocators.locator D x)†).norm_map_iff_adjoint_comp_self).mpr h2 w
  rw [h1, hiso, ODETaggedMoments.generator_boundary_norm_sq D.slots_pos _ _ ρ hρ]
  have hl := ODETaggedSupport.left_boundary_energy_le (D.matrix x) K (D.rowloc x) (D.colloc x)
    (D.row_covers x) (D.column_covers x) ρp hr v
  have hr' := ODETaggedSupport.right_boundary_energy_le (D.matrix x) K (D.rowloc x) (D.colloc x)
    (D.row_covers x) (D.column_covers x) ρp hc v
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ρ ^ 2)]
  have hρ2 : ρp ^ 2 / ρ ^ 2 * ‖v‖ ^ 2 * (2 * ρ ^ 2) = 2 * (ρp ^ 2 * ‖v‖ ^ 2) := by
    field_simp
  rw [hρ2]
  linarith

/-- **The boundary moment** of the four-sector generator is at most one. -/
theorem gen4_bdry4_norm (D : Data X n Z s) (x : X) (k ρ : ℝ) (ρp : Bool → ℝ) (hρ : 0 < ρ)
    (hr : ∀ p i, ∑ j, ‖partK (D.matrix x) k p i j‖ ^ 2 ≤ ρp p ^ 2)
    (hc : ∀ p j, ∑ i, ‖partK (D.matrix x) k p i j‖ ^ 2 ≤ ρp p ^ 2)
    (hsum : ρp false ^ 2 + ρp true ^ 2 ≤ ρ ^ 2) :
    ‖gen4 D x k ρ ∘L bdry4 D‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖gen4 D x k ρ (bdry4 D v)‖ ^ 2 ≤ _
  rw [gen4, bdry4, WeightedClock.diagonal_boundary_energy _ (fun _ => by norm_num),
    Fintype.sum_bool]
  have hsq : ∀ p, (1 / 2 : ℝ) * ‖(((Real.sqrt 2 : ℝ) : ℂ) •
      ODEFixedTaggedMoments.generator D x (partK (D.matrix x) k p) ρ)
        (ODEFixedTaggedMoments.boundary D v)‖ ^ 2 =
      ‖ODEFixedTaggedMoments.generator D x (partK (D.matrix x) k p) ρ
        (ODEFixedTaggedMoments.boundary D v)‖ ^ 2 := by
    intro p
    rw [smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hsq, hsq]
  have h1 := sector_bdry_sq D x _ ρ (ρp true) hρ (hr true) (hc true) v
  have h2 := sector_bdry_sq D x _ ρ (ρp false) hρ (hr false) (hc false) v
  have h3 : ρp true ^ 2 / ρ ^ 2 * ‖v‖ ^ 2 + ρp false ^ 2 / ρ ^ 2 * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← add_mul]
    apply mul_le_of_le_one_left (sq_nonneg _)
    rw [← add_div, div_le_one (by positivity)]
    linarith
  linarith

/-- **The compression** `bdry4† gen4 bdry4 = (ρ √(4s))⁻¹ (H + k D)`. -/
theorem compression4 (D : Data X n Z s) (x : X) (k ρ : ℝ) :
    (bdry4 D)† ∘L gen4 D x k ρ ∘L bdry4 D =
      ((ρ : ℂ) * (Real.sqrt (4 * (s : ℝ)) : ℂ))⁻¹ •
        SparseStateOverlap.matrixOperator (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) := by
  have hc : ∀ p, (ODEFixedTaggedMoments.boundary D)† ∘L
      ((((Real.sqrt 2 : ℝ) : ℂ) • ODEFixedTaggedMoments.generator D x (partK (D.matrix x) k p) ρ)
        ∘L ODEFixedTaggedMoments.boundary D) =
      (((Real.sqrt 2 : ℝ) : ℂ) * ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹) •
        SparseStateOverlap.matrixOperator (partK (D.matrix x) k p) := by
    intro p
    rw [smul_comp, comp_smul, ODEFixedTaggedMoments.compression D x _ (partK_isHermitian _ k p) ρ
      (fun i j hij hji => partK_eq_zero _ k p i j hij hji), smul_smul]
  unfold gen4 bdry4
  rw [WeightedClock.boundary_compression _ (fun _ => by norm_num), Fintype.sum_bool, hc, hc,
    smul_smul, smul_smul, ← smul_add, add_comm, ← ODEMatrixEnergy.matrixOperator_add, partK_add,
    scalar4]

/-! ### The clock promises of the four sectors -/

/-- The resolvent at one of the rescaled four-sector generator. -/
def res4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) : Space4 n →L[ℂ] Space4 n :=
  ImprovedCayleyMoments.resolventAtOne (scaled (gen4 D x k ρ) γ)

theorem one_sub_act4_res4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    (1 - act4 D x k ρ γ) * res4 D x k ρ γ = 1 := by
  rw [act4_eq_cayley]
  exact ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne _ _
    (inv4_right D x k ρ γ) (inv4_left D x k ρ γ)

theorem res4_one_sub_act4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    res4 D x k ρ γ * (1 - act4 D x k ρ γ) = 1 := by
  rw [act4_eq_cayley]
  exact ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction _ _ (inv4_right D x k ρ γ)

theorem norm_res4_le (D : Data X n Z s) (x : X) (k ρ γ : ℝ) (hρ : 0 < ρ) (hγ : 0 ≤ γ)
    (hent : ∀ p i j, ‖partK (D.matrix x) k p i j‖ ≤ ρ) :
    ‖res4 D x k ρ γ‖ ≤ width (4 * (s : ℝ)) γ :=
  resolvent_norm _ _ γ hγ (gen4_norm D x k ρ hρ hent)

theorem res4_compression (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    (bdry4 D)† ∘L res4 D x k ρ γ ∘L bdry4 D =
      (2 : ℂ)⁻¹ • (1 + Complex.I • ((γ : ℂ) * ((ρ : ℂ) * (Real.sqrt (4 * (s : ℝ)) : ℂ))⁻¹) •
        SparseStateOverlap.matrixOperator (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k)) := by
  rw [res4, ImprovedCayleyMoments.resolventAtOne_compression _ _ (bdry4_isometry D)]
  congr 3
  rw [scaled, smul_comp, comp_smul, compression4, smul_smul]

theorem norm_res4_bdry4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) (ρp : Bool → ℝ) (hρ : 0 < ρ)
    (hγ : 0 ≤ γ)
    (hr : ∀ p i, ∑ j, ‖partK (D.matrix x) k p i j‖ ^ 2 ≤ ρp p ^ 2)
    (hc : ∀ p j, ∑ i, ‖partK (D.matrix x) k p i j‖ ^ 2 ≤ ρp p ^ 2)
    (hsum : ρp false ^ 2 + ρp true ^ 2 ≤ ρ ^ 2) :
    ‖res4 D x k ρ γ ∘L bdry4 D‖ ≤ endpoint γ :=
  endpoint_norm _ _ γ (gen4_star D x k ρ) (bdry4_isometry D) hγ
    (gen4_bdry4_norm D x k ρ ρp hρ hr hc hsum)

end Four

end

end SparseHamiltonian.GateBinaryODE
