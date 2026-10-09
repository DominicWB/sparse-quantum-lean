import SparseHamiltonian.ImprovedSparseHamiltonian

/-!
# Entry-oracle unitary implementation at constant error

Lean / Mathlib: 4.32.1.

Main declaration: `SparseHamiltonian.UnitaryImplementation.implementation`.
It constructs a clean unitary circuit with operator-norm error at most 1/4
using at most C sqrt(N) original entry-oracle or inverse-entry-oracle calls.
The absolute positive constant C is `UnitaryImplementation.queryConstant`.

Checked axiom dependencies are collected in `SparseHamiltonian/Audit.lean`.
-/

/-! ===== UnitaryEntryData.lean ===== -/

/-!
# Dense unitary entries as native sparse Hermitian data

The doubled matrix uses exactly `card n` fixed slots per row. Its value alphabet
is the original alphabet: every address, including a diagonal Boolean block,
queries one original entry. The fixed decoder suppresses the diagonal blocks.
No controlled entry query or input-dependent location oracle is supplied.
-/

namespace SparseHamiltonian.UnitaryEntryData

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 3000000

/-- An ordinary reversible entry table for a unitary matrix. The decoder,
including its finite global bound, is fixed independently of the instance. -/
structure Data (X n Z : Type*) [Fintype n] where
  matrix : X → Matrix n n ℂ
  unitary : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (matrix x))
  table : X → (n × n) → Z
  decode : (n × n) → Z → ℂ
  scale : ℝ
  scale_pos : 0 < scale
  decode_bound : ∀ a z, ‖decode a z‖ ≤ scale
  decoded : ∀ x i j, decode (i, j) (table x (i, j)) = matrix x i j

abbrev Index (n : Type*) := Bool × n

variable {X n Z : Type*} [Fintype n]

/-- The original entry address. Its routing depends only on the row flag. -/
def address (a : Index n × Index n) : n × n :=
  if a.1.1 then (a.2.2, a.1.2) else (a.1.2, a.2.2)

/-- The Boolean Hermitian dilation `[[0,U],[U†,0]]`. -/
def dilationMatrix (D : Data X n Z) (x : X) : Matrix (Index n) (Index n) ℂ :=
  fun i j => if i.1 = j.1 then 0 else if i.1 then star (D.matrix x j.2 i.2)
    else D.matrix x i.2 j.2

/-- All addresses use an unconditional original entry lookup. -/
def dilationTable (D : Data X n Z) (x : X) (a : Index n × Index n) : Z :=
  D.table x (address a)

/-- Conjugation and diagonal suppression belong to a fixed decoder. -/
def dilationDecode (D : Data X n Z) (a : Index n × Index n) (z : Z) : ℂ :=
  if a.1.1 = a.2.1 then 0 else if a.1.1 then star (D.decode (address a) z)
    else D.decode (address a) z

theorem dilationDecode_bound (D : Data X n Z) (a : Index n × Index n) (z : Z) :
    ‖dilationDecode D a z‖ ≤ D.scale := by
  unfold dilationDecode
  split
  · simpa using D.scale_pos.le
  · split
    · simpa only [norm_star] using D.decode_bound (address a) z
    · exact D.decode_bound (address a) z

@[simp] theorem dilationDecoded (D : Data X n Z) (x : X) (i j : Index n) :
    dilationDecode D (i, j) (dilationTable D x (i, j)) = dilationMatrix D x i j := by
  rcases i with ⟨b, i⟩
  rcases j with ⟨c, j⟩
  cases b <;> cases c <;>
    simp [dilationDecode, dilationTable, address, dilationMatrix, D.decoded]

theorem dilation_hermitian (D : Data X n Z) (x : X) :
    (dilationMatrix D x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [dilationMatrix]

/-- Unitarity of the supplied matrix implies the column energy promise. -/
theorem column_energy (D : Data X n Z) (x : X) (j : n) :
    ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ (1 : ℝ) := by
  simpa using SparseSpectralEnergy.column_energy_le (D.matrix x) 1
    (D.unitary x).norm_le_one j

/-- Applying the column argument to the adjoint supplies row energies. -/
theorem row_energy (D : Data X n Z) (x : X) (i : n) :
    ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ (1 : ℝ) := by
  have hNorm : ‖SparseStateOverlap.matrixOperator (D.matrix x).conjTranspose‖ ≤ 1 := by
    rw [← SparseValuePrecision.matrixOperator_adjoint]
    exact (D.unitary x).adjoint.norm_le_one
  simpa [Matrix.conjTranspose_apply] using
    SparseSpectralEnergy.column_energy_le (D.matrix x).conjTranspose 1 hNorm i

theorem dilation_row_energy (D : Data X n Z) (x : X) (i : Index n) :
    ∑ j, ‖dilationMatrix D x i j‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
  rcases i with ⟨b, i⟩
  cases b
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using row_energy D x i
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using column_energy D x i

theorem dilation_column_energy (D : Data X n Z) (x : X) (j : Index n) :
    ∑ i, ‖dilationMatrix D x i j‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
  rcases j with ⟨b, j⟩
  cases b
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using row_energy D x j
  · simpa [dilationMatrix, Fintype.sum_prod_type, Fintype.sum_bool] using column_energy D x j

/-- The fixed Hilbert-space identification between flat and nested registers. -/
def flatToDouble : EuclideanSpace ℂ (Index n) ≃ₗᵢ[ℂ]
    HermitianDilation.Double (EuclideanSpace ℂ n) :=
  (RegisterEquivalences.productFlatten Bool n).symm

@[simp] theorem flatToDouble_apply (v : EuclideanSpace ℂ (Index n)) (b : Bool) (i : n) :
    flatToDouble v b i = v (b, i) := rfl

@[simp] theorem flatToDouble_symm_apply
    (v : HermitianDilation.Double (EuclideanSpace ℂ n)) (b : Bool) (i : n) :
    flatToDouble.symm v (b, i) = v b i := rfl

abbrev flatToDoubleCLM : EuclideanSpace ℂ (Index n) →L[ℂ]
    HermitianDilation.Double (EuclideanSpace ℂ n) :=
  flatToDouble.toLinearIsometry.toContinuousLinearMap

/-- The concrete entry matrix is exactly the existing operator dilation. -/
theorem flatToDouble_dilation_apply (D : Data X n Z) (x : X)
    (v : EuclideanSpace ℂ (Index n)) :
    flatToDouble (SparseStateOverlap.matrixOperator (dilationMatrix D x) v) =
      HermitianDilation.dilation (SparseStateOverlap.matrixOperator (D.matrix x))
        (flatToDouble v) := by
  ext b i
  cases b <;>
    simp [flatToDouble_apply, HermitianDilation.dilation_apply_false,
      HermitianDilation.dilation_apply_true, SparseValuePrecision.matrixOperator_adjoint,
      SparseStateOverlap.matrixOperator_apply, dilationMatrix,
      Fintype.sum_prod_type, Matrix.conjTranspose_apply]

theorem flatToDouble_dilation (D : Data X n Z) (x : X) :
    flatToDoubleCLM ∘L SparseStateOverlap.matrixOperator (dilationMatrix D x) =
      HermitianDilation.dilation (SparseStateOverlap.matrixOperator (D.matrix x)) ∘L
        flatToDoubleCLM := by
  apply ContinuousLinearMap.ext
  intro v
  exact flatToDouble_dilation_apply D x v

/-- The full flat operator squares to the identity, not merely on clean inputs. -/
theorem dilation_involution (D : Data X n Z) (x : X)
    (v : EuclideanSpace ℂ (Index n)) :
    SparseStateOverlap.matrixOperator (dilationMatrix D x)
      (SparseStateOverlap.matrixOperator (dilationMatrix D x) v) = v := by
  apply flatToDouble.injective
  rw [flatToDouble_dilation_apply, flatToDouble_dilation_apply,
    HermitianDilation.dilation_involution _ (D.unitary x)]

theorem dilation_sq (D : Data X n Z) (x : X) :
    SparseStateOverlap.matrixOperator (dilationMatrix D x) ∘L
      SparseStateOverlap.matrixOperator (dilationMatrix D x) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  exact dilation_involution D x v

/-- Fixed injection into the false Boolean half of the flat matrix register. -/
def includeZero : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (Index n) :=
  flatToDouble.symm.toLinearIsometry.toContinuousLinearMap ∘L
    CleanOutputAlignment.includeZero

/-- Fixed injection into the true half, on which the dilation applies U. -/
def includeOne : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (Index n) :=
  flatToDouble.symm.toLinearIsometry.toContinuousLinearMap ∘L
    HermitianDilation.swap ∘L CleanOutputAlignment.includeZero

@[simp] theorem flatToDouble_includeZero (v : EuclideanSpace ℂ n) :
    flatToDouble (includeZero v) = CleanOutputAlignment.includeZero v := by
  change flatToDouble (flatToDouble.symm _) = _
  exact flatToDouble.apply_symm_apply _

@[simp] theorem flatToDouble_includeOne (v : EuclideanSpace ℂ n) :
    flatToDouble (includeOne v) =
      HermitianDilation.swap (CleanOutputAlignment.includeZero v) := by
  change flatToDouble (flatToDouble.symm _) = _
  exact flatToDouble.apply_symm_apply _

theorem includeZero_isometry :
    (includeZero (n := n))† ∘L includeZero = 1 := by
  apply norm_map_iff_adjoint_comp_self _ |>.mp
  intro v
  change ‖flatToDouble.symm (CleanOutputAlignment.includeZero v)‖ = ‖v‖
  rw [LinearIsometryEquiv.norm_map]
  exact (CleanOutputAlignment.includeZero : EuclideanSpace ℂ n →L[ℂ]
    HermitianDilation.Double (EuclideanSpace ℂ n)).norm_map_iff_adjoint_comp_self.mpr
      CleanOutputAlignment.includeZero_isometry v

theorem includeOne_isometry :
    (includeOne (n := n))† ∘L includeOne = 1 := by
  apply norm_map_iff_adjoint_comp_self _ |>.mp
  intro v
  change ‖flatToDouble.symm
    (HermitianDilation.swap (CleanOutputAlignment.includeZero v))‖ = ‖v‖
  rw [LinearIsometryEquiv.norm_map]
  rw [(HermitianDilation.swap : HermitianDilation.Double (EuclideanSpace ℂ n) →L[ℂ]
    HermitianDilation.Double (EuclideanSpace ℂ n)).norm_map_iff_adjoint_comp_self.mpr
      HermitianDilation.swap_unitary.1]
  exact (CleanOutputAlignment.includeZero : EuclideanSpace ℂ n →L[ℂ]
    HermitianDilation.Double (EuclideanSpace ℂ n)).norm_map_iff_adjoint_comp_self.mpr
      CleanOutputAlignment.includeZero_isometry v

/-- Exact off-diagonal action, with fixed clean input and output embeddings. -/
theorem dilation_includeOne (D : Data X n Z) (x : X) :
    SparseStateOverlap.matrixOperator (dilationMatrix D x) ∘L includeOne =
      includeZero ∘L SparseStateOverlap.matrixOperator (D.matrix x) := by
  apply ContinuousLinearMap.ext
  intro v
  change SparseStateOverlap.matrixOperator (dilationMatrix D x) (includeOne v) =
    includeZero (SparseStateOverlap.matrixOperator (D.matrix x) v)
  apply flatToDouble.injective
  rw [flatToDouble_dilation_apply, flatToDouble_includeOne, flatToDouble_includeZero]
  apply PiLp.ext
  intro b
  cases b <;> simp

section Native
variable [DecidableEq n] [Nonempty n]

/-- Original slots occupy only the false-flag half of the address space. -/
def slot : Fin (Fintype.card n) ↪ Index n where
  toFun k := (false, (Fintype.equivFin n).symm k)
  inj' := by
    intro k l h
    exact (Fintype.equivFin n).symm.injective (congrArg Prod.snd h)

/-- Every row addresses exactly the opposite Boolean half. -/
def loc (i : Index n) (k : Fin (Fintype.card n)) : Index n :=
  (!i.1, (Fintype.equivFin n).symm k)

omit [DecidableEq n] [Nonempty n] in
theorem loc_injective (i : Index n) : Function.Injective (loc i) := by
  intro k l h
  exact (Fintype.equivFin n).symm.injective (congrArg Prod.snd h)

/-- An explicitly reversible extension of the fixed row slot locator. -/
def rowEquiv : (Index n × Index n) ≃ (Index n × Index n) where
  toFun a := (a.1, (if a.1.1 then a.2.1 else !a.2.1, a.2.2))
  invFun a := (a.1, (if a.1.1 then a.2.1 else !a.2.1, a.2.2))
  left_inv := by
    rintro ⟨⟨b, i⟩, ⟨c, j⟩⟩
    cases b <;> cases c <;> rfl
  right_inv := by
    rintro ⟨⟨b, i⟩, ⟨c, j⟩⟩
    cases b <;> cases c <;> rfl

def columnEquiv : (Index n × Index n) ≃ (Index n × Index n) :=
  rowEquiv.trans (Equiv.prodComm (Index n) (Index n))

/-- These location operators contain no unknown matrix or input instance. -/
def rowOracle : EuclideanSpace ℂ (Index n × Index n) →L[ℂ]
    EuclideanSpace ℂ (Index n × Index n) :=
  (LookupOracle.permutationUnitary rowEquiv).toLinearIsometry.toContinuousLinearMap

def columnOracle : EuclideanSpace ℂ (Index n × Index n) →L[ℂ]
    EuclideanSpace ℂ (Index n × Index n) :=
  (LookupOracle.permutationUnitary columnEquiv).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq n] [Nonempty n] in
theorem rowOracle_unitary : IsUnitary (rowOracle (n := n)) :=
  LookupOracle.permutationUnitary_unitary rowEquiv

omit [DecidableEq n] [Nonempty n] in
theorem columnOracle_unitary : IsUnitary (columnOracle (n := n)) :=
  LookupOracle.permutationUnitary_unitary columnEquiv

omit [Nonempty n] in
theorem rowOracle_valid (i : Index n) (k : Fin (Fintype.card n)) :
    rowOracle (EuclideanSpace.single (i, slot k) 1) =
      EuclideanSpace.single (i, loc i k) 1 := by
  change LookupOracle.permutationUnitary rowEquiv _ = _
  rw [LookupOracle.permutationUnitary_single]
  rcases i with ⟨b, i⟩
  cases b <;> rfl

omit [Nonempty n] in
theorem columnOracle_valid (j : Index n) (k : Fin (Fintype.card n)) :
    columnOracle (EuclideanSpace.single (j, slot k) 1) =
      EuclideanSpace.single (loc j k, j) 1 := by
  change LookupOracle.permutationUnitary columnEquiv _ = _
  rw [LookupOracle.permutationUnitary_single]
  rcases j with ⟨b, j⟩
  cases b <;> rfl

omit [Nonempty n] in
theorem row_covers (D : Data X n Z) (x : X) (i j : Index n)
    (h : dilationMatrix D x i j ≠ 0) : SparseSlotStates.selected loc i j := by
  have hflag : i.1 ≠ j.1 := by
    intro hij
    exact h (by simp [dilationMatrix, hij])
  have hloc : loc i ((Fintype.equivFin n) j.2) = j := by
    rcases i with ⟨b, i⟩
    rcases j with ⟨c, j⟩
    cases b <;> cases c <;> simp_all [loc]
  rw [← hloc]
  exact SparseSlotStates.selected_loc loc i _

/-- Dense entry access supplies the original native interface with sparsity N. -/
def toNative (D : Data X n Z) :
    NativeSparseBlockEncoding.Data X (Index n) Z (Fintype.card n) where
  slot := slot
  slots_pos := Fintype.card_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix := dilationMatrix D
  table := dilationTable D
  decode := dilationDecode D
  decode_bound := dilationDecode_bound D
  decoded := dilationDecoded D
  rowloc := fun _ => loc
  colloc := fun _ => loc
  row_injective := fun _ => loc_injective
  column_injective := fun _ => loc_injective
  row_covers := row_covers D
  column_covers := by
    intro x i j h
    apply row_covers D x j i
    intro hji
    have hHerm := (dilation_hermitian D x).apply i j
    rw [hji, star_zero] at hHerm
    exact h hHerm.symm
  rowOracle := fun _ => rowOracle
  columnOracle := fun _ => columnOracle
  row_unitary := fun _ => rowOracle_unitary
  column_unitary := fun _ => columnOracle_unitary
  row_valid := fun _ => rowOracle_valid
  column_valid := fun _ => columnOracle_valid

@[simp] theorem toNative_matrix (D : Data X n Z) :
    (toNative D).matrix = dilationMatrix D := rfl

@[simp] theorem toNative_table (D : Data X n Z) :
    (toNative D).table = dilationTable D := rfl

@[simp] theorem toNative_rowOracle (D : Data X n Z) (x : X) :
    (toNative D).rowOracle x = rowOracle := rfl

@[simp] theorem toNative_columnOracle (D : Data X n Z) (x : X) :
    (toNative D).columnOracle x = columnOracle := rfl

end Native
end
end SparseHamiltonian.UnitaryEntryData

/-! ===== UnitaryDilationTransfer.lean ===== -/

/-!
# Exact quarter-turn evolution and clean unitary implementation

The exponential of an involution is evaluated by its two algebraic spectral
factors.  Restricting a simulation to one fixed input sector then implements
the off-diagonal unitary.  A final fixed clean-output alignment removes the
sector change and the scalar phase.  This transformation preserves the actual
program, its total query count, and the cost of every primitive label.
-/

namespace SparseHamiltonian.UnitaryDilationTransfer

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

section Exponential

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- The elementary two-factor exponential formula for a bounded involution.
No self-adjointness or finite-dimensional spectral theorem is needed. -/
theorem exp_smul_involution (H : V →L[ℂ] V) (hH : H ∘L H = 1) (c : ℂ) :
    NormedSpace.exp (c • H) =
      Complex.exp c • ((2 : ℂ)⁻¹ • (1 + H)) +
        Complex.exp (-c) • ((2 : ℂ)⁻¹ • (1 - H)) := by
  let P : V →L[ℂ] V := (2 : ℂ)⁻¹ • (1 + H)
  let Q : V →L[ℂ] V := (2 : ℂ)⁻¹ • (1 - H)
  have hHmul : H * H = 1 := hH
  have hHP : H * P = P := by
    dsimp [P]
    rw [mul_smul_comm, mul_add, mul_one, hHmul, add_comm H]
  have hHQ : H * Q = -Q := by
    dsimp [Q]
    rw [mul_smul_comm, mul_sub, mul_one, hHmul]
    module
  have hPQ : P + Q = 1 := by
    dsimp [P, Q]
    module
  have hpow (n : ℕ) : (c • H) ^ n = c ^ n • P + (-c) ^ n • Q := by
    induction n with
    | zero => simpa only [pow_zero, one_smul] using hPQ.symm
    | succ n ih =>
      rw [pow_succ', ih]
      simp only [mul_add, smul_mul_smul_comm, hHP, hHQ, smul_neg,
        pow_succ', neg_mul, neg_smul]
  have hs :=
    ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const P).add
      ((NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (-c)).smul_const Q)
  have hseries : HasSum
      (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • (c • H) ^ n)
      (NormedSpace.exp c • P + NormedSpace.exp (-c) • Q) := by
    refine hs.congr_fun ?_
    intro n
    rw [hpow, smul_add]
    simp only [smul_smul, smul_eq_mul]
  have hexp := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • H)
  simpa only [Complex.exp_eq_exp_ℂ, P, Q] using hexp.unique hseries

/-- At time `π/2`, an involution is implemented exactly, with phase `-i`. -/
theorem exp_quarter_turn (H : V →L[ℂ] V) (hH : H ∘L H = 1) :
    NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • H) =
      -Complex.I • H := by
  rw [exp_smul_involution H hH]
  have hneg : -Complex.I * ((Real.pi / 2 : ℝ) : ℂ) =
      -(Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
  have hpos : -(-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      (Real.pi : ℂ) / 2 * Complex.I := by push_cast; ring
  have hc : Complex.exp (-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      -Complex.I := by rw [hneg, Complex.exp_neg_pi_div_two_mul_I]
  have hnc : Complex.exp (-(-Complex.I * ((Real.pi / 2 : ℝ) : ℂ))) =
      Complex.I := by rw [hpos, Complex.exp_pi_div_two_mul_I]
  rw [hc, hnc]
  module

end Exponential

/-- Cache the standard endomorphism topology before substituting the doubled
Hilbert space.  This is the ordinary operator-norm topology, not an extra
assumption on the dilation. -/
private theorem endomorphism_topologicalRing (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℂ E] :
    IsTopologicalRing (E →L[ℂ] E) := by
  infer_instance

section Dilation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

local instance dilationEndomorphismTopologicalRing :
    IsTopologicalRing (HermitianDilation.Double V →L[ℂ] HermitianDilation.Double V) :=
  endomorphism_topologicalRing (HermitianDilation.Double V)

/-- The Boolean `true` sector, independent of the unknown unitary. -/
def includeOne : V →L[ℂ] HermitianDilation.Double V :=
  HermitianDilation.swap ∘L CleanOutputAlignment.includeZero

omit [CompleteSpace V] in
@[simp] theorem includeOne_apply_false (v : V) : includeOne v false = 0 := by
  simp [includeOne]

omit [CompleteSpace V] in
@[simp] theorem includeOne_apply_true (v : V) : includeOne v true = v := by
  simp [includeOne]

theorem includeOne_isometry :
    (includeOne : V →L[ℂ] HermitianDilation.Double V)† ∘L includeOne = 1 := by
  apply norm_map_iff_adjoint_comp_self _ |>.mp
  intro v
  rw [includeOne, comp_apply,
    (HermitianDilation.swap : HermitianDilation.Double V →L[ℂ]
      HermitianDilation.Double V).norm_map_iff_adjoint_comp_self.mpr
        HermitianDilation.swap_unitary.1,
    (CleanOutputAlignment.includeZero : V →L[ℂ]
      HermitianDilation.Double V).norm_map_iff_adjoint_comp_self.mpr
        CleanOutputAlignment.includeZero_isometry]

/-- The upper off-diagonal block is the desired unitary on its entire space. -/
theorem dilation_includeOne (U : V →L[ℂ] V) :
    HermitianDilation.dilation U ∘L includeOne =
      CleanOutputAlignment.includeZero ∘L U := by
  ext v b
  cases b <;> simp

theorem dilation_exp_quarter_turn (U : V →L[ℂ] V) (hU : IsUnitary U) :
    NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
      HermitianDilation.dilation U) = -Complex.I • HermitianDilation.dilation U :=
  exp_quarter_turn _ (HermitianDilation.dilation_sq U hU)

/-- Exact unitary action after quarter-turn simulation of the Hermitian dilation. -/
theorem dilation_exp_includeOne (U : V →L[ℂ] V) (hU : IsUnitary U) :
    NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
      HermitianDilation.dilation U) ∘L includeOne =
        (-Complex.I • (CleanOutputAlignment.includeZero : V →L[ℂ]
          HermitianDilation.Double V)) ∘L U := by
  rw [dilation_exp_quarter_turn U hU, smul_comp, dilation_includeOne, smul_comp]

end Dilation

section CleanTransfer

variable {V P K : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {X L : Type*}

/-- Composing two fixed clean isometries again gives a clean isometry. -/
theorem comp_isometry (E : P →L[ℂ] K) (J : V →L[ℂ] P)
    (hE : E† ∘L E = 1) (hJ : J† ∘L J = 1) :
    (E ∘L J)† ∘L (E ∘L J) = 1 := by
  apply norm_map_iff_adjoint_comp_self _ |>.mp
  intro v
  rw [comp_apply, E.norm_map_iff_adjoint_comp_self.mpr hE,
    J.norm_map_iff_adjoint_comp_self.mpr hJ]

/-- Multiplication by the known phase `-i` preserves a clean isometry. -/
theorem phase_isometry (F : V →L[ℂ] K) (hF : F† ∘L F = 1) :
    (-Complex.I • F)† ∘L (-Complex.I • F) = 1 := by
  apply norm_map_iff_adjoint_comp_self _ |>.mp
  intro v
  simp only [smul_apply, norm_smul, norm_neg, Complex.norm_I, one_mul,
    F.norm_map_iff_adjoint_comp_self.mpr hF]

omit [CompleteSpace K] in
/-- Restricting the simulation to the input sector loses no operator-norm
precision, and the quarter-turn phase is part of a fixed output encoding. -/
theorem restricted_simulation_error
    (A : K →L[ℂ] K) (E : P →L[ℂ] K)
    (H : P →L[ℂ] P) (U : V →L[ℂ] V) (J₁ J₀ : V →L[ℂ] P)
    (hH : H ∘L H = 1) (hJ₁ : J₁† ∘L J₁ = 1)
    (hBlock : H ∘L J₁ = J₀ ∘L U) (ε : ℝ)
    (hSim : ‖A ∘L E - E ∘L
      NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • H)‖ ≤ ε) :
    ‖A ∘L (E ∘L J₁) - (-Complex.I • (E ∘L J₀)) ∘L U‖ ≤ ε := by
  have hExact : E ∘L NormedSpace.exp
      ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • H) ∘L J₁ =
        (-Complex.I • (E ∘L J₀)) ∘L U := by
    rw [exp_quarter_turn H hH, smul_comp, hBlock, comp_smul, smul_comp]
    simp only [comp_assoc]
  calc
    ‖A ∘L (E ∘L J₁) - (-Complex.I • (E ∘L J₀)) ∘L U‖ =
        ‖(A ∘L E - E ∘L NormedSpace.exp
          ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • H)) ∘L J₁‖ := by
      rw [sub_comp]
      simp only [comp_assoc]
      rw [hExact]
    _ ≤ ‖A ∘L E - E ∘L NormedSpace.exp
          ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • H)‖ :=
      (opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _)
          (LabeledSimulationTransfer.isometry_norm_le_one J₁ hJ₁))
    _ ≤ ε := hSim

/-- An actual bounded-query simulation of an involution gives an actual
bounded-query implementation of its unitary block, with one common clean
encoding.  The added gate uses only `E`, `J₀`, and `J₁`; the target family `U`
is never installed as a fixed gate or supplied as an oracle. -/
theorem exists_clean_unitary_program
    (O : L → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : P →L[ℂ] K) (J₁ J₀ : V →L[ℂ] P)
    (hE : E† ∘L E = 1) (hJ₁ : J₁† ∘L J₁ = 1) (hJ₀ : J₀† ∘L J₀ = 1)
    (H : X → P →L[ℂ] P) (U : X → V →L[ℂ] V)
    (hH : ∀ x, H x ∘L H x = 1)
    (hBlock : ∀ x, H x ∘L J₁ = J₀ ∘L U x)
    (p : MultiOracleCircuit.Program O) (ε : ℝ)
    (hSim : ∀ x, ‖p.eval x ∘L E - E ∘L
      NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) • H x)‖ ≤ ε) :
    ∃ q : MultiOracleCircuit.Program (AlignedMultiOracleProgram.oracle O),
      q.count = p.count ∧ (∀ w : L → ℕ, q.cost w = p.cost w) ∧
      (AlignedMultiOracleProgram.input (E ∘L J₁))† ∘L
        AlignedMultiOracleProgram.input (E ∘L J₁) = 1 ∧
      ∀ x, IsUnitary (q.eval x) ∧
        ‖q.eval x ∘L AlignedMultiOracleProgram.input (E ∘L J₁) -
          AlignedMultiOracleProgram.input (E ∘L J₁) ∘L U x‖ ≤ ε := by
  exact AlignedMultiOracleProgram.exists_aligned_program O hO
    (E ∘L J₁) (-Complex.I • (E ∘L J₀))
    (comp_isometry E J₁ hE hJ₁)
    (phase_isometry _ (comp_isometry E J₀ hE hJ₀)) p U ε
    (fun x => restricted_simulation_error (p.eval x) E (H x) (U x) J₁ J₀
      (hH x) hJ₁ (hBlock x) ε (hSim x))

end CleanTransfer

end
end SparseHamiltonian.UnitaryDilationTransfer

/-! ===== UnitaryEntryOracle.lean ===== -/

/-!
# Entry-only oracle reduction for unitary implementation

The two block flags and all simulator work registers are spectators of one
ordinary reversible entry query. A known address permutation swaps the row and
column indices in the lower block. Fixed row and column locators are compiled
into query-free gates. No controlled unknown oracle is assumed.
-/

namespace SparseHamiltonian.UnitaryEntryOracle

noncomputable section
open ContinuousLinearMap OracleCircuit UnitaryEntryData
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

abbrev Base (n Z : Type*) := NativeSparseMaskedAccess.Basis (Index n) Z

/-- The plain entry query ignores the two Boolean flags. -/
def plainTable (D : Data X n Z) (x : X) (a : Index n × Index n) : Z :=
  D.table x (a.1.2, a.2.2)

/-- Expose the flags and qutrit as spectators of the original entry query. -/
def entryBasis : Base n Z ≃ (((Bool × Bool) × Fin 3) × ((n × n) × Z)) where
  toFun a := (((a.1.1.1.1, a.1.1.2.1), a.2), ((a.1.1.1.2, a.1.1.2.2), a.1.2))
  invFun a := ((((a.1.1.1, a.2.1.1), (a.1.1.2, a.2.1.2)), a.2.2), a.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A fixed, explicitly routed representation of one ordinary entry call. -/
def flatEntry (D : Data X n Z) (x : X) :
    EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z) :=
  (NativeSparseMaskedAccess.layout (n := Index n) (Z := Z)).conjStarAlgEquiv
    (LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) (plainTable D) x)

omit [DecidableEq n] [DecidableEq Z] in
/-- This exact full-space identity identifies the only unknown primitive with
one call to the original table, with untouched spectator registers. -/
theorem flatEntry_eq_original (D : Data X n Z) (x : X) :
    flatEntry D x =
      (LookupOracle.permutationUnitary (entryBasis (n := n) (Z := Z))).symm.conjStarAlgEquiv
        ((LookupOracle.permutationUnitary
          (LookupOracle.spectatorEquiv ((Bool × Bool) × Fin 3) D.table x)).toLinearIsometry.toContinuousLinearMap) := by
  ext v a
  rcases a with ⟨⟨⟨⟨b, i⟩, ⟨c, j⟩⟩, z⟩, f⟩
  rfl

/-- Fixed row/column exchange, conditioned only on a known block flag. -/
def routeAddress : (Index n × Index n) ≃ (Index n × Index n) where
  toFun a := if a.1.1 then ((a.1.1, a.2.2), (a.2.1, a.1.2)) else a
  invFun a := if a.1.1 then ((a.1.1, a.2.2), (a.2.1, a.1.2)) else a
  left_inv := by
    rintro ⟨⟨b, i⟩, ⟨c, j⟩⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨⟨b, i⟩, ⟨c, j⟩⟩
    cases b <;> rfl

/-- The value register and qutrit are untouched by the routing gates. -/
def routeBasis : Base n Z ≃ Base n Z :=
  Equiv.prodCongr (Equiv.prodCongr routeAddress (Equiv.refl Z)) (Equiv.refl (Fin 3))

def route : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z) :=
  (LookupOracle.permutationUnitary routeBasis).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] in
theorem route_unitary : IsUnitary (route (n := n) (Z := Z)) :=
  LookupOracle.permutationUnitary_unitary routeBasis

omit [DecidableEq n] [DecidableEq Z] in
theorem flatEntry_unitary (D : Data X n Z) (x : X) : IsUnitary (flatEntry D x) :=
  (LookupControlledGate.oracle_unitary (K := SparseFlagEmbedding.Qutrit)
    (plainTable D) x).transport NativeSparseMaskedAccess.layout

section Native
variable [Nonempty n]

omit [DecidableEq Z] in
/-- One original lookup and two fixed routing gates implement the dilation
value oracle on its entire workspace, including unclean value registers. -/
theorem value_routing (D : Data X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (toNative D) .value x =
      route * (flatEntry D x * route) := by
  ext v a
  rcases a with ⟨⟨⟨⟨b, i⟩, ⟨c, j⟩⟩, z⟩, f⟩
  cases b <;> rfl

/-- A public row-location gate, independent of the input family. -/
def rowBase : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z) :=
  (NativeSparseMaskedAccess.layout (n := Index n) (Z := Z)).conjStarAlgEquiv
    (SparseFlagEmbedding.location (fun _ : PUnit.{1} => UnitaryEntryData.rowOracle (n := n)) PUnit.unit)

/-- A public column-location gate, independent of the input family. -/
def columnBase : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z) :=
  (NativeSparseMaskedAccess.layout (n := Index n) (Z := Z)).conjStarAlgEquiv
    (SparseFlagEmbedding.location (fun _ : PUnit.{1} => UnitaryEntryData.columnOracle (n := n)) PUnit.unit)

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] [Nonempty n] in
theorem rowBase_unitary : IsUnitary (rowBase (n := n) (Z := Z)) := by
  unfold rowBase
  exact (SparseFlagEmbedding.location_unitary (Z := Z)
    (fun _ : PUnit.{1} => UnitaryEntryData.rowOracle (n := n))
    (fun _ => UnitaryEntryData.rowOracle_unitary (n := n)) PUnit.unit).transport
      (NativeSparseMaskedAccess.layout (n := Index n) (Z := Z))

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] [Nonempty n] in
theorem columnBase_unitary : IsUnitary (columnBase (n := n) (Z := Z)) := by
  unfold columnBase
  exact (SparseFlagEmbedding.location_unitary (Z := Z)
    (fun _ : PUnit.{1} => UnitaryEntryData.columnOracle (n := n))
    (fun _ => UnitaryEntryData.columnOracle_unitary (n := n)) PUnit.unit).transport
      (NativeSparseMaskedAccess.layout (n := Index n) (Z := Z))

omit [DecidableEq Z] in
@[simp] theorem flat_row (D : Data X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (toNative D) .rowLocation x = rowBase := rfl

omit [DecidableEq Z] in
@[simp] theorem flat_column (D : Data X n Z) (x : X) :
    NativeSparseMaskedAccess.flatOracle (toNative D) .columnLocation x = columnBase := rfl

end Native

section Lift
variable {B S K : Type*} [Fintype B] [Fintype S]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Unconditional spectator extension preserves operator products. -/
theorem spectator_mul (U V : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    LookupFromBasisOracle.spectator (S := S) (U * V) =
      LookupFromBasisOracle.spectator (S := S) U *
        LookupFromBasisOracle.spectator (S := S) V := by
  unfold LookupFromBasisOracle.spectator
  rw [← map_mul]
  congr 1

omit [Fintype S] [CompleteSpace K] in
/-- The same product rule for nested, unflattened spectator registers. -/
theorem diagonal_mul (U V : K →L[ℂ] K) :
    WeightedClock.diagonal (fun _ : S => U * V) =
      WeightedClock.diagonal (fun _ : S => U) *
        WeightedClock.diagonal (fun _ : S => V) :=
  (WeightedClock.diagonal_comp (fun _ : S => U) (fun _ : S => V)).symm

end Lift

/-- First native-control spectator layer, in the release's flat coordinates.
Every branch receives the call: this operation supplies no oracle control. -/
def firstLift (F : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z)) :
    EuclideanSpace ℂ (NativeCayleyProgram.Basis (Index n) Z) →L[ℂ]
      EuclideanSpace ℂ (NativeCayleyProgram.Basis (Index n) Z) :=
  (NativeDilationLayout.layout (B := Base n Z)).conjStarAlgEquiv
    (MaskedProgram.masked (fun _ : Bool => true)
      (LookupFromBasisOracle.spectator (S := (Bool × Base n Z) × Base n Z) F))

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] in
theorem firstLift_mul
    (U V : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z)) :
    firstLift (U * V) = firstLift U * firstLift V := by
  simp only [firstLift, spectator_mul, MaskedProgram.masked_mul, map_mul]

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] in
theorem firstLift_unitary
    (U : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z))
    (hU : IsUnitary U) : IsUnitary (firstLift U) :=
  (MaskedProgram.masked_unitary (fun _ : Bool => true) _
    (LookupFromBasisOracle.spectator_unitary U hU)).transport NativeDilationLayout.layout

/-- The simulator workspace plus the final clean-output alignment spectator. -/
abbrev Physical (n Z : Type*) [Fintype n] [Fintype Z] (γ η t ε : ℝ) :=
  CleanOutputAlignment.Double
    (ImprovedSparseHamiltonian.Physical (Index n) Z (Fintype.card n) γ η t ε)

/-- Only tensoring with identities and fixed coordinate changes are used to
bring an original entry call to the simulator's final workspace. -/
def lift (γ η t ε : ℝ)
    (F : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z)) :
    Physical n Z γ η t ε →L[ℂ] Physical n Z γ η t ε :=
  WeightedClock.diagonal (fun _ : Bool =>
    WeightedClock.diagonal (fun _ : Bool =>
      MaskedProgram.masked
        (fun _ : ActiveRegisterLayout.Label PUnit.{1}
          (ImprovedNativeSimulation.slots (Fintype.card n : ℝ) γ (η * |t|) ε)
          (ImprovedNativeSimulation.degree (Fintype.card n : ℝ) γ (η * |t|) ε) => true)
        (LookupFromBasisOracle.spectator
          (S := (Bool × NativeCayleyProgram.Basis (Index n) Z) ×
            NativeCayleyProgram.Basis (Index n) Z) (firstLift F))))

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] in
theorem lift_mul (γ η t ε : ℝ)
    (U V : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z)) :
    lift γ η t ε (U * V) = lift γ η t ε U * lift γ η t ε V := by
  simp only [lift, firstLift_mul, spectator_mul, MaskedProgram.masked_mul,
    diagonal_mul]

omit [DecidableEq n] [DecidableEq Z] [AddCommGroup Z] in
theorem lift_unitary (γ η t ε : ℝ)
    (U : EuclideanSpace ℂ (Base n Z) →L[ℂ] EuclideanSpace ℂ (Base n Z))
    (hU : IsUnitary U) : IsUnitary (lift γ η t ε U) :=
  CoherentQuerySchedule.diagonal_unitary _ (fun _ =>
    CoherentQuerySchedule.diagonal_unitary _ (fun _ =>
      MaskedProgram.masked_unitary _ _
        (LookupFromBasisOracle.spectator_unitary _ (firstLift_unitary U hU))))

/-- One ordinary original-entry oracle with the simulator's spectators. The
raw table interpretation is `flatEntry_eq_original`; `lift` adds no control. -/
def oracle (D : Data X n Z) (γ η t ε : ℝ) (x : X) :
    Physical n Z γ η t ε →L[ℂ] Physical n Z γ η t ε :=
  lift γ η t ε (flatEntry D x)

omit [DecidableEq n] [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z) (γ η t ε : ℝ) (x : X) :
    IsUnitary (oracle D γ η t ε x) :=
  lift_unitary γ η t ε _ (flatEntry_unitary D x)

section Compile
variable [Nonempty n]

/-- The existing simulator labels, including final clean-output alignment. -/
abbrev nativeOracle (D : Data X n Z) (γ η t ε : ℝ) :=
  AlignedMultiOracleProgram.oracle
    (ImprovedSparseHamiltonian.oracle (toNative D) γ η t ε)

omit [DecidableEq Z] in
/-- Definitionally, the released simulator only lifts each primitive through
the same unconditional spectator operations. -/
theorem nativeOracle_eq (D : Data X n Z) (γ η t ε : ℝ) (l : Query) (x : X) :
    nativeOracle D γ η t ε l x =
      lift γ η t ε (NativeSparseMaskedAccess.flatOracle (toNative D) l x) := rfl

/-- Known locators become fixed gates, and value queries use one original entry
query bracketed by fixed address permutations. -/
def letter (D : Data X n Z) (γ η t ε : ℝ) :
    Query → OracleCircuit.Program (oracle D γ η t ε)
  | .rowLocation => .fixed (lift γ η t ε rowBase)
      (lift_unitary γ η t ε _ rowBase_unitary)
  | .columnLocation => .fixed (lift γ η t ε columnBase)
      (lift_unitary γ η t ε _ columnBase_unitary)
  | .value => .seq (.fixed (lift γ η t ε route)
        (lift_unitary γ η t ε _ route_unitary))
      (.seq .query (.fixed (lift γ η t ε route)
        (lift_unitary γ η t ε _ route_unitary)))

omit [DecidableEq n] [DecidableEq Z] [Nonempty n] in
@[simp] theorem letter_count_row (D : Data X n Z) (γ η t ε : ℝ) :
    (letter D γ η t ε .rowLocation).count = 0 := rfl

omit [DecidableEq n] [DecidableEq Z] [Nonempty n] in
@[simp] theorem letter_count_column (D : Data X n Z) (γ η t ε : ℝ) :
    (letter D γ η t ε .columnLocation).count = 0 := rfl

omit [DecidableEq n] [DecidableEq Z] [Nonempty n] in
@[simp] theorem letter_count_value (D : Data X n Z) (γ η t ε : ℝ) :
    (letter D γ η t ε .value).count = 1 := rfl

omit [DecidableEq Z] in
theorem letter_eval (D : Data X n Z) (γ η t ε : ℝ) (l : Query) (x : X) :
    (letter D γ η t ε l).eval x = nativeOracle D γ η t ε l x := by
  rw [nativeOracle_eq]
  cases l
  · rfl
  · rfl
  · change lift γ η t ε route *
      (lift γ η t ε (flatEntry D x) * lift γ η t ε route) = _
    rw [← lift_mul, ← lift_mul, ← value_routing]

/-- Exact compilation of the constructed simulator to original-entry queries. -/
def compile (D : Data X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle D γ η t ε)) :
    OracleCircuit.Program (oracle D γ η t ε) :=
  p.compile (letter D γ η t ε)

omit [DecidableEq Z] in
/-- The transformation preserves the entire physical operator, not just a
successful branch or a clean input state. -/
theorem compile_eval (D : Data X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle D γ η t ε)) (x : X) :
    (compile D γ η t ε p).eval x = p.eval x :=
  p.eval_compile (letter D γ η t ε) (letter_eval D γ η t ε) x

omit [DecidableEq Z] in
/-- Only value calls remain, with no multiplicative overhead from controls. -/
theorem compile_count_le (D : Data X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle D γ η t ε)) :
    (compile D γ η t ε p).count ≤ p.count := by
  change (p.compile (letter D γ η t ε)).count ≤ p.count
  rw [MultiOracleCircuit.Program.count_compile]
  calc
    _ ≤ p.cost (fun _ => 1) := p.cost_mono (by intro l; cases l <;> simp)
    _ = p.count := by simp

omit [DecidableEq Z] in
/-- Counting is exact: no locator is counted as an unknown entry operation. -/
theorem compile_count (D : Data X n Z) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (nativeOracle D γ η t ε)) :
    (compile D γ η t ε p).count = p.labelCount .value := by
  change (p.compile (letter D γ η t ε)).count = _
  rw [MultiOracleCircuit.Program.count_compile]
  unfold MultiOracleCircuit.Program.labelCount
  congr 1
  funext l
  cases l <;> simp

end Compile
end
end SparseHamiltonian.UnitaryEntryOracle

/-! ===== UnitaryImplementation.lean ===== -/

/-!
# Constant-error implementation of an entry-access unitary

This extension specialises the released Hamiltonian simulation theorem to the
Hermitian dilation of a unitary matrix. The result constructs a uniform circuit
with one fixed clean encoding, operator-norm error at most `1/4`, and an explicit
absolute constant times `sqrt (card n)` original entry queries. Both forward and
inverse entry queries count. Known locations and coordinate permutations are
free gates; no controlled access to an opaque unitary is assumed.

The mathematical input is an entry table, a fixed bounded decoder, and the
promise that the decoded matrix is unitary. The target matrix itself is not
available as a gate. This result concerns query complexity only.
-/

namespace SparseHamiltonian.UnitaryImplementation

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 3000000

/-- An absolute constant, independent of dimension, value alphabet, decoder
bound, and unknown unitary instance. Constants are inherited from the released
simulator and are not optimised. -/
def queryConstant : ℝ :=
  497664 * (Real.pi / 2 + Real.sqrt ((Real.pi / 2) * Real.log 8) + Real.log 8)

theorem queryConstant_pos : 0 < queryConstant := by
  have hpi : 0 < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  have hlog : 0 < Real.log 8 := Real.log_pos (by norm_num)
  unfold queryConstant
  positivity

/-- The three-term Hamiltonian bound reduces to a square-root dimension bound
at time `π/2`, unit norm, and fixed error `1/4`. -/
theorem constant_budget (N : ℕ) (hN : 0 < N) :
    497664 * (Real.sqrt (N : ℝ) * (1 * |Real.pi / 2|) +
      Real.sqrt ((N : ℝ) * (1 * |Real.pi / 2|) * Real.log (2 / (1 / 4 : ℝ))) +
      Real.log (2 / (1 / 4 : ℝ))) ≤ queryConstant * Real.sqrt (N : ℝ) := by
  have hpi : 0 ≤ Real.pi / 2 := (div_pos Real.pi_pos (by norm_num)).le
  have hNOne : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hN)
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr hNOne
  have hlog : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hAbsorb : Real.log 8 ≤ Real.sqrt (N : ℝ) * Real.log 8 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt hlog
  simp only [one_mul, abs_of_nonneg hpi,
    show (2 / (1 / 4 : ℝ)) = 8 by norm_num]
  rw [mul_assoc (N : ℝ) (Real.pi / 2) (Real.log 8),
    Real.sqrt_mul (Nat.cast_nonneg N)]
  calc
    _ ≤ 497664 * (Real.sqrt (N : ℝ) * (Real.pi / 2) +
        Real.sqrt (N : ℝ) * Real.sqrt ((Real.pi / 2) * Real.log 8) +
        Real.sqrt (N : ℝ) * Real.log 8) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hAbsorb) (by norm_num)
    _ = queryConstant * Real.sqrt (N : ℝ) := by
      unfold queryConstant
      ring

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The simulation workspace and a final clean-output alignment spectator. -/
abbrev Physical (n Z : Type*) [Fintype n] [Fintype Z] (γ : ℝ) :=
  CleanOutputAlignment.Double
    (ImprovedSparseHamiltonian.Physical (UnitaryEntryData.Index n) Z
      (Fintype.card n) γ 1 (Real.pi / 2) (1 / 4))

/-- Intermediate native interface. The next theorem constructs this program;
the entry compiler below eliminates both known location primitives. -/
abbrev nativeOracle (D : UnitaryEntryData.Data X n Z) (γ : ℝ) :=
  AlignedMultiOracleProgram.oracle
    (ImprovedSparseHamiltonian.oracle (UnitaryEntryData.toNative D)
      γ 1 (Real.pi / 2) (1 / 4))

/-- One known clean encoding is used for both input and output. -/
def input (D : UnitaryEntryData.Data X n Z) (γ : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical n Z γ :=
  AlignedMultiOracleProgram.input
    (ImprovedSparseHamiltonian.input (UnitaryEntryData.toNative D)
      γ 1 (Real.pi / 2) (1 / 4) ∘L UnitaryEntryData.includeOne)

/-- Construct the clean implementation before eliminating the known location
labels. The exponential identity and the unitary block relation are proved in
the preceding modules, and are derived here from the decoded-unitary promise. -/
theorem native_implementation (D : UnitaryEntryData.Data X n Z) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : MultiOracleCircuit.Program (nativeOracle D γ),
        (p.count : ℝ) ≤ queryConstant * Real.sqrt (Fintype.card n : ℝ) ∧
        (input D γ)† ∘L input D γ = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ - input D γ ∘L
            SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ (1 / 4 : ℝ) := by
  obtain ⟨γ, hγ, hγOne, _hWidth, p, hCount, hInput, hAction⟩ :=
    ImprovedSparseHamiltonian.simulation (UnitaryEntryData.toNative D)
      1 (Real.pi / 2) (1 / 4) (by norm_num) (by norm_num) (by norm_num)
      (UnitaryEntryData.dilation_hermitian D)
      (UnitaryEntryData.dilation_row_energy D)
      (UnitaryEntryData.dilation_column_energy D)
  obtain ⟨q, hCountEq, _hCosts, hClean, hResult⟩ :=
    UnitaryDilationTransfer.exists_clean_unitary_program
      (ImprovedSparseHamiltonian.oracle (UnitaryEntryData.toNative D)
        γ 1 (Real.pi / 2) (1 / 4))
      (ImprovedSparseHamiltonian.oracle_unitary (UnitaryEntryData.toNative D)
        γ 1 (Real.pi / 2) (1 / 4))
      (ImprovedSparseHamiltonian.input (UnitaryEntryData.toNative D)
        γ 1 (Real.pi / 2) (1 / 4))
      UnitaryEntryData.includeOne UnitaryEntryData.includeZero
      hInput UnitaryEntryData.includeOne_isometry UnitaryEntryData.includeZero_isometry
      (fun x => SparseStateOverlap.matrixOperator (UnitaryEntryData.dilationMatrix D x))
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
      (UnitaryEntryData.dilation_sq D) (UnitaryEntryData.dilation_includeOne D)
      p (1 / 4) (fun x => (hAction x).2)
  refine ⟨γ, hγ, hγOne, q, ?_, hClean, hResult⟩
  rw [hCountEq]
  exact hCount.trans (constant_budget (Fintype.card n) Fintype.card_pos)

/-- The sole unknown primitive is the original entry query. All other
registers are spectators, with fixed coordinate identifications explicitly
proved in `UnitaryEntryOracle.flatEntry_eq_original`. -/
abbrev oracle (D : UnitaryEntryData.Data X n Z) (γ : ℝ) :=
  UnitaryEntryOracle.oracle D γ 1 (Real.pi / 2) (1 / 4)

/-- Constant-error unitary implementation from ordinary reversible entries.
There are at most `queryConstant * sqrt N` original entry or inverse-entry
queries, where `N = card n`. The program and clean encoding are uniform in the
unknown instance `x`, and the output error includes all temporary registers.
This is an existence theorem for an actual oracle circuit, not an assumed
block encoding or an implementation certificate supplied as input. -/
theorem implementation (D : UnitaryEntryData.Data X n Z) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (oracle D γ),
        (p.count : ℝ) ≤ queryConstant * Real.sqrt (Fintype.card n : ℝ) ∧
        (input D γ)† ∘L input D γ = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ - input D γ ∘L
            SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ (1 / 4 : ℝ) := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ := native_implementation D
  refine ⟨γ, hγ, hγOne,
    UnitaryEntryOracle.compile D γ 1 (Real.pi / 2) (1 / 4) p,
    ?_, hInput, ?_⟩
  · have hCompile :
        ((UnitaryEntryOracle.compile D γ 1 (Real.pi / 2) (1 / 4) p).count : ℝ) ≤
          (p.count : ℝ) := by
      exact_mod_cast UnitaryEntryOracle.compile_count_le
        D γ 1 (Real.pi / 2) (1 / 4) p
    exact hCompile.trans hCount
  · intro x
    simpa only [UnitaryEntryOracle.compile_eval] using hAction x

/-- The same circuit works coherently on arbitrary entangled inputs with an
untouched finite reference, without changing its entry-query count. -/
theorem reference_error {R : Type*} [Fintype R]
    (D : UnitaryEntryData.Data X n Z) (γ : ℝ)
    (p : OracleCircuit.Program (oracle D γ))
    (hError : ∀ x, ‖p.eval x ∘L input D γ - input D γ ∘L
      SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ (1 / 4 : ℝ))
    (x : X) (ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n)) :
    ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift (input D γ) ψ) -
      FiniteReferenceLift.lift (input D γ)
        (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (D.matrix x)) ψ)‖ ≤
          (1 / 4 : ℝ) * ‖ψ‖ :=
  FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D γ)
    (SparseStateOverlap.matrixOperator (D.matrix x)) (1 / 4) (hError x) ψ

end
end SparseHamiltonian.UnitaryImplementation




