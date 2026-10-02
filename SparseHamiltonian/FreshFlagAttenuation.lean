import SparseHamiltonian.NativeControlledOracle

/-!
# Query-free attenuation with a genuinely fresh flag

A fixed projection identifies the success subspace. A real plane rotation is
applied between two fresh flag sectors, only on that subspace. The old failure
subspace is left unchanged: existing failure amplitudes are never rotated into
success. The complete operator is proved unitary, including away from the clean
input sector, and is represented by a zero-query circuit.
-/

namespace SparseHamiltonian.FreshFlagAttenuation

noncomputable section
open ContinuousLinearMap OracleCircuit PhaseSubspaceGates GlobalColligation
open scoped InnerProduct
set_option maxHeartbeats 800000

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A fresh two-sector Hilbert flag. -/
abbrev Space (K : Type*) := WithLp 2 (K × K)

/-- Adjoint of an actual continuous two-by-two operator matrix. -/
theorem block_adjoint (A B C D : K →L[ℂ] K) :
    star (blockMap A B C D) = blockMap (star A) (star C) (star B) (star D) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [star_eq_adjoint]
  rw [adjoint_inner_left]
  simp only [blockMap_apply, WithLp.prod_inner_apply, WithLp.fst, WithLp.snd,
    inner_add_left, inner_add_right, adjoint_inner_left]
  abel

omit [CompleteSpace K] in
/-- Product of two actual operator matrices. -/
theorem block_mul (A B C D E F G H : K →L[ℂ] K) :
    blockMap A B C D * blockMap E F G H =
      blockMap (A * E + B * G) (A * F + B * H)
        (C * E + D * G) (C * F + D * H) := by
  ext x
  simp only [mul_apply_eq_comp, blockMap_apply, WithLp.fst, WithLp.snd,
    map_add, add_apply]
  congr 1
  abel_nf

omit [CompleteSpace K] in
@[simp] theorem block_identity :
    blockMap (1 : K →L[ℂ] K) (0 : K →L[ℂ] K) 0 1 = 1 := by
  ext x
  simp only [blockMap_apply, zero_apply, add_zero, zero_add]
  exact WithLp.toLp_ofLp 2 x

/-- Diagonal action: multiply success by `c`, preserve old failure. -/
def diagonal (Q : K →L[ℂ] K) (c : ℝ) : K →L[ℂ] K :=
  1 + ((c : ℂ) - 1) • Q

/-- The amplitude sent to the fresh failure sector. -/
def residual (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)

/-- Full rotation, on both possible values of the fresh flag. -/
def gate (Q : K →L[ℂ] K) (c b : ℝ) : Space K →L[ℂ] Space K :=
  blockMap (diagonal Q c) (-((b : ℂ) • Q)) ((b : ℂ) • Q) (diagonal Q c)

omit [CompleteSpace K] in
@[simp] theorem diagonal_apply (Q : K →L[ℂ] K) (c : ℝ) (v : K) :
    diagonal Q c v = v + ((c : ℂ) - 1) • Q v := by simp [diagonal]

/-- Real coefficients and a self-adjoint projection give a self-adjoint diagonal. -/
theorem diagonal_adjoint (Q : K →L[ℂ] K) (hQ : star Q = Q) (c : ℝ) :
    star (diagonal Q c) = diagonal Q c := by
  simp only [diagonal, star_add, star_one, star_smul, star_sub, hQ,
    Complex.star_def, Complex.conj_ofReal]

/-- The adjoint reverses the rotation angle. -/
theorem gate_adjoint (Q : K →L[ℂ] K) (hQ : star Q = Q) (c b : ℝ) :
    star (gate Q c b) = gate Q c (-b) := by
  simp only [gate, block_adjoint, star_smul, star_neg,
    diagonal_adjoint Q hQ, hQ, Complex.star_def,
    Complex.conj_ofReal, Complex.ofReal_neg, neg_smul, neg_neg]

/-- Exact normalization of the residual amplitude. -/
theorem residual_identity (c : ℝ) (hc : |c| ≤ 1) : c ^ 2 + residual c ^ 2 = 1 := by
  have hc2 : c ^ 2 ≤ 1 := by
    have hh := abs_le.mp hc
    nlinarith
  rw [residual, Real.sq_sqrt (sub_nonneg.mpr hc2)]
  ring

omit [CompleteSpace K] in
/-- Operator identities for the projected rotation. -/
theorem diagonal_square (Q : K →L[ℂ] K) (hQ : Q * Q = Q) (c b : ℝ)
    (hcb : c ^ 2 + b ^ 2 = 1) :
    diagonal Q c * diagonal Q c + ((b : ℂ) • Q) * ((b : ℂ) • Q) = 1 := by
  have hcb' : (c : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hcb
  simp only [diagonal, mul_add, add_mul, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hQ, smul_smul]
  calc
    _ = 1 + ((c : ℂ) ^ 2 + (b : ℂ) ^ 2 - 1) • Q := by module
    _ = 1 := by rw [hcb']; simp

omit [CompleteSpace K] in
/-- The diagonal and off-diagonal blocks commute. -/
theorem diagonal_commutes (Q : K →L[ℂ] K) (c b : ℝ) :
    diagonal Q c * ((b : ℂ) • Q) = ((b : ℂ) • Q) * diagonal Q c := by
  simp only [diagonal, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, smul_add]
  rw [mul_comm ((c : ℂ) - 1) (b : ℂ)]

omit [CompleteSpace K] in
/-- The opposite-angle rotation is a two-sided inverse. -/
theorem gate_inverse (Q : K →L[ℂ] K) (hQ : Q * Q = Q) (c b : ℝ)
    (hcb : c ^ 2 + b ^ 2 = 1) : gate Q c (-b) * gate Q c b = 1 := by
  rw [gate, gate, block_mul]
  simp only [Complex.ofReal_neg, neg_smul, neg_neg, neg_mul, mul_neg, neg_neg]
  have hd := diagonal_square Q hQ c b hcb
  have hm := diagonal_commutes Q c b
  rw [add_comm (((b : ℂ) • Q) * ((b : ℂ) • Q))]
  simp only [hd, hm, neg_add_cancel, block_identity]

/-- Unitarity holds on the entire enlarged workspace, not only clean inputs. -/
theorem gate_unitary (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) (c b : ℝ)
    (hcb : c ^ 2 + b ^ 2 = 1) : IsUnitary (gate Q c b) := by
  constructor
  · rw [gate_adjoint Q hQ.1]
    exact gate_inverse Q hQ.2 c b hcb
  · rw [gate_adjoint Q hQ.1]
    simpa only [neg_neg] using gate_inverse Q hQ.2 c (-b) (by simpa using hcb)

/-- The canonical attenuator for every real gain in the unit interval. -/
def attenuator (Q : K →L[ℂ] K) (c : ℝ) : Space K →L[ℂ] Space K :=
  gate Q c (residual c)

theorem attenuator_unitary (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (c : ℝ) (hc : |c| ≤ 1) : IsUnitary (attenuator Q c) :=
  gate_unitary Q hQ c (residual c) (residual_identity c hc)

/-- Append a genuinely fresh zero flag, retaining every old amplitude. -/
def clean : K →ₗᵢ[ℂ] Space K where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (v, 0)
      map_add' := by
        intro v w
        change WithLp.toLp 2 (v + w, 0) = WithLp.toLp 2 (v + w, (0 : K) + 0)
        rw [zero_add]
      map_smul' := by
        intro z v
        change WithLp.toLp 2 (z • v, 0) = WithLp.toLp 2 (z • v, z • (0 : K))
        rw [smul_zero] }
  norm_map' := WithLp.norm_toLp_fst 2 K K

omit [CompleteSpace K] in
@[simp] theorem clean_apply (v : K) : clean v = WithLp.toLp 2 (v, 0) := rfl

omit [CompleteSpace K] in
/-- Full output on a clean fresh flag. Existing bad amplitudes stay in the
first sector, and only projected good amplitude enters the second sector. -/
theorem attenuator_clean (Q : K →L[ℂ] K) (c : ℝ) (v : K) :
    attenuator Q c (clean v) =
      WithLp.toLp 2 (diagonal Q c v, (residual c : ℂ) • Q v) := by
  simp [attenuator, gate, blockMap_apply, clean_apply]

omit [CompleteSpace K] in
/-- Idempotence in pointwise form. -/
theorem projection_twice (Q : K →L[ℂ] K) (hQ : Q * Q = Q) (v : K) :
    Q (Q v) = Q v := congrArg (fun A : K →L[ℂ] K => A v) hQ

omit [CompleteSpace K] in
/-- The retained good amplitude is exactly the chosen scalar multiple. -/
theorem diagonal_good (Q : K →L[ℂ] K) (hQ : Q * Q = Q) (c : ℝ) (v : K) :
    Q (diagonal Q c v) = (c : ℂ) • Q v := by
  rw [diagonal_apply, map_add, map_smul, projection_twice Q hQ]
  module

omit [CompleteSpace K] in
/-- The pre-existing failure vector is exactly preserved. -/
theorem diagonal_failure (Q : K →L[ℂ] K) (hQ : Q * Q = Q) (c : ℝ) (v : K) :
    (1 - Q) (diagonal Q c v) = (1 - Q) v := by
  change diagonal Q c v - Q (diagonal Q c v) = v - Q v
  rw [diagonal_good Q hQ, diagonal_apply]
  module

omit [CompleteSpace K] in
/-- Success means both the old success test and the fresh flag being zero. -/
theorem attenuator_clean_good (Q : K →L[ℂ] K) (hQ : Q * Q = Q) (c : ℝ) (v : K) :
    Q (attenuator Q c (clean v)).fst = (c : ℂ) • Q v := by
  rw [attenuator_clean]
  exact diagonal_good Q hQ c v

omit [CompleteSpace K] in
/-- No old failure is converted into a good amplitude. -/
theorem attenuator_clean_failure (Q : K →L[ℂ] K) (hQ : Q * Q = Q)
    (c : ℝ) (v : K) :
    (1 - Q) (attenuator Q c (clean v)).fst = (1 - Q) v := by
  rw [attenuator_clean]
  exact diagonal_failure Q hQ c v

/-- The complete attenuated preparation, with both fresh flag sectors retained. -/
def preparation (Q : K →L[ℂ] K) (c : ℝ) : K →L[ℂ] Space K :=
  attenuator Q c ∘L clean.toContinuousLinearMap

/-- The complete preparation is an isometry, even though success was attenuated. -/
theorem preparation_isometry (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (c : ℝ) (hc : |c| ≤ 1) :
    (preparation Q c)† ∘L preparation Q c = 1 := by
  have hU : (attenuator Q c)† ∘L attenuator Q c = 1 :=
    (attenuator_unitary Q hQ c hc).1
  apply (preparation Q c).norm_map_iff_adjoint_comp_self.mp
  intro v
  change ‖attenuator Q c (clean v)‖ = ‖v‖
  rw [(attenuator Q c).norm_map_iff_adjoint_comp_self.mpr hU,
    clean.norm_map]

/-- Attenuation is one fixed gate and requires zero oracle calls. The projection
and gain here are fixed data, independent of the unknown oracle input. -/
def program {X : Type*} (O : X → Space K →L[ℂ] Space K)
    (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) (c : ℝ) (hc : |c| ≤ 1) :
    Program O := .fixed (attenuator Q c) (attenuator_unitary Q hQ c hc)

@[simp] theorem program_count {X : Type*} (O : X → Space K →L[ℂ] Space K)
    (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) (c : ℝ) (hc : |c| ≤ 1) :
    (program O Q hQ c hc).count = 0 := rfl

@[simp] theorem program_eval {X : Type*} (O : X → Space K →L[ℂ] Space K)
    (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) (c : ℝ) (hc : |c| ≤ 1) (x : X) :
    (program O Q hQ c hc).eval x = attenuator Q c := rfl

/-- One-quarter attenuation, used to leave room for amplitude multiplication. -/
theorem quarter_certificate (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) :
    IsUnitary (attenuator Q (1 / 4)) ∧
    (preparation Q (1 / 4))† ∘L preparation Q (1 / 4) = 1 ∧
    ∀ v : K, Q (attenuator Q (1 / 4) (clean v)).fst = (1 / 4 : ℂ) • Q v := by
  refine ⟨attenuator_unitary Q hQ _ (by norm_num),
    preparation_isometry Q hQ _ (by norm_num), ?_⟩
  intro v
  simpa using attenuator_clean_good Q hQ.2 (1 / 4) v

/-- Common workspace with old, fresh-row-failure, and fresh-column-failure sectors. -/
abbrev Triple (K : Type*) := WithLp 2 (K × Space K)

/-- Embed the fresh row failure in its own orthogonal sector. -/
def rowEmbedding : Space K →ₗᵢ[ℂ] Triple K where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (v.fst, WithLp.toLp 2 (v.snd, 0))
      map_add' := by
        intro v w
        change WithLp.toLp 2 (v.fst + w.fst, WithLp.toLp 2 (v.snd + w.snd, 0)) =
          WithLp.toLp 2 (v.fst + w.fst, WithLp.toLp 2 (v.snd + w.snd, (0 : K) + 0))
        rw [zero_add]
      map_smul' := by
        intro z v
        change WithLp.toLp 2 (z • v.fst, WithLp.toLp 2 (z • v.snd, 0)) =
          WithLp.toLp 2 (z • v.fst, WithLp.toLp 2 (z • v.snd, z • (0 : K)))
        rw [smul_zero] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (v.fst, WithLp.toLp 2 (v.snd, (0 : K)))‖ ^ 2 = ‖v‖ ^ 2
    simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
      norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero]

/-- Embed the fresh column failure in a different orthogonal sector. -/
def columnEmbedding : Space K →ₗᵢ[ℂ] Triple K where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (v.fst, WithLp.toLp 2 (0, v.snd))
      map_add' := by
        intro v w
        change WithLp.toLp 2 (v.fst + w.fst, WithLp.toLp 2 (0, v.snd + w.snd)) =
          WithLp.toLp 2 (v.fst + w.fst, WithLp.toLp 2 ((0 : K) + 0, v.snd + w.snd))
        rw [zero_add]
      map_smul' := by
        intro z v
        change WithLp.toLp 2 (z • v.fst, WithLp.toLp 2 (0, z • v.snd)) =
          WithLp.toLp 2 (z • v.fst, WithLp.toLp 2 (z • (0 : K), z • v.snd))
        rw [smul_zero] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2 (v.fst, WithLp.toLp 2 ((0 : K), v.snd))‖ ^ 2 = ‖v‖ ^ 2
    simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
      norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]

omit [CompleteSpace K] in
@[simp] theorem rowEmbedding_apply (v : Space K) :
    rowEmbedding v = WithLp.toLp 2 (v.fst, WithLp.toLp 2 (v.snd, 0)) := rfl

omit [CompleteSpace K] in
@[simp] theorem columnEmbedding_apply (v : Space K) :
    columnEmbedding v = WithLp.toLp 2 (v.fst, WithLp.toLp 2 (0, v.snd)) := rfl

omit [CompleteSpace K] in
/-- Both orientations begin with exactly the same clean fresh workspace. -/
theorem common_clean :
    rowEmbedding.toContinuousLinearMap ∘L (clean : K →ₗᵢ[ℂ] Space K).toContinuousLinearMap =
      columnEmbedding.toContinuousLinearMap ∘L clean.toContinuousLinearMap := by
  ext v
  rfl

/-- Fixed full-space row rotation, acting trivially on the column failure sector. -/
def rowGate (Q : K →L[ℂ] K) (c : ℝ) : Triple K →L[ℂ] Triple K :=
  SubspaceOracle.lift rowEmbedding.toContinuousLinearMap (attenuator Q c)

/-- Fixed full-space column rotation, acting trivially on the row failure sector. -/
def columnGate (Q : K →L[ℂ] K) (c : ℝ) : Triple K →L[ℂ] Triple K :=
  SubspaceOracle.lift columnEmbedding.toContinuousLinearMap (attenuator Q c)

theorem rowGate_unitary (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (c : ℝ) (hc : |c| ≤ 1) : IsUnitary (rowGate Q c) :=
  SubspaceOracle.lift_unitary (rowEmbedding (K := K)).toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self (rowEmbedding (K := K))) _
    (attenuator_unitary Q hQ c hc)

theorem columnGate_unitary (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (c : ℝ) (hc : |c| ≤ 1) : IsUnitary (columnGate Q c) :=
  SubspaceOracle.lift_unitary (columnEmbedding (K := K)).toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self (columnEmbedding (K := K))) _
    (attenuator_unitary Q hQ c hc)

/-- Actual row output map with disjoint fresh-failure label. -/
def rowPreparation (Q : K →L[ℂ] K) (c : ℝ) : K →L[ℂ] Triple K :=
  rowEmbedding.toContinuousLinearMap ∘L preparation Q c

/-- Actual column output map with disjoint fresh-failure label. -/
def columnPreparation (Q : K →L[ℂ] K) (c : ℝ) : K →L[ℂ] Triple K :=
  columnEmbedding.toContinuousLinearMap ∘L preparation Q c

/-- The row output is implemented by the fixed unitary on the common input. -/
theorem rowGate_preparation (Q : K →L[ℂ] K) (c : ℝ) :
    rowGate Q c ∘L rowEmbedding.toContinuousLinearMap ∘L
      (clean : K →ₗᵢ[ℂ] Space K).toContinuousLinearMap = rowPreparation Q c := by
  rw [rowGate, ← comp_assoc, EncodedOracle.lift_comp (rowEmbedding (K := K)).toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self (rowEmbedding (K := K)))]
  rfl

/-- The column output is implemented on the very same common input. -/
theorem columnGate_preparation (Q : K →L[ℂ] K) (c : ℝ) :
    columnGate Q c ∘L rowEmbedding.toContinuousLinearMap ∘L
      (clean : K →ₗᵢ[ℂ] Space K).toContinuousLinearMap = columnPreparation Q c := by
  rw [common_clean, columnGate, ← comp_assoc, EncodedOracle.lift_comp (columnEmbedding (K := K)).toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self (columnEmbedding (K := K)))]
  rfl

omit [CompleteSpace K] in
@[simp] theorem rowPreparation_apply (Q : K →L[ℂ] K) (c : ℝ) (v : K) :
    rowPreparation Q c v = WithLp.toLp 2
      (diagonal Q c v, WithLp.toLp 2 ((residual c : ℂ) • Q v, 0)) := by
  change rowEmbedding (attenuator Q c (clean v)) = _
  rw [attenuator_clean]
  rfl

omit [CompleteSpace K] in
@[simp] theorem columnPreparation_apply (Q : K →L[ℂ] K) (c : ℝ) (v : K) :
    columnPreparation Q c v = WithLp.toLp 2
      (diagonal Q c v, WithLp.toLp 2 (0, (residual c : ℂ) • Q v)) := by
  change columnEmbedding (attenuator Q c (clean v)) = _
  rw [attenuator_clean]
  rfl

/-- Fresh row and column failures have zero overlap, on every input. -/
theorem row_column_overlap (Q : K →L[ℂ] K) (c : ℝ) :
    (rowPreparation Q c)† ∘L columnPreparation Q c =
      (diagonal Q c)† ∘L diagonal Q c := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  simp only [comp_apply, adjoint_inner_left, rowPreparation_apply,
    columnPreparation_apply, WithLp.prod_inner_apply,
    inner_zero_left, inner_zero_right, add_zero]

/-- The retained block weights old failure by one and old success by `c²`. -/
theorem diagonal_gram (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) (c : ℝ) :
    (diagonal Q c)† ∘L diagonal Q c = (1 - Q) + ((c : ℂ) ^ 2) • Q := by
  change star (diagonal Q c) * diagonal Q c = _
  rw [diagonal_adjoint Q hQ.1]
  simp only [diagonal, mul_add, add_mul, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, hQ.2]
  module

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- If old row and column failures were orthogonal, the actual full-state
overlap is attenuated by exactly `c²`. New failures never contaminate it. -/
theorem prepared_overlap (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) (c : ℝ)
    (R C : P →L[ℂ] K) (hbad : R† ∘L (1 - Q) ∘L C = 0) :
    (rowPreparation Q c ∘L R)† ∘L (columnPreparation Q c ∘L C) =
      ((c : ℂ) ^ 2) • (R† ∘L Q ∘L C) := by
  calc
    _ = R† ∘L ((rowPreparation Q c)† ∘L columnPreparation Q c) ∘L C := by
      simp only [adjoint_comp, comp_assoc]
    _ = R† ∘L ((1 - Q) + ((c : ℂ) ^ 2) • Q) ∘L C := by
      rw [row_column_overlap, diagonal_gram Q hQ]
    _ = _ := by
      rw [add_comp, comp_add, hbad]
      simp only [zero_add, comp_smul, smul_comp]

/-- Original bad-overlap orthogonality identifies total overlap with good overlap. -/
theorem overlap_eq_good (Q : K →L[ℂ] K) (R C : P →L[ℂ] K)
    (hbad : R† ∘L (1 - Q) ∘L C = 0) : R† ∘L C = R† ∘L Q ∘L C := by
  have hsplit : R† ∘L C = R† ∘L (1 - Q) ∘L C + R† ∘L Q ∘L C := by
    simp only [sub_comp, one_def, id_comp, comp_sub]
    abel
  simpa only [hbad, zero_add] using hsplit

/-- When old failures were orthogonal, full overlap acquires only the desired
scalar gain; neither fresh failure sector creates an additional overlap. -/
theorem prepared_overlap_full (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) (c : ℝ)
    (R C : P →L[ℂ] K) (hbad : R† ∘L (1 - Q) ∘L C = 0) :
    (rowPreparation Q c ∘L R)† ∘L (columnPreparation Q c ∘L C) =
      ((c : ℂ) ^ 2) • (R† ∘L C) := by
  rw [prepared_overlap Q hQ c R C hbad, overlap_eq_good Q R C hbad]

/-- For quarter-gain attenuation, the row/column overlap is divided by sixteen. -/
theorem quarter_overlap (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (R C : P →L[ℂ] K) (hbad : R† ∘L (1 - Q) ∘L C = 0) :
    (rowPreparation Q (1 / 4) ∘L R)† ∘L (columnPreparation Q (1 / 4) ∘L C) =
      (1 / 16 : ℂ) • (R† ∘L Q ∘L C) := by
  rw [prepared_overlap Q hQ _ R C hbad]
  norm_num

end
end SparseHamiltonian.FreshFlagAttenuation
