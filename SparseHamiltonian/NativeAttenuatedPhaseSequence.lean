import SparseHamiltonian.NativeSparseAttenuation

/-!
# Counted polynomial action after native fresh-flag attenuation

The complete quarter-gain sparse preparation is the oracle-bearing unitary in
this phase circuit. Its signal on a row or column is the old signal divided by
four, and consequently lies in `[0, 1/4]`. Every phase is a fixed gate on the
same full physical workspace. No phase synthesis or approximation guarantee
is assumed in the polynomial output identity.
-/

namespace SparseHamiltonian.NativeAttenuatedPhaseSequence

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding NativeSparseAttenuation
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 600000

/-- The generic counted circuit acts on the preparation's invariant plane.
Keeping this step abstract avoids unfolding the physical native circuit. -/
theorem counted_output {Y L E K : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {O : L → Y → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (hO : ∀ l y, IsUnitary (O l y))
    (F R : E →L[ℂ] K) (y : Y) (hprep : p.eval y ∘L F = R) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection (F ∘L F†))
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (z : ℝ) (hz : |z| ≤ 1) (he : (R†) (Q (R e)) = (z : ℂ) ^ 2 • e)
    (ss : List AmplitudePolynomialSequence.Phases) :
    (InvariantPhaseSequence.nativePrepared p (F ∘L F†) Q hP hQ ss).eval y (F e) =
      PreparationInvariantPlane.plane
        (PreparationInvariantPlane.goodDirection R Q e z)
        (PreparationInvariantPlane.badDirection R Q e z)
        (AmplitudePolynomialSequence.column z (AmplitudePolynomialSequence.polynomials ss).1
          (AmplitudePolynomialSequence.polynomials ss).2) := by
  rw [InvariantPhaseSequence.nativePrepared_eval]
  exact PreparationInvariantPlane.prepared_column (p.eval y) (p.eval_unitary hO y)
    F R hprep hR Q hQ e z hz he ss

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Fixed input projection for the full preparation with fresh flags. -/
def inputProjection (D : Data X n Z s) : Workspace n Z →L[ℂ] Workspace n Z :=
  (NativeSparseAttenuation.input D).toContinuousLinearMap ∘L
    (NativeSparseAttenuation.input D).toContinuousLinearMap†

theorem inputProjection_orthogonal (D : Data X n Z s) :
    PhaseSubspaceGates.IsOrthogonalProjection (inputProjection D) := by
  have h := NativeSparsePhaseSequence.projection_lift
    (NativeSparseAttenuation.input D).toContinuousLinearMap
    (NativeSparseAttenuation.input_adjoint_comp D) 1 (by constructor <;> simp)
  simpa only [one_def, id_comp, inputProjection] using h

/-- Fixed phase list acting on the actual quarter-gain row preparation. -/
def rowProgram (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D) :=
  InvariantPhaseSequence.nativePrepared
    (NativeSparseAttenuation.rowProgram D (1 / 4) (by norm_num))
    (inputProjection D) goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal ss

def columnProgram (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D) :=
  InvariantPhaseSequence.nativePrepared
    (NativeSparseAttenuation.columnProgram D (1 / 4) (by norm_num))
    (inputProjection D) goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal ss

@[simp] theorem rowProgram_count (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    (rowProgram D ss).count = (2 * ss.length + 1) * 3 := by simp [rowProgram]

@[simp] theorem columnProgram_count (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    (columnProgram D ss).count = (2 * ss.length + 1) * 3 := by simp [columnProgram]

theorem rowProgram_cost (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (w : Query → ℕ) :
    (rowProgram D ss).cost w = (2 * ss.length + 1) * (w .rowLocation + 2 * w .value) := by
  rw [rowProgram, InvariantPhaseSequence.nativePrepared_cost, NativeSparseAttenuation.rowProgram_cost]

theorem columnProgram_cost (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (w : Query → ℕ) :
    (columnProgram D ss).cost w = (2 * ss.length + 1) * (w .columnLocation + 2 * w .value) := by
  rw [columnProgram, InvariantPhaseSequence.nativePrepared_cost, NativeSparseAttenuation.columnProgram_cost]

theorem rowProgram_unitary (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    IsUnitary ((rowProgram D ss).eval x) :=
  (rowProgram D ss).eval_unitary (NativeSparseAttenuation.oracles_unitary D) x

theorem columnProgram_unitary (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    IsUnitary ((columnProgram D ss).eval x) :=
  (columnProgram D ss).eval_unitary (NativeSparseAttenuation.oracles_unitary D) x

/-- These signals are analysis parameters only; the circuit never queries row sums. -/
def rowSignal (D : Data X n Z s) (x : X) (i : n) : ℝ :=
  NativeSparsePhaseSequence.rowSignal D x i / 4

def columnSignal (D : Data X n Z s) (x : X) (j : n) : ℝ :=
  NativeSparsePhaseSequence.columnSignal D x j / 4

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rowSignal_nonneg (D : Data X n Z s) (x : X) (i : n) : 0 ≤ rowSignal D x i := by
  exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem columnSignal_nonneg (D : Data X n Z s) (x : X) (j : n) : 0 ≤ columnSignal D x j := by
  exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rowSignal_le_quarter (D : Data X n Z s) (x : X) (i : n) : rowSignal D x i ≤ 1 / 4 := by
  have h := (abs_le.mp (NativeSparsePhaseSequence.rowSignal_bound D x i)).2
  unfold rowSignal
  linarith

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem columnSignal_le_quarter (D : Data X n Z s) (x : X) (j : n) : columnSignal D x j ≤ 1 / 4 := by
  have h := (abs_le.mp (NativeSparsePhaseSequence.columnSignal_bound D x j)).2
  unfold columnSignal
  linarith

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rowSignal_bound (D : Data X n Z s) (x : X) (i : n) : |rowSignal D x i| ≤ 1 := by
  rw [abs_of_nonneg (rowSignal_nonneg D x i)]
  linarith [rowSignal_le_quarter D x i]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem columnSignal_bound (D : Data X n Z s) (x : X) (j : n) : |columnSignal D x j| ≤ 1 := by
  rw [abs_of_nonneg (columnSignal_nonneg D x j)]
  linarith [columnSignal_le_quarter D x j]

/-- The quarter-gain native success eigenvalue is exactly the squared row signal. -/
theorem rowSignal_eigen (D : Data X n Z s) (x : X) (i : n) :
    ((NativeSparseAttenuation.rowState D (1 / 4) x)†)
      (goodProjection (NativeSparseAttenuation.rowState D (1 / 4) x (EuclideanSpace.single i 1))) =
      (rowSignal D x i : ℂ) ^ 2 • EuclideanSpace.single i 1 := by
  have h := congrArg (fun f : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n =>
    f (EuclideanSpace.single i 1)) (NativeSparseAttenuation.row_compression D (1 / 4) x)
  have hs : (rowSignal D x i : ℂ) ^ 2 = (1 / 16 : ℂ) *
      (SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x) i : ℂ) := by
    have hr := NativeSparsePhaseSequence.rowSignal_sq D x i
    have hr' : (NativeSparsePhaseSequence.rowSignal D x i : ℂ) ^ 2 =
        (SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x) i : ℂ) := by
      exact_mod_cast hr
    simp only [rowSignal, Complex.ofReal_div, Complex.ofReal_ofNat, div_pow, hr']
    ring
  rw [hs]
  apply PiLp.ext
  intro j
  have hj := congrArg (fun v : EuclideanSpace ℂ n => v j) h
  by_cases hij : i = j
  · subst j; simpa [SparseSuccessProjection.diagonal, show (4 : ℂ) ^ 2 = 16 by norm_num] using hj
  · simpa [SparseSuccessProjection.diagonal, hij] using hj

/-- The analogous column eigenvalue uses the analytical column sum. -/
theorem columnSignal_eigen (D : Data X n Z s) (x : X) (i : n) :
    ((NativeSparseAttenuation.columnState D (1 / 4) x)†)
      (goodProjection (NativeSparseAttenuation.columnState D (1 / 4) x (EuclideanSpace.single i 1))) =
      (columnSignal D x i : ℂ) ^ 2 • EuclideanSpace.single i 1 := by
  have h := congrArg (fun f : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n =>
    f (EuclideanSpace.single i 1)) (NativeSparseAttenuation.column_compression D (1 / 4) x)
  have hs : (columnSignal D x i : ℂ) ^ 2 = (1 / 16 : ℂ) *
      (SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x) i : ℂ) := by
    have hr := NativeSparsePhaseSequence.columnSignal_sq D x i
    have hr' : (NativeSparsePhaseSequence.columnSignal D x i : ℂ) ^ 2 =
        (SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x) i : ℂ) := by
      exact_mod_cast hr
    simp only [columnSignal, Complex.ofReal_div, Complex.ofReal_ofNat, div_pow, hr']
    ring
  rw [hs]
  apply PiLp.ext
  intro j
  have hj := congrArg (fun v : EuclideanSpace ℂ n => v j) h
  by_cases hij : i = j
  · subst j; simpa [SparseSuccessProjection.diagonal, show (4 : ℂ) ^ 2 = 16 by norm_num] using hj
  · simpa [SparseSuccessProjection.diagonal, hij] using hj

/-- The analytical output plane is allowed to degenerate at zero or unit success. -/
def rowPlane (D : Data X n Z s) (x : X) (i : n) :
    ComplexAmplitudeRotation.Qubit →L[ℂ] Workspace n Z :=
  PreparationInvariantPlane.plane
    (PreparationInvariantPlane.goodDirection (NativeSparseAttenuation.rowState D (1 / 4) x) goodProjection
      (EuclideanSpace.single i 1) (rowSignal D x i))
    (PreparationInvariantPlane.badDirection (NativeSparseAttenuation.rowState D (1 / 4) x) goodProjection
      (EuclideanSpace.single i 1) (rowSignal D x i))

/-- Full output identity for the actual native sparse phase circuit. -/
theorem rowProgram_output (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    (rowProgram D ss).eval x ((NativeSparseAttenuation.input D).toContinuousLinearMap (EuclideanSpace.single i 1)) =
      rowPlane D x i (AmplitudePolynomialSequence.column (rowSignal D x i)
        (AmplitudePolynomialSequence.polynomials ss).1
        (AmplitudePolynomialSequence.polynomials ss).2) := by
  unfold rowProgram rowPlane inputProjection
  have h := counted_output (Y := X) (L := NativeSparseBlockEncoding.Query)
    (E := EuclideanSpace ℂ n) (K := Workspace n Z)
    (O := NativeSparseAttenuation.oracles D)
    (NativeSparseAttenuation.rowProgram D (1 / 4) (by norm_num))
    (NativeSparseAttenuation.oracles_unitary D)
    (NativeSparseAttenuation.input D).toContinuousLinearMap
    (NativeSparseAttenuation.rowState D (1 / 4) x) x
    (NativeSparseAttenuation.row_preparation D (1 / 4) (by norm_num) x)
    (NativeSparseAttenuation.rowState_isometry D (1 / 4) (by norm_num) x)
    goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal
    (EuclideanSpace.single i 1) (rowSignal D x i) (rowSignal_bound D x i)
    (rowSignal_eigen D x i) ss
  with_reducible exact h

/-- Exact good polynomial on each original label; no row-sum query is supplied. -/
theorem rowProgram_good (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    goodProjection ((rowProgram D ss).eval x ((NativeSparseAttenuation.input D).toContinuousLinearMap (EuclideanSpace.single i 1))) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) •
        PreparationInvariantPlane.goodDirection (NativeSparseAttenuation.rowState D (1 / 4) x) goodProjection
          (EuclideanSpace.single i 1) (rowSignal D x i) := by
  rw [rowProgram_output]
  simp only [rowPlane, PreparationInvariantPlane.plane_apply, map_add, map_smul,
    PreparationInvariantPlane.good_fixed _ _ goodProjection_orthogonal,
    PreparationInvariantPlane.bad_kernel _ _ goodProjection_orthogonal,
    AmplitudePolynomialSequence.column_false, smul_zero, add_zero]

/-- A supplied scalar relative approximation bounds the actual good-output error. -/
theorem rowProgram_good_error (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) -
      gain * (rowSignal D x i : ℂ)‖ ≤ δ * |rowSignal D x i|) :
    ‖goodProjection ((rowProgram D ss).eval x ((NativeSparseAttenuation.input D).toContinuousLinearMap (EuclideanSpace.single i 1))) -
      gain • goodProjection (NativeSparseAttenuation.rowState D (1 / 4) x (EuclideanSpace.single i 1))‖ ≤
      δ * ‖goodProjection (NativeSparseAttenuation.rowState D (1 / 4) x (EuclideanSpace.single i 1))‖ := by
  have hg := (PreparationInvariantPlane.good_scale (NativeSparseAttenuation.rowState D (1 / 4) x) goodProjection
    goodProjection_orthogonal (EuclideanSpace.single i 1) (rowSignal D x i)
    (rowSignal_eigen D x i)).symm
  rw [rowProgram_good, hg, smul_smul, ← sub_smul, norm_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (δ * |rowSignal D x i|) *
        ‖PreparationInvariantPlane.goodDirection (NativeSparseAttenuation.rowState D (1 / 4) x) goodProjection
          (EuclideanSpace.single i 1) (rowSignal D x i)‖ :=
      mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    _ = _ := by ring

/-- The analytical output plane is allowed to degenerate at zero or unit success. -/
def columnPlane (D : Data X n Z s) (x : X) (i : n) :
    ComplexAmplitudeRotation.Qubit →L[ℂ] Workspace n Z :=
  PreparationInvariantPlane.plane
    (PreparationInvariantPlane.goodDirection (NativeSparseAttenuation.columnState D (1 / 4) x) goodProjection
      (EuclideanSpace.single i 1) (columnSignal D x i))
    (PreparationInvariantPlane.badDirection (NativeSparseAttenuation.columnState D (1 / 4) x) goodProjection
      (EuclideanSpace.single i 1) (columnSignal D x i))

/-- Full output identity for the actual native sparse phase circuit. -/
theorem columnProgram_output (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    (columnProgram D ss).eval x ((NativeSparseAttenuation.input D).toContinuousLinearMap (EuclideanSpace.single i 1)) =
      columnPlane D x i (AmplitudePolynomialSequence.column (columnSignal D x i)
        (AmplitudePolynomialSequence.polynomials ss).1
        (AmplitudePolynomialSequence.polynomials ss).2) := by
  unfold columnProgram columnPlane inputProjection
  have h := counted_output (Y := X) (L := NativeSparseBlockEncoding.Query)
    (E := EuclideanSpace ℂ n) (K := Workspace n Z)
    (O := NativeSparseAttenuation.oracles D)
    (NativeSparseAttenuation.columnProgram D (1 / 4) (by norm_num))
    (NativeSparseAttenuation.oracles_unitary D)
    (NativeSparseAttenuation.input D).toContinuousLinearMap
    (NativeSparseAttenuation.columnState D (1 / 4) x) x
    (NativeSparseAttenuation.column_preparation D (1 / 4) (by norm_num) x)
    (NativeSparseAttenuation.columnState_isometry D (1 / 4) (by norm_num) x)
    goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal
    (EuclideanSpace.single i 1) (columnSignal D x i) (columnSignal_bound D x i)
    (columnSignal_eigen D x i) ss
  with_reducible exact h

/-- Exact good polynomial on each original label; no row-sum query is supplied. -/
theorem columnProgram_good (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    goodProjection ((columnProgram D ss).eval x ((NativeSparseAttenuation.input D).toContinuousLinearMap (EuclideanSpace.single i 1))) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (columnSignal D x i : ℂ) •
        PreparationInvariantPlane.goodDirection (NativeSparseAttenuation.columnState D (1 / 4) x) goodProjection
          (EuclideanSpace.single i 1) (columnSignal D x i) := by
  rw [columnProgram_output]
  simp only [columnPlane, PreparationInvariantPlane.plane_apply, map_add, map_smul,
    PreparationInvariantPlane.good_fixed _ _ goodProjection_orthogonal,
    PreparationInvariantPlane.bad_kernel _ _ goodProjection_orthogonal,
    AmplitudePolynomialSequence.column_false, smul_zero, add_zero]

/-- A supplied scalar relative approximation bounds the actual good-output error. -/
theorem columnProgram_good_error (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (columnSignal D x i : ℂ) -
      gain * (columnSignal D x i : ℂ)‖ ≤ δ * |columnSignal D x i|) :
    ‖goodProjection ((columnProgram D ss).eval x ((NativeSparseAttenuation.input D).toContinuousLinearMap (EuclideanSpace.single i 1))) -
      gain • goodProjection (NativeSparseAttenuation.columnState D (1 / 4) x (EuclideanSpace.single i 1))‖ ≤
      δ * ‖goodProjection (NativeSparseAttenuation.columnState D (1 / 4) x (EuclideanSpace.single i 1))‖ := by
  have hg := (PreparationInvariantPlane.good_scale (NativeSparseAttenuation.columnState D (1 / 4) x) goodProjection
    goodProjection_orthogonal (EuclideanSpace.single i 1) (columnSignal D x i)
    (columnSignal_eigen D x i)).symm
  rw [columnProgram_good, hg, smul_smul, ← sub_smul, norm_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (δ * |columnSignal D x i|) *
        ‖PreparationInvariantPlane.goodDirection (NativeSparseAttenuation.columnState D (1 / 4) x) goodProjection
          (EuclideanSpace.single i 1) (columnSignal D x i)‖ :=
      mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    _ = _ := by ring

end
end SparseHamiltonian.NativeAttenuatedPhaseSequence
