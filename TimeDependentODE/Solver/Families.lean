import TimeDependentODE.Native.Select
import TimeDependentODE.LCHS.Table
import TimeDependentODE.Continuous.Discretisation
import SparseODE.ODEPublicSourceMesh
import SparseODE.ODECoefficientPadding

/-!
# Sampled generators, source labels and their LCHS product families

For an instance `x`, chronological slot `r` reads the sample `r mod M` of the
coherent time-indexed sparse oracle. Its matrix operator is the represented
generator `generator D hM x r` of `x' = -G x + b`, with Hermitian parts
`dissipative` and `hamiltonian`. A source label `a` (the initial state, or
the forcing term injected at slot `q`) propagates from its start slot onward:
its slot durations are `(T / M) * mask (start a) r`.

The product family of label `a` (`family`) is entire, contractive on the
closed lower half-plane and `T s Λ`-Lipschitz on the real axis, with
`Λ = D.scale` the public decoder scale; at `-i` it is the masked propagator
of the exponential recurrence (`family_neg_I`), and at real frequencies it is
exactly the coherent SELECT branch with the public duration table
(`branchEvolution_eq_family`). Padding labels cancel (`padded_sum`).
-/

namespace SparseHamiltonian.TimeDependentODE.Sampling

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- The represented generator at chronological slot `r`, read from the sample
`r mod M`. -/
def generator (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (r : ℕ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  SparseStateOverlap.matrixOperator (D.matrix (x, TimeDependent.Sampled.sampleIndex hM r))

/-- Hermitian real part of the sampled generator. -/
def dissipative (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (r : ℕ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ODEHermitianReduction.dissipativePart (generator D hM x r)

/-- Hermitian imaginary part of the sampled generator. -/
def hamiltonian (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (r : ℕ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ODEHermitianReduction.hamiltonianPart (generator D hM x r)

/-- Start slot of a source label: the initial state is propagated from slot
`0`, the forcing term of node `q` from slot `q`. -/
def start : Option (Fin M) → ℕ
  | none => 0
  | some q => q

/-- Public duration table of a source label at a time address. -/
def durations (T : ℝ) (a : Option (Fin M)) (r : Fin M) : ℝ := T * mask (start a) r

/-- Public SELECT duration table: every LCHS branch of a source label uses
that label's durations. -/
def durationTable {ι : Type*} (T : ℝ) (b : Option (Fin M) × ι) (r : Fin M) : ℝ :=
  durations T b.1 r

/-- Slot durations of a source label in chronological order. -/
def slotDurations (hM : 0 < M) (T : ℝ) (a : Option (Fin M)) (r : ℕ) : ℝ :=
  durations T a (TimeDependent.Sampled.sampleIndex hM r) / M

/-- The ordered product family of a source label. -/
def family (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (x : X)
    (a : Option (Fin M)) : ℂ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  GaussianLCHS.productFamily (hamiltonian D hM x) (dissipative D hM x)
    (slotDurations hM T a) M

/-- Positivity of the represented dissipative part makes every sampled
generator accretive. -/
theorem generator_accretive (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (r : ℕ) : Accretive (generator D hM x r) :=
  (accretive_iff_dissipative _).mpr
    (ODEPublicSourceMesh.generator_dissipative D
      (x, TimeDependent.Sampled.sampleIndex hM r) (hPSD _))

/-- The public operator-norm bound of the sparse access data. -/
theorem generator_norm_le (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (r : ℕ) :
    ‖generator D hM x r‖ ≤ (s : ℝ) * D.scale := by
  have h := ODEPublicSourceMesh.norm_generator_le D (x, TimeDependent.Sampled.sampleIndex hM r)
  rwa [ODEPublicSourceMesh.generator, norm_neg] at h

theorem dissipative_norm_le (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (r : ℕ) :
    ‖dissipative D hM x r‖ ≤ (s : ℝ) * D.scale :=
  ODEWeightedLCHS.native_dissipative_norm_le D (x, TimeDependent.Sampled.sampleIndex hM r)

theorem decomposition (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (r : ℕ) :
    dissipative D hM x r + Complex.I • hamiltonian D hM x r = generator D hM x r :=
  ODEHermitianReduction.decomposition _

theorem slotDurations_nonneg (hM : 0 < M) (T : ℝ) (hT : 0 ≤ T) (a : Option (Fin M))
    (r : ℕ) : 0 ≤ slotDurations hM T a r :=
  div_nonneg (mul_nonneg hT (mask_nonneg _ _)) (Nat.cast_nonneg M)

theorem slotDurations_le (hM : 0 < M) (T : ℝ) (hT : 0 ≤ T) (a : Option (Fin M))
    (r : ℕ) : slotDurations hM T a r ≤ T / M := by
  unfold slotDurations durations
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
  have hm : mask (start a) (TimeDependent.Sampled.sampleIndex hM r : ℕ) ≤ 1 := by
    unfold mask
    split_ifs <;> norm_num
  calc
    T * mask (start a) (TimeDependent.Sampled.sampleIndex hM r : ℕ) ≤ T * 1 :=
      mul_le_mul_of_nonneg_left hm hT
    _ = T := mul_one T

theorem family_analyticAt (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (x : X)
    (a : Option (Fin M)) (z : ℂ) : AnalyticAt ℂ (family D hM T x a) z :=
  GaussianLCHS.productFamily_analyticAt _ _ _ M z

theorem family_norm_le_one (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (hT : 0 ≤ T)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (a : Option (Fin M)) (z : ℂ) (hz : z.im ≤ 0) :
    ‖family D hM T x a z‖ ≤ 1 :=
  GaussianLCHS.productFamily_norm_le_one _ _ _ M
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (fun r v => by
      have h := hPSD (x, TimeDependent.Sampled.sampleIndex hM r) v
      rwa [ODEMatrixEnergy.matrixOperator_dissipativePart] at h)
    (slotDurations_nonneg hM T hT a) z hz

/-- One public real-axis Lipschitz constant `T s D.scale` serves every
instance and every source label. -/
theorem family_lipschitz (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (hT : 0 ≤ T)
    (x : X) (a : Option (Fin M)) (k l : ℝ) :
    ‖family D hM T x a (k : ℂ) - family D hM T x a (l : ℂ)‖ ≤
      T * ((s : ℝ) * D.scale) * |k - l| := by
  have h := GaussianLCHS.productFamily_lipschitz (hamiltonian D hM x) (dissipative D hM x)
    (slotDurations hM T a) M
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun r => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (slotDurations_nonneg hM T hT a) k l
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  calc
    ∑ r ∈ Finset.range M, slotDurations hM T a r * ‖dissipative D hM x r‖ ≤
        ∑ r ∈ Finset.range M, T / M * ((s : ℝ) * D.scale) :=
      Finset.sum_le_sum (fun r _ => mul_le_mul (slotDurations_le hM T hT a r)
        (dissipative_norm_le D hM x r) (norm_nonneg _) (div_nonneg hT (Nat.cast_nonneg M)))
    _ = T * ((s : ℝ) * D.scale) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- At the pole `-i` the family of label `a` is its masked propagator. -/
theorem family_neg_I (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (x : X)
    (a : Option (Fin M)) :
    family D hM T x a (-Complex.I) =
      maskedPropagator (generator D hM x) (T / M) (start a) M := by
  unfold family maskedPropagator
  rw [GaussianLCHS.productFamily_neg_I]
  apply Select.evolution_congr
  intro r hr
  rw [decomposition]
  have hτ : slotDurations hM T a r = T / M * mask (start a) r := by
    show T * mask (start a) (r % M) / M = T / M * mask (start a) r
    rw [Nat.mod_eq_of_lt hr]
    ring
  rw [hτ]

/-- At a real frequency the family is the coherent SELECT branch with the
public duration table of the source label. -/
theorem branchEvolution_eq_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (hM : 0 < M) (T : ℝ) (x : X)
    (k : Option (Fin M) × ι → ℝ) (a : Option (Fin M)) (i : ι) :
    Select.branchEvolution D hM k (durationTable T) x (a, i) =
      family D hM T x a (k (a, i) : ℂ) := by
  unfold family
  rw [GaussianLCHS.productFamily_ofReal]
  unfold Select.branchEvolution
  congr 1
  funext t
  exact ODEWeightedLCHS.nativeEvolution_eq_evolution D
    (x, TimeDependent.Sampled.sampleIndex hM t) _ _

/-- Opposite padding coefficients on equal padding branches cancel. -/
theorem padded_sum {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (c : ι → ℂ) (k : ι → ℝ) (F : ℂ → V →L[ℂ] V) :
    ∑ i, ODECoefficientPadding.paddedCoefficient c 3 i •
        F (ODECoefficientPadding.paddedNodes k i : ℂ) =
      ∑ j, c j • F (k j : ℂ) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, ODECoefficientPadding.paddedCoefficient,
    ODECoefficientPadding.paddedNodes, neg_smul, neg_add_cancel, add_zero]

end

end SparseHamiltonian.TimeDependentODE.Sampling
