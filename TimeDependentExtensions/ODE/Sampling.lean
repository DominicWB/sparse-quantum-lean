import TimeDependentExtensions.ODE.Select
import TimeDependentExtensions.ODE.Discretisation
import TimeDependentODE.Solver.Target

set_option autoImplicit false

/-!
# Mesh sources, slot generators and their LCHS product families

**Sources on a mesh.** The source register carries the initial state and the `M` weighted
forcing samples `Δ_q b̃_q`, `Δ_q = t_{q+1} - t_q`, of the left-endpoint rule on the mesh
(`sources`). With public norms `r₀` and `rb q` the joint source/LCHS coefficients depend only
on public data (`coefficients`, `actual_coefficients_eq`); their absolute mass is exactly
three (`coefficients_mass`), and the source mass is `B = r₀ + ∑_q Δ_q rb q` (`mass`), the
quadrature of `‖x₀‖ + ∫ ‖b‖` on the mesh.

**Slot generators.** Slot `k` of the `N` slots reads the sample `σ k` (`generator`). A source
label `a` (the initial state, or the forcing of interval `q`) propagates from the start of its
interval: its slot durations are `(T / N) mask(start a, σ k)` (`slotDurations`), so the
released public duration table (`Sampling.durationTable`) applies unchanged.

**Families.** The product family of label `a` (`family`) is entire, contractive on the closed
lower half-plane, `T s Λ`-Lipschitz on the real axis (`Λ = D.scale`), and at `-i` it is the
refined masked propagator of the scheme (`family_neg_I`); at real frequencies it is exactly
the SELECT branch on `N` slots (`branchEvolution_eq_family`).
-/

namespace TimeDependentExtensions

namespace MeshSampling

noncomputable section

open SparseHamiltonian ContinuousLinearMap NativeSparseBlockEncoding
open SparseHamiltonian.TimeDependentODE (mask mask_nonneg Accretive accretive_iff_dissipative)
open SparseHamiltonian.TimeDependentODE.Sampling (start durations durationTable)
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily productFamily_analyticAt
  productFamily_norm_le_one productFamily_lipschitz productFamily_neg_I productFamily_ofReal)
open scoped BigOperators InnerProduct

/-! ### Public sources on a mesh -/

section Sources

variable {M : ℕ}

/-- Public source norms: the initial norm and the forcing norms weighted by the interval
lengths. -/
def norms (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ) : Option (Fin M) → ℝ
  | none => r₀
  | some q => (t ((q : ℕ) + 1) - t q) * rb q

/-- Public source mass, the left-endpoint quadrature of `‖x₀‖ + ∫ ‖b‖` on the mesh. -/
def mass (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ) : ℝ :=
  r₀ + ∑ q : Fin M, (t ((q : ℕ) + 1) - t q) * rb q

theorem sum_norms (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ) :
    ∑ a, norms r₀ t rb a = mass r₀ t rb := by
  rw [Fintype.sum_option]
  rfl

theorem norms_nonneg (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ) (h₀ : 0 ≤ r₀) (ht : Monotone t)
    (hb : ∀ q, 0 ≤ rb q) (a : Option (Fin M)) : 0 ≤ norms r₀ t rb a := by
  cases a with
  | none => exact h₀
  | some q => exact mul_nonneg (sub_nonneg.mpr (ht (Nat.le_succ _))) (hb q)

/-- Source-loading probabilities from public norms only. -/
def probability (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ) (a : Option (Fin M)) : ℝ :=
  norms r₀ t rb a / mass r₀ t rb

/-- The public joint source/LCHS coefficient table. -/
def coefficients {ι : Type*} (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ) (c : ι → ℂ) :
    Option (Fin M) × ι → ℂ :=
  ODESourceCoefficients.productCoeff (probability r₀ t rb) c

/-- The public coefficient mass is exactly that of the LCHS table. -/
theorem coefficients_mass {ι : Type*} [Fintype ι] (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ)
    (h₀ : 0 ≤ r₀) (ht : Monotone t) (hb : ∀ q, 0 ≤ rb q) (hB : 0 < mass r₀ t rb)
    (c : ι → ℂ) (hc : ODECoherentLCU.coefficientMass c = 3) :
    ODECoherentLCU.coefficientMass (coefficients r₀ t rb c) = 3 := by
  unfold coefficients
  rw [ODESourceCoefficients.coefficientMass_product (probability r₀ t rb) c
    (fun a => div_nonneg (norms_nonneg r₀ t rb h₀ ht hb a) hB.le)]
  unfold probability
  rw [← Finset.sum_div, sum_norms, div_self hB.ne', one_mul, hc]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- Source vectors with the public norms have the public mass. -/
theorem mass_eq (z : Option (Fin M) → P) (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ)
    (hz : ∀ a, ‖z a‖ = norms r₀ t rb a) :
    ODESourceBranches.mass z = mass r₀ t rb := by
  unfold ODESourceBranches.mass
  rw [← sum_norms]
  exact Finset.sum_congr rfl (fun a _ => hz a)

omit [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- Source vectors with the public norms have the public coefficients. -/
theorem actual_coefficients_eq {ι : Type*} [Fintype ι] (z : Option (Fin M) → P)
    (r₀ : ℝ) (t : ℕ → ℝ) (rb : Fin M → ℝ) (hz : ∀ a, ‖z a‖ = norms r₀ t rb a) (c : ι → ℂ) :
    ODEActualSourceError.coefficients z c = coefficients r₀ t rb c := by
  have hmass := mass_eq z r₀ t rb hz
  unfold ODEActualSourceError.coefficients coefficients
  congr 1
  funext a
  unfold ODESourceBranches.probability probability
  rw [hz a, hmass]

/-- Source vectors: the initial state and the forcing samples weighted by the interval
lengths. -/
def sources (y0 : P) (t : ℕ → ℝ) (bs : Fin M → P) : Option (Fin M) → P
  | none => y0
  | some q => (t ((q : ℕ) + 1) - t q) • bs q

omit [CompleteSpace P] in
/-- Source vectors of public norms. -/
theorem sources_norm (y0 : P) (t : ℕ → ℝ) (ht : Monotone t) (bs : Fin M → P) (r₀ : ℝ)
    (rb : Fin M → ℝ) (h₀ : ‖y0‖ = r₀) (hb : ∀ q, ‖bs q‖ = rb q) (a : Option (Fin M)) :
    ‖sources y0 t bs a‖ = norms r₀ t rb a := by
  cases a with
  | none => exact h₀
  | some q =>
      simp only [sources, norms, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (ht (Nat.le_succ _))), hb q]

end Sources

/-! ### Slot generators and product families -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- The represented generator at slot `k`, read from the sample `σ k`. -/
def generator (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X) (k : ℕ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  SparseStateOverlap.matrixOperator (D.matrix (x, σ k))

/-- Hermitian real part of the slot generator. -/
def dissipative (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X) (k : ℕ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ODEHermitianReduction.dissipativePart (generator D σ x k)

/-- Hermitian imaginary part of the slot generator. -/
def hamiltonian (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X) (k : ℕ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ODEHermitianReduction.hamiltonianPart (generator D σ x k)

/-- Slot durations of a source label: `(T / N) mask(start a, σ k)`. -/
def slotDurations (σ : ℕ → Fin M) (N : ℕ) (T : ℝ) (a : Option (Fin M)) (k : ℕ) : ℝ :=
  durations T a (σ k) / N

/-- The ordered product family of a source label on `N` slots. -/
def family (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (T : ℝ) (x : X)
    (a : Option (Fin M)) : ℂ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  productFamily (hamiltonian D σ x) (dissipative D σ x)
    (slotDurations σ N T a) N

theorem dissipative_norm_le (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X) (k : ℕ) :
    ‖dissipative D σ x k‖ ≤ (s : ℝ) * D.scale :=
  ODEWeightedLCHS.native_dissipative_norm_le D (x, σ k)

/-- The public operator-norm bound of the sparse access data. -/
theorem generator_norm_le (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X) (k : ℕ) :
    ‖generator D σ x k‖ ≤ (s : ℝ) * D.scale := by
  have h := ODEPublicSourceMesh.norm_generator_le D (x, σ k)
  rwa [ODEPublicSourceMesh.generator, norm_neg] at h

/-- Positivity of the represented dissipative part makes every slot generator accretive. -/
theorem generator_accretive (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (k : ℕ) : Accretive (generator D σ x k) :=
  (accretive_iff_dissipative _).mpr
    (ODEPublicSourceMesh.generator_dissipative D (x, σ k) (hPSD _))

theorem decomposition (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X) (k : ℕ) :
    dissipative D σ x k + Complex.I • hamiltonian D σ x k = generator D σ x k :=
  ODEHermitianReduction.decomposition _

theorem slotDurations_nonneg (σ : ℕ → Fin M) (N : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (a : Option (Fin M)) (k : ℕ) : 0 ≤ slotDurations σ N T a k :=
  div_nonneg (mul_nonneg hT (mask_nonneg _ _)) (Nat.cast_nonneg N)

theorem slotDurations_le (σ : ℕ → Fin M) (N : ℕ) (T : ℝ) (hT : 0 ≤ T) (a : Option (Fin M))
    (k : ℕ) : slotDurations σ N T a k ≤ T / N := by
  unfold slotDurations durations
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  have hm : mask (start a) (σ k : ℕ) ≤ 1 := by
    unfold mask
    split_ifs <;> norm_num
  calc
    T * mask (start a) (σ k : ℕ) ≤ T * 1 := mul_le_mul_of_nonneg_left hm hT
    _ = T := mul_one T

theorem family_analyticAt (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (T : ℝ)
    (x : X) (a : Option (Fin M)) (z : ℂ) : AnalyticAt ℂ (family D σ N T x a) z :=
  productFamily_analyticAt _ _ _ N z

theorem family_norm_le_one (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (T : ℝ)
    (hT : 0 ≤ T)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (a : Option (Fin M)) (z : ℂ) (hz : z.im ≤ 0) :
    ‖family D σ N T x a z‖ ≤ 1 :=
  productFamily_norm_le_one _ _ _ N
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (fun k v => by
      have h := hPSD (x, σ k) v
      rwa [ODEMatrixEnergy.matrixOperator_dissipativePart] at h)
    (slotDurations_nonneg σ N T hT a) z hz

/-- One public real-axis Lipschitz constant `T s D.scale` serves every instance, every source
label and every slot count. -/
theorem family_lipschitz (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) {N : ℕ} (hN : 0 < N)
    (T : ℝ) (hT : 0 ≤ T) (x : X) (a : Option (Fin M)) (k l : ℝ) :
    ‖family D σ N T x a (k : ℂ) - family D σ N T x a (l : ℂ)‖ ≤
      T * ((s : ℝ) * D.scale) * |k - l| := by
  have h := productFamily_lipschitz (hamiltonian D σ x) (dissipative D σ x)
    (slotDurations σ N T a) N
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (slotDurations_nonneg σ N T hT a) k l
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    ∑ k ∈ Finset.range N, slotDurations σ N T a k * ‖dissipative D σ x k‖ ≤
        ∑ k ∈ Finset.range N, T / N * ((s : ℝ) * D.scale) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul (slotDurations_le σ N T hT a k)
        (dissipative_norm_le D σ x k) (norm_nonneg _) (div_nonneg hT (Nat.cast_nonneg N)))
    _ = T * ((s : ℝ) * D.scale) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- At the pole `-i` the family of label `a` is its masked slot propagator. -/
theorem family_neg_I (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (T : ℝ) (x : X)
    (a : Option (Fin M)) :
    family D σ N T x a (-Complex.I) =
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((T / N * mask (start a) (σ k)) • (-generator D σ x k))) N := by
  unfold family
  rw [productFamily_neg_I]
  congr 1
  funext k
  rw [decomposition]
  have hτ : slotDurations σ N T a k = T / N * mask (start a) (σ k) := by
    show T * mask (start a) (σ k) / N = T / N * mask (start a) (σ k)
    ring
  rw [hτ]

/-- At a real frequency the family is the coherent SELECT branch on `N` slots with the public
duration table of the source label. -/
theorem branchEvolution_eq_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (T : ℝ) (x : X)
    (k : Option (Fin M) × ι → ℝ) (a : Option (Fin M)) (i : ι) :
    MeshSelect.branchEvolution D σ N k (durationTable T) x (a, i) =
      family D σ N T x a (k (a, i) : ℂ) := by
  unfold family
  rw [productFamily_ofReal]
  unfold MeshSelect.branchEvolution
  congr 1
  funext t
  exact ODEWeightedLCHS.nativeEvolution_eq_evolution D (x, σ t) _ _

end

end MeshSampling

end TimeDependentExtensions
