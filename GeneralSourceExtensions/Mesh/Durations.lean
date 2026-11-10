import TimeDependentExtensions.ODE.Sampling
import GeneralSourceODE.Durations
import GeneralSourceODE.Branch

/-!
# Node durations, product families and node propagators on a mesh

A mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` (`TimeDependentExtensions.IsMesh`) carries one represented
generator `G̃_r` per interval; the coherent sampled-time clock runs on `N` slots of length `T/N`,
slot `k` reading the sample of the interval containing `k T / N`
(`TimeDependentExtensions.pieceOf`). A source label with start time `t₀` (the initial state at
`0`, node `i` at `v i`) is propagated on interval `r` for the part after `t₀`,

  `meshWidth t₀ t r = max t₀ t_{r+1} - max t₀ t_r ∈ [0, Δ_r]`, `Δ_r = t_{r+1} - t_r`.

The public SELECT table of the label has the entry `T · meshWidth / Δ_r ∈ [0, T]` on sample `r`
(`meshDurations`); every slot of interval `r` evolves for that entry divided by `N`.

* `tableFamily`: the Gaussian-LCHS product family of the slot samples with the slot times of a
  public table `u` (entries in `[0, T]`): entire, contractive on the closed lower half-plane,
  `T s Λ`-Lipschitz on the real axis, the slot propagator at `-i`, and the coherent SELECT branch
  of `MeshSelect` at real frequencies.
* `IsMeshPropagator`: `U t₀ w` is the homogeneous solution with value `w` at `t₀`, solving piece
  `r` on `[max t₀ t_r, t_{r+1}]` for every interval that ends after `t₀` (one-sided derivatives at
  the mesh points, so the pieces may jump there).
* `node_error_nat`: the mesh product `∏_r exp(-meshWidth · G̃_r)` (`meshNodeProduct`) is within
  `‖w‖ ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r - G̃_r‖` of `U(T, t₀) w`, for accretive interval-integrable
  pieces;
* `roundingError`: the rounding `∑_r |c_r T / N - Δ_r|` of the interval lengths to whole slots
  (`c_r` slots in interval `r`), at most `M T / N` (`roundingError_le`) and zero when the mesh
  points lie on the slot grid (`roundingError_eq_zero_of_grid`; the uniform mesh with `N = q M`,
  `roundingError_uniform`);
* `refined_sub_le`: the slot product of the public table is within `Λ · roundingError` of the
  mesh product, `Λ ≥ ‖G̃_r‖`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.Mesh

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE accretive_exp_norm_le_one
  accretive_exp_sub_norm_le)
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily productFamily_analyticAt
  productFamily_norm_le_one productFamily_lipschitz productFamily_neg_I productFamily_ofReal)
open SparseHamiltonian.GeneralSourceODE (startTime)
open scoped BigOperators InnerProduct

/-! ### Durations of a start time on a mesh -/

section Durations

variable {t : ℕ → ℝ} {M : ℕ} {T : ℝ}

/-- The part of interval `r` after the start time `t₀`. -/
def meshWidth (t₀ : ℝ) (t : ℕ → ℝ) (r : ℕ) : ℝ := max t₀ (t (r + 1)) - max t₀ (t r)

theorem meshWidth_nonneg (hmesh : IsMesh t M T) (t₀ : ℝ) (r : ℕ) : 0 ≤ meshWidth t₀ t r :=
  sub_nonneg.mpr (max_le_max le_rfl (hmesh.mono (Nat.le_succ r)))

theorem meshWidth_le (hmesh : IsMesh t M T) (t₀ : ℝ) (r : ℕ) :
    meshWidth t₀ t r ≤ t (r + 1) - t r := by
  have hle := hmesh.mono (Nat.le_succ r)
  unfold meshWidth
  rcases le_total t₀ (t r) with h | h
  · rw [max_eq_right h, max_eq_right (h.trans hle)]
  · rcases le_total t₀ (t (r + 1)) with h' | h'
    · rw [max_eq_left h, max_eq_right h']
      linarith
    · rw [max_eq_left h, max_eq_left h', sub_self]
      exact sub_nonneg.mpr hle

/-- Public duration of a source label on sample `r`: `T · meshWidth / Δ_r` (zero on an empty
interval). -/
def meshDurations {m : ℕ} (t : ℕ → ℝ) (T : ℝ) (v : Fin m → ℝ) (a : Option (Fin m))
    (r : Fin M) : ℝ :=
  T * meshWidth (startTime v a) t r / (t ((r : ℕ) + 1) - t r)

/-- The public SELECT duration table: every LCHS branch of a source label uses that label's
durations. -/
def meshTable {m : ℕ} {ι : Type*} (t : ℕ → ℝ) (T : ℝ) (v : Fin m → ℝ)
    (b : Option (Fin m) × ι) (r : Fin M) : ℝ :=
  meshDurations t T v b.1 r

theorem meshDurations_nonneg {m : ℕ} (hmesh : IsMesh t M T) (hT : 0 ≤ T) (v : Fin m → ℝ)
    (a : Option (Fin m)) (r : Fin M) : 0 ≤ meshDurations t T v a r :=
  div_nonneg (mul_nonneg hT (meshWidth_nonneg hmesh _ r)) (hmesh.length_nonneg r)

theorem meshDurations_le {m : ℕ} (hmesh : IsMesh t M T) (hT : 0 ≤ T) (v : Fin m → ℝ)
    (a : Option (Fin m)) (r : Fin M) : meshDurations t T v a r ≤ T := by
  unfold meshDurations
  rcases (hmesh.length_nonneg r).eq_or_lt with h | h
  · rw [← h, div_zero]
    exact hT
  · rw [div_le_iff₀ h]
    exact mul_le_mul_of_nonneg_left (meshWidth_le hmesh _ r) hT

/-- The slots of interval `r` evolve the label for its part of the interval up to the rounding of
the interval to whole slots, `|c_r T / N - Δ_r|` with `c_r = blockLength r`. -/
theorem block_duration_sub_le {m : ℕ} (hmesh : IsMesh t M T) {N : ℕ} (hN : 0 < N)
    (v : Fin m → ℝ) (a : Option (Fin m)) (r : ℕ) :
    |(blockLength t T N r : ℝ) * (T * meshWidth (startTime v a) t r / (t (r + 1) - t r) / N) -
        meshWidth (startTime v a) t r| ≤
      |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set w := meshWidth (startTime v a) t r with hw
  have hw0 : 0 ≤ w := meshWidth_nonneg hmesh _ r
  have hwΔ : w ≤ t (r + 1) - t r := meshWidth_le hmesh _ r
  rcases (hmesh.length_nonneg r).eq_or_lt with h | h
  · have hw' : w = 0 := le_antisymm (h ▸ hwΔ) hw0
    have hL : (blockLength t T N r : ℝ) * (T * w / (t (r + 1) - t r) / N) - w = 0 := by
      rw [← h, hw', div_zero, zero_div, mul_zero, sub_zero]
    rw [hL, abs_zero]
    exact abs_nonneg _
  · have e : (blockLength t T N r : ℝ) * (T * w / (t (r + 1) - t r) / N) - w =
        w / (t (r + 1) - t r) * ((blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg (div_nonneg hw0 h.le)]
    have hq : w / (t (r + 1) - t r) ≤ 1 := (div_le_one h).mpr hwΔ
    calc w / (t (r + 1) - t r) * |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| ≤
          1 * |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| :=
        mul_le_mul_of_nonneg_right hq (abs_nonneg _)
      _ = _ := one_mul _

/-- **The rounding of the interval lengths to whole slots**:
`∑_{r < M} |c_r T / N - Δ_r|`, with `c_r = blockLength r` slots in interval `r` and
`Δ_r = t_{r+1} - t_r`. -/
def roundingError (t : ℕ → ℝ) (T : ℝ) (N M : ℕ) : ℝ :=
  ∑ r ∈ Finset.range M, |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)|

theorem roundingError_nonneg (t : ℕ → ℝ) (T : ℝ) (N M : ℕ) : 0 ≤ roundingError t T N M :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Every interval is rounded by less than one slot, so the rounding error is at most `M T / N`. -/
theorem roundingError_le (hmesh : IsMesh t M T) (hT : 0 ≤ T) {N : ℕ} (hN : 0 < N) :
    roundingError t T N M ≤ M * (T / N) := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    have ht0 : ∀ r ≤ M, t r = 0 := fun r hr =>
      le_antisymm (hmesh.last ▸ hmesh.mono hr) (hmesh.zero ▸ hmesh.mono (Nat.zero_le r))
    have h : roundingError t 0 N M = 0 := by
      unfold roundingError
      refine Finset.sum_eq_zero fun r hr => ?_
      have hr' := Finset.mem_range.mp hr
      simp [ht0 r hr'.le, ht0 (r + 1) hr']
    rw [h, zero_div, mul_zero]
  · calc roundingError t T N M ≤ ∑ _r ∈ Finset.range M, T / N :=
          Finset.sum_le_sum fun r _ => (blockLength_sub_lt hmesh hpos hN r).le
      _ = M * (T / N) := by simp

/-- **Mesh points on the slot grid are not rounded**: if `t_r = k_r T / N` for natural numbers
`k_r`, `r ≤ M`, the rounding error vanishes. -/
theorem roundingError_eq_zero_of_grid (hmesh : IsMesh t M T) (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    (k : ℕ → ℕ) (hk : ∀ r ≤ M, t r = k r * (T / N)) : roundingError t T N M = 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hTN : 0 < T / N := div_pos hT hNR
  have hstart : ∀ r ≤ M, blockStart t T N r = k r := by
    intro r hr
    unfold blockStart
    rw [hk r hr]
    have e : (k r : ℝ) * (T / N) * N / T = k r := by field_simp
    rw [e, Nat.ceil_natCast]
  unfold roundingError
  refine Finset.sum_eq_zero fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  have hmono : k r ≤ k (r + 1) := by
    have h1 := hmesh.mono (Nat.le_succ r)
    rw [hk r hr'.le, hk (r + 1) hr'] at h1
    exact_mod_cast le_of_mul_le_mul_right h1 hTN
  rw [blockLength, hstart r hr'.le, hstart (r + 1) hr', Nat.cast_sub hmono, hk r hr'.le,
    hk (r + 1) hr', abs_eq_zero]
  ring

/-- On the uniform mesh `t_r = r T / M` with `N = q M` slots, `q > 0`, the rounding error
vanishes. -/
theorem roundingError_uniform (hM : 0 < M) (hT : 0 ≤ T) {q : ℕ} (hq : 0 < q) :
    roundingError (fun r : ℕ => (r : ℝ) * T / M) T (q * M) M = 0 := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    unfold roundingError
    exact Finset.sum_eq_zero fun r _ => by simp
  · have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hmesh : IsMesh (fun r : ℕ => (r : ℝ) * T / M) M T := by
      refine ⟨by simp, by field_simp, fun a b hab => ?_⟩
      apply div_le_div_of_nonneg_right _ hMR.le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hpos.le
    refine roundingError_eq_zero_of_grid hmesh hpos (Nat.mul_pos hq hM) (fun r => q * r)
      fun r _ => ?_
    push_cast
    field_simp

end Durations

/-! ### The product family of a public table -/

section Families

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M m : ℕ}

/-- The ordered product family of a source label on `N` slots with the public table `u`: slot `k`
uses the sample `σ k` for the time `u a (σ k) / N`. -/
def tableFamily (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (x : X) (a : Option (Fin m)) :
    ℂ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  productFamily (MeshSampling.hamiltonian D σ x) (MeshSampling.dissipative D σ x)
    (fun k => u a (σ k) / N) N

theorem tableFamily_analyticAt (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (x : X) (a : Option (Fin m)) (z : ℂ) :
    AnalyticAt ℂ (tableFamily D σ N u x a) z :=
  productFamily_analyticAt _ _ _ N z

theorem tableFamily_norm_le_one (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (hu : ∀ a r, 0 ≤ u a r)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (a : Option (Fin m)) (z : ℂ) (hz : z.im ≤ 0) :
    ‖tableFamily D σ N u x a z‖ ≤ 1 :=
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
    (fun k => div_nonneg (hu a (σ k)) (Nat.cast_nonneg N)) z hz

/-- One public real-axis Lipschitz constant `T s D.scale` serves every instance, every source
label and every table with entries in `[0, T]`. -/
theorem tableFamily_lipschitz (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) {N : ℕ} (hN : 0 < N)
    {T : ℝ} (u : Option (Fin m) → Fin M → ℝ) (hu : ∀ a r, 0 ≤ u a r)
    (huT : ∀ a r, u a r ≤ T) (x : X) (a : Option (Fin m)) (k l : ℝ) :
    ‖tableFamily D σ N u x a (k : ℂ) - tableFamily D σ N u x a (l : ℂ)‖ ≤
      T * ((s : ℝ) * D.scale) * |k - l| := by
  have h := productFamily_lipschitz (MeshSampling.hamiltonian D σ x)
    (MeshSampling.dissipative D σ x) (fun k => u a (σ k) / N) N
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (fun k => div_nonneg (hu a (σ k)) (Nat.cast_nonneg N)) k l
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hT : 0 ≤ T := (hu a ⟨0, (σ 0).pos⟩).trans (huT a _)
  calc
    ∑ k ∈ Finset.range N, u a (σ k) / N * ‖MeshSampling.dissipative D σ x k‖ ≤
        ∑ k ∈ Finset.range N, T / N * ((s : ℝ) * D.scale) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul
        (div_le_div_of_nonneg_right (huT a (σ k)) (Nat.cast_nonneg N))
        (MeshSampling.dissipative_norm_le D σ x k) (norm_nonneg _)
        (div_nonneg hT (Nat.cast_nonneg N)))
    _ = T * ((s : ℝ) * D.scale) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- At the pole `-i` the family is the slot propagator of the table. -/
theorem tableFamily_neg_I (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (x : X) (a : Option (Fin m)) :
    tableFamily D σ N u x a (-Complex.I) =
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((u a (σ k) / N) • (-MeshSampling.generator D σ x k))) N := by
  unfold tableFamily
  rw [productFamily_neg_I]
  congr 1
  funext k
  rw [MeshSampling.decomposition]

/-- At a real frequency the family is the coherent SELECT branch on `N` slots with the table. -/
theorem branchEvolution_eq_tableFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ) (u : Option (Fin m) → Fin M → ℝ)
    (x : X) (k : Option (Fin m) × ι → ℝ) (a : Option (Fin m)) (i : ι) :
    MeshSelect.branchEvolution D σ N k (fun b r => u b.1 r) x (a, i) =
      tableFamily D σ N u x a (k (a, i) : ℂ) := by
  unfold tableFamily
  rw [productFamily_ofReal]
  unfold MeshSelect.branchEvolution
  congr 1
  funext t
  exact ODEWeightedLCHS.nativeEvolution_eq_evolution D (x, σ t) _ _

end Families

/-! ### Propagators on a mesh -/

/-- An ordered product whose first `n` factors are the identity is the identity. -/
theorem evolution_congr_one {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (U : ℕ → P →L[ℂ] P) (n : ℕ) (h : ∀ k < n, U k = 1) : TimeDependent.evolution U n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [TimeDependent.evolution_succ, h n (Nat.lt_succ_self n),
        ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), one_mul]


section Propagator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {t : ℕ → ℝ} {M : ℕ} {T : ℝ}

/-- **Propagators on a mesh.** `U t₀ w` is the homogeneous solution with value `w` at `t₀`: for
every interval ending after `t₀` it solves the piece of that interval on `[max t₀ t_r, t_{r+1}]`,
with one-sided derivatives at the mesh points. -/
def IsMeshPropagator (G : Fin M → ℝ → V →L[ℂ] V) (t : ℕ → ℝ) (T : ℝ)
    (U : ℝ → V → ℝ → V) : Prop :=
  ∀ t₀ ∈ Icc 0 T, ∀ w, U t₀ w t₀ = w ∧
    ∀ r : Fin M, t₀ ≤ t ((r : ℕ) + 1) →
      SolvesODE (G r) 0 (U t₀ w) (max t₀ (t r)) (t ((r : ℕ) + 1))

/-- The mesh product of a start time: interval `r` evolves under `Gs r` for its part after `t₀`. -/
def meshNodeProduct (Gs : ℕ → V →L[ℂ] V) (t : ℕ → ℝ) (M : ℕ) (t₀ : ℝ) : V →L[ℂ] V :=
  TimeDependent.evolution (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Gs r))) M

theorem meshNodeProduct_norm_le_one (hmesh : IsMesh t M T) (Gs : ℕ → V →L[ℂ] V)
    (hGs : ∀ r, Accretive (Gs r)) (t₀ : ℝ) : ‖meshNodeProduct Gs t M t₀‖ ≤ 1 :=
  TimeDependent.evolution_norm_le_one _
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _ (meshWidth_nonneg hmesh t₀ r)) M

set_option maxHeartbeats 1000000 in
/-- **A node propagator against its mesh product** (chronological indexing). -/
theorem node_error_nat (hmesh : IsMesh t M T) (Gq : ℕ → ℝ → V →L[ℂ] V)
    (hG : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (Gq r u))
    (hGint : ∀ r < M, IntervalIntegrable (Gq r) volume (t r) (t (r + 1)))
    (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (y : ℝ → V)
    (hsol : ∀ r < M, t₀ ≤ t (r + 1) → SolvesODE (Gq r) 0 y (max t₀ (t r)) (t (r + 1))) :
    ‖y T - meshNodeProduct Gs t M t₀ (y t₀)‖ ≤
      ‖y t₀‖ * ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖ := by
  have hle : ∀ r, t r ≤ t (r + 1) := fun r => hmesh.mono (Nat.le_succ r)
  have hstep : ∀ m ≤ M,
      ‖y (max t₀ (t m)) -
          TimeDependent.evolution (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Gs r))) m
            (y t₀)‖ ≤
        ‖y t₀‖ * ∑ r ∈ Finset.range m, ∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖ ∧
      ‖y (max t₀ (t m))‖ ≤ ‖y t₀‖ := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [hmesh.zero, max_eq_left ht₀.1, TimeDependent.evolution_zero, one_apply_eq_self,
          sub_self, norm_zero, Finset.sum_range_zero, mul_zero]
        exact ⟨le_rfl, le_rfl⟩
    | succ m ih =>
        intro hm
        have hmM : m < M := by omega
        obtain ⟨ih1, ih2⟩ := ih hmM.le
        set a := max t₀ (t m) with ha
        set c := max t₀ (t (m + 1)) with hc
        have hac : a ≤ c := max_le_max le_rfl (hle m)
        have hI0 : 0 ≤ ∫ u in t m..t (m + 1), ‖Gq m u - Gs m‖ :=
          intervalIntegral.integral_nonneg (hle m) (fun u _ => norm_nonneg _)
        have hE : ‖NormedSpace.exp (meshWidth t₀ t m • (-Gs m))‖ ≤ 1 :=
          accretive_exp_norm_le_one (Gs m) (hGs m) _ (meshWidth_nonneg hmesh t₀ m)
        rw [TimeDependent.evolution_succ, mul_apply_eq_comp, Finset.sum_range_succ, mul_add]
        by_cases hst : t₀ ≤ t (m + 1)
        · have hcm : c = t (m + 1) := max_eq_right hst
          have hsolm := hsol m hmM hst
          rw [← ha, ← hcm] at hsolm
          have hGm : ∀ u ∈ Icc a c, Accretive (Gq m u) := fun u hu =>
            hG m hmM u ⟨(le_max_right t₀ (t m)).trans hu.1, hcm ▸ hu.2⟩
          have hnorm : ∀ u ∈ Icc a c, ‖y u‖ ≤ ‖y t₀‖ := fun u hu =>
            (GeneralSourceODE.homogeneous_norm_le hsolm hGm u hu).trans ih2
          have hint : IntervalIntegrable (Gq m) volume a c := by
            refine (hGint m hmM).mono_set ?_
            rw [uIcc_of_le hac, uIcc_of_le (hle m)]
            exact Icc_subset_Icc (le_max_right _ _) (le_of_eq hcm)
          have h1 := TimeDependentExtensions.ODEMesh.step_error_integral hsolm hac hint
            intervalIntegrable_const (Gs m) (hGs m) 0 ‖y t₀‖ hnorm
          simp only [Pi.zero_apply, smul_zero, add_zero, sub_zero, norm_zero, mul_zero,
            intervalIntegral.integral_zero] at h1
          have hwidth : c - a = meshWidth t₀ t m := rfl
          rw [hwidth] at h1
          have hmono : ∫ u in a..c, ‖Gq m u - Gs m‖ ≤ ∫ u in t m..t (m + 1), ‖Gq m u - Gs m‖ :=
            intervalIntegral.integral_mono_interval (le_max_right _ _) hac (le_of_eq hcm)
              (Filter.Eventually.of_forall fun u => norm_nonneg _)
              (((hGint m hmM).sub intervalIntegrable_const).norm)
          have hsplit : y c - NormedSpace.exp (meshWidth t₀ t m • (-Gs m))
              (TimeDependent.evolution (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Gs r))) m
                (y t₀)) =
              (y c - NormedSpace.exp (meshWidth t₀ t m • (-Gs m)) (y a)) +
                NormedSpace.exp (meshWidth t₀ t m • (-Gs m))
                  (y a - TimeDependent.evolution
                    (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Gs r))) m (y t₀)) := by
            rw [map_sub]
            abel
          refine ⟨?_, hnorm c ⟨hac, le_rfl⟩⟩
          rw [hsplit]
          calc _ ≤ ‖y c - NormedSpace.exp (meshWidth t₀ t m • (-Gs m)) (y a)‖ +
                ‖NormedSpace.exp (meshWidth t₀ t m • (-Gs m))‖ *
                  ‖y a - TimeDependent.evolution
                    (fun r => NormedSpace.exp (meshWidth t₀ t r • (-Gs r))) m (y t₀)‖ :=
                (norm_add_le _ _).trans (add_le_add le_rfl (le_opNorm _ _))
            _ ≤ ‖y t₀‖ * (∫ u in a..c, ‖Gq m u - Gs m‖) +
                1 * (‖y t₀‖ * ∑ r ∈ Finset.range m, ∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖) :=
                add_le_add h1 (mul_le_mul hE ih1 (norm_nonneg _) zero_le_one)
            _ ≤ _ := by
                rw [one_mul, add_comm]
                exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmono (norm_nonneg _))
        · push Not at hst
          have hcm : c = t₀ := max_eq_left hst.le
          have ham : a = t₀ := max_eq_left ((hle m).trans hst.le)
          have hw0 : meshWidth t₀ t m = 0 := by
            change c - a = 0
            rw [hcm, ham, sub_self]
          rw [hw0, zero_smul, NormedSpace.exp_zero, one_apply_eq_self]
          rw [ham] at ih1
          refine ⟨?_, by rw [hcm]⟩
          rw [hcm]
          refine ih1.trans ?_
          have := mul_nonneg (norm_nonneg (y t₀)) hI0
          linarith
  have h := (hstep M le_rfl).1
  rw [hmesh.last, max_eq_right ht₀.2] at h
  exact h

/-- **Refinement into slots.** For the public table of a start time, the slot product is within
`Λ ∑_{r < M} |c_r T / N - Δ_r|` (`roundingError`) of the mesh product. -/
theorem refined_sub_le (hmesh : IsMesh t M T) (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r)) {Λ : ℝ} (hΛ : ∀ r, ‖Gs r‖ ≤ Λ)
    {m : ℕ} (v : Fin m → ℝ) (a : Option (Fin m)) :
    ‖TimeDependent.evolution (fun k => NormedSpace.exp
        ((T * meshWidth (startTime v a) t (slotPiece t T N M k) /
            (t (slotPiece t T N M k + 1) - t (slotPiece t T N M k)) / N) •
          (-Gs (slotPiece t T N M k)))) N -
      meshNodeProduct Gs t M (startTime v a)‖ ≤ roundingError t T N M * Λ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  set e : ℕ → ℝ := fun r => T * meshWidth (startTime v a) t r / (t (r + 1) - t r) / N with he
  have he0 : ∀ r, 0 ≤ e r := fun r =>
    div_nonneg (div_nonneg (mul_nonneg hT.le (meshWidth_nonneg hmesh _ r))
      (hmesh.length_nonneg r)) hNR.le
  have hgroup := evolution_slotPiece (N := N)
    (fun r => NormedSpace.exp (e r • (-Gs r))) hmesh hT
  change ‖TimeDependent.evolution (fun k => (fun r => NormedSpace.exp (e r • (-Gs r)))
      (slotPiece t T N M k)) N - meshNodeProduct Gs t M (startTime v a)‖ ≤ _
  rw [hgroup]
  unfold meshNodeProduct
  have hpow : ∀ r, NormedSpace.exp (e r • (-Gs r)) ^ blockLength t T N r =
      NormedSpace.exp (((blockLength t T N r : ℝ) * e r) • (-Gs r)) := fun r =>
    TimeDependentExtensions.ODEMesh.exp_smul_pow (-Gs r) (e r) _
  simp only [hpow]
  have hstep : ∀ r, ‖NormedSpace.exp (((blockLength t T N r : ℝ) * e r) • (-Gs r)) -
      NormedSpace.exp (meshWidth (startTime v a) t r • (-Gs r))‖ ≤
        |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| * Λ := by
    intro r
    refine (accretive_exp_sub_norm_le (Gs r) (hGs r) _ _
      (mul_nonneg (Nat.cast_nonneg _) (he0 r)) (meshWidth_nonneg hmesh _ r)).trans ?_
    exact mul_le_mul (block_duration_sub_le hmesh hN v a r) (hΛ r) (norm_nonneg _)
      (abs_nonneg _)
  have h1 := SparseHamiltonian.TimeDependent.evolution_sub_norm_le
    (fun r => NormedSpace.exp (((blockLength t T N r : ℝ) * e r) • (-Gs r)))
    (fun r => NormedSpace.exp (meshWidth (startTime v a) t r • (-Gs r)))
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _
      (mul_nonneg (Nat.cast_nonneg _) (he0 r)))
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _ (meshWidth_nonneg hmesh _ r)) M
  refine h1.trans ((Finset.sum_le_sum fun r _ => hstep r).trans (le_of_eq ?_))
  rw [roundingError, Finset.sum_mul]

/-- The refinement bound for every `T ≥ 0`: at `T = 0` both products are the identity. -/
theorem refined_sub_le_of_nonneg (hmesh : IsMesh t M T) (hT : 0 ≤ T) {N : ℕ} (hN : 0 < N)
    (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r)) {Λ : ℝ} (hΛ : ∀ r, ‖Gs r‖ ≤ Λ)
    {m : ℕ} (v : Fin m → ℝ) (a : Option (Fin m)) :
    ‖TimeDependent.evolution (fun k => NormedSpace.exp
        ((T * meshWidth (startTime v a) t (slotPiece t T N M k) /
            (t (slotPiece t T N M k + 1) - t (slotPiece t T N M k)) / N) •
          (-Gs (slotPiece t T N M k)))) N -
      meshNodeProduct Gs t M (startTime v a)‖ ≤ roundingError t T N M * Λ := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    have h1 : TimeDependent.evolution (fun k => NormedSpace.exp
        (((0 : ℝ) * meshWidth (startTime v a) t (slotPiece t 0 N M k) /
            (t (slotPiece t 0 N M k + 1) - t (slotPiece t 0 N M k)) / N) •
          (-Gs (slotPiece t 0 N M k)))) N = 1 := by
      have hf : (fun k => NormedSpace.exp
          (((0 : ℝ) * meshWidth (startTime v a) t (slotPiece t 0 N M k) /
              (t (slotPiece t 0 N M k + 1) - t (slotPiece t 0 N M k)) / N) •
            (-Gs (slotPiece t 0 N M k)))) = fun _ => (1 : V →L[ℂ] V) := by
        funext k
        rw [zero_mul, zero_div, zero_div, zero_smul, NormedSpace.exp_zero]
      rw [hf]
      exact evolution_congr_one _ N (fun _ _ => rfl)
    have ht0 : ∀ r ≤ M, t r = 0 := fun r hr =>
      le_antisymm (hmesh.last ▸ hmesh.mono hr) (hmesh.zero ▸ hmesh.mono (Nat.zero_le r))
    have h2 : meshNodeProduct Gs t M (startTime v a) = 1 := by
      unfold meshNodeProduct
      apply evolution_congr_one
      intro r hr
      have hw : meshWidth (startTime v a) t r = 0 := by
        unfold meshWidth
        rw [ht0 r hr.le, ht0 (r + 1) hr]
        exact sub_self _
      rw [hw, zero_smul, NormedSpace.exp_zero]
    rw [h1, h2, sub_self, norm_zero]
    exact mul_nonneg (roundingError_nonneg t 0 N M) ((norm_nonneg _).trans (hΛ 0))
  · exact refined_sub_le hmesh hpos hN Gs hGs hΛ v a

end Propagator

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
