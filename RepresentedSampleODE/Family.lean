import RepresentedSampleODE.Repair
import GeneralSourceExtensions.Mesh.Theorem

/-!
# The repaired product family of a public table

For an instance `x` with represented samples `G̃_r = D.matrix (x, r)` and negativity bounds
`κ_r ≥ 0`, `Re ⟨w, G̃_r w⟩ ≥ -κ_r ‖w‖²`, the *repaired* product family of a source label uses the
positive repairs `repair D̃_r κ_r` of the dissipative parts in place of `D̃_r`, with the same
Hamiltonian parts and the same public slot durations as `GeneralSourceExtensions.Mesh.tableFamily`:

* `robustFamily`: entire, contractive on the closed lower half-plane, `T s Λ`-Lipschitz on the
  real axis (`Λ = D.scale`), and at `-i` the slot propagator of the repaired generators
  `repair D̃_r κ_r + i H̃_r`;
* `tableFamily_sub_robustFamily`: at a real frequency `k` the represented family (the SELECT
  branch) is within `2 |k| (Λ_κ + ΔR)` of the repaired family, `Λ_κ = ∑_r (t_{r+1} - t_r) κ_r`
  (`negativity`) and `ΔR = refinementError`; the slot sum is regrouped by mesh interval
  (`sum_slotPiece`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding Set
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily productFamily_analyticAt
  productFamily_norm_le_one productFamily_lipschitz productFamily_neg_I)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshWidth meshDurations meshWidth_nonneg
  meshWidth_le meshDurations_nonneg meshDurations_le tableFamily roundingError
  roundingError_nonneg block_duration_sub_le refinementError)
open SparseHamiltonian.GeneralSourceODE (startTime)
open scoped BigOperators InnerProduct

/-! ### Regrouping a slot sum by mesh interval -/

section Regroup

variable {t : ℕ → ℝ} {M N : ℕ} {T : ℝ}

theorem sum_slotPiece_blocks (h : IsMesh t M T) (hT : 0 < T) (f : ℕ → ℝ) :
    ∀ q ≤ M, ∑ j ∈ Finset.range (blockStart t T N q), f (slotPiece t T N M j) =
      ∑ r ∈ Finset.range q, (blockLength t T N r : ℝ) * f r := by
  intro q
  induction q with
  | zero =>
      intro _
      rw [blockStart_zero h]
      simp
  | succ q ih =>
      intro hq
      have hmono : blockStart t T N q ≤ blockStart t T N (q + 1) :=
        blockStart_mono h hT (Nat.le_succ q)
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le _) hmono,
        ← Finset.range_eq_Ico, ih (Nat.le_of_succ_le hq), Finset.sum_range_succ]
      congr 1
      have hblock : ∀ j ∈ Finset.Ico (blockStart t T N q) (blockStart t T N (q + 1)),
          f (slotPiece t T N M j) = f q := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [slotPiece_eq h hT (Nat.lt_of_succ_le hq) hj.1 hj.2]
      rw [Finset.sum_congr rfl hblock, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      rfl

/-- A slot sum of a function of the slot's interval is the mesh sum weighted by the numbers of
slots, `∑_{k < N} f(r(k)) = ∑_{r < M} c_r f(r)`. -/
theorem sum_slotPiece (h : IsMesh t M T) (hT : 0 < T) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.range N, f (slotPiece t T N M j) =
      ∑ r ∈ Finset.range M, (blockLength t T N r : ℝ) * f r := by
  have h1 := sum_slotPiece_blocks (N := N) h hT f M le_rfl
  rwa [blockStart_last h hT] at h1

end Regroup

/-! ### Negativity bounds -/

section Negativity

variable {M : ℕ}

/-- The negativity mass `Λ_κ = ∑_r (t_{r+1} - t_r) κ_r` of negativity bounds on a mesh. -/
def negativity (t : ℕ → ℝ) (κ : Fin M → ℝ) : ℝ :=
  ∑ r : Fin M, (t ((r : ℕ) + 1) - t r) * κ r

theorem negativity_nonneg {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T) {κ : Fin M → ℝ}
    (hκ : ∀ r, 0 ≤ κ r) : 0 ≤ negativity t κ :=
  Finset.sum_nonneg fun r _ => mul_nonneg (hmesh.length_nonneg r) (hκ r)

/-- With nonnegative bounds `0 = κ` is the negativity mass of positive samples. -/
theorem negativity_zero (t : ℕ → ℝ) : negativity t (fun _ : Fin M => (0 : ℝ)) = 0 := by
  simp [negativity]

end Negativity

/-! ### The repaired family -/

section Families

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M m : ℕ}

/-- The repaired dissipative part of slot `k`: the positive repair of the sample `σ k` with its
negativity bound. -/
def repairedDissipative (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (k : ℕ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  repair (MeshSampling.dissipative D σ x k) (κ (σ k))

/-- The repaired generator of slot `k`: `repair D̃ κ + i H̃`. -/
def repairedGenerator (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (k : ℕ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  repairedDissipative D σ x κ k + Complex.I • MeshSampling.hamiltonian D σ x k

/-- The repaired product family of a source label on `N` slots with the public table `u`. -/
def robustFamily (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (x : X) (κ : Fin M → ℝ) (a : Option (Fin m)) :
    ℂ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  productFamily (MeshSampling.hamiltonian D σ x) (repairedDissipative D σ x κ)
    (fun k => u a (σ k) / N) N

/-- A negativity bound of the represented generator bounds the negativity of its dissipative
part. -/
theorem dissipative_negativity (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ)
    (hneg : ∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re)
    (k : ℕ) (w : EuclideanSpace ℂ n) :
    -κ (σ k) * ‖w‖ ^ 2 ≤ (inner ℂ w (MeshSampling.dissipative D σ x k w)).re := by
  unfold MeshSampling.dissipative
  rw [ODEHermitianReduction.real_inner_dissipativePart]
  exact hneg (σ k) w

theorem repairedDissipative_selfAdjoint (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (k : ℕ) :
    star (repairedDissipative D σ x κ k) = repairedDissipative D σ x κ k :=
  repair_selfAdjoint _ (by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ODEHermitianReduction.dissipativePart_selfAdjoint _) _

theorem repairedDissipative_nonneg (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (hneg : ∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re)
    (k : ℕ) (w : EuclideanSpace ℂ n) :
    0 ≤ (inner ℂ w (repairedDissipative D σ x κ k w)).re :=
  repair_nonneg _ (hκ (σ k)) (dissipative_negativity D σ x κ hneg k) w

theorem repairedDissipative_norm_le (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r) (k : ℕ) :
    ‖repairedDissipative D σ x κ k‖ ≤ (s : ℝ) * D.scale :=
  (norm_repair_le _ (hκ (σ k))).trans (MeshSampling.dissipative_norm_le D σ x k)

theorem hamiltonian_norm_le (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X) (k : ℕ) :
    ‖MeshSampling.hamiltonian D σ x k‖ ≤ (s : ℝ) * D.scale :=
  (ODEHermitianReduction.norm_hamiltonianPart_le _).trans (MeshSampling.generator_norm_le D σ x k)

/-- The repaired generator is accretive. -/
theorem repairedGenerator_accretive (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (hneg : ∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re)
    (k : ℕ) : TimeDependentODE.Accretive (repairedGenerator D σ x κ k) := by
  intro w
  have hH : (inner ℂ w (MeshSampling.hamiltonian D σ x k w)).im = 0 :=
    ODEComplexFrequency.inner_im_eq_zero _ (by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _) w
  have h0 := repairedDissipative_nonneg D σ x κ hκ hneg k w
  simp only [repairedGenerator, add_apply, smul_apply, inner_add_right, inner_smul_right,
    Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, hH]
  simpa using h0

/-- The repaired generator is within `2 min(κ, s Λ)` of the represented sample. -/
theorem repairedGenerator_sub_le (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r) (k : ℕ) :
    ‖repairedGenerator D σ x κ k - MeshSampling.generator D σ x k‖ ≤
      2 * min (κ (σ k)) ((s : ℝ) * D.scale) := by
  have hdec := MeshSampling.decomposition D σ x k
  have e : repairedGenerator D σ x κ k - MeshSampling.generator D σ x k =
      repairedDissipative D σ x κ k - MeshSampling.dissipative D σ x k := by
    rw [← hdec, repairedGenerator]
    abel
  rw [e]
  refine (norm_repair_sub_le_min _ (hκ (σ k))).trans ?_
  exact mul_le_mul_of_nonneg_left (min_le_min le_rfl (MeshSampling.dissipative_norm_le D σ x k))
    (by norm_num)

theorem repairedGenerator_norm_le (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (x : X)
    (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r) (k : ℕ) :
    ‖repairedGenerator D σ x κ k‖ ≤ 2 * ((s : ℝ) * D.scale) := by
  unfold repairedGenerator
  calc _ ≤ ‖repairedDissipative D σ x κ k‖ + ‖Complex.I • MeshSampling.hamiltonian D σ x k‖ :=
        norm_add_le _ _
    _ ≤ (s : ℝ) * D.scale + (s : ℝ) * D.scale := by
        refine add_le_add (repairedDissipative_norm_le D σ x κ hκ k) ?_
        rw [norm_smul, Complex.norm_I, one_mul]
        exact hamiltonian_norm_le D σ x k
    _ = 2 * ((s : ℝ) * D.scale) := by ring

theorem robustFamily_analyticAt (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (x : X) (κ : Fin M → ℝ) (a : Option (Fin m)) (z : ℂ) :
    AnalyticAt ℂ (robustFamily D σ N u x κ a) z :=
  productFamily_analyticAt _ _ _ N z

/-- The repaired family is contractive on the closed lower half-plane. -/
theorem robustFamily_norm_le_one (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (hu : ∀ a r, 0 ≤ u a r) (x : X) (κ : Fin M → ℝ)
    (hκ : ∀ r, 0 ≤ κ r)
    (hneg : ∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re)
    (a : Option (Fin m)) (z : ℂ) (hz : z.im ≤ 0) :
    ‖robustFamily D σ N u x κ a z‖ ≤ 1 :=
  productFamily_norm_le_one _ _ _ N
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun k => repairedDissipative_selfAdjoint D σ x κ k)
    (fun k v => repairedDissipative_nonneg D σ x κ hκ hneg k v)
    (fun k => div_nonneg (hu a (σ k)) (Nat.cast_nonneg N)) z hz

/-- The repaired family has the public real-axis Lipschitz constant `T s D.scale` of the
represented family. -/
theorem robustFamily_lipschitz (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) {N : ℕ} (hN : 0 < N)
    {T : ℝ} (u : Option (Fin m) → Fin M → ℝ) (hu : ∀ a r, 0 ≤ u a r)
    (huT : ∀ a r, u a r ≤ T) (x : X) (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r) (a : Option (Fin m))
    (k l : ℝ) :
    ‖robustFamily D σ N u x κ a (k : ℂ) - robustFamily D σ N u x κ a (l : ℂ)‖ ≤
      T * ((s : ℝ) * D.scale) * |k - l| := by
  have h := productFamily_lipschitz (MeshSampling.hamiltonian D σ x)
    (repairedDissipative D σ x κ) (fun k => u a (σ k) / N) N
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun k => repairedDissipative_selfAdjoint D σ x κ k)
    (fun k => div_nonneg (hu a (σ k)) (Nat.cast_nonneg N)) k l
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hT : 0 ≤ T := (hu a ⟨0, (σ 0).pos⟩).trans (huT a _)
  calc
    ∑ k ∈ Finset.range N, u a (σ k) / N * ‖repairedDissipative D σ x κ k‖ ≤
        ∑ k ∈ Finset.range N, T / N * ((s : ℝ) * D.scale) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul
        (div_le_div_of_nonneg_right (huT a (σ k)) (Nat.cast_nonneg N))
        (repairedDissipative_norm_le D σ x κ hκ k) (norm_nonneg _)
        (div_nonneg hT (Nat.cast_nonneg N)))
    _ = T * ((s : ℝ) * D.scale) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-- At the pole `-i` the repaired family is the slot propagator of the repaired generators. -/
theorem robustFamily_neg_I (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (x : X) (κ : Fin M → ℝ) (a : Option (Fin m)) :
    robustFamily D σ N u x κ a (-Complex.I) =
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((u a (σ k) / N) • (-repairedGenerator D σ x κ k))) N := by
  unfold robustFamily
  rw [productFamily_neg_I]
  rfl

/-- At a real frequency the represented family is within `|k| ∑_k τ_k ‖D̃ - repair D̃‖` of the
repaired family. -/
theorem tableFamily_sub_robustFamily_slots (D : Data (X × Fin M) n Z s) (σ : ℕ → Fin M) (N : ℕ)
    (u : Option (Fin m) → Fin M → ℝ) (hu : ∀ a r, 0 ≤ u a r) (x : X) (κ : Fin M → ℝ)
    (a : Option (Fin m)) (k : ℝ) :
    ‖tableFamily D σ N u x a (k : ℂ) - robustFamily D σ N u x κ a (k : ℂ)‖ ≤
      |k| * ∑ j ∈ Finset.range N, u a (σ j) / N *
        ‖MeshSampling.dissipative D σ x j - repairedDissipative D σ x κ j‖ :=
  productFamily_sub_le _ _ _ _ N
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    (fun k => by
      rw [ContinuousLinearMap.star_eq_adjoint]
      exact ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (fun k => repairedDissipative_selfAdjoint D σ x κ k)
    (fun k => div_nonneg (hu a (σ k)) (Nat.cast_nonneg N)) k

end Families

/-! ### The branch comparison in mesh terms -/

section MeshBranch

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M m : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The branch comparison on a mesh.** At a real frequency `k` the represented family of a
source label is within `2 |k| (Λ_κ + ΔR)` of the repaired family. -/
theorem tableFamily_sub_robustFamily (D : Data (X × Fin M) n Z s) (hM : 0 < M) {t : ℕ → ℝ}
    {T : ℝ} (hmesh : IsMesh t M T) (hT : 0 < T) {N : ℕ} (hN : 0 < N) (v : Fin m → ℝ) (x : X)
    (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r) (a : Option (Fin m)) (k : ℝ) :
    ‖tableFamily D (pieceOf t T N hM) N (meshDurations t T v) x a (k : ℂ) -
        robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a (k : ℂ)‖ ≤
      2 * |k| * (negativity t κ + refinementError D t T N) := by
  set σ := pieceOf t T N hM with hσ
  have hu0 := meshDurations_nonneg hmesh hT.le v
  have h := tableFamily_sub_robustFamily_slots D σ N (meshDurations t T v) hu0 x κ a k
  refine h.trans ?_
  -- The slot sum depends on the slot only through its interval.
  set Λ : ℝ := (s : ℝ) * D.scale with hΛ
  have hΛ0 : 0 ≤ Λ := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  let idx : ℕ → Fin M := fun r => ⟨r % M, Nat.mod_lt r hM⟩
  have hidxlt : ∀ r (hr : r < M), idx r = ⟨r, hr⟩ := fun r hr => Fin.ext (Nat.mod_eq_of_lt hr)
  let g : ℕ → ℝ := fun r => meshDurations t T v a (idx r) / N *
    (2 * min (κ (idx r)) Λ)
  have hslot : ∀ j, σ j = idx (slotPiece t T N M j) := fun j =>
    Fin.ext (Nat.mod_eq_of_lt (slotPiece_lt hM j)).symm
  have hterm : ∀ j ∈ Finset.range N, meshDurations t T v a (σ j) / N *
      ‖MeshSampling.dissipative D σ x j - repairedDissipative D σ x κ j‖ ≤
        g (slotPiece t T N M j) := by
    intro j _
    have hd : ‖MeshSampling.dissipative D σ x j - repairedDissipative D σ x κ j‖ ≤
        2 * min (κ (σ j)) Λ := by
      rw [norm_sub_rev]
      refine (norm_repair_sub_le_min _ (hκ (σ j))).trans ?_
      exact mul_le_mul_of_nonneg_left (min_le_min le_rfl
        (MeshSampling.dissipative_norm_le D σ x j)) (by norm_num)
    have hnn : 0 ≤ meshDurations t T v a (σ j) / N :=
      div_nonneg (hu0 a (σ j)) (Nat.cast_nonneg N)
    calc _ ≤ meshDurations t T v a (σ j) / N * (2 * min (κ (σ j)) Λ) :=
          mul_le_mul_of_nonneg_left hd hnn
      _ = g (slotPiece t T N M j) := by
          simp only [g]
          rw [← hslot j]
  have hsum := Finset.sum_le_sum hterm
  rw [sum_slotPiece hmesh hT g] at hsum
  -- Each interval contributes at most `(Δ_r + |c_r T/N - Δ_r|) 2 min(κ_r, Λ)`.
  have hblock : ∀ r ∈ Finset.range M, (blockLength t T N r : ℝ) * g r ≤
      2 * ((t (r + 1) - t r) * κ (idx r)) +
        2 * (Λ * |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)|) := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hdur := block_duration_sub_le hmesh hN v a r
    have hw0 := meshWidth_nonneg hmesh (startTime v a) r
    have hwΔ := meshWidth_le hmesh (startTime v a) r
    have hmd : meshDurations t T v a (idx r) =
        T * meshWidth (startTime v a) t r / (t (r + 1) - t r) := by
      rw [hidxlt r hr']
      rfl
    have hcw : (blockLength t T N r : ℝ) * (meshDurations t T v a (idx r) / N) ≤
        (t (r + 1) - t r) + |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| := by
      rw [hmd]
      have := (abs_le.mp hdur).2
      linarith
    have hmin0 : 0 ≤ min (κ (idx r)) Λ := le_min (hκ _) hΛ0
    have hc0 : 0 ≤ (blockLength t T N r : ℝ) * (meshDurations t T v a (idx r) / N) :=
      mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hu0 a _) (Nat.cast_nonneg N))
    calc (blockLength t T N r : ℝ) * g r =
          (blockLength t T N r : ℝ) * (meshDurations t T v a (idx r) / N) *
            (2 * min (κ (idx r)) Λ) := by simp only [g]; ring
      _ ≤ ((t (r + 1) - t r) + |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)|) *
            (2 * min (κ (idx r)) Λ) :=
          mul_le_mul_of_nonneg_right hcw (by positivity)
      _ ≤ 2 * ((t (r + 1) - t r) * κ (idx r)) +
            2 * (Λ * |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)|) := by
          have hΔ0 := hmesh.length_nonneg r
          have h1 : (t (r + 1) - t r) * min (κ (idx r)) Λ ≤ (t (r + 1) - t r) * κ (idx r) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hΔ0
          have h2 : |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| *
              min (κ (idx r)) Λ ≤
              Λ * |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _)
          nlinarith
  have hsum2 := Finset.sum_le_sum hblock
  have hneg : ∑ r ∈ Finset.range M, (t (r + 1) - t r) * κ (idx r) = negativity t κ := by
    rw [negativity, ← Fin.sum_univ_eq_sum_range (fun r => (t (r + 1) - t r) * κ (idx r)) M]
    apply Finset.sum_congr rfl
    intro r _
    rw [hidxlt r r.isLt]
  have href : ∑ r ∈ Finset.range M,
      Λ * |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| =
        refinementError D t T N := by
    rw [refinementError, roundingError, Finset.mul_sum]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hneg, href] at hsum2
  have hk : 0 ≤ |k| := abs_nonneg k
  calc |k| * ∑ j ∈ Finset.range N, meshDurations t T v a (σ j) / N *
        ‖MeshSampling.dissipative D σ x j - repairedDissipative D σ x κ j‖ ≤
        |k| * (2 * negativity t κ + 2 * refinementError D t T N) :=
      mul_le_mul_of_nonneg_left (hsum.trans hsum2) hk
    _ = 2 * |k| * (negativity t κ + refinementError D t T N) := by ring

end MeshBranch

end

end SparseHamiltonian.RepresentedSampleODE
