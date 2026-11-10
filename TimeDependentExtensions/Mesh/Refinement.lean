import TimeDependentHamiltonian.Continuous.Propagator

set_option autoImplicit false

/-!
# Uniform refinement of a nonuniform mesh

A mesh `0 = t₀ ≤ t₁ ≤ ⋯ ≤ t_M = T` (`IsMesh`) carries one represented sample per interval. The
chronological clock of the released time-dependent simulation runs on a uniform grid of `N` slots of
length `T / N`. Each slot `k` is assigned the interval containing its left endpoint (`slotPiece`;
the proof of `hs:cor:hybrid` refines in the same way: "on each new interval choose the original
sample containing its left endpoint"): the slots `⌈t_r N / T⌉ ≤ k < ⌈t_{r+1} N / T⌉` belong to
interval `r` (`slotPiece_eq`), so the ordered product over the slots splits into one block per
interval (`evolution_blocks`, `refined_evolution_eq`).

On interval `r` the slots evolve under the sample `A_r` for `n_r T / N`, which differs from
the interval length `t_{r+1} - t_r` by less than `T / N` (`blockLength_sub_lt`). Hence, for
self-adjoint samples with `‖A_r‖ ≤ Λ`, the refined product of the slot exponentials is within
`M (T / N) Λ` of the product `∏_r exp(-i (t_{r+1} - t_r) A_r)` over the mesh
(`refined_evolution_sub_le`). Refining further makes this arbitrarily small; the query count
of the clock does not depend on `N`.
-/

namespace TimeDependentExtensions

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap Set
open scoped BigOperators

/-! ### Meshes and their uniform refinement -/

/-- A mesh of `[0, T]` with `M` intervals: `t 0 = 0`, `t M = T` and `t` monotone. -/
structure IsMesh (t : ℕ → ℝ) (M : ℕ) (T : ℝ) : Prop where
  zero : t 0 = 0
  last : t M = T
  mono : Monotone t

namespace IsMesh

variable {t : ℕ → ℝ} {M : ℕ} {T : ℝ}

theorem nonneg (h : IsMesh t M T) (r : ℕ) : 0 ≤ t r := by
  rw [← h.zero]
  exact h.mono (Nat.zero_le r)

theorem le_last (h : IsMesh t M T) {r : ℕ} (hr : r ≤ M) : t r ≤ T := by
  rw [← h.last]
  exact h.mono hr

theorem length_nonneg (h : IsMesh t M T) (r : ℕ) : 0 ≤ t (r + 1) - t r :=
  sub_nonneg.mpr (h.mono (Nat.le_succ r))

theorem sum_length (h : IsMesh t M T) : ∑ r ∈ Finset.range M, (t (r + 1) - t r) = T := by
  rw [Finset.sum_range_sub (f := t), h.last, h.zero, sub_zero]

end IsMesh

/-- The first slot of interval `r`: `⌈t_r N / T⌉`. -/
def blockStart (t : ℕ → ℝ) (T : ℝ) (N r : ℕ) : ℕ := ⌈t r * N / T⌉₊

/-- The interval containing the left endpoint of slot `k`: the largest `r < M` with
`blockStart r ≤ k`. -/
def slotPiece (t : ℕ → ℝ) (T : ℝ) (N M k : ℕ) : ℕ :=
  Nat.findGreatest (fun r => blockStart t T N r ≤ k) (M - 1)

variable {t : ℕ → ℝ} {M N : ℕ} {T : ℝ}

theorem blockStart_zero (h : IsMesh t M T) : blockStart t T N 0 = 0 := by
  simp [blockStart, h.zero]

theorem blockStart_last (h : IsMesh t M T) (hT : 0 < T) : blockStart t T N M = N := by
  have e : T * (N : ℝ) / T = N := by field_simp
  rw [blockStart, h.last, e]
  exact Nat.ceil_natCast N

theorem blockStart_mono (h : IsMesh t M T) (hT : 0 < T) : Monotone (blockStart t T N) := by
  intro r q hrq
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ hT.le
  exact mul_le_mul_of_nonneg_right (h.mono hrq) (Nat.cast_nonneg N)

theorem blockStart_le (h : IsMesh t M T) (hT : 0 < T) {r : ℕ} (hr : r ≤ M) :
    blockStart t T N r ≤ N :=
  (blockStart_mono h hT hr).trans (blockStart_last h hT).le

/-- `t_r ≤ blockStart r · T / N < t_r + T / N`. -/
theorem blockStart_bounds (h : IsMesh t M T) (hT : 0 < T) (hN : 0 < N) (r : ℕ) :
    t r ≤ (blockStart t T N r : ℝ) * (T / N) ∧
      (blockStart t T N r : ℝ) * (T / N) < t r + T / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 ≤ t r * N / T := div_nonneg (mul_nonneg (h.nonneg r) hNR.le) hT.le
  have hle := Nat.le_ceil (t r * N / T)
  have hlt := Nat.ceil_lt_add_one hx
  have hscale : 0 < T / N := div_pos hT hNR
  have key : t r * N / T * (T / N) = t r := by field_simp
  constructor
  · calc t r = t r * N / T * (T / N) := key.symm
      _ ≤ (blockStart t T N r : ℝ) * (T / N) := mul_le_mul_of_nonneg_right hle hscale.le
  · calc (blockStart t T N r : ℝ) * (T / N) < (t r * N / T + 1) * (T / N) :=
          mul_lt_mul_of_pos_right hlt hscale
      _ = t r + T / N := by rw [add_mul, key, one_mul]

/-- The number of slots of interval `r`. -/
def blockLength (t : ℕ → ℝ) (T : ℝ) (N r : ℕ) : ℕ :=
  blockStart t T N (r + 1) - blockStart t T N r

/-- The slots of interval `r` last `T/N` less or more than the interval itself. -/
theorem blockLength_sub_lt (h : IsMesh t M T) (hT : 0 < T) (hN : 0 < N) (r : ℕ) :
    |(blockLength t T N r : ℝ) * (T / N) - (t (r + 1) - t r)| < T / N := by
  have hmono : blockStart t T N r ≤ blockStart t T N (r + 1) :=
    blockStart_mono h hT (Nat.le_succ r)
  have h1 := blockStart_bounds (N := N) h hT hN r
  have h2 := blockStart_bounds (N := N) h hT hN (r + 1)
  have hcast : (blockLength t T N r : ℝ) =
      (blockStart t T N (r + 1) : ℝ) - (blockStart t T N r : ℝ) := by
    rw [blockLength, Nat.cast_sub hmono]
  rw [hcast, abs_lt]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem slotPiece_lt (hM : 0 < M) (k : ℕ) : slotPiece t T N M k < M :=
  lt_of_le_of_lt (Nat.findGreatest_le (M - 1)) (by omega)

/-- Slot `k` of the refinement into `N` slots uses the sample of the mesh interval containing
it. -/
def pieceOf (t : ℕ → ℝ) (T : ℝ) (N : ℕ) (hM : 0 < M) (k : ℕ) : Fin M :=
  ⟨slotPiece t T N M k, slotPiece_lt hM k⟩

/-- The slots of interval `r` are exactly `blockStart r ≤ k < blockStart (r + 1)`. -/
theorem slotPiece_eq (h : IsMesh t M T) (hT : 0 < T) {r k : ℕ} (hr : r < M)
    (hk1 : blockStart t T N r ≤ k) (hk2 : k < blockStart t T N (r + 1)) :
    slotPiece t T N M k = r := by
  rw [slotPiece, Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ => hk1, fun q hq _ hP => ?_⟩
  have hmono := blockStart_mono (N := N) h hT (show r + 1 ≤ q by omega)
  omega

/-! ### Ordered products over blocks -/

section Products

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

theorem orderedProduct_add (u : ℕ → P →L[ℂ] P) (k a b : ℕ) :
    TimeDependent.orderedProduct u k (a + b) =
      TimeDependent.orderedProduct u (k + a) b *
        TimeDependent.orderedProduct u k a := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, TimeDependent.orderedProduct_succ,
      TimeDependent.orderedProduct_succ, ih, mul_assoc, add_assoc]

/-- An ordered product splits into consecutive blocks. -/
theorem evolution_blocks (A : ℕ → P →L[ℂ] P) (kb : ℕ → ℕ) (hkb0 : kb 0 = 0)
    (hmono : Monotone kb) (M : ℕ) :
    evolution A (kb M) = evolution
      (fun r => TimeDependent.orderedProduct A (kb r) (kb (r + 1) - kb r)) M := by
  induction M with
  | zero => rw [hkb0]; rfl
  | succ M ih =>
    have hle : kb M ≤ kb (M + 1) := hmono (Nat.le_succ M)
    rw [evolution_succ, ← ih]
    have hsplit : kb (M + 1) = kb M + (kb (M + 1) - kb M) := by omega
    change TimeDependent.orderedProduct A 0 (kb (M + 1)) = _
    rw [hsplit, orderedProduct_add, zero_add, ← hsplit]
    rfl

/-- Ordered products depend only on the factors used. -/
theorem evolution_congr' (U U' : ℕ → P →L[ℂ] P) (m : ℕ) (h : ∀ k < m, U k = U' k) :
    evolution U m = evolution U' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [evolution_succ, evolution_succ, h m (Nat.lt_succ_self m),
      ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

theorem orderedProduct_congr_const (A : ℕ → P →L[ℂ] P) (B : P →L[ℂ] P) (k m : ℕ)
    (h : ∀ j < m, A (k + j) = B) :
    TimeDependent.orderedProduct A k m = B ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [TimeDependent.orderedProduct_succ, h m (Nat.lt_succ_self m),
      ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), pow_succ']

/-- A slot product whose factors depend only on the mesh interval of the slot is the mesh
product of the block powers. -/
theorem evolution_slotPiece (f : ℕ → P →L[ℂ] P) (h : IsMesh t M T) (hT : 0 < T) :
    evolution (fun k => f (slotPiece t T N M k)) N =
      evolution (fun r => f r ^ blockLength t T N r) M := by
  have hlast := blockStart_last (N := N) h hT
  calc evolution (fun k => f (slotPiece t T N M k)) N =
        evolution (fun k => f (slotPiece t T N M k)) (blockStart t T N M) := by rw [hlast]
    _ = evolution (fun r => TimeDependent.orderedProduct (fun k => f (slotPiece t T N M k))
          (blockStart t T N r) (blockStart t T N (r + 1) - blockStart t T N r)) M :=
        evolution_blocks _ (blockStart t T N) (blockStart_zero h) (blockStart_mono h hT) M
    _ = _ := by
      apply evolution_congr'
      intro r hr
      have hmono := blockStart_mono (N := N) h hT (Nat.le_succ r)
      apply orderedProduct_congr_const
      intro j hj
      show f (slotPiece t T N M (blockStart t T N r + j)) = f r
      rw [slotPiece_eq h hT hr (by omega) (by omega)]

end Products

/-! ### The refined product of sampled exponentials -/

section Refined

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The slot exponentials of the samples, on `N` slots of length `T / N`. -/
def refinedEvolution (A : ℕ → P →L[ℂ] P) (t : ℕ → ℝ) (T : ℝ) (N M : ℕ) : P →L[ℂ] P :=
  evolution (fun k => NormedSpace.exp ((-Complex.I * ((T / N : ℝ) : ℂ)) •
    A (slotPiece t T N M k))) N

/-- The product of the sampled exponentials over the mesh. -/
def meshEvolution (A : ℕ → P →L[ℂ] P) (t : ℕ → ℝ) (M : ℕ) : P →L[ℂ] P :=
  evolution (fun r => NormedSpace.exp ((-Complex.I * ((t (r + 1) - t r : ℝ) : ℂ)) • A r)) M

theorem exp_skew_norm_le (A : P →L[ℂ] P) (hA : star A = A) (θ : ℝ) :
    ‖NormedSpace.exp ((-Complex.I * (θ : ℂ)) • A)‖ ≤ 1 := by
  apply CayleyApproximation.skew_exp_norm_le
  rw [star_smul, hA, ← neg_smul]
  congr 1
  simp [Complex.conj_ofReal]

/-- The exponential of a sum of commuting operators. -/
theorem exp_add_commute (X Y : P →L[ℂ] P) (h : Commute X Y) :
    NormedSpace.exp (X + Y) = NormedSpace.exp X * NormedSpace.exp Y :=
  NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) h
    ((NormedSpace.expSeries_radius_eq_top ℂ (P →L[ℂ] P)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ (P →L[ℂ] P)).symm ▸ edist_lt_top _ _)

/-- `n` slots of length `h` under one sample give the exponential of `n h`. -/
theorem exp_pow (A : P →L[ℂ] P) (h : ℝ) (n : ℕ) :
    NormedSpace.exp ((-Complex.I * (h : ℂ)) • A) ^ n =
      NormedSpace.exp ((-Complex.I * ((n * h : ℝ) : ℂ)) • A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← exp_add_commute]
    · congr 1
      rw [← add_smul]
      congr 1
      push_cast
      ring
    · exact (Commute.refl A).smul_left _ |>.smul_right _

/-- `‖exp(-i a A) - exp(-i b A)‖ ≤ |a - b| ‖A‖` for self-adjoint `A`. -/
theorem exp_sub_exp_norm_le (A : P →L[ℂ] P) (hA : star A = A) (a b : ℝ) :
    ‖NormedSpace.exp ((-Complex.I * (a : ℂ)) • A) -
      NormedSpace.exp ((-Complex.I * (b : ℂ)) • A)‖ ≤ |a - b| * ‖A‖ := by
  let X : P →L[ℂ] P := (-Complex.I) • A
  have hf : ∀ θ : ℝ, NormedSpace.exp ((-Complex.I * (θ : ℂ)) • A) =
      NormedSpace.exp (θ • X) := by
    intro θ
    congr 1
    simp only [X, smul_smul, ← Complex.coe_smul]
    congr 1
    ring
  have hXnorm : ‖X‖ = ‖A‖ := by
    simp only [X, norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hderiv : ∀ θ : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • X))
      (NormedSpace.exp (θ • X) * X) θ := fun θ => hasDerivAt_exp_smul_const (𝕂 := ℝ) X θ
  have hbound : ∀ θ : ℝ, ‖NormedSpace.exp (θ • X) * X‖ ≤ ‖A‖ := by
    intro θ
    calc ‖NormedSpace.exp (θ • X) * X‖ ≤ ‖NormedSpace.exp (θ • X)‖ * ‖X‖ := norm_mul_le _ _
      _ ≤ 1 * ‖A‖ := by
        rw [hXnorm]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [← hf]
        exact exp_skew_norm_le A hA θ
      _ = ‖A‖ := one_mul _
  rw [hf, hf]
  rcases le_total b a with hba | hab
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ =>
      NormedSpace.exp (u • X)) (a := b) (b := a)
      (fun θ _ => (hderiv θ).hasDerivWithinAt) (fun θ _ => hbound θ) a ⟨hba, le_rfl⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    linarith
  · have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ =>
      NormedSpace.exp (u • X)) (a := a) (b := b)
      (fun θ _ => (hderiv θ).hasDerivWithinAt) (fun θ _ => hbound θ) b ⟨hab, le_rfl⟩
    rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith

/-- The refined product is the mesh product with block lengths `n_r T / N`. -/
theorem refined_evolution_eq (A : ℕ → P →L[ℂ] P) (h : IsMesh t M T) (hT : 0 < T) :
    refinedEvolution A t T N M = evolution (fun r => NormedSpace.exp
      ((-Complex.I * (((blockLength t T N r : ℕ) * (T / N) : ℝ) : ℂ)) • A r)) M := by
  unfold refinedEvolution
  set F : ℕ → P →L[ℂ] P := fun k => NormedSpace.exp ((-Complex.I * ((T / N : ℝ) : ℂ)) •
    A (slotPiece t T N M k)) with hF
  have hlast := blockStart_last (N := N) h hT
  calc evolution F N = evolution F (blockStart t T N M) := by rw [hlast]
    _ = evolution (fun r => TimeDependent.orderedProduct F (blockStart t T N r)
          (blockStart t T N (r + 1) - blockStart t T N r)) M :=
        evolution_blocks F (blockStart t T N) (blockStart_zero h) (blockStart_mono h hT) M
    _ = _ := by
      apply evolution_congr'
      intro r hr
      have hmono := blockStart_mono (N := N) h hT (Nat.le_succ r)
      rw [orderedProduct_congr_const F (NormedSpace.exp ((-Complex.I * ((T / N : ℝ) : ℂ)) •
        A r)), exp_pow]
      · rfl
      · intro j hj
        simp only [hF]
        rw [slotPiece_eq h hT hr (by omega) (by omega)]

/-- **Refinement error**: the refined product of slot exponentials is within
`M (T / N) Λ` of the mesh product, for self-adjoint samples with `‖A_r‖ ≤ Λ`. -/
theorem refined_evolution_sub_le (A : ℕ → P →L[ℂ] P) (hA : ∀ r, star (A r) = A r) {Λ : ℝ}
    (hΛ : ∀ r, ‖A r‖ ≤ Λ) (h : IsMesh t M T) (hT : 0 < T) (hN : 0 < N) :
    ‖refinedEvolution A t T N M - meshEvolution A t M‖ ≤ M * (T / N) * Λ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  rw [refined_evolution_eq A h hT, meshEvolution]
  have hstep : ∀ r, ‖NormedSpace.exp ((-Complex.I * (((blockLength t T N r : ℕ) *
      (T / N) : ℝ) : ℂ)) • A r) - NormedSpace.exp ((-Complex.I *
        ((t (r + 1) - t r : ℝ) : ℂ)) • A r)‖ ≤ T / N * Λ := by
    intro r
    refine (exp_sub_exp_norm_le (A r) (hA r) _ _).trans ?_
    exact mul_le_mul (blockLength_sub_lt h hT hN r).le (hΛ r) (norm_nonneg _)
      (div_pos hT hNR).le
  have h1 := evolution_sub_norm_le_mul _ _ (fun r => exp_skew_norm_le (A r) (hA r) _)
    (fun r => exp_skew_norm_le (A r) (hA r) _) hstep M
  calc _ ≤ (M : ℝ) * (T / N * Λ) := h1
    _ = M * (T / N) * Λ := by ring

end Refined

end

end TimeDependentExtensions
