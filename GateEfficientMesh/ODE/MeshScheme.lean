import GateEfficientMesh.ODE.Target

/-!
# The slot scheme of a nonuniform mesh against the mesh scheme

Theorem `ode:thm:gates`, time-dependent part, extended by uniform refinement to nonuniform
meshes with breakpoints. A mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` with represented samples `G̃_q`, `b̃_q`
per interval is refined into `N` uniform slots of length `h = T/N`; slot `k` reads the samples
of the interval `σ k = slotPiece k` containing `k T / N`. The uniform slot scheme is the
released recurrence `y_{k+1} = exp(-h G̃_{σ k})(y_k + h b̃_{σ k})` (forcing samples per slot
from the containing interval), and the mesh scheme is `z_{q+1} = exp(-Δ_q G̃_q)(z_q + Δ_q b̃_q)`
(`TimeDependentExtensions.ODEMesh.meshRecurrence`). Interval `q` holds the `n_q` slots
`blockStart q ≤ k < blockStart (q + 1)`, with `|n_q h - Δ_q| < h`.

* `sum_mask`, `maskedPropagator_sub_le`: moving the start of a masked propagator by `j` slots
  changes it by at most `j h Λ`;
* `sum_blocks`: a sum over the slots splits into the blocks of the intervals;
* `mask_blockStart`, `maskedPropagator_blockStart`: the masked propagator from the first slot of
  interval `q` is the released refined propagator
  `TimeDependentExtensions.ODEMesh.refinedPropagator`;
* `block_error`: one block of forcing terms against the mesh forcing term;
* `slot_mesh_recurrence`: the slot scheme is within
  `M h Λ ‖y₀‖ + ∑_q (Λ (n_q h)²/2 + |n_q h - Δ_q| + Δ_q M h Λ) ‖b̃_q‖` of the mesh scheme, for
  accretive samples of norm at most `Λ` (with the released
  `TimeDependentExtensions.ODEMesh.refinedPropagator_sub_le`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap Set
open TimeDependentODE (mask mask_nonneg mask_of_le mask_of_lt maskedPropagator recurrence
  Accretive accretive_exp_sub_norm_le accretive_exp_norm_le_one maskedPropagator_norm_le_one)
open TimeDependentExtensions (IsMesh slotPiece slotPiece_lt blockStart blockLength)
open TimeDependentExtensions.ODEMesh (meshRecurrence meshPropagator refinedPropagator)
open scoped BigOperators

/-! ### Masks and blocks -/

/-- `∑_{r < N} [q ≤ r] = N - min (q, N)`. -/
theorem sum_mask (q N : ℕ) : ∑ r ∈ Finset.range N, mask q r = (N : ℝ) - (min q N : ℕ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hq : q ≤ N
    · rw [mask_of_le hq, min_eq_left hq, min_eq_left (by omega)]
      push_cast
      ring
    · rw [mask_of_lt (by omega), min_eq_right (by omega), min_eq_right (by omega)]
      push_cast
      ring

/-- A sum over the slots `k < kb M` splits into the blocks `kb q ≤ k < kb (q + 1)`. -/
theorem sum_blocks {E : Type*} [AddCommMonoid E] (f : ℕ → E) (kb : ℕ → ℕ) (hkb0 : kb 0 = 0)
    (hmono : Monotone kb) (M : ℕ) :
    ∑ k ∈ Finset.range (kb M), f k =
      ∑ q ∈ Finset.range M, ∑ j ∈ Finset.range (kb (q + 1) - kb q), f (kb q + j) := by
  induction M with
  | zero => rw [hkb0]; simp
  | succ M ih =>
    have hle : kb M ≤ kb (M + 1) := hmono (Nat.le_succ M)
    have hsplit : kb (M + 1) = kb M + (kb (M + 1) - kb M) := by omega
    rw [Finset.sum_range_succ, ← ih, hsplit, Finset.sum_range_add, ← hsplit]

/-- `∑_{j < n} j ≤ n² / 2`. -/
theorem sum_range_le_sq (n : ℕ) : ∑ j ∈ Finset.range n, (j : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith

variable {t : ℕ → ℝ} {M N : ℕ} {T : ℝ}

/-- For an interval `q < M`, a slot lies at or after the first slot of interval `q` exactly
when its interval is at least `q`. -/
theorem mask_blockStart (hmesh : IsMesh t M T) (hT : 0 < T) {q : ℕ} (hq : q < M) (k : ℕ) :
    mask (blockStart t T N q) k = mask q (slotPiece t T N M k) := by
  have hspec : blockStart t T N (slotPiece t T N M k) ≤ k := by
    unfold slotPiece
    exact Nat.findGreatest_spec (P := fun r => blockStart t T N r ≤ k) (m := 0)
      (Nat.zero_le _) (by rw [TimeDependentExtensions.blockStart_zero hmesh]; exact Nat.zero_le k)
  by_cases hk : blockStart t T N q ≤ k
  · have hge : q ≤ slotPiece t T N M k := by
      unfold slotPiece
      exact Nat.le_findGreatest (by omega) hk
    rw [mask_of_le hk, mask_of_le hge]
  · have hlt : slotPiece t T N M k < q := by
      by_contra hc
      have hmono := TimeDependentExtensions.blockStart_mono (N := N) hmesh hT (not_lt.mp hc)
      exact hk (hmono.trans hspec)
    rw [mask_of_lt (not_le.mp hk), mask_of_lt hlt]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- The masked propagator of the slot generators from the first slot of interval `q` is the
released refined propagator of the interval. -/
theorem maskedPropagator_blockStart (Gm : ℕ → V →L[ℂ] V) (hmesh : IsMesh t M T) (hT : 0 < T)
    {q : ℕ} (hq : q < M) :
    maskedPropagator (fun k => Gm (slotPiece t T N M k)) (T / N) (blockStart t T N q) N =
      refinedPropagator Gm t T N M q := by
  unfold maskedPropagator refinedPropagator
  congr 1
  funext k
  rw [mask_blockStart hmesh hT hq k]

/-- **Moving the start of a masked propagator** by `k - k'` slots changes it by at most
`(k - k') h Λ`, for accretive generators of norm at most `Λ`. -/
theorem maskedPropagator_sub_le (Gs : ℕ → V →L[ℂ] V) (hGs : ∀ r, Accretive (Gs r)) {Λ : ℝ}
    (hΛ : ∀ r, ‖Gs r‖ ≤ Λ) {h : ℝ} (hh : 0 ≤ h) {k k' : ℕ} (hkk : k' ≤ k) (n : ℕ) :
    ‖maskedPropagator Gs h k n - maskedPropagator Gs h k' n‖ ≤ ((k : ℝ) - k') * h * Λ := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  unfold maskedPropagator
  have h1 := SparseHamiltonian.TimeDependent.evolution_sub_norm_le _ _
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _ (mul_nonneg hh (mask_nonneg k r)))
    (fun r => accretive_exp_norm_le_one (Gs r) (hGs r) _ (mul_nonneg hh (mask_nonneg k' r))) n
  refine h1.trans ?_
  have hterm : ∀ r, ‖NormedSpace.exp ((h * mask k r) • (-Gs r)) -
      NormedSpace.exp ((h * mask k' r) • (-Gs r))‖ ≤ (mask k' r - mask k r) * (h * Λ) := by
    intro r
    refine (accretive_exp_sub_norm_le (Gs r) (hGs r) _ _ (mul_nonneg hh (mask_nonneg _ _))
      (mul_nonneg hh (mask_nonneg _ _))).trans ?_
    have hm : mask k r ≤ mask k' r := by
      by_cases h1 : k ≤ r
      · rw [mask_of_le h1, mask_of_le (hkk.trans h1)]
      · rw [mask_of_lt (not_le.mp h1)]
        exact mask_nonneg _ _
    have e : |h * mask k r - h * mask k' r| = (mask k' r - mask k r) * h := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hh, abs_of_nonpos (by linarith)]
      ring
    rw [e]
    have : 0 ≤ (mask k' r - mask k r) * h := mul_nonneg (by linarith) hh
    calc (mask k' r - mask k r) * h * ‖Gs r‖ ≤ (mask k' r - mask k r) * h * Λ :=
          mul_le_mul_of_nonneg_left (hΛ r) this
      _ = (mask k' r - mask k r) * (h * Λ) := by ring
  refine (Finset.sum_le_sum fun r _ => hterm r).trans ?_
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, sum_mask, sum_mask]
  have hmin : ((min k n : ℕ) : ℝ) - (min k' n : ℕ) ≤ (k : ℝ) - k' := by
    have : min k n - min k' n ≤ k - k' := by omega
    have h2 : min k' n ≤ min k n := by omega
    have h3 : ((min k n - min k' n : ℕ) : ℝ) ≤ ((k - k' : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub h2, Nat.cast_sub hkk] at h3
    exact h3
  have hhΛ : 0 ≤ h * Λ := mul_nonneg hh hΛ0
  calc ((n : ℝ) - (min k' n : ℕ) - ((n : ℝ) - (min k n : ℕ))) * (h * Λ) =
        (((min k n : ℕ) : ℝ) - (min k' n : ℕ)) * (h * Λ) := by ring
    _ ≤ ((k : ℝ) - k') * (h * Λ) := mul_le_mul_of_nonneg_right hmin hhΛ
    _ = ((k : ℝ) - k') * h * Λ := by ring

/-! ### One block -/

omit [CompleteSpace V] in
/-- **One block of forcing terms against the mesh forcing term.** If the propagators `P (s + j)`
from the slots of a block of `n` slots move by at most `j h Λ` from `P s`, `P s` is a
contraction within `e` of the mesh propagator `Pm`, then the block of slot forcing terms
`∑_{j<n} P (s + j) (h b)` is within `(Λ (n h)² / 2 + |n h - Δ| + Δ e) ‖b‖` of `Pm (Δ b)`. -/
theorem block_error (P : ℕ → V →L[ℂ] V) (Pm : V →L[ℂ] V) (s n : ℕ) {h Δ Λ e : ℝ} (hh : 0 ≤ h)
    (hΔ : 0 ≤ Δ) (hΛ : 0 ≤ Λ) (hP : ∀ j, ‖P (s + j) - P s‖ ≤ (j : ℝ) * h * Λ)
    (hP1 : ‖P s‖ ≤ 1) (hPm : ‖P s - Pm‖ ≤ e) (b : V) :
    ‖(∑ j ∈ Finset.range n, P (s + j) (h • b)) - Pm (Δ • b)‖ ≤
      (Λ * ((n : ℝ) * h) ^ 2 / 2 + |(n : ℝ) * h - Δ| + Δ * e) * ‖b‖ := by
  have hPs : ∀ c : ℝ, P s (c • b) = c • P s b := fun c => (P s).map_smul_of_tower c b
  have hPm' : ∀ c : ℝ, Pm (c • b) = c • Pm b := fun c => Pm.map_smul_of_tower c b
  have e0 : ∑ _j ∈ Finset.range n, P s (h • b) = ((n : ℝ) * h) • P s b := by
    rw [Finset.sum_const, Finset.card_range, hPs, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have e1 : ∑ j ∈ Finset.range n, P (s + j) (h • b) =
      ∑ j ∈ Finset.range n, (P (s + j) - P s) (h • b) + ((n : ℝ) * h) • P s b := by
    rw [← e0, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sub_apply, sub_add_cancel]
  have hsplit : (∑ j ∈ Finset.range n, P (s + j) (h • b)) - Pm (Δ • b) =
      (∑ j ∈ Finset.range n, (P (s + j) - P s) (h • b)) + (((n : ℝ) * h - Δ) • P s b) +
        Δ • ((P s - Pm) b) := by
    rw [e1, hPm', sub_apply]
    simp only [sub_smul, smul_sub]
    abel
  rw [hsplit]
  have h1 : ‖∑ j ∈ Finset.range n, (P (s + j) - P s) (h • b)‖ ≤
      Λ * ((n : ℝ) * h) ^ 2 / 2 * ‖b‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j ∈ Finset.range n, ‖(P (s + j) - P s) (h • b)‖ ≤
          ∑ j ∈ Finset.range n, (j : ℝ) * (h * h * Λ * ‖b‖) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (le_opNorm _ _).trans ?_
          rw [norm_smul, Real.norm_of_nonneg hh]
          calc ‖P (s + j) - P s‖ * (h * ‖b‖) ≤ (j : ℝ) * h * Λ * (h * ‖b‖) :=
                mul_le_mul_of_nonneg_right (hP j) (by positivity)
            _ = (j : ℝ) * (h * h * Λ * ‖b‖) := by ring
      _ = (∑ j ∈ Finset.range n, (j : ℝ)) * (h * h * Λ * ‖b‖) := by rw [Finset.sum_mul]
      _ ≤ (n : ℝ) ^ 2 / 2 * (h * h * Λ * ‖b‖) :=
          mul_le_mul_of_nonneg_right (sum_range_le_sq n) (by positivity)
      _ = Λ * ((n : ℝ) * h) ^ 2 / 2 * ‖b‖ := by ring
  have h2 : ‖((n : ℝ) * h - Δ) • P s b‖ ≤ |(n : ℝ) * h - Δ| * ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((le_opNorm _ _).trans
      (by simpa using mul_le_mul_of_nonneg_right hP1 (norm_nonneg b))) (abs_nonneg _)
  have h3 : ‖Δ • ((P s - Pm) b)‖ ≤ Δ * e * ‖b‖ := by
    rw [norm_smul, Real.norm_of_nonneg hΔ, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hPm (norm_nonneg b))) hΔ
  calc _ ≤ ‖∑ j ∈ Finset.range n, (P (s + j) - P s) (h • b)‖ +
        ‖((n : ℝ) * h - Δ) • P s b‖ + ‖Δ • ((P s - Pm) b)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith [h1, h2, h3]

/-! ### The slot scheme against the mesh scheme -/

/-- **The slot scheme against the mesh scheme.** For accretive mesh samples `G̃_q` of norm at
most `Λ`, forcing samples `b̃_q` and slots reading the samples of their intervals, the released
slot recurrence with step `h = T/N` is within
`M h Λ ‖y₀‖ + ∑_q (Λ (n_q h)²/2 + |n_q h - Δ_q| + Δ_q M h Λ) ‖b̃_q‖` of the mesh recurrence. -/
theorem slot_mesh_recurrence (Gm : ℕ → V →L[ℂ] V) (bm : ℕ → V) (hGm : ∀ r, Accretive (Gm r))
    {Λ : ℝ} (hΛ : ∀ r, ‖Gm r‖ ≤ Λ) (hmesh : IsMesh t M T) (hT : 0 < T) (hN : 0 < N)
    (hM : 0 < M) (y0 : V) :
    ‖recurrence (fun k => Gm (slotPiece t T N M k)) (fun k => bm (slotPiece t T N M k)) (T / N)
        y0 N - meshRecurrence Gm bm (fun r => t (r + 1) - t r) y0 M‖ ≤
      M * (T / N) * Λ * ‖y0‖ + ∑ q ∈ Finset.range M,
        (Λ * ((blockLength t T N q : ℝ) * (T / N)) ^ 2 / 2 +
          |(blockLength t T N q : ℝ) * (T / N) - (t (q + 1) - t q)| +
          (t (q + 1) - t q) * (M * (T / N) * Λ)) * ‖bm q‖ := by
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans (hΛ 0)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 ≤ T / N := (div_pos hT hNR).le
  set Gs : ℕ → V →L[ℂ] V := fun k => Gm (slotPiece t T N M k) with hGsdef
  have hGs : ∀ r, Accretive (Gs r) := fun r => hGm _
  have hΛs : ∀ r, ‖Gs r‖ ≤ Λ := fun r => hΛ _
  set P : ℕ → V →L[ℂ] V := fun k => maskedPropagator Gs (T / N) k N with hPdef
  set Pm : ℕ → V →L[ℂ] V := fun q => meshPropagator Gm (fun r => t (r + 1) - t r) q M
    with hPmdef
  have hround : ∀ q < M, ‖P (blockStart t T N q) - Pm q‖ ≤ M * (T / N) * Λ := by
    intro q hq
    simp only [hPdef, hPmdef, hGsdef]
    rw [maskedPropagator_blockStart Gm hmesh hT hq]
    exact TimeDependentExtensions.ODEMesh.refinedPropagator_sub_le Gm hGm hΛ hmesh hT hN q
  rw [TimeDependentODE.recurrence_eq_sum, TimeDependentExtensions.ODEMesh.meshRecurrence_eq_sum]
  -- the forcing sum over the blocks of the intervals
  have hlast := TimeDependentExtensions.blockStart_last (N := N) hmesh hT
  have hblocks : ∑ k ∈ Finset.range N, maskedPropagator Gs (T / N) k N
      ((T / N) • bm (slotPiece t T N M k)) =
      ∑ q ∈ Finset.range M, ∑ j ∈ Finset.range (blockLength t T N q),
        P (blockStart t T N q + j) ((T / N) • bm q) := by
    have hrange : Finset.range N = Finset.range (blockStart t T N M) := by rw [hlast]
    rw [hrange, sum_blocks _ (blockStart t T N) (TimeDependentExtensions.blockStart_zero hmesh)
      (TimeDependentExtensions.blockStart_mono hmesh hT) M]
    refine Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun j hj => ?_
    have hqM := Finset.mem_range.mp hq
    have hjn := Finset.mem_range.mp hj
    have hmono := TimeDependentExtensions.blockStart_mono (N := N) hmesh hT
      (show q ≤ q + 1 by omega)
    unfold blockLength at hjn
    rw [TimeDependentExtensions.slotPiece_eq hmesh hT hqM (by omega) (by omega)]
  rw [hblocks]
  have h0 : maskedPropagator Gs (T / N) 0 N = P (blockStart t T N 0) := by
    simp only [hPdef, TimeDependentExtensions.blockStart_zero hmesh]
  rw [h0]
  have hsplit : (P (blockStart t T N 0) y0 + ∑ q ∈ Finset.range M, ∑ j ∈
      Finset.range (blockLength t T N q), P (blockStart t T N q + j) ((T / N) • bm q)) -
      (meshPropagator Gm (fun r => t (r + 1) - t r) 0 M y0 + ∑ q ∈ Finset.range M,
        meshPropagator Gm (fun r => t (r + 1) - t r) q M ((t (q + 1) - t q) • bm q)) =
      (P (blockStart t T N 0) - Pm 0) y0 + ∑ q ∈ Finset.range M,
        ((∑ j ∈ Finset.range (blockLength t T N q),
          P (blockStart t T N q + j) ((T / N) • bm q)) - Pm q ((t (q + 1) - t q) • bm q)) := by
    rw [Finset.sum_sub_distrib, sub_apply]
    simp only [hPmdef]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (le_opNorm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hround 0 hM) (norm_nonneg _)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
    have hqM := Finset.mem_range.mp hq
    refine block_error P (Pm q) (blockStart t T N q) (blockLength t T N q) hh
      (hmesh.length_nonneg q) hΛ0 (fun j => ?_) ?_ (hround q hqM) (bm q)
    · simpa using maskedPropagator_sub_le Gs hGs hΛs hh (Nat.le_add_right (blockStart t T N q) j) N
    · exact maskedPropagator_norm_le_one Gs hGs (T / N) hh _ N

end

end SparseHamiltonian.GateMesh.ODE
