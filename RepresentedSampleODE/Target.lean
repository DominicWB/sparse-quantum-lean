import RepresentedSampleODE.Family

/-!
# The repaired target and its certified distance from the propagated source sum

The repaired target propagates every source branch by the repaired family of its label at `-i`
(the slot product of the repaired generators `repair D̃_r κ_r + i H̃_r`). The repaired generators
are accretive whatever the sign of the represented dissipative parts, so the mesh comparison of
`GeneralSourceExtensions.Mesh` applies to them; they differ from the represented samples by at most
`2 κ_r`, which adds `2 Λ_κ` to the sample certificate, and their norms are at most `2 s Λ`, which
doubles the refinement term.

* `robustTarget_norm_le`: the target norm is at most the source mass;
* `robust_branch_error`: one source branch, `(ΔG + 2 Λ_κ + 2 ΔR) ‖w‖`;
* `robust_target_error`: the target against the propagated source sum,
  `(ΔG + 2 Λ_κ + 2 ΔR) B_q`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshWidth meshDurations meshWidth_nonneg
  meshDurations_nonneg tableFamily refinementError sampleError IsMeshPropagator meshNodeProduct
  node_error_nat refined_sub_le_of_nonneg)
open SparseHamiltonian.GeneralSourceODE (startTime sources mass_sources)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- `∫_a^b ‖f - c'‖ ≤ ∫_a^b ‖f - c‖ + (b - a) ‖c - c'‖`. -/
theorem integral_norm_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) (c c' : E) :
    ∫ u in a..b, ‖f u - c'‖ ≤ (∫ u in a..b, ‖f u - c‖) + (b - a) * ‖c - c'‖ := by
  have h1 : IntervalIntegrable (fun u => ‖f u - c'‖) volume a b :=
    (hf.sub intervalIntegrable_const).norm
  have h2 : IntervalIntegrable (fun u => ‖f u - c‖) volume a b :=
    (hf.sub intervalIntegrable_const).norm
  have hmono : ∫ u in a..b, ‖f u - c'‖ ≤ ∫ u in a..b, (‖f u - c‖ + ‖c - c'‖) :=
    intervalIntegral.integral_mono_on hab h1 (h2.add intervalIntegrable_const)
      (fun u _ => by
        calc ‖f u - c'‖ = ‖(f u - c) + (c - c')‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖f u - c‖ + ‖c - c'‖ := norm_add_le _ _)
  rw [intervalIntegral.integral_add h2 intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  exact hmono

/-- The repaired target: every source branch propagated by the repaired family of its label at
`-i`. -/
def robustTarget (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (T : ℝ) (N : ℕ) {m : ℕ}
    (v : Fin m → ℝ) (x : X) (κ : Fin M → ℝ) (x₀ : EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (ω : Fin m → ℂ) : EuclideanSpace ℂ n :=
  ∑ a, robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a (-Complex.I)
    (sources x₀ bv ω a)

/-- The target norm is at most the source mass. -/
theorem robustTarget_norm_le (D : Data (X × Fin M) n Z s) (hM : 0 < M) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (hT : 0 ≤ T) (N : ℕ) {m : ℕ} (v : Fin m → ℝ) (x : X)
    (κ : Fin M → ℝ) (hκ : ∀ r, 0 ≤ κ r)
    (hneg : ∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re)
    (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n) (ω : Fin m → ℂ) :
    ‖robustTarget D hM t T N v x κ x₀ bv ω‖ ≤ ODESourceBranches.mass (sources x₀ bv ω) := by
  unfold robustTarget ODESourceBranches.mass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  calc
    _ ≤ ‖robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a (-Complex.I)‖ *
        ‖sources x₀ bv ω a‖ := le_opNorm _ _
    _ ≤ 1 * ‖sources x₀ bv ω a‖ := mul_le_mul_of_nonneg_right
        (robustFamily_norm_le_one D _ N _ (meshDurations_nonneg hmesh hT v) x κ hκ hneg a _
          (by simp)) (norm_nonneg _)
    _ = ‖sources x₀ bv ω a‖ := one_mul _

set_option maxHeartbeats 4000000 in
/-- **One source branch.** The propagation of `w` from the start time of a label against the
slot product of the repaired generators: at most `(ΔG + 2 Λ_κ + 2 ΔR) ‖w‖`. -/
theorem robust_branch_error (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (κ : Fin M → ℝ)
    (hκ : ∀ r, 0 ≤ κ r)
    (hneg : ∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re)
    {t : ℕ → ℝ} {T : ℝ} {N : ℕ} (hmesh : IsMesh t M T) (hT : 0 ≤ T) (hN : 0 < N)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (hU : IsMeshPropagator G t T U)
    {m : ℕ} (v : Fin m → ℝ) (a : Option (Fin m)) (ha : startTime v a ∈ Icc 0 T)
    (w : EuclideanSpace ℂ n) :
    ‖U (startTime v a) w T -
        robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a (-Complex.I) w‖ ≤
      (sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N) * ‖w‖ := by
  classical
  set idx : ℕ → Fin M := TimeDependent.Sampled.sampleIndex hM with hidx
  have hidxlt : ∀ r (hr : r < M), idx r = ⟨r, hr⟩ := fun r hr =>
    Fin.ext (Nat.mod_eq_of_lt hr)
  let Gs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    repairedGenerator D (fun _ => idx r) x κ 0
  let Gt : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    SparseStateOverlap.matrixOperator (D.matrix (x, idx r))
  let Gq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r => G (idx r)
  set Λ : ℝ := (s : ℝ) * D.scale with hΛdef
  have hGs : ∀ r, Accretive (Gs r) := fun r =>
    repairedGenerator_accretive D (fun _ => idx r) x κ hκ hneg 0
  have hGsn : ∀ r, ‖Gs r‖ ≤ 2 * Λ := fun r =>
    repairedGenerator_norm_le D (fun _ => idx r) x κ hκ 0
  have hGst : ∀ r, ‖Gt r - Gs r‖ ≤ 2 * κ (idx r) := fun r => by
    rw [norm_sub_rev]
    exact (repairedGenerator_sub_le D (fun _ => idx r) x κ hκ 0).trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num))
  have hGq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (Gq r u) := by
    intro r hr u hu
    change Accretive (G (idx r) u)
    rw [hidxlt r hr]
    exact hG ⟨r, hr⟩ u hu
  have hGqint : ∀ r < M, IntervalIntegrable (Gq r) volume (t r) (t (r + 1)) := by
    intro r hr
    change IntervalIntegrable (G (idx r)) volume (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hGint ⟨r, hr⟩
  obtain ⟨h0, hsol⟩ := hU (startTime v a) ha w
  have hsolq : ∀ r < M, startTime v a ≤ t (r + 1) →
      SolvesODE (Gq r) 0 (U (startTime v a) w) (max (startTime v a) (t r)) (t (r + 1)) := by
    intro r hr hst
    change SolvesODE (G (idx r)) 0 (U (startTime v a) w) (max (startTime v a) (t r)) (t (r + 1))
    rw [hidxlt r hr]
    exact hsol ⟨r, hr⟩ hst
  -- The mesh product of the repaired generators against the propagator.
  have hNode := node_error_nat hmesh Gq hGq hGqint Gs hGs ha (U (startTime v a) w) hsolq
  rw [h0] at hNode
  have hSum : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖ ≤
      sampleError D x t G + 2 * negativity t κ := by
    have hpiece : ∀ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖ ≤
        (∫ u in t r..t (r + 1), ‖Gq r u - Gt r‖) + 2 * ((t (r + 1) - t r) * κ (idx r)) := by
      intro r hr
      have hr' := Finset.mem_range.mp hr
      refine (integral_norm_sub_le (hmesh.mono (Nat.le_succ r)) (hGqint r hr') (Gt r)
        (Gs r)).trans ?_
      have := mul_le_mul_of_nonneg_left (hGst r) (hmesh.length_nonneg r)
      linarith
    refine (Finset.sum_le_sum hpiece).trans (le_of_eq ?_)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Gq r u - Gt r‖) M]
      unfold sampleError
      apply Finset.sum_congr rfl
      intro r _
      simp only [Gq, Gt, hidxlt r r.isLt]
    · congr 1
      rw [← Fin.sum_univ_eq_sum_range (fun r => (t (r + 1) - t r) * κ (idx r)) M]
      unfold negativity
      apply Finset.sum_congr rfl
      intro r _
      simp only [hidxlt r r.isLt]
  have hNode' : ‖U (startTime v a) w T - meshNodeProduct Gs t M (startTime v a) w‖ ≤
      ‖w‖ * (sampleError D x t G + 2 * negativity t κ) :=
    hNode.trans (mul_le_mul_of_nonneg_left hSum (norm_nonneg w))
  -- The slot product against the mesh product.
  have hSlot : robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a (-Complex.I) =
      TimeDependent.evolution (fun k => NormedSpace.exp
        ((T * meshWidth (startTime v a) t (slotPiece t T N M k) /
            (t (slotPiece t T N M k + 1) - t (slotPiece t T N M k)) / N) •
          (-Gs (slotPiece t T N M k)))) N := by
    rw [robustFamily_neg_I]
    congr 1
    funext k
    have hk : idx (slotPiece t T N M k) = pieceOf t T N hM k :=
      Fin.ext (Nat.mod_eq_of_lt (slotPiece_lt hM k))
    simp only [repairedGenerator, repairedDissipative, MeshSampling.hamiltonian,
      MeshSampling.dissipative, MeshSampling.generator, Gs, hk]
    rfl
  have hRef := refined_sub_le_of_nonneg hmesh hT hN Gs hGs hGsn v a
  rw [← hSlot] at hRef
  have hRef' : ‖meshNodeProduct Gs t M (startTime v a) w -
      robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a (-Complex.I) w‖ ≤
        2 * refinementError D t T N * ‖w‖ := by
    rw [← sub_apply]
    refine (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [norm_sub_rev]
    refine hRef.trans (le_of_eq ?_)
    unfold refinementError
    ring
  calc _ ≤ ‖U (startTime v a) w T - meshNodeProduct Gs t M (startTime v a) w‖ +
        ‖meshNodeProduct Gs t M (startTime v a) w -
          robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a (-Complex.I) w‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖w‖ * (sampleError D x t G + 2 * negativity t κ) +
        2 * refinementError D t T N * ‖w‖ := add_le_add hNode' hRef'
    _ = (sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N) * ‖w‖ := by
        ring

set_option maxHeartbeats 2000000 in
/-- **The certified distance of the repaired target from the propagated source sum.** -/
theorem robust_target_error (D : Data (X × Fin M) n Z s) (hM : 0 < M) (x : X) (κ : Fin M → ℝ)
    (hκ : ∀ r, 0 ≤ κ r)
    (hneg : ∀ (r : Fin M) (w : EuclideanSpace ℂ n),
      -κ r * ‖w‖ ^ 2 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re)
    {t : ℕ → ℝ} {T : ℝ} {N : ℕ} (hmesh : IsMesh t M T) (hT : 0 ≤ T) (hN : 0 < N)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (hU : IsMeshPropagator G t T U)
    {m : ℕ} (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (x₀ : EuclideanSpace ℂ n) (bv : Fin m → EuclideanSpace ℂ n) :
    ‖(U 0 x₀ T + ∑ i, ω i • U (v i) (bv i) T) - robustTarget D hM t T N v x κ x₀ bv ω‖ ≤
      (sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N) *
        ODESourceBranches.mass (sources x₀ bv ω) := by
  set K := sampleError D x t G + 2 * negativity t κ + 2 * refinementError D t T N with hK
  set F := fun a => robustFamily D (pieceOf t T N hM) N (meshDurations t T v) x κ a
    (-Complex.I) with hF
  have hInit : ‖U 0 x₀ T - F none x₀‖ ≤ K * ‖x₀‖ :=
    robust_branch_error D hM x κ hκ hneg hmesh hT hN G hG hGint U hU v none ⟨le_rfl, hT⟩ x₀
  have hNode : ∀ i, ‖ω i • U (v i) (bv i) T - F (some i) (ω i • bv i)‖ ≤
      K * (‖ω i‖ * ‖bv i‖) := by
    intro i
    have h := robust_branch_error D hM x κ hκ hneg hmesh hT hN G hG hGint U hU v (some i) (hv i)
      (bv i)
    have hsplit : ω i • U (v i) (bv i) T - F (some i) (ω i • bv i) =
        ω i • (U (v i) (bv i) T - F (some i) (bv i)) := by
      rw [map_smul, smul_sub]
    rw [hsplit, norm_smul]
    calc ‖ω i‖ * ‖U (v i) (bv i) T - F (some i) (bv i)‖ ≤ ‖ω i‖ * (K * ‖bv i‖) :=
          mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = K * (‖ω i‖ * ‖bv i‖) := by ring
  have hTarget : robustTarget D hM t T N v x κ x₀ bv ω =
      F none x₀ + ∑ i, F (some i) (ω i • bv i) := by
    unfold robustTarget
    rw [Fintype.sum_option]
    rfl
  have hsplit : (U 0 x₀ T + ∑ i, ω i • U (v i) (bv i) T) - robustTarget D hM t T N v x κ x₀ bv ω =
      (U 0 x₀ T - F none x₀) + ∑ i, (ω i • U (v i) (bv i) T - F (some i) (ω i • bv i)) := by
    rw [hTarget, Finset.sum_sub_distrib]
    abel
  rw [hsplit, mass_sources]
  calc
    _ ≤ ‖U 0 x₀ T - F none x₀‖ +
        ∑ i, ‖ω i • U (v i) (bv i) T - F (some i) (ω i • bv i)‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ K * ‖x₀‖ + ∑ i, K * (‖ω i‖ * ‖bv i‖) :=
      add_le_add hInit (Finset.sum_le_sum fun i _ => hNode i)
    _ = K * (‖x₀‖ + ∑ i, ‖ω i‖ * ‖bv i‖) := by
      rw [← Finset.mul_sum]
      ring

end

end SparseHamiltonian.RepresentedSampleODE
