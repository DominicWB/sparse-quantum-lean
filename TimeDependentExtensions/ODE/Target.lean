import TimeDependentExtensions.ODE.Sampling

set_option autoImplicit false

/-!
# The discretised target on a mesh and its certified distance from the solution

With slot `k` of the refinement into `N` slots reading the sample of its mesh interval
(`pieceOf`), the families of the source labels at `-i`, applied to the mesh sources, give the
discretised target `y = ∑_a F_a(-i) z_a` (`target`). It is within

  `(‖x(0)‖ + b_max T) ∑_r ∫ ‖G_r - G̃_r‖ + ∑_r ∫ ‖b_r - b̃_r‖
    + s Λ (∑_q Δ_q² ‖b̃_q‖ / 2 + M (T / N) ∑_a ‖z_a‖)`

of every solution of the piecewise problem (`target_error`), and has norm at most the source
mass (`target_norm_le`). The first two terms are the integrated sample-error certificates of
the generator and of the forcing, the third is the left-endpoint source quadrature on the mesh,
and the last is the refinement of the mesh into slots (`Λ = D.scale`).
-/

namespace TimeDependentExtensions

namespace MeshSampling

noncomputable section

open SparseHamiltonian ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open SparseHamiltonian.TimeDependentODE (mask mask_nonneg Accretive SolvesODE)
open SparseHamiltonian.TimeDependentODE.Sampling (start durations durationTable)
open TimeDependentExtensions.ODEMesh (meshRecurrence meshPropagator refinedPropagator
  meshRecurrence_eq_sum meshPropagator_norm_le_one refinedPropagator_sub_le mesh_error
  piecewise_norm_le)
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s M : ℕ}

/-- The discretised target: the families of the source labels at `-i` applied to the mesh
sources. -/
def target (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (T : ℝ) (N : ℕ) (x : X)
    (y0 : EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  ∑ a, family D (pieceOf t T N hM) N T x a (-Complex.I) (sources y0 t bs a)

theorem sampleIndex_of_lt (hM : 0 < M) {r : ℕ} (hr : r < M) :
    TimeDependent.Sampled.sampleIndex hM r = ⟨r, hr⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hr)

/-- The target norm is at most the source mass. -/
theorem target_norm_le (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (N : ℕ)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) (y0 : EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n) :
    ‖target D hM t T N x y0 bs‖ ≤ ODESourceBranches.mass (sources y0 t bs) := by
  unfold target ODESourceBranches.mass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  calc
    _ ≤ ‖family D (pieceOf t T N hM) N T x a (-Complex.I)‖ * ‖sources y0 t bs a‖ :=
      le_opNorm _ _
    _ ≤ 1 * ‖sources y0 t bs a‖ := mul_le_mul_of_nonneg_right
        (family_norm_le_one D _ N T hT hPSD x a _ (by simp)) (norm_nonneg _)
    _ = ‖sources y0 t bs a‖ := one_mul _

/-- At `-i`, the family of a source label is the refined masked propagator of the samples. -/
theorem family_neg_I_eq (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (T : ℝ)
    (N : ℕ) (x : X) (a : Option (Fin M)) :
    family D (pieceOf t T N hM) N T x a (-Complex.I) =
      refinedPropagator (fun r => SparseStateOverlap.matrixOperator
        (D.matrix (x, TimeDependent.Sampled.sampleIndex hM r))) t T N M (start a) := by
  rw [family_neg_I]
  unfold refinedPropagator
  congr 1
  funext k
  have hk : TimeDependent.Sampled.sampleIndex hM (slotPiece t T N M k) = pieceOf t T N hM k :=
    sampleIndex_of_lt hM (slotPiece_lt hM k)
  simp only [generator, hk]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The certified distance of the discretised target from the solution.** -/
theorem target_error (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (x : X) {t : ℕ → ℝ} {T : ℝ} {N : ℕ} (hmesh : IsMesh t M T) (hT : 0 < T) (hN : 0 < N)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bs : Fin M → EuclideanSpace ℂ n) (bmax : ℝ) (hbmax : 0 ≤ bmax)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (hbint : ∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1)))
    (hb : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax)
    (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) :
    ‖sol T - target D hM t T N x (sol 0) bs‖ ≤
      (‖sol 0‖ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        (s : ℝ) * D.scale * ((∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * ‖bs q‖) / 2 +
          M * (T / N) * ∑ a, ‖sources (sol 0) t bs a‖) := by
  classical
  set idx : ℕ → Fin M := TimeDependent.Sampled.sampleIndex hM with hidx
  have hidxv : ∀ r : Fin M, idx r = r := fun r => sampleIndex_of_lt hM r.isLt
  let Gs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    SparseStateOverlap.matrixOperator (D.matrix (x, idx r))
  let Gq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r => G (idx r)
  let bq : ℕ → ℝ → EuclideanSpace ℂ n := fun r => b (idx r)
  let bsq : ℕ → EuclideanSpace ℂ n := fun r => bs (idx r)
  let Δ : ℕ → ℝ := fun r => t (r + 1) - t r
  have hΔ : ∀ r, 0 ≤ Δ r := fun r => hmesh.length_nonneg r
  set Λ : ℝ := (s : ℝ) * D.scale with hΛdef
  have hΛ0 : 0 ≤ Λ := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  have hGs : ∀ r, Accretive (Gs r) := fun r => by
    have h := generator_accretive D (fun _ => idx r) hPSD x 0
    exact h
  have hGsn : ∀ r, ‖Gs r‖ ≤ Λ := fun r => by
    have h := generator_norm_le D (fun _ => idx r) x 0
    exact h
  -- Pieces in chronological indexing.
  have hidxlt : ∀ r (hr : r < M), idx r = ⟨r, hr⟩ := fun r hr => sampleIndex_of_lt hM hr
  have hsolq : ∀ r < M, SolvesODE (Gq r) (bq r) sol (t r) (t (r + 1)) := by
    intro r hr
    change SolvesODE (G (idx r)) (b (idx r)) sol (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hsol ⟨r, hr⟩
  have hGq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (Gq r u) := by
    intro r hr u hu
    change Accretive (G (idx r) u)
    rw [hidxlt r hr]
    exact hG ⟨r, hr⟩ u hu
  have hbq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), ‖bq r u‖ ≤ bmax := by
    intro r hr u hu
    change ‖b (idx r) u‖ ≤ bmax
    rw [hidxlt r hr]
    exact hb ⟨r, hr⟩ u hu
  have hGqint : ∀ r < M, IntervalIntegrable (Gq r) volume (t r) (t (r + 1)) := by
    intro r hr
    change IntervalIntegrable (G (idx r)) volume (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hGint ⟨r, hr⟩
  have hbqint : ∀ r < M, IntervalIntegrable (bq r) volume (t r) (t (r + 1)) := by
    intro r hr
    change IntervalIntegrable (b (idx r)) volume (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hbint ⟨r, hr⟩
  -- The scheme on the mesh against the solution.
  have hX := piecewise_norm_le hmesh hsolq hGq bmax hbmax hbq
  have hMesh := mesh_error hmesh hsolq hGqint hbqint Gs hGs bsq (‖sol 0‖ + bmax * T) hX
  -- The scheme as a sum over the source labels.
  have hRec : meshRecurrence Gs bsq Δ (sol 0) M =
      ∑ a, meshPropagator Gs Δ (start a) M (sources (sol 0) t bs a) := by
    rw [meshRecurrence_eq_sum, Fintype.sum_option]
    congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun q => meshPropagator Gs Δ q M (Δ q • bsq q)) M]
    apply Finset.sum_congr rfl
    intro q _
    simp only [start, sources, Δ, bsq, hidxv]
  have hTarget : target D hM t T N x (sol 0) bs =
      ∑ a, refinedPropagator Gs t T N M (start a) (sources (sol 0) t bs a) := by
    unfold target
    apply Finset.sum_congr rfl
    intro a _
    rw [family_neg_I_eq]
  -- The refinement into slots.
  have hRef : ‖meshRecurrence Gs bsq Δ (sol 0) M - target D hM t T N x (sol 0) bs‖ ≤
      M * (T / N) * Λ * ∑ a, ‖sources (sol 0) t bs a‖ := by
    rw [hRec, hTarget, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [← sub_apply]
    calc _ ≤ ‖meshPropagator Gs Δ (start a) M - refinedPropagator Gs t T N M (start a)‖ *
          ‖sources (sol 0) t bs a‖ := le_opNorm _ _
      _ ≤ M * (T / N) * Λ * ‖sources (sol 0) t bs a‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [norm_sub_rev]
        exact refinedPropagator_sub_le Gs hGs hGsn hmesh hT hN (start a)
  -- The certificate in the indexing of the statement.
  have hSum : ∑ r ∈ Finset.range M, ((‖sol 0‖ + bmax * T) *
        (∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖) + (∫ u in t r..t (r + 1), ‖bq r u - bsq r‖) +
          (t (r + 1) - t r) ^ 2 / 2 * (‖Gs r‖ * ‖bsq r‖)) ≤
      (‖sol 0‖ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        Λ * ((∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * ‖bs q‖) / 2) := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => ((‖sol 0‖ + bmax * T) *
        (∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖) + (∫ u in t r..t (r + 1), ‖bq r u - bsq r‖) +
          (t (r + 1) - t r) ^ 2 / 2 * (‖Gs r‖ * ‖bsq r‖))) M]
    simp only [Gq, bq, Gs, bsq, hidxv]
    calc _ ≤ ∑ r : Fin M, ((‖sol 0‖ + bmax * T) * (∫ u in t r..t ((r : ℕ) + 1),
            ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
          (∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
            Λ * ((t ((r : ℕ) + 1) - t r) ^ 2 * ‖bs r‖ / 2)) := by
          apply Finset.sum_le_sum
          intro r _
          refine add_le_add le_rfl ?_
          have h := hGsn r
          simp only [Gs, hidxv] at h
          calc (t ((r : ℕ) + 1) - t r) ^ 2 / 2 *
                (‖SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ * ‖bs r‖) ≤
              (t ((r : ℕ) + 1) - t r) ^ 2 / 2 * (Λ * ‖bs r‖) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
            _ = Λ * ((t ((r : ℕ) + 1) - t r) ^ 2 * ‖bs r‖ / 2) := by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.sum_div]
  calc ‖sol T - target D hM t T N x (sol 0) bs‖ ≤
        ‖sol T - meshRecurrence Gs bsq Δ (sol 0) M‖ +
          ‖meshRecurrence Gs bsq Δ (sol 0) M - target D hM t T N x (sol 0) bs‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by
      have h1 : ‖sol T - meshRecurrence Gs bsq Δ (sol 0) M‖ ≤ _ := hMesh.trans hSum
      nlinarith [hRef, h1]

end

end MeshSampling

end TimeDependentExtensions
