import DysonFullClass.Theorem

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Coverage: from the paper's precision and source clauses to `FullValidAt`

Manuscript, Lemma `odel:lem:dyson` and the input class of Theorem `ode:thm:time`: the
promised certificate selects, for the requested accuracy, an accessible finite mesh, a
represented-data precision and a certified finite source rule. `Theorem.FullValidAt` is the
validity relation of the full-class solver; it states the analytic and source clauses of
`ode:thm:time` together with the Dyson budget `ζ + c_q (e^{E} - 1) ≤ ε/(2000 ḡ)`, where `E` is the
integrated distance `∑_r ∫_{cell r} ‖G_r(u) - C_r‖` between the true pieces and the clipped
represented samples. This module derives that budget from the paper-facing clauses:

* `exp_sub_one_le_of_le_log`: `E ≤ log(1 + δ_m)` gives `e^E - 1 ≤ δ_m` (the paper's form of the
  integrated certificate);
* `fullValidAt_of_clipped`: the clauses of `ode:thm:time`, `E ≤ log(1 + δ_m)` on the clipped
  samples and `ζ + c_q δ_m ≤ ε/(2000 ḡ)` give `FullValidAt`;
* `entry_le_of_opNorm_le`, `entry_le_of_row_norm`: the true row (or operator) norm bound `η`
  bounds every true entry by `η`; `opNorm_add_le`: for `G = D + iH`, `‖G‖ ≤ η_D + η_H`;
* `cellError_clip_le`: if every true piece has entries at most `η` and at most `s` nonzeros per row
  and column, clipping costs at most the factor `2s`: `E(p_η(C_raw)) ≤ 2 s E(C_raw)` (pointwise
  `‖p_η(C_raw) - A‖ ≤ 2 s ‖C_raw - A‖`, `Clip.clip_sub_le`; not a nonexpansiveness claim);
  `clipData_matrix_of_le`: no clipping happens when the represented entries are capped by `η`;
* `fullValidAt_of_raw`: the same as `fullValidAt_of_clipped` from the tighter certificate
  `2 s E(C_raw) ≤ log(1 + δ_m)` on the unclipped represented samples;
* `cell_lipschitz_le`, `cellError_le_lipschitz`: on a Lipschitz cell of width `h_r` with constant
  `L_r` and representation error `ρ_r = ‖G_r(t_r) - C_r‖`, the cell charge is at most
  `L_r h_r²/2 + h_r ρ_r` (time variation and finite representation error together).

The theorems here accept the direct certificate on the represented `C`; certificates on the
Hermitian branches `K_{±k} = H ± kD` of two opposite frequencies give the certificates of
`fullValidAt_of_raw` and `fullValidAt_of_clipped` through the branch bound
`ManuscriptConformance.sampleErr_le_branchSum` (`ManuscriptConformance.BranchCertificates`:
`fullValidAt_of_branch_raw`, `fullValidAt_of_branch_clipped`, `fullValid_of_branch_raw`).
-/

namespace DysonFullClass

noncomputable section
open SparseHamiltonian ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale IsMeshPropagator)
open SparseHamiltonian.GeneralSourceODE (sources)
open SparseHamiltonian.GeneralSourceODE.Compiled (WeightPrep)
open scoped InnerProduct BigOperators

/-- **The paper's integrated certificate**: `E ≤ log(1 + δ)` gives `e^E - 1 ≤ δ`. -/
theorem exp_sub_one_le_of_le_log {E δ : ℝ} (hδ : 0 ≤ δ) (hE : E ≤ Real.log (1 + δ)) :
    Real.exp E - 1 ≤ δ := by
  have h := Real.exp_le_exp.mpr hE
  rw [Real.exp_log (by linarith)] at h
  linarith

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks M m : ℕ}

/-! ### From the clauses of `ode:thm:time` to the validity relation -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Coverage from the clipped certificate**: the clauses of Theorem `ode:thm:time` for an
instance (accretive integrable pieces with mesh propagator, mild solution, weight preparation and
label-controlled loading of the actual source vectors, `B_q ≤ c_q B`, the propagated source
certificate `ζ B`, `x(T) ≠ 0`, `B ≤ ḡ ‖x(T)‖`), the integrated certificate
`E ≤ log(1 + δ_m)` on the clipped represented samples and the budget
`ζ + c_q δ_m ≤ ε/(2000 ḡ)` give `FullValidAt` with target `x(T)`. -/
theorem fullValidAt_of_clipped (D₀ : Data (X × Fin Ks) n Z s) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hη : 0 < η) (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    (ζ δm : ℝ)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : RepresentedSampleODE.RegularPieces t G)
    (hmild : RepresentedSampleODE.MildSolution t T b sol U)
    (hU : IsMeshPropagator G t T U)
    (hW : WeightPrep P (sources (sol 0) bv ω))
    (hL₀ : sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0))
    (hLb : ∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed = ODEStateNormalization.unitDirection (bv i))
    (hmass : ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t)
    (hsrc : ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
        ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t)
    (hsol : sol T ≠ 0) (hB : meshScale sol b t ≤ g * ‖sol T‖)
    (hcq : 0 ≤ cq) (hδm : 0 ≤ δm)
    (hE : cellError σ (clipData D₀ η hη) x t G ≤ Real.log (1 + δm))
    (hbud : ζ + cq * δm ≤ ε / (2000 * g)) :
    FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x (sol T) := by
  refine ⟨G, b, sol, bv, U, ζ, hG, hGint, hmild, hU, hW, hL₀, hLb, hmass, hsrc, hsol, hB, ?_, rfl⟩
  have h := mul_le_mul_of_nonneg_left (exp_sub_one_le_of_le_log hδm hE) hcq
  linarith

/-! ### Entry bounds of the true pieces -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- An operator-norm bound `η` bounds every entry by `η`. -/
theorem entry_le_of_opNorm_le {A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {η : ℝ}
    (h : ‖A‖ ≤ η) (i j : n) : ‖opMatrix A i j‖ ≤ η := by
  have h1 := norm_entry_le (opMatrix A) i j
  rw [matrixOperator_opMatrix] at h1
  exact h1.trans h

omit [DecidableEq n] in
/-- A row Euclidean-norm bound `η` bounds every entry of the row by `η`. -/
theorem entry_le_of_row_norm {A : Matrix n n ℂ} {η : ℝ}
    (h : ∀ i, Real.sqrt (∑ j, ‖A i j‖ ^ 2) ≤ η) (i j : n) : ‖A i j‖ ≤ η := by
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ k, ‖A i k‖ ^ 2 :=
    Finset.single_le_sum (f := fun k => ‖A i k‖ ^ 2) (fun k _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 := Real.abs_le_sqrt h1
  rw [abs_of_nonneg (norm_nonneg _)] at h2
  exact h2.trans (h i)

/-- For `G = D + iH` with `‖D‖ ≤ η_D` and `‖H‖ ≤ η_H`, `‖G‖ ≤ η_D + η_H`. -/
theorem opNorm_add_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {D H : V →L[ℂ] V} {ηD ηH : ℝ} (hD : ‖D‖ ≤ ηD) (hH : ‖H‖ ≤ ηH) :
    ‖D + Complex.I • H‖ ≤ ηD + ηH := by
  calc ‖D + Complex.I • H‖ ≤ ‖D‖ + ‖Complex.I • H‖ := norm_add_le _ _
    _ = ‖D‖ + ‖H‖ := by rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ ηD + ηH := add_le_add hD hH

/-! ### The cost of clipping -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Clipping costs at most `2s` in the integrated certificate**: if every true piece has entries
at most `η` and at most `s` nonzeros in every row and column on its closed cell, the integrated
distance to the clipped represented samples is at most `2 s` times the distance to the raw
represented samples. -/
theorem cellError_clip_le (D₀ : Data (X × Fin Ks) n Z s) {η : ℝ} (hη : 0 < η)
    (σ : Fin M → Fin Ks) (x : X) {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hGint : RepresentedSampleODE.RegularPieces t G)
    (hent : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i j, ‖opMatrix (G r u) i j‖ ≤ η)
    (hrow : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i,
      (Finset.univ.filter fun j => opMatrix (G r u) i j ≠ 0).card ≤ s)
    (hcol : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ j,
      (Finset.univ.filter fun i => opMatrix (G r u) i j ≠ 0).card ≤ s) :
    cellError σ (clipData D₀ η hη) x t G ≤ 2 * s * cellError σ D₀ x t G := by
  unfold cellError
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  have hle : t r ≤ t ((r : ℕ) + 1) := hmesh.mono (Nat.le_succ r)
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hle ((hGint r).sub intervalIntegrable_const).norm
    (((hGint r).sub intervalIntegrable_const).norm.const_mul _) fun u hu => ?_
  have h := clip_sub_le (D₀.matrix (x, σ r)) (opMatrix (G r u)) hη.le s (hent r u hu)
    (data_row_sparse D₀ (x, σ r)) (data_column_sparse D₀ (x, σ r)) (hrow r u hu) (hcol r u hu)
  rw [matrixOperator_opMatrix] at h
  rw [norm_sub_rev, norm_sub_rev (G r u)]
  exact h

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Coverage from the raw certificate**: as `fullValidAt_of_clipped`, with the tighter
certificate `2 s E(C_raw) ≤ log(1 + δ_m)` on the unclipped represented samples, true entries at
most `η` and `s`-sparse true pieces. -/
theorem fullValidAt_of_raw (D₀ : Data (X × Fin Ks) n Z s) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hη : 0 < η) (hmesh : IsMesh t M T) (v : Fin m → ℝ)
    (ω : Fin m → ℂ) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    (ζ δm : ℝ)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGint : RepresentedSampleODE.RegularPieces t G)
    (hmild : RepresentedSampleODE.MildSolution t T b sol U)
    (hU : IsMeshPropagator G t T U)
    (hW : WeightPrep P (sources (sol 0) bv ω))
    (hL₀ : sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0))
    (hLb : ∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed = ODEStateNormalization.unitDirection (bv i))
    (hmass : ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t)
    (hsrc : ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
        ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t)
    (hsol : sol T ≠ 0) (hB : meshScale sol b t ≤ g * ‖sol T‖)
    (hent : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i j, ‖opMatrix (G r u) i j‖ ≤ η)
    (hrow : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ i,
      (Finset.univ.filter fun j => opMatrix (G r u) i j ≠ 0).card ≤ s)
    (hcol : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ j,
      (Finset.univ.filter fun i => opMatrix (G r u) i j ≠ 0).card ≤ s)
    (hcq : 0 ≤ cq) (hδm : 0 ≤ δm)
    (hE : 2 * s * cellError σ D₀ x t G ≤ Real.log (1 + δm))
    (hbud : ζ + cq * δm ≤ ε / (2000 * g)) :
    FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x (sol T) :=
  fullValidAt_of_clipped D₀ σ t T η g cq ε hη v ω P L seed x G b sol bv U ζ δm hG hGint hmild hU
    hW hL₀ hLb hmass hsrc hsol hB hcq hδm
    ((cellError_clip_le D₀ hη σ x hmesh G hGint hent hrow hcol).trans hE) hbud

/-! ### Lipschitz cells -/

/-- **A Lipschitz cell**: if `‖G(u) - G(a)‖ ≤ L (u - a)` on `[a, b]` and `‖G(a) - C‖ ≤ ρ`, the cell
charge is at most `L (b - a)²/2 + (b - a) ρ`. -/
theorem cell_lipschitz_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {a b L ρ : ℝ} (hab : a ≤ b) (Gr : ℝ → V →L[ℂ] V) (C : V →L[ℂ] V)
    (hint : IntervalIntegrable Gr volume a b)
    (hLip : ∀ u ∈ Icc a b, ‖Gr u - Gr a‖ ≤ L * (u - a)) (hρ : ‖Gr a - C‖ ≤ ρ) :
    ∫ u in a..b, ‖Gr u - C‖ ≤ L * (b - a) ^ 2 / 2 + (b - a) * ρ := by
  have hpt : ∀ u ∈ Icc a b, ‖Gr u - C‖ ≤ L * (u - a) + ρ := fun u hu =>
    calc ‖Gr u - C‖ = ‖(Gr u - Gr a) + (Gr a - C)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖Gr u - Gr a‖ + ‖Gr a - C‖ := norm_add_le _ _
      _ ≤ L * (u - a) + ρ := add_le_add (hLip u hu) hρ
  have hc1 : Continuous fun u : ℝ => u - a := by fun_prop
  have hc2 : Continuous fun u : ℝ => L * (u - a) := by fun_prop
  have hint2 : IntervalIntegrable (fun u => L * (u - a) + ρ) volume a b :=
    (hc2.add continuous_const).intervalIntegrable a b
  have e1 : ∫ u in a..b, (u - a) = (b - a) ^ 2 / 2 := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b) (fun x : ℝ => x) a
    try simp only at h
    rw [h, sub_self, integral_id]
    ring
  have e2 : ∫ u in a..b, (L * (u - a) + ρ) = L * ((b - a) ^ 2 / 2) + (b - a) * ρ := by
    rw [intervalIntegral.integral_add (hc2.intervalIntegrable a b) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, e1, intervalIntegral.integral_const, smul_eq_mul]
  calc ∫ u in a..b, ‖Gr u - C‖ ≤ ∫ u in a..b, (L * (u - a) + ρ) :=
        intervalIntegral.integral_mono_on hab (hint.sub intervalIntegrable_const).norm hint2 hpt
    _ = L * (b - a) ^ 2 / 2 + (b - a) * ρ := by rw [e2]; ring

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The integrated certificate on Lipschitz cells**: with cell constants `L_r` and
representation errors `ρ_r = ‖G_r(t_r) - C_r‖`,
`E ≤ ∑_r (L_r h_r²/2 + h_r ρ_r)`, `h_r = t_{r+1} - t_r`. -/
theorem cellError_le_lipschitz (D : Data (X × Fin Ks) n Z s) (σ : Fin M → Fin Ks) (x : X)
    {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hGint : RepresentedSampleODE.RegularPieces t G) (Lc ρ : Fin M → ℝ)
    (hLip : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)),
      ‖G r u - G r (t r)‖ ≤ Lc r * (u - t r))
    (hρ : ∀ r : Fin M,
      ‖G r (t r) - SparseStateOverlap.matrixOperator (D.matrix (x, σ r))‖ ≤ ρ r) :
    cellError σ D x t G ≤
      ∑ r : Fin M, (Lc r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 + (t ((r : ℕ) + 1) - t r) * ρ r) :=
  Finset.sum_le_sum fun r _ =>
    cell_lipschitz_le (hmesh.mono (Nat.le_succ r)) (G r) _ (hGint r) (hLip r) (hρ r)

end

end DysonFullClass
