import MeasuredUnitaryLowerBound.Global.Kernel
import AdaptiveUnitaryLowerBound.Kernel
import AdaptiveHamiltonianLowerBound.Model.Single

set_option autoImplicit false

/-!
# The endpoint search bound from readout probabilities

For the lower half of Corollary `hs:cor:unitary` of the manuscript at trace-distance error `1/2`. A
family of readout effects `R_y`, `y : Fin N`, on the output, with `‖R_x - R_{x'}‖ ≤ 1`, gives read
values `r(x, y)`: the heralded correlation of `R_y` on instance `x`. The pair observable
`R_x - R_{x'}` has the gap `g(x, x') = r(x, x) - r(x, x') - r(x', x) + r(x', x')` (`pair_gap_eq`),
and these gaps sum to `2 ∑_x (N r(x, x) - ∑_y r(x, y))` over the ordered pairs (`sum_pair_gaps`):
the gaps are large on average whenever the read value of the correct answer exceeds a `1/N` share of
the total, even though a single pair may have no gap.

* `tree_count_ge_of_reads`: adaptive protocols over phase-implemented labels, on
  finite-dimensional spaces; separation from
  `AdaptiveUnitaryLowerBound.Kernel.treeKernel_re_le_of_gap`.
* `program_count_ge_of_reads`: a single program on a unit seed, with read values the expectations
  of `R_y` on the final vectors, on any workspace; separation from
  `SparseLowerBounds.PositiveAdversary.norm_inner_le_of_gap` and the progress of the one-trial
  protocol `AdaptiveHamiltonianLowerBound.Single.tree`.

If `N r(x, x) - ∑_y r(x, y) ≥ b ≥ 0` on every instance, the worst-case weighted cost satisfies
`b² ≤ 4 (N - 1) √(N - 1) Q`.
-/

namespace MeasuredUnitaryLowerBound.Global

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLinearSystems.Protocol
open AdaptiveODELowerBound.Adversary (treeKernel)
open LinearSystemLowerBound (corr)
open UnitaryImplementationExtensions
open scoped InnerProduct InnerProductSpace

variable {E W Fl L B I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

/-- **The summed pair gaps.** For read values `r : Fin N → Fin N → ℝ`,
`∑_{x ≠ x'} (r(x, x) - r(x, x') - r(x', x) + r(x', x')) = 2 ∑_x (N r(x, x) - ∑_y r(x, y))`. -/
theorem sum_pair_gaps {N : ℕ} (r : Fin N → Fin N → ℝ) :
    ∑ x, ∑ x', Search.adversary N x x' * (r x x - r x x' - r x' x + r x' x') =
      2 * ∑ x, ((N : ℝ) * r x x - ∑ y, r x y) := by
  have h : ∀ x x', Search.adversary N x x' * (r x x - r x x' - r x' x + r x' x') =
      r x x - r x x' - r x' x + r x' x' := by
    intro x x'
    unfold Search.adversary
    split_ifs with hx
    · subst hx; ring
    · ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun x x' => r x' x)]
  ring

omit [CompleteSpace E] in
/-- **The gap of a difference of effects** in the heralded correlation:
`corr (R_x - R_{x'}) ρ_x - corr (R_x - R_{x'}) ρ_{x'} = r(x, x) - r(x, x') - r(x', x) + r(x', x')`
with `r(x, y) = corr R_y ρ_x`. -/
theorem pair_gap_eq {X : Type*} (R : X → E →L[ℂ] E) (ρ : X → E →L[ℂ] E) (x x' : X) :
    corr (R x - R x') (ρ x) - corr (R x - R x') (ρ x') =
      corr (R x) (ρ x) - corr (R x') (ρ x) - corr (R x) (ρ x') + corr (R x') (ρ x') := by
  simp only [corr, ContinuousLinearMap.sub_comp, ContinuousLinearMap.toLinearMap_sub, map_sub,
    Complex.sub_re]
  ring

/-- **The endpoint search bound for adaptive protocols, readout form.** Under the access
hypotheses of `adversary_deficit_le`, on finite-dimensional workspace and output spaces, let
`R : Fin N → E →L[ℂ] E` be readout effects with `‖R x - R x'‖ ≤ 1` for `x ≠ x'`. If on every
instance `x`, with `r(x, y) = corr (R y) (T.successDensity x)`,
`b ≤ N r(x, x) - ∑_y r(x, y)` for some `b ≥ 0`, then
`b² ≤ 4 (N - 1) √(N - 1) worstCost_w(T)`. -/
theorem tree_count_ge_of_reads [Fintype I] [FiniteDimensional ℂ W] [FiniteDimensional ℂ E]
    {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I) (c : I → Fin N) (Enc : W →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (T : Tree O Fl E) (R : Fin N → E →L[ℂ] E) (hR : ∀ x x', x ≠ x' → ‖R x - R x'‖ ≤ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hread : ∀ x, b ≤ (N : ℝ) * corr (R x) (T.successDensity x) -
      ∑ y, corr (R y) (T.successDensity x)) :
    b ^ 2 ≤ 4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * T.worstCost w := by
  have hsum : ∑ x, ∑ x', Search.adversary N x x' *
      (corr (R x - R x') (T.successDensity x) - corr (R x - R x') (T.successDensity x')) =
      2 * ∑ x, ((N : ℝ) * corr (R x) (T.successDensity x) -
        ∑ y, corr (R y) (T.successDensity x)) := by
    rw [← sum_pair_gaps (fun x y => corr (R y) (T.successDensity x))]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    rw [pair_gap_eq]
  have hb' : ∑ _x : Fin N, b = (N : ℝ) * b := by simp
  have hle := Finset.sum_le_sum (s := Finset.univ) fun x (_ : x ∈ Finset.univ) => hread x
  refine tree_count_ge_of_kernel_gaps hN P c Enc hEnc hO w hw T
    (fun x x' => corr (R x - R x') (T.successDensity x) - corr (R x - R x') (T.successDensity x'))
    hb ?_ ?_ ?_
  · intro x x' _
    have h := AdaptiveUnitaryLowerBound.Kernel.treeKernel_re_le_of_gap hO T 0 (by simp) le_rfl
      (x := x) (x' := x') (by simp [corr])
    simpa using h
  · intro x x' hxx' hg
    have h := AdaptiveUnitaryLowerBound.Kernel.treeKernel_re_le_of_gap hO T (R x - R x')
      (hR x x' hxx') (β := (corr (R x - R x') (T.successDensity x) -
        corr (R x - R x') (T.successDensity x')) / 2) (by linarith) (x := x) (x' := x')
      (by linarith)
    linarith
  · rw [hsum]
    linarith

/-- **The endpoint search bound for one program, readout form.** Under the access hypotheses of
`adversary_deficit_le` (any workspace), let `p` be a program over the labels run on a unit seed
`φ₀`, and `R : Fin N → W →L[ℂ] W` effects on the workspace with `‖R x - R x'‖ ≤ 1` for `x ≠ x'`.
If on every instance `x`, with `r(x, y) = Re ⟪p(x) φ₀, R_y p(x) φ₀⟫`,
`b ≤ N r(x, x) - ∑_y r(x, y)` for some `b ≥ 0`, then
`b² ≤ 4 (N - 1) √(N - 1) cost_w(p)`. -/
theorem program_count_ge_of_reads [Fintype I] {N : ℕ} (hN : 2 ≤ N) (P : ProjFamily B I)
    (c : I → Fin N) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    {O : L → Fin N → W →L[ℂ] W} (hO : ∀ l m, OracleCircuit.IsUnitary (O l m)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun m => P.phase (Search.markedString c m))
      (O l) Enc (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : W) (hφ₀ : ‖φ₀‖ = 1)
    (R : Fin N → W →L[ℂ] W) (hR : ∀ x x', x ≠ x' → ‖R x - R x'‖ ≤ 1) {b : ℝ} (hb : 0 ≤ b)
    (hread : ∀ x, b ≤ (N : ℝ) * (⟪p.eval x φ₀, R x (p.eval x φ₀)⟫_ℂ).re -
      ∑ y, (⟪p.eval x φ₀, R y (p.eval x φ₀)⟫_ℂ).re) :
    b ^ 2 ≤ 4 * ((N : ℝ) - 1) * Real.sqrt ((N : ℝ) - 1) * p.cost w := by
  let T := AdaptiveHamiltonianLowerBound.Single.tree ℂ p φ₀ hφ₀
  have hkern : ∀ m m', treeKernel T m m' = ⟪p.eval m φ₀, p.eval m' φ₀⟫_ℂ := by
    intro m m'
    simp [T, AdaptiveODELowerBound.Adversary.treeKernel, AdaptiveHamiltonianLowerBound.Single.tree,
      ODELowerBoundExtensions.Release.kernel, ODELowerBoundExtensions.Release.trialKernel,
      AdaptiveHamiltonianLowerBound.Single.trial]
  have hEval : ∀ m, ‖p.eval m φ₀‖ = 1 := by
    intro m
    rw [(ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
      (MultiOracleCircuit.Program.eval_unitary p hO m).1]
    exact hφ₀
  let r : Fin N → Fin N → ℝ := fun x y => (⟪p.eval x φ₀, R y (p.eval x φ₀)⟫_ℂ).re
  let g : Fin N → Fin N → ℝ := fun x x' =>
    (⟪p.eval x φ₀, (R x - R x') (p.eval x φ₀)⟫_ℂ).re -
      (⟪p.eval x' φ₀, (R x - R x') (p.eval x' φ₀)⟫_ℂ).re
  have hsum : ∑ x, ∑ x', Search.adversary N x x' * g x x' =
      2 * ∑ x, ((N : ℝ) * r x x - ∑ y, r x y) := by
    rw [← sum_pair_gaps r]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    simp only [g, r, sub_apply, inner_sub_right, Complex.sub_re]
    ring
  have hb' : ∑ _x : Fin N, b = (N : ℝ) * b := by simp
  have hle := Finset.sum_le_sum (s := Finset.univ) fun x (_ : x ∈ Finset.univ) => hread x
  have h := tree_count_ge_of_kernel_gaps hN P c Enc hEnc hO w hw T g hb ?_ ?_ ?_
  · rwa [AdaptiveHamiltonianLowerBound.Single.worstCost_tree] at h
  · intro x x' _
    rw [hkern]
    refine (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [hEval, hEval, one_mul]
  · intro x x' hxx' hg
    rw [hkern]
    have h := PositiveAdversary.norm_inner_le_of_gap (A := R x - R x') (hR x x' hxx')
      (ψ := p.eval x φ₀) (φ := p.eval x' φ₀) (by rw [hEval, hEval]) (hEval x).le hg
      (le_abs_self _)
    rw [hEval, one_pow] at h
    exact (Complex.re_le_norm _).trans h
  · rw [hsum]
    linarith

end
end MeasuredUnitaryLowerBound.Global
