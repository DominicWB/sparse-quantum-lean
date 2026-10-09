import ChebyshevFilter.SignedWalk
import ChebyshevFilter.Facts

set_option autoImplicit false

/-!
# Proposition `qls:prop:chebyshev`

`chebyshev_filter` collects the statement of the proposition for a unitary `W` on a
finite-dimensional Hilbert space whose eigenphases `θ` with `e^{iθ} ≠ 1` satisfy
`|sin(θ/2)| ≥ b`, `0 < b < 1`, `0 < δ < 1`, at the degree `d = ⌈arcosh(1/δ)/(2 artanh b)⌉`:
the Laurent coefficients of `F_{b,d}` are nonnegative, supported on `-d, …, d` and sum to one;
`∑_j p_j e^{ijθ} = T_d((1 + λ) cos θ + λ) / T_d(1 + 2λ)`; `F_{b,d}(1) = 1`;
`‖F_{b,d}(W) - P‖ ≤ δ`; `F_{b,d}(W)` acts as `F_{b,d}(e^{iθ})` on each eigenvector; and the
normalisation-one LCU circuit with `d` signed walk steps has success block `F_{b,d}(W)`.

`chebyshev_filter_program` adds Lemma `qls:lem:signedwalk`: for a walk
`W(x) = R V(x)† C V(x)` with oracle programs `V`, the LCU circuit is a program whose success
block is `F_{b,d}(W(x))` on every input and whose oracle cost is `d` times that of one
forward walk step, label by label.
-/

namespace ChebyshevFilter

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems SparseLinearSystems.UnitaryFilter
open scoped InnerProduct

/-- **Proposition `qls:prop:chebyshev`.** -/
theorem chebyshev_filter {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] {W : V →L[ℂ] V} (hW : Unitary W) {b δ : ℝ}
    (hb0 : 0 < b) (hb1 : b < 1)
    (hphase : ∀ (θ : ℝ) (v : V), v ≠ 0 → W v = Complex.exp (θ * Complex.I) • v →
      Complex.exp (θ * Complex.I) ≠ 1 → b ≤ |Real.sin (θ / 2)|)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ j, 0 ≤ filterCoeff b (chebDegree b δ) j) ∧
      (∀ j ∉ Finset.Icc (-(chebDegree b δ : ℤ)) (chebDegree b δ),
        filterCoeff b (chebDegree b δ) j = 0) ∧
      ∑ j ∈ Finset.Icc (-(chebDegree b δ : ℤ)) (chebDegree b δ),
        filterCoeff b (chebDegree b δ) j = 1 ∧
      (∀ θ : ℝ, ∑ j ∈ Finset.Icc (-(chebDegree b δ : ℤ)) (chebDegree b δ),
          ((filterCoeff b (chebDegree b δ) j : ℝ) : ℂ) * Complex.exp ((j : ℂ) * θ * Complex.I) =
        ((filterFun b (chebDegree b δ) θ : ℝ) : ℂ)) ∧
      filterFun b (chebDegree b δ) 0 = 1 ∧
      ‖filterOp W b (chebDegree b δ) - fixedProj W‖ ≤ δ ∧
      (∀ (θ : ℝ) (v : V), v ≠ 0 → W v = Complex.exp (θ * Complex.I) • v →
        filterOp W b (chebDegree b δ) v = ((filterFun b (chebDegree b δ) θ : ℝ) : ℂ) • v) ∧
      ((seed (V := V) b (chebDegree b δ))†) ∘L seed b (chebDegree b δ) = 1 ∧
      ((seed (V := V) b (chebDegree b δ))†) ∘L
          (signedSteps W (chebDegree b δ) (chebDegree b δ) ∘L seed b (chebDegree b δ)) =
        filterOp W b (chebDegree b δ) := by
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hb1⟩
  have hb2 := sq_lt_one_of_mem hb
  exact ⟨filterCoeff_nonneg hb _, fun j hj => filterCoeff_eq_zero hb hj, sum_filterCoeff hb _,
    laurent_eq hb2 _, filterFun_zero hb _,
    norm_filterOp_sub_fixedProj_le hW hb0 hb1 (gap_of_phase hW hphase) hδ0 hδ1.le,
    fun θ v hv hWv => filterOp_apply_eigen hW hb2 _ hv hWv, seed_isometry hb _,
    lcu_compression W hb _⟩

/-- **Proposition `qls:prop:chebyshev` with Lemma `qls:lem:signedwalk`**: for the walk
`W(x) = R V(x)† C V(x)` with a gap `2b` on every input, the LCU program of
`d = chebDegree b δ` signed steps has success block `F_{b,d}(W(x))`, within `δ` of the
eigenvalue-one projector, and costs `d` forward walk steps. -/
theorem chebyshev_filter_program {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [FiniteDimensional ℂ K] [CompleteSpace K] {X L : Type*} {O : L → X → K →L[ℂ] K}
    (R C : K →L[ℂ] K) (hR : OracleCircuit.IsUnitary R) (hC : OracleCircuit.IsUnitary C)
    (pV : MultiOracleCircuit.Program O) (hO : ∀ l x, OracleCircuit.IsUnitary (O l x))
    {b δ : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hgap : ∀ (x : X) (z : ℂ) (v : K), v ≠ 0 → conjWalk R C pV x v = z • v → z ≠ 1 →
      2 * b ≤ ‖z - 1‖)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ x : X, ((seed (V := K) b (chebDegree b δ))†) ∘L
          ((lcuProg R C hR hC pV (chebDegree b δ) (chebDegree b δ)).eval x ∘L
            seed b (chebDegree b δ)) =
        filterOp (conjWalk R C pV x) b (chebDegree b δ)) ∧
      (∀ x : X, ‖filterOp (conjWalk R C pV x) b (chebDegree b δ) -
        fixedProj (conjWalk R C pV x)‖ ≤ δ) ∧
      ∀ w : L → ℕ, (lcuProg R C hR hC pV (chebDegree b δ) (chebDegree b δ)).cost w =
        chebDegree b δ * (forwardProg R C hR hC pV).cost w := by
  have hb : b ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, hb1⟩
  refine ⟨fun x => lcuProg_compression R C hR hC pV hO hb _ x, fun x => ?_,
    fun w => lcuProg_cost R C hR hC pV _ _ w⟩
  have hU := conjWalk_unitary R C hR hC pV hO x
  exact norm_filterOp_sub_fixedProj_le ⟨hU.1, hU.2⟩ hb0 hb1 (hgap x) hδ0 hδ1.le

end

end ChebyshevFilter
