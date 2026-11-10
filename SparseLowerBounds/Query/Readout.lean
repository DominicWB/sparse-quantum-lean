import SparseLowerBounds.Query.XorWeight

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Output readout and accuracy in observable form

An algorithm's output is read through a fixed isometry
`e : K →L[ℂ] SysGarb S G` into system ⊗ garbage, where the system is
`EuclideanSpace ℂ S` and the garbage `G` is any Hilbert space. A system
observable `M` acts on the workspace as `outObs e M = e† (M ⊗ 1_G) e`.

Accuracy is stated in the observable form equivalent to trace distance: for
Hermitian `X`, `‖X‖₁ = sup {|tr (M X)| : M Hermitian, ‖M‖ ≤ 1}`, so
`½ ‖ρ - |ψ⟩⟨ψ|‖₁ ≤ ε` iff `|tr (M ρ) - ⟪ψ, M ψ⟫| ≤ 2 ε` for every such `M`
(manuscript eqs. `qlsl:eq:target` and `hsl:eq:accuracy`). The reduced density
of the output is `reducedDensity`, with `tr (M ρ) = ⟪Φ, (M ⊗ 1) Φ⟫`
(`inner_liftObs`); the bridge to the release's `hermitianTraceDistance` uses it.

In the heralded form the input-independent herald projection `P` is applied
first and the conditional statement is multiplied through by the success
probability `‖P Φ‖²`, so no division occurs and zero success is allowed.
The heralded correlation lemma (`heralded_correlation`) is the step of
eq. `qlsl:eq:bias` and of eq. `odel:eq:heraldcorr`.
-/

namespace SparseLowerBounds

noncomputable section
open scoped InnerProduct InnerProductSpace Matrix

/-- System ⊗ garbage, `ℂ^S ⊗ G`. -/
abbrev SysGarb (S G : Type*) [NormedAddCommGroup G] : Type _ := Joint S G

namespace Readout

variable {S G K : Type*} [Fintype S] [DecidableEq S]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A system observable on system ⊗ garbage: `M ⊗ 1_G`. -/
def liftObs (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    SysGarb S G →L[ℂ] SysGarb S G :=
  Joint.kernel ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm M)

omit [CompleteSpace G] in
theorem liftObs_apply (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (Φ : SysGarb S G)
    (i : S) : liftObs M Φ i = ∑ i', M (EuclideanSpace.single i' 1) i • Φ i' := by
  rw [liftObs, Joint.kernel_apply]
  refine Finset.sum_congr rfl fun i' _ => ?_
  congr 1

omit [CompleteSpace G] in
theorem norm_liftObs_le (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    ‖(liftObs M : SysGarb S G →L[ℂ] SysGarb S G)‖ ≤ ‖M‖ := by
  refine (Joint.norm_kernel_le (K := G) ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm M)).trans
    (le_of_eq ?_)
  rw [Matrix.cstar_norm_def, StarAlgEquiv.apply_symm_apply]

theorem isSelfAdjoint_liftObs {M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S}
    (hM : IsSelfAdjoint M) : IsSelfAdjoint (liftObs M : SysGarb S G →L[ℂ] SysGarb S G) := by
  have hT : ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm M)ᴴ =
      (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm M := by
    rw [← Matrix.star_eq_conjTranspose, ← map_star, hM.star_eq]
  show star (liftObs M) = liftObs M
  rw [liftObs, Joint.star_kernel, hT]

/-- The workspace operator measuring `M` on the output: `e† (M ⊗ 1_G) e`. -/
def outObs (e : K →L[ℂ] SysGarb S G) (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    K →L[ℂ] K :=
  e† ∘L liftObs M ∘L e

theorem norm_outObs_le (e : K →L[ℂ] SysGarb S G) (he : e† ∘L e = 1)
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) : ‖outObs e M‖ ≤ ‖M‖ := by
  have he1 : ‖e‖ ≤ 1 := by
    have h := ContinuousLinearMap.norm_adjoint_comp_self e
    rw [he] at h
    have h1 : ‖(1 : K →L[ℂ] K)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg e]
  have he2 : ‖e†‖ ≤ 1 := by rwa [LinearIsometryEquiv.norm_map]
  calc ‖outObs e M‖ = ‖e† ∘L (liftObs M ∘L e)‖ := rfl
    _ ≤ ‖e†‖ * (‖(liftObs M : SysGarb S G →L[ℂ] SysGarb S G)‖ * ‖e‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖M‖ * 1) := by
        gcongr
        exact norm_liftObs_le (G := G) M
    _ = ‖M‖ := by ring

/-- The reduced density of a vector of system ⊗ garbage,
`ρ_{ij} = ⟪Φ_j, Φ_i⟫_G` (unnormalised: its trace is `‖Φ‖²`). -/
def reducedDensity (Φ : SysGarb S G) : Matrix S S ℂ :=
  Matrix.of fun i j => ⟪Φ j, Φ i⟫_ℂ

omit [CompleteSpace G] in
/-- `⟪Φ, (M ⊗ 1) Φ⟫ = tr (M ρ)`. -/
theorem inner_liftObs (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (Φ : SysGarb S G) :
    ⟪Φ, liftObs M Φ⟫_ℂ =
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm M * reducedDensity Φ).trace := by
  rw [PiLp.inner_apply, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [liftObs, Joint.kernel_apply, inner_sum, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, reducedDensity, Matrix.of_apply]

/-- The output expectation of `M` is `tr (M ρ)` for the reduced density of `e v`. -/
theorem inner_outObs (e : K →L[ℂ] SysGarb S G)
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (v : K) :
    ⟪v, outObs e M v⟫_ℂ =
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm M * reducedDensity (e v)).trace := by
  rw [outObs, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.comp_apply]
  exact inner_liftObs M (e v)

/-- **Accuracy, observable form of trace distance at most `ε`**: the output
`Φ` read through `e` reproduces every Hermitian contraction's expectation on
the target `ψ` within `2 ε`. -/
def Accurate (e : K →L[ℂ] SysGarb S G) (Φ : K) (ψ : EuclideanSpace ℂ S) (ε : ℝ) : Prop :=
  ∀ M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S, IsSelfAdjoint M → ‖M‖ ≤ 1 →
    |(⟪Φ, outObs e M Φ⟫_ℂ).re - (⟪ψ, M ψ⟫_ℂ).re| ≤ 2 * ε

/-- **Heralded accuracy**: conditional on the herald projection `P` the output
is `ε`-close to `ψ` in trace distance, multiplied through by the success
probability `‖P Φ‖²`. With `P = 1` this is `Accurate` for a unit vector `Φ`. -/
def HeraldedAccurate (e : K →L[ℂ] SysGarb S G) (P : K →L[ℂ] K) (Φ : K)
    (ψ : EuclideanSpace ℂ S) (ε : ℝ) : Prop :=
  ∀ M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S, IsSelfAdjoint M → ‖M‖ ≤ 1 →
    |(⟪Φ, (P ∘L outObs e M ∘L P) Φ⟫_ℂ).re - ‖P Φ‖ ^ 2 * (⟪ψ, M ψ⟫_ℂ).re| ≤
      2 * ε * ‖P Φ‖ ^ 2

/-- **Heralded correlation** (eq. `qlsl:eq:bias`, and
eq. `odel:eq:heraldcorr`). If the output is heralded-accurate with success
probability at least `p₀`, and a Hermitian contraction `D` has signed ideal
expectation `sgn ⟪ψ, D ψ⟫ ≥ a ≥ 2 ε` with `|sgn| ≤ 1`, then the unconditional
workspace observable `P (e† (D ⊗ 1) e) P`, a contraction, has signed
correlation at least `p₀ (a - 2 ε)`. No division by the success probability. -/
theorem heralded_correlation (e : K →L[ℂ] SysGarb S G) (he : e† ∘L e = 1)
    (P : K →L[ℂ] K) (hP : IsStarProjection P) (Φ : K) (ψ : EuclideanSpace ℂ S) (ε : ℝ)
    (hacc : HeraldedAccurate e P Φ ψ ε) {p₀ : ℝ} (hp₀ : p₀ ≤ ‖P Φ‖ ^ 2)
    (D : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (hD : IsSelfAdjoint D) (hD1 : ‖D‖ ≤ 1)
    {sgn a : ℝ} (hsgn : |sgn| ≤ 1) (ha : a ≤ sgn * (⟪ψ, D ψ⟫_ℂ).re) (hεa : 2 * ε ≤ a) :
    p₀ * (a - 2 * ε) ≤ sgn * (⟪Φ, (P ∘L outObs e D ∘L P) Φ⟫_ℂ).re ∧
      ‖P ∘L outObs e D ∘L P‖ ≤ 1 := by
  have hA : ‖outObs e D‖ ≤ 1 := (norm_outObs_le e he D).trans hD1
  have hP1 : ‖P‖ ≤ 1 := IsStarProjection.norm_le P hP
  refine ⟨?_, ?_⟩
  · have h := hacc D hD hD1
    set X := (⟪Φ, (P ∘L outObs e D ∘L P) Φ⟫_ℂ).re
    set q := ‖P Φ‖ ^ 2
    set d := (⟪ψ, D ψ⟫_ℂ).re
    have hq : 0 ≤ q := by positivity
    have h3 : |sgn * (X - q * d)| ≤ 2 * ε * q := by
      rw [abs_mul]
      calc |sgn| * |X - q * d| ≤ 1 * (2 * ε * q) :=
            mul_le_mul hsgn h (abs_nonneg _) zero_le_one
        _ = 2 * ε * q := one_mul _
    have h4 := neg_abs_le (sgn * (X - q * d))
    have h5 : q * a ≤ q * (sgn * d) := mul_le_mul_of_nonneg_left ha hq
    have h6 : p₀ * (a - 2 * ε) ≤ q * (a - 2 * ε) :=
      mul_le_mul_of_nonneg_right hp₀ (by linarith)
    have e1 : sgn * X = sgn * (X - q * d) + q * (sgn * d) := by ring
    have e2 : q * (a - 2 * ε) = q * a - 2 * ε * q := by ring
    linarith
  · calc ‖P ∘L outObs e D ∘L P‖ ≤ ‖P‖ * (‖outObs e D‖ * ‖P‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (1 * 1) := by gcongr
      _ = 1 := by norm_num

end Readout

end

end SparseLowerBounds
end
