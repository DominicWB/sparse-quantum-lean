import AdaptiveHamiltonianLowerBound.Access.HardData
import SparseLowerBounds.Hamiltonian.Amplitude
import LinearSystemLowerBound.Weight.Bias

set_option autoImplicit false

/-!
# Accuracy of adaptive outputs and the heralded correlation

An adaptive protocol `T : SparseLinearSystems.Protocol.Tree O F E` heralds success with
probability `T.successMass x` and then outputs the conditional density operator
`T.conditionalDensity x` on the finite-dimensional output space `E`. As in the released
Hamiltonian-simulation lower bound (`SparseLowerBounds.Readout`), the output is read through a
fixed isometry `e : E →L[ℂ] SysGarb S G` into system ⊗ garbage, and a system observable `M`
acts as `outObs e M = e† (M ⊗ 1_G) e`.

`DensityAccurate e ρ ψ ε` is the observable form of trace distance at most `ε` (manuscript
eq. `hsl:eq:accuracy`): for every self-adjoint `M` with `‖M‖ ≤ 1`,
`|Re tr(outObs e M · ρ) - Re⟪ψ, M ψ⟫| ≤ 2ε`. For a pure output `ρ = |Φ⟩⟨Φ|` it is the released
notion `Readout.Accurate e Φ ψ ε` (`densityAccurate_pure_iff`).

`tree_correlation` is the heralded-correlation step (eq. `odel:eq:heraldcorr`, with the random-bit
convention for failures): success probability at least `2/3`, conditional accuracy `ε` and ideal
signed expectation `σ Re⟪ψ, D ψ⟫ ≥ a₀ ≥ 2ε` give the signed correlation
`σ Re tr(outObs e D · ρ_x) ≥ (2/3)(a₀ - 2ε)` of the unnormalised heralded output
`ρ_x = T.successDensity x`.

The signs of the hard families are the parity `parSign` of the weight argument:
`parity_eq_parSign` (search families) and `bitParity_toBits` (precision family).
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open LinearSystemLowerBound SparseLowerBounds SparseLowerBounds.Readout

section Accuracy

variable {S G E : Type*} [Fintype S] [DecidableEq S]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]

/-- **Accuracy of a density operator, observable form of trace distance at most `ε`**: the
output `ρ`, read through `e`, reproduces every Hermitian contraction's expectation on the
target `ψ` within `2ε`. -/
def DensityAccurate (e : E →L[ℂ] SysGarb S G) (ρ : E →L[ℂ] E) (ψ : EuclideanSpace ℂ S)
    (ε : ℝ) : Prop :=
  ∀ M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S, IsSelfAdjoint M → ‖M‖ ≤ 1 →
    |corr (outObs e M) ρ - (⟪ψ, M ψ⟫_ℂ).re| ≤ 2 * ε

/-- For a pure output, `DensityAccurate` is the released `Readout.Accurate`. -/
theorem densityAccurate_pure_iff (e : E →L[ℂ] SysGarb S G) (Φ : E) (ψ : EuclideanSpace ℂ S)
    (ε : ℝ) :
    DensityAccurate e (ODEMixedOutput.pureOperator Φ) ψ ε ↔ Accurate e Φ ψ ε := by
  simp only [DensityAccurate, Accurate, corr_pure]

omit [FiniteDimensional ℂ E] in
/-- The workspace readout of a system contraction is a contraction. -/
theorem outObs_contraction (e : E →L[ℂ] SysGarb S G) (he : e† ∘L e = 1)
    (M : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (hM : ‖M‖ ≤ 1) (v : E) :
    ‖outObs e M v‖ ≤ ‖v‖ :=
  ((outObs e M).le_opNorm v).trans
    (mul_le_of_le_one_left (norm_nonneg _) ((norm_outObs_le e he M).trans hM))

variable {K F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

omit [FiniteDimensional ℂ E] in
/-- Heralded success turns a conditional correlation into an unconditional one: if the
conditional output has signed correlation at least `b ≥ 0` and success has probability at
least `2/3`, the unconditional signed correlation is at least `(2/3) b`. -/
theorem tree_bias_general (T : Tree O F E) (x : X) (M : E →L[ℂ] E) (σ b : ℝ) (hb : 0 ≤ b)
    (hsucc : 2 / 3 ≤ T.successMass x) (hclose : b ≤ σ * corr M (T.conditionalDensity x)) :
    2 / 3 * b ≤ σ * corr M (T.successDensity x) := by
  set s := T.successMass x
  have hs0 : 0 < s := by linarith
  have hsd : T.successDensity x = ((s : ℝ) : ℂ) • T.conditionalDensity x := by
    rw [Tree.conditionalDensity, smul_smul]
    have : ((s : ℝ) : ℂ) * ((s : ℂ))⁻¹ = 1 := by
      have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      field_simp
    rw [this, one_smul]
  rw [hsd, corr_smul_real]
  nlinarith [mul_le_mul_of_nonneg_left hclose hs0.le]

omit [FiniteDimensional ℂ E] in
/-- **The heralded correlation of an adaptive protocol** (eq. `odel:eq:heraldcorr`): if the
conditional output is `ε`-accurate for the target `ψ`, success has probability at least
`2/3`, and a Hermitian contraction `D` has signed ideal expectation
`σ Re⟪ψ, D ψ⟫ ≥ a₀ ≥ 2ε` with `|σ| ≤ 1`, then
`σ Re tr(outObs e D · ρ_x) ≥ (2/3)(a₀ - 2ε)` for the heralded output `ρ_x`. -/
theorem tree_correlation (e : E →L[ℂ] SysGarb S G) (T : Tree O F E) (x : X)
    (ψ : EuclideanSpace ℂ S) (ε : ℝ) (hacc : DensityAccurate e (T.conditionalDensity x) ψ ε)
    (hsucc : 2 / 3 ≤ T.successMass x) (D : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)
    (hD : IsSelfAdjoint D) (hD1 : ‖D‖ ≤ 1) {σ a₀ : ℝ} (hσ : |σ| ≤ 1)
    (hideal : a₀ ≤ σ * (⟪ψ, D ψ⟫_ℂ).re) (ha₀ : 2 * ε ≤ a₀) :
    2 / 3 * (a₀ - 2 * ε) ≤ σ * corr (outObs e D) (T.successDensity x) := by
  have h := hacc D hD hD1
  set c := corr (outObs e D) (T.conditionalDensity x)
  set r := (⟪ψ, D ψ⟫_ℂ).re
  have h3 : |σ * (c - r)| ≤ 2 * ε := by
    rw [abs_mul]
    calc |σ| * |c - r| ≤ 1 * (2 * ε) :=
          mul_le_mul hσ h (abs_nonneg _) zero_le_one
      _ = 2 * ε := one_mul _
  have hclose : a₀ - 2 * ε ≤ σ * c := by
    have h4 := (abs_le.mp h3).1
    nlinarith
  exact tree_bias_general T x _ σ _ (by linarith) hsucc hclose

end Accuracy

/-! ### Signs -/

/-- The parity `(-1)^{j_1 + ⋯ + j_n}` of the search families is the sign `parSign` of the
weight argument. -/
theorem parity_eq_parSign {n m : ℕ} (j : Fin n → Fin m) : parity j = parSign j := by
  rw [parity_eq_prod]
  rfl

/-- The bit parity of the precision family, read along `toBits`, is `parSign`. -/
theorem bitParity_toBits {n : ℕ} (j : Fin n → Fin 2) :
    BitDegree.bitParity (Access.toBits j) = parSign j := by
  have hj : ∀ k, sgn 2 (j k) = if j k = 1 then -1 else 1 := by
    intro k
    rcases Fin.exists_fin_two.mp ⟨j k, rfl⟩ with h | h <;> simp [h, sgn]
  unfold BitDegree.bitParity parSign
  simp only [hj, Access.toBits, decide_eq_true_eq]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

end

end AdaptiveHamiltonianLowerBound
