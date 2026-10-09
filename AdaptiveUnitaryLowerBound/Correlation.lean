import AdaptiveUnitaryLowerBound.Observable

set_option autoImplicit false

/-!
# Heralded correlations of accurate adaptive outputs with the pair observable

The accuracy notion is the one of the package's adaptive lower bounds
(`AdaptiveHamiltonianLowerBound.DensityAccurate`): an adaptive protocol
`T : SparseLinearSystems.Protocol.Tree O F E` heralds success with probability
`T.successMass x`, and its conditional output `T.conditionalDensity x`, read
through an isometry `e : E →L[ℂ] SysGarb S G` into system ⊗ garbage, is
`ε₀`-accurate for a target `ψ_x` (observable form of trace distance at most
`ε₀`). For the reduction of corollary `hs:cor:unitary` of the manuscript (lines
1711-1718), the target on instance `m` is `|m⟩`.

* `tree_bias_of_mass`: the step `AdaptiveHamiltonianLowerBound.tree_bias_general`
  with any success threshold `s₀ > 0` in place of `2/3`: a conditional signed
  correlation `b ≥ 0` becomes the unconditional `s₀ b`.
* `norm_outObs_pairObs_le`: the workspace readout of the pair observable is a
  contraction.
* `pair_gap`: success probability at least `s₀ > 0` and conditional accuracy
  `ε₀ ≤ 1/2` for the targets `|m⟩`, `|m'⟩` give heralded correlations of the
  pair observable that differ by at least `2 s₀ (1 - 2ε₀)`.
-/

namespace AdaptiveUnitaryLowerBound.Correlation

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout
open SparseLinearSystems.Protocol ContinuousLinearMap
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open LinearSystemLowerBound (corr)
open Observable
open scoped InnerProduct InnerProductSpace

variable {K F E X L G : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  {O : L → X → K →L[ℂ] K}

/-- **Heralded success with any positive threshold**: if the conditional output
has signed correlation at least `b ≥ 0` and success has probability at least
`s₀ > 0`, the unconditional signed correlation is at least `s₀ b`. The case
`s₀ = 2/3` is `AdaptiveHamiltonianLowerBound.tree_bias_general`; the general
threshold serves the unheralded case `s₀ = 1`. -/
theorem tree_bias_of_mass (T : Tree O F E) (x : X) (M : E →L[ℂ] E) (σ b : ℝ) (hb : 0 ≤ b)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hsucc : s₀ ≤ T.successMass x)
    (hclose : b ≤ σ * corr M (T.conditionalDensity x)) :
    s₀ * b ≤ σ * corr M (T.successDensity x) := by
  set s := T.successMass x
  have hs0 : 0 < s := lt_of_lt_of_le hs₀ hsucc
  have hsd : T.successDensity x = ((s : ℝ) : ℂ) • T.conditionalDensity x := by
    rw [Tree.conditionalDensity, smul_smul]
    have : ((s : ℝ) : ℂ) * ((s : ℂ))⁻¹ = 1 := by
      have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      field_simp
    rw [this, one_smul]
  rw [hsd, LinearSystemLowerBound.corr_smul_real]
  nlinarith [mul_le_mul_of_nonneg_left hclose hs0.le, mul_le_mul_of_nonneg_right hsucc hb]

/-- The workspace readout of the pair observable is a contraction
(`SparseLowerBounds.Readout.norm_outObs_le` with `Observable.norm_pairObs_le`). -/
theorem norm_outObs_pairObs_le {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G) (he : e† ∘L e = 1)
    (m m' : Fin N) : ‖outObs e (pairObs m m')‖ ≤ 1 := by
  exact (norm_outObs_le e he _).trans (norm_pairObs_le m m')

/-- **The pair gap of accurate heralded outputs.** If on the instances `m ≠ m'`
the protocol succeeds with probability at least `s₀ > 0` and its conditional
outputs are `ε₀`-accurate for `|m⟩` and `|m'⟩`, with `ε₀ ≤ 1/2`, then the
heralded correlations of the readout of the pair observable `D_{m,m'}` differ by
at least `2 s₀ (1 - 2ε₀)`. -/
theorem pair_gap {N : ℕ} (e : E →L[ℂ] SysGarb (Fin N) G)
    {Q : L → Fin N → K →L[ℂ] K} (T : Tree Q F E) {s₀ ε₀ : ℝ} (hs₀ : 0 < s₀) (hε₀ : ε₀ ≤ 1 / 2)
    {m m' : Fin N}
    (hmm : m ≠ m') (hs : s₀ ≤ T.successMass m) (hs' : s₀ ≤ T.successMass m')
    (hacc : DensityAccurate e (T.conditionalDensity m) (ket m) ε₀)
    (hacc' : DensityAccurate e (T.conditionalDensity m') (ket m') ε₀) :
    2 * (s₀ * (1 - 2 * ε₀)) ≤
      corr (outObs e (pairObs m m')) (T.successDensity m) -
        corr (outObs e (pairObs m m')) (T.successDensity m') := by
  have h1 := hacc (pairObs m m') (isSelfAdjoint_pairObs m m') (norm_pairObs_le m m')
  rw [pairObs_expect_left hmm] at h1
  have h2 := hacc' (pairObs m m') (isSelfAdjoint_pairObs m m') (norm_pairObs_le m m')
  rw [pairObs_expect_right hmm] at h2
  obtain ⟨h1l, -⟩ := abs_le.mp h1
  obtain ⟨-, h2r⟩ := abs_le.mp h2
  have hb : (0 : ℝ) ≤ 1 - 2 * ε₀ := by linarith
  have k1 := tree_bias_of_mass T m (outObs e (pairObs m m')) 1 (1 - 2 * ε₀) hb hs₀ hs
    (by linarith)
  have k2 := tree_bias_of_mass T m' (outObs e (pairObs m m')) (-1) (1 - 2 * ε₀) hb hs₀ hs'
    (by linarith)
  linarith

end
end AdaptiveUnitaryLowerBound.Correlation
