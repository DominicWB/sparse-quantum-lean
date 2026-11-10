import ODELowerBoundExtensions.Release.Purify

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The positive-weight adversary for retry protocols

Manuscript: Lemma `odel:lem:outer` and its use of the bounded-error spectral adversary, for the
release's retry protocols (`ODERepeatProtocol.Protocol`). This is
`SparseLowerBounds.PositiveAdversary.decision_count_ge` with the program replaced by a protocol and
its count by the worst-case weighted cost `Protocol.worstCost w`; the constants are unchanged.

Route. Every label of the oracle family `O` is implemented on a fixed isometric encoding by at most
`w l` queries of a Boolean phase oracle `x ↦ P.phase (y x)` (`EncodedOracle.ImplementsOn`, as in
`Query/Reduction`).

* Progress (`Release/Kernel`, `abs_kernel_progress_le`): the kernel progress
  `Σ_{x,x'} Γ x x' Re κ_p(x, x')` starts at `Σ Γ` (all seeds fixed) and moves by at most
  `2 λ worstCost_w(p) |X|`.
* Bounded error (`Release/Purify`, `exists_purification`, then
  `PositiveAdversary.norm_inner_le_of_gap`): if a contraction `A` on the output space has signed
  heralded correlation `ans x · corr A (p.successDensity x) ≥ β ≥ 0` on every input and `Γ` joins
  only inputs with opposite answers, the purified states of `Γ`-joined inputs have expectation gap
  at least `2β` for the contraction `R` of the purification, hence overlap
  `Re κ_p(x, x') ≤ |κ_p(x, x')| ≤ 1 - β²/2`.
* With the minimum degree `D ≤ Σ_{x'} Γ x x'`: `(β²/2) D ≤ 2 λ worstCost_w(p)`
  (`retry_decision_count_ge`).
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open LinearSystemLowerBound (corr)
open scoped InnerProduct InnerProductSpace

variable {E K X L B I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  {O : L → X → K →L[ℂ] K}

/-- **Positive-weight adversary for retry protocols, bounded-error decision form**
(`PositiveAdversary.decision_count_ge` for protocols): if `Γ` is nonnegative and symmetric, joins
only inputs with opposite answers `ans x' = -ans x` (`|ans x| = 1`), every masked `Γ ∘ Δ_i` has a
Schur certificate with constant `λ ≥ 0`, every row sum of `Γ` is at least `D`, every label of `O`
is implemented on the isometric encoding `Enc` by at most `w l` Boolean phase queries, and a
contraction `A` on the output space has signed heralded correlation at least `β ≥ 0` on every
input, then `(β²/2) D ≤ 2 λ worstCost_w(p)`. -/
theorem retry_decision_count_ge [Fintype X] [Nonempty X] [Fintype I] [FiniteDimensional ℂ K]
    [FiniteDimensional ℂ E] (P : ProjFamily B I) (y : X → I → Bool) (Γ : X → X → ℝ)
    (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam) {D : ℝ} (hdeg : ∀ x, D ≤ ∑ x', Γ x x')
    (ans : X → ℝ) (hans : ∀ x, |ans x| = 1) (hopp : ∀ x x', Γ x x' ≠ 0 → ans x' = -ans x)
    (Enc : K →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l))
    (p : ODERepeatProtocol.Protocol O E) (A : E →L[ℂ] E) (hA : ‖A‖ ≤ 1) {β : ℝ} (hβ : 0 ≤ β)
    (hcorr : ∀ x, β ≤ ans x * corr A (p.successDensity x)) :
    β ^ 2 / 2 * D ≤ 2 * lam * p.worstCost w := by
  obtain ⟨H, _, _, Ψ, R, hΨ, hR, hG, hC⟩ := exists_purification hO p A hA
  -- Overlap bound on `Γ`-joined inputs (proof of Lemma `odel:lem:outer`).
  have hsep : ∀ x x', Γ x x' ≠ 0 → (kernel p x x').re - 1 ≤ -(β ^ 2 / 2) := by
    intro x x' hΓ
    have h1 := hcorr x
    have h2 := hcorr x'
    rw [← hC x] at h1
    rw [← hC x', hopp x x' hΓ] at h2
    have hgap : 2 * β ≤ |(⟪Ψ x, R (Ψ x)⟫_ℂ).re - (⟪Ψ x', R (Ψ x')⟫_ℂ).re| := by
      calc 2 * β ≤ ans x * (⟪Ψ x, R (Ψ x)⟫_ℂ).re + -ans x * (⟪Ψ x', R (Ψ x')⟫_ℂ).re := by
            linarith
        _ = ans x * ((⟪Ψ x, R (Ψ x)⟫_ℂ).re - (⟪Ψ x', R (Ψ x')⟫_ℂ).re) := by ring
        _ ≤ |ans x * ((⟪Ψ x, R (Ψ x)⟫_ℂ).re - (⟪Ψ x', R (Ψ x')⟫_ℂ).re)| := le_abs_self _
        _ = _ := by rw [abs_mul, hans, one_mul]
    have h := PositiveAdversary.norm_inner_le_of_gap hR ((hΨ x).trans (hΨ x').symm)
      (hΨ x).le (mul_nonneg two_pos.le hβ) hgap
    rw [hΨ x, hG x x'] at h
    have hre := Complex.re_le_norm (kernel p x x')
    nlinarith
  have hprog := abs_kernel_progress_le P y Γ hΓ0 hΓs hlam hcert Enc hEnc hO w hw p
  have hfin : ∑ x, ∑ x', Γ x x' * ((kernel p x x').re - 1) ≤
      ∑ x, ∑ x', Γ x x' * (-(β ^ 2 / 2)) := by
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => ?_
    by_cases hΓ : Γ x x' = 0
    · rw [hΓ, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hsep x x' hΓ) (hΓ0 x x')
  have hsum : ∑ x, ∑ x', Γ x x' * (-(β ^ 2 / 2)) = -(β ^ 2 / 2) * ∑ x, ∑ x', Γ x x' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x' _ => by ring
  have hS : (Fintype.card X : ℝ) * D ≤ ∑ x, ∑ x', Γ x x' := by
    have h := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hdeg x
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcard : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hb2 : 0 ≤ β ^ 2 / 2 := by positivity
  have e1 : β ^ 2 / 2 * ((Fintype.card X : ℝ) * D) ≤ β ^ 2 / 2 * ∑ x, ∑ x', Γ x x' :=
    mul_le_mul_of_nonneg_left hS hb2
  have h3 := (abs_le.mp hprog).1
  have key : (Fintype.card X : ℝ) * (β ^ 2 / 2 * D) ≤
      (Fintype.card X : ℝ) * (2 * lam * p.worstCost w) := by
    nlinarith
  exact le_of_mul_le_mul_left key hcard

end

end ODELowerBoundExtensions.Release
