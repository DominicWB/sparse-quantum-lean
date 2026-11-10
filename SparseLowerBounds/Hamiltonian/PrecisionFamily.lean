import SparseLowerBounds.Hamiltonian.SearchFamily

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The signed scalar family: precision lower bound

Manuscript: Lemma `hsl:lem:precision` (eq. `hsl:eq:precisionlower`), for **any** labelled oracle
family whose labels are implementable on a fixed isometric encoding with `w l` Boolean bit queries
(`EncodedOracle.ImplementsOn` over `bitOracle P`).

* `precision_cost_of_corr`: correlation form. If some input-independent
  operator has positive (unnormalised) parity correlation, then
  `p.cost w ≥ n/2`: compile (`Reduction.exists_boolean_program_inner`) and
  apply the degree bound `BitDegree.le_two_mul_count` (`2q ≥ n`). No norm
  hypothesis on the seed, the operator or the readout is needed. Shared with
  `Hamiltonian/Herald`.
* `precision_general`: for `n ≥ 1` (the manuscript states `n ≥ 2`; `n ≥ 1`
  suffices), `0 < τ ≤ n` and `ε ≤ (τ/(2n))^n/8`, an `ε`-accurate algorithm has
  parity correlation `≥ 7A/8 - 2ε > 0` with the readout of eq.
  `hsl:eq:readout`, so `p.cost w ≥ n/2`. Correlation is used in its
  arbitrarily-small positive form, not bounded-error parity (Lemma `hsl:lem:precision`).

Intermediate statements (per output vector; no isometry hypothesis on the
readout `e` is needed, since `Readout.Accurate` already quantifies over
Hermitian contractions of the system and `corr_of_accurate` uses only those):

* `precision_corr`: an `ε`-accurate output on bits `x` has parity correlation
  `≥ 7A/8 - 2ε ≥ 5A/8 ≥ A/2 > 0`, `A = sin(τ/n)^n` (the chain construction of Section `part:hsl` and
  proof of Lemma `hsl:lem:precision`).
* `precision_corr_pos`: summed over all `2^n` inputs, the parity correlation of an
  everywhere-accurate algorithm is strictly positive (proof of Lemma `hsl:lem:precision`, "strictly
  positive correlation with full `n`-bit parity").
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

variable {K K' G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Correlation form of the precision bound** (proof of Lemma `hsl:lem:precision`). -/
theorem precision_cost_of_corr {n : ℕ} (P : ProjFamily K' (Fin n)) (E : K →L[ℂ] K')
    (hE : E† ∘L E = 1) (O : L → (Fin n → Bool) → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hw : ∀ l, EncodedOracle.ImplementsOn (bitOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (A : K →L[ℂ] K)
    (hcorr : 0 < ∑ x, BitDegree.bitParity x * (⟪p.eval x φ₀, A (p.eval x φ₀)⟫_ℂ).re) :
    (n : ℝ) / 2 ≤ p.cost w := by
  -- Proof sketch: `obtain ⟨c, hc, hinner⟩ := Reduction.exists_boolean_program_inner E hE
  --   (fun x => P.isUnitary_phase x) hO w hw p` (`bitOracle P x = P.phase x` by
  -- `rfl`); rewrite the correlation of `c` on seed `E φ₀` with
  -- `Reduction.encodeObs E A` through `hinner x φ₀ A`; then
  -- `BitDegree.le_two_mul_count P c (E φ₀) (Reduction.encodeObs E A)` gives
  -- `n ≤ 2 c.count ≤ 2 p.cost w` (`hc`); cast.
  obtain ⟨c, hc, hinner⟩ := Reduction.exists_boolean_program_inner (Q := bitOracle P) E hE
    (fun x => P.isUnitary_phase x) hO w hw p
  have hcorr' : 0 < ∑ x, BitDegree.bitParity x *
      (⟪c.eval x (E φ₀), Reduction.encodeObs E A (c.eval x (E φ₀))⟫_ℂ).re := by
    simpa only [hinner] using hcorr
  have h1 : n ≤ 2 * c.count :=
    BitDegree.le_two_mul_count P c (E φ₀) (Reduction.encodeObs E A) hcorr'
  have h2 : (n : ℝ) ≤ 2 * (c.count : ℝ) := by exact_mod_cast h1
  have h3 : (c.count : ℝ) ≤ p.cost w := by exact_mod_cast hc
  linarith

/-- **Precision-family correlation** (the chain construction of Section `part:hsl` and proof of
Lemma `hsl:lem:precision`): for `n ≥ 1`, `0 < τ ≤ n` and `ε ≤ (τ/(2n))^n/8`, an `ε`-accurate output
of the signed scalar family on bits `x` has parity correlation at least `A/2 > 0`, `A = sin(τ/n)^n`.
No isometry hypothesis on `e` is needed.

Proof sketch: `A ≥ (τ/(2n))^n > 0` (`amp_ge`), so `ε ≤ A/8`;
`scalar_corr` gives ideal correlation `≥ 7A/8` (`chainAmp n 1 τ`
unfolds to `Real.sin (1 * τ / n) ^ n`; rewrite with `one_mul`), and
`corr_of_accurate` with `sgn = bitParity x` (`BitDegree.abs_bitParity`),
`M = scalarObs n s` (`scalarObs_contraction`) gives `≥ 7A/8 - 2ε ≥ A/2`. -/
theorem precision_corr {n s : ℕ} {τ ε : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hε : ε ≤ (τ / (2 * n)) ^ n / 8) (e : K →L[ℂ] SysGarb (ScalarIndex n s) G)
    (x : Fin n → Bool) (Φ : K)
    (hacc : Accurate e Φ (evolve (scalarHam n s τ x) τ (scalarInput n s)) ε) :
    Real.sin (τ / n) ^ n / 2 ≤
      BitDegree.bitParity x * (⟪Φ, outObs e (scalarObs n s) Φ⟫_ℂ).re := by
  have hA : (τ / (2 * n)) ^ n ≤ Real.sin (τ / n) ^ n := amp_ge hn hτ hτn
  have hpos : 0 < (τ / (2 * n)) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hchain : chainAmp n 1 τ = Real.sin (τ / n) ^ n := by
    simp only [chainAmp, one_mul]
  have hA0 : 0 < chainAmp n 1 τ := by rw [hchain]; linarith
  have hideal := scalar_corr (s := s) hn hτ hA0 x
  rw [hchain] at hideal
  have h := corr_of_accurate e Φ _ ε hacc (scalarObs n s) (scalarObs_contraction n s).1
    (scalarObs_contraction n s).2 (BitDegree.abs_bitParity x).le hideal
  linarith

/-- **Positive parity correlation** (proof of Lemma `hsl:lem:precision`): if every output `Φ x` is
`ε`-accurate for its input, the summed parity correlation of the readout
`outObs e (scalarObs n s)` is strictly positive (each term is
`≥ sin(τ/n)^n/2 > 0` by `precision_corr` and `amp_ge`, and the input set is
nonempty). -/
theorem precision_corr_pos {n s : ℕ} {τ ε : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hε : ε ≤ (τ / (2 * n)) ^ n / 8) (e : K →L[ℂ] SysGarb (ScalarIndex n s) G)
    (Φ : (Fin n → Bool) → K)
    (hacc : ∀ x, Accurate e (Φ x) (evolve (scalarHam n s τ x) τ (scalarInput n s)) ε) :
    0 < ∑ x, BitDegree.bitParity x * (⟪Φ x, outObs e (scalarObs n s) (Φ x)⟫_ℂ).re := by
  have hA : (τ / (2 * n)) ^ n ≤ Real.sin (τ / n) ^ n := amp_ge hn hτ hτn
  have hpos : 0 < (τ / (2 * n)) ^ n := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  refine Finset.sum_pos (fun x _ => ?_) Finset.univ_nonempty
  have h := precision_corr hn hτ hτn hε e x (Φ x) (hacc x)
  linarith

/-- **Lemma `hsl:lem:precision`, general form** (Lemma `hsl:lem:precision`). Any
algorithm over a 2-query-implementable labelled family that is `ε`-accurate
on every input of the signed scalar family, with `0 < τ ≤ n` and
`ε ≤ (τ/(2n))^n/8` (eq. `hsl:eq:mixepsilon`), has Boolean cost
`p.cost w ≥ n/2`. -/
theorem precision_general {n s : ℕ} {τ ε : ℝ} (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (P : ProjFamily K' (Fin n)) (E : K →L[ℂ] K') (hE : E† ∘L E = 1)
    (O : L → (Fin n → Bool) → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hw : ∀ l, EncodedOracle.ImplementsOn (bitOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K)
    (e : K →L[ℂ] SysGarb (ScalarIndex n s) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀) (evolve (scalarHam n s τ x) τ (scalarInput n s)) ε) :
    (n : ℝ) / 2 ≤ p.cost w := by
  -- Proof sketch: `precision_cost_of_corr P E hE O hO w hw p φ₀ (outObs e (scalarObs n s))
  --   (precision_corr_pos hn hτ hτn hε e (fun x => p.eval x φ₀) hacc)`.
  exact precision_cost_of_corr P E hE O hO w hw p φ₀ (outObs e (scalarObs n s))
    (precision_corr_pos hn hτ hτn hε e (fun x => p.eval x φ₀) hacc)

end

end SparseLowerBounds.Hamiltonian
end
