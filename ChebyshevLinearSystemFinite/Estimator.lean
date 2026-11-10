import SparseLinearSystems.Protocol.Estimator

set_option autoImplicit false

/-!
# The norm estimator with the two-sided test tolerance of equation `qls:eq:bernoulli`

With approximate known gates a test probability `p_F` is no longer bounded below by the exact
probability `p_ξ(r)` of the eigenvalue-one projection: the manuscript's bound is two-sided,
`|p_F - p_ξ(r)| ≤ δ₀² + 2e ≤ 10⁻⁴` (equation `qls:eq:bernoulli`). With equation
`qls:eq:probability` this gives

`1/(2(1 + q²)) - 10⁻⁴ ≤ p_F ≤ 1/(1 + q²) + 10⁻⁴`,   `q = r_ξ / r`,

whereas the released analysis `Estimator.algorithm_bad_le` assumes the lower bound without the
`10⁻⁴` (exact gates). The threshold arithmetic still closes with the manuscript's margins:

* `reject_inv_tol`: an accurate rejection (`p̂ < 0.22`, `|p̂ - p_F| < 0.0099`) gives
  `p_F < 0.2299`, so `1/(2(1 + q²)) < 0.2299 + 0.0001 = 0.23` and `r < 2 √(23/27) r_ξ`;
* `last_accepts_tol`: at `r ≥ r_ξ`, `p_F ≥ 1/4 - 10⁻⁴`, and an accurate count is at least
  `0.2499 - 0.0099 = 0.24 ≥ 0.22`;
* acceptances use only the upper bound (released `Estimator.accept_good`).

`candidates_le_tol`, `stages_le_tol` and `algorithm_bad_le_tol` are the released stage, stages
and union-bound analysis (`Estimator.candidates_le`, `Estimator.stages_le`,
`Estimator.algorithm_bad_le`) with this two-sided hypothesis; the classical protocol
(`Estimator.algorithm`) is unchanged.
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit SparseLinearSystems BinomialTail
  Protocol Estimator
open scoped InnerProduct

variable {K E F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

/-! ### Threshold arithmetic with the two-sided tolerance -/

/-- An accurate rejection certifies the invariant `27 (2r)² ≤ 92 ρ²` for the next candidate,
when the test probability is only known to satisfy `1/(2(1+q²)) - 10⁻⁴ ≤ p`. -/
theorem reject_inv_tol (ρ r p : ℝ) (n c : ℕ) (hρ : 0 < ρ) (hr : 0 < r)
    (hpl : 1 / (2 * (1 + (ρ / r) ^ 2)) - 1 / 10000 ≤ p) (hacc : |(c : ℝ) - n * p| < n * tAcc)
    (hR : ¬ 22 * n ≤ 100 * c) : 27 * (2 * r) ^ 2 ≤ 92 * ρ ^ 2 := by
  have hn := n_pos_of_accurate n c p hacc
  have hR' : (100 : ℝ) * c < 22 * n := by
    have : 100 * c < 22 * n := Nat.lt_of_not_le hR
    exact_mod_cast this
  have hc := (abs_lt.mp hacc).1
  unfold tAcc at hc
  have hp : p < 2299 / 10000 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hQ : 0 < 1 + (ρ / r) ^ 2 := by positivity
  have h1 : 1 / (2 * (1 + (ρ / r) ^ 2)) < 23 / 100 := by linarith
  rw [div_lt_iff₀ (by positivity)] at h1
  have hq : 27 / 23 < (ρ / r) ^ 2 := by nlinarith
  rw [div_pow, lt_div_iff₀ (by positivity)] at hq
  nlinarith

/-- At a candidate `r ≥ ρ` an accurate count always accepts, when the test probability is only
known to satisfy `1/(2(1+q²)) - 10⁻⁴ ≤ p`. -/
theorem last_accepts_tol (ρ r p : ℝ) (n c : ℕ) (hρ : 0 < ρ) (hr : 0 < r) (hρr : ρ ≤ r)
    (hpl : 1 / (2 * (1 + (ρ / r) ^ 2)) - 1 / 10000 ≤ p) (hacc : |(c : ℝ) - n * p| < n * tAcc) :
    22 * n ≤ 100 * c := by
  have hn := n_pos_of_accurate n c p hacc
  have hq : (ρ / r) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  have hp : 1 / 4 - 1 / 10000 ≤ p := by
    refine le_trans ?_ hpl
    have : 1 / 4 ≤ 1 / (2 * (1 + (ρ / r) ^ 2)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    linarith
  have hc := (abs_lt.mp hacc).1
  unfold tAcc at hc
  have : (22 : ℝ) * n ≤ 100 * c := by nlinarith
  exact_mod_cast this

/-! ### The accuracy analysis -/

section Analysis

variable (x : X) (test : ℕ → ℝ → TestRun O F) (g : ODERepeatProtocol.Protocol O E → ℝ)

/-- **One stage with the two-sided tolerance** (the released `Estimator.candidates_le` with
`1/(2(1+q²)) - 10⁻⁴ ≤ p`): with the invariant `27 r² ≤ 92 ρ²` and `ρ ≤ 2^k r`, the
candidates `r, …, 2^k r` lead to a good estimate in `[ρ, 4ρ]`, except with probability
`(k+1) ζ`. -/
theorem candidates_le_tol (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (j n : ℕ) (κ ρ ζ β : ℝ)
    (hρ1 : 1 ≤ ρ) (hρκ : ρ ≤ κ) (hζ : 0 < ζ) (hβ : 0 ≤ β)
    (hn : 4 * Real.log (2 / ζ) / tAcc ^ 2 ≤ n)
    (htU : ∀ r, IsUnitary ((test j r).circuit.eval x))
    (hp : ∀ r, 1 / 8 ≤ r →
      1 / (2 * (1 + (ρ / r) ^ 2)) - 1 / 10000 ≤ (test j r).probability x ∧
        (test j r).probability x ≤ 1 / (1 + (ρ / r) ^ 2) + 1 / 10000)
    (cont : ℝ → Protocol.Tree O F E) (hcU : ∀ r, (cont r).RunsUnitary x)
    (hcont : ∀ r, ρ ≤ r → r ≤ 4 * ρ → (cont r).expect ℝ g x ≤ β) :
    ∀ k r, 1 / 8 ≤ r → 27 * r ^ 2 ≤ 92 * ρ ^ 2 → ρ ≤ 2 ^ k * r →
      (candidates test j n κ cont (k + 1) r).expect ℝ g x ≤ β + (k + 1) * ζ := by
  have hρ0 : 0 < ρ := by linarith
  have hU : ∀ k r, (candidates test j n κ cont k r).RunsUnitary x :=
    candidates_runsUnitary x test j n κ cont htU hcU
  intro k
  induction k with
  | zero =>
    intro r hr8 hinv hlast
    have hr0 : 0 < r := by linarith
    rw [pow_zero, one_mul] at hlast
    obtain ⟨hpl, hpu⟩ := hp r hr8
    rw [candidates, Tree.expect_countRuns]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, zero_add]
    have hstep := count_step (fun c => (if 22 * n ≤ 100 * c then cont (clip κ (2 * r))
        else candidates test j n κ cont 0 (2 * r)).expect ℝ g x) n ((test j r).probability x)
      ((test j r).probability_nonneg x) ((test j r).probability_le_one x (htU r)) tAcc ζ
      (by unfold tAcc; norm_num) (by unfold tAcc; norm_num) hζ hn
      (fun c => (expect_unit x g hg0 hg1 _ (by split_ifs <;> [exact hcU _; exact hU 0 _])).2)
      β hβ (fun c hcn hacc => by
        have hA := last_accepts_tol ρ r _ n c hρ0 hr0 hlast hpl hacc
        rw [if_pos hA]
        obtain ⟨hg1', hg2'⟩ := accept_good ρ r _ n c hρ0 hr0 hinv hpu hacc hA
        rw [clip_of_mem κ (2 * r) (by linarith) (by linarith)]
        exact hcont _ hg1' hg2')
    push_cast
    linarith
  | succ k ih =>
    intro r hr8 hinv hlast
    have hr0 : 0 < r := by linarith
    obtain ⟨hpl, hpu⟩ := hp r hr8
    rw [candidates, Tree.expect_countRuns]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul, zero_add]
    have hkζ : 0 ≤ (k + 1 : ℝ) * ζ := by positivity
    have hstep := count_step (fun c => (if 22 * n ≤ 100 * c then cont (clip κ (2 * r))
        else candidates test j n κ cont (k + 1) (2 * r)).expect ℝ g x) n
      ((test j r).probability x)
      ((test j r).probability_nonneg x) ((test j r).probability_le_one x (htU r)) tAcc ζ
      (by unfold tAcc; norm_num) (by unfold tAcc; norm_num) hζ hn
      (fun c => (expect_unit x g hg0 hg1 _ (by split_ifs <;> [exact hcU _; exact hU _ _])).2)
      (β + (k + 1) * ζ) (by linarith) (fun c hcn hacc => by
        by_cases hA : 22 * n ≤ 100 * c
        · rw [if_pos hA]
          obtain ⟨hg1', hg2'⟩ := accept_good ρ r _ n c hρ0 hr0 hinv hpu hacc hA
          rw [clip_of_mem κ (2 * r) (by linarith) (by linarith)]
          exact (hcont _ hg1' hg2').trans (by linarith)
        · rw [if_neg hA]
          have hinv' := reject_inv_tol ρ r _ n c hρ0 hr0 hpl hacc hA
          have hlast' : ρ ≤ 2 ^ k * (2 * r) := by
            rw [pow_succ] at hlast
            linarith
          exact ih (2 * r) (by linarith) hinv' hlast')
    push_cast at hstep ⊢
    linarith

/-- **All stages with the two-sided tolerance** (the released `Estimator.stages_le`): from a
good previous estimate, the remaining stages reach a leaf with `g = 0` except with probability
`Σ 5 ζ_j`. -/
theorem stages_le_tol (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) (ρ ζ : ℕ → ℝ)
    (hρ : ∀ j, j ≤ m → 1 ≤ ρ j ∧ ρ j ≤ κ)
    (hlad : ∀ j, 1 ≤ j → j ≤ m → ρ (j - 1) ≤ ρ j ∧ ρ j ≤ 2 * ρ (j - 1))
    (hζ : ∀ j, 0 < ζ j) (hn : ∀ j, 4 * Real.log (2 / ζ j) / tAcc ^ 2 ≤ reps j)
    (htU : ∀ j r, IsUnitary ((test j r).circuit.eval x))
    (hp : ∀ j r, 1 ≤ j → j ≤ m → 1 / 8 ≤ r →
      1 / (2 * (1 + (ρ j / r) ^ 2)) - 1 / 10000 ≤ (test j r).probability x ∧
        (test j r).probability x ≤ 1 / (1 + (ρ j / r) ^ 2) + 1 / 10000)
    (hgood : ∀ r, ρ m ≤ r → r ≤ 4 * ρ m → g (leaf r) = 0) :
    ∀ i, i ≤ m → ∀ rhat, ρ (m - i) ≤ rhat → rhat ≤ 4 * ρ (m - i) →
      (stages test leaf reps m κ i rhat).expect ℝ g x ≤
        ∑ q ∈ Finset.range i, 5 * ζ (m - q) := by
  intro i
  induction i with
  | zero =>
    intro _ rhat h1 h2
    rw [Nat.sub_zero] at h1 h2
    show g (leaf rhat) ≤ _
    rw [hgood rhat h1 h2]
    simp
  | succ i ih =>
    intro hi rhat h1 h2
    set j := m - i with hj
    have hj1 : 1 ≤ j := by omega
    have hjm : j ≤ m := by omega
    have hjprev : m - (i + 1) = j - 1 := by omega
    rw [hjprev] at h1 h2
    obtain ⟨hρj1, hρjκ⟩ := hρ j hjm
    obtain ⟨hlad1, hlad2⟩ := hlad j hj1 hjm
    have hβ : 0 ≤ ∑ q ∈ Finset.range i, 5 * ζ (m - q) :=
      Finset.sum_nonneg fun q _ => by have := hζ (m - q); positivity
    have hstage := candidates_le_tol x test g hg0 hg1 j (reps j) κ (ρ j) (ζ j)
      (∑ q ∈ Finset.range i, 5 * ζ (m - q)) hρj1 hρjκ (hζ j) hβ (hn j) (htU j)
      (fun r hr => hp j r hj1 hjm hr) (stages test leaf reps m κ i)
      (stages_runsUnitary x test leaf reps m κ htU i)
      (fun r hr1 hr2 => ih (by omega) r hr1 hr2)
      4 (rhat / 8) (by linarith [(hρ (j - 1) (by omega)).1]) (by nlinarith)
      (by norm_num; linarith)
    show (candidates test j (reps j) κ (stages test leaf reps m κ i) 5 (rhat / 8)).expect ℝ g x ≤ _
    rw [Finset.sum_range_succ]
    push_cast at hstage
    linarith

/-- **The estimator analysis with the two-sided tolerance** (equations `qls:eq:bernoulli`,
`qls:eq:estimatebound` and the union bound; the released `Estimator.algorithm_bad_le` with
`1/(2(1+q²)) - 10⁻⁴ ≤ p`): any leaf functional with values in `[0, 1]` that vanishes at the
good leaves `ρ_m ≤ r ≤ 4 ρ_m` has expectation at most `Σ_j 5 ζ_j`. -/
theorem algorithm_bad_le_tol (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) (ρ ζ : ℕ → ℝ)
    (hρ0 : ρ 0 = 1) (hρ : ∀ j, j ≤ m → 1 ≤ ρ j ∧ ρ j ≤ κ)
    (hlad : ∀ j, 1 ≤ j → j ≤ m → ρ (j - 1) ≤ ρ j ∧ ρ j ≤ 2 * ρ (j - 1))
    (hζ : ∀ j, 0 < ζ j) (hn : ∀ j, 4 * Real.log (2 / ζ j) / tAcc ^ 2 ≤ reps j)
    (htU : ∀ j r, IsUnitary ((test j r).circuit.eval x))
    (hp : ∀ j r, 1 ≤ j → j ≤ m → 1 / 8 ≤ r →
      1 / (2 * (1 + (ρ j / r) ^ 2)) - 1 / 10000 ≤ (test j r).probability x ∧
        (test j r).probability x ≤ 1 / (1 + (ρ j / r) ^ 2) + 1 / 10000)
    (hgood : ∀ r, ρ m ≤ r → r ≤ 4 * ρ m → g (leaf r) = 0) :
    (algorithm test leaf reps m κ).expect ℝ g x ≤ ∑ q ∈ Finset.range m, 5 * ζ (m - q) := by
  apply stages_le_tol x test g hg0 hg1 leaf reps m κ ρ ζ hρ hlad hζ hn htU hp hgood m le_rfl 1
  · rw [Nat.sub_self, hρ0]
  · rw [Nat.sub_self, hρ0]; norm_num

end Analysis

end

end ChebyshevLinearSystemFinite
