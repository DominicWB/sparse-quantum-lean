import QLSHoeffding.Hoeffding
import ChebyshevLinearSystemFinite.Estimator

/-!
# The norm estimator with any repetition schedule meeting its tail budget

The released estimator analyses (`SparseLinearSystems.Protocol.Estimator.algorithm_bad_le`,
`ChebyshevLinearSystemFinite.algorithm_bad_le_tol`) assume the repetition counts
`n_j ≥ 4 log(2/ζ_j)/t²` of the elementary binomial tail bound. They use these counts only
through the bound `ζ_j` on the binomial mass of the inaccurate counts. Here that bound is the
hypothesis (`TailOK n t ζ`), so the same classical protocol (`Estimator.algorithm`) is analysed
for every repetition schedule meeting it:

* `tailOK_hoeffding`: Hoeffding's count `n ≥ log(2/ζ)/(2t²)` (equation `qls:eq:hoeffding`);
* `tailOK_released`: the released count `n ≥ 4 log(2/ζ)/t²`.

`count_step_tail`, `candidates_le_tail`, `stages_le_tail` and `algorithm_bad_le_tail` are the
released stage, stages and union-bound analysis with the two-sided tolerance
`1/(2(1+q²)) - 10⁻⁴ ≤ p ≤ 1/(1+q²) + 10⁻⁴` of equation `qls:eq:bernoulli` (which contains the
exact-gate case), with `TailOK` in place of the count.
-/

set_option autoImplicit false

namespace QLSHoeffding

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit SparseLinearSystems BinomialTail
  Protocol Estimator
open ChebyshevLinearSystemFinite (reject_inv_tol last_accepts_tol)
open scoped InnerProduct

/-! ### The tail budget of one counted test -/

/-- **The tail budget**: the inaccurate counts (`|c - n p| ≥ n t`) have binomial mass at most `ζ`
for every success probability `p`. -/
def TailOK (n : ℕ) (t ζ : ℝ) : Prop :=
  ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    ∑ c ∈ Finset.range (n + 1), (if (n : ℝ) * t ≤ |(c : ℝ) - n * p| then binom n p c else 0) ≤ ζ

/-- **Hoeffding's count meets the tail budget**: `n ≥ log(2/ζ)/(2t²)`. -/
theorem tailOK_hoeffding {n : ℕ} {t ζ : ℝ} (ht : 0 < t) (hζ : 0 < ζ)
    (hn : Real.log (2 / ζ) / (2 * t ^ 2) ≤ n) : TailOK n t ζ :=
  fun _ hp0 hp1 => two_sided_le_of_count_sharp n hp0 hp1 ht hζ hn

/-- The released count `n ≥ 4 log(2/ζ)/t²` meets the tail budget. -/
theorem tailOK_released {n : ℕ} {t ζ : ℝ} (ht0 : 0 < t) (ht2 : t ≤ 2) (hζ : 0 < ζ)
    (hn : 4 * Real.log (2 / ζ) / t ^ 2 ≤ n) : TailOK n t ζ :=
  fun _ hp0 hp1 => BinomialTail.two_sided_le_of_count n hp0 hp1 ht0 ht2 hζ hn

/-- **One counted test with a tail budget**: a `[0,1]`-valued continuation that is at most `β`
on accurate counts has expectation at most `β + ζ`. -/
theorem count_step_tail (V : ℕ → ℝ) (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t ζ : ℝ)
    (htail : TailOK n t ζ) (hV1 : ∀ c, V c ≤ 1) (β : ℝ) (hβ : 0 ≤ β)
    (hacc : ∀ c, c ≤ n → |(c : ℝ) - n * p| < n * t → V c ≤ β) :
    ∑ c ∈ Finset.range (n + 1), binom n p c * V c ≤ β + ζ := by
  have htail' := htail p hp0 hp1
  have hterm : ∀ c ∈ Finset.range (n + 1), binom n p c * V c ≤
      β * binom n p c + (if (n : ℝ) * t ≤ |(c : ℝ) - n * p| then binom n p c else 0) := by
    intro c hc
    have hb := binom_nonneg n hp0 hp1 c
    have hcn : c ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
    split_ifs with h
    · nlinarith [hV1 c]
    · have := hacc c hcn (lt_of_not_ge h)
      nlinarith
  calc ∑ c ∈ Finset.range (n + 1), binom n p c * V c
      ≤ ∑ c ∈ Finset.range (n + 1), (β * binom n p c +
          (if (n : ℝ) * t ≤ |(c : ℝ) - n * p| then binom n p c else 0)) :=
        Finset.sum_le_sum hterm
    _ = β * ∑ c ∈ Finset.range (n + 1), binom n p c +
          ∑ c ∈ Finset.range (n + 1),
            (if (n : ℝ) * t ≤ |(c : ℝ) - n * p| then binom n p c else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ β * 1 + ζ := by rw [sum_binom]; linarith
    _ = β + ζ := by ring

/-! ### The accuracy analysis -/

section Analysis

variable {K E F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

variable (x : X) (test : ℕ → ℝ → TestRun O F) (g : ODERepeatProtocol.Protocol O E → ℝ)

/-- **One stage with a tail budget and the two-sided tolerance**: with the invariant
`27 r² ≤ 92 ρ²` and `ρ ≤ 2^k r`, the candidates `r, …, 2^k r` lead to a good estimate in
`[ρ, 4ρ]`, except with probability `(k+1) ζ`. -/
theorem candidates_le_tail (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (j n : ℕ) (κ ρ ζ β : ℝ)
    (hρ1 : 1 ≤ ρ) (hρκ : ρ ≤ κ) (hζ : 0 < ζ) (hβ : 0 ≤ β) (htail : TailOK n tAcc ζ)
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
    have hstep := count_step_tail (fun c => (if 22 * n ≤ 100 * c then cont (clip κ (2 * r))
        else candidates test j n κ cont 0 (2 * r)).expect ℝ g x) n ((test j r).probability x)
      ((test j r).probability_nonneg x) ((test j r).probability_le_one x (htU r)) tAcc ζ htail
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
    have hstep := count_step_tail (fun c => (if 22 * n ≤ 100 * c then cont (clip κ (2 * r))
        else candidates test j n κ cont (k + 1) (2 * r)).expect ℝ g x) n
      ((test j r).probability x)
      ((test j r).probability_nonneg x) ((test j r).probability_le_one x (htU r)) tAcc ζ htail
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

/-- **All stages with tail budgets and the two-sided tolerance**: from a good previous
estimate, the remaining stages reach a leaf with `g = 0` except with probability `Σ 5 ζ_j`. -/
theorem stages_le_tail (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) (ρ ζ : ℕ → ℝ)
    (hρ : ∀ j, j ≤ m → 1 ≤ ρ j ∧ ρ j ≤ κ)
    (hlad : ∀ j, 1 ≤ j → j ≤ m → ρ (j - 1) ≤ ρ j ∧ ρ j ≤ 2 * ρ (j - 1))
    (hζ : ∀ j, 0 < ζ j) (htail : ∀ j, TailOK (reps j) tAcc (ζ j))
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
    have hstage := candidates_le_tail x test g hg0 hg1 j (reps j) κ (ρ j) (ζ j)
      (∑ q ∈ Finset.range i, 5 * ζ (m - q)) hρj1 hρjκ (hζ j) hβ (htail j) (htU j)
      (fun r hr => hp j r hj1 hjm hr) (stages test leaf reps m κ i)
      (stages_runsUnitary x test leaf reps m κ htU i)
      (fun r hr1 hr2 => ih (by omega) r hr1 hr2)
      4 (rhat / 8) (by linarith [(hρ (j - 1) (by omega)).1]) (by nlinarith)
      (by norm_num; linarith)
    show (candidates test j (reps j) κ (stages test leaf reps m κ i) 5 (rhat / 8)).expect ℝ g x ≤ _
    rw [Finset.sum_range_succ]
    push_cast at hstage
    linarith

/-- **The estimator analysis with tail budgets** (equations `qls:eq:bernoulli`,
`qls:eq:estimatebound` and the union bound): for every repetition schedule whose counts meet the
tail budgets `ζ_j` (`TailOK`), any leaf functional with values in `[0, 1]` that vanishes at the
good leaves `ρ_m ≤ r ≤ 4 ρ_m` has expectation at most `Σ_j 5 ζ_j`. -/
theorem algorithm_bad_le_tail (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) (ρ ζ : ℕ → ℝ)
    (hρ0 : ρ 0 = 1) (hρ : ∀ j, j ≤ m → 1 ≤ ρ j ∧ ρ j ≤ κ)
    (hlad : ∀ j, 1 ≤ j → j ≤ m → ρ (j - 1) ≤ ρ j ∧ ρ j ≤ 2 * ρ (j - 1))
    (hζ : ∀ j, 0 < ζ j) (htail : ∀ j, TailOK (reps j) tAcc (ζ j))
    (htU : ∀ j r, IsUnitary ((test j r).circuit.eval x))
    (hp : ∀ j r, 1 ≤ j → j ≤ m → 1 / 8 ≤ r →
      1 / (2 * (1 + (ρ j / r) ^ 2)) - 1 / 10000 ≤ (test j r).probability x ∧
        (test j r).probability x ≤ 1 / (1 + (ρ j / r) ^ 2) + 1 / 10000)
    (hgood : ∀ r, ρ m ≤ r → r ≤ 4 * ρ m → g (leaf r) = 0) :
    (algorithm test leaf reps m κ).expect ℝ g x ≤ ∑ q ∈ Finset.range m, 5 * ζ (m - q) := by
  apply stages_le_tail x test g hg0 hg1 leaf reps m κ ρ ζ hρ hlad hζ htail htU hp hgood m le_rfl 1
  · rw [Nat.sub_self, hρ0]
  · rw [Nat.sub_self, hρ0]; norm_num

end Analysis

end

end QLSHoeffding
