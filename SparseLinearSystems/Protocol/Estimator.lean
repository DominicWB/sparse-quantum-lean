import SparseLinearSystems.Protocol.Tree

/-!
# The geometric solution-norm estimator (Section `qls`, norm estimation)

Stages `j = 1, …, m`, previous estimate `r̂`: the candidates
`r = r̂ 2^{i-3}`, `i = 0, …, 4`, are tested in increasing order, each with
`n_j` fresh runs; the first candidate with at least `0.22 n_j` successes is
accepted and the new estimate is `2 r` (`candidates`).  Estimates are clipped
to `[1, 4κ]`; if no candidate is accepted the clipped value `2 r` of the last
candidate is used.  After stage `m` the final leaf is run (`stages`).

Abstract analysis (`algorithm_bad_le`): suppose the true values `ρ_j` satisfy
the ladder `ρ_0 = 1`, `ρ_{j-1} ≤ ρ_j ≤ 2 ρ_{j-1}`, and the test probabilities obey
`1/(2(1+q²)) ≤ p_j(r) ≤ 1/(1+q²) + 10⁻⁴` with `q = ρ_j/r` for every `r ≥ 1/8`.
If `n_j ≥ 4 log(2/ζ_j)/t²` with `t = 0.0099`, then any leaf functional with
values in `[0, 1]` that vanishes at the good leaves `ρ_m ≤ r ≤ 4 ρ_m` has
expectation at most `Σ_j 5 ζ_j`: on the event that all performed tests are
accurate the estimate stays good (equation `qls:eq:estimatebound`), and the
union bound holds along the adaptive transcript.
-/

namespace SparseLinearSystems.Protocol

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit BinomialTail
open scoped InnerProduct

variable {K E F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

namespace Estimator

/-- Clipping to `[1, 4κ]`. -/
def clip (κ r : ℝ) : ℝ := min (max r 1) (4 * κ)

theorem clip_of_mem (κ r : ℝ) (h1 : 1 ≤ r) (h2 : r ≤ 4 * κ) : clip κ r = r := by
  unfold clip
  rw [max_eq_left h1, min_eq_left h2]

theorem one_le_clip (κ r : ℝ) (hκ : 1 ≤ κ) : 1 ≤ clip κ r := by
  unfold clip
  exact le_min (le_max_right _ _) (by linarith)

theorem clip_le (κ r : ℝ) : clip κ r ≤ 4 * κ := min_le_right _ _

/-- The candidates of one stage (`k` remaining, current candidate `r`). -/
def candidates (test : ℕ → ℝ → TestRun O F) (j n : ℕ) (κ : ℝ) (cont : ℝ → Tree O F E) :
    ℕ → ℝ → Tree O F E
  | 0, r => cont (clip κ r)
  | k + 1, r => Tree.countRuns (test j r)
      (fun c => if 22 * n ≤ 100 * c then cont (clip κ (2 * r))
        else candidates test j n κ cont k (2 * r)) n 0

/-- Stages `m - i + 1, …, m` (`i` remaining), then the final leaf. -/
def stages (test : ℕ → ℝ → TestRun O F) (leaf : ℝ → ODERepeatProtocol.Protocol O E)
    (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) : ℕ → ℝ → Tree O F E
  | 0, rhat => .final (leaf rhat)
  | i + 1, rhat => candidates test (m - i) (reps (m - i)) κ (stages test leaf reps m κ i) 5 (rhat / 8)

/-- **The algorithm**: the norm estimator from `r̂_0 = 1`, then the final leaf. -/
def algorithm (test : ℕ → ℝ → TestRun O F) (leaf : ℝ → ODERepeatProtocol.Protocol O E)
    (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) : Tree O F E :=
  stages test leaf reps m κ m 1

/-! ### Structural facts -/

theorem candidates_allLeaves (test : ℕ → ℝ → TestRun O F) (j n : ℕ) (κ : ℝ)
    (cont : ℝ → Tree O F E) (Q : ODERepeatProtocol.Protocol O E → Prop)
    (hc : ∀ r, (cont r).AllLeaves Q) : ∀ k r, (candidates test j n κ cont k r).AllLeaves Q
  | 0, r => hc _
  | k + 1, r => Tree.allLeaves_countRuns Q _ _ (fun c => by
      split_ifs
      · exact hc _
      · exact candidates_allLeaves test j n κ cont Q hc k (2 * r)) n 0

theorem stages_allLeaves (test : ℕ → ℝ → TestRun O F) (leaf : ℝ → ODERepeatProtocol.Protocol O E)
    (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) (Q : ODERepeatProtocol.Protocol O E → Prop)
    (hl : ∀ r, Q (leaf r)) : ∀ i r, (stages test leaf reps m κ i r).AllLeaves Q
  | 0, r => hl r
  | i + 1, _ => candidates_allLeaves test _ _ κ _ Q (stages_allLeaves test leaf reps m κ Q hl i) 5 _

theorem candidates_runsUnitary (x : X) (test : ℕ → ℝ → TestRun O F) (j n : ℕ) (κ : ℝ)
    (cont : ℝ → Tree O F E) (ht : ∀ r, IsUnitary ((test j r).circuit.eval x))
    (hc : ∀ r, (cont r).RunsUnitary x) : ∀ k r, (candidates test j n κ cont k r).RunsUnitary x
  | 0, r => hc _
  | k + 1, r => Tree.runsUnitary_countRuns x _ (ht r) _ (fun c => by
      split_ifs
      · exact hc _
      · exact candidates_runsUnitary x test j n κ cont ht hc k (2 * r)) n 0

theorem stages_runsUnitary (x : X) (test : ℕ → ℝ → TestRun O F)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ)
    (ht : ∀ j r, IsUnitary ((test j r).circuit.eval x)) :
    ∀ i r, (stages test leaf reps m κ i r).RunsUnitary x
  | 0, _ => trivial
  | i + 1, _ => candidates_runsUnitary x test _ _ κ _ (ht _)
      (stages_runsUnitary x test leaf reps m κ ht i) 5 _

/-! ### Worst-case cost -/

theorem candidates_cost (w : L → ℕ) (test : ℕ → ℝ → TestRun O F) (j n : ℕ) (κ : ℝ)
    (cont : ℝ → Tree O F E) (C B : ℕ) (ht : ∀ r, (test j r).circuit.cost w ≤ C)
    (hc : ∀ r, (cont r).worstCost w ≤ B) :
    ∀ k r, (candidates test j n κ cont k r).worstCost w ≤ k * (n * C) + B
  | 0, r => by rw [candidates, zero_mul, zero_add]; exact hc _
  | k + 1, r => by
      rw [candidates]
      refine (Tree.worstCost_countRuns w _ _ (k * (n * C) + B) (fun c => ?_) n 0).trans ?_
      · split_ifs
        · exact (hc _).trans (Nat.le_add_left _ _)
        · exact candidates_cost w test j n κ cont C B ht hc k (2 * r)
      · have := Nat.mul_le_mul_left n (ht r)
        rw [Nat.succ_mul]
        omega

theorem stages_cost (w : L → ℕ) (test : ℕ → ℝ → TestRun O F)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ)
    (C : ℕ → ℕ) (ht : ∀ j r, (test j r).circuit.cost w ≤ C j) (B : ℕ)
    (hl : ∀ r, (leaf r).worstCost w ≤ B) :
    ∀ i r, (stages test leaf reps m κ i r).worstCost w ≤
      (∑ q ∈ Finset.range i, 5 * (reps (m - q) * C (m - q))) + B
  | 0, r => by simpa [stages, Tree.worstCost] using hl r
  | i + 1, r => by
      refine (candidates_cost w test (m - i) (reps (m - i)) κ _ (C (m - i))
        ((∑ q ∈ Finset.range i, 5 * (reps (m - q) * C (m - q))) + B) (ht _)
        (stages_cost w test leaf reps m κ C ht B hl i) 5 _).trans ?_
      rw [Finset.sum_range_succ]
      omega

/-! ### One counted test -/

/-- Accurate counts concentrate: the binomial mass of inaccurate counts is at
most `ζ`, so a `[0,1]`-valued continuation that is at most `β` on accurate counts
has expectation at most `β + ζ`. -/
theorem count_step (V : ℕ → ℝ) (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t ζ : ℝ)
    (ht0 : 0 < t) (ht2 : t ≤ 2) (hζ : 0 < ζ) (hn : 4 * Real.log (2 / ζ) / t ^ 2 ≤ n)
    (hV1 : ∀ c, V c ≤ 1) (β : ℝ) (hβ : 0 ≤ β)
    (hacc : ∀ c, c ≤ n → |(c : ℝ) - n * p| < n * t → V c ≤ β) :
    ∑ c ∈ Finset.range (n + 1), binom n p c * V c ≤ β + ζ := by
  have htail := BinomialTail.two_sided_le_of_count n hp0 hp1 ht0 ht2 hζ hn
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

variable (x : X) (test : ℕ → ℝ → TestRun O F) (g : ODERepeatProtocol.Protocol O E → ℝ)

theorem expect_unit (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (T : Tree O F E)
    (hU : T.RunsUnitary x) : 0 ≤ T.expect ℝ g x ∧ T.expect ℝ g x ≤ 1 := by
  constructor
  · have h := Tree.expect_mono (fun _ => (0 : ℝ)) g x T hU
      (Tree.AllLeaves.imp (fun p _ => hg0 p) T (Tree.allLeaves_true T))
    rwa [Tree.expect_const] at h
  · have h := Tree.expect_mono g (fun _ => (1 : ℝ)) x T hU
      (Tree.AllLeaves.imp (fun p _ => hg1 p) T (Tree.allLeaves_true T))
    rwa [Tree.expect_const] at h

/-- The accuracy margin `t = 0.0099`. -/
def tAcc : ℝ := 99 / 10000

/-! Elementary threshold arithmetic (`q = ρ / r`). -/

theorem n_pos_of_accurate (n c : ℕ) (p : ℝ) (hacc : |(c : ℝ) - n * p| < n * tAcc) :
    (0 : ℝ) < n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h] at hacc; simp at hacc; linarith [abs_nonneg (c : ℝ)]
  · exact_mod_cast h

/-- An accurate acceptance certifies `ρ < 2 r ≤ 4 ρ`. -/
theorem accept_good (ρ r p : ℝ) (n c : ℕ) (hρ : 0 < ρ) (hr : 0 < r)
    (hinv : 27 * r ^ 2 ≤ 92 * ρ ^ 2) (hpu : p ≤ 1 / (1 + (ρ / r) ^ 2) + 1 / 10000)
    (hacc : |(c : ℝ) - n * p| < n * tAcc) (hA : 22 * n ≤ 100 * c) :
    ρ ≤ 2 * r ∧ 2 * r ≤ 4 * ρ := by
  have hn := n_pos_of_accurate n c p hacc
  have hA' : (22 : ℝ) * n ≤ 100 * c := by exact_mod_cast hA
  have hc := (abs_lt.mp hacc).2
  unfold tAcc at hc
  have hp : 2101 / 10000 < p := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hQ : 0 < 1 + (ρ / r) ^ 2 := by positivity
  have h1 : 21 / 100 < 1 / (1 + (ρ / r) ^ 2) := by linarith
  rw [lt_div_iff₀ hQ] at h1
  have hq : (ρ / r) ^ 2 < 4 := by nlinarith
  have hq' : ρ ^ 2 < 4 * r ^ 2 := by
    rw [div_pow, div_lt_iff₀ (by positivity)] at hq
    linarith
  constructor
  · nlinarith
  · nlinarith

/-- An accurate rejection certifies the invariant for the next candidate. -/
theorem reject_inv (ρ r p : ℝ) (n c : ℕ) (hρ : 0 < ρ) (hr : 0 < r)
    (hpl : 1 / (2 * (1 + (ρ / r) ^ 2)) ≤ p) (hacc : |(c : ℝ) - n * p| < n * tAcc)
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

/-- At a candidate `r ≥ ρ` an accurate count always accepts. -/
theorem last_accepts (ρ r p : ℝ) (n c : ℕ) (hρ : 0 < ρ) (hr : 0 < r) (hρr : ρ ≤ r)
    (hpl : 1 / (2 * (1 + (ρ / r) ^ 2)) ≤ p) (hacc : |(c : ℝ) - n * p| < n * tAcc) :
    22 * n ≤ 100 * c := by
  have hn := n_pos_of_accurate n c p hacc
  have hq : (ρ / r) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  have hp : 1 / 4 ≤ p := by
    refine le_trans ?_ hpl
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hc := (abs_lt.mp hacc).1
  unfold tAcc at hc
  have : (22 : ℝ) * n ≤ 100 * c := by nlinarith
  exact_mod_cast this

/-- **One stage.**  With the invariant `27 r² ≤ 92 ρ²` (`r ≤ 2√(23/27) ρ`) and
`ρ ≤ 2^k r`, the candidates `r, …, 2^k r` lead to a good estimate in
`[ρ, 4ρ]`, except with probability `(k+1) ζ`. -/
theorem candidates_le (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (j n : ℕ) (κ ρ ζ β : ℝ)
    (hρ1 : 1 ≤ ρ) (hρκ : ρ ≤ κ) (hζ : 0 < ζ) (hβ : 0 ≤ β)
    (hn : 4 * Real.log (2 / ζ) / tAcc ^ 2 ≤ n)
    (htU : ∀ r, IsUnitary ((test j r).circuit.eval x))
    (hp : ∀ r, 1 / 8 ≤ r →
      1 / (2 * (1 + (ρ / r) ^ 2)) ≤ (test j r).probability x ∧
        (test j r).probability x ≤ 1 / (1 + (ρ / r) ^ 2) + 1 / 10000)
    (cont : ℝ → Tree O F E) (hcU : ∀ r, (cont r).RunsUnitary x)
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
        have hA := last_accepts ρ r _ n c hρ0 hr0 hlast hpl hacc
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
          have hinv' := reject_inv ρ r _ n c hρ0 hr0 hpl hacc hA
          have hlast' : ρ ≤ 2 ^ k * (2 * r) := by
            rw [pow_succ] at hlast
            linarith
          exact ih (2 * r) (by linarith) hinv' hlast')
    push_cast at hstep ⊢
    linarith

/-- **All stages.**  From a good previous estimate, the remaining stages reach a
leaf with `g = 0` except with probability `Σ 5 ζ_j`. -/
theorem stages_le (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) (ρ ζ : ℕ → ℝ)
    (hρ : ∀ j, j ≤ m → 1 ≤ ρ j ∧ ρ j ≤ κ)
    (hlad : ∀ j, 1 ≤ j → j ≤ m → ρ (j - 1) ≤ ρ j ∧ ρ j ≤ 2 * ρ (j - 1))
    (hζ : ∀ j, 0 < ζ j) (hn : ∀ j, 4 * Real.log (2 / ζ j) / tAcc ^ 2 ≤ reps j)
    (htU : ∀ j r, IsUnitary ((test j r).circuit.eval x))
    (hp : ∀ j r, 1 ≤ j → j ≤ m → 1 / 8 ≤ r →
      1 / (2 * (1 + (ρ j / r) ^ 2)) ≤ (test j r).probability x ∧
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
    have hstage := candidates_le x test g hg0 hg1 j (reps j) κ (ρ j) (ζ j)
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

/-- **The estimator analysis** (equations `qls:eq:estimatebound`, union bound). -/
theorem algorithm_bad_le (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1)
    (leaf : ℝ → ODERepeatProtocol.Protocol O E) (reps : ℕ → ℕ) (m : ℕ) (κ : ℝ) (ρ ζ : ℕ → ℝ)
    (hρ0 : ρ 0 = 1) (hρ : ∀ j, j ≤ m → 1 ≤ ρ j ∧ ρ j ≤ κ)
    (hlad : ∀ j, 1 ≤ j → j ≤ m → ρ (j - 1) ≤ ρ j ∧ ρ j ≤ 2 * ρ (j - 1))
    (hζ : ∀ j, 0 < ζ j) (hn : ∀ j, 4 * Real.log (2 / ζ j) / tAcc ^ 2 ≤ reps j)
    (htU : ∀ j r, IsUnitary ((test j r).circuit.eval x))
    (hp : ∀ j r, 1 ≤ j → j ≤ m → 1 / 8 ≤ r →
      1 / (2 * (1 + (ρ j / r) ^ 2)) ≤ (test j r).probability x ∧
        (test j r).probability x ≤ 1 / (1 + (ρ j / r) ^ 2) + 1 / 10000)
    (hgood : ∀ r, ρ m ≤ r → r ≤ 4 * ρ m → g (leaf r) = 0) :
    (algorithm test leaf reps m κ).expect ℝ g x ≤ ∑ q ∈ Finset.range m, 5 * ζ (m - q) := by
  apply stages_le x test g hg0 hg1 leaf reps m κ ρ ζ hρ hlad hζ hn htU hp hgood m le_rfl 1
  · rw [Nat.sub_self, hρ0]
  · rw [Nat.sub_self, hρ0]; norm_num

end Analysis

end Estimator

end

end SparseLinearSystems.Protocol
