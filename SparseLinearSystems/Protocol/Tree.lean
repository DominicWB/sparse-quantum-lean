import SparseODE.ODECompleteSuccess
import SparseLinearSystems.Statistics.BinomialTail

/-!
# Adaptive classical control of fresh measured runs

A `TestRun` is one fresh execution of a public program on a public unit seed,
followed by the public two-outcome measurement of the flag `F F†` (`F` an
isometry); its Born success probability is `‖F† C_x ψ‖²`.  The measured
workspace is discarded; only the classical bit is kept.

A `Tree` is a finite classical decision tree: a `test` node performs one fresh
run and continues with the `success` or `failure` subtree; a `final` leaf runs
a bounded fresh-trial preparation protocol (`ODERepeatProtocol.Protocol`) whose
heralded output is the output of the whole algorithm.

Semantics (`expect`) is the transcript law: a run with success probability `p`
contributes weight `p` to its success branch and `1 - p` to its failure branch.
`successMass`, `successDensity` and the probability `reach` of reaching a leaf
with a given property are expectations of leaf quantities.  `worstCost` is the
maximum query cost over all transcripts.

`countRuns t next n` performs `n` fresh runs of `t` and continues with
`next (number of successes)`; its law is binomial (`expect_countRuns`).
-/

namespace SparseLinearSystems.Protocol

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit BinomialTail
open scoped InnerProduct ComplexOrder

variable {K E F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

/-- One fresh measured run with public data. -/
structure TestRun (O : L → X → K →L[ℂ] K) (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] where
  circuit : MultiOracleCircuit.Program O
  seed : K
  seed_unit : ‖seed‖ = 1
  flag : F →L[ℂ] K
  flag_isometry : flag† ∘L flag = 1

namespace TestRun

/-- Born probability of the success flag. -/
def probability (t : TestRun O F) (x : X) : ℝ := ‖(t.flag†) (t.circuit.eval x t.seed)‖ ^ 2

theorem probability_nonneg (t : TestRun O F) (x : X) : 0 ≤ t.probability x := sq_nonneg _

theorem probability_le_one (t : TestRun O F) (x : X) (hU : IsUnitary (t.circuit.eval x)) :
    t.probability x ≤ 1 := by
  have hPart := ODERepeatProtocol.herald_probability_partition t.flag t.flag_isometry
    (t.circuit.eval x t.seed)
  have hNorm : ‖t.circuit.eval x t.seed‖ = 1 := by
    rw [(t.circuit.eval x).norm_map_iff_adjoint_comp_self.mpr hU.1, t.seed_unit]
  rw [hNorm] at hPart
  unfold probability
  nlinarith [sq_nonneg ‖t.circuit.eval x t.seed - t.flag ((t.flag†) (t.circuit.eval x t.seed))‖]

end TestRun

/-- Finite adaptive protocols: fresh measured runs, then a final preparation. -/
inductive Tree (O : L → X → K →L[ℂ] K) (F E : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  | final (p : ODERepeatProtocol.Protocol O E)
  | test (t : TestRun O F) (success failure : Tree O F E)

namespace Tree

/-! ### Semantics -/

/-- Expectation of a leaf quantity over the classical transcript law. -/
def expect (R : Type*) {M : Type*} [CommRing R] [Algebra ℝ R] [AddCommGroup M] [Module R M]
    (f : ODERepeatProtocol.Protocol O E → M) (x : X) : Tree O F E → M
  | .final p => f p
  | .test t s fl => algebraMap ℝ R (t.probability x) • expect R f x s +
      algebraMap ℝ R (1 - t.probability x) • expect R f x fl

/-- Probability of a heralded output. -/
def successMass (T : Tree O F E) (x : X) : ℝ := T.expect ℝ (fun p => p.successMass x) x

/-- Unnormalised heralded output operator. -/
def successDensity (T : Tree O F E) (x : X) : E →L[ℂ] E :=
  T.expect ℂ (fun p => p.successDensity x) x

/-- Output conditioned on the herald, classical transcripts discarded. -/
def conditionalDensity (T : Tree O F E) (x : X) : E →L[ℂ] E :=
  ((T.successMass x)⁻¹ : ℂ) • T.successDensity x

open Classical in
/-- Indicator of a leaf property. -/
def indicator (P : ODERepeatProtocol.Protocol O E → Prop) (p : ODERepeatProtocol.Protocol O E) :
    ℝ :=
  if P p then 1 else 0

theorem indicator_of_pos {P : ODERepeatProtocol.Protocol O E → Prop}
    {p : ODERepeatProtocol.Protocol O E} (h : P p) : indicator P p = 1 := by
  classical
  simp [indicator, h]

theorem indicator_of_neg {P : ODERepeatProtocol.Protocol O E → Prop}
    {p : ODERepeatProtocol.Protocol O E} (h : ¬ P p) : indicator P p = 0 := by
  classical
  simp [indicator, h]

theorem indicator_nonneg (P : ODERepeatProtocol.Protocol O E → Prop)
    (p : ODERepeatProtocol.Protocol O E) : 0 ≤ indicator P p := by
  by_cases h : P p
  · rw [indicator_of_pos h]; norm_num
  · rw [indicator_of_neg h]

theorem indicator_le_one (P : ODERepeatProtocol.Protocol O E → Prop)
    (p : ODERepeatProtocol.Protocol O E) : indicator P p ≤ 1 := by
  by_cases h : P p
  · rw [indicator_of_pos h]
  · rw [indicator_of_neg h]; norm_num

/-- Probability of reaching a final leaf with property `P`. -/
def reach (P : ODERepeatProtocol.Protocol O E → Prop) (T : Tree O F E) (x : X) : ℝ :=
  T.expect ℝ (indicator P) x

/-- Maximum weighted query cost over all transcripts, every run counted. -/
def worstCost : Tree O F E → (L → ℕ) → ℕ
  | .final p, w => p.worstCost w
  | .test t s f, w => t.circuit.cost w + max (s.worstCost w) (f.worstCost w)

/-- A property of every final leaf. -/
def AllLeaves (Q : ODERepeatProtocol.Protocol O E → Prop) : Tree O F E → Prop
  | .final p => Q p
  | .test _ s f => AllLeaves Q s ∧ AllLeaves Q f

/-- All runs are unitary circuits at the input `x`. -/
def RunsUnitary (x : X) : Tree O F E → Prop
  | .final _ => True
  | .test t s f => IsUnitary (t.circuit.eval x) ∧ RunsUnitary x s ∧ RunsUnitary x f

/-! ### Counting fresh runs -/

/-- `n` fresh runs of `t`, adding the number of successes to `acc`. -/
def countRuns (t : TestRun O F) (next : ℕ → Tree O F E) : ℕ → ℕ → Tree O F E
  | 0, acc => next acc
  | n + 1, acc => .test t (countRuns t next n (acc + 1)) (countRuns t next n acc)

/-- Pascal's rule for one binomial weight. -/
theorem binom_succ (n : ℕ) (p : ℝ) (k : ℕ) :
    binom (n + 1) p k = (1 - p) * binom n p k + (if k = 0 then 0 else p * binom n p (k - 1)) := by
  rcases k with _ | j
  · simp [binom, pow_succ]
    ring
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    unfold binom
    rw [Nat.choose_succ_succ, Nat.cast_add]
    rcases Nat.lt_trichotomy j n with hlt | heq | hgt
    · have e1 : n + 1 - (j + 1) = n - j := by omega
      have e2 : n - j = (n - (j + 1)) + 1 := by omega
      rw [e1, e2, pow_succ, pow_succ]
      ring
    · subst heq
      simp [Nat.choose_succ_self]
      ring
    · have h1 : n.choose j = 0 := Nat.choose_eq_zero_of_lt hgt
      have h2 : n.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h1, h2]

/-- Pascal's rule for the binomial law, summed against a test function. -/
theorem binom_sum_succ {M : Type*} [AddCommGroup M] [Module ℝ M] (n : ℕ) (p : ℝ) (g : ℕ → M) :
    ∑ k ∈ Finset.range (n + 2), binom (n + 1) p k • g k =
      p • ∑ k ∈ Finset.range (n + 1), binom n p k • g (k + 1) +
        (1 - p) • ∑ k ∈ Finset.range (n + 1), binom n p k • g k := by
  have hlast : binom n p (n + 1) = 0 := by simp [binom, Nat.choose_succ_self]
  have hA : ∑ k ∈ Finset.range (n + 2), binom (n + 1) p k • g k =
      ∑ k ∈ Finset.range (n + 2), ((1 - p) * binom n p k) • g k +
        ∑ k ∈ Finset.range (n + 2), (if k = 0 then 0 else p * binom n p (k - 1)) • g k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [binom_succ, add_smul]
  have hB : ∑ k ∈ Finset.range (n + 2), ((1 - p) * binom n p k) • g k =
      (1 - p) • ∑ k ∈ Finset.range (n + 1), binom n p k • g k := by
    rw [Finset.sum_range_succ, hlast, mul_zero, zero_smul, add_zero, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_smul]
  have hC : ∑ k ∈ Finset.range (n + 2), (if k = 0 then 0 else p * binom n p (k - 1)) • g k =
      p • ∑ k ∈ Finset.range (n + 1), binom n p k • g (k + 1) := by
    rw [Finset.sum_range_succ', Finset.smul_sum, if_pos rfl, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, smul_smul]
  rw [hA, hB, hC, add_comm]

/-- **Binomial law of counted fresh runs.** -/
theorem expect_countRuns (R : Type*) {M : Type*} [CommRing R] [Algebra ℝ R] [AddCommGroup M]
    [Module R M] (f : ODERepeatProtocol.Protocol O E → M) (x : X) (t : TestRun O F)
    (next : ℕ → Tree O F E) (n acc : ℕ) :
    (countRuns t next n acc).expect R f x =
      ∑ k ∈ Finset.range (n + 1),
        algebraMap ℝ R (binom n (t.probability x) k) • (next (acc + k)).expect R f x := by
  letI : Module ℝ M := Module.compHom M (algebraMap ℝ R)
  have hsm : ∀ (c : ℝ) (m : M), algebraMap ℝ R c • m = c • m := fun _ _ => rfl
  simp only [hsm]
  induction n generalizing acc with
  | zero => simp [countRuns, binom]
  | succ n ih =>
    rw [countRuns, expect, hsm, hsm, ih, ih, binom_sum_succ]
    congr 2
    · apply Finset.sum_congr rfl
      intro k _
      rw [show acc + 1 + k = acc + (k + 1) by omega]

theorem AllLeaves.imp {Q Q' : ODERepeatProtocol.Protocol O E → Prop} (h : ∀ p, Q p → Q' p) :
    ∀ T : Tree O F E, T.AllLeaves Q → T.AllLeaves Q'
  | .final p, hT => h p hT
  | .test _ s f, hT => ⟨AllLeaves.imp h s hT.1, AllLeaves.imp h f hT.2⟩

theorem allLeaves_true : ∀ T : Tree O F E, T.AllLeaves (fun _ => True)
  | .final _ => trivial
  | .test _ s f => ⟨allLeaves_true s, allLeaves_true f⟩

/-! ### Real expectations -/

theorem expect_real_test (f : ODERepeatProtocol.Protocol O E → ℝ) (x : X) (t : TestRun O F)
    (s fl : Tree O F E) :
    (test t s fl).expect ℝ f x =
      t.probability x * s.expect ℝ f x + (1 - t.probability x) * fl.expect ℝ f x := by
  simp only [expect, Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]

theorem expect_mono (f g : ODERepeatProtocol.Protocol O E → ℝ) (x : X) (T : Tree O F E)
    (hU : T.RunsUnitary x) (h : T.AllLeaves (fun p => f p ≤ g p)) :
    T.expect ℝ f x ≤ T.expect ℝ g x := by
  induction T with
  | final p => exact h
  | test t s fl ihs ihf =>
    rw [expect_real_test, expect_real_test]
    have hp0 := t.probability_nonneg x
    have hp1 := t.probability_le_one x hU.1
    have h1 := ihs hU.2.1 h.1
    have h2 := ihf hU.2.2 h.2
    have h3 : 0 ≤ 1 - t.probability x := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hp0, mul_le_mul_of_nonneg_left h2 h3]

theorem expect_const (c : ℝ) (x : X) (T : Tree O F E) :
    T.expect ℝ (fun _ => c) x = c := by
  induction T with
  | final p => rfl
  | test t s fl ihs ihf => rw [expect_real_test, ihs, ihf]; ring

theorem expect_add (f g : ODERepeatProtocol.Protocol O E → ℝ) (x : X) (T : Tree O F E) :
    T.expect ℝ (fun p => f p + g p) x = T.expect ℝ f x + T.expect ℝ g x := by
  induction T with
  | final p => rfl
  | test t s fl ihs ihf => rw [expect_real_test, expect_real_test, expect_real_test, ihs, ihf]; ring

theorem expect_mul (c : ℝ) (f : ODERepeatProtocol.Protocol O E → ℝ) (x : X) (T : Tree O F E) :
    T.expect ℝ (fun p => c * f p) x = c * T.expect ℝ f x := by
  induction T with
  | final p => rfl
  | test t s fl ihs ihf => rw [expect_real_test, expect_real_test, ihs, ihf]; ring

theorem reach_add_compl (P : ODERepeatProtocol.Protocol O E → Prop) (x : X) (T : Tree O F E) :
    T.reach P x + T.reach (fun p => ¬ P p) x = 1 := by
  induction T with
  | final p =>
    unfold reach
    simp only [expect]
    by_cases hp : P p
    · rw [indicator_of_pos hp, indicator_of_neg (not_not.mpr hp)]; norm_num
    · rw [indicator_of_neg hp, indicator_of_pos (show (fun p => ¬ P p) p from hp)]; norm_num
  | test t s fl ihs ihf =>
    unfold reach at *
    rw [expect_real_test, expect_real_test]
    linear_combination t.probability x * ihs + (1 - t.probability x) * ihf

theorem reach_nonneg (P : ODERepeatProtocol.Protocol O E → Prop) (x : X) (T : Tree O F E)
    (hU : T.RunsUnitary x) : 0 ≤ T.reach P x := by
  have h := expect_mono (fun _ => (0 : ℝ)) (indicator P) x T hU
    (AllLeaves.imp (fun p _ => indicator_nonneg P p) T (allLeaves_true T))
  rw [expect_const] at h
  exact h

/-- **Success lower bound** from good leaves. -/
theorem successMass_ge (x : X) (T : Tree O F E) (hU : T.RunsUnitary x) (a : ℝ)
    (G : ODERepeatProtocol.Protocol O E → Prop)
    (hleaf : T.AllLeaves (fun p => 0 ≤ p.successMass x ∧ (G p → a ≤ p.successMass x))) :
    a * T.reach G x ≤ T.successMass x := by
  unfold reach successMass
  rw [← expect_mul]
  apply expect_mono _ _ x T hU
  refine AllLeaves.imp (fun p hp => ?_) T hleaf
  obtain ⟨h0, h1⟩ := hp
  by_cases hg : G p
  · rw [indicator_of_pos hg, mul_one]; exact h1 hg
  · rw [indicator_of_neg hg, mul_zero]; exact h0

/-! ### Counted runs: leaves, unitarity and cost -/

theorem allLeaves_countRuns (Q : ODERepeatProtocol.Protocol O E → Prop) (t : TestRun O F)
    (next : ℕ → Tree O F E) (h : ∀ j, (next j).AllLeaves Q) (n acc : ℕ) :
    (countRuns t next n acc).AllLeaves Q := by
  induction n generalizing acc with
  | zero => exact h acc
  | succ n ih => exact ⟨ih (acc + 1), ih acc⟩

theorem runsUnitary_countRuns (x : X) (t : TestRun O F) (ht : IsUnitary (t.circuit.eval x))
    (next : ℕ → Tree O F E) (h : ∀ j, (next j).RunsUnitary x) (n acc : ℕ) :
    (countRuns t next n acc).RunsUnitary x := by
  induction n generalizing acc with
  | zero => exact h acc
  | succ n ih => exact ⟨ht, ih (acc + 1), ih acc⟩

theorem worstCost_countRuns (w : L → ℕ) (t : TestRun O F) (next : ℕ → Tree O F E) (B : ℕ)
    (h : ∀ j, (next j).worstCost w ≤ B) (n acc : ℕ) :
    (countRuns t next n acc).worstCost w ≤ n * t.circuit.cost w + B := by
  induction n generalizing acc with
  | zero => simpa [countRuns] using h acc
  | succ n ih =>
    simp only [countRuns, worstCost]
    have h1 := ih (acc + 1)
    have h2 := ih acc
    have := max_le h1 h2
    rw [Nat.succ_mul]
    omega

/-! ### Output density and trace distance -/

section Density

open ODEMixedOutput

variable [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
theorem successMass_test (x : X) (t : TestRun O F) (s fl : Tree O F E) :
    (test t s fl).successMass x =
      t.probability x * s.successMass x + (1 - t.probability x) * fl.successMass x :=
  expect_real_test _ x t s fl

omit [FiniteDimensional ℂ E] in
theorem successDensity_test (x : X) (t : TestRun O F) (s fl : Tree O F E) :
    (test t s fl).successDensity x =
      ((t.probability x : ℝ) : ℂ) • s.successDensity x +
        ((1 - t.probability x : ℝ) : ℂ) • fl.successDensity x := rfl

omit [FiniteDimensional ℂ E] in
theorem successDensity_positive (x : X) (T : Tree O F E) (hU : T.RunsUnitary x)
    (hleaf : T.AllLeaves (fun p => (p.successDensity x).IsPositive)) :
    (T.successDensity x).IsPositive := by
  induction T with
  | final p => exact hleaf
  | test t s fl ihs ihf =>
    rw [successDensity_test]
    have hp0 := t.probability_nonneg x
    have hp1 := t.probability_le_one x hU.1
    have hq0 : (0 : ℝ) ≤ 1 - t.probability x := by linarith
    exact ((ihs hU.2.1 hleaf.1).smul_of_nonneg (Complex.zero_le_real.mpr hp0)).add
      ((ihf hU.2.2 hleaf.2).smul_of_nonneg (Complex.zero_le_real.mpr hq0))

omit [FiniteDimensional ℂ E] in
theorem trace_successDensity (x : X) (T : Tree O F E)
    (hleaf : T.AllLeaves (fun p =>
      LinearMap.trace ℂ E (p.successDensity x).toLinearMap = (p.successMass x : ℂ))) :
    LinearMap.trace ℂ E (T.successDensity x).toLinearMap = (T.successMass x : ℂ) := by
  induction T with
  | final p => exact hleaf
  | test t s fl ihs ihf =>
    rw [successDensity_test, successMass_test, ContinuousLinearMap.toLinearMap_add,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, map_smul,
      ihs hleaf.1, ihf hleaf.2]
    push_cast
    simp only [smul_eq_mul]

omit [FiniteDimensional ℂ E] in
theorem diagonalMass_sub_le {α : Type*} [Fintype α] (b : OrthonormalBasis α ℂ E) (v : E)
    (x : X) (T : Tree O F E) (hU : T.RunsUnitary x) :
    diagonalMass b (T.successDensity x - ((T.successMass x : ℝ) : ℂ) • pureOperator v) ≤
      T.expect ℝ (fun p => diagonalMass b
        (p.successDensity x - ((p.successMass x : ℝ) : ℂ) • pureOperator v)) x := by
  induction T with
  | final p => exact le_rfl
  | test t s fl ihs ihf =>
    rw [expect_real_test, successDensity_test, successMass_test]
    have hp0 := t.probability_nonneg x
    have hp1 := t.probability_le_one x hU.1
    have hq0 : (0 : ℝ) ≤ 1 - t.probability x := by linarith
    have hrw : ((t.probability x : ℝ) : ℂ) • s.successDensity x +
        ((1 - t.probability x : ℝ) : ℂ) • fl.successDensity x -
        (((t.probability x * s.successMass x + (1 - t.probability x) * fl.successMass x : ℝ)) : ℂ) •
          pureOperator v =
        ((t.probability x : ℝ) : ℂ) •
            (s.successDensity x - ((s.successMass x : ℝ) : ℂ) • pureOperator v) +
          ((1 - t.probability x : ℝ) : ℂ) •
            (fl.successDensity x - ((fl.successMass x : ℝ) : ℂ) • pureOperator v) := by
      push_cast
      module
    rw [hrw]
    refine (diagonalMass_add_le b _ _).trans ?_
    rw [diagonalMass_smul, diagonalMass_smul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hp0, abs_of_nonneg hq0]
    exact add_le_add (mul_le_mul_of_nonneg_left (ihs hU.2.1) hp0)
      (mul_le_mul_of_nonneg_left (ihf hU.2.2) hq0)

omit [FiniteDimensional ℂ E] [CompleteSpace E] in
theorem diagonalMass_pure_le {α : Type*} [Fintype α] (b : OrthonormalBasis α ℂ E) (u : E) :
    diagonalMass b (pureOperator u) ≤ ‖u‖ ^ 2 := by
  rw [sq]
  exact diagonalMass_rankOne_le b u u

/-- **Output guarantee.**  If every leaf outputs a pure state with its success
mass, and leaves satisfying `G` are `δ`-close to `v` up to phase, then the
conditional output is a density operator within trace distance
`δ + P(¬G)/P(success)` of `|v⟩⟨v|`. -/
theorem output_guarantee (x : X) (T : Tree O F E) (hU : T.RunsUnitary x) (v : E) (hv : ‖v‖ = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (G : ODERepeatProtocol.Protocol O E → Prop)
    (dir : ODERepeatProtocol.Protocol O E → E)
    (hleaf : T.AllLeaves (fun p => 0 ≤ p.successMass x ∧ p.successMass x ≤ 1 ∧
      (p.successMass x ≠ 0 → ‖dir p‖ = 1) ∧
      p.successDensity x = ((p.successMass x : ℝ) : ℂ) • pureOperator (dir p) ∧
      (G p → p.successMass x ≠ 0 → ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • dir p - v‖ ≤ δ)))
    (hM : 0 < T.successMass x) :
    IsDensity (T.conditionalDensity x) ∧
      ∃ h : (T.conditionalDensity x - pureOperator v).toLinearMap.IsSymmetric,
        hermitianTraceDistance (T.conditionalDensity x) (pureOperator v) h ≤
          δ + T.reach (fun p => ¬ G p) x / T.successMass x := by
  classical
  have hMne : ((T.successMass x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  -- positivity and trace of the unnormalised output
  have hpos : (T.successDensity x).IsPositive := by
    apply successDensity_positive x T hU
    refine AllLeaves.imp (fun p hp => ?_) T hleaf
    obtain ⟨h0, -, -, hd, -⟩ := hp
    rw [hd]
    exact (pureOperator_positive _).smul_of_nonneg (Complex.zero_le_real.mpr h0)
  have htr : LinearMap.trace ℂ E (T.successDensity x).toLinearMap = (T.successMass x : ℂ) := by
    apply trace_successDensity x T
    refine AllLeaves.imp (fun p hp => ?_) T hleaf
    obtain ⟨-, -, hn, hd, -⟩ := hp
    rw [hd, ContinuousLinearMap.toLinearMap_smul, map_smul, pureOperator,
      InnerProductSpace.trace_rankOne, inner_self_complex]
    by_cases hm : p.successMass x = 0
    · simp [hm]
    · rw [hn hm]; simp
  have hρpos : (T.conditionalDensity x).IsPositive := by
    unfold conditionalDensity
    have hMinv : (0 : ℂ) ≤ (((T.successMass x)⁻¹ : ℝ) : ℂ) :=
      Complex.zero_le_real.mpr (inv_nonneg.mpr hM.le)
    have := hpos.smul_of_nonneg hMinv
    convert this using 2
    push_cast
    rfl
  have hρtr : LinearMap.trace ℂ E (T.conditionalDensity x).toLinearMap = 1 := by
    unfold conditionalDensity
    rw [ContinuousLinearMap.toLinearMap_smul, map_smul, htr, smul_eq_mul]
    exact inv_mul_cancel₀ hMne
  have hdens : IsDensity (T.conditionalDensity x) := ⟨hρpos, hρtr⟩
  have hherm : (T.conditionalDensity x - pureOperator v).toLinearMap.IsSymmetric :=
    hρpos.isSymmetric.sub (pureOperator_positive v).isSymmetric
  refine ⟨hdens, hherm, ?_⟩
  rw [hermitianTraceDistance_eq_diagonalMass]
  -- `ρ - |v⟩⟨v| = M⁻¹ (S - M |v⟩⟨v|)`
  have hsub : T.conditionalDensity x - pureOperator v =
      (((T.successMass x)⁻¹ : ℝ) : ℂ) •
        (T.successDensity x - ((T.successMass x : ℝ) : ℂ) • pureOperator v) := by
    unfold conditionalDensity
    rw [smul_sub, smul_smul]
    congr 1
    · push_cast; rfl
    · rw [show (((T.successMass x)⁻¹ : ℝ) : ℂ) * ((T.successMass x : ℝ) : ℂ) = 1 by
        push_cast; exact inv_mul_cancel₀ hMne, one_smul]
  generalize hherm.eigenvectorBasis (n := Module.finrank ℂ E) rfl = b
  rw [hsub, diagonalMass_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hM.le)]
  have hD := diagonalMass_sub_le b v x T hU
  -- leafwise bound
  have hleafD : T.expect ℝ (fun p => diagonalMass b
      (p.successDensity x - ((p.successMass x : ℝ) : ℂ) • pureOperator v)) x ≤
      T.expect ℝ (fun p => 2 * δ * p.successMass x + 2 * indicator (fun p => ¬ G p) p) x := by
    apply expect_mono _ _ x T hU
    refine AllLeaves.imp (fun p hp => ?_) T hleaf
    obtain ⟨h0, h1, hn, hd, hg⟩ := hp
    rw [hd, ← smul_sub, diagonalMass_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    by_cases hm : p.successMass x = 0
    · rw [hm, zero_mul]
      have := indicator_nonneg (fun p => ¬ G p) p
      nlinarith
    by_cases hgp : G p
    · obtain ⟨ω, hω, hclose⟩ := hg hgp hm
      rw [indicator_of_neg (show ¬ (fun p => ¬ G p) p from not_not.mpr hgp), mul_zero, add_zero,
        ← pureOperator_phase ω hω (dir p)]
      have hn1 : ‖ω • dir p‖ = 1 := by rw [norm_smul, hω, hn hm, one_mul]
      have h2 := diagonalMass_pure_sub_le b _ _ hn1 hv
      have h3 : diagonalMass b (pureOperator (ω • dir p) - pureOperator v) ≤ 2 * δ :=
        h2.trans (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left h3 h0]
    · rw [indicator_of_pos (show (fun p => ¬ G p) p from hgp), mul_one]
      have h2 : diagonalMass b (pureOperator (dir p) - pureOperator v) ≤ 2 := by
        rw [sub_eq_add_neg, ← neg_one_smul ℂ (pureOperator v)]
        refine (diagonalMass_add_le b _ _).trans ?_
        rw [diagonalMass_smul, norm_neg, norm_one, one_mul]
        have ha := diagonalMass_pure_le b (dir p)
        have hb := diagonalMass_pure_le b v
        rw [hn hm] at ha
        rw [hv] at hb
        linarith
      have hδm : 0 ≤ 2 * δ * p.successMass x := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  rw [expect_add, expect_mul, expect_mul] at hleafD
  have hR : T.expect ℝ (indicator (fun p => ¬ G p)) x = T.reach (fun p => ¬ G p) x := rfl
  have hMexp : T.expect ℝ (fun p => p.successMass x) x = T.successMass x := rfl
  rw [hR, hMexp] at hleafD
  have hfinal : (T.successMass x)⁻¹ * diagonalMass b
      (T.successDensity x - ((T.successMass x : ℝ) : ℂ) • pureOperator v) ≤
      (T.successMass x)⁻¹ * (2 * δ * T.successMass x + 2 * T.reach (fun p => ¬ G p) x) :=
    mul_le_mul_of_nonneg_left (hD.trans hleafD) (inv_nonneg.mpr hM.le)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hexpand : (T.successMass x)⁻¹ *
      (2 * δ * T.successMass x + 2 * T.reach (fun p => ¬ G p) x) =
      (δ + T.reach (fun p => ¬ G p) x / T.successMass x) * 2 := by
    field_simp
  linarith [hfinal, hexpand]

end Density

end Tree

end

end SparseLinearSystems.Protocol
