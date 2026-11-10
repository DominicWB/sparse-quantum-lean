import OptimalLowerBounds.Access
import OptimalSparseSimulation.Optimal

set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `hs:thm:optimal`: the worst-case query complexity is `Θ(√s τ + √(sτr) + r)`

Theorem `hs:thm:optimal` of the manuscript (`hs:eq:optimal-theta`): for `s ≥ 32` the worst-case
query complexity of simulating a sparse Hamiltonian with row and column Euclidean norms at most `η`,
time `τ = η|t| ≥ 1` and `0 < ε ≤ 1/64`, allowing the dimension to grow, is
`Θ(√s τ + √(sτ L/log(e + L/τ)) + L/log(e + L/τ))`. Its proof: "Theorem `hsl:thm:main` supplies the
matching lower bound in the stated range. Its hard matrices have maximum row and column Euclidean
norms exactly one, so rescaling them by `η` gives the present promise at normalised time `η|t|`."
The remark after Theorem `hsl:thm:main` adds "Theorem `hs:thm:optimal` matches it term by term", and
the remark after Corollary `hsl:cor:power` "The optimal mixed term still contains a divisor
`√(log(e+L/τ))`, so the stronger lower bound `Ω(√(sτL))` cannot hold uniformly: our upper bound is
smaller in the relevant joint regimes."

Both bounds are stated here in **one query model**, the common form of the upper bound
(`NativeSignedFactor.Simulates`: a known isometric input, one program over the native
primitives with spectator registers, unitary on every instance, full-output error `ε`), on the
three hard families of Theorem `hsl:thm:main` (`timeData`, `mixedMainData`,
`precisionMainData`, with `η = 1` and `t = τ`).

* `time_common`, `mixed_common`, `precision_common`: the per-family lower bounds for every
  program in the common form under the endpoint error (value queries, inverses included;
  location queries free), from `time_of_access` and the certificates of `Access`;
* `main_max_simulates`: eq. `hsl:eq:main` for any three common-form simulations of the three
  families, `c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`;
* `simulationCost D t ε`: the infimum of the query bounds of the common-form simulations of `D`
  (worst case over its instances; `0` if there is none), with `simulationCost_le`,
  `exists_simulates_lt` and `simulationCost_nonneg`;
* `optimal_on_hard`: the hard families meet the hypotheses of
  `OptimalSparseSimulation.optimal_simulation` with `η = 1`, so each is simulated with at most
  `2·10¹² (√s τ + √(sτr) + r)` queries (`bound_eq`: `rb τ ε = hsR τ ε`);
* **`optimal_theta`**: `c₀ S ≤ max(simulationCost_T, simulationCost_M, simulationCost_P) ≤
  2·10¹² S`, `S = √s τ + √(sτr) + r`, `c₀ = log 2/(4096π)`;
* **`not_uniform_sqrt`**: for every `c > 0` there are parameters in the range of
  `hsl:thm:main` at which every Hermitian `H` with row and column norms at most one is simulated
  with fewer than `c √(sτL)` queries (`bound_lt_sqrt`, at `τ = 1`, `s = N²`, `ε = e^{-N}`), so
  `Ω(√(sτL))` cannot hold uniformly.

As in the released bracket `SparseLowerBounds.Hamiltonian.release_theta`, the lower bound is on
the maximum over the three families: they have different index and word types, and different
families may witness the three terms.
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.Hamiltonian.HsRelease Readout
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### The cost of a simulation in the common form -/

section Cost

variable {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  {s : ℕ}

/-- **The query complexity of `D` in the common form**: the infimum of the query bounds `q` of
the common-form simulations (`NativeSignedFactor.Simulates`) of `e^{-itH(x)}`, `H(x) = D.matrix x`,
within full-output error `ε`. One program serves every instance, so this is the worst case over
the instances of `D`. -/
def simulationCost (D : Data X n Z s) (t ε : ℝ) : ℝ :=
  sInf {q : ℝ | NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
    (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε q}

/-- Every query bound of a common-form simulation is nonnegative. -/
theorem nonneg_of_simulates (D : Data X n Z s) {t ε q : ℝ}
    (h : NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε q) : 0 ≤ q := by
  obtain ⟨ι, hι, inp, p, -, hcount, -⟩ := h
  exact (Nat.cast_nonneg _).trans hcount

/-- The cost is at most every query bound of a simulation. -/
theorem simulationCost_le (D : Data X n Z s) {t ε q : ℝ}
    (h : NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε q) :
    simulationCost D t ε ≤ q :=
  csInf_le ⟨0, fun _ hq => nonneg_of_simulates D hq⟩ h

/-- If the cost is below `b` and some simulation exists, then some simulation has a query bound
below `b`. -/
theorem exists_simulates_lt (D : Data X n Z s) {t ε q₀ b : ℝ}
    (h₀ : NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε q₀)
    (hlt : simulationCost D t ε < b) :
    ∃ q, q < b ∧ NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε q := by
  obtain ⟨q, hq, hqb⟩ := exists_lt_of_csInf_lt (s := {q : ℝ | NativeSignedFactor.Simulates
    (NativeSignedFactor.physOracle D)
    (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε q}) (Set.nonempty_of_mem h₀) hlt
  exact ⟨q, hqb, hq⟩

/-- The cost is nonnegative. -/
theorem simulationCost_nonneg (D : Data X n Z s) (t ε : ℝ) : 0 ≤ simulationCost D t ε := by
  unfold simulationCost
  rcases Set.eq_empty_or_nonempty {q : ℝ | NativeSignedFactor.Simulates
      (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε q} with hE | hne
  · rw [hE, Real.sInf_empty]
  · exact le_csInf hne fun _ hq => nonneg_of_simulates D hq

end Cost

/-! ### The lower bounds in the common form -/

variable {τ ε : ℝ} {s : ℕ}

/-- The common workspace of a hard family: `ℂ^ι ⊗` the native-control workspace. -/
abbrev CommonSpace (ι : Type) (N Z : Type) [Fintype N] [Fintype Z] : Type :=
  PiLp 2 (fun _ : ι => NativeSignedFactor.Phys N Z)

/-- **Time family, common form** (eq. `hsl:eq:timelower`): every common-form program with
endpoint error `ε` for `e^{-iτH}` on the time family makes at least `c_T √s τ` value queries,
hence at least as many queries. -/
theorem time_common (h : HSRange τ s ε) (ι : Type) [Fintype ι]
    (p : MultiOracleCircuit.Program
      (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle (timeData τ s h.s_ge))))
    (inp : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      CommonSpace ι (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)))
    (hinp : inp† ∘L inp = 1)
    (hsim : ∀ j, ‖p.eval j ∘L inp - inp ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε) :
    2 * (cT * Real.sqrt s * τ) ≤ p.cost hardCost ∧ cT * Real.sqrt s * τ ≤ p.labelCount .value ∧
      cT * Real.sqrt s * τ ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (common_unitary _ ι) p inp hinp refZero
    (hard_instances h).1.isHermitian (norm_searchInput _ _ _) hsim
  exact time_of_access h (common_unitary _ ι) (timeCommonAccess h.s_ge ι) p _ hψ _
    (endpointReadout_isometry inp hinp refZero) hacc

/-- **Mixed family, common form** (eq. `hsl:eq:mixrbound`): for `L ≥ 64τ` and `s ≥ 64n/τ`, at
least `(log 2/(384√2)) √(sτr)` value queries. -/
theorem mixed_common (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (ι : Type) [Fintype ι]
    (p : MultiOracleCircuit.Program (CoherentQuerySchedule.oracle (ι := ι)
      (NativeSignedFactor.physOracle (mixedMainData τ ε s h.s_ge))))
    (inp : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      CommonSpace ι (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)))
    (hinp : inp† ∘L inp = 1)
    (hsim : ∀ j, ‖p.eval j ∘L inp - inp ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε) :
    2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) ≤ p.cost hardCost ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (common_unitary _ ι) p inp hinp refZero
    (hard_instances h).2.1.isHermitian (norm_searchInput _ _ _) hsim
  exact mixed_of_access h hL hs (common_unitary _ ι) (mixedCommonAccess h.s_ge ι) p _ hψ _
    (endpointReadout_isometry inp hinp refZero) hacc

/-- **Precision family, common form** (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`): for
`L ≥ 64τ`, at least `r/32` value queries, and at least `√(sτr)/(64√2)` when `s < 64n/τ`. -/
theorem precision_common (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (ι : Type) [Fintype ι]
    (p : MultiOracleCircuit.Program (CoherentQuerySchedule.oracle (ι := ι)
      (NativeSignedFactor.physOracle (precisionMainData τ ε s h.s_ge))))
    (inp : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      CommonSpace ι (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)))
    (hinp : inp† ∘L inp = 1)
    (hsim : ∀ x, ‖p.eval x ∘L inp - inp ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    2 * (hsR τ ε / 32) ≤ p.cost hardCost ∧ hsR τ ε / 32 ≤ p.labelCount .value ∧
      hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program (common_unitary _ ι) p inp hinp refZero
    (hard_instances h).2.2.1.isHermitian (norm_scalarInput _ _) hsim
  exact precision_of_access h hL (common_unitary _ ι) (precisionCommonAccess h.s_ge ι) p _ _ hacc

/-- **Theorem `hsl:thm:main` in the common form, max form** (eq. `hsl:eq:main`): for any
common-form simulations of the time, mixed and precision families at time `τ` and error `ε`,
with query bounds `q_T`, `q_M`, `q_P`, `c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`. -/
theorem main_max_simulates (h : HSRange τ s ε) {qT qM qP : ℝ}
    (hT : NativeSignedFactor.Simulates (NativeSignedFactor.physOracle (timeData τ s h.s_ge))
      (fun j => SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j)) τ ε qT)
    (hM : NativeSignedFactor.Simulates (NativeSignedFactor.physOracle (mixedMainData τ ε s h.s_ge))
      (fun j => SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j)) τ ε qM)
    (hP : NativeSignedFactor.Simulates
      (NativeSignedFactor.physOracle (precisionMainData τ ε s h.s_ge))
      (fun x => SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))
      τ ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  obtain ⟨ιT, _, inpT, pT, hinpT, hcT, hsimT⟩ := hT
  obtain ⟨ιM, _, inpM, pM, hinpM, hcM, hsimM⟩ := hM
  obtain ⟨ιP, _, inpP, pP, hinpP, hcP, hsimP⟩ := hP
  have hQT : (pT.labelCount .value : ℝ) ≤ qT :=
    (by exact_mod_cast labelCount_le_count pT .value : (pT.labelCount .value : ℝ) ≤ pT.count).trans
      hcT
  have hQM : (pM.labelCount .value : ℝ) ≤ qM :=
    (by exact_mod_cast labelCount_le_count pM .value : (pM.labelCount .value : ℝ) ≤ pM.count).trans
      hcM
  have hQP : (pP.labelCount .value : ℝ) ≤ qP :=
    (by exact_mod_cast labelCount_le_count pP .value : (pP.labelCount .value : ℝ) ≤ pP.count).trans
      hcP
  refine (assembly h (time_common h ιT pT inpT hinpT fun j => (hsimT j).2).2.1
    (fun hL => ?_) (fun hL hs => (mixed_common h hL hs ιM pM inpM hinpM
      fun j => (hsimM j).2).2.1)).trans (max_le_max hQT (max_le_max hQM hQP))
  have hP' := precision_common h hL ιP pP inpP hinpP fun x => (hsimP x).2
  exact ⟨hP'.2.1, hP'.2.2.2⟩

/-! ### The upper bound on the hard families -/

/-- The precision parameter of the upper bound is that of the lower bound:
`rb τ ε = L/log(e + L/τ) = hsR τ ε`. -/
theorem rb_eq_hsR (τ ε : ℝ) : SignedFactorSimulation.rb τ ε = hsR τ ε := rfl

/-- The query bound of `hs:thm:optimal` at `η = 1` is `2·10¹² (√s τ + √(sτr) + r)` in the
notation of `hsl:thm:main`. -/
theorem bound_eq (s : ℕ) (τ ε : ℝ) :
    OptimalSparseSimulation.bound s τ ε =
      2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := rfl

/-- `optimal_simulation` with `η = 1` and `t = τ` on data meeting `HardInstance`. -/
theorem optimal_of_hardInstance {X N : Type} [Fintype N] [DecidableEq N] {B : ℕ}
    (D : Data X N (Word B) s) (hD : HardInstance D) (h : HSRange τ s ε) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) τ ε
      (2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hτ : (1 : ℝ) * |τ| = τ := by rw [one_mul, abs_of_pos h.tau_pos]
  have hτ1 : 1 ≤ (1 : ℝ) * |τ| := by rw [hτ]; exact h.one_le_tau
  have key := OptimalSparseSimulation.optimal_simulation D (η := 1) (t := τ) hτ1 h.eps_pos
    h.eps_le hD.isHermitian
    (fun x i => by rw [one_pow]; exact hD.row_norm_le x i)
    (fun x j => by rw [one_pow]; exact hD.col_norm_le x j)
  rwa [hτ, bound_eq] at key

/-- **The hard families meet the hypotheses of `hs:thm:optimal`** (proof of `hs:thm:optimal`: "Its
hard matrices have maximum row and column Euclidean norms exactly one, so rescaling them by `η`
gives the present promise"): each is simulated in the common form with at most
`2·10¹² (√s τ + √(sτr) + r)` queries. -/
theorem optimal_on_hard (h : HSRange τ s ε) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle (timeData τ s h.s_ge))
        (fun j => SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j)) τ ε
        (2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∧
      NativeSignedFactor.Simulates (NativeSignedFactor.physOracle (mixedMainData τ ε s h.s_ge))
        (fun j => SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j)) τ ε
        (2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∧
      NativeSignedFactor.Simulates
        (NativeSignedFactor.physOracle (precisionMainData τ ε s h.s_ge))
        (fun x => SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))
        τ ε (2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact ⟨optimal_of_hardInstance _ hT h, optimal_of_hardInstance _ hM h,
    optimal_of_hardInstance _ hP h⟩

/-! ### The bracket -/

/-- **`hs:eq:optimal-theta`: the worst-case query complexity is `Θ(√s τ + √(sτr) + r)`.** For
`τ ≥ 1`, `s ≥ 32` and `0 < ε ≤ 1/64`, with `S = √s τ + √(sτr) + r`, the common-form query
complexities of the three hard families of `hsl:thm:main` (row and column norms exactly one,
hence `η = 1` and `t = τ`) satisfy

`c₀ S ≤ max(simulationCost_T, simulationCost_M, simulationCost_P) ≤ 2·10¹² S`,

`c₀ = log 2/(4096π)`: the lower bound is `main_max_simulates`, the upper bound
`OptimalSparseSimulation.optimal_simulation`, in the same query model. At `τ = 1`, `S` is the
sum of `hsl:eq:fixedtime` (`SparseLowerBounds.Hamiltonian.fixedtime_sum`). -/
theorem optimal_theta (h : HSRange τ s ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (simulationCost (timeData τ s h.s_ge) τ ε)
          (max (simulationCost (mixedMainData τ ε s h.s_ge) τ ε)
            (simulationCost (precisionMainData τ ε s h.s_ge) τ ε)) ∧
      max (simulationCost (timeData τ s h.s_ge) τ ε)
          (max (simulationCost (mixedMainData τ ε s h.s_ge) τ ε)
            (simulationCost (precisionMainData τ ε s h.s_ge) τ ε)) ≤
        2 * 10 ^ 12 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  obtain ⟨hT, hM, hP⟩ := optimal_on_hard h
  refine ⟨?_, max_le (simulationCost_le _ hT)
    (max_le (simulationCost_le _ hM) (simulationCost_le _ hP))⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨qT, hqT', hqT⟩ := exists_simulates_lt _ hT ((le_max_left _ _).trans_lt hlt)
  obtain ⟨qM, hqM', hqM⟩ := exists_simulates_lt _ hM
    (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hlt)
  obtain ⟨qP, hqP', hqP⟩ := exists_simulates_lt _ hP
    (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hlt)
  have hmax := main_max_simulates h hqT hqM hqP
  have := max_lt hqT' (max_lt hqM' hqP')
  linarith

/-! ### `Ω(√(sτL))` cannot hold uniformly -/

/-- `x ≤ exp x`. -/
theorem le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  linarith [Real.add_one_le_exp x]

/-- **Numerics of the non-uniformity**: for every `c > 0` there are `τ = 1`, `s = N²` and
`ε = e^{-N}` (so `L = N`) in the range of `hsl:thm:main` with
`2·10¹² (√s τ + √(sτr) + r) < c √(sτL)`. With `K = 6·10¹²/c`, any `N` with `N > K²` and
`log(e + N) > K²` works (each of the three terms is below `c N^{3/2}/3`). -/
theorem bound_lt_sqrt (c : ℝ) (hc : 0 < c) :
    ∃ (s : ℕ) (ε : ℝ), HSRange 1 s ε ∧
      2 * 10 ^ 12 * (Real.sqrt s * 1 + Real.sqrt (s * 1 * hsR 1 ε) + hsR 1 ε) <
        c * Real.sqrt (s * 1 * hsL ε) := by
  set K : ℝ := 6 * 10 ^ 12 / c with hK
  have hK0 : 0 < K := by positivity
  -- `N = ⌈e^{K²}⌉₊ + ⌈K²⌉₊ + 64`
  set N : ℕ := ⌈Real.exp (K ^ 2)⌉₊ + ⌈K ^ 2⌉₊ + 64 with hNdef
  have hN1 : Real.exp (K ^ 2) ≤ (N : ℝ) - ⌈K ^ 2⌉₊ - 64 := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil (Real.exp (K ^ 2))]
  have hN2 : K ^ 2 ≤ (N : ℝ) - ⌈Real.exp (K ^ 2)⌉₊ - 64 := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil (K ^ 2)]
  have hc1 : (0 : ℝ) ≤ ⌈K ^ 2⌉₊ := Nat.cast_nonneg _
  have hc2 : (0 : ℝ) ≤ ⌈Real.exp (K ^ 2)⌉₊ := Nat.cast_nonneg _
  have hN64 : (64 : ℝ) ≤ N := by linarith [Real.exp_pos (K ^ 2)]
  have hNK : K ^ 2 < N := by linarith [Real.exp_pos (K ^ 2)]
  have hNpos : (0 : ℝ) < N := by linarith
  -- the parameters
  refine ⟨N ^ 2, Real.exp (-(N : ℝ)), ⟨le_rfl, ?_, Real.exp_pos _, ?_⟩, ?_⟩
  · have : (64 : ℕ) ≤ N := by exact_mod_cast hN64
    nlinarith
  · have h64 : (64 : ℝ) ≤ Real.exp N := hN64.trans (le_exp_self _)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    exact h64
  · have hL : hsL (Real.exp (-(N : ℝ))) = N := by
      rw [hsL, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    -- the logarithm `h = log(e + N) > K²`
    set hh : ℝ := Real.log (Real.exp 1 + N) with hhdef
    have hh_gt : K ^ 2 < hh := by
      rw [hhdef, ← Real.log_exp (K ^ 2)]
      exact Real.log_lt_log (Real.exp_pos _) (by linarith [Real.exp_pos 1])
    have hhpos : 0 < hh := lt_of_le_of_lt (sq_nonneg K) hh_gt
    have hH : hsH 1 (Real.exp (-(N : ℝ))) = hh := by rw [hsH, hL, div_one]
    have hR : hsR 1 (Real.exp (-(N : ℝ))) = N / hh := by rw [hsR, hL, hH]
    rw [hR, hL]
    push_cast
    have hsN : Real.sqrt ((N : ℝ) ^ 2) = N := Real.sqrt_sq hNpos.le
    have hsq : Real.sqrt ((N : ℝ) ^ 2 * 1 * N) = N * Real.sqrt N := by
      rw [mul_one, Real.sqrt_mul (sq_nonneg _), hsN]
    have hsqr : Real.sqrt ((N : ℝ) ^ 2 * 1 * (N / hh)) = N * Real.sqrt N / Real.sqrt hh := by
      rw [mul_one, ← mul_div_assoc, Real.sqrt_div' _ hhpos.le, Real.sqrt_mul (sq_nonneg _),
        hsN]
    rw [hsN, hsq, hsqr]
    set r : ℝ := Real.sqrt N with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hNpos
    have hrr : r * r = N := Real.mul_self_sqrt hNpos.le
    have hrK : K < r := by
      rw [hr, ← Real.sqrt_sq hK0.le]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hNK
    set q : ℝ := Real.sqrt hh with hq
    have hq0 : 0 < q := Real.sqrt_pos.mpr hhpos
    have hqq : q * q = hh := Real.mul_self_sqrt hhpos.le
    have hqK : K < q := by
      rw [hq, ← Real.sqrt_sq hK0.le]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hh_gt
    have hq1 : 1 ≤ hh := by
      have : Real.exp 1 ≤ Real.exp 1 + N := by linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ hh := Real.log_le_log (Real.exp_pos 1) this
    -- the three terms, each below `c N r / 3`
    have hcK : c * K = 6 * 10 ^ 12 := by rw [hK]; field_simp
    have t1 : 2 * 10 ^ 12 * (N : ℝ) < c * (N * r) / 3 := by
      have : 2 * 10 ^ 12 * (N : ℝ) * 3 < c * (N * r) := by
        have hNr : (N : ℝ) * K < N * r := mul_lt_mul_of_pos_left hrK hNpos
        nlinarith
      linarith
    have t2 : 2 * 10 ^ 12 * (N * r / q) < c * (N * r) / 3 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      have hNr0 : 0 < (N : ℝ) * r := mul_pos hNpos hr0
      have e : 2 * 10 ^ 12 * (N * r / q) * 3 = 6 * 10 ^ 12 * (N * r) / q := by ring
      rw [e, div_lt_iff₀ hq0]
      have : 6 * 10 ^ 12 * (N * r) = c * K * (N * r) := by rw [hcK]
      rw [this]
      have h2 : c * K * (N * r) < c * q * (N * r) :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hqK hc) hNr0
      linarith
    have t3 : 2 * 10 ^ 12 * ((N : ℝ) / hh) < c * (N * r) / 3 := by
      have hdiv : (N : ℝ) / hh ≤ N := div_le_self hNpos.le hq1
      linarith [mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2 * 10 ^ 12)]
    have e : 2 * 10 ^ 12 * ((N : ℝ) * 1 + N * r / q + N / hh) =
        2 * 10 ^ 12 * N + 2 * 10 ^ 12 * (N * r / q) + 2 * 10 ^ 12 * (N / hh) := by ring
    rw [e]
    linarith

/-- **`Ω(√(sτL))` cannot hold uniformly** (the remark after Corollary `hsl:cor:power`: "the stronger
lower bound `Ω(√(sτL))` cannot hold uniformly: our upper bound is smaller in the relevant joint
regimes"). For every `c > 0` there are parameters `τ = 1`, `s`, `ε` in the range of `hsl:thm:main`
at which **every** native sparse Hamiltonian data `D` at sparsity `s` with Hermitian matrices of row
and column Euclidean norms at most one, in particular each hard family, is simulated at time `τ`
within `ε` with fewer than `c √(sτL)` queries in the common form. -/
theorem not_uniform_sqrt (c : ℝ) (hc : 0 < c) :
    ∃ (s : ℕ) (ε : ℝ), HSRange 1 s ε ∧
      ∀ {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
        [DecidableEq Z] (D : Data X n Z s), (∀ x, (D.matrix x).IsHermitian) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) → (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        ∃ q : ℝ, q < c * Real.sqrt (s * 1 * hsL ε) ∧
          NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
            (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) 1 ε q := by
  obtain ⟨s, ε, h, hlt⟩ := bound_lt_sqrt c hc
  refine ⟨s, ε, h, fun D hH hrow hcol => ⟨_, hlt, ?_⟩⟩
  have key := OptimalSparseSimulation.optimal_simulation D (η := 1) (t := 1)
    (by norm_num) h.eps_pos h.eps_le hH (fun x i => by rw [one_pow]; exact hrow x i)
    (fun x j => by rw [one_pow]; exact hcol x j)
  rwa [show (1 : ℝ) * |(1 : ℝ)| = 1 by norm_num, bound_eq] at key

end

end OptimalLowerBounds
