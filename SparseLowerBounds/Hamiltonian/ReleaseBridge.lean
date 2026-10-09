import SparseLowerBounds.Hamiltonian.ReleaseAccess

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Theorem `hsl:thm:main` for programs over the release simulator's oracles

Manuscript lines 2078-2124 (statement; the
lower bound holds in the native access model "with inverses and coherent
controls", location operations free) and 2090-2097 (an operator-norm error at
most `ε` implies eq. `hsl:eq:accuracy`).

`Hamiltonian/ReleaseForm` proves the lower bounds under the release's
endpoint error `‖p.eval x ∘L ι - ι ∘L exp(-iτH_x)‖ ≤ ε` for programs over the
native primitives (`oracles D`, with or without spectator). The release's own
simulator (`ImprovedSparseHamiltonian.simulation_log_one`) is instead a program
over `ImprovedSparseHamiltonian.oracle D γ η t δ` on
`ImprovedSparseHamiltonian.Physical …`. This module states the same lower
bounds for **every** program over that physical family, for every schedule
`γ η t δ` of the physical workspace, every isometric input encoding `ι` into it,
and endpoint error `ε` for the evolution time `τ` of the hard family:

* `time_release`: `Q ≥ c_T √s τ` (eq. `hsl:eq:timelower`);
* `mixed_release`: for `L ≥ 64τ`, `s ≥ 64n/τ`, `Q ≥ (log 2/(384√2)) √(sτr)`
  (eq. `hsl:eq:mixrbound`);
* `precision_release`: for `L ≥ 64τ`, `Q ≥ r/32` (eq. `hsl:eq:rbound`), and
  `Q ≥ √(sτr)/(64√2)` when `s < 64n/τ` (eq. `hsl:eq:failedmix`);
* `main_max_release`: `max(Q_T, Q_M, Q_P) ≥ c₀ (√s τ + √(sτr) + r)` and the
  same for the release's own counts `max(count_T, count_M, count_P)`;
* `main_max_release_cost`: the same in the Boolean weighted cost,
  `max(cost_T, cost_M, cost_P) ≥ 2 c₀ (√s τ + √(sτr) + r)`.

Here `Q = p.labelCount .value` is the number of native value queries (forward
and inverse) and `p.count` the release's own query count (all row, column and
value calls, inverses included); the Boolean weighted cost is
`p.cost hardCost = 2 Q` (`cost_hardCost`), and each per-family theorem states
the weighted-cost bound `2b ≤ p.cost hardCost` as well as `b ≤ Q ≤ p.count`.

Proof route: `accurate_of_endpoint_program` (generic in the oracle family) with
`release_oracle_unitary`, seed `ι ψ_in` and readout `endpointReadout ι r₀`
gives `Readout.Accurate`; `time_general`, `mixed_general`, `precision_general`
with the certificates of `Hamiltonian/ReleaseAccess` (`*_release_implementsOn`,
weight `hardCost`) give the Boolean-cost bound; `native_bound_of_cost` and the
numerics of `Hamiltonian/Theorem` (`precN_range`, `sixteen_eps_le`,
`mixed_m_cond`, `mixrbound`, `rbound`, `failedmix`) and `assembly` finish, as in
`mixed_main_native` / `precision_main_native` / `main_max_endpoint`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {τ ε : ℝ} {s : ℕ}

/-! ### The three families -/

/-- **Time family, release oracle** (`time_endpoint` for the release
simulator's oracle family): every program over
`ImprovedSparseHamiltonian.oracle (timeData τ s _) γ η t δ` with endpoint
error `ε` makes at least `c_T √s τ` value queries (`c_T = log 2/(192π)`), hence
at least as many release queries, and has Boolean weighted cost at least
`2 c_T √s τ`. -/
theorem time_release (h : HSRange τ s ε) (γ η t δ : ℝ)
    (p : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle (timeData τ s h.s_ge) γ η t δ))
    (ι : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] TimePhys τ s γ η t δ)
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε) :
    2 * (cT * Real.sqrt s * τ) ≤ p.cost hardCost ∧ cT * Real.sqrt s * τ ≤ p.labelCount .value ∧
      cT * Real.sqrt s * τ ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (release_oracle_unitary _ γ η t δ) p ι hι
    refZero (hard_instances h).1.isHermitian (norm_searchInput _ _ _) hsim
  obtain ⟨hE, hw⟩ := time_release_implementsOn (τ := τ) h.s_ge γ η t δ
  have hb := (time_general h.one_le_tau h.s_ge h.eps_le _ _ hE _
    (release_oracle_unitary _ γ η t δ) hardCost hw p _ hψ _
    (endpointReadout_isometry ι hι refZero) hacc).2
  have hb' : 2 * (cT * Real.sqrt s * τ) ≤ p.cost hardCost := by linarith
  exact ⟨hb', native_bound_of_cost p hb'⟩

/-- **Mixed family, release oracle** (`mixed_endpoint` for the release
simulator's oracle family): for `L ≥ 64τ` and `s ≥ 64n/τ`, every program over
`ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s _) γ η t δ` with
endpoint error `ε` makes at least `(log 2/(384√2)) √(sτr)` value queries. -/
theorem mixed_release (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (γ η t δ : ℝ)
    (p : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s h.s_ge) γ η t δ))
    (ι : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] MixedPhys τ ε s γ η t δ)
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε) :
    2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) ≤ p.cost hardCost ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (release_oracle_unitary _ γ η t δ) p ι hι
    refZero (hard_instances h).2.1.isHermitian (norm_searchInput _ _ _) hsim
  obtain ⟨hE, hw⟩ := mixed_release_implementsOn (τ := τ) (ε := ε) h.s_ge γ η t δ
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hb := mixed_general (n := precN τ ε) (μ := hsMu s) (s := s) (τ := τ) (ε := ε) hn
    (by linarith [h.one_le_tau]) (by linarith) (mixed_m_cond h hs) (by linarith [h.eps_pos])
    _ _ hE _ (release_oracle_unitary _ γ η t δ) hardCost hw p _ hψ _
    (endpointReadout_isometry ι hι refZero) hacc
  have hnum := mixrbound h hL
  have hb' : 2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) ≤
      p.cost hardCost := by linarith
  exact ⟨hb', native_bound_of_cost p hb'⟩

/-- **Precision family, release oracle** (`precision_endpoint` for the release
simulator's oracle family): for `L ≥ 64τ`, every program over
`ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s _) γ η t δ` with
endpoint error `ε` makes at least `r/32` value queries, and at least
`√(sτr)/(64√2)` when `s < 64n/τ`. -/
theorem precision_release (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (γ η t δ : ℝ)
    (p : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s h.s_ge) γ η t δ))
    (ι : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] PrecisionPhys τ ε s γ η t δ)
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ x, ‖p.eval x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    2 * (hsR τ ε / 32) ≤ p.cost hardCost ∧ hsR τ ε / 32 ≤ p.labelCount .value ∧
      hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program (release_oracle_unitary _ γ η t δ) p ι hι
    refZero (hard_instances h).2.2.1.isHermitian (norm_scalarInput _ _) hsim
  obtain ⟨hE, hw⟩ := precision_release_implementsOn (τ := τ) (ε := ε) h.s_ge γ η t δ
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hb := precision_general (n := precN τ ε) (s := s) (τ := τ) (ε := ε) (by omega)
    (by linarith [h.one_le_tau]) (by linarith) (by linarith [h.eps_pos])
    _ _ hE _ (release_oracle_unitary _ γ η t δ) hardCost hw p _ _ hacc
  have hrb := rbound h hL
  have hq : 2 * ((precN τ ε : ℝ) / 4) ≤ p.cost hardCost := by linarith
  have hb' : 2 * (hsR τ ε / 32) ≤ p.cost hardCost := by linarith
  have hQ := native_bound_of_cost p hb'
  exact ⟨hb', hQ.1, hQ.2,
    fun hs' => (failedmix h hL hs').trans (native_bound_of_cost p hq).1⟩

/-! ### Combined statement -/

/-- **Theorem `hsl:thm:main` for the release simulator's oracle family, max
form** (eq. `hsl:eq:main`, `c₀ = log 2/(4096π)`): for any three programs over
`ImprovedSparseHamiltonian.oracle` on the time, mixed and precision families
(any schedules), each with endpoint error `ε` on its own family,
`max(Q_T, Q_M, Q_P) ≥ c₀ (√s τ + √(sτr) + r)`, and the same for the release's
counts `max(count_T, count_M, count_P)`. -/
theorem main_max_release (h : HSRange τ s ε) (γT ηT tT δT γM ηM tM δM γP ηP tP δP : ℝ)
    (pT : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (timeData τ s h.s_ge) γT ηT tT δT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] TimePhys τ s γT ηT tT δT)
    (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (pM : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s h.s_ge) γM ηM tM δM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] MixedPhys τ ε s γM ηM tM δM)
    (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (pP : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s h.s_ge) γP ηP tP δP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] PrecisionPhys τ ε s γP ηP tP δP)
    (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hQ : c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
    refine assembly h (time_release h γT ηT tT δT pT ιT hιT hsimT).2.1 (fun hL => ?_)
      (fun hL hs => (mixed_release h hL hs γM ηM tM δM pM ιM hιM hsimM).2.1)
    have hP := precision_release h hL γP ηP tP δP pP ιP hιP hsimP
    exact ⟨hP.2.1, hP.2.2.2⟩
  have hT' : (pT.labelCount .value : ℝ) ≤ pT.count := by
    exact_mod_cast labelCount_le_count pT .value
  have hM' : (pM.labelCount .value : ℝ) ≤ pM.count := by
    exact_mod_cast labelCount_le_count pM .value
  have hP' : (pP.labelCount .value : ℝ) ≤ pP.count := by
    exact_mod_cast labelCount_le_count pP .value
  exact ⟨hQ, hQ.trans (max_le_max hT' (max_le_max hM' hP'))⟩

/-- **Theorem `hsl:thm:main` for the release simulator's oracle family, max
form, Boolean weighted cost** (eq. `hsl:eq:main`; lines 2286-2289: a value
call, forward or inverse, costs two Boolean queries, a location call none):
under the hypotheses of `main_max_release`,
`max(cost_T, cost_M, cost_P) ≥ 2 c₀ (√s τ + √(sτr) + r)`, where
`cost = p.cost hardCost = 2Q` (`cost_hardCost`). -/
theorem main_max_release_cost (h : HSRange τ s ε) (γT ηT tT δT γM ηM tM δM γP ηP tP δP : ℝ)
    (pT : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (timeData τ s h.s_ge) γT ηT tT δT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] TimePhys τ s γT ηT tT δT)
    (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (pM : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s h.s_ge) γM ηM tM δM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] MixedPhys τ ε s γM ηM tM δM)
    (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (pP : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s h.s_ge) γP ηP tP δP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] PrecisionPhys τ ε s γP ηP tP δP)
    (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
      max (pT.cost hardCost : ℝ) (max (pM.cost hardCost : ℝ) (pP.cost hardCost)) := by
  have hQ := (main_max_release h γT ηT tT δT γM ηM tM δM γP ηP tP δP pT ιT hιT hsimT
    pM ιM hιM hsimM pP ιP hιP hsimP).1
  have hcT : (pT.cost hardCost : ℝ) = 2 * (pT.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcM : (pM.cost hardCost : ℝ) = 2 * (pM.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcP : (pP.cost hardCost : ℝ) = 2 * (pP.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  rw [hcT, hcM, hcP, ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left hQ (by norm_num)

end

end SparseLowerBounds.Hamiltonian
end
