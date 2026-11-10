import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import SparseLowerBounds.Hamiltonian.Theorem
import SparseLowerBounds.Hamiltonian.Power
import OptimalLowerBounds.TwoNorm

/-!
# Conformance: Hamiltonian-simulation lower bounds

Theorem `hsl:thm:main`, Corollary `hsl:cor:power` and Proposition `hsl:prop:two-norm`, stated in the
manuscript's lower-bound model (Section `hsl:sec:main`, before Theorem `hsl:thm:main`):

* **Access.** The native sparse access of Section `sec:overview`: the value oracle and the
  in-place row and column locators of `NativeSparseBlockEncoding.Data`, inverse calls included
  (`MultiOracleCircuit.Program.queryAdjoint`). The primitives act on their register tensored with
  an untouched spectator register `ℂ^Ω` of any finite size (`specOracles`); known gates are
  arbitrary unitaries of the whole workspace. Controlled calls are not primitive; the hard
  families have input-independent locators, so a controlled locator call is a known gate, and a
  controlled value call is one value call between known controlled swaps (module docstring of
  `SparseLowerBounds.Hamiltonian.Theorem`).
* **Algorithms.** A program run on an input-independent initial vector of norm at most one (state
  preparation is free); its output is read through a fixed isometry into system ⊗ garbage, and
  its system state `systemState e Φ` is the reduced density operator — a mixed state in general.
  There is no postselection.
* **Accuracy** (eq. `hsl:eq:accuracy`): on every input `x`, trace distance at most `ε` from
  `e^{-iτH_x} ψ_in` for the known initial state `ψ_in` (`TraceDistanceLE`).
* **Cost.** Worst case: `p.labelCount .value` counts value queries (and their inverses), the only
  queries that carry the hidden input; `p.count` counts every primitive query. Both are bounded
  below.

`ForcesSimulation D ψ_in t ε b` says that every such algorithm, accurate on every input of `D`,
makes at least `b` value queries (and at least `b` queries). The lower bounds are proved from the
package's `SparseLowerBounds.Hamiltonian.main_exists`, `cor_power` and
`OptimalLowerBounds.two_norm_main_max`, whose accuracy hypothesis is the observable form of trace
distance (`accurate_of_traceDistanceLE`).
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds
open SparseLowerBounds.Hamiltonian
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

universe u v

/-- **`D` with known initial state `ψ_in` forces `b` queries for simulation time `t` at accuracy
`ε`** (the model of Section `hsl:sec:main`): every program over the native primitives of `D` on any
untouched spectator register `ℂ^Ω`, run on an input-independent initial vector of norm at most one
and read through an isometry into system ⊗ any garbage `G`, whose system state is within trace
distance `ε` of `e^{-itH_x} ψ_in` on every input `x`, makes at least `b` value queries and at least
`b` primitive queries. -/
def ForcesSimulation {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {s : ℕ} (D : Data X N Z s) (ψin : EuclideanSpace ℂ N) (t ε b : ℝ) : Prop :=
  ∀ (Ω : Type u) [Fintype Ω] (G : Type v) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (p : MultiOracleCircuit.Program (specOracles Ω D))
    (φ₀ : Joint Ω (SparseFlagEmbedding.Space (N × N) Z))
    (e : Joint Ω (SparseFlagEmbedding.Space (N × N) Z) →L[ℂ] SysGarb N G),
    ‖φ₀‖ ≤ 1 → e† ∘L e = 1 →
    (∀ x, TraceDistanceLE (systemState e (p.eval x φ₀))
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x)) ψin) ε) →
    b ≤ p.labelCount .value ∧ b ≤ p.count

/-- A value-query bound is also a bound on all primitive queries. -/
theorem le_count_of_le_labelCount {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {s : ℕ} {D : Data X N Z s} {Ω : Type u} [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω D)) {b : ℝ}
    (h : b ≤ p.labelCount .value) : b ≤ p.count :=
  h.trans (by exact_mod_cast labelCount_le_count p .value)

/-- A family that does not force `b` has a cheap accurate algorithm. -/
theorem exists_cheap_of_not_forces {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {s : ℕ} {D : Data X N Z s} {ψin : EuclideanSpace ℂ N} {t ε b : ℝ}
    (h : ¬ ForcesSimulation.{u, v} D ψin t ε b) :
    ∃ (Ω : Type u) (_ : Fintype Ω) (G : Type v) (_ : NormedAddCommGroup G)
      (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
      (p : MultiOracleCircuit.Program (specOracles Ω D))
      (φ₀ : Joint Ω (SparseFlagEmbedding.Space (N × N) Z))
      (e : Joint Ω (SparseFlagEmbedding.Space (N × N) Z) →L[ℂ] SysGarb N G),
      ‖φ₀‖ ≤ 1 ∧ e† ∘L e = 1 ∧
      (∀ x, TraceDistanceLE (systemState e (p.eval x φ₀))
        (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          SparseStateOverlap.matrixOperator (D.matrix x)) ψin) ε) ∧
      (p.labelCount .value : ℝ) < b := by
  by_contra hc
  apply h
  intro Ω _ G _ _ _ p φ₀ e hφ he hacc
  have hb : b ≤ p.labelCount .value := by
    by_contra hlt
    exact hc ⟨Ω, inferInstance, G, inferInstance, inferInstance, inferInstance, p, φ₀, e, hφ, he,
      hacc, not_le.mp hlt⟩
  exact ⟨hb, le_count_of_le_labelCount p hb⟩

/-- `r = L/h` of the package is the manuscript's `r`. -/
theorem hsR_eq_hslR (τ ε : ℝ) : hsR τ ε = hslR τ ε := rfl

set_option maxHeartbeats 4000000 in
/-- **Theorem `hsl:thm:main`** (eq. `hsl:eq:main`). Let `τ ≥ 1`, let the
integer sparsity satisfy `s ≥ 32`, and let `0 < ε ≤ 1/64`; `L = log(1/ε)`, `h = log(e + L/τ)`,
`r = L/h`. There is a hard family — native sparse data `D` with exact `B`-bit words and a known
unit initial state `ψ_in` — such that every algorithm of the model, accurate on every input, makes
at least `c₀ (√s τ + √(sτr) + r)` value queries, `c₀ = log 2/(4096π)`: the worst-case
sparse-query complexity obeys eq. `hsl:eq:main`. The hard matrices are those of the theorem
(`HardInstance`): real symmetric, with exact dyadic entries `v/2^B`, operator norm and maximum row
and column Euclidean norms exactly one (so `η = 1` and `τ = η|t|`), maximum row and column
sparsity exactly `s`, input-independent location lists and full in-place locator extensions; and
the dimension is at most `4s(τ + r + 1)` (`O(s(τ + r + 1))`). Formal restrictions: single programs,
uncontrolled calls; adaptive algorithms: `AdaptiveHamiltonianLowerBound.main_exists_tree`;
measured algorithms: `DeferredMeasurementLowerBounds.Corollaries.main_exists_measured`. (The
remark "with further known padding allowed" is `LowerBoundRemarks`.) -/
theorem hsl_thm_main {τ ε : ℝ} {s : ℕ} (hτ : 1 ≤ τ) (hs : 32 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    ∃ (X N : Type) (_ : Fintype N) (_ : DecidableEq N) (B : ℕ) (D : Data X N (Word B) s)
      (ψin : EuclideanSpace ℂ N),
      HardInstance D ∧ ‖ψin‖ = 1 ∧ (Fintype.card N : ℝ) ≤ 4 * s * (τ + hslR τ ε + 1) ∧
      ForcesSimulation.{u, v} D ψin τ ε
        (Real.log 2 / (4096 * Real.pi) *
          (Real.sqrt s * τ + Real.sqrt (s * τ * hslR τ ε) + hslR τ ε)) := by
  have h : HSRange τ s ε := ⟨hτ, hs, hε, hε1⟩
  obtain ⟨hIT, hIM, hIP, hcT, hcM, hcP⟩ := hard_instances h
  rcases main_exists.{u, v} h with hT | hM | hP
  · refine ⟨_, _, inferInstance, inferInstance, _, timeData τ s h.s_ge,
      searchInput (timeN τ) (hsMu s) s, hIT, norm_searchInput _ _ _, hcT, ?_⟩
    intro Ω _ G _ _ _ p φ₀ e hφ he hacc
    have hb := hT Ω G p φ₀ hφ e he fun x => accurate_of_traceDistanceLE (hacc x)
    exact ⟨hb, le_count_of_le_labelCount p hb⟩
  · refine ⟨_, _, inferInstance, inferInstance, _, mixedMainData τ ε s h.s_ge,
      searchInput (precN τ ε) (hsMu s) s, hIM, norm_searchInput _ _ _, hcM, ?_⟩
    intro Ω _ G _ _ _ p φ₀ e hφ he hacc
    have hb := hM Ω G p φ₀ hφ e he fun x => accurate_of_traceDistanceLE (hacc x)
    exact ⟨hb, le_count_of_le_labelCount p hb⟩
  · refine ⟨_, _, inferInstance, inferInstance, _, precisionMainData τ ε s h.s_ge,
      scalarInput (precN τ ε) s, hIP, norm_scalarInput _ _, hcP, ?_⟩
    intro Ω _ G _ _ _ p φ₀ e _ _ hacc
    have hb := hP Ω G p φ₀ e fun x => accurate_of_traceDistanceLE (hacc x)
    exact ⟨hb, le_count_of_le_labelCount p hb⟩

set_option maxHeartbeats 4000000 in
/-- **Corollary `hsl:cor:power`**: for any fixed `p < 1/2`, a uniform bound
`O(√s L^p + L)` at `τ = 1` is impossible, even with a fixed additional polylogarithmic factor
`(log s)^k`. Precisely: there are no constant `C` and thresholds `L₀`, `s₀` such that, for all
`s ≥ max(32, s₀)` and `0 < ε ≤ 1/64` with `L = log(1/ε) ≥ L₀`, every sparse Hermitian input of
the class (native sparse data of sparsity `s`, operator norm and row and column Euclidean norms at
most one) and every known unit initial state admit an algorithm of the model, accurate at time
`τ = 1`, with at most `C (√s L^p + L)(log s)^k` value queries. Formal restrictions: single
programs, uncontrolled calls (the input class here is the intersection of the operator-norm and
Euclidean-norm classes, which makes the statement stronger); no adaptive or measured form is
stated. -/
theorem hsl_cor_power {pw : ℝ} (hp : pw < 1 / 2) (k : ℕ) :
    ¬ ∃ (C L₀ : ℝ) (s₀ : ℕ), ∀ (s : ℕ) (ε : ℝ), 32 ≤ s → 0 < ε → ε ≤ 1 / 64 → s₀ ≤ s →
      L₀ ≤ logInv ε →
      ∀ (X N Z : Type) [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
        (D : Data X N Z s) (ψin : EuclideanSpace ℂ N),
        (∀ x, (D.matrix x).IsHermitian) →
        (∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) →
        (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) → (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) →
        ‖ψin‖ = 1 →
        ∃ (Ω : Type u) (_ : Fintype Ω) (G : Type v) (_ : NormedAddCommGroup G)
          (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
          (p : MultiOracleCircuit.Program (specOracles Ω D))
          (φ₀ : Joint Ω (SparseFlagEmbedding.Space (N × N) Z))
          (e : Joint Ω (SparseFlagEmbedding.Space (N × N) Z) →L[ℂ] SysGarb N G),
          ‖φ₀‖ ≤ 1 ∧ e† ∘L e = 1 ∧
          (∀ x, TraceDistanceLE (systemState e (p.eval x φ₀))
            (NormedSpace.exp ((-Complex.I * ((1 : ℝ) : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x)) ψin) ε) ∧
          (p.labelCount .value : ℝ) ≤
            C * (Real.sqrt s * logInv ε ^ pw + logInv ε) * Real.log s ^ k := by
  rintro ⟨C, L₀, s₀, hC⟩
  obtain ⟨s, ε, h, hL₀, hs₀, hcor⟩ := cor_power.{u, v} hp k C L₀ s₀
  have hI := (hard_instances h).2.1
  obtain ⟨Ω, _, G, _, _, _, p, φ₀, e, hφ, he, hacc, hle⟩ :=
    hC s ε h.s_ge h.eps_pos h.eps_le hs₀ hL₀ _ _ _ (mixedMainData 1 ε s h.s_ge)
      (searchInput (precN 1 ε) (hsMu s) s) hI.isHermitian (fun x => (hI.norm_eq_one x).le)
      hI.row_norm_le hI.col_norm_le (norm_searchInput _ _ _)
  exact absurd hle (not_le.mpr (hcor Ω G p φ₀ hφ e he fun x => accurate_of_traceDistanceLE (hacc x)))

set_option maxHeartbeats 8000000 in
/-- **Proposition `hsl:prop:two-norm`** (eq. `twonorml:eq:lower`). Let
`m ≥ 1` and `s₀ ≥ 32` be integers, let `μ > 0` be dyadic, and set `s = m s₀`, `η = μ√m`,
`θ = μm|t| = η²|t|/μ ≥ 1`, `L = log(1/ε)`, `r_μ = L/log(e + L/θ)`. For `0 < ε ≤ 1/64` there are
real symmetric dyadic Hamiltonians (`TwoNormInstance D c m` with `|c| = μ`, and entries
`(M v)/2^{B+q}` for `μ = M/2^q`) with maximum sparsity exactly `s`, maximum entry magnitude exactly
`μ` and maximum row and column Euclidean norms exactly `η`, and input-independent location lists
and full in-place extensions, requiring `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ)` queries,
`c₀ = log 2/(4096π)`, for the known-input system trace-distance guarantee of eq. `hsl:eq:accuracy`
(mixed outputs allowed, no postselection). Formal restrictions: single programs, uncontrolled calls
(the spectator register `ℂ^Ω` ranges over `Ω : Type`, the package's two-norm endpoint being stated
in that universe); adaptive protocols: `OptimalLowerBounds.two_norm_main_max_tree`; measured
algorithms: `OptimalLowerBounds.two_norm_main_max_measured`. -/
theorem hsl_prop_two_norm {m s₀ : ℕ} {μ t ε : ℝ} (hm : 1 ≤ m) (hs₀ : 32 ≤ s₀) (hμ : 0 < μ)
    (hdy : ∃ (M : ℤ) (q : ℕ), μ = M / 2 ^ q) (hθ : 1 ≤ μ * m * |t|) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    ∃ (X N : Type) (_ : Fintype N) (_ : DecidableEq N) (B : ℕ) (c : ℝ)
      (D : Data X N (Word B) (s₀ * m)) (ψin : EuclideanSpace ℂ N),
      OptimalLowerBounds.TwoNormInstance D c m ∧ |c| = μ ∧
      (∀ x i j, ∃ (v : ℤ) (q : ℕ), D.matrix x i j = (v : ℂ) / 2 ^ q) ∧ ‖ψin‖ = 1 ∧
      ForcesSimulation.{0, v} D ψin t ε
        (Real.log 2 / (4096 * Real.pi) *
          (Real.sqrt ((s₀ * m : ℕ) : ℝ) * (μ * Real.sqrt m) * |t| +
            Real.sqrt ((s₀ * m : ℕ) * μ * |t| * hslR (μ * m * |t|) ε) +
            hslR (μ * m * |t|) ε)) := by
  have ht : t ≠ 0 := by
    rintro rfl
    norm_num at hθ
  have hm0 : 0 < m := hm
  obtain ⟨c, hc, hcμ, hcθ⟩ := OptimalLowerBounds.exists_coeff hμ ht m
  have h : HSRange (μ * m * |t|) s₀ ε := ⟨hθ, hs₀, hε, hε1⟩
  obtain ⟨hIT, hIM, hIP⟩ := OptimalLowerBounds.two_instances (m := m) (c := c) h hm0 hc
  obtain ⟨M, q, hMq⟩ := hdy
  -- the sign of `c` is that of `t`; `c = ±M/2^q` is dyadic
  have hcd : ∃ M' : ℤ, c = M' / 2 ^ q := by
    rcases abs_choice c with hca | hca
    · exact ⟨M, by rw [← hca, hcμ, hMq]⟩
    · exact ⟨-M, by rw [show c = -|c| by linarith, hcμ, hMq]; push_cast; ring⟩
  obtain ⟨M', hM'⟩ := hcd
  have hdyad : ∀ {X N : Type} [Fintype N] [DecidableEq N] {B s' : ℕ}
      {D : Data X N (Word B) s'}, OptimalLowerBounds.TwoNormInstance D c m →
      ∀ x i j, ∃ (v : ℤ) (q' : ℕ), D.matrix x i j = (v : ℂ) / 2 ^ q' := by
    intro X N _ _ B s' D hD x i j
    obtain ⟨v, hv⟩ := hD.dyadic_entries hM' x i j
    exact ⟨M' * v, B + q, hv⟩
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Real.log 2 / (4096 * Real.pi) *
      (Real.sqrt ((s₀ * m : ℕ) : ℝ) * (μ * Real.sqrt m) * |t| +
        Real.sqrt ((s₀ * m : ℕ) * μ * |t| * hslR (μ * m * |t|) ε) + hslR (μ * m * |t|) ε) :=
    ⟨_, rfl⟩
  rw [← hbdef]
  have hbc : b = c0 * (Real.sqrt ((s₀ * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
      Real.sqrt ((s₀ * m : ℕ) * |c| * |t| * hsR (μ * m * |t|) ε) + hsR (μ * m * |t|) ε) := by
    rw [hbdef, hcμ]
    rfl
  -- the classical step from the max form to the family form
  have key : ForcesSimulation.{0, v} (OptimalLowerBounds.timeTwo (μ * m * |t|) s₀ h.s_ge m hm0 c hc)
        (OptimalLowerBounds.embedU m (searchInput (timeN (μ * m * |t|)) (hsMu s₀) s₀)) t ε b ∨
      ForcesSimulation.{0, v}
        (OptimalLowerBounds.mixedTwo (μ * m * |t|) ε s₀ h.s_ge m hm0 c hc)
        (OptimalLowerBounds.embedU m (searchInput (precN (μ * m * |t|) ε) (hsMu s₀) s₀)) t ε b ∨
      ForcesSimulation.{0, v}
        (OptimalLowerBounds.precisionTwo (μ * m * |t|) ε s₀ h.s_ge m hm0 c hc)
        (OptimalLowerBounds.embedU m (scalarInput (precN (μ * m * |t|) ε) s₀)) t ε b := by
    by_contra hneg
    rw [not_or, not_or] at hneg
    obtain ⟨ΩT, _, GT, _, _, _, pT, φT, eT, hφT, heT, haccT, hT⟩ := exists_cheap_of_not_forces hneg.1
    obtain ⟨ΩM, _, GM, _, _, _, pM, φM, eM, hφM, heM, haccM, hM⟩ :=
      exists_cheap_of_not_forces hneg.2.1
    obtain ⟨ΩP, _, GP, _, _, _, pP, φP, eP, -, -, haccP, hP⟩ := exists_cheap_of_not_forces hneg.2.2
    have hmax := OptimalLowerBounds.two_norm_main_max h hm0 hc hcθ ΩT ΩM ΩP pT φT hφT eT heT
      (fun x => accurate_of_traceDistanceLE (haccT x)) pM φM hφM eM heM
      (fun x => accurate_of_traceDistanceLE (haccM x)) pP φP eP
      (fun x => accurate_of_traceDistanceLE (haccP x))
    rw [← hbc] at hmax
    have := max_lt hT (max_lt hM hP)
    linarith
  rcases key with hk | hk | hk
  · exact ⟨_, _, inferInstance, inferInstance, _, c, _, _, hIT, hcμ, hdyad hIT,
      OptimalLowerBounds.norm_embedU_searchInput _ _ _ hm0, hk⟩
  · exact ⟨_, _, inferInstance, inferInstance, _, c, _, _, hIM, hcμ, hdyad hIM,
      OptimalLowerBounds.norm_embedU_searchInput _ _ _ hm0, hk⟩
  · exact ⟨_, _, inferInstance, inferInstance, _, c, _, _, hIP, hcμ, hdyad hIP,
      OptimalLowerBounds.norm_embedU_scalarInput _ _ hm0, hk⟩

end

end ManuscriptConformance
