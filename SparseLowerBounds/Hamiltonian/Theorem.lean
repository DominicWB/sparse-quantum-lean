import SparseLowerBounds.Hamiltonian.Native

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Theorem `hsl:thm:main`: the Hamiltonian-simulation query lower bound

Manuscript: Theorem `hsl:thm:main` (statement and remarks) and its proof (assembly; dimension
and exact sparsity at the end). Let `τ ≥ 1`, `s ≥ 32` and
`0 < ε ≤ 1/64` (`HSRange τ s ε`), `L = log(1/ε)`, `h = log(e + L/τ)`,
`r = L/h` (eq. `hsl:eq:parameters`).

**Algorithm model.** A
`MultiOracleCircuit.Program` over the release's native primitives of a hard
family (`NativeSparseBlockEncoding.oracles`: in-place row and column location
oracles and the value oracle, inverses included), without (`*_native`) or with
(`specOracles`) an untouched spectator register `ℂ^Ω`, run on an
input-independent seed `φ₀`, read through a fixed isometry `e` into
system ⊗ garbage. It is `ε`-accurate on input `X` if the system output is
within trace distance `ε` of `e^{-iτH_X} ψ_in`, in the observable form
`Readout.Accurate` (eq. `hsl:eq:accuracy`). `Q = p.labelCount .value` counts
value queries; location queries are free (they are input-independent).

**Controlled calls** (Section `hsl:sec:main` and the chain construction of Section `part:hsl`:
public locators, inverses and controls). `MultiOracleCircuit.Program` has no controlled primitive;
controlled calls are covered by reduction. A controlled location call is a fixed gate
(input-independent locators, `HardInstance.locators_const`): cost 0. A controlled value call is one
spectator value call between fixed controlled swaps that, on the inactive branch, route the word
register to a dummy `Word B` register in the uniform superposition `Σ_z |z⟩/√|Word B|`, invariant
under every shift `z ↦ z ∓ f a` (the release's `NativeControlledOracle.referenceSwap` pattern). So
`*_main`, `*_herald` and `*_endpoint` with spectator `Ω × Fin 2 × Word B` apply at cost 1 per
controlled value call; `*_native` does not. (Not stated here: an `ImplementsOn` lemma for a
controlled-value label at cost 2 via `PhaseCircuit.implementsOn_circuit`, for the `*_general`
forms.)

**Per-family bounds at the main parameters** (the three families of the
proof, as concrete native data from `Hamiltonian/HardData`):

* `time_main`: time family `timeData`, `Q ≥ c_T √s τ` (eq. `hsl:eq:timelower`);
* `mixed_main`: for `L ≥ 64τ` and `s ≥ 64n/τ`, mixed family `mixedMainData`,
  `Q ≥ (log 2/(384√2)) √(sτr)` (eq. `hsl:eq:mixrbound`);
* `precision_main`: for `L ≥ 64τ`, precision family `precisionMainData`,
  `Q ≥ r/32` (eq. `hsl:eq:rbound`), and `Q ≥ √(sτr)/(64√2)` when `s < 64n/τ`
  (eq. `hsl:eq:failedmix`);

and the same for programs without spectator (`*_main_native`).

**Hard instances** (`hard_instances`, Theorem `hsl:thm:main`): each
family's matrices are real symmetric with operator norm exactly one, maximum
row and column Euclidean norms exactly one (the release's `η = 1` promise),
maximum row and column sparsity exactly `s`, exact dyadic words with
position-independent decode, input-independent location lists and locator
extensions, and dimension at most `4 s (τ + r + 1)` (`HardInstance`).

**Combined statement** (eq. `hsl:eq:main`, `c₀ = log 2/(4096π)`). The manuscript uses that the
maximum of three nonnegative lower bounds is at least a third of their sum (Section `hsl:sec:main`):
the three terms are witnessed by different families. Combined quantification (a formalization
choice): the max form, which is what the manuscript proves, with the family form as an equivalent
statement:

* `main_max`: for any three algorithms, each accurate on its own
  family, `max(Q_T, Q_M, Q_P) ≥ c₀ (√s τ + √(sτr) + r)`;
* `main_exists`: equivalently, one of the three concrete families
  (chosen by the parameters) forces every accurate algorithm to make at least
  `c₀ (√s τ + √(sτr) + r)` value queries;
* `fixedtime_sum`: the sum at `τ = 1` (eq. `hsl:eq:fixedtime`).

The heralded extension (Lemma `odel:lem:herald`) is `Hamiltonian/Herald`; the
endpoint (release) form of the accuracy hypothesis is `Hamiltonian/ReleaseForm`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped Matrix InnerProduct InnerProductSpace

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

universe u v

variable {τ ε : ℝ} {s : ℕ} {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [CompleteSpace G]

/-! ### The hard instances -/

/-- Entries of a symmetric matrix: `Mᵀ = M` gives `M i j = M j i`. -/
theorem entry_symm_of_transpose {S : Type*} {M : Matrix S S ℂ} (hT : Mᵀ = M) (i j : S) :
    M i j = M j i := by
  have := congrFun (congrFun hT j) i
  rwa [Matrix.transpose_apply] at this

/-- A real symmetric complex matrix is Hermitian. -/
theorem isHermitian_of_realSymmetric {S : Type*} {M : Matrix S S ℂ}
    (hM : Mᵀ = M ∧ ∀ i j, star (M i j) = M i j) : M.IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, hM.2, entry_symm_of_transpose hM.1 j i]

/-- **The instance properties of Theorem `hsl:thm:main`** (Theorem `hsl:thm:main`) for native sparse
data with words `Word B`: real symmetric; operator norm exactly one; maximum row and column
Euclidean norms exactly one; maximum row and column sparsity exactly `s`; exact finite-word dyadic
entries (scale `1`, position-independent decode `valMinAbs z / 2^B`, every entry `v/2^B` with
`-2^B < v ≤ 2^B`); input-independent location lists and full in-place locator extensions. -/
structure HardInstance {X N : Type*} [Fintype N] [DecidableEq N] {B s : ℕ}
    (D : Data X N (Word B) s) : Prop where
  transpose_eq : ∀ x, (D.matrix x)ᵀ = D.matrix x
  real : ∀ x i j, star (D.matrix x i j) = D.matrix x i j
  isHermitian : ∀ x, (D.matrix x).IsHermitian
  norm_eq_one : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ = 1
  row_norm_le : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1
  col_norm_le : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1
  row_norm_attained : ∀ x, ∃ i, ∑ j, ‖D.matrix x i j‖ ^ 2 = 1
  col_norm_attained : ∀ x, ∃ j, ∑ i, ‖D.matrix x i j‖ ^ 2 = 1
  row_sparsity_le : ∀ x i, (Finset.univ.filter fun j => D.matrix x i j ≠ 0).card ≤ s
  col_sparsity_le : ∀ x j, (Finset.univ.filter fun i => D.matrix x i j ≠ 0).card ≤ s
  row_sparsity_attained : ∀ x, ∃ i, (Finset.univ.filter fun j => D.matrix x i j ≠ 0).card = s
  col_sparsity_attained : ∀ x, ∃ j, (Finset.univ.filter fun i => D.matrix x i j ≠ 0).card = s
  scale_eq : D.scale = 1
  decode_eq : ∀ a, D.decode a = wordDecode B
  dyadic : ∀ x i j, ∃ v : ℤ, -(2 : ℤ) ^ B < v ∧ v ≤ 2 ^ B ∧ D.matrix x i j = (v : ℂ) / 2 ^ B
  locators_const : ∀ x x', D.rowloc x = D.rowloc x' ∧ D.colloc x = D.colloc x' ∧
    D.rowOracle x = D.rowOracle x' ∧ D.columnOracle x = D.columnOracle x'

/-- The search-decorated data satisfy `HardInstance` for `0 ≤ a ≤ 1`. -/
theorem searchData_hardInstance {n μ : ℕ} {a : ℝ} (τ : ℝ) (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : HardInstance (searchData n μ s a τ hμ hs) := by
  have hP := fun j => searchHam_props (n := n) ha0 ha1 τ hs j
  have hR := fun j => searchHam_realSymmetric (n := n) (μ := μ) (s := s) a τ j
  refine
    { transpose_eq := fun j => (hR j).1
      real := fun j => (hR j).2
      isHermitian := fun j => isHermitian_of_realSymmetric (hR j)
      norm_eq_one := fun j => (hP j).1
      row_norm_le := fun j => (hP j).2.1
      col_norm_le := fun j => (hP j).2.2.1
      row_norm_attained := fun j => ⟨refOne, (hP j).2.2.2.1⟩
      col_norm_attained := fun j => ⟨refOne, ?_⟩
      row_sparsity_le := fun j => (hP j).2.2.2.2.1
      col_sparsity_le := fun j => (hP j).2.2.2.2.2.1
      row_sparsity_attained := fun j => (hP j).2.2.2.2.2.2.1
      col_sparsity_attained := fun j => (hP j).2.2.2.2.2.2.2
      scale_eq := rfl
      decode_eq := fun _ => rfl
      dyadic := fun j i i' =>
        ⟨(searchTable n μ s a τ).value (oneHotBits j) (i, i'),
          (searchTable_bound hμ (i, i') ((searchTable n μ s a τ).bit (oneHotBits j) (i, i'))).1,
          (searchTable_bound hμ (i, i') ((searchTable n μ s a τ).bit (oneHotBits j) (i, i'))).2,
          (searchTable_decode j i i').symm⟩
      locators_const := bitData_locators_const }
  calc ∑ i, ‖searchHam n μ s a τ j i refOne‖ ^ 2 = ∑ i, ‖searchHam n μ s a τ j refOne i‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [entry_symm_of_transpose (hR j).1 i refOne]
    _ = 1 := (hP j).2.2.2.1

/-- The signed scalar data satisfy `HardInstance`. -/
theorem scalarData_hardInstance {n : ℕ} (τ : ℝ) (hs : 2 ≤ s) :
    HardInstance (scalarData n s τ hs) := by
  have hP := fun x => scalarHam_props (n := n) τ hs x
  have hR := fun x => scalarHam_realSymmetric (n := n) (s := s) τ x
  refine
    { transpose_eq := fun x => (hR x).1
      real := fun x => (hR x).2
      isHermitian := fun x => isHermitian_of_realSymmetric (hR x)
      norm_eq_one := fun x => (hP x).1
      row_norm_le := fun x => (hP x).2.1
      col_norm_le := fun x => (hP x).2.2.1
      row_norm_attained := fun x => ⟨refOne, (hP x).2.2.2.1⟩
      col_norm_attained := fun x => ⟨refOne, ?_⟩
      row_sparsity_le := fun x => (hP x).2.2.2.2.1
      col_sparsity_le := fun x => (hP x).2.2.2.2.2.1
      row_sparsity_attained := fun x => (hP x).2.2.2.2.2.2.1
      col_sparsity_attained := fun x => (hP x).2.2.2.2.2.2.2
      scale_eq := rfl
      decode_eq := fun _ => rfl
      dyadic := fun x i i' =>
        ⟨(scalarTable n s τ).value x (i, i'),
          (scalarTable_bound (i, i') ((scalarTable n s τ).bit x (i, i'))).1,
          (scalarTable_bound (i, i') ((scalarTable n s τ).bit x (i, i'))).2,
          (scalarTable_decode x i i').symm⟩
      locators_const := bitData_locators_const }
  calc ∑ i, ‖scalarHam n s τ x i refOne‖ ^ 2 = ∑ i, ‖scalarHam n s τ x refOne i‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [entry_symm_of_transpose (hR x).1 i refOne]
    _ = 1 := (hP x).2.2.2.1

/-- The time family's clock length is at most `τ` for `τ ≥ 1` (dimension
bound, proof of Theorem `hsl:thm:main`). -/
theorem timeN_le (hτ : 1 ≤ τ) : (timeN τ : ℝ) ≤ τ := by
  unfold timeN
  rw [Nat.cast_max, Nat.cast_one]
  refine max_le hτ ?_
  have hπ := Real.pi_gt_three
  calc (⌊2 * τ / Real.pi⌋₊ : ℝ) ≤ 2 * τ / Real.pi :=
        Nat.floor_le (div_nonneg (by linarith) Real.pi_pos.le)
    _ ≤ τ := by rw [div_le_iff₀ Real.pi_pos]; nlinarith

/-- **Theorem `hsl:thm:main`, hard instances** (Theorem `hsl:thm:main`): the three families at the
main parameters satisfy `HardInstance`, and their dimensions are at most `4 s (τ + r + 1)`
(`O(s(τ + r + 1))`, made explicit). -/
theorem hard_instances (h : HSRange τ s ε) :
    HardInstance (timeData τ s h.s_ge) ∧ HardInstance (mixedMainData τ ε s h.s_ge) ∧
      HardInstance (precisionMainData τ ε s h.s_ge) ∧
      (Fintype.card (SearchIndex (timeN τ) (hsMu s) s) : ℝ) ≤ 4 * s * (τ + hsR τ ε + 1) ∧
      (Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) : ℝ) ≤ 4 * s * (τ + hsR τ ε + 1) ∧
      (Fintype.card (ScalarIndex (precN τ ε) s) : ℝ) ≤ 4 * s * (τ + hsR τ ε + 1) := by
  have hτ := h.one_le_tau
  have hr := h.hsR_pos
  have hs : (32 : ℝ) ≤ s := by exact_mod_cast h.s_ge
  have hm := (hsM_range h.s_ge).2.2
  have hm0 : (0 : ℝ) ≤ 2 ^ hsMu s := by positivity
  have hsτ : 0 ≤ (s : ℝ) * τ := by nlinarith
  have hsr : 0 ≤ (s : ℝ) * hsR τ ε := by nlinarith
  have hpn := h.precN_le_quarter
  refine ⟨searchData_hardInstance τ _ _ (timeC_pos (by linarith)).le (timeC_le_one τ),
    searchData_hardInstance τ _ _ zero_le_one le_rfl, scalarData_hardInstance τ _, ?_, ?_, ?_⟩
  · rw [card_searchIndex]
    push_cast
    have h1 : ((timeN τ : ℝ) + 1) * 2 ^ hsMu s ≤ (τ + 1) * (s / 2) :=
      mul_le_mul (by linarith [timeN_le hτ]) hm hm0 (by linarith)
    nlinarith
  · rw [card_searchIndex]
    push_cast
    have h1 : ((precN τ ε : ℝ) + 1) * 2 ^ hsMu s ≤ (hsR τ ε / 4 + 1) * (s / 2) :=
      mul_le_mul (by linarith) hm hm0 (by linarith)
    nlinarith
  · rw [card_scalarIndex]
    push_cast
    nlinarith

/-! ### The three families at the main parameters -/

/-- **Time family** (Lemma `hsl:lem:time`, eq. `hsl:eq:timelower`), spectator form:
an `ε`-accurate algorithm makes at least `c_T √s τ` value queries,
`c_T = log 2/(192π)`. -/
theorem time_main (h : HSRange τ s ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (timeData τ s h.s_ge)))
    (φ₀ : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count :=
  time_spec Ω h.one_le_tau h.s_ge h.eps_le p φ₀ hφ₀ e he hacc

/-- **Mixed family** (proof of Theorem `hsl:thm:main`, eq. `hsl:eq:mixrbound`), spectator
form: if `L ≥ 64τ` and `s ≥ 64n/τ` (`n = ⌊r/4⌋`), an `ε`-accurate algorithm
makes at least `(log 2/(384√2)) √(sτr)` value queries. -/
theorem mixed_main (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (mixedMainData τ ε s h.s_ge)))
    (φ₀ : Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hmix := mixed_spec (n := precN τ ε) (μ := hsMu s) (s := s) (τ := τ) (ε := ε) Ω hn
    (by linarith [h.one_le_tau]) (by linarith) (mixed_m_cond h hs) (one_le_hsMu h.s_ge)
    (two_mul_hsM_le h.s_ge) (by linarith [h.eps_pos]) p φ₀ hφ₀ e he hacc
  have hnum := mixrbound h hL
  exact ⟨hnum.trans hmix.1, hnum.trans hmix.2⟩

/-- **Precision family** (proof of Theorem `hsl:thm:main`, eqs. `hsl:eq:rbound`,
`hsl:eq:failedmix`), spectator form: if `L ≥ 64τ`, an `ε`-accurate algorithm
makes at least `r/32` value queries, and at least `√(sτr)/(64√2)` when
`s < 64n/τ`. No seed or readout norm hypothesis is needed. -/
theorem precision_main (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (precisionMainData τ ε s h.s_ge)))
    (φ₀ : Joint Ω (ScalarSpace (precN τ ε) s τ))
    (e : Joint Ω (ScalarSpace (precN τ ε) s τ) →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    hsR τ ε / 32 ≤ p.labelCount .value ∧ hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hP := precision_spec (n := precN τ ε) (s := s) (τ := τ) (ε := ε) Ω (by omega)
    (by linarith [h.one_le_tau]) (by linarith) (le_trans (by norm_num) h.s_ge)
    (by linarith [h.eps_pos]) p φ₀ e hacc
  have hrb := rbound h hL
  exact ⟨hrb.trans hP.1, hrb.trans hP.2, fun hs' => (failedmix h hL hs').trans hP.1⟩

/-- `time_main` for programs over the native primitives (no spectator). -/
theorem time_main_native (h : HSRange τ s ε)
    (p : MultiOracleCircuit.Program (oracles (timeData τ s h.s_ge)))
    (φ₀ : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count :=
  time_native h.one_le_tau h.s_ge h.eps_le p φ₀ hφ₀ e he hacc

/-- `mixed_main` for programs over the native primitives (no spectator). -/
theorem mixed_main_native (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    (p : MultiOracleCircuit.Program (oracles (mixedMainData τ ε s h.s_ge)))
    (φ₀ : SearchSpace (precN τ ε) (hsMu s) s 1 τ) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : SearchSpace (precN τ ε) (hsMu s) s 1 τ →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hmix := mixed_native (n := precN τ ε) (μ := hsMu s) (s := s) (τ := τ) (ε := ε) hn
    (by linarith [h.one_le_tau]) (by linarith) (mixed_m_cond h hs) (one_le_hsMu h.s_ge)
    (two_mul_hsM_le h.s_ge) (by linarith [h.eps_pos]) p φ₀ hφ₀ e he hacc
  have hnum := mixrbound h hL
  exact ⟨hnum.trans hmix.1, hnum.trans hmix.2⟩

/-- `precision_main` for programs over the native primitives (no spectator). -/
theorem precision_main_native (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (p : MultiOracleCircuit.Program (oracles (precisionMainData τ ε s h.s_ge)))
    (φ₀ : ScalarSpace (precN τ ε) s τ)
    (e : ScalarSpace (precN τ ε) s τ →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    hsR τ ε / 32 ≤ p.labelCount .value ∧ hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hP := precision_native (n := precN τ ε) (s := s) (τ := τ) (ε := ε) (by omega)
    (by linarith [h.one_le_tau]) (by linarith) (le_trans (by norm_num) h.s_ge)
    (by linarith [h.eps_pos]) p φ₀ e hacc
  have hrb := rbound h hL
  exact ⟨hrb.trans hP.1, hrb.trans hP.2, fun hs' => (failedmix h hL hs').trans hP.1⟩

/-! ### Combined statement -/

/-- **Theorem `hsl:thm:main`, eq. `hsl:eq:main`, max form**: for any three algorithms (spectator
form), accurate on the time, mixed and precision families respectively,
`max(Q_T, Q_M, Q_P) ≥ c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. The
mixed algorithm is only used when `L ≥ 64τ` and `s ≥ 64n/τ`, the precision
algorithm only when `L ≥ 64τ`. -/
theorem main_max (h : HSRange τ s ε) (ΩT ΩM ΩP : Type*)
    [Fintype ΩT] [Fintype ΩM] [Fintype ΩP] {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (specOracles ΩT (timeData τ s h.s_ge)))
    (φT : Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hφT : ‖φT‖ ≤ 1)
    (eT : Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (pM : MultiOracleCircuit.Program (specOracles ΩM (mixedMainData τ ε s h.s_ge)))
    (φM : Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hφM : ‖φM‖ ≤ 1)
    (eM : Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
      SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (pP : MultiOracleCircuit.Program (specOracles ΩP (precisionMainData τ ε s h.s_ge)))
    (φP : Joint ΩP (ScalarSpace (precN τ ε) s τ))
    (eP : Joint ΩP (ScalarSpace (precN τ ε) s τ) →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  refine assembly h (time_main h ΩT pT φT hφT eT heT haccT).1 (fun hL => ?_) (fun hL hs => ?_)
  · have := precision_main h hL ΩP pP φP eP haccP
    exact ⟨this.1, this.2.2⟩
  · exact (mixed_main h hL hs ΩM pM φM hφM eM heM haccM).1

/-- **Theorem `hsl:thm:main`, eq. `hsl:eq:main`, family form**:
for every parameter triple, one of the three concrete hard families (time,
mixed or precision, chosen by the parameters) forces **every** `ε`-accurate
algorithm (spectator form, any spectator `Ω : Type u`, any garbage
`G : Type v`) to make at least `c₀ (√s τ + √(sτr) + r)` value queries.
Derived from `main_max`; conversely it implies the max form for
algorithms in these universes. -/
theorem main_exists (h : HSRange τ s ε) :
    (∀ (Ω : Type u) [Fintype Ω] (G : Type v) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
        [CompleteSpace G] (p : MultiOracleCircuit.Program (specOracles Ω (timeData τ s h.s_ge)))
        (φ₀ : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)), ‖φ₀‖ ≤ 1 →
        ∀ e : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
          SysGarb (SearchIndex (timeN τ) (hsMu s) s) G, e† ∘L e = 1 →
        (∀ j, Accurate e (p.eval j φ₀)
          (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ p.labelCount .value) ∨
    (∀ (Ω : Type u) [Fintype Ω] (G : Type v) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
        [CompleteSpace G] (p : MultiOracleCircuit.Program (specOracles Ω (mixedMainData τ ε s h.s_ge)))
        (φ₀ : Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ)), ‖φ₀‖ ≤ 1 →
        ∀ e : Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ) →L[ℂ]
          SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G, e† ∘L e = 1 →
        (∀ j, Accurate e (p.eval j φ₀)
          (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ
            (searchInput (precN τ ε) (hsMu s) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ p.labelCount .value) ∨
    (∀ (Ω : Type u) [Fintype Ω] (G : Type v) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
        [CompleteSpace G]
        (p : MultiOracleCircuit.Program (specOracles Ω (precisionMainData τ ε s h.s_ge)))
        (φ₀ : Joint Ω (ScalarSpace (precN τ ε) s τ))
        (e : Joint Ω (ScalarSpace (precN τ ε) s τ) →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G),
        (∀ x, Accurate e (p.eval x φ₀)
          (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) →
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ p.labelCount .value) := by
  by_contra hneg
  push Not at hneg
  obtain ⟨⟨ΩT, _, GT, _, _, _, pT, φT, hφT, eT, heT, haccT, hT⟩,
    ⟨ΩM, _, GM, _, _, _, pM, φM, hφM, eM, heM, haccM, hM⟩,
    ⟨ΩP, _, GP, _, _, _, pP, φP, eP, haccP, hP⟩⟩ := hneg
  have hmax := main_max h ΩT ΩM ΩP pT φT hφT eT heT haccT pM φM hφM eM heM haccM
    pP φP eP haccP
  have := max_lt hT (max_lt hM hP)
  linarith

/-- **Eq. `hsl:eq:fixedtime`** (Section `part:hsl`): at `τ = 1` the sum of
eq. `hsl:eq:main` is `√s + √(sL/log(e+L)) + L/log(e+L)`. This is only the
algebraic identity: the `Ω`-bound of eq. `hsl:eq:fixedtime` is
`main_max` (or `main_exists`) at `τ = 1` rewritten by
it. -/
theorem fixedtime_sum (ε : ℝ) (s : ℕ) :
    Real.sqrt s * 1 + Real.sqrt (s * 1 * hsR 1 ε) + hsR 1 ε =
      Real.sqrt s + Real.sqrt (s * hsL ε / Real.log (Real.exp 1 + hsL ε)) +
        hsL ε / Real.log (Real.exp 1 + hsL ε) := by
  simp only [hsR, hsH, div_one, mul_one, mul_div_assoc]

end

end SparseLowerBounds.Hamiltonian
end
