import SparseLowerBounds.Hamiltonian.PrecisionFamily

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The three family bounds for the release's native primitives

Manuscript: the chain construction of Section `part:hsl` (two Boolean queries per value call,
location calls free), Lemmas `hsl:lem:mixed`, `hsl:lem:precision` and `hsl:lem:time`
(eq. `hsl:eq:timelower`), for programs over
the release's native primitives of the hard data
(`NativeSparseBlockEncoding.oracles`: in-place row and column location oracles
and the value oracle, inverses included), without or with an untouched
spectator register (`specOracles`).

* `implementsOn_searchData(_spec)`, `implementsOn_scalarData(_spec)`: the
  generic compilation `Hamiltonian/Compile` specialised to the hard data; the
  Boolean oracle is `oneHotOracle` (search) or `bitOracle` (scalar) of the
  address family, by `rfl`.
* `time_native/_spec`: `Q ≥ c_T √s τ` (eq. `hsl:eq:timelower`);
* `mixed_native/_spec`: `Q ≥ (log 2/96) √(m n τ)` (eq. `hsl:eq:mixedlower`);
* `precision_native/_spec`: `Q ≥ n/4` (eq. `hsl:eq:precisionlower`);

where `Q = p.labelCount .value` (and hence also `p.count`), since
`p.cost hardCost = 2 Q` (`cost_hardCost`).

Each native bound is the corresponding general bound of
`Hamiltonian/SearchFamily` / `Hamiltonian/PrecisionFamily` with Boolean family
`searchBoolean …` / `scalarBoolean …` (or the spectator versions), encoding
`ancillaEmbed _` (`ancillaEmbed_isometry`), labelled family `oracles D`
(`oracles_unitary`) or `specOracles Ω D` (`specOracles_unitary`), costs
`hardCost` and `implementsOn_*Data(_spec)`. The targets agree by `rfl`:
`(timeData τ s hs).matrix j` and `(searchData n μ s 1 τ hμ hs).matrix j` are
`searchHam … j`, and `(scalarData n s τ hs).matrix x` is `scalarHam n s τ x`
(`searchData_matrix`, `scalarData_matrix`). The Boolean cost bound
`2 b ≤ p.cost hardCost` then becomes `b ≤ Q ≤ p.count`
(`native_bound_of_cost`).
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

/-! ### Compilation of the hard data -/

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- The Boolean family of the search data (one-hot address family with ancilla). -/
abbrev searchBoolean (n μ s : ℕ) (a τ : ℝ) :=
  bitBooleanFamily (searchTable n μ s a τ) (Word (searchBits n μ s a τ))

/-- The same with a spectator register. -/
abbrev searchSpecBoolean (Ω : Type*) [Fintype Ω] (n μ s : ℕ) (a τ : ℝ) :=
  bitSpecFamily Ω (searchTable n μ s a τ) (Word (searchBits n μ s a τ))

/-- The Boolean family of the scalar data (bit address family with ancilla). -/
abbrev scalarBoolean (n s : ℕ) (τ : ℝ) :=
  bitBooleanFamily (scalarTable n s τ) (Word (scalarBits n s τ))

/-- The same with a spectator register. -/
abbrev scalarSpecBoolean (Ω : Type*) [Fintype Ω] (n s : ℕ) (τ : ℝ) :=
  bitSpecFamily Ω (scalarTable n s τ) (Word (scalarBits n s τ))

variable {n μ s : ℕ} {a τ ε : ℝ}

/-- The native primitives of the search data are `hardCost`-query programs over
`oneHotOracle (searchBoolean …)` (the chain construction of Section `part:hsl`):
`implementsOn_bitData` with `y = oneHotBits`, whose phase oracle is `oneHotOracle` by definition. -/
theorem implementsOn_searchData (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (l : Query) :
    EncodedOracle.ImplementsOn (oneHotOracle (searchBoolean n μ s a τ))
      (oracles (searchData n μ s a τ hμ hs) l) (ancillaEmbed (SearchSpace n μ s a τ))
      (hardCost l) :=
  implementsOn_bitData _ _ _ _ _ _ _ _ _ _ l

/-- `implementsOn_searchData` with an untouched spectator register. -/
theorem implementsOn_searchData_spec (Ω : Type*) [Fintype Ω] (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s)
    (l : Query) :
    EncodedOracle.ImplementsOn (oneHotOracle (searchSpecBoolean Ω n μ s a τ))
      (specOracles Ω (searchData n μ s a τ hμ hs) l)
      (ancillaEmbed (Joint Ω (SearchSpace n μ s a τ))) (hardCost l) :=
  implementsOn_bitData_spec Ω _ _ _ _ _ _ _ _ _ _ l

/-- The native primitives of the scalar data are `hardCost`-query programs over
`bitOracle (scalarBoolean …)` (the chain construction of Section `part:hsl`): `implementsOn_bitData`
with `y x = x`, whose phase oracle is `bitOracle` by definition. -/
theorem implementsOn_scalarData (hs : 2 ≤ s) (l : Query) :
    EncodedOracle.ImplementsOn (bitOracle (scalarBoolean n s τ))
      (oracles (scalarData n s τ hs) l) (ancillaEmbed (ScalarSpace n s τ)) (hardCost l) :=
  implementsOn_bitData _ _ _ _ _ _ _ _ _ _ l

/-- `implementsOn_scalarData` with an untouched spectator register. -/
theorem implementsOn_scalarData_spec (Ω : Type*) [Fintype Ω] (hs : 2 ≤ s) (l : Query) :
    EncodedOracle.ImplementsOn (bitOracle (scalarSpecBoolean Ω n s τ))
      (specOracles Ω (scalarData n s τ hs) l) (ancillaEmbed (Joint Ω (ScalarSpace n s τ)))
      (hardCost l) :=
  implementsOn_bitData_spec Ω _ _ _ _ _ _ _ _ _ _ l

/-! ### From Boolean cost to value queries -/

/-- **Two Boolean queries per value call** (the chain construction of Section `part:hsl`): a
Boolean-cost bound `2 b ≤ p.cost hardCost` is a bound `b` on the number of value queries, and hence
on the total count (`cost_hardCost`, `labelCount_le_count`). -/
theorem native_bound_of_cost {X W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {O : Query → X → W →L[ℂ] W} (p : MultiOracleCircuit.Program O) {b : ℝ}
    (h : 2 * b ≤ p.cost hardCost) : b ≤ p.labelCount .value ∧ b ≤ p.count := by
  rw [cost_hardCost] at h
  have hle : (p.labelCount .value : ℝ) ≤ p.count := by
    exact_mod_cast labelCount_le_count p .value
  push_cast at h
  constructor <;> linarith

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-! ### Time family (eq. `hsl:eq:timelower`) -/

/-- **The time lower bound** (Lemma `hsl:lem:time`) for the native primitives of the
time family: an `ε`-accurate algorithm (`ε ≤ 1/64`) makes at least
`c_T √s τ` value queries, `c_T = log 2/(192π)`. -/
theorem time_native (hτ : 1 ≤ τ) (hs : 32 ≤ s) (hε : ε ≤ 1 / 64)
    (p : MultiOracleCircuit.Program (oracles (timeData τ s hs)))
    (φ₀ : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((timeData τ s hs).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count := by
  have h := (time_general hτ hs hε
    (searchBoolean (timeN τ) (hsMu s) s (timeC τ) τ) (ancillaEmbed _)
    ancillaEmbed_isometry (oracles (timeData τ s hs)) (oracles_unitary _) hardCost
    (implementsOn_searchData (one_le_hsMu hs) (two_mul_hsM_le hs)) p φ₀ hφ₀ e he hacc).2
  exact native_bound_of_cost p (by linarith)

/-- `time_native` with an untouched spectator register `ℂ^Ω`. -/
theorem time_spec (Ω : Type*) [Fintype Ω] (hτ : 1 ≤ τ) (hs : 32 ≤ s) (hε : ε ≤ 1 / 64)
    (p : MultiOracleCircuit.Program (specOracles Ω (timeData τ s hs)))
    (φ₀ : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) →L[ℂ]
      SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((timeData τ s hs).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count := by
  have h := (time_general hτ hs hε
    (searchSpecBoolean Ω (timeN τ) (hsMu s) s (timeC τ) τ) (ancillaEmbed _)
    ancillaEmbed_isometry (specOracles Ω (timeData τ s hs)) (specOracles_unitary Ω _) hardCost
    (implementsOn_searchData_spec Ω (one_le_hsMu hs) (two_mul_hsM_le hs)) p φ₀ hφ₀ e he
    hacc).2
  exact native_bound_of_cost p (by linarith)

/-! ### Mixed family (Lemma `hsl:lem:mixed`) -/

/-- **Lemma `hsl:lem:mixed`** (Lemma `hsl:lem:mixed`) for the native primitives: for
`n ≥ 2`, `0 < τ ≤ n`, `m = 2^μ ≥ 16n/τ`, `2m ≤ s` and
`ε ≤ (τ/(2n))^n/8`, an `ε`-accurate algorithm makes at least
`(log 2/96) √(m n τ)` value queries (eq. `hsl:eq:mixedlower`). -/
theorem mixed_native (hn : 2 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n) (hm : 16 * n / τ ≤ (2 : ℝ) ^ μ)
    (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (p : MultiOracleCircuit.Program (oracles (searchData n μ s 1 τ hμ hs)))
    (φ₀ : SearchSpace n μ s 1 τ) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : SearchSpace n μ s 1 τ →L[ℂ] SysGarb (SearchIndex n μ s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((searchData n μ s 1 τ hμ hs).matrix j) τ (searchInput n μ s)) ε) :
    Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ μ * n * τ) ≤ p.labelCount .value ∧
      Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ μ * n * τ) ≤ p.count := by
  have h := mixed_general hn hτ hτn hm hε (searchBoolean n μ s 1 τ) (ancillaEmbed _)
    ancillaEmbed_isometry (oracles (searchData n μ s 1 τ hμ hs)) (oracles_unitary _) hardCost
    (implementsOn_searchData hμ hs) p φ₀ hφ₀ e he hacc
  exact native_bound_of_cost p (by linarith)

/-- `mixed_native` with an untouched spectator register `ℂ^Ω`. -/
theorem mixed_spec (Ω : Type*) [Fintype Ω] (hn : 2 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hm : 16 * n / τ ≤ (2 : ℝ) ^ μ) (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s)
    (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (p : MultiOracleCircuit.Program (specOracles Ω (searchData n μ s 1 τ hμ hs)))
    (φ₀ : Joint Ω (SearchSpace n μ s 1 τ)) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : Joint Ω (SearchSpace n μ s 1 τ) →L[ℂ] SysGarb (SearchIndex n μ s) G)
    (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((searchData n μ s 1 τ hμ hs).matrix j) τ (searchInput n μ s)) ε) :
    Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ μ * n * τ) ≤ p.labelCount .value ∧
      Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ μ * n * τ) ≤ p.count := by
  have h := mixed_general hn hτ hτn hm hε (searchSpecBoolean Ω n μ s 1 τ) (ancillaEmbed _)
    ancillaEmbed_isometry (specOracles Ω (searchData n μ s 1 τ hμ hs))
    (specOracles_unitary Ω _) hardCost (implementsOn_searchData_spec Ω hμ hs) p φ₀ hφ₀ e he hacc
  exact native_bound_of_cost p (by linarith)

/-! ### Precision family (Lemma `hsl:lem:precision`) -/

/-- **Lemma `hsl:lem:precision`** (Lemma `hsl:lem:precision`) for the native primitives:
for `n ≥ 1`, `0 < τ ≤ n`, `2 ≤ s` and `ε ≤ (τ/(2n))^n/8`, an `ε`-accurate
algorithm on the signed scalar family makes at least `n/4` value queries
(eq. `hsl:eq:precisionlower`). No seed or readout norm hypothesis is needed. -/
theorem precision_native (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n) (hs : 2 ≤ s)
    (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (p : MultiOracleCircuit.Program (oracles (scalarData n s τ hs))) (φ₀ : ScalarSpace n s τ)
    (e : ScalarSpace n s τ →L[ℂ] SysGarb (ScalarIndex n s) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((scalarData n s τ hs).matrix x) τ (scalarInput n s)) ε) :
    (n : ℝ) / 4 ≤ p.labelCount .value ∧ (n : ℝ) / 4 ≤ p.count := by
  have h := precision_general hn hτ hτn hε (scalarBoolean n s τ) (ancillaEmbed _)
    ancillaEmbed_isometry (oracles (scalarData n s τ hs)) (oracles_unitary _) hardCost
    (implementsOn_scalarData hs) p φ₀ e hacc
  exact native_bound_of_cost p (by linarith)

/-- `precision_native` with an untouched spectator register `ℂ^Ω`. -/
theorem precision_spec (Ω : Type*) [Fintype Ω] (hn : 1 ≤ n) (hτ : 0 < τ) (hτn : τ ≤ n)
    (hs : 2 ≤ s) (hε : ε ≤ (τ / (2 * n)) ^ n / 8)
    (p : MultiOracleCircuit.Program (specOracles Ω (scalarData n s τ hs)))
    (φ₀ : Joint Ω (ScalarSpace n s τ))
    (e : Joint Ω (ScalarSpace n s τ) →L[ℂ] SysGarb (ScalarIndex n s) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((scalarData n s τ hs).matrix x) τ (scalarInput n s)) ε) :
    (n : ℝ) / 4 ≤ p.labelCount .value ∧ (n : ℝ) / 4 ≤ p.count := by
  have h := precision_general hn hτ hτn hε (scalarSpecBoolean Ω n s τ) (ancillaEmbed _)
    ancillaEmbed_isometry (specOracles Ω (scalarData n s τ hs)) (specOracles_unitary Ω _)
    hardCost (implementsOn_scalarData_spec Ω hs) p φ₀ e hacc
  exact native_bound_of_cost p (by linarith)

end

end SparseLowerBounds.Hamiltonian
end
