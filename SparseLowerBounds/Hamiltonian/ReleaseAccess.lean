import SparseLowerBounds.Helpers.HsRelease.Layers

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The release simulator's oracles on the hard families are Boolean-implementable

The lemma named in the module docstring of `Hamiltonian/ReleaseForm`. Manuscript: Section
`hsl:sec:main` (the native sparse access of Section `sec:overview`, "allowing all location
operations, known gates and state preparation for free"), the chain construction of Section
`part:hsl` (two Boolean queries per value call) and the comparison after Theorem `hsl:thm:main` with
the baseline upper bound eq. `hsl:eq:upper` of the release simulator, in the same access model.

The release's simulator (`ImprovedSparseHamiltonian.simulation_log_one`,
`SparseHamiltonian/ManuscriptPrecision.lean`) is a
`MultiOracleCircuit.Program` over the physical family
`ImprovedSparseHamiltonian.oracle D γ η t δ`, labelled by
`NativeSparseBlockEncoding.Query`, on
`ImprovedSparseHamiltonian.Physical n Z s γ η t δ`. By the unfolding recorded in
`Helpers/HsRelease/Layers`, **every label `l` of this family is exactly one
call of the native primitive `oracles D l` of the same label**, inside
untouched spectator registers (clean-output alignment `Bool`, chronological
cells `ActiveRegisterLayout.Label PUnit T d`, control/dummy/reference
registers, Hermitian-dilation branch `Bool`) and fixed register relabellings.
No label wraps several native calls. Hence the per-label Boolean weight is

  `hardCost l` = `2` for `.value` (query bit, add word, unquery; the chain construction of Section
  `part:hsl`), `0` for `.rowLocation` and `.columnLocation` (input-independent permutation
  unitaries, the chain construction of Section `part:hsl`),

i.e. 2 per native value query inside the label and 0 for its input-independent
parts, exactly as for programs over the bare native primitives
(`Hamiltonian/Native`).

**Encoding and Boolean oracle.** The encoding `E` is the clean-ancilla encoding
of the native certificates (`ancillaEmbed`: `v ↦ |0⟩ ⊗ v` on the native workspace), placed in every
spectator copy and composed with the inverses of the fixed relabellings
(`PhaseAccess.conj`, `PhaseAccess.spectate`): `E = (1 ⊗ ⋯ ⊗ 1 ⊗ ancillaEmbed) ∘ V⁻¹`.
The Boolean oracle is the XOR oracle of the queried bit in phase form
(`bitBooleanFamily`, i.e. `|−⟩⟨−| ⊗ Π_i`) on every spectator copy: `oneHotOracle`
for the search families (time, mixed), `bitOracle` for the precision family.

Contents:

* `searchAccess`, `scalarAccess`: the native certificates
  (`implementsOn_searchData`, `implementsOn_scalarData`) as `PhaseAccess`;
* `searchReleaseAccess`, `scalarReleaseAccess`: their transport to
  `ImprovedSparseHamiltonian.oracle` (`HsRelease.releaseAccess`), any `γ η t δ`;
* `timeReleaseAccess`, `mixedReleaseAccess`, `precisionReleaseAccess`: the
  three hard families at the main parameters (`timeData`, `mixedMainData`,
  `precisionMainData`);
* `TimePhys`, `MixedPhys`, `PrecisionPhys`: the release's physical workspaces
  of the three families;
* **`time_release_implementsOn`, `mixed_release_implementsOn`,
  `precision_release_implementsOn`**: isometric encoding
  and `EncodedOracle.ImplementsOn (oneHotOracle P)` (resp. `bitOracle P`) of
  every label at cost `hardCost l`, in exactly the form of the hypotheses `hE`,
  `hw` of `time_general`, `mixed_general`, `precision_general` and
  `*_herald_general`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit HsRelease
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

variable {n μ s : ℕ} {a τ ε : ℝ}

/-! ### Native certificates -/

/-- The native primitives of the search data as a one-hot phase-access
certificate with costs `hardCost` (`implementsOn_searchData`). -/
def searchAccess (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) :
    PhaseAccess (Fin n × Fin (2 ^ μ)) oneHotPattern (oracles (searchData n μ s a τ hμ hs))
      hardCost :=
  PhaseAccess.ofImplementsOn (searchBoolean n μ s a τ) (ancillaEmbed _) ancillaEmbed_isometry
    (implementsOn_searchData hμ hs)

/-- The native primitives of the scalar data as a bit phase-access certificate
with costs `hardCost` (`implementsOn_scalarData`). -/
def scalarAccess (hs : 2 ≤ s) :
    PhaseAccess (Fin n) bitPattern (oracles (scalarData n s τ hs)) hardCost :=
  PhaseAccess.ofImplementsOn (scalarBoolean n s τ) (ancillaEmbed _) ancillaEmbed_isometry
    (implementsOn_scalarData hs)

/-! ### The release oracle on the search and scalar data -/

/-- The release simulator's oracle family on the search data, costs `hardCost`. -/
def searchReleaseAccess (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s) (γ η t δ : ℝ) :
    PhaseAccess (Fin n × Fin (2 ^ μ)) oneHotPattern
      (ImprovedSparseHamiltonian.oracle (searchData n μ s a τ hμ hs) γ η t δ) hardCost :=
  releaseAccess _ (searchAccess hμ hs) γ η t δ

/-- The release simulator's oracle family on the scalar data, costs `hardCost`. -/
def scalarReleaseAccess (hs : 2 ≤ s) (γ η t δ : ℝ) :
    PhaseAccess (Fin n) bitPattern
      (ImprovedSparseHamiltonian.oracle (scalarData n s τ hs) γ η t δ) hardCost :=
  releaseAccess _ (scalarAccess hs) γ η t δ

/-! ### The three hard families at the main parameters -/

/-- Time family (`timeData`): the release oracle's certificate. -/
def timeReleaseAccess (hs : 32 ≤ s) (γ η t δ : ℝ) :
    PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern
      (ImprovedSparseHamiltonian.oracle (timeData τ s hs) γ η t δ) hardCost :=
  searchReleaseAccess (one_le_hsMu hs) (two_mul_hsM_le hs) γ η t δ

/-- Mixed family (`mixedMainData`): the release oracle's certificate. -/
def mixedReleaseAccess (hs : 32 ≤ s) (γ η t δ : ℝ) :
    PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern
      (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s hs) γ η t δ) hardCost :=
  searchReleaseAccess (one_le_hsMu hs) (two_mul_hsM_le hs) γ η t δ

/-- Precision family (`precisionMainData`): the release oracle's certificate. -/
def precisionReleaseAccess (hs : 32 ≤ s) (γ η t δ : ℝ) :
    PhaseAccess (Fin (precN τ ε)) bitPattern
      (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s hs) γ η t δ) hardCost :=
  scalarReleaseAccess (by omega) γ η t δ

/-- The release's physical workspace for the time family
(`ImprovedSparseHamiltonian.Physical`, schedule parameters `γ η t δ`). -/
abbrev TimePhys (τ : ℝ) (s : ℕ) (γ η t δ : ℝ) : Type :=
  ImprovedSparseHamiltonian.Physical (SearchIndex (timeN τ) (hsMu s) s)
    (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s γ η t δ

/-- The release's physical workspace for the mixed family. -/
abbrev MixedPhys (τ ε : ℝ) (s : ℕ) (γ η t δ : ℝ) : Type :=
  ImprovedSparseHamiltonian.Physical (SearchIndex (precN τ ε) (hsMu s) s)
    (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s γ η t δ

/-- The release's physical workspace for the precision family. -/
abbrev PrecisionPhys (τ ε : ℝ) (s : ℕ) (γ η t δ : ℝ) : Type :=
  ImprovedSparseHamiltonian.Physical (ScalarIndex (precN τ ε) s)
    (Word (scalarBits (precN τ ε) s τ)) s γ η t δ

/-! ### Boolean implementability of the release oracle -/

/-- **The release oracle on the time family is Boolean-implementable** (the chain construction of
Section `part:hsl`): for every schedule `γ η t δ`, with the isometric encoding
`E = (timeReleaseAccess hs γ η t δ).enc` and the one-hot Boolean family
`P = (timeReleaseAccess hs γ η t δ).fam`, every label `l` of
`ImprovedSparseHamiltonian.oracle (timeData τ s hs) γ η t δ` is implemented on `E` by at most
`hardCost l` queries to `oneHotOracle P` (`2` for the value label, `0` for the location labels). -/
theorem time_release_implementsOn (hs : 32 ≤ s) (γ η t δ : ℝ) :
    (timeReleaseAccess (τ := τ) hs γ η t δ).enc† ∘L (timeReleaseAccess (τ := τ) hs γ η t δ).enc =
        1 ∧
      ∀ l, EncodedOracle.ImplementsOn (oneHotOracle (timeReleaseAccess (τ := τ) hs γ η t δ).fam)
        (ImprovedSparseHamiltonian.oracle (timeData τ s hs) γ η t δ l)
        (timeReleaseAccess (τ := τ) hs γ η t δ).enc (hardCost l) :=
  ⟨(timeReleaseAccess hs γ η t δ).enc_isometry, (timeReleaseAccess hs γ η t δ).implementsOn_oneHot⟩

/-- **The release oracle on the mixed family is Boolean-implementable**: as
`time_release_implementsOn`, for `mixedMainData`. -/
theorem mixed_release_implementsOn (hs : 32 ≤ s) (γ η t δ : ℝ) :
    (mixedReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).enc† ∘L
        (mixedReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).enc = 1 ∧
      ∀ l, EncodedOracle.ImplementsOn
        (oneHotOracle (mixedReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).fam)
        (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s hs) γ η t δ l)
        (mixedReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).enc (hardCost l) :=
  ⟨(mixedReleaseAccess hs γ η t δ).enc_isometry, (mixedReleaseAccess hs γ η t δ).implementsOn_oneHot⟩

/-- **The release oracle on the precision family is Boolean-implementable**:
as `time_release_implementsOn`, for `precisionMainData`, with the bit oracle
`bitOracle P` of the `precN τ ε` sign bits. -/
theorem precision_release_implementsOn (hs : 32 ≤ s) (γ η t δ : ℝ) :
    (precisionReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).enc† ∘L
        (precisionReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).enc = 1 ∧
      ∀ l, EncodedOracle.ImplementsOn
        (bitOracle (precisionReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).fam)
        (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s hs) γ η t δ l)
        (precisionReleaseAccess (τ := τ) (ε := ε) hs γ η t δ).enc (hardCost l) :=
  ⟨(precisionReleaseAccess hs γ η t δ).enc_isometry,
    (precisionReleaseAccess hs γ η t δ).implementsOn_bit⟩

/-- The release oracle family is unitary on every label and input (re-export of
`ImprovedSparseHamiltonian.oracle_unitary`, the hypothesis `hO` of the general
family lemmas). -/
theorem release_oracle_unitary {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] {s : ℕ} (D : Data X N Z s) (γ η t δ : ℝ) (l : Query) (x : X) :
    IsUnitary (ImprovedSparseHamiltonian.oracle D γ η t δ l x) :=
  ImprovedSparseHamiltonian.oracle_unitary D γ η t δ l x

end

end SparseLowerBounds.Hamiltonian
end
