import SparseLowerBounds.Hamiltonian.ReleaseTheta
import NativeSignedFactor.Simulation

set_option synthInstance.maxHeartbeats 400000

/-!
# Lower bounds from Boolean access certificates, and the common query form

Theorem `hsl:thm:main` of the manuscript (the Hamiltonian-simulation lower bound, released
library `SparseLowerBounds`) holds for every program over every labelled oracle family whose
labels are implemented by Boolean queries to the hidden input of a hard family: two Boolean
queries per native value call and none for the input-independent locators (the general family
lemmas `SparseLowerBounds.Hamiltonian.time_general`, `mixed_general`, `precision_general`).
The released module `Hamiltonian/ReleaseAccess` packages such an implementation as a
`PhaseAccess` certificate and transports it through fixed register relabellings and untouched
spectator registers at the same per-label cost.

This module states the lower bounds once for an arbitrary certified family:

* `time_of_access`, `mixed_of_access`, `precision_of_access`: the three per-family bounds of
  `hsl:thm:main` (eqs. `hsl:eq:timelower`, `hsl:eq:mixrbound`, `hsl:eq:rbound`,
  `hsl:eq:failedmix`) for every program over a family `O` with a `PhaseAccess` certificate of
  cost `hardCost` (`2` per value label, `0` per location label), in the trace-distance form
  `Readout.Accurate` of eq. `hsl:eq:accuracy`;
* `main_max_of_access`: eq. `hsl:eq:main` in max form for three such programs.

It then certifies the oracle family of the improved-precision upper bounds. The common query form
`NativeSignedFactor.Simulates` of Theorems `hs:thm:optimal` and `hs:thm:two-norm` uses programs
over `CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D)`: each native
primitive on its register of the native-control workspace, with every other register a spectator
(`physOracle D = NativeMaskedProgram.oracle (ι := Bool) (NativeSparseMaskedAccess.flatOracle D)`),
on every block of `ℂ^ι`. Every label is therefore exactly one call of the native primitive of the
same label inside spectators and fixed relabellings, as for the release simulator's family:

* `physAccess`: `physOracle D` from a certificate for `NativeSparseBlockEncoding.oracles D`
  (`HsRelease.nativeMaskedAccess` on the dilation branch `Bool` after
  `HsRelease.flatSparseAccess`);
* `commonAccess`: the common family, by `PhaseAccess.spectate ι` and
  `Helpers.Adaptive.Access.diagonal_const_eq_fiber`;
* `timeCommonAccess`, `mixedCommonAccess`, `precisionCommonAccess`: the three hard families of
  `hsl:thm:main` at the main parameters, from `searchAccess` and `scalarAccess`;
* `common_unitary`: the common family is unitary on every label and input.
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.Hamiltonian.HsRelease Readout
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### The lower bounds for any certified family -/

section Generic

variable {τ ε : ℝ} {s : ℕ} {K G : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Time family, any certified family** (eq. `hsl:eq:timelower`): if every label of a unitary
family `O` over the time family's hidden inputs costs at most `hardCost` Boolean queries, every
program over `O` that is `ε`-accurate on the time family makes at least `c_T √s τ` value
queries, with Boolean cost at least `2 c_T √s τ`. -/
theorem time_of_access (h : HSRange τ s ε)
    {O : Query → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε) :
    2 * (cT * Real.sqrt s * τ) ≤ p.cost hardCost ∧ cT * Real.sqrt s * τ ≤ p.labelCount .value ∧
      cT * Real.sqrt s * τ ≤ p.count := by
  have hb := (time_general h.one_le_tau h.s_ge h.eps_le A.fam A.enc A.enc_isometry O hO
    hardCost A.implementsOn_oneHot p φ₀ hφ₀ e he hacc).2
  have hb' : 2 * (cT * Real.sqrt s * τ) ≤ p.cost hardCost := by linarith
  exact ⟨hb', native_bound_of_cost p hb'⟩

/-- **Mixed family, any certified family** (eq. `hsl:eq:mixrbound`): for `L ≥ 64τ` and
`s ≥ 64n/τ`, at least `(log 2/(384√2)) √(sτr)` value queries. -/
theorem mixed_of_access (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    {O : Query → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K}
    (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε) :
    2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) ≤ p.cost hardCost ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hb := mixed_general (n := precN τ ε) (μ := hsMu s) (s := s) (τ := τ) (ε := ε) hn
    (by linarith [h.one_le_tau]) (by linarith) (mixed_m_cond h hs) (by linarith [h.eps_pos])
    A.fam A.enc A.enc_isometry O hO hardCost A.implementsOn_oneHot p φ₀ hφ₀ e he hacc
  have hnum := mixrbound h hL
  have hb' : 2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) ≤
      p.cost hardCost := by linarith
  exact ⟨hb', native_bound_of_cost p hb'⟩

/-- **Precision family, any certified family** (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`): for
`L ≥ 64τ`, at least `r/32` value queries, and at least `√(sτr)/(64√2)` when `s < 64n/τ`. No
seed or readout norm hypothesis is needed. -/
theorem precision_of_access (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    {O : Query → (Fin (precN τ ε) → Bool) → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (precN τ ε)) bitPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K)
    (e : K →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    2 * (hsR τ ε / 32) ≤ p.cost hardCost ∧ hsR τ ε / 32 ≤ p.labelCount .value ∧
      hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hb := precision_general (n := precN τ ε) (s := s) (τ := τ) (ε := ε) (by omega)
    (by linarith [h.one_le_tau]) (by linarith) (by linarith [h.eps_pos])
    A.fam A.enc A.enc_isometry O hO hardCost A.implementsOn_bit p φ₀ e hacc
  have hrb := rbound h hL
  have hq : 2 * ((precN τ ε : ℝ) / 4) ≤ p.cost hardCost := by linarith
  have hb' : 2 * (hsR τ ε / 32) ≤ p.cost hardCost := by linarith
  have hQ := native_bound_of_cost p hb'
  exact ⟨hb', hQ.1, hQ.2, fun hs' => (failedmix h hL hs').trans (native_bound_of_cost p hq).1⟩

end Generic

/-- **Theorem `hsl:thm:main`, max form, for any certified families** (eq. `hsl:eq:main`,
`c₀ = log 2/(4096π)`): for any three programs over certified unitary families, accurate on the
time, mixed and precision families respectively,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`. -/
theorem main_max_of_access {τ ε : ℝ} {s : ℕ} (h : HSRange τ s ε)
    {KT KM KP GT GM GP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    {OT : Query → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT}
    (hOT : ∀ l x, IsUnitary (OT l x))
    (AT : PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern OT hardCost)
    (pT : MultiOracleCircuit.Program OT) (φT : KT) (hφT : ‖φT‖ ≤ 1)
    (eT : KT →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeData τ s h.s_ge).matrix j) τ (searchInput (timeN τ) (hsMu s) s)) ε)
    {OM : Query → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM}
    (hOM : ∀ l x, IsUnitary (OM l x))
    (AM : PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern OM hardCost)
    (pM : MultiOracleCircuit.Program OM) (φM : KM) (hφM : ‖φM‖ ≤ 1)
    (eM : KM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedMainData τ ε s h.s_ge).matrix j) τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    {OP : Query → (Fin (precN τ ε) → Bool) → KP →L[ℂ] KP} (hOP : ∀ l x, IsUnitary (OP l x))
    (AP : PhaseAccess (Fin (precN τ ε)) bitPattern OP hardCost)
    (pP : MultiOracleCircuit.Program OP) (φP : KP)
    (eP : KP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionMainData τ ε s h.s_ge).matrix x) τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  refine assembly h (time_of_access h hOT AT pT φT hφT eT heT haccT).2.1 (fun hL => ?_)
    (fun hL hs => (mixed_of_access h hL hs hOM AM pM φM hφM eM heM haccM).2.1)
  have hP := precision_of_access h hL hOP AP pP φP eP haccP
  exact ⟨hP.2.1, hP.2.2.2⟩

/-! ### The common query form of the upper bounds -/

section Common

variable {I : Type*} [Fintype I] {X : Type*} {y : X → I → Bool}
  {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- **The physical oracle family** `NativeSignedFactor.physOracle D` (each native primitive on
its register, every other register of the native-control workspace a spectator, on both
dilation branches): the same Boolean costs as `oracles D`. -/
def physAccess (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w) :
    PhaseAccess I y (NativeSignedFactor.physOracle D) w :=
  nativeMaskedAccess Bool (flatSparseAccess D A)

/-- **The common query form** `CoherentQuerySchedule.oracle (ι := ι) (physOracle D)` of
`NativeSignedFactor.Simulates`: the physical family on every block of `ℂ^ι`. Same Boolean
costs as `oracles D`. -/
def commonAccess (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w)
    (ι : Type) [Fintype ι] :
    PhaseAccess I y (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D)) w :=
  ((physAccess D A).spectate ι).congr fun _ _ =>
    (Helpers.Adaptive.Access.diagonal_const_eq_fiber _).symm

/-- The common family is unitary on every label and input. -/
theorem common_unitary {X : Type*} (D : Data X N Z s) (ι : Type) [Fintype ι] (l : Query)
    (x : X) :
    IsUnitary (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D) l x) :=
  CoherentQuerySchedule.oracle_unitary _ (NativeSignedFactor.physOracle_unitary D) l x

end Common

section HardFamilies

variable {τ ε : ℝ} {s : ℕ}

/-- The time family's common-form certificate (one-hot Boolean oracle, costs `hardCost`). -/
def timeCommonAccess (hs : 32 ≤ s) (ι : Type) [Fintype ι] :
    PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern
      (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle (timeData τ s hs)))
      hardCost :=
  commonAccess _ (searchAccess (one_le_hsMu hs) (two_mul_hsM_le hs)) ι

/-- The mixed family's common-form certificate. -/
def mixedCommonAccess (hs : 32 ≤ s) (ι : Type) [Fintype ι] :
    PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern
      (CoherentQuerySchedule.oracle (ι := ι)
        (NativeSignedFactor.physOracle (mixedMainData τ ε s hs))) hardCost :=
  commonAccess _ (searchAccess (one_le_hsMu hs) (two_mul_hsM_le hs)) ι

/-- The precision family's common-form certificate (bit Boolean oracle). -/
def precisionCommonAccess (hs : 32 ≤ s) (ι : Type) [Fintype ι] :
    PhaseAccess (Fin (precN τ ε)) bitPattern
      (CoherentQuerySchedule.oracle (ι := ι)
        (NativeSignedFactor.physOracle (precisionMainData τ ε s hs))) hardCost :=
  commonAccess _ (scalarAccess (by omega)) ι

end HardFamilies

end

end OptimalLowerBounds
