import SparseLowerBounds.Hamiltonian.ReleaseBridge

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The release Hamiltonian simulator on the hard families: the `Θ` bracket

Manuscript lines 2120-2135: the lower bound
`c₀ (√s τ + √(sτr) + r)` of Theorem `hsl:thm:main` is compared with the common
upper bound `O(√s τ + √(sτL) + L)` (eq. `hsl:eq:upper`) of the release's
simulator; "the time term matches and the mixed term is within `√h`" (and the
additive term within `h = L/r`).

**The release algorithm.** `ImprovedSparseHamiltonian.simulation_log_one D η t ε`
is an existence theorem: it provides a schedule `γ` and a program `p` over
`ImprovedSparseHamiltonian.oracle D γ η t ε` with the guarantees collected in
`ReleaseSimulates D γ η t ε p` (its literal conclusion: the count bound
`p.count ≤ 995328 (√s η|t| + √(s η|t| L) + L)`, the isometric clean input
`ImprovedSparseHamiltonian.input D γ η t ε`, unitarity, and endpoint error
`ε`). Since the program is a witness of a `Prop`-valued existential, "the
release algorithm" is formalised as **every** program with
`ReleaseSimulates`, together with the existence of one (`exists_releaseSimulates`,
which is `simulation_log_one` repackaged).

**Statements.**

* `release_shape_eq`, `release_shape_le`: for `τ ≥ 1` the release shape is
  `√s τ + √(sτL) + L = √s τ + √h √(sτr) + h r ≤ h (√s τ + √(sτr) + r)`
  (`L = h r`, `h ≥ 1`): the gap is `√h` on the mixed term and `h` on the
  additive term, nothing on the time term;
* `release_theta`: for any release simulators `p_T`, `p_M`, `p_P`
  (`ReleaseSimulates`, `η = 1`, time `τ`, precision `ε`) of the time, mixed and
  precision families, with `S = √s τ + √(sτr) + r`,
  `c₀ S ≤ max(Q_T, Q_M, Q_P)`, `2 c₀ S ≤ max(cost_T, cost_M, cost_P)` (Boolean
  weighted cost `p.cost hardCost = 2Q`), `max Q ≤ max count`,
  `max count ≤ 995328 (√s τ + √(sτL) + L) ≤ 995328 h S`;
* `release_theta_exists`: such simulators exist (the hard families meet the
  hypotheses of `simulation_log_one` with `η = 1`,
  `hard_data_meet_release_hypotheses`);
* `release_theta_bracket`: the combination, `∃` release simulators with
  `c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ max(count_T, count_M, count_P) ≤ 995328 h S`
  and `2 c₀ S ≤ max(cost_T, cost_M, cost_P)`.

The lower half is `main_max_release` (`Hamiltonian/ReleaseBridge`) at the
release's own input `ι = ImprovedSparseHamiltonian.input D γ 1 τ ε`.

**Reading of the bracket.** As in the manuscript (lines 2121-2124: "the three
terms can be witnessed by different families"; the theorem is a worst-case
statement), the lower bound is on the **maximum over the three families** of
the per-family release programs' value-query counts; no single hard family is
claimed to force all three terms. No bound `c₀ S ≤ Q(p)` for **one** release
program `p` is stated, for three reasons. (a) The three hard families have
different input, index and word types (`timeData` on
`SearchIndex (timeN τ) (hsMu s) s` with `Word (searchBits … (timeC τ) τ)`,
`mixedMainData` on `SearchIndex (precN τ ε) (hsMu s) s` with
`Word (searchBits … 1 τ)`, `precisionMainData` on `ScalarIndex (precN τ ε) s`
with `Word (scalarBits …)`; compare `TimePhys`, `MixedPhys`, `PrecisionPhys`),
so no single program over one `ImprovedSparseHamiltonian.oracle D γ 1 τ ε` can
be run on all three. (b) The step of lines 2123-2124 ("their dimensions can be
padded to a common known size without affecting their hardness"), which would
put the three families into one instance class on one common space and so give
one algorithm, is not formalised. (c)
`simulation_log_one` is a per-data `Prop`-valued existential, so `p_T`, `p_M`,
`p_P` are unrelated witnesses whose counts may differ; each family forces only
part of `S` (`time_release`: `√s τ`; `mixed_release`: `√(sτr)` when `L ≥ 64τ`
and `s ≥ 64n/τ`; `precision_release`: `r` when `L ≥ 64τ`, and `√(sτr)` when
moreover `s < 64n/τ`; `n = precN τ ε`), so `c₀ S ≤ Q(p)` for a single `p` does not follow. The bracket is therefore on the
worst case over the families, in the form of `main_max_endpoint` and of
`main_max_release`. Counts: `Q = p.labelCount .value` is the
paper's `Q` (native value queries, forward and inverse); the Boolean weighted
cost is `p.cost hardCost = 2 Q` (`cost_hardCost`); `p.count` is the release's
own count (row, column and value calls, inverses included), so `Q ≤ p.count`
(`labelCount_le_count`), and the upper bound of `simulation_log_one` is on
`p.count`.

**The gap.** `release_shape_eq` is an exact identity: the time term matches,
the mixed term carries `√h` (line 2130), the additive term carries `h`
(`L = h r`). The manuscript's improvement of the additive `L` by
Corollary `hs:cor:hybrid` (lines 2131-2135) is not part of the release
simulator `simulation_log_one` and is not used here, and the manuscript does
not claim the mixed term `√(sτL)` is necessary without its `√h` (lines
2136-2137); hence the bracket is `Θ` only up to the factor `h` of
`release_shape_le`.

**Relation to `Hamiltonian/ReleaseForm`.** The release simulator is not a
program over the native primitives, so it does not instantiate the hypotheses
of `*_endpoint` directly. The connecting lemma is
`time_release_implementsOn`, `mixed_release_implementsOn`,
`precision_release_implementsOn` (`Hamiltonian/ReleaseAccess`); its
consequences are `main_max_release`, `main_max_release_cost`
(`Hamiltonian/ReleaseBridge`) and `release_theta`, `release_theta_bracket`
(here). What remains open is the factor `h` of `release_shape_le` (`√h` on the
mixed term, `h` on the additive term) and the unformalised padding of (b).
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### The release simulator -/

/-- **The guarantees of the release simulator** (the conclusion of
`ImprovedSparseHamiltonian.simulation_log_one D η t ε` for the schedule `γ`
and program `p`): query count at most `995328 (√s η|t| + √(s η|t| log(1/ε)) +
log(1/ε))`, isometric clean input `ImprovedSparseHamiltonian.input D γ η t ε`,
and on every input a unitary run with endpoint error at most `ε` for
`exp(-itH_x)`. -/
def ReleaseSimulates {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {s : ℕ} (D : Data X N Z s) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle D γ η t ε)) : Prop :=
  (p.count : ℝ) ≤ 995328 *
      (Real.sqrt (s : ℝ) * (η * |t|) +
        Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
    (ImprovedSparseHamiltonian.input D γ η t ε)† ∘L ImprovedSparseHamiltonian.input D γ η t ε = 1 ∧
    ∀ x, IsUnitary (p.eval x) ∧
      ‖p.eval x ∘L ImprovedSparseHamiltonian.input D γ η t ε -
        ImprovedSparseHamiltonian.input D γ η t ε ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε

/-- **The release simulator exists** (`simulation_log_one`, repackaged): under
its hypotheses there are a schedule `γ ∈ (0, 1]` with `1 ≤ γ √s` and a program
`p` with `ReleaseSimulates D γ η t ε p`. -/
theorem exists_releaseSimulates {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X N Z s) (η t ε : ℝ) (hη : 0 < η)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle D γ η t ε),
        ReleaseSimulates D γ η t ε p := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    ImprovedSparseHamiltonian.simulation_log_one D η t ε hη hε hεHalf hH hrow hcol
  exact ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩

/-! ### The `√h` gap between the two shapes -/

variable {τ ε : ℝ} {s : ℕ}

/-- **The release's shape in the lower bound's parameters** (lines 2126-2130): for
`τ ≥ 1` and `η = 1`, `√s τ + √(sτL) + L = √s τ + √h √(sτr) + h r`, where
`L = log(1/ε)`, `h = log(e + L/τ)`, `r = L/h`. -/
theorem release_shape_eq (h : HSRange τ s ε) :
    Real.sqrt (s : ℝ) * (1 * |τ|) + Real.sqrt ((s : ℝ) * (1 * |τ|) * Real.log (1 / ε)) +
        Real.log (1 / ε) =
      Real.sqrt s * τ + Real.sqrt (hsH τ ε) * Real.sqrt (s * τ * hsR τ ε) + hsH τ ε * hsR τ ε := by
  have hL : Real.log (1 / ε) = hsH τ ε * hsR τ ε := by
    rw [mul_comm, h.hsR_mul_hsH, hsL]
  have hmul : (s : ℝ) * τ * (hsH τ ε * hsR τ ε) = hsH τ ε * (s * τ * hsR τ ε) := by ring
  rw [abs_of_pos h.tau_pos, one_mul, hL, hmul, Real.sqrt_mul h.hsH_pos.le]

/-- **The gap is at most `h`** (lines 2126-2136): the release's upper-bound
shape is at most `h` times the lower-bound shape,
`√s τ + √(sτL) + L ≤ h (√s τ + √(sτr) + r)` (the time term matches, the mixed
term is within `√h ≤ h`, the additive term within `h`). -/
theorem release_shape_le (h : HSRange τ s ε) :
    Real.sqrt s * τ + Real.sqrt (s * τ * hsL ε) + hsL ε ≤
      hsH τ ε * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  have heq := release_shape_eq h
  rw [abs_of_pos h.tau_pos, one_mul] at heq
  change Real.sqrt s * τ + Real.sqrt (s * τ * Real.log (1 / ε)) + Real.log (1 / ε) ≤ _
  rw [heq]
  have h1 : 1 ≤ hsH τ ε := h.one_le_hsH
  have hsq : Real.sqrt (hsH τ ε) ≤ hsH τ ε :=
    calc Real.sqrt (hsH τ ε) ≤ Real.sqrt (hsH τ ε ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = hsH τ ε := Real.sqrt_sq h.hsH_pos.le
  have hA : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hB : 0 ≤ Real.sqrt (s * τ * hsR τ ε) := Real.sqrt_nonneg _
  have hT : Real.sqrt s * τ ≤ hsH τ ε * (Real.sqrt s * τ) := by nlinarith
  have hM : Real.sqrt (hsH τ ε) * Real.sqrt (s * τ * hsR τ ε) ≤
      hsH τ ε * Real.sqrt (s * τ * hsR τ ε) := mul_le_mul_of_nonneg_right hsq hB
  nlinarith

/-! ### The bracket -/

/-- **`Θ` bracket for the release simulator** (lines 2120-2135): for any
release simulators (`ReleaseSimulates`, `η = 1`, time `τ`, precision `ε`) of
the time, mixed and precision families, with `S = √s τ + √(sτr) + r`:
`c₀ S ≤ max(Q_T, Q_M, Q_P)` (value queries), `2 c₀ S ≤ max` of the Boolean
weighted costs `p.cost hardCost`, `max Q ≤ max count`, and
`max count ≤ 995328 (√s τ + √(sτL) + L) ≤ 995328 h S`.

The lower bound is on the maximum over the three per-family programs, not on a
single program: the families have different input, index and word types, so
one program over one `ImprovedSparseHamiltonian.oracle` cannot be run on all
three; the padding to a common known dimension of lines 2123-2124, which would
give one algorithm on one instance class, is not formalised; and
`simulation_log_one` is a per-data existential, so `p_T`, `p_M`, `p_P` are
unrelated witnesses and each family forces only part of `S` (module
docstring, "Reading of the bracket"). -/
theorem release_theta (h : HSRange τ s ε) {γT γM γP : ℝ}
    {pT : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (timeData τ s h.s_ge) γT 1 τ ε)}
    {pM : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s h.s_ge) γM 1 τ ε)}
    {pP : MultiOracleCircuit.Program
      (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s h.s_ge) γP 1 τ ε)}
    (hT : ReleaseSimulates (timeData τ s h.s_ge) γT 1 τ ε pT)
    (hM : ReleaseSimulates (mixedMainData τ ε s h.s_ge) γM 1 τ ε pM)
    (hP : ReleaseSimulates (precisionMainData τ ε s h.s_ge) γP 1 τ ε pP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
        max (pT.cost hardCost : ℝ) (max (pM.cost hardCost : ℝ) (pP.cost hardCost)) ∧
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ∧
      max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ≤
        995328 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsL ε) + hsL ε) ∧
      995328 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsL ε) + hsL ε) ≤
        995328 * hsH τ ε * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  obtain ⟨hlow, -⟩ := main_max_release h γT 1 τ ε γM 1 τ ε γP 1 τ ε
    pT (ImprovedSparseHamiltonian.input _ γT 1 τ ε) hT.2.1 (fun j => (hT.2.2 j).2)
    pM (ImprovedSparseHamiltonian.input _ γM 1 τ ε) hM.2.1 (fun j => (hM.2.2 j).2)
    pP (ImprovedSparseHamiltonian.input _ γP 1 τ ε) hP.2.1 (fun x => (hP.2.2 x).2)
  have hcT : (pT.cost hardCost : ℝ) = 2 * (pT.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcM : (pM.cost hardCost : ℝ) = 2 * (pM.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcP : (pP.cost hardCost : ℝ) = 2 * (pP.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hshape : ∀ c : ℝ, c ≤ 995328 * (Real.sqrt (s : ℝ) * (1 * |τ|) +
      Real.sqrt ((s : ℝ) * (1 * |τ|) * Real.log (1 / ε)) + Real.log (1 / ε)) →
      c ≤ 995328 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsL ε) + hsL ε) := by
    intro c hc
    rw [abs_of_pos h.tau_pos, one_mul] at hc
    exact hc
  refine ⟨hlow, ?_, ?_, ?_, ?_⟩
  · rw [hcT, hcM, hcP, ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hlow (by norm_num)
  · exact max_le_max (by exact_mod_cast labelCount_le_count pT _)
      (max_le_max (by exact_mod_cast labelCount_le_count pM _)
        (by exact_mod_cast labelCount_le_count pP _))
  · exact max_le (hshape _ hT.1) (max_le (hshape _ hM.1) (hshape _ hP.1))
  · rw [mul_assoc (995328 : ℝ) (hsH τ ε)]
    exact mul_le_mul_of_nonneg_left (release_shape_le h) (by norm_num)

/-- **Non-vacuity**: release simulators of the three hard families exist
(`exists_releaseSimulates` with `η = 1`, `t = τ`, from
`hard_data_meet_release_hypotheses`). -/
theorem release_theta_exists (h : HSRange τ s ε) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program
        (ImprovedSparseHamiltonian.oracle (timeData τ s h.s_ge) γT 1 τ ε))
      (pM : MultiOracleCircuit.Program
        (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s h.s_ge) γM 1 τ ε))
      (pP : MultiOracleCircuit.Program
        (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s h.s_ge) γP 1 τ ε)),
      ReleaseSimulates (timeData τ s h.s_ge) γT 1 τ ε pT ∧
        ReleaseSimulates (mixedMainData τ ε s h.s_ge) γM 1 τ ε pM ∧
        ReleaseSimulates (precisionMainData τ ε s h.s_ge) γP 1 τ ε pP := by
  obtain ⟨⟨hε0, hεh⟩, hT, hM, hP⟩ := hard_data_meet_release_hypotheses h
  obtain ⟨γT, -, -, -, pT, hpT⟩ := exists_releaseSimulates (timeData τ s h.s_ge) 1 τ ε one_pos
    hε0 hεh (fun j => (hT j).1) (fun j => (hT j).2.1) (fun j => (hT j).2.2)
  obtain ⟨γM, -, -, -, pM, hpM⟩ := exists_releaseSimulates (mixedMainData τ ε s h.s_ge) 1 τ ε
    one_pos hε0 hεh (fun j => (hM j).1) (fun j => (hM j).2.1) (fun j => (hM j).2.2)
  obtain ⟨γP, -, -, -, pP, hpP⟩ := exists_releaseSimulates (precisionMainData τ ε s h.s_ge) 1 τ ε
    one_pos hε0 hεh (fun x => (hP x).1) (fun x => (hP x).2.1) (fun x => (hP x).2.2)
  exact ⟨γT, γM, γP, pT, pM, pP, hpT, hpM, hpP⟩

/-- **The release simulator on the hard families is `Θ(√s τ + √(sτr) + r)` up
to the factor `h`** (lines 2120-2135): there are release simulators of the
time, mixed and precision families (`ReleaseSimulates`) with
`c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ max(count_T, count_M, count_P) ≤ 995328 h S`,
`S = √s τ + √(sτr) + r`, and Boolean weighted cost
`2 c₀ S ≤ max(cost_T, cost_M, cost_P)` (`cost = p.cost hardCost = 2Q`); and by
`release_theta` every release simulator satisfies the same bracket. As in
`release_theta`, the bracket is on the worst case over the three families, not
on one program (module docstring, "Reading of the bracket"). -/
theorem release_theta_bracket (h : HSRange τ s ε) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program
        (ImprovedSparseHamiltonian.oracle (timeData τ s h.s_ge) γT 1 τ ε))
      (pM : MultiOracleCircuit.Program
        (ImprovedSparseHamiltonian.oracle (mixedMainData τ ε s h.s_ge) γM 1 τ ε))
      (pP : MultiOracleCircuit.Program
        (ImprovedSparseHamiltonian.oracle (precisionMainData τ ε s h.s_ge) γP 1 τ ε)),
      ReleaseSimulates (timeData τ s h.s_ge) γT 1 τ ε pT ∧
        ReleaseSimulates (mixedMainData τ ε s h.s_ge) γM 1 τ ε pM ∧
        ReleaseSimulates (precisionMainData τ ε s h.s_ge) γP 1 τ ε pP ∧
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
          max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
        2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
          max (pT.cost hardCost : ℝ) (max (pM.cost hardCost : ℝ) (pP.cost hardCost)) ∧
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ≤
          max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ∧
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ≤
          995328 * hsH τ ε * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  obtain ⟨γT, γM, γP, pT, pM, pP, hT, hM, hP⟩ := release_theta_exists h
  obtain ⟨h1, h2, h3, h4, h5⟩ := release_theta h hT hM hP
  exact ⟨γT, γM, γP, pT, pM, pP, hT, hM, hP, h1, h2, h3, h4.trans h5⟩

end

end SparseLowerBounds.Hamiltonian
end
