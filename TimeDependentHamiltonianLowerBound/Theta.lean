import TimeDependentHamiltonianLowerBound.ClassBound
import TimeDependentExtensions.Hamiltonian.Corollaries
import SparseLowerBounds.Hamiltonian.ReleaseTheta

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The released time-dependent simulators on the constant hard families: the `Θ` bracket

The common upper bound eq. `hsl:eq:upper` of Theorems `hs:thm:main` and `hs:thm:time`,
`O(√s τ + √(sτL) + L)`, against the lower bound `c₀ (√s τ + √(sτr) + r)` of Theorem
`hsl:thm:main` (the baseline has "a mixed term larger by `√h`"), for the released
time-dependent simulators run on the constant data of the hard families, as the released
`SparseLowerBounds.Hamiltonian.release_theta_bracket` for the time-independent simulator.

**The released simulators.** `TimeDependent.simulation` and
`TimeDependentExtensions.Hamiltonian.simulation` are existence theorems, so "the released
simulator" is every program satisfying their conclusion on the constant data with the
constant path (`UniformSimulates`, `MeshSimulates`), with existence from the class membership
of the constant hard data (`exists_uniformSimulates`, `exists_meshSimulates`; `η = 1`,
`t = τ`, `β = δ_val = 0`).

* `uniform_theta`: for any such uniform-mesh simulators of the time, mixed and precision
  families (any numbers of samples), with `S = √s τ + √(sτr) + r`: `c₀ S ≤ max(Q_T, Q_M, Q_P)`,
  `2 c₀ S ≤ max` of the Boolean costs, `max Q ≤ max count`,
  `max count ≤ 995328 (√s τ + √(sτL) + L) ≤ 995328 h S` (`release_shape_le`).
* `uniform_theta_bracket`: such simulators exist (at the explicit mesh size
  `TimeDependent.meshSize s 1 τ 0 ε`) and satisfy
  `c₀ S ≤ max Q ≤ max count ≤ 995328 h S`, `2 c₀ S ≤ max cost`.
* `mesh_theta`, `mesh_theta_bracket`: the same for the general-mesh simulator (on any mesh of
  `[0, τ]`; the bracket on the uniform mesh with `M` intervals and the explicit slot count
  `TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε`).

As for the released bracket, the lower half is on the maximum over the three per-family
programs (the three terms are witnessed by different families), and the gap is the factor
`h = log(e + L/τ)` of `release_shape_le` (`√h` on the mixed term, `h` on the additive term).
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian
open TimeDependentExtensions (IsMesh)
open scoped InnerProduct InnerProductSpace

/-! ### The released simulators on constant data -/

section Simulates

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- **The guarantees of the released uniform-mesh simulator on constant data** (the
conclusion of `TimeDependent.simulation` for the samples `constData D M` and the constant path
`constPath D`, schedule `γ`, program `p`): at most
`995328 (√s η t + √(s η t log(1/ε)) + log(1/ε))` queries, isometric clean input
`TimeDependent.input`, unitary runs and error at most `ε` against every propagator of the
constant path at time `t`. -/
def UniformSimulates (D : Data X n Z s) (M : ℕ) (hM : 0 < M) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program (TimeDependent.oracle (constData D M) γ η t ε)) : Prop :=
  (p.count : ℝ) ≤ 995328 *
      (Real.sqrt (s : ℝ) * (η * t) +
        Real.sqrt ((s : ℝ) * (η * t) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
    (TimeDependent.input (constData D M) hM γ η t ε)† ∘L
      TimeDependent.input (constData D M) hM γ η t ε = 1 ∧
    (∀ x, IsUnitary (p.eval x)) ∧
    UniformGuarantee p.eval (TimeDependent.input (constData D M) hM γ η t ε) (constPath D) t ε

/-- **The guarantees of the released general-mesh simulator on constant data** (the
conclusion of `TimeDependentExtensions.Hamiltonian.simulation` for `constData D M` on the mesh
`t` with `N` slots): the count bound, the isometric clean input, unitary runs and the
general-mesh guarantee for every path of the class. -/
def MeshSimulates (D : Data X n Z s) (M : ℕ) (hM : 0 < M) (t : ℕ → ℝ) (Nsl : ℕ)
    (γ η T ε : ℝ)
    (p : MultiOracleCircuit.Program
      (TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε)) : Prop :=
  (p.count : ℝ) ≤ 995328 *
      (Real.sqrt (s : ℝ) * (η * T) +
        Real.sqrt ((s : ℝ) * (η * T) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
    (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε)† ∘L
      TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε = 1 ∧
    (∀ x, IsUnitary (p.eval x)) ∧
    MeshGuarantee p.eval
      (TimeDependentExtensions.Hamiltonian.input (constData D M) hM t Nsl γ η T ε)
      (constData D M) t T ε

set_option maxRecDepth 8192 in
/-- **The released uniform-mesh simulator exists on constant hard data** (`η = 1`, time `t`,
`β = δ_val = 0`): from the class membership `uniformHyp_hard` and `TimeDependent.simulation`. -/
theorem exists_uniformSimulates {B : ℕ} {D : Data X n (Word B) s} (hD : HardInstance D) {M : ℕ}
    (hM : 0 < M) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hMesh : 4 * s * (1 * t) ≤ M) (hCayley : 9 * (Real.sqrt s * (1 * t)) ^ 3 ≤ ε * (M : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (TimeDependent.oracle (constData D M) γ 1 t ε),
        UniformSimulates D M hM γ 1 t ε p := by
  have hc := uniformHyp_hard hD ht le_rfl le_rfl hε hεHalf hM hMesh
    (by rw [mul_zero, zero_mul]; exact mul_nonneg hε.le (Nat.cast_nonneg M)) hCayley
    (by rw [mul_zero]; positivity)
  obtain ⟨γ, hγ, hγ1, hw, p, hcount, hin, hU, hguar⟩ := hc.simulation
  exact ⟨γ, hγ, hγ1, hw, p, hcount, hin, hU, hguar⟩

set_option maxRecDepth 8192 in
/-- **The released general-mesh simulator exists on constant hard data** (`η = 1`, final time
`T`), on every admissible mesh: from `meshHyp_hard` and
`TimeDependentExtensions.Hamiltonian.simulation`. -/
theorem exists_meshSimulates {B : ℕ} {D : Data X n (Word B) s} (hD : HardInstance D) {M : ℕ}
    (hM : 0 < M) {t : ℕ → ℝ} {T ε : ℝ} {Nsl : ℕ} (hT : 0 < T) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hN : 0 < Nsl) (hmesh : IsMesh t M T) (hClock : 4 * s * (1 * T) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt s * (1 * T)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (1 * T)) ≤ ε * Nsl) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ 1 T ε),
        MeshSimulates D M hM t Nsl γ 1 T ε p := by
  have hc := meshHyp_hard hD hM hT hε hεHalf hN hmesh hClock hCayley hRefine
  obtain ⟨γ, hγ, hγ1, hw, p, hcount, hin, hU, hguar⟩ := hc.simulation
  exact ⟨γ, hγ, hγ1, hw, p, hcount, hin, hU, hguar⟩

end Simulates

/-! ### The brackets -/

variable {τ ε : ℝ} {s : ℕ}

/-- The released count bound at `η = 1`, `t = τ` is `995328 (√s τ + √(sτL) + L)`. -/
theorem count_shape_one {c : ℝ}
    (hc : c ≤ 995328 * (Real.sqrt (s : ℝ) * (1 * τ) +
      Real.sqrt ((s : ℝ) * (1 * τ) * Real.log (1 / ε)) + Real.log (1 / ε))) :
    c ≤ 995328 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsL ε) + hsL ε) := by
  rw [one_mul] at hc
  exact hc

/-- **`Θ` bracket for the released uniform-mesh simulator** (eq. `hsl:eq:upper` against eq.
`hsl:eq:main`): for any released uniform-mesh simulators (`UniformSimulates`, `η = 1`, time `τ`,
precision `ε`, any numbers of samples) of the constant time, mixed and precision families, with
`S = √s τ + √(sτr) + r`: `c₀ S ≤ max(Q_T, Q_M, Q_P)`, `2 c₀ S ≤ max` of the Boolean costs
`p.cost hardCost`, `max Q ≤ max count` and
`max count ≤ 995328 (√s τ + √(sτL) + L) ≤ 995328 h S`. -/
theorem uniform_theta (h : HSRange τ s ε) {MT MM MP : ℕ} (hMT : 0 < MT) (hMM : 0 < MM)
    (hMP : 0 < MP) {γT γM γP : ℝ}
    {pT : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (timeData τ s h.s_ge) MT) γT 1 τ ε)}
    {pM : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) MM) γM 1 τ ε)}
    {pP : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) MP) γP 1 τ ε)}
    (hT : UniformSimulates (timeData τ s h.s_ge) MT hMT γT 1 τ ε pT)
    (hM : UniformSimulates (mixedMainData τ ε s h.s_ge) MM hMM γM 1 τ ε pM)
    (hP : UniformSimulates (precisionMainData τ ε s h.s_ge) MP hMP γP 1 τ ε pP) :
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
  obtain ⟨hlow, -⟩ := main_max_uniform h MT MM MP γT 1 τ ε γM 1 τ ε γP 1 τ ε
    pT (TimeDependent.input _ hMT γT 1 τ ε) hT.2.1 hT.2.2.2
    pM (TimeDependent.input _ hMM γM 1 τ ε) hM.2.1 hM.2.2.2
    pP (TimeDependent.input _ hMP γP 1 τ ε) hP.2.1 hP.2.2.2
  have hcT : (pT.cost hardCost : ℝ) = 2 * (pT.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcM : (pM.cost hardCost : ℝ) = 2 * (pM.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcP : (pP.cost hardCost : ℝ) = 2 * (pP.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  refine ⟨hlow, ?_, ?_, ?_, ?_⟩
  · rw [hcT, hcM, hcP, ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hlow (by norm_num)
  · exact max_le_max (by exact_mod_cast labelCount_le_count pT _)
      (max_le_max (by exact_mod_cast labelCount_le_count pM _)
        (by exact_mod_cast labelCount_le_count pP _))
  · exact max_le (count_shape_one hT.1) (max_le (count_shape_one hM.1) (count_shape_one hP.1))
  · rw [mul_assoc (995328 : ℝ) (hsH τ ε)]
    exact mul_le_mul_of_nonneg_left (release_shape_le h) (by norm_num)

/-- **The released uniform-mesh simulator on the constant hard families is
`Θ(√s τ + √(sτr) + r)` up to the factor `h`** (eq. `hsl:eq:upper` against eq. `hsl:eq:main`):
at the explicit mesh size `TimeDependent.meshSize s 1 τ 0 ε` there are released simulators of
the constant time, mixed and precision families (`UniformSimulates`) with
`c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ max(count_T, count_M, count_P) ≤ 995328 h S` and
`2 c₀ S ≤ max(cost_T, cost_M, cost_P)`; by `uniform_theta` every released simulator satisfies
the same bracket. -/
theorem uniform_theta_bracket (h : HSRange τ s ε) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program (TimeDependent.oracle
        (constData (timeData τ s h.s_ge) (TimeDependent.meshSize s 1 τ 0 ε)) γT 1 τ ε))
      (pM : MultiOracleCircuit.Program (TimeDependent.oracle
        (constData (mixedMainData τ ε s h.s_ge) (TimeDependent.meshSize s 1 τ 0 ε)) γM 1 τ ε))
      (pP : MultiOracleCircuit.Program (TimeDependent.oracle
        (constData (precisionMainData τ ε s h.s_ge) (TimeDependent.meshSize s 1 τ 0 ε)) γP 1 τ ε)),
      UniformSimulates (timeData τ s h.s_ge) (TimeDependent.meshSize s 1 τ 0 ε)
          (Nat.succ_pos _) γT 1 τ ε pT ∧
        UniformSimulates (mixedMainData τ ε s h.s_ge) (TimeDependent.meshSize s 1 τ 0 ε)
          (Nat.succ_pos _) γM 1 τ ε pM ∧
        UniformSimulates (precisionMainData τ ε s h.s_ge) (TimeDependent.meshSize s 1 τ 0 ε)
          (Nat.succ_pos _) γP 1 τ ε pP ∧
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
          max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
        2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
          max (pT.cost hardCost : ℝ) (max (pM.cost hardCost : ℝ) (pP.cost hardCost)) ∧
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ≤
          max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ∧
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ≤
          995328 * hsH τ ε * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hεHalf : ε ≤ 1 / 2 := by linarith [h.eps_le]
  obtain ⟨hpos, hMesh, -, hCayley⟩ :=
    TimeDependent.meshSize_spec s 1 τ 0 ε zero_le_one hτ le_rfl h.eps_pos
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  obtain ⟨γT, -, -, -, pT, hpT⟩ := exists_uniformSimulates hTi hpos hτ h.eps_pos hεHalf hMesh
    hCayley
  obtain ⟨γM, -, -, -, pM, hpM⟩ := exists_uniformSimulates hMi hpos hτ h.eps_pos hεHalf hMesh
    hCayley
  obtain ⟨γP, -, -, -, pP, hpP⟩ := exists_uniformSimulates hPi hpos hτ h.eps_pos hεHalf hMesh
    hCayley
  obtain ⟨h1, h2, h3, h4, h5⟩ := uniform_theta h hpos hpos hpos hpT hpM hpP
  exact ⟨γT, γM, γP, pT, pM, pP, hpT, hpM, hpP, h1, h2, h3, h4.trans h5⟩

/-- **`Θ` bracket for the released general-mesh simulator** (eq. `hsl:eq:upper` against eq.
`hsl:eq:main`): for any released general-mesh simulators (`MeshSimulates`, `η = 1`, final time
`τ`, precision `ε`, any meshes and slot counts) of the constant time, mixed and precision
families, the bracket of `uniform_theta`. -/
theorem mesh_theta (h : HSRange τ s ε) {MT MM MP : ℕ} (hMT : 0 < MT) (hMM : 0 < MM)
    (hMP : 0 < MP) {tT tM tP : ℕ → ℝ} {NT NM NP : ℕ} {γT γM γP : ℝ}
    {pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) MT) NT γT 1 τ ε)}
    {pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM 1 τ ε)}
    {pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP 1 τ ε)}
    (hT : MeshSimulates (timeData τ s h.s_ge) MT hMT tT NT γT 1 τ ε pT)
    (hM : MeshSimulates (mixedMainData τ ε s h.s_ge) MM hMM tM NM γM 1 τ ε pM)
    (hP : MeshSimulates (precisionMainData τ ε s h.s_ge) MP hMP tP NP γP 1 τ ε pP) :
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
  have hε : 0 ≤ ε := h.eps_pos.le
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  obtain ⟨hlow, -⟩ := main_max_mesh h MT MM MP NT NM NP tT tM tP γT 1 τ ε γM 1 τ ε γP 1 τ ε
    pT _ hT.2.1 (hT.2.2.2.criterion_const hTi.isHermitian hε)
    pM _ hM.2.1 (hM.2.2.2.criterion_const hMi.isHermitian hε)
    pP _ hP.2.1 (hP.2.2.2.criterion_const hPi.isHermitian hε)
  have hcT : (pT.cost hardCost : ℝ) = 2 * (pT.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcM : (pM.cost hardCost : ℝ) = 2 * (pM.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  have hcP : (pP.cost hardCost : ℝ) = 2 * (pP.labelCount .value : ℝ) := by
    rw [cost_hardCost]; push_cast; ring
  refine ⟨hlow, ?_, ?_, ?_, ?_⟩
  · rw [hcT, hcM, hcP, ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left hlow (by norm_num)
  · exact max_le_max (by exact_mod_cast labelCount_le_count pT _)
      (max_le_max (by exact_mod_cast labelCount_le_count pM _)
        (by exact_mod_cast labelCount_le_count pP _))
  · exact max_le (count_shape_one hT.1) (max_le (count_shape_one hM.1) (count_shape_one hP.1))
  · rw [mul_assoc (995328 : ℝ) (hsH τ ε)]
    exact mul_le_mul_of_nonneg_left (release_shape_le h) (by norm_num)

/-- **The released general-mesh simulator on the constant hard families is
`Θ(√s τ + √(sτr) + r)` up to the factor `h`** (eq. `hsl:eq:upper` against eq. `hsl:eq:main`):
for every number `M > 0` of mesh intervals, on the uniform mesh `t_r = r τ/M` with the explicit
slot count `TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε`, there are released
general-mesh simulators of the constant time, mixed and precision families (`MeshSimulates`) with
`c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ max(count_T, count_M, count_P) ≤ 995328 h S` and
`2 c₀ S ≤ max(cost_T, cost_M, cost_P)`; by `mesh_theta` every released general-mesh simulator
satisfies the same bracket. -/
theorem mesh_theta_bracket (h : HSRange τ s ε) {M : ℕ} (hM : 0 < M) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (timeData τ s h.s_ge) M)
        (TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε) γT 1 τ ε))
      (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (mixedMainData τ ε s h.s_ge) M)
        (TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε) γM 1 τ ε))
      (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (precisionMainData τ ε s h.s_ge) M)
        (TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε) γP 1 τ ε)),
      MeshSimulates (timeData τ s h.s_ge) M hM (fun r : ℕ => (r : ℝ) * τ / M)
          (TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε) γT 1 τ ε pT ∧
        MeshSimulates (mixedMainData τ ε s h.s_ge) M hM (fun r : ℕ => (r : ℝ) * τ / M)
          (TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε) γM 1 τ ε pM ∧
        MeshSimulates (precisionMainData τ ε s h.s_ge) M hM (fun r : ℕ => (r : ℝ) * τ / M)
          (TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε) γP 1 τ ε pP ∧
        c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
          max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
        2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
          max (pT.cost hardCost : ℝ) (max (pM.cost hardCost : ℝ) (pP.cost hardCost)) ∧
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ≤
          max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ∧
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) ≤
          995328 * hsH τ ε * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := by
  have hτ : 0 < τ := by linarith [h.one_le_tau]
  have hεHalf : ε ≤ 1 / 2 := by linarith [h.eps_le]
  obtain ⟨hN, hClock, hCayley, hRefine⟩ :=
    TimeDependentExtensions.Hamiltonian.slotCount_spec s M 1 τ ε zero_le_one hτ.le h.eps_pos _
      le_rfl
  have hmesh := TimeDependentExtensions.Hamiltonian.isMesh_uniform hM hτ.le
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  obtain ⟨γT, -, -, -, pT, hpT⟩ := exists_meshSimulates hTi hM hτ h.eps_pos hεHalf hN hmesh
    hClock hCayley hRefine
  obtain ⟨γM, -, -, -, pM, hpM⟩ := exists_meshSimulates hMi hM hτ h.eps_pos hεHalf hN hmesh
    hClock hCayley hRefine
  obtain ⟨γP, -, -, -, pP, hpP⟩ := exists_meshSimulates hPi hM hτ h.eps_pos hεHalf hN hmesh
    hClock hCayley hRefine
  obtain ⟨h1, h2, h3, h4, h5⟩ := mesh_theta h hM hM hM hpT hpM hpP
  exact ⟨γT, γM, γP, pT, pM, pP, hpT, hpM, hpP, h1, h2, h3, h4.trans h5⟩

end

end TimeDependentHamiltonianLowerBound
