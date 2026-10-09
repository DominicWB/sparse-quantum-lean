import TimeDependentHamiltonianLowerBound.Release

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The lower bound of Theorem `hsl:thm:main` for the time-dependent classes

The remark after Theorem `hs:thm:time` (end of the paragraph "Regularity and coherent
parameters"): "The lower bound in Theorem `hsl:thm:main` also applies to this class, since its
time-independent hard instances satisfy the new assumptions with `β = δ_val = 0`." Here an
algorithm for a class is given, on each of the three hard families, by a program over the
released oracle family of the constant data of that family (any schedule) and an isometric
encoding, and it **meets the guarantee of the released theorem for every path of the class**
compatible with its data. The constant hard paths are shown to belong to the class
(`uniformHyp_hard`, `meshPath_const`, `integrablePath_const`), and this membership is used in
the proofs, not assumed.

* Uniform meshes (`TimeDependent.simulation`): `uniform_class_members` (the constant data of
  the three hard families, with their constant paths, satisfy `UniformHyp` with `η = 1`,
  `t = τ`, every `β, δ ≥ 0` and every number `M` of samples meeting the public mesh
  conditions; in particular with `β = δ_val = 0`) and `uniform_class_max`: if the three
  programs meet `UniformGuarantee` (error at most `ε` against every propagator at time `τ`)
  for every path `Hpath` with `UniformHyp (constData D M) Hpath 1 τ β δ ε`, then
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`.
* General meshes (`TimeDependentExtensions.Hamiltonian.simulation`): `mesh_class_members`
  (`MeshHyp` on every mesh `t` of `[0, τ]` with `M` intervals and admissible slot counts) and
  `mesh_class_max`: if the three programs meet `MeshGuarantee` (every piecewise path of the
  class with integrated certificate at most `ε/9` and every piecewise propagator), the same
  bound.
* Integrable paths (`IntegrablePathSimulation.Hamiltonian.simulation`): `integrable_class_max`,
  with `IntegrableGuarantee` (every integrable path of the class with certificate at most `ε/9`
  and every integral-sense propagator); the data-level hypotheses are those of the general
  mesh (`mesh_class_members`).

In each case `Q` is the number of value queries (inverses included), and the bound holds for
the query counts as well; the three terms are witnessed by different families ("on one of the
three families").
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian
open TimeDependentExtensions (IsMesh)
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-! ### Uniform meshes -/

/-- **The constant hard paths are in the uniform-mesh class** (the remark after Theorem
`hs:thm:time`): for every `β, δ ≥ 0` and every number `M` of samples with the public mesh
conditions `4 s τ ≤ M`, `9 β τ² ≤ ε M`, `9 (√s τ)³ ≤ ε M²` and `τ δ ≤ ε/12`, the constant data
of the time, mixed and precision families with their constant paths satisfy the hypotheses of
`TimeDependent.simulation` with `η = 1` and `t = τ`. -/
theorem uniform_class_members (h : HSRange τ s ε) {M : ℕ} {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hMesh : 4 * s * (1 * τ) ≤ M) (hFreeze : 9 * β * τ ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (1 * τ)) ^ 3 ≤ ε * (M : ℝ) ^ 2) (hBudget : τ * δ ≤ ε / 12) :
    UniformHyp (constData (timeData τ s h.s_ge) M) (constPath (timeData τ s h.s_ge)) 1 τ β δ ε ∧
      UniformHyp (constData (mixedMainData τ ε s h.s_ge) M)
        (constPath (mixedMainData τ ε s h.s_ge)) 1 τ β δ ε ∧
      UniformHyp (constData (precisionMainData τ ε s h.s_ge) M)
        (constPath (precisionMainData τ ε s h.s_ge)) 1 τ β δ ε := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hεHalf : ε ≤ 1 / 2 := by linarith [h.eps_le]
  have hM : 0 < M := by
    have hs : (0 : ℝ) < 4 * s * (1 * τ) := by
      have : (32 : ℝ) ≤ s := by exact_mod_cast h.s_ge
      nlinarith [h.one_le_tau]
    exact_mod_cast hs.trans_le hMesh
  obtain ⟨hT, hMi, hP, -⟩ := hard_instances h
  exact ⟨uniformHyp_hard hT hτ hβ hδ h.eps_pos hεHalf hM hMesh hFreeze hCayley hBudget,
    uniformHyp_hard hMi hτ hβ hδ h.eps_pos hεHalf hM hMesh hFreeze hCayley hBudget,
    uniformHyp_hard hP hτ hβ hδ h.eps_pos hεHalf hM hMesh hFreeze hCayley hBudget⟩

/-- **Theorem `hsl:thm:main` for the uniform-mesh class of Theorem `hs:thm:time`** (eq.
`hsl:eq:main`, max form): fix `β, δ ≥ 0` and a number `M` of samples with the public mesh
conditions. For any three programs over the released uniform-mesh oracle families of the
constant time, mixed and precision data (any schedules) and isometric encodings, each meeting
the guarantee of `TimeDependent.simulation` for **every** path of the class compatible with
its data (`UniformHyp … 1 τ β δ ε`, error at most `ε` against every propagator at time `τ`),
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the same for the counts. The constant hard
paths belong to the class (`uniform_class_members`). -/
theorem uniform_class_max (h : HSRange τ s ε) {M : ℕ} {β δ : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hMesh : 4 * s * (1 * τ) ≤ M) (hFreeze : 9 * β * τ ^ 2 ≤ ε * M)
    (hCayley : 9 * (Real.sqrt s * (1 * τ)) ^ 3 ≤ ε * (M : ℝ) ^ 2) (hBudget : τ * δ ≤ ε / 12)
    (γT ηT tT εT γM ηM tM εM γP ηP tP εP : ℝ)
    (pT : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (timeData τ s h.s_ge) M) γT ηT tT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      TimeDependent.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M γT ηT tT εT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : ∀ Hpath, UniformHyp (constData (timeData τ s h.s_ge) M) Hpath 1 τ β δ ε →
      UniformGuarantee pT.eval ιT Hpath τ ε)
    (pM : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) M) γM ηM tM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      TimeDependent.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M γM ηM tM εM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : ∀ Hpath, UniformHyp (constData (mixedMainData τ ε s h.s_ge) M) Hpath 1 τ β δ ε →
      UniformGuarantee pM.eval ιM Hpath τ ε)
    (pP : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) M) γP ηP tP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      TimeDependent.Workspace (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)) s
        M γP ηP tP εP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : ∀ Hpath, UniformHyp (constData (precisionMainData τ ε s h.s_ge) M) Hpath 1 τ β δ ε →
      UniformGuarantee pP.eval ιP Hpath τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  obtain ⟨hcT, hcM, hcP⟩ := uniform_class_members h hβ hδ hMesh hFreeze hCayley hBudget
  exact main_max_uniform h M M M γT ηT tT εT γM ηM tM εM γP ηP tP εP pT ιT hιT (hT _ hcT)
    pM ιM hιM (hM _ hcM) pP ιP hιP (hP _ hcP)

/-! ### General meshes and integrable paths -/

/-- **The constant hard data are in the general-mesh class** (generalisations after Theorem
`hs:thm:time`): on every mesh `t` of `[0, τ]` with `M` intervals and every slot count `N` with
`4 s τ ≤ N`, `9 (√s τ)³ ≤ ε N²` and `9 M √s τ ≤ ε N`, the constant data of the time, mixed and
precision families satisfy the hypotheses of `TimeDependentExtensions.Hamiltonian.simulation`
(and of `IntegrablePathSimulation.Hamiltonian.simulation`) with `η = 1` and `T = τ`; their
constant pieces and paths belong to the path classes with certificate `0` (`meshPath_const`,
`integrablePath_const`). -/
theorem mesh_class_members (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} {Nsl : ℕ} (hM : 0 < M)
    (hmesh : IsMesh t M τ) (hN : 0 < Nsl) (hClock : 4 * s * (1 * τ) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt s * (1 * τ)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (1 * τ)) ≤ ε * Nsl) :
    MeshHyp (constData (timeData τ s h.s_ge) M) t 1 τ ε Nsl ∧
      MeshHyp (constData (mixedMainData τ ε s h.s_ge) M) t 1 τ ε Nsl ∧
      MeshHyp (constData (precisionMainData τ ε s h.s_ge) M) t 1 τ ε Nsl := by
  have hτ : 0 < τ := by linarith [h.one_le_tau]
  have hεHalf : ε ≤ 1 / 2 := by linarith [h.eps_le]
  obtain ⟨hT, hMi, hP, -⟩ := hard_instances h
  exact ⟨meshHyp_hard hT hM hτ h.eps_pos hεHalf hN hmesh hClock hCayley hRefine,
    meshHyp_hard hMi hM hτ h.eps_pos hεHalf hN hmesh hClock hCayley hRefine,
    meshHyp_hard hP hM hτ h.eps_pos hεHalf hN hmesh hClock hCayley hRefine⟩

/-- **Theorem `hsl:thm:main` for the general-mesh class** (generalisations after Theorem
`hs:thm:time`; eq. `hsl:eq:main`, max form): for any three programs over the released
general-mesh oracle families of the constant time, mixed and precision data with `M` mesh
intervals (any slot counts and schedules) and isometric encodings, each meeting the guarantee
of `TimeDependentExtensions.Hamiltonian.simulation` on the mesh `t` at time `τ` for **every**
path of the class compatible with its data (`MeshGuarantee`: every family of Hermitian,
interval-integrable pieces with integrated certificate at most `ε/9` and every piecewise
propagator), `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the same for the counts. The
constant pieces belong to the class (`meshPath_const`), and the constant data satisfy the
data-level hypotheses on every admissible mesh (`mesh_class_members`). -/
theorem mesh_class_max (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} (NT NM NP : ℕ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) M) NT γT ηT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M NT γT ηT TT εT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : MeshGuarantee pT.eval ιT (constData (timeData τ s h.s_ge) M) t τ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) M) NM γM ηM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M NM γM ηM TM εM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : MeshGuarantee pM.eval ιM (constData (mixedMainData τ ε s h.s_ge) M) t τ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) M) NP γP ηP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s M NP γP ηP TP εP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : MeshGuarantee pP.eval ιP (constData (precisionMainData τ ε s h.s_ge) M) t τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hε : 0 ≤ ε := h.eps_pos.le
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  exact main_max_mesh h M M M NT NM NP t t t γT ηT TT εT γM ηM TM εM γP ηP TP εP pT ιT hιT
    (hT.criterion_const hTi.isHermitian hε) pM ιM hιM (hM.criterion_const hMi.isHermitian hε)
    pP ιP hιP (hP.criterion_const hPi.isHermitian hε)

/-- **Theorem `hsl:thm:main` for the class of integrable paths** (eq. `hsl:eq:main`, max
form): for any three programs over the released oracle families of the constant time, mixed
and precision data (the family of `IntegrablePathSimulation.Hamiltonian.simulation`) and
isometric encodings, each meeting the guarantee of that theorem on the mesh `t` at time `τ`
for **every** path of the class compatible with its data (`IntegrableGuarantee`: every path
Hermitian almost everywhere and interval integrable with integrated certificate at most `ε/9`,
and every integral-sense propagator), `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the
same for the counts. The constant path belongs to the class (`integrablePath_const`). -/
theorem integrable_class_max (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} (NT NM NP : ℕ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) M) NT γT ηT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M NT γT ηT TT εT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : IntegrableGuarantee pT.eval ιT (constData (timeData τ s h.s_ge) M) t τ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) M) NM γM ηM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M NM γM ηM TM εM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : IntegrableGuarantee pM.eval ιM (constData (mixedMainData τ ε s h.s_ge) M) t τ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) M) NP γP ηP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s M NP γP ηP TP εP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : IntegrableGuarantee pP.eval ιP (constData (precisionMainData τ ε s h.s_ge) M) t τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hε : 0 ≤ ε := h.eps_pos.le
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  exact main_max_integrable h M M M NT NM NP γT ηT TT εT γM ηM TM εM γP ηP TP εP pT ιT hιT
    (hT.criterion_const hTi.isHermitian hε) pM ιM hιM (hM.criterion_const hMi.isHermitian hε)
    pP ιP hιP (hP.criterion_const hPi.isHermitian hε)

end

end TimeDependentHamiltonianLowerBound
