import TimeDependentLowerBoundExtensions.Tolerant.LipschitzClass
import TimeDependentHamiltonianLowerBound.ClassBound
import TimeDependentHamiltonianLowerBound.NonVacuity
import TimeDependentLowerBoundExtensions.Calls.Bound

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for the class of piecewise Lipschitz paths

The remark after Theorem `hs:thm:time` (the manuscript, lines 1513-1516): "The lower bound in
Theorem `hsl:thm:main` also applies to this class, since its time-independent hard instances
satisfy the new assumptions with `β = δ_val = 0`." For the class of piecewise Lipschitz paths
with breakpoints (lines 1497-1500; `LipschitzPath`), an algorithm is given, on each of the three
hard families, by a program over the released general-mesh oracle family of the constant data
of that family and an isometric encoding, and it meets the guarantee of
`TimeDependentExtensions.Hamiltonian.simulation_lipschitz` for **every** piecewise Lipschitz path
compatible with its data (`LipschitzGuarantee`). The constant hard pieces belong to the class
with `β = δ = 0` on every mesh (`lipschitzPath_const`), and this membership is used in the
proof.

* `lipschitz_class_max`: `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` and the same for the
  counts, through `TimeDependentHamiltonianLowerBound.main_max_mesh`;
* `lipschitz_class_max_calls`: the same for programs over all call forms (plain, inverse,
  controlled, controlled inverse) of those families, through `Calls.main_max_calls_mesh`;
* `mesh_class_max_of_lipschitz`: the general-mesh form
  `TimeDependentHamiltonianLowerBound.mesh_class_max` on nondecreasing mesh points, as a
  corollary (`lipschitzGuarantee_of_meshGuarantee`);
* `lipschitz_class_nonvacuous`: the released general-mesh simulators of the three constant
  families meet the hypotheses, on every admissible mesh.
-/

namespace TimeDependentLowerBoundExtensions.Tolerant

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian
open TimeDependentExtensions (IsMesh)
open TimeDependentHamiltonianLowerBound (MeshGuarantee constData)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily)
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for the class of piecewise Lipschitz paths with breakpoints**
(remark after Theorem `hs:thm:time`; eq. `hsl:eq:main`, max form): for any three programs over
the released general-mesh oracle families of the constant time, mixed and precision data with `M`
mesh intervals (any slot counts and schedules) and isometric encodings, each meeting the
guarantee of `TimeDependentExtensions.Hamiltonian.simulation_lipschitz` on the mesh `t` at time
`τ` for **every** piecewise Lipschitz path compatible with its data (`LipschitzGuarantee`),
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the same for the counts. The constant pieces
belong to the class with `β = δ = 0` (`lipschitzPath_const`). -/
theorem lipschitz_class_max (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} (NT NM NP : ℕ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) M) NT γT ηT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M NT γT ηT TT εT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : LipschitzGuarantee pT.eval ιT (constData (timeData τ s h.s_ge) M) t τ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) M) NM γM ηM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M NM γM ηM TM εM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : LipschitzGuarantee pM.eval ιM (constData (mixedMainData τ ε s h.s_ge) M) t τ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) M) NP γP ηP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s M NP γP ηP TP εP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : LipschitzGuarantee pP.eval ιP (constData (precisionMainData τ ε s h.s_ge) M) t τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hε : 0 ≤ ε := h.eps_pos.le
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  exact TimeDependentHamiltonianLowerBound.main_max_mesh h M M M NT NM NP t t t γT ηT TT εT γM ηM
    TM εM γP ηP TP εP pT ιT hιT (hT.criterion_const hTi.isHermitian hε) pM ιM hιM
    (hM.criterion_const hMi.isHermitian hε) pP ιP hιP (hP.criterion_const hPi.isHermitian hε)

/-- **Theorem `hsl:thm:main` for the class of piecewise Lipschitz paths, all call forms**
(eq. `hsl:eq:main`, max form): as `lipschitz_class_max`, for programs over
`callFamily (TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε')` (plain,
inverse, controlled and controlled-inverse calls, each value call counted once) on isometric
encodings into `ℂ² ⊗` workspace, each meeting `LipschitzGuarantee` on the mesh `t` at time `τ`,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` with `Q` the number of value calls, and the same
for the counts. -/
theorem lipschitz_class_max_calls (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} (NT NM NP : ℕ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) M) NT γT ηT TT εT)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M NT γT ηT TT εT))
    (hιT : ιT† ∘L ιT = 1)
    (hT : LipschitzGuarantee pT.eval ιT (constData (timeData τ s h.s_ge) M) t τ ε)
    (pM : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) M) NM γM ηM TM εM)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M NM γM ηM TM εM))
    (hιM : ιM† ∘L ιM = 1)
    (hM : LipschitzGuarantee pM.eval ιM (constData (mixedMainData τ ε s h.s_ge) M) t τ ε)
    (pP : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) M) NP γP ηP TP εP)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s M NP γP ηP TP εP))
    (hιP : ιP† ∘L ιP = 1)
    (hP : LipschitzGuarantee pP.eval ιP (constData (precisionMainData τ ε s h.s_ge) M) t τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.cost (fun c => valueWeight c.1) : ℝ)
          (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hε : 0 ≤ ε := h.eps_pos.le
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  exact Calls.main_max_calls_mesh h M M M NT NM NP t t t γT ηT TT εT γM ηM TM εM γP ηP TP εP
    pT ιT hιT (hT.criterion_const hTi.isHermitian hε) pM ιM hιM
    (hM.criterion_const hMi.isHermitian hε) pP ιP hιP (hP.criterion_const hPi.isHermitian hε)

/-- **The general-mesh class form as a corollary** (containment check): on nondecreasing mesh
points `t`, the statement of `TimeDependentHamiltonianLowerBound.mesh_class_max` follows from
`lipschitz_class_max`, since the general-mesh guarantee gives the Lipschitz guarantee
(`lipschitzGuarantee_of_meshGuarantee`). The restriction covers every mesh in the sense of
`TimeDependentExtensions.IsMesh` (its points are monotone, `IsMesh.mono`), hence every mesh of
the released theorems; `mesh_class_max` itself needs no monotonicity and remains the statement
for arbitrary `t`. On a reversed interval the Lipschitz hypothesis of `LipschitzPath` is vacuous,
so the containment of the Lipschitz class in the general-mesh class uses `t_r ≤ t_{r+1}`. -/
theorem mesh_class_max_of_lipschitz (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ}
    (hmono : ∀ r : Fin M, t r ≤ t ((r : ℕ) + 1)) (NT NM NP : ℕ)
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
  exact lipschitz_class_max h NT NM NP γT ηT TT εT γM ηM TM εM γP ηP TP εP pT ιT hιT
    (lipschitzGuarantee_of_meshGuarantee hmono hT) pM ιM hιM
    (lipschitzGuarantee_of_meshGuarantee hmono hM) pP ιP hιP
    (lipschitzGuarantee_of_meshGuarantee hmono hP)

set_option maxRecDepth 8192 in
/-- **The hypotheses of `lipschitz_class_max` can be met**: on every mesh `t` of `[0, τ]` with
`M > 0` intervals and every slot count `N` with `4 s τ ≤ N`, `9 (√s τ)³ ≤ ε N²` and
`9 M √s τ ≤ ε N`, the released general-mesh simulators of the constant time, mixed and precision
families (`TimeDependentExtensions.Hamiltonian.simulation`), with their isometric clean inputs,
meet the Lipschitz guarantee for every piecewise Lipschitz path of the class (a corollary of
`TimeDependentHamiltonianLowerBound.mesh_class_nonvacuous` and
`lipschitzGuarantee_of_meshGuarantee`). -/
theorem lipschitz_class_nonvacuous (h : HSRange τ s ε) {M : ℕ} {t : ℕ → ℝ} {Nsl : ℕ}
    (hM : 0 < M) (hmesh : IsMesh t M τ) (hN : 0 < Nsl) (hClock : 4 * s * (1 * τ) ≤ Nsl)
    (hCayley : 9 * (Real.sqrt s * (1 * τ)) ^ 3 ≤ ε * (Nsl : ℝ) ^ 2)
    (hRefine : 9 * M * (Real.sqrt s * (1 * τ)) ≤ ε * Nsl) :
    ∃ (γT γM γP : ℝ)
      (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (timeData τ s h.s_ge) M) Nsl γT 1 τ ε))
      (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
          (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M Nsl γT 1 τ ε)
      (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (mixedMainData τ ε s h.s_ge) M) Nsl γM 1 τ ε))
      (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
          (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M Nsl γM 1 τ ε)
      (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
        (constData (precisionMainData τ ε s h.s_ge) M) Nsl γP 1 τ ε))
      (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
          (Word (scalarBits (precN τ ε) s τ)) s M Nsl γP 1 τ ε),
      (ιT† ∘L ιT = 1 ∧
        LipschitzGuarantee pT.eval ιT (constData (timeData τ s h.s_ge) M) t τ ε) ∧
      (ιM† ∘L ιM = 1 ∧
        LipschitzGuarantee pM.eval ιM (constData (mixedMainData τ ε s h.s_ge) M) t τ ε) ∧
      (ιP† ∘L ιP = 1 ∧
        LipschitzGuarantee pP.eval ιP (constData (precisionMainData τ ε s h.s_ge) M) t τ ε) := by
  obtain ⟨γT, γM, γP, pT, ιT, pM, ιM, pP, ιP, ⟨hiT, hgT⟩, ⟨hiM, hgM⟩, ⟨hiP, hgP⟩⟩ :=
    TimeDependentHamiltonianLowerBound.mesh_class_nonvacuous h hM hmesh hN hClock hCayley hRefine
  have hmono : ∀ r : Fin M, t r ≤ t ((r : ℕ) + 1) := fun r => hmesh.mono (Nat.le_succ _)
  exact ⟨γT, γM, γP, pT, ιT, pM, ιM, pP, ιP,
    ⟨hiT, lipschitzGuarantee_of_meshGuarantee hmono hgT⟩,
    ⟨hiM, lipschitzGuarantee_of_meshGuarantee hmono hgM⟩,
    ⟨hiP, lipschitzGuarantee_of_meshGuarantee hmono hgP⟩⟩

end

end TimeDependentLowerBoundExtensions.Tolerant
