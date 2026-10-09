import TimeDependentLowerBoundExtensions.Coherent.Access
import TimeDependentHamiltonianLowerBound.Trees

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` with coherent selection of durations and start times

The proof of Theorem `hs:thm:time` "also permits coherent selection of known durations, start
times, or other public parameters, provided the corresponding coherent sampled-time oracle is
supplied" (the manuscript, lines 1505-1510), and the lower bound of Theorem `hsl:thm:main`
applies to the time-dependent class with time-independent hard instances (lines 1512-1516).
Here the algorithms are programs over the released selection family
`TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε'` (any branch
register, number of samples, slot count and schedule) on the constant time, mixed and precision
data, with any isometric encoding `E` of the branch-and-system space `ℂ^ι ⊗ ℂ^n`.

* `SelectCriterion`: the guarantee of `TimeDependentExtensions.Coherent.coherent_select` for one
  public duration table `u` (full output within `ε` of the coherently selected products
  `selected D σ N u x`); `select_endpoint`: on constant data a branch `i₀` of total duration
  `∑_k u_{i₀}(σ k)/N = τ` gives the endpoint error against `exp(-iτH_x)` on the encoding
  `E ∘ |i₀⟩`;
* `WindowsCriterion`: the guarantee of `TimeDependentExtensions.Coherent.coherent_windows` for
  one public table of windows `[t_{a_i}, t_{b_i}]`; `windows_endpoint`: a branch with
  `t_{b_{i₀}} - t_{a_{i₀}} = τ` gives the endpoint error;
* `main_max_select`, `main_max_windows`: `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` (value
  calls) and the same for the counts.

Adaptive algorithms over the selection family are in `Coherent.Tree`, non-vacuity is in
`Coherent.NonVacuity`, and all call forms of the selection family are in
`Coherent.Calls`.
-/

namespace TimeDependentLowerBoundExtensions.Coherent

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseHamiltonian.TimeDependent (SolvesOn)
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout HsRelease
open SparseLinearSystems.Protocol
open TimeDependentHamiltonianLowerBound (constData constPath)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

/-! ### Criteria and endpoints -/

section Criteria

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The branch injection `v ↦ |i₀⟩ ⊗ v` into `ℂ^ι ⊗ ℂ^n`. -/
def branchInj (ι N : Type) [Fintype ι] [DecidableEq ι] [Fintype N] (i₀ : ι) :
    EuclideanSpace ℂ N →L[ℂ] ODEJointNative.Public ι N :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => EuclideanSpace ℂ N)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.single ℂ (fun _ : ι => EuclideanSpace ℂ N) i₀

omit [DecidableEq N] in
/-- The branch injection is an isometry. -/
theorem branchInj_isometry (i₀ : ι) : (branchInj ι N i₀)† ∘L branchInj ι N i₀ = 1 := by
  ext1 v
  refine ext_inner_left ℂ fun w => ?_
  rw [comp_apply, adjoint_inner_right]
  simp only [branchInj, comp_apply, ContinuousLinearEquiv.coe_coe, PiLp.inner_apply]
  rw [Fintype.sum_eq_single i₀ (fun i hi => by simp [hi])]
  simp

omit [DecidableEq N] in
/-- A diagonal operator on `ℂ^ι ⊗ ℂ^n` acts on the branch `i₀` by its `i₀` block. -/
theorem diagonal_comp_branchInj (f : ι → EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (i₀ : ι) :
    WeightedClock.diagonal f ∘L branchInj ι N i₀ = branchInj ι N i₀ ∘L f i₀ := by
  ext1 v
  refine PiLp.ext fun i => ?_
  by_cases hi : i = i₀
  · subst hi
    simp [branchInj]
  · simp [branchInj, hi]

/-- The chronological product of exponentials of one operator is the exponential of the summed
durations. -/
theorem evolution_exp_const {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (H : P →L[ℂ] P) (c : ℕ → ℝ) (n : ℕ) :
    TimeDependent.evolution (fun k => NormedSpace.exp ((-Complex.I * ((c k : ℝ) : ℂ)) • H)) n =
      NormedSpace.exp ((-Complex.I * ((∑ k ∈ Finset.range n, c k : ℝ) : ℂ)) • H) := by
  letI : NormedAlgebra ℚ (P →L[ℂ] P) := NormedAlgebra.restrictScalars ℚ ℂ _
  induction n with
  | zero => simp
  | succ n ih =>
    rw [TimeDependent.evolution_succ, ih, ← NormedSpace.exp_add_of_commute
      (((Commute.refl H).smul_left _).smul_right _), ← add_smul, Finset.sum_range_succ]
    congr 2
    push_cast
    ring

omit [DecidableEq N] [CompleteSpace K] in
/-- An error bound against an operator `S` that acts on the branch `i₀` as `X` gives the same
error bound against `X` on the encoding `E ∘ |i₀⟩`. -/
theorem endpoint_of_comp (run : K →L[ℂ] K) (E : ODEJointNative.Public ι N →L[ℂ] K)
    (S : ODEJointNative.Public ι N →L[ℂ] ODEJointNative.Public ι N) (i₀ : ι)
    (X : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) {ε : ℝ}
    (hS : S ∘L branchInj ι N i₀ = branchInj ι N i₀ ∘L X) (h : ‖run ∘L E - E ∘L S‖ ≤ ε) :
    ‖run ∘L (E ∘L branchInj ι N i₀) - (E ∘L branchInj ι N i₀) ∘L X‖ ≤ ε := by
  have heq : run ∘L (E ∘L branchInj ι N i₀) - (E ∘L branchInj ι N i₀) ∘L X =
      (run ∘L E - E ∘L S) ∘L branchInj ι N i₀ := by
    simp only [sub_comp, comp_assoc, hS]
  rw [heq]
  have hB := LabeledSimulationTransfer.isometry_norm_le_one _ (branchInj_isometry (N := N) i₀)
  calc _ ≤ ‖run ∘L E - E ∘L S‖ * ‖branchInj ι N i₀‖ := opNorm_comp_le _ _
    _ ≤ ε * 1 := mul_le_mul h hB (norm_nonneg _) ((norm_nonneg _).trans h)
    _ = ε := mul_one ε

/-- **The guarantee of `coherent_select`** for one public duration table `u` and slot map `σ` on
`Nsel` slots: the full output is within `ε` of the coherently selected products. -/
def SelectCriterion (run : X → K →L[ℂ] K) (E : ODEJointNative.Public ι N →L[ℂ] K)
    (D : Data (X × Fin M) N Z s) (σ : ℕ → Fin M) (Nsel : ℕ) (u : ι → Fin M → ℝ) (ε : ℝ) :
    Prop :=
  ∀ x, ‖run x ∘L E - E ∘L TimeDependentExtensions.Coherent.selected D σ Nsel u x‖ ≤ ε

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] [CompleteSpace K] in
/-- **A branch of total duration `τ` is a simulation**: on constant data, if the branch `i₀`
has total duration `∑_{k < Nsel} u_{i₀}(σ k)/Nsel = τ`, the selection guarantee gives the
endpoint error `ε` against `exp(-iτH_x)` on the encoding `E ∘ |i₀⟩`. -/
theorem select_endpoint (D : Data X N Z s) (M Nsel : ℕ) (σ : ℕ → Fin M)
    (u : ι → Fin M → ℝ) (i₀ : ι) {τ ε : ℝ}
    (hdur : ∑ k ∈ Finset.range Nsel, u i₀ (σ k) / (Nsel : ℝ) = τ) (run : X → K →L[ℂ] K)
    (E : ODEJointNative.Public ι N →L[ℂ] K)
    (hcrit : SelectCriterion run E (constData D M) σ Nsel u ε) (x : X) :
    ‖run x ∘L (E ∘L branchInj ι N i₀) - (E ∘L branchInj ι N i₀) ∘L
      NormedSpace.exp ((-Complex.I * (τ : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))‖
        ≤ ε := by
  subst hdur
  refine endpoint_of_comp (run x) E _ i₀ _ ?_ (hcrit x)
  have he := evolution_exp_const (SparseStateOverlap.matrixOperator (D.matrix x))
    (fun k => u i₀ (σ k) / (Nsel : ℝ)) Nsel
  rw [TimeDependentExtensions.Coherent.selected, diagonal_comp_branchInj]
  exact congrArg (fun A => branchInj ι N i₀ ∘L A) he

/-- **The guarantee of `coherent_windows`** for one public table of windows
`[t_{a_i}, t_{b_i}]` on a mesh `t` with `M` intervals: for every instance, every piecewise
Hermitian, integrable path whose integrated sample errors are at most `ε / 3`, and every family
of propagators `V_i` of that path from the identity at `t_{a_i}`, the full output is within `ε`
of `∑_i |i⟩⟨i| ⊗ V_i(t_{b_i})`. -/
def WindowsCriterion (run : X → K →L[ℂ] K) (E : ODEJointNative.Public ι N →L[ℂ] K)
    (D : Data (X × Fin M) N Z s) (t : ℕ → ℝ) (a b : ι → ℕ) (ε : ℝ) : Prop :=
  ∀ x, ∀ (Hp : Fin M → ℝ → Matrix N N ℂ)
    (V : ι → ℝ → EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N),
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), (Hp r u).IsHermitian) →
    (∀ r : Fin M, IntervalIntegrable
      (fun u => SparseStateOverlap.matrixOperator (Hp r u)) volume (t r) (t ((r : ℕ) + 1))) →
    ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
      ‖SparseStateOverlap.matrixOperator (Hp r u) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 3 →
    (∀ i, V i (t (a i)) = 1) →
    (∀ i (r : Fin M), a i ≤ (r : ℕ) → (r : ℕ) < b i →
      SolvesOn (fun u => SparseStateOverlap.matrixOperator (Hp r u)) (V i)
        (t r) (t ((r : ℕ) + 1))) →
    ‖run x ∘L E - E ∘L WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤ ε

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] [CompleteSpace K] in
/-- **A window of length `τ` is a simulation**: on constant Hermitian data, if the window of the
branch `i₀` has length `t_{b_{i₀}} - t_{a_{i₀}} = τ`, the windows guarantee gives the endpoint
error `ε` against `exp(-iτH_x)` on the encoding `E ∘ |i₀⟩` (the constant pieces have zero
sample error, and `V_i(u) = exp(-i(u - t_{a_i})H_x)` are propagators from the identity). -/
theorem windows_endpoint (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian) (M : ℕ)
    (t : ℕ → ℝ) (a b : ι → ℕ) (i₀ : ι) {τ ε : ℝ} (hε : 0 ≤ ε)
    (hlen : t (b i₀) - t (a i₀) = τ) (run : X → K →L[ℂ] K)
    (E : ODEJointNative.Public ι N →L[ℂ] K)
    (hcrit : WindowsCriterion run E (constData D M) t a b ε) (x : X) :
    ‖run x ∘L (E ∘L branchInj ι N i₀) - (E ∘L branchInj ι N i₀) ∘L
      NormedSpace.exp ((-Complex.I * (τ : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))‖
        ≤ ε := by
  set H := SparseStateOverlap.matrixOperator (D.matrix x)
  have hc : ∀ r : Fin M, (constData D M).matrix (x, r) = D.matrix x := fun _ => rfl
  have hW := hcrit x (fun _ _ => D.matrix x)
    (fun i u => TimeDependentHamiltonianLowerBound.constProp H (u - t (a i)))
    (fun _ _ _ => hH x) (fun _ => intervalIntegrable_const)
    (by simp [hc]; positivity)
    (fun i => by simp [TimeDependentHamiltonianLowerBound.constProp_zero])
    (fun i _ _ _ u _ => ((TimeDependentHamiltonianLowerBound.hasDerivAt_constProp H
      (u - t (a i))).comp_sub_const u (t (a i))).hasDerivWithinAt)
  refine endpoint_of_comp (run x) E _ i₀ _ ?_ hW
  rw [diagonal_comp_branchInj]
  congr 1
  show TimeDependentHamiltonianLowerBound.constProp H (t (b i₀) - t (a i₀)) = _
  rw [hlen]
  rfl

end Criteria

/-! ### The three hard families -/

variable {τ ε : ℝ} {s : ℕ}

/-- The workspace of the selection family on the time family. -/
abbrev SelTimeWork (ι : Type) [Fintype ι] (τ : ℝ) (s M Nsl : ℕ) (γ ρ T ε' : ℝ) : Type :=
  TimeDependentExtensions.MeshSelect.Workspace ι (SearchIndex (timeN τ) (hsMu s) s)
    (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s M Nsl γ ρ T ε'

/-- The workspace of the selection family on the mixed family. -/
abbrev SelMixedWork (ι : Type) [Fintype ι] (τ ε : ℝ) (s M Nsl : ℕ) (γ ρ T ε' : ℝ) : Type :=
  TimeDependentExtensions.MeshSelect.Workspace ι (SearchIndex (precN τ ε) (hsMu s) s)
    (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s M Nsl γ ρ T ε'

/-- The workspace of the selection family on the precision family. -/
abbrev SelPrecisionWork (ι : Type) [Fintype ι] (τ ε : ℝ) (s M Nsl : ℕ) (γ ρ T ε' : ℝ) : Type :=
  TimeDependentExtensions.MeshSelect.Workspace ι (ScalarIndex (precN τ ε) s)
    (Word (scalarBits (precN τ ε) s τ)) s M Nsl γ ρ T ε'

/-- From the Boolean-cost bound with the weights `hardCost` (`2` per value call) to the bound
on value calls and on all calls. -/
theorem main_max_of_value {KT KM KP XT XM XP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    {OT : Query → XT → KT →L[ℂ] KT} {OM : Query → XM → KM →L[ℂ] KM}
    {OP : Query → XP → KP →L[ℂ] KP} (_h : HSRange τ s ε)
    (pT : MultiOracleCircuit.Program OT) (pM : MultiOracleCircuit.Program OM)
    (pP : MultiOracleCircuit.Program OP)
    (hb : 2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
      max (pT.cost hardCost : ℝ) (max (pM.cost hardCost : ℝ) (pP.cost hardCost))) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  rw [cost_hardCost, cost_hardCost, cost_hardCost] at hb
  push_cast at hb
  rw [← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)] at hb
  have hQ : c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
    linarith
  have hT' : (pT.labelCount .value : ℝ) ≤ pT.count := by
    exact_mod_cast labelCount_le_count pT .value
  have hM' : (pM.labelCount .value : ℝ) ≤ pM.count := by
    exact_mod_cast labelCount_le_count pM .value
  have hP' : (pP.labelCount .value : ℝ) ≤ pP.count := by
    exact_mod_cast labelCount_le_count pP .value
  exact ⟨hQ, hQ.trans (max_le_max hT' (max_le_max hM' hP'))⟩

/-- **Theorem `hsl:thm:main` with coherent selection of durations** (eq. `hsl:eq:main`, max
form): for any three programs over the released selection families of the constant time,
mixed and precision data (any branch registers, numbers of samples, slot counts and
schedules), isometric encodings of `ℂ^ι ⊗ ℂ^n`, and public duration tables, each meeting the
guarantee of `coherent_select` (`SelectCriterion`) with a branch of total duration `τ`,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` (value calls), and the same for the counts. -/
theorem main_max_select (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT] [DecidableEq ιT]
    [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (MT MM MP NT NM NP ST SM SP : ℕ) (γT ρT TT εT γM ρM TM εM γP ρP TP εP : ℝ)
    (σT : ℕ → Fin MT) (σM : ℕ → Fin MM) (σP : ℕ → Fin MP)
    (uT : ιT → Fin MT → ℝ) (uM : ιM → Fin MM → ℝ) (uP : ιP → Fin MP → ℝ)
    (iT : ιT) (iM : ιM) (iP : ιP)
    (hdT : ∑ k ∈ Finset.range ST, uT iT (σT k) / (ST : ℝ) = τ)
    (hdM : ∑ k ∈ Finset.range SM, uM iM (σM k) / (SM : ℝ) = τ)
    (hdP : ∑ k ∈ Finset.range SP, uP iP (σP k) / (SP : ℝ) = τ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιT)
      (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT))
    (ET : ODEJointNative.Public ιT (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      SelTimeWork ιT τ s MT NT γT ρT TT εT) (hET : ET† ∘L ET = 1)
    (hT : SelectCriterion pT.eval ET (constData (timeData τ s h.s_ge) MT) σT ST uT ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιM)
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM))
    (EM : ODEJointNative.Public ιM (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      SelMixedWork ιM τ ε s MM NM γM ρM TM εM) (hEM : EM† ∘L EM = 1)
    (hM : SelectCriterion pM.eval EM (constData (mixedMainData τ ε s h.s_ge) MM) σM SM uM ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιP)
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP))
    (EP : ODEJointNative.Public ιP (ScalarIndex (precN τ ε) s) →L[ℂ]
      SelPrecisionWork ιP τ ε s MP NP γP ρP TP εP) (hEP : EP† ∘L EP = 1)
    (hP : SelectCriterion pP.eval EP (constData (precisionMainData τ ε s h.s_ge) MP) σP SP uP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  exact main_max_of_value h pT pM pP
    (Core.main_max_access h _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (timeData τ s h.s_ge)
        (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MT NT γT ρT TT εT)
      pT (ET ∘L branchInj ιT _ iT) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iT) hET) (select_endpoint _ MT ST σT uT iT hdT pT.eval ET hT)
      _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (mixedMainData τ ε s h.s_ge)
        (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MM NM γM ρM TM εM)
      pM (EM ∘L branchInj ιM _ iM) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iM) hEM) (select_endpoint _ MM SM σM uM iM hdM pM.eval EM hM)
      _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (precisionMainData τ ε s h.s_ge)
        (scalarAccess (by have := h.s_ge; omega)) MP NP γP ρP TP εP)
      pP (EP ∘L branchInj ιP _ iP) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iP) hEP) (select_endpoint _ MP SP σP uP iP hdP pP.eval EP hP))

/-- **Theorem `hsl:thm:main` with coherent start times and durations** (eq. `hsl:eq:main`, max
form): as `main_max_select`, for programs meeting the guarantee of `coherent_windows`
(`WindowsCriterion`, any mesh `t` and public table of windows) with a branch whose window has
length `τ`. -/
theorem main_max_windows (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT] [DecidableEq ιT]
    [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (MT MM MP NT NM NP : ℕ) (γT ρT TT εT γM ρM TM εM γP ρP TP εP : ℝ) (tT tM tP : ℕ → ℝ)
    (aT bT : ιT → ℕ) (aM bM : ιM → ℕ) (aP bP : ιP → ℕ) (iT : ιT) (iM : ιM) (iP : ιP)
    (hlT : tT (bT iT) - tT (aT iT) = τ) (hlM : tM (bM iM) - tM (aM iM) = τ)
    (hlP : tP (bP iP) - tP (aP iP) = τ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιT)
      (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT))
    (ET : ODEJointNative.Public ιT (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      SelTimeWork ιT τ s MT NT γT ρT TT εT) (hET : ET† ∘L ET = 1)
    (hT : WindowsCriterion pT.eval ET (constData (timeData τ s h.s_ge) MT) tT aT bT ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιM)
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM))
    (EM : ODEJointNative.Public ιM (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      SelMixedWork ιM τ ε s MM NM γM ρM TM εM) (hEM : EM† ∘L EM = 1)
    (hM : WindowsCriterion pM.eval EM (constData (mixedMainData τ ε s h.s_ge) MM) tM aM bM ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιP)
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP))
    (EP : ODEJointNative.Public ιP (ScalarIndex (precN τ ε) s) →L[ℂ]
      SelPrecisionWork ιP τ ε s MP NP γP ρP TP εP) (hEP : EP† ∘L EP = 1)
    (hP : WindowsCriterion pP.eval EP (constData (precisionMainData τ ε s h.s_ge) MP) tP aP bP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  obtain ⟨hHT, hHM, hHP, -⟩ := hard_instances h
  have hε : 0 ≤ ε := h.eps_pos.le
  exact main_max_of_value h pT pM pP
    (Core.main_max_access h _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (timeData τ s h.s_ge)
        (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MT NT γT ρT TT εT)
      pT (ET ∘L branchInj ιT _ iT) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iT) hET)
      (windows_endpoint _ hHT.isHermitian MT tT aT bT iT hε hlT pT.eval ET hT)
      _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (mixedMainData τ ε s h.s_ge)
        (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MM NM γM ρM TM εM)
      pM (EM ∘L branchInj ιM _ iM) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iM) hEM)
      (windows_endpoint _ hHM.isHermitian MM tM aM bM iM hε hlM pM.eval EM hM)
      _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (precisionMainData τ ε s h.s_ge)
        (scalarAccess (by have := h.s_ge; omega)) MP NP γP ρP TP εP)
      pP (EP ∘L branchInj ιP _ iP) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iP) hEP)
      (windows_endpoint _ hHP.isHermitian MP tP aP bP iP hε hlP pP.eval EP hP))

end

end TimeDependentLowerBoundExtensions.Coherent
