import TimeDependentLowerBoundExtensions.Coherent.Bound
import IntegrablePathSimulation.Coherent.Theorem

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Coherent start times and durations under the integrable-path criterion

For an integrable Hermitian path it suffices to have a certified bound on the integrated sample
errors, and the proof permits coherent selection of known durations and start times (the
manuscript, lines 1500-1510); `IntegrablePathSimulation.Coherent.coherent_windows` states this
on the released selection family. The lower bound of Theorem `hsl:thm:main` applies to the
time-dependent class with time-independent hard instances (lines 1512-1516).

* `WindowsIntegrableCriterion`: the guarantee of
  `IntegrablePathSimulation.Coherent.coherent_windows` for one program and one public table of
  windows `[t_{a_i}, t_{b_i}]` (every path Hermitian at almost every time of `[0, T]` and
  interval integrable on `[0, T]`, whose integrated sample errors are at most `ε / 3`, and every
  family `V_i` of integral-sense solutions on `[t_{a_i}, t_{b_i}]` from the identity at
  `t_{a_i}`);
* `windowsIntegrable_endpoint`: on constant Hermitian data a branch with
  `t_{b_{i₀}} - t_{a_{i₀}} = τ` gives the endpoint error against `exp(-iτH_x)` on `E ∘ |i₀⟩`;
* `main_max_windows_integrable`: `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` (value calls) and
  the same for the counts, under this criterion.
-/

namespace TimeDependentLowerBoundExtensions.Coherent

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open TimeDependentHamiltonianLowerBound (constData constProp)
open IntegrablePathSimulation.Propagator (SolvesIntegralOn)
open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

section Criteria

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The guarantee of `IntegrablePathSimulation.Coherent.coherent_windows`** for one program and
one public table of windows `[t_{a_i}, t_{b_i}]` on a mesh `t` with `M` intervals and final time
`T`: for every instance, every path `H` Hermitian at almost every time of `[0, T]` and interval
integrable on `[0, T]`, whose integrated sample errors are at most `ε / 3`, and every family
`V_i` of integral-sense solutions of that path on `[t_{a_i}, t_{b_i}]` with `V_i(t_{a_i}) = 1`,
the full output is within `ε` of `∑_i |i⟩⟨i| ⊗ V_i(t_{b_i})`. -/
def WindowsIntegrableCriterion (run : X → K →L[ℂ] K) (E : ODEJointNative.Public ι N →L[ℂ] K)
    (D : Data (X × Fin M) N Z s) (t : ℕ → ℝ) (T : ℝ) (a b : ι → ℕ) (ε : ℝ) : Prop :=
  ∀ x, ∀ (H : ℝ → Matrix N N ℂ) (V : ι → ℝ → EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N),
    (∀ᵐ u, u ∈ Icc 0 T → (H u).IsHermitian) →
    IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 T →
    ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
      ‖SparseStateOverlap.matrixOperator (H u) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ ε / 3 →
    (∀ i, V i (t (a i)) = 1) →
    (∀ i, SolvesIntegralOn (fun u => SparseStateOverlap.matrixOperator (H u)) (V i)
      (t (a i)) (t (b i))) →
    ‖run x ∘L E - E ∘L WeightedClock.diagonal (fun i => V i (t (b i)))‖ ≤ ε

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] [CompleteSpace K] in
/-- **A window of length `τ` is a simulation, integrable-path criterion**: on constant Hermitian
data, if the window of the branch `i₀` has length `t_{b_{i₀}} - t_{a_{i₀}} = τ`, the guarantee of
`coherent_windows` gives the endpoint error `ε` against `exp(-iτH_x)` on the encoding
`E ∘ |i₀⟩` (the constant path has zero sample error, and `V_i(u) = exp(-i(u - t_{a_i})H_x)`
are integral-sense solutions from the identity on every window). -/
theorem windowsIntegrable_endpoint (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian)
    (M : ℕ) (t : ℕ → ℝ) (T : ℝ) (a b : ι → ℕ) (i₀ : ι) {τ ε : ℝ} (hε : 0 ≤ ε)
    (hlen : t (b i₀) - t (a i₀) = τ) (run : X → K →L[ℂ] K)
    (E : ODEJointNative.Public ι N →L[ℂ] K)
    (hcrit : WindowsIntegrableCriterion run E (constData D M) t T a b ε) (x : X) :
    ‖run x ∘L (E ∘L branchInj ι N i₀) - (E ∘L branchInj ι N i₀) ∘L
      NormedSpace.exp ((-Complex.I * (τ : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))‖
        ≤ ε := by
  set H := SparseStateOverlap.matrixOperator (D.matrix x)
  have hc : ∀ r : Fin M, (constData D M).matrix (x, r) = D.matrix x := fun _ => rfl
  have hV : ∀ c : ℝ, ∀ u, HasDerivAt (fun v => constProp H (v - c))
      ((-Complex.I) • (H * constProp H (u - c))) u := fun c u =>
    (TimeDependentHamiltonianLowerBound.hasDerivAt_constProp H (u - c)).comp_sub_const u c
  have hSol : ∀ i, SolvesIntegralOn (fun _ => H) (fun u => constProp H (u - t (a i)))
      (t (a i)) (t (b i)) := by
    intro i
    by_cases hab : t (a i) ≤ t (b i)
    · exact IntegrablePathSimulation.Propagator.solvesIntegralOn_of_solvesOn hab
        (fun u _ => (hV (t (a i)) u).hasDerivWithinAt) intervalIntegrable_const
    · have hcont : Continuous fun u => H * constProp H (u - t (a i)) :=
        continuous_const.mul
          (continuous_iff_continuousAt.2 fun u => (hV (t (a i)) u).continuousAt)
      exact ⟨hcont.intervalIntegrable _ _, fun v hv => absurd (hv.1.trans hv.2) hab⟩
  have hW := hcrit x (fun _ => D.matrix x) (fun i u => constProp H (u - t (a i)))
    (Filter.Eventually.of_forall fun _ _ => hH x) intervalIntegrable_const
    (by simp [hc]; positivity)
    (fun i => by simp [TimeDependentHamiltonianLowerBound.constProp_zero]) hSol
  refine endpoint_of_comp (run x) E _ i₀ _ ?_ hW
  rw [diagonal_comp_branchInj]
  congr 1
  show constProp H (t (b i₀) - t (a i₀)) = _
  rw [hlen]
  rfl

end Criteria

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` with coherent start times and durations, integrable-path
criterion** (eq. `hsl:eq:main`, max form): as `main_max_windows`, for programs over the released
selection family on the constant time, mixed and precision data meeting the guarantee of
`IntegrablePathSimulation.Coherent.coherent_windows` (`WindowsIntegrableCriterion`, any mesh `t`,
final times `fT`, `fM`, `fP` and public tables of windows) with a branch whose window has length
`τ`: `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` with `Q` the value calls, and the same for
the counts. -/
theorem main_max_windows_integrable (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [DecidableEq ιT] [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (MT MM MP NT NM NP : ℕ) (γT ρT TT εT γM ρM TM εM γP ρP TP εP : ℝ) (tT tM tP : ℕ → ℝ)
    (fT fM fP : ℝ)
    (aT bT : ιT → ℕ) (aM bM : ιM → ℕ) (aP bP : ιP → ℕ) (iT : ιT) (iM : ιM) (iP : ιP)
    (hlT : tT (bT iT) - tT (aT iT) = τ) (hlM : tM (bM iM) - tM (aM iM) = τ)
    (hlP : tP (bP iP) - tP (aP iP) = τ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιT)
      (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT))
    (ET : ODEJointNative.Public ιT (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      SelTimeWork ιT τ s MT NT γT ρT TT εT) (hET : ET† ∘L ET = 1)
    (hT : WindowsIntegrableCriterion pT.eval ET (constData (timeData τ s h.s_ge) MT) tT fT aT bT
      ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιM)
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM))
    (EM : ODEJointNative.Public ιM (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      SelMixedWork ιM τ ε s MM NM γM ρM TM εM) (hEM : EM† ∘L EM = 1)
    (hM : WindowsIntegrableCriterion pM.eval EM (constData (mixedMainData τ ε s h.s_ge) MM) tM fM
      aM bM ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιP)
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP))
    (EP : ODEJointNative.Public ιP (ScalarIndex (precN τ ε) s) →L[ℂ]
      SelPrecisionWork ιP τ ε s MP NP γP ρP TP εP) (hEP : EP† ∘L EP = 1)
    (hP : WindowsIntegrableCriterion pP.eval EP (constData (precisionMainData τ ε s h.s_ge) MP) tP
      fP aP bP ε) :
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
      (windowsIntegrable_endpoint _ hHT.isHermitian MT tT fT aT bT iT hε hlT pT.eval ET hT)
      _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (mixedMainData τ ε s h.s_ge)
        (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) MM NM γM ρM TM εM)
      pM (EM ∘L branchInj ιM _ iM) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iM) hEM)
      (windowsIntegrable_endpoint _ hHM.isHermitian MM tM fM aM bM iM hε hlM pM.eval EM hM)
      _ (TimeDependentExtensions.MeshSelect.alignedOracle_unitary _ _ _ _ _ _)
      hardCost (nonempty_selectAccess (precisionMainData τ ε s h.s_ge)
        (scalarAccess (by have := h.s_ge; omega)) MP NP γP ρP TP εP)
      pP (EP ∘L branchInj ιP _ iP) (NativeSparseAttenuation.isometry_comp _ _
        (branchInj_isometry iP) hEP)
      (windowsIntegrable_endpoint _ hHP.isHermitian MP tP fP aP bP iP hε hlP pP.eval EP hP))

end

end TimeDependentLowerBoundExtensions.Coherent
