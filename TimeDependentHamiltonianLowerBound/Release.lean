import TimeDependentHamiltonianLowerBound.Access
import TimeDependentHamiltonianLowerBound.Class

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for programs over the released time-dependent oracles

The remark after Theorem `hs:thm:time` (the paragraphs after its proof): the
lower bound of Theorem `hsl:thm:main` applies to the time-dependent classes, since the
time-independent hard instances satisfy their assumptions with `β = δ_val = 0`. Here the
algorithms are programs over the oracle families of the released time-dependent simulators,
run on the constant data of the hard families (every sample equal to the time-independent
instance, any number `M` of samples), with any schedule of the physical workspace, any
isometric input encoding `ι`, inverse calls included, location calls free.

* `time_sampled`, `mixed_sampled`, `precision_sampled`: per-family bounds for every program
  over the aligned family `AlignedMultiOracleProgram.oracle (Sampled.oracle (constData D M) T d)`
  (any `M`, slot count `T` and degree `d`) with endpoint error `ε` against `exp(-iτH_x)`:
  `c_T √s τ`, `(log 2/(384√2)) √(sτr)` (for `L ≥ 64τ`, `s ≥ 64n/τ`), `r/32` and, for
  `s < 64n/τ`, `√(sτr)/(64√2)` (for `L ≥ 64τ`) value queries; except for the last, the
  Boolean cost `p.cost hardCost = 2Q` is at least twice the bound, and `p.count` at least the
  bound.
* `main_max_sampled`: max form, eq. `hsl:eq:main`,
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` (and the same for the release counts).
* `main_max_uniform`: the same for programs over the uniform-mesh family
  `TimeDependent.oracle (constData D M) γ η t ε'` (any `M` and schedule) meeting the error
  criterion of `TimeDependent.simulation` on the constant path (`UniformGuarantee`: error at
  most `ε` against every propagator of the path at time `τ`).
* `main_max_mesh`: programs over the general-mesh family
  `TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε'` meeting the criterion
  of `TimeDependentExtensions.Hamiltonian.simulation` on the constant pieces (`MeshCriterion`,
  any mesh `t`).
* `main_max_integrable`: programs over the same family meeting the criterion of
  `IntegrablePathSimulation.Hamiltonian.simulation` on the constant path
  (`IntegrableCriterion`: every integral-sense propagator).

Proof route: the criteria give the endpoint error (`uniform_criterion_iff`,
`endpoint_of_mesh`, `integrable_criterion_iff`); `accurate_of_endpoint_program` (seed `ι ψ_in`,
readout `endpointReadout ι r₀`) gives `Readout.Accurate`; the general family lemmas
`time_general`, `mixed_general`, `precision_general` with the certificates of `Access`
(`*_sampled_implementsOn`, weight `hardCost`) give the Boolean cost; `native_bound_of_cost`,
the numerics of `SparseLowerBounds.Hamiltonian` and `assembly` finish, exactly as for the
released `main_max_release`.
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-! ### The three families over the aligned family -/

/-- **Time family, released time-dependent oracles**: every program over the aligned family of
the constant time family (any `M`, `T`, `d`) with endpoint error `ε` against `exp(-iτH_j)` makes
at least `c_T √s τ` value queries (`c_T = log 2/(192π)`), hence as many queries, and has Boolean
cost at least `2 c_T √s τ` (eq. `hsl:eq:timelower`). -/
theorem time_sampled (h : HSRange τ s ε) (M T d : ℕ)
    (p : MultiOracleCircuit.Program (AlignedMultiOracleProgram.oracle
      (TimeDependent.Sampled.oracle (constData (timeData τ s h.s_ge) M) T d)))
    (ι : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] TimeWork τ s M T d)
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε) :
    2 * (cT * Real.sqrt s * τ) ≤ p.cost hardCost ∧ cT * Real.sqrt s * τ ≤ p.labelCount .value ∧
      cT * Real.sqrt s * τ ≤ p.count := by
  have hU := aligned_oracle_unitary (constData (timeData τ s h.s_ge) M) T d
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program hU p ι hι refZero
    (hard_instances h).1.isHermitian (norm_searchInput _ _ _) hsim
  obtain ⟨hE, hw⟩ := time_sampled_implementsOn (τ := τ) h.s_ge M T d
  have hb := (time_general h.one_le_tau h.s_ge h.eps_le _ _ hE _ hU hardCost hw p _ hψ _
    (endpointReadout_isometry ι hι refZero) hacc).2
  have hb' : 2 * (cT * Real.sqrt s * τ) ≤ p.cost hardCost := by linarith
  exact ⟨hb', native_bound_of_cost p hb'⟩

/-- **Mixed family, released time-dependent oracles**: for `L ≥ 64τ` and `s ≥ 64n/τ`, every
program over the aligned family of the constant mixed family with endpoint error `ε` makes at
least `(log 2/(384√2)) √(sτr)` value queries (eq. `hsl:eq:mixrbound`). -/
theorem mixed_sampled (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (M T d : ℕ)
    (p : MultiOracleCircuit.Program (AlignedMultiOracleProgram.oracle
      (TimeDependent.Sampled.oracle (constData (mixedMainData τ ε s h.s_ge) M) T d)))
    (ι : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] MixedWork τ ε s M T d)
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε) :
    2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) ≤ p.cost hardCost ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  have hU := aligned_oracle_unitary (constData (mixedMainData τ ε s h.s_ge) M) T d
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program hU p ι hι refZero
    (hard_instances h).2.1.isHermitian (norm_searchInput _ _ _) hsim
  obtain ⟨hE, hw⟩ := mixed_sampled_implementsOn (τ := τ) (ε := ε) h.s_ge M T d
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hb := mixed_general (n := precN τ ε) (μ := hsMu s) (s := s) (τ := τ) (ε := ε) hn
    (by linarith [h.one_le_tau]) (by linarith) (mixed_m_cond h hs) (by linarith [h.eps_pos])
    _ _ hE _ hU hardCost hw p _ hψ _ (endpointReadout_isometry ι hι refZero) hacc
  have hnum := mixrbound h hL
  have hb' : 2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) ≤
      p.cost hardCost := by linarith
  exact ⟨hb', native_bound_of_cost p hb'⟩

/-- **Precision family, released time-dependent oracles**: for `L ≥ 64τ`, every program over
the aligned family of the constant precision family with endpoint error `ε` makes at least
`r/32` value queries, and at least `√(sτr)/(64√2)` when `s < 64n/τ` (eqs. `hsl:eq:rbound`,
`hsl:eq:failedmix`). -/
theorem precision_sampled (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (M T d : ℕ)
    (p : MultiOracleCircuit.Program (AlignedMultiOracleProgram.oracle
      (TimeDependent.Sampled.oracle (constData (precisionMainData τ ε s h.s_ge) M) T d)))
    (ι : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] PrecisionWork τ ε s M T d)
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ x, ‖p.eval x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    2 * (hsR τ ε / 32) ≤ p.cost hardCost ∧ hsR τ ε / 32 ≤ p.labelCount .value ∧
      hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  have hU := aligned_oracle_unitary (constData (precisionMainData τ ε s h.s_ge) M) T d
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program hU p ι hι refZero
    (hard_instances h).2.2.1.isHermitian (norm_scalarInput _ _) hsim
  obtain ⟨hE, hw⟩ := precision_sampled_implementsOn (τ := τ) (ε := ε) h.s_ge M T d
  obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
  have h16 := sixteen_eps_le h hL
  have hb := precision_general (n := precN τ ε) (s := s) (τ := τ) (ε := ε) (by omega)
    (by linarith [h.one_le_tau]) (by linarith) (by linarith [h.eps_pos])
    _ _ hE _ hU hardCost hw p _ _ hacc
  have hrb := rbound h hL
  have hq : 2 * ((precN τ ε : ℝ) / 4) ≤ p.cost hardCost := by linarith
  have hb' : 2 * (hsR τ ε / 32) ≤ p.cost hardCost := by linarith
  have hQ := native_bound_of_cost p hb'
  exact ⟨hb', hQ.1, hQ.2,
    fun hs' => (failedmix h hL hs').trans (native_bound_of_cost p hq).1⟩

/-! ### Combined statements -/

/-- **Theorem `hsl:thm:main` for the released time-dependent oracles, endpoint form, max**
(eq. `hsl:eq:main`, `c₀ = log 2/(4096π)`): for any three programs over the aligned families of
the constant time, mixed and precision families (any mesh sizes, slot counts and degrees),
each with endpoint error `ε` on its family,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the same for the counts. -/
theorem main_max_sampled (h : HSRange τ s ε) (MT TT dT MM TM dM MP TP dP : ℕ)
    (pT : MultiOracleCircuit.Program (AlignedMultiOracleProgram.oracle
      (TimeDependent.Sampled.oracle (constData (timeData τ s h.s_ge) MT) TT dT)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] TimeWork τ s MT TT dT)
    (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (pM : MultiOracleCircuit.Program (AlignedMultiOracleProgram.oracle
      (TimeDependent.Sampled.oracle (constData (mixedMainData τ ε s h.s_ge) MM) TM dM)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] MixedWork τ ε s MM TM dM)
    (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (pP : MultiOracleCircuit.Program (AlignedMultiOracleProgram.oracle
      (TimeDependent.Sampled.oracle (constData (precisionMainData τ ε s h.s_ge) MP) TP dP)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] PrecisionWork τ ε s MP TP dP)
    (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hQ : c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
    refine assembly h (time_sampled h MT TT dT pT ιT hιT hsimT).2.1 (fun hL => ?_)
      (fun hL hs => (mixed_sampled h hL hs MM TM dM pM ιM hιM hsimM).2.1)
    have hP := precision_sampled h hL MP TP dP pP ιP hιP hsimP
    exact ⟨hP.2.1, hP.2.2.2⟩
  have hT' : (pT.labelCount .value : ℝ) ≤ pT.count := by
    exact_mod_cast labelCount_le_count pT .value
  have hM' : (pM.labelCount .value : ℝ) ≤ pM.count := by
    exact_mod_cast labelCount_le_count pM .value
  have hP' : (pP.labelCount .value : ℝ) ≤ pP.count := by
    exact_mod_cast labelCount_le_count pP .value
  exact ⟨hQ, hQ.trans (max_le_max hT' (max_le_max hM' hP'))⟩

/-- **Theorem `hsl:thm:main` for programs over the uniform-mesh released oracles**
(`TimeDependent.oracle`, Theorem `hs:thm:time`), max form: for any three programs over the
uniform-mesh families of the constant time, mixed and precision data (any numbers of samples
`M` and schedules `γ η t ε'`) and isometric encodings, each meeting the error criterion of
`TimeDependent.simulation` on the constant path of its family at time `τ` (error at most `ε`
against every propagator, `UniformGuarantee`),
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the same for the counts. -/
theorem main_max_uniform (h : HSRange τ s ε) (MT MM MP : ℕ)
    (γT ηT tT εT γM ηM tM εM γP ηP tP εP : ℝ)
    (pT : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (timeData τ s h.s_ge) MT) γT ηT tT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      TimeDependent.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT γT ηT tT εT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : UniformGuarantee pT.eval ιT (constPath (timeData τ s h.s_ge)) τ ε)
    (pM : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) MM) γM ηM tM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      TimeDependent.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM γM ηM tM εM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : UniformGuarantee pM.eval ιM (constPath (mixedMainData τ ε s h.s_ge)) τ ε)
    (pP : MultiOracleCircuit.Program
      (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) MP) γP ηP tP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      TimeDependent.Workspace (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ)) s
        MP γP ηP tP εP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : UniformGuarantee pP.eval ιP (constPath (precisionMainData τ ε s h.s_ge)) τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  exact main_max_sampled h MT MT _ MM MM _ MP MP _ pT ιT hιT
    ((uniform_criterion_iff _ pT.eval ιT hτ).1 hT) pM ιM hιM
    ((uniform_criterion_iff _ pM.eval ιM hτ).1 hM) pP ιP hιP
    ((uniform_criterion_iff _ pP.eval ιP hτ).1 hP)

/-- **Theorem `hsl:thm:main` for programs over the general-mesh released oracles**
(`TimeDependentExtensions.Hamiltonian.oracle`), max form: for any three programs over the
general-mesh families of the constant time, mixed and precision data (any numbers of mesh
intervals `M`, slot counts `N` and schedules) and isometric encodings, each meeting the error
criterion of `TimeDependentExtensions.Hamiltonian.simulation` on the constant pieces of its
family (`MeshCriterion`, any mesh `t`, final time `τ`),
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the same for the counts. -/
theorem main_max_mesh (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ) (tT tM tP : ℕ → ℝ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) MT) NT γT ηT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT NT γT ηT TT εT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : MeshCriterion pT.eval ιT (constPath (timeData τ s h.s_ge)) tT MT τ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM NM γM ηM TM εM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : MeshCriterion pM.eval ιM (constPath (mixedMainData τ ε s h.s_ge)) tM MM τ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s MP NP γP ηP TP εP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : MeshCriterion pP.eval ιP (constPath (precisionMainData τ ε s h.s_ge)) tP MP τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) :=
  main_max_sampled h MT NT _ MM NM _ MP NP _ pT ιT hιT (endpoint_of_mesh _ pT.eval ιT hT) pM ιM
    hιM (endpoint_of_mesh _ pM.eval ιM hM) pP ιP hιP (endpoint_of_mesh _ pP.eval ιP hP)

/-- **Theorem `hsl:thm:main` for programs over the released oracles for integrable paths**
(`TimeDependentExtensions.Hamiltonian.oracle`, the family of
`IntegrablePathSimulation.Hamiltonian.simulation`), max form: for any three programs over the
general-mesh families of the constant time, mixed and precision data and isometric encodings,
each meeting the error criterion of the integrable-path theorem on the constant path of its
family (`IntegrableCriterion`: error at most `ε` against every integral-sense propagator at
time `τ`), `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, and the same for the counts. -/
theorem main_max_integrable (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) MT) NT γT ηT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT NT γT ηT TT εT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : IntegrableCriterion pT.eval ιT (constPath (timeData τ s h.s_ge)) τ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM NM γM ηM TM εM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : IntegrableCriterion pM.eval ιM (constPath (mixedMainData τ ε s h.s_ge)) τ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s MP NP γP ηP TP εP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : IntegrableCriterion pP.eval ιP (constPath (precisionMainData τ ε s h.s_ge)) τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  exact main_max_sampled h MT NT _ MM NM _ MP NP _ pT ιT hιT
    ((integrable_criterion_iff _ pT.eval ιT hτ).1 hT) pM ιM hιM
    ((integrable_criterion_iff _ pM.eval ιM hτ).1 hM) pP ιP hιP
    ((integrable_criterion_iff _ pP.eval ιP hτ).1 hP)

end

end TimeDependentHamiltonianLowerBound
