import SparseLowerBounds.Hamiltonian.Herald

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Theorem `hsl:thm:main` in the release's endpoint form

Manuscript: Section `hsl:sec:main`, after eq. `hsl:eq:accuracy` ("The complete-output norm
guarantee of our upper bounds implies this weaker requirement after the work registers are
discarded"). The release's simulation theorem
`ImprovedSparseHamiltonian.simulation_log_one` certifies an algorithm by the
endpoint error

  `‖p.eval x ∘L ι - ι ∘L exp(-iτ H_x)‖ ≤ ε`

for a fixed isometric input encoding `ι`. This module states the lower bounds
of `Hamiltonian/Theorem` under exactly that hypothesis, for programs over the
native primitives of the hard families without (`*_endpoint_native`) or with
(`*_endpoint`) an untouched spectator register. The seed is `ι ψ_in` and the
readout is the constructed isometry `endpointReadout ι r₀`
(`Hamiltonian/Accuracy`), so endpoint error `ε` gives `Readout.Accurate`
(`accurate_of_endpoint_program`).

`hard_data_meet_release_hypotheses`: the three hard families satisfy the
hypotheses `hH`, `hrow`, `hcol` of `simulation_log_one` with `η = 1` (and
`0 < ε ≤ 1/64 ≤ 1/2`), so the release upper bound
`count ≤ 995328 (√s τ + √(sτL) + L)` applies to the same families, in the
release's physical oracle model `ImprovedSparseHamiltonian.oracle D γ 1 τ ε`
(`release_upper`, for every `HardInstance`).

The lower bounds here are for programs over the native primitives
(`NativeSparseBlockEncoding.oracles`, with or without spectator). The release's
own simulator (`release_upper`) is instead a program over
`ImprovedSparseHamiltonian.oracle D γ 1 τ ε` on `ImprovedSparseHamiltonian.Physical`
(clean-output alignment, coherent query-schedule copies, Cayley-active and
masked layers around the native primitives), so it does not instantiate the
hypotheses of `*_endpoint` directly. The bridge is formalized in
`Hamiltonian/ReleaseAccess`, `ReleaseBridge` and `ReleaseTheta`. Its target:
the general forms (`time_general`, `mixed_general`, `precision_general`,
`*_herald_general`) accept any unitary labelled family `O` with
`hw : ∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (O l) E (w l)`
(`bitOracle P` for the precision family), and `accurate_of_endpoint_program`
is generic in `O`. So the release-algorithm corollary needs only, for some
isometric encoding `E`, the lemma
`∀ l, EncodedOracle.ImplementsOn (oneHotOracle P) (ImprovedSparseHamiltonian.oracle D γ 1 τ ε l) E (hardCost l)`
for `timeData` and `mixedMainData`, and its `bitOracle` analogue for
`precisionMainData`; it is proved in `Hamiltonian/ReleaseAccess`
(`time_release_implementsOn`, `mixed_release_implementsOn`,
`precision_release_implementsOn`), with the lower bounds for every program over
the release's physical oracle in `Hamiltonian/ReleaseBridge` and the bracket
with this upper bound in `Hamiltonian/ReleaseTheta` (`release_theta`). Controlled calls are
covered as in the module docstring of `Hamiltonian/Theorem`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ}

/-- **Endpoint error gives accuracy** for a program over unitary oracles: if
`‖p.eval x ∘L ι - ι ∘L exp(-iτH_x)‖ ≤ ε` for every input, `ι` is an
isometry, `H_x` is Hermitian and `‖ψ‖ = 1`, then the seed `ι ψ` is a unit
vector and the output read through `endpointReadout ι i₀` is `ε`-accurate for
`e^{-iτH_x} ψ` on every input. -/
theorem accurate_of_endpoint_program {S X L K : Type*} [Fintype S] [DecidableEq S]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {O : L → X → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x)) (p : MultiOracleCircuit.Program O)
    (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1) (i₀ : S) {H : X → Matrix S S ℂ}
    (hH : ∀ x, (H x).IsHermitian) {ψ : EuclideanSpace ℂ S} (hψ : ‖ψ‖ = 1)
    (hsim : ∀ x, ‖p.eval x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (H x))‖ ≤ ε) :
    ‖ι ψ‖ ≤ 1 ∧ ∀ x, Accurate (endpointReadout ι i₀) (p.eval x (ι ψ)) (evolve (H x) τ ψ) ε := by
  refine ⟨by rw [Reduction.norm_encode ι hι, hψ], fun x => ?_⟩
  exact accurate_of_endpoint ι hι i₀ (p.eval x) (p.eval_unitary hO x).norm_le_one
    (evolve (H x) τ) hψ.le (by rw [norm_evolve_apply (hH x), hψ]) (hsim x)

/-! ### Spectator form -/

/-- **Time family, endpoint form** (`time_main` under the release's endpoint
error): `Q ≥ c_T √s τ`. -/
theorem time_endpoint (h : HSRange τ s ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (timeData τ s h.s_ge)))
    (ι : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Ω (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (specOracles_unitary Ω _) p ι hι refZero
    (hard_instances h).1.isHermitian (norm_searchInput _ _ _) hsim
  exact time_main h Ω p _ hψ _ (endpointReadout_isometry ι hι refZero) hacc

/-- **Mixed family, endpoint form** (`mixed_main` under the release's endpoint
error): for `L ≥ 64τ`, `s ≥ 64n/τ`, `Q ≥ (log 2/(384√2)) √(sτr)`. -/
theorem mixed_endpoint (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (mixedMainData τ ε s h.s_ge)))
    (ι : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Ω (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (specOracles_unitary Ω _) p ι hι refZero
    (hard_instances h).2.1.isHermitian (norm_searchInput _ _ _) hsim
  exact mixed_main h hL hs Ω p _ hψ _ (endpointReadout_isometry ι hι refZero) hacc

/-- **Precision family, endpoint form** (`precision_main` under the release's
endpoint error): for `L ≥ 64τ`, `Q ≥ r/32`, and `Q ≥ √(sτr)/(64√2)` when
`s < 64n/τ`. -/
theorem precision_endpoint (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (Ω : Type*) [Fintype Ω]
    (p : MultiOracleCircuit.Program (specOracles Ω (precisionMainData τ ε s h.s_ge)))
    (ι : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] Joint Ω (ScalarSpace (precN τ ε) s τ))
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ x, ‖p.eval x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    hsR τ ε / 32 ≤ p.labelCount .value ∧ hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program (specOracles_unitary Ω _) p ι hι refZero
    (hard_instances h).2.2.1.isHermitian (norm_scalarInput _ _) hsim
  exact precision_main h hL Ω p _ _ hacc

/-! ### Native form (no spectator) -/

/-- `time_endpoint` for programs over the native primitives. -/
theorem time_endpoint_native (h : HSRange τ s ε)
    (p : MultiOracleCircuit.Program (oracles (timeData τ s h.s_ge)))
    (ι : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ) (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε) :
    cT * Real.sqrt s * τ ≤ p.labelCount .value ∧ cT * Real.sqrt s * τ ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (oracles_unitary _) p ι hι refZero
    (hard_instances h).1.isHermitian (norm_searchInput _ _ _) hsim
  exact time_main_native h p _ hψ _ (endpointReadout_isometry ι hι refZero) hacc

/-- `mixed_endpoint` for programs over the native primitives. -/
theorem mixed_endpoint_native (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    (p : MultiOracleCircuit.Program (oracles (mixedMainData τ ε s h.s_ge)))
    (ι : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      SearchSpace (precN τ ε) (hsMu s) s 1 τ) (hι : ι† ∘L ι = 1)
    (hsim : ∀ j, ‖p.eval j ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ p.count := by
  obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program (oracles_unitary _) p ι hι refZero
    (hard_instances h).2.1.isHermitian (norm_searchInput _ _ _) hsim
  exact mixed_main_native h hL hs p _ hψ _ (endpointReadout_isometry ι hι refZero) hacc

/-- `precision_endpoint` for programs over the native primitives. -/
theorem precision_endpoint_native (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (p : MultiOracleCircuit.Program (oracles (precisionMainData τ ε s h.s_ge)))
    (ι : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] ScalarSpace (precN τ ε) s τ)
    (hι : ι† ∘L ι = 1)
    (hsim : ∀ x, ‖p.eval x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    hsR τ ε / 32 ≤ p.labelCount .value ∧ hsR τ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) := by
  obtain ⟨-, hacc⟩ := accurate_of_endpoint_program (oracles_unitary _) p ι hι refZero
    (hard_instances h).2.2.1.isHermitian (norm_scalarInput _ _) hsim
  exact precision_main_native h hL p _ _ hacc

/-! ### Combined statement -/

/-- **Theorem `hsl:thm:main`, endpoint form, max**: for any three
programs (spectator form) with endpoint error `ε` on the time, mixed and
precision families respectively, `max(Q_T, Q_M, Q_P) ≥ c₀ (√s τ + √(sτr) + r)`,
`c₀ = log 2/(4096π)`. -/
theorem main_max_endpoint (h : HSRange τ s ε) (ΩT ΩM ΩP : Type*)
    [Fintype ΩT] [Fintype ΩM] [Fintype ΩP]
    (pT : MultiOracleCircuit.Program (specOracles ΩT (timeData τ s h.s_ge)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint ΩT (SearchSpace (timeN τ) (hsMu s) s (timeC τ) τ)) (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (pM : MultiOracleCircuit.Program (specOracles ΩM (mixedMainData τ ε s h.s_ge)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint ΩM (SearchSpace (precN τ ε) (hsMu s) s 1 τ)) (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (pP : MultiOracleCircuit.Program (specOracles ΩP (precisionMainData τ ε s h.s_ge)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint ΩP (ScalarSpace (precN τ ε) s τ)) (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  refine assembly h (time_endpoint h ΩT pT ιT hιT hsimT).1 (fun hL => ?_) (fun hL hs => ?_)
  · have := precision_endpoint h hL ΩP pP ιP hιP hsimP
    exact ⟨this.1, this.2.2⟩
  · exact (mixed_endpoint h hL hs ΩM pM ιM hιM hsimM).1

/-! ### The release's simulation hypotheses -/

/-- **The hard families meet the hypotheses of the release's simulation
theorem** `ImprovedSparseHamiltonian.simulation_log_one` with `η = 1`:
every matrix is Hermitian (`hH`) and every row and column has Euclidean norm
at most `1` (`hrow`, `hcol`, in exactly the release's form `≤ η ^ 2`); also
`0 < ε ≤ 1/2` (`hε`, `hεHalf`). So the release upper bound
`count ≤ 995328 (√s τ + √(sτL) + L)` (endpoint error `ε`, physical oracles
`ImprovedSparseHamiltonian.oracle D γ 1 τ ε`) applies to the same three
families as the lower bounds. -/
theorem hard_data_meet_release_hypotheses (h : HSRange τ s ε) :
    (0 < ε ∧ ε ≤ 1 / 2) ∧
    (∀ j, ((timeData τ s h.s_ge).matrix j).IsHermitian ∧
      (∀ i, ∑ i', ‖(timeData τ s h.s_ge).matrix j i i'‖ ^ 2 ≤ 1 ^ 2) ∧
      (∀ i', ∑ i, ‖(timeData τ s h.s_ge).matrix j i i'‖ ^ 2 ≤ 1 ^ 2)) ∧
    (∀ j, ((mixedMainData τ ε s h.s_ge).matrix j).IsHermitian ∧
      (∀ i, ∑ i', ‖(mixedMainData τ ε s h.s_ge).matrix j i i'‖ ^ 2 ≤ 1 ^ 2) ∧
      (∀ i', ∑ i, ‖(mixedMainData τ ε s h.s_ge).matrix j i i'‖ ^ 2 ≤ 1 ^ 2)) ∧
    (∀ x, ((precisionMainData τ ε s h.s_ge).matrix x).IsHermitian ∧
      (∀ i, ∑ i', ‖(precisionMainData τ ε s h.s_ge).matrix x i i'‖ ^ 2 ≤ 1 ^ 2) ∧
      (∀ i', ∑ i, ‖(precisionMainData τ ε s h.s_ge).matrix x i i'‖ ^ 2 ≤ 1 ^ 2)) := by
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  simp only [one_pow]
  exact ⟨⟨h.eps_pos, by linarith [h.eps_le]⟩,
    fun j => ⟨hT.isHermitian j, hT.row_norm_le j, hT.col_norm_le j⟩,
    fun j => ⟨hM.isHermitian j, hM.row_norm_le j, hM.col_norm_le j⟩,
    fun x => ⟨hP.isHermitian x, hP.row_norm_le x, hP.col_norm_le x⟩⟩

/-- **The release upper bound on every hard instance**: for native data `D`
with the properties of Theorem `hsl:thm:main` (`HardInstance`, in particular
each of `timeData`, `mixedMainData`, `precisionMainData` by `hard_instances`),
`ImprovedSparseHamiltonian.simulation_log_one` with `η = 1` gives a program
over the release's physical oracles with
`count ≤ 995328 (√s |t| + √(s|t|L) + L)` and endpoint error at most `ε`. With
the lower bounds of this module this brackets the native query complexity of
the hard families, up to the passage between the release's physical oracles
and the native primitives, which is formalized in `Hamiltonian/ReleaseAccess`;
the bracket is `Hamiltonian/ReleaseTheta` (`release_theta`,
`release_theta_bracket`), up to the factor `h` of `release_shape_le`. -/
theorem release_upper {X N : Type*} [Fintype N] [DecidableEq N] {B : ℕ}
    (D : Data X N (Word B) s) (hD : HardInstance D) (t : ℝ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program (ImprovedSparseHamiltonian.oracle D γ 1 t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (1 * |t|) +
            Real.sqrt ((s : ℝ) * (1 * |t|) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (ImprovedSparseHamiltonian.input D γ 1 t ε)† ∘L ImprovedSparseHamiltonian.input D γ 1 t ε =
          1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L ImprovedSparseHamiltonian.input D γ 1 t ε -
            ImprovedSparseHamiltonian.input D γ 1 t ε ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε :=
  ImprovedSparseHamiltonian.simulation_log_one D 1 t ε one_pos hε hεHalf hD.isHermitian
    (by simpa only [one_pow] using hD.row_norm_le) (by simpa only [one_pow] using hD.col_norm_le)

end

end SparseLowerBounds.Hamiltonian
end
