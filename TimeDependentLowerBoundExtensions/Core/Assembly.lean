import TimeDependentHamiltonianLowerBound.Release

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for any oracle family with Boolean certificates

The three hard families of Theorem `hsl:thm:main` (the manuscript, lines 2102-2119) are proved
hard through Boolean phase-oracle certificates: every label of the algorithm's oracle family is
implemented, on one fixed isometric encoding, by a bounded number of queries of a Boolean phase
oracle (`SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess`), and the general family lemmas
`SparseLowerBounds.Hamiltonian.time_general`, `mixed_general` and `precision_general` bound the
Boolean cost `p.cost w`. This module states the max form once for **any** three oracle families
with such certificates and any weights:

* `main_max_access`: for programs over families `O_T`, `O_M`, `O_P` with certificates of
  weights `w_T`, `w_M`, `w_P` and endpoint error `ε` against `exp(-iτH_x)`,
  `2 c₀ (√s τ + √(sτr) + r) ≤ max(p_T.cost w_T, p_M.cost w_M, p_P.cost w_P)`;
* `main_max_uniform_weight`: the same with one constant weight `c` per call,
  `2 c₀ (√s τ + √(sτr) + r) ≤ c · max(count_T, count_M, count_P)`;
* `nonempty_access_of_normal_form`: a family of the normal form
  `U⁻¹ (1_Ω ⊗ oracles D l x) U` inherits every certificate of the native primitives, with the
  same weights.

`main_max_access` contains the released max forms over certified families as special cases
(`SparseLowerBounds.Hamiltonian.main_max_release_cost` for the released time-independent
families, `TimeDependentHamiltonianLowerBound.main_max_sampled` for the sampled-time families).
All later bounds of this library (time-indexed block encodings, coherent selection, call forms
and gate-level circuits) are instances.
-/

namespace TimeDependentLowerBoundExtensions.Core

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout HsRelease
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-! ### Normal forms inherit certificates -/

section Normal

variable {I : Type*} [Fintype I] {X : Type*} {y : X → I → Bool}
variable {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]

/-- **Normal forms inherit Boolean certificates**: if every label of `O` is
`U⁻¹ (1_Ω ⊗ oracles D l x) U` for one fixed isometric identification `U`, every Boolean
certificate of the native primitives of `D` gives one of `O` with the same weights. This is
the case `F = oracles D`, `W A = U⁻¹ (1_Ω ⊗ A) U` of `Core.nonempty_access_of_wrap`. -/
theorem nonempty_access_of_normal_form {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (D : Data X N Z s) {w : Query → ℕ} (A : PhaseAccess I y (oracles D) w)
    {O : Query → X → K →L[ℂ] K}
    (hO : ∃ (Ω : Type) (_ : Fintype Ω) (U : K ≃ₗᵢ[ℂ] Joint Ω (SparseFlagEmbedding.Space (N × N) Z)),
      ∀ l x, O l x = U.symm.conjStarAlgEquiv (specOracles Ω D l x)) :
    Nonempty (PhaseAccess I y O w) := by
  obtain ⟨Ω, _, U, hU⟩ := hO
  exact ⟨((A.spectate Ω).conj U.symm).congr (fun l x => (hU l x).symm)⟩

end Normal

/-! ### The max form for certified families -/

/-- **Theorem `hsl:thm:main` for any three certified oracle families, Boolean-cost max form**
(eq. `hsl:eq:main`, `c₀ = log 2/(4096π)`): for programs over unitary families `O_T`, `O_M`,
`O_P` of the time, mixed and precision families with Boolean certificates of weights `w_T`,
`w_M`, `w_P`, isometric encodings and endpoint error `ε` against `exp(-iτH_x)` on every input,
`2 c₀ (√s τ + √(sτr) + r) ≤ max(p_T.cost w_T, p_M.cost w_M, p_P.cost w_P)`. -/
theorem main_max_access (h : HSRange τ s ε)
    {LT LM LP KT KM KP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    (OT : LT → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT)
    (hOT : ∀ l x, IsUnitary (OT l x)) (wT : LT → ℕ)
    (AT : Nonempty (PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern OT wT))
    (pT : MultiOracleCircuit.Program OT)
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] KT) (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (OM : LM → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM)
    (hOM : ∀ l x, IsUnitary (OM l x)) (wM : LM → ℕ)
    (AM : Nonempty (PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern OM wM))
    (pM : MultiOracleCircuit.Program OM)
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] KM) (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (OP : LP → (Fin (precN τ ε) → Bool) → KP →L[ℂ] KP)
    (hOP : ∀ l x, IsUnitary (OP l x)) (wP : LP → ℕ)
    (AP : Nonempty (PhaseAccess (Fin (precN τ ε)) bitPattern OP wP))
    (pP : MultiOracleCircuit.Program OP)
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] KP) (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
      max (pT.cost wT : ℝ) (max (pM.cost wM : ℝ) (pP.cost wP)) := by
  obtain ⟨AT⟩ := AT
  obtain ⟨AM⟩ := AM
  obtain ⟨AP⟩ := AP
  have hT : cT * Real.sqrt s * τ ≤ (pT.cost wT : ℝ) / 2 := by
    obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program hOT pT ιT hιT refZero
      (hard_instances h).1.isHermitian (norm_searchInput _ _ _) hsimT
    have hb := (time_general h.one_le_tau h.s_ge h.eps_le AT.fam AT.enc AT.enc_isometry OT hOT
      wT (fun l => AT.implementsOn_oneHot l) pT _ hψ _ (endpointReadout_isometry ιT hιT refZero)
      hacc).2
    linarith
  have hM : 64 * τ ≤ hsL ε → 64 * (precN τ ε : ℝ) / τ ≤ s →
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        (pM.cost wM : ℝ) / 2 := by
    intro hL hs
    obtain ⟨hψ, hacc⟩ := accurate_of_endpoint_program hOM pM ιM hιM refZero
      (hard_instances h).2.1.isHermitian (norm_searchInput _ _ _) hsimM
    obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
    have h16 := sixteen_eps_le h hL
    have hb := mixed_general (n := precN τ ε) (μ := hsMu s) (s := s) (τ := τ) (ε := ε) hn
      (by linarith [h.one_le_tau]) (by linarith) (mixed_m_cond h hs) (by linarith [h.eps_pos])
      AM.fam AM.enc AM.enc_isometry OM hOM wM (fun l => AM.implementsOn_oneHot l) pM _ hψ _
      (endpointReadout_isometry ιM hιM refZero) hacc
    have hnum := mixrbound h hL
    linarith
  have hP : 64 * τ ≤ hsL ε → hsR τ ε / 32 ≤ (pP.cost wP : ℝ) / 2 ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ (pP.cost wP : ℝ) / 2) := by
    intro hL
    obtain ⟨-, hacc⟩ := accurate_of_endpoint_program hOP pP ιP hιP refZero
      (hard_instances h).2.2.1.isHermitian (norm_scalarInput _ _) hsimP
    obtain ⟨hn, hrn, hτr, -⟩ := precN_range h hL
    have h16 := sixteen_eps_le h hL
    have hb := precision_general (n := precN τ ε) (s := s) (τ := τ) (ε := ε) (by omega)
      (by linarith [h.one_le_tau]) (by linarith) (by linarith [h.eps_pos])
      AP.fam AP.enc AP.enc_isometry OP hOP wP (fun l => AP.implementsOn_bit l) pP _ _ hacc
    have hrb := rbound h hL
    exact ⟨by linarith, fun hs' => by have := failedmix h hL hs'; linarith⟩
  have key := assembly h hT hP hM
  have h1 := le_max_left (pT.cost wT : ℝ) (max (pM.cost wM : ℝ) (pP.cost wP))
  have h2 := le_max_right (pT.cost wT : ℝ) (max (pM.cost wM : ℝ) (pP.cost wP))
  have h3 := le_max_left (pM.cost wM : ℝ) (pP.cost wP)
  have h4 := le_max_right (pM.cost wM : ℝ) (pP.cost wP)
  have hmax : max ((pT.cost wT : ℝ) / 2) (max ((pM.cost wM : ℝ) / 2) ((pP.cost wP : ℝ) / 2)) ≤
      max (pT.cost wT : ℝ) (max (pM.cost wM : ℝ) (pP.cost wP)) / 2 :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  linarith

/-- **Constant weight per call**: under the hypotheses of `main_max_access` with the constant
weights `fun _ => c`, `2 c₀ (√s τ + √(sτr) + r) ≤ c · max(count_T, count_M, count_P)`. -/
theorem main_max_uniform_weight (h : HSRange τ s ε) (c : ℕ)
    {LT LM LP KT KM KP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    (OT : LT → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT)
    (hOT : ∀ l x, IsUnitary (OT l x))
    (AT : Nonempty (PhaseAccess (Fin (timeN τ) × Fin (2 ^ hsMu s)) oneHotPattern OT
      (fun _ => c)))
    (pT : MultiOracleCircuit.Program OT)
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] KT) (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖pT.eval j ∘L ιT - ιT ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (OM : LM → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM)
    (hOM : ∀ l x, IsUnitary (OM l x))
    (AM : Nonempty (PhaseAccess (Fin (precN τ ε) × Fin (2 ^ hsMu s)) oneHotPattern OM
      (fun _ => c)))
    (pM : MultiOracleCircuit.Program OM)
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] KM) (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖pM.eval j ∘L ιM - ιM ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (OP : LP → (Fin (precN τ ε) → Bool) → KP →L[ℂ] KP)
    (hOP : ∀ l x, IsUnitary (OP l x))
    (AP : Nonempty (PhaseAccess (Fin (precN τ ε)) bitPattern OP (fun _ => c)))
    (pP : MultiOracleCircuit.Program OP)
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] KP) (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖pP.eval x ∘L ιP - ιP ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    2 * (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ≤
      c * max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hb := main_max_access h OT hOT (fun _ => c) AT pT ιT hιT hsimT OM hOM (fun _ => c) AM
    pM ιM hιM hsimM OP hOP (fun _ => c) AP pP ιP hιP hsimP
  rw [MultiOracleCircuit.Program.cost_const, MultiOracleCircuit.Program.cost_const,
    MultiOracleCircuit.Program.cost_const] at hb
  push_cast at hb
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [mul_max_of_nonneg _ _ hc, mul_max_of_nonneg _ _ hc]
  simpa only [mul_comm] using hb

end

end TimeDependentLowerBoundExtensions.Core
