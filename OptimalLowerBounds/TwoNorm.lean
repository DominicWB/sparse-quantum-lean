import OptimalLowerBounds.Enlarge
import OptimalLowerBounds.Optimal
import TwoNormSimulation.TwoNorm

set_option synthInstance.maxHeartbeats 400000

/-!
# Proposition `hsl:prop:two-norm`: a matching lower bound with a maximum-entry promise

Proposition `hsl:prop:two-norm` (Section `twonorml:sec:lower`): let `m ≥ 1` and `s₀ ≥ 32` be
integers, `μ > 0` dyadic, `s = m s₀`, `η = μ√m`, `θ = μ m |t| = η²|t|/μ ≥ 1`, `L = log(1/ε)`,
`r_μ = L/log(e + L/θ)`. For `0 < ε ≤ 1/64` there are real-symmetric, exact finite-word dyadic
Hamiltonians with maximum sparsity exactly `s`, maximum entry magnitude exactly `μ` and maximum row
and column Euclidean norms exactly `η`, "requiring `Ω(√s η|t| + √(sμ|t| r_μ) + r_μ)` queries" (eq.
`twonorml:eq:lower`). "The output need only satisfy the known-input system trace-distance guarantee
[eq. `hsl:eq:accuracy`], with physical time `t` replacing `τ` in the target state, permitting mixed
states but no postselection." After Theorem
`hs:thm:two-norm` the manuscript adds: "Its matching lower bound is established on the aligned
parameter families of Proposition `hsl:prop:two-norm`".

**The families** (module `Enlarge`): the hard families of `hsl:thm:main` at sparsity `s₀` and time
`θ`, enlarged by `m` with coefficient `c` (`timeTwo`, `mixedTwo`, `precisionTwo`), where `μ = |c|`
and the sign of `c` is that of `t` (`c m t = θ`; "for negative time we negate the Hamiltonian");
`exists_coeff` provides `c` for every `μ > 0` and `t ≠ 0`. They satisfy `TwoNormInstance`
(`two_instances`); with `c = ±M/2^p` every entry is the dyadic `±M v/2^{B+p}`
(`TwoNormInstance.dyadic_entries`). The known input is `ψ_in ⊗ u_m` (`embedU`).

**The bound.** With `S' = √s η|t| + √(sμ|t| r_μ) + r_μ`, `s = s₀ m`, `η = |c|√m`, `μ = |c|`, and
`c₀ = log 2/(4096π)` (the constant of `hsl:thm:main`, unchanged: a value call of an enlarged
family costs the same two Boolean queries as one of the original family):

* `two_shape_eq` (eq. `twonorml:eq:scaling`): `S' = √s₀ θ + √(s₀ θ r_μ) + r_μ`;
* `time_two_of_access`, `mixed_two_of_access`, `precision_two_of_access`: the per-family bounds
  for any program over any certified family, from the trace-distance accuracy for the enlarged
  family (`accurate_of_embedU`, `evolve_enlarge`);
* **`two_norm_main_max`** (spectator form: any untouched spectator register `ℂ^Ω`, any garbage,
  trace-distance accuracy), **`two_norm_main_max_native`** (no spectator) and
  **`two_norm_main_max_simulates`** (the common form of the upper bounds): `c₀ S' ≤ max` of the
  three value-query counts (resp. query bounds);
* **`two_norm_theta`**: on the aligned families, `c₀ S' ≤ max` of the three common-form
  complexities `≤ 2·10¹² S'`, the upper bound being `TwoNormSimulation.two_norm_simulation`
  (`two_on_aligned`: the families meet its hypotheses).

As in Theorem `hsl:thm:main` ("We need not find one matrix on which all three mechanisms are
simultaneously difficult"; "For three nonnegative numbers, that maximum is at least one third of
their sum, which is enough for the stated joint bound"), and as the proof of the proposition says,
"the maximum of the three witnessing family bounds supplies their sum up to a constant"; hence the
max form.
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.Hamiltonian.HsRelease Readout
open scoped InnerProduct InnerProductSpace
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

/-! ### Parameters -/

/-- **Every `μ > 0` and `t ≠ 0` is covered**: the coefficient `c = ±μ` with the sign of `t` has
`|c| = μ` and `c m t = μ m |t|`. -/
theorem exists_coeff {μ t : ℝ} (hμ : 0 < μ) (ht : t ≠ 0) (m : ℕ) :
    ∃ c : ℝ, c ≠ 0 ∧ |c| = μ ∧ c * m * t = μ * m * |t| := by
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · refine ⟨-μ, by linarith, by rw [abs_neg, abs_of_pos hμ], ?_⟩
    rw [abs_of_neg hneg]; ring
  · exact ⟨μ, hμ.ne', abs_of_pos hμ, by rw [abs_of_pos hpos]⟩

/-- `θ = |c| m |t|` when `c m t = θ > 0`. -/
theorem theta_eq_abs {θ c t : ℝ} {m : ℕ} (hθ : c * m * t = θ) (hθ0 : 0 < θ) :
    θ = |c| * m * |t| := by
  have h := congrArg abs hθ
  rw [abs_mul, abs_mul, Nat.abs_cast, abs_of_pos hθ0] at h
  exact h.symm

/-- **Eq. `twonorml:eq:scaling`**: with `s = s₀ m`, `η = |c|√m`, `μ = |c|` and `θ = c m t > 0`,
`√s η|t| = √s₀ θ` and `s μ |t| = s₀ θ`, so the bound of the proposition is the bound of
`hsl:thm:main` at sparsity `s₀` and time `θ`. -/
theorem two_shape_eq {θ c t r : ℝ} {s m : ℕ} (hθ : c * m * t = θ) (hθ0 : 0 < θ) :
    Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * r) + r =
      Real.sqrt s * θ + Real.sqrt (s * θ * r) + r := by
  have hθa := theta_eq_abs hθ hθ0
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| = Real.sqrt s * θ := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg s), hθa]
    have : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0
    calc Real.sqrt s * Real.sqrt m * (|c| * Real.sqrt m) * |t| =
          Real.sqrt s * (|c| * (Real.sqrt m * Real.sqrt m) * |t|) := by ring
      _ = Real.sqrt s * (|c| * m * |t|) := by rw [this]
  have h2 : ((s * m : ℕ) : ℝ) * |c| * |t| * r = s * θ * r := by
    rw [hθa]; push_cast; ring
  rw [h1, h2]

/-! ### The per-family bounds for any certified family -/

section Generic

variable {θ ε : ℝ} {s m : ℕ} {c t : ℝ} {K G : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Accuracy for an enlarged search family is accuracy for the original family at time `θ`. -/
theorem accurate_search_of_two {n μ s : ℕ} {a τ : ℝ} (hμ : 1 ≤ μ) (hs : 2 * 2 ^ μ ≤ s)
    (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = τ)
    (e : K →L[ℂ] SysGarb (SearchIndex n μ s × Fin m) G) (Φ : K) (j : Fin n → Fin (2 ^ μ))
    (hacc : Accurate e Φ (evolve ((searchTwo n μ s a τ hμ hs m hm c hc).matrix j) t
      (embedU m (searchInput n μ s))) ε) :
    Accurate (((regroup (SearchIndex n μ s) (Fin m) G) :
        SysGarb (SearchIndex n μ s × Fin m) G →L[ℂ]
          SysGarb (SearchIndex n μ s) (Joint (Fin m) G)) ∘L e) Φ
      (evolve (searchHam n μ s a τ j) τ (searchInput n μ s)) ε := by
  rw [searchTwo_matrix, evolve_enlarge, hθ] at hacc
  exact accurate_of_embedU m hm e Φ _ ε hacc

/-- Accuracy for the enlarged scalar family is accuracy for the original family at time `θ`. -/
theorem accurate_scalar_of_two {n s : ℕ} {τ : ℝ} (hs : 2 ≤ s) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = τ) (e : K →L[ℂ] SysGarb (ScalarIndex n s × Fin m) G) (Φ : K)
    (x : Fin n → Bool)
    (hacc : Accurate e Φ (evolve ((scalarTwo n s τ hs m hm c hc).matrix x) t
      (embedU m (scalarInput n s))) ε) :
    Accurate (((regroup (ScalarIndex n s) (Fin m) G) :
        SysGarb (ScalarIndex n s × Fin m) G →L[ℂ]
          SysGarb (ScalarIndex n s) (Joint (Fin m) G)) ∘L e) Φ
      (evolve (scalarHam n s τ x) τ (scalarInput n s)) ε := by
  rw [scalarTwo_matrix, evolve_enlarge, hθ] at hacc
  exact accurate_of_embedU m hm e Φ _ ε hacc

/-- **Enlarged time family, any certified family**: every program that is `ε`-accurate on the
enlarged time family (known input `ψ_in ⊗ u_m`, time `t`, `c m t = θ`) makes at least
`c_T √s₀ θ` value queries. -/
theorem time_two_of_access (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    {O : Query → (Fin (timeN θ) → Fin (2 ^ hsMu s)) → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (timeN θ) × Fin (2 ^ hsMu s)) oneHotPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀) (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
      (embedU m (searchInput (timeN θ) (hsMu s) s))) ε) :
    2 * (cT * Real.sqrt s * θ) ≤ p.cost hardCost ∧ cT * Real.sqrt s * θ ≤ p.labelCount .value ∧
      cT * Real.sqrt s * θ ≤ p.count :=
  time_of_access h hO A p φ₀ hφ₀ _ (regroup_comp_isometry m e he)
    fun j => accurate_search_of_two _ _ hm hc hθ e _ j (hacc j)

/-- **Enlarged mixed family, any certified family**: for `L ≥ 64θ` and `s₀ ≥ 64n/θ`, at least
`(log 2/(384√2)) √(s₀ θ r_μ)` value queries. -/
theorem mixed_two_of_access (h : HSRange θ s ε) (hL : 64 * θ ≤ hsL ε)
    (hs : 64 * (precN θ ε : ℝ) / θ ≤ s) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    {O : Query → (Fin (precN θ ε) → Fin (2 ^ hsMu s)) → K →L[ℂ] K}
    (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (precN θ ε) × Fin (2 ^ hsMu s)) oneHotPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : K →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) G) (he : e† ∘L e = 1)
    (hacc : ∀ j, Accurate e (p.eval j φ₀)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε) :
    2 * (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * θ * hsR θ ε)) ≤ p.cost hardCost ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * θ * hsR θ ε) ≤ p.labelCount .value ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * θ * hsR θ ε) ≤ p.count :=
  mixed_of_access h hL hs hO A p φ₀ hφ₀ _ (regroup_comp_isometry m e he)
    fun j => accurate_search_of_two _ _ hm hc hθ e _ j (hacc j)

/-- **Enlarged precision family, any certified family**: for `L ≥ 64θ`, at least `r_μ/32` value
queries, and at least `√(s₀ θ r_μ)/(64√2)` when `s₀ < 64n/θ`. -/
theorem precision_two_of_access (h : HSRange θ s ε) (hL : 64 * θ ≤ hsL ε) (hm : 0 < m)
    (hc : c ≠ 0) (hθ : c * m * t = θ)
    {O : Query → (Fin (precN θ ε) → Bool) → K →L[ℂ] K} (hO : ∀ l x, IsUnitary (O l x))
    (A : PhaseAccess (Fin (precN θ ε)) bitPattern O hardCost)
    (p : MultiOracleCircuit.Program O) (φ₀ : K)
    (e : K →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) G)
    (hacc : ∀ x, Accurate e (p.eval x φ₀)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    2 * (hsR θ ε / 32) ≤ p.cost hardCost ∧ hsR θ ε / 32 ≤ p.labelCount .value ∧
      hsR θ ε / 32 ≤ p.count ∧
      ((s : ℝ) < 64 * precN θ ε / θ →
        Real.sqrt (s * θ * hsR θ ε) / (64 * Real.sqrt 2) ≤ p.labelCount .value) :=
  precision_of_access h hL hO A p φ₀ _
    fun x => accurate_scalar_of_two _ hm hc hθ e _ x (hacc x)

end Generic

/-- **Proposition `hsl:prop:two-norm`, max form, any certified families** (eq.
`twonorml:eq:lower`): for any three programs over certified unitary families, accurate on the
enlarged time, mixed and precision families respectively (known input `ψ_in ⊗ u_m`, time `t`,
`c m t = θ`), with `s = s₀ m`, `η = |c|√m`, `μ = |c|`, `r_μ = hsR θ ε`,
`c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(Q_T, Q_M, Q_P)`. -/
theorem two_norm_max_of_access {θ ε : ℝ} {s m : ℕ} {c t : ℝ} (h : HSRange θ s ε) (hm : 0 < m)
    (hc : c ≠ 0) (hθ : c * m * t = θ)
    {KT KM KP GT GM GP : Type*}
    [NormedAddCommGroup KT] [InnerProductSpace ℂ KT] [CompleteSpace KT]
    [NormedAddCommGroup KM] [InnerProductSpace ℂ KM] [CompleteSpace KM]
    [NormedAddCommGroup KP] [InnerProductSpace ℂ KP] [CompleteSpace KP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    {OT : Query → (Fin (timeN θ) → Fin (2 ^ hsMu s)) → KT →L[ℂ] KT}
    (hOT : ∀ l x, IsUnitary (OT l x))
    (AT : PhaseAccess (Fin (timeN θ) × Fin (2 ^ hsMu s)) oneHotPattern OT hardCost)
    (pT : MultiOracleCircuit.Program OT) (φT : KT) (hφT : ‖φT‖ ≤ 1)
    (eT : KT →L[ℂ] SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε)
    {OM : Query → (Fin (precN θ ε) → Fin (2 ^ hsMu s)) → KM →L[ℂ] KM}
    (hOM : ∀ l x, IsUnitary (OM l x))
    (AM : PhaseAccess (Fin (precN θ ε) × Fin (2 ^ hsMu s)) oneHotPattern OM hardCost)
    (pM : MultiOracleCircuit.Program OM) (φM : KM) (hφM : ‖φM‖ ≤ 1)
    (eM : KM →L[ℂ] SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) GM)
    (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε)
    {OP : Query → (Fin (precN θ ε) → Bool) → KP →L[ℂ] KP} (hOP : ∀ l x, IsUnitary (OP l x))
    (AP : PhaseAccess (Fin (precN θ ε)) bitPattern OP hardCost)
    (pP : MultiOracleCircuit.Program OP) (φP : KP)
    (eP : KP →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) := by
  rw [two_shape_eq hθ h.tau_pos]
  exact main_max_of_access h hOT AT pT φT hφT _ (regroup_comp_isometry m eT heT)
    (fun j => accurate_search_of_two _ _ hm hc hθ eT _ j (haccT j))
    hOM AM pM φM hφM _ (regroup_comp_isometry m eM heM)
    (fun j => accurate_search_of_two _ _ hm hc hθ eM _ j (haccM j))
    hOP AP pP φP _ (fun x => accurate_scalar_of_two _ hm hc hθ eP _ x (haccP x))

/-! ### The three access models -/

variable {θ ε : ℝ} {s m : ℕ} {c t : ℝ}

/-- **Proposition `hsl:prop:two-norm`, spectator form** (eq. `twonorml:eq:lower`): for any three
programs over the native primitives of the enlarged time, mixed and precision families acting on
every copy of untouched spectator registers `ℂ^{Ω_T}`, `ℂ^{Ω_M}`, `ℂ^{Ω_P}`, run on
input-independent seeds and read into system ⊗ any garbage (through isometries for the time and
mixed families, through any map for the precision family), each
`ε`-accurate in trace distance (mixed outputs allowed) for `e^{-itH_X}(ψ_in ⊗ u_m)` on its own
family: `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(Q_T, Q_M, Q_P)`, with `s = s₀ m`,
`η = |c|√m`, `μ = |c|`, `c m t = θ`, `r_μ = L/log(e + L/θ)` and `c₀ = log 2/(4096π)`. -/
theorem two_norm_main_max (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ)
    (ΩT ΩM ΩP : Type) [Fintype ΩT] [Fintype ΩM] [Fintype ΩP] {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (specOracles ΩT (timeTwo θ s h.s_ge m hm c hc)))
    (φT : Joint ΩT (SearchTwoSpace (timeN θ) (hsMu s) s (timeC θ) θ m)) (hφT : ‖φT‖ ≤ 1)
    (eT : Joint ΩT (SearchTwoSpace (timeN θ) (hsMu s) s (timeC θ) θ m) →L[ℂ]
      SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε)
    (pM : MultiOracleCircuit.Program (specOracles ΩM (mixedTwo θ ε s h.s_ge m hm c hc)))
    (φM : Joint ΩM (SearchTwoSpace (precN θ ε) (hsMu s) s 1 θ m)) (hφM : ‖φM‖ ≤ 1)
    (eM : Joint ΩM (SearchTwoSpace (precN θ ε) (hsMu s) s 1 θ m) →L[ℂ]
      SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε)
    (pP : MultiOracleCircuit.Program (specOracles ΩP (precisionTwo θ ε s h.s_ge m hm c hc)))
    (φP : Joint ΩP (ScalarTwoSpace (precN θ ε) s θ m))
    (eP : Joint ΩP (ScalarTwoSpace (precN θ ε) s θ m) →L[ℂ]
      SysGarb (ScalarIndex (precN θ ε) s × Fin m) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) :=
  two_norm_max_of_access h hm hc hθ (specOracles_unitary ΩT _)
    ((timeTwoAccess h.s_ge hm hc).spectate ΩT) pT φT hφT eT heT haccT
    (specOracles_unitary ΩM _) ((mixedTwoAccess h.s_ge hm hc).spectate ΩM) pM φM hφM eM heM haccM
    (specOracles_unitary ΩP _) ((precisionTwoAccess h.s_ge hm hc).spectate ΩP) pP φP eP haccP

/-- **Proposition `hsl:prop:two-norm`, native form**: `two_norm_main_max` for programs over the
native primitives of the enlarged families without a spectator register. -/
theorem two_norm_main_max_native (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = θ) {GT GM GP : Type*}
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (pT : MultiOracleCircuit.Program (oracles (timeTwo θ s h.s_ge m hm c hc)))
    (φT : SearchTwoSpace (timeN θ) (hsMu s) s (timeC θ) θ m) (hφT : ‖φT‖ ≤ 1)
    (eT : SearchTwoSpace (timeN θ) (hsMu s) s (timeC θ) θ m →L[ℂ]
      SysGarb (SearchIndex (timeN θ) (hsMu s) s × Fin m) GT) (heT : eT† ∘L eT = 1)
    (haccT : ∀ j, Accurate eT (pT.eval j φT)
      (evolve ((timeTwo θ s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (timeN θ) (hsMu s) s))) ε)
    (pM : MultiOracleCircuit.Program (oracles (mixedTwo θ ε s h.s_ge m hm c hc)))
    (φM : SearchTwoSpace (precN θ ε) (hsMu s) s 1 θ m) (hφM : ‖φM‖ ≤ 1)
    (eM : SearchTwoSpace (precN θ ε) (hsMu s) s 1 θ m →L[ℂ]
      SysGarb (SearchIndex (precN θ ε) (hsMu s) s × Fin m) GM) (heM : eM† ∘L eM = 1)
    (haccM : ∀ j, Accurate eM (pM.eval j φM)
      (evolve ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j) t
        (embedU m (searchInput (precN θ ε) (hsMu s) s))) ε)
    (pP : MultiOracleCircuit.Program (oracles (precisionTwo θ ε s h.s_ge m hm c hc)))
    (φP : ScalarTwoSpace (precN θ ε) s θ m)
    (eP : ScalarTwoSpace (precN θ ε) s θ m →L[ℂ] SysGarb (ScalarIndex (precN θ ε) s × Fin m) GP)
    (haccP : ∀ x, Accurate eP (pP.eval x φP)
      (evolve ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x) t
        (embedU m (scalarInput (precN θ ε) s))) ε) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
      max (pT.labelCount .value : ℝ) (max (pM.labelCount .value : ℝ) (pP.labelCount .value)) :=
  two_norm_max_of_access h hm hc hθ (oracles_unitary _) (timeTwoAccess h.s_ge hm hc) pT φT hφT
    eT heT haccT (oracles_unitary _) (mixedTwoAccess h.s_ge hm hc) pM φM hφM eM heM haccM
    (oracles_unitary _) (precisionTwoAccess h.s_ge hm hc) pP φP eP haccP

/-- The enlarged input `ψ_in ⊗ u_m` is a unit vector. -/
theorem norm_embedU_searchInput (n μ s : ℕ) (hm : 0 < m) :
    ‖embedU m (searchInput n μ s)‖ = 1 := by
  rw [norm_embedU m hm, norm_searchInput]

/-- The enlarged scalar input is a unit vector. -/
theorem norm_embedU_scalarInput (n s : ℕ) (hm : 0 < m) :
    ‖embedU m (scalarInput n s)‖ = 1 := by
  rw [norm_embedU m hm, norm_scalarInput]

/-- **Proposition `hsl:prop:two-norm`, common form** (the query model of
`hs:thm:two-norm`): for any common-form simulations (`NativeSignedFactor.Simulates`) of the
enlarged time, mixed and precision families at time `t` within full-output error `ε`, with query
bounds `q_T`, `q_M`, `q_P`, `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(q_T, q_M, q_P)`. -/
theorem two_norm_main_max_simulates (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0)
    (hθ : c * m * t = θ) {qT qM qP : ℝ}
    (hT : NativeSignedFactor.Simulates
      (NativeSignedFactor.physOracle (timeTwo θ s h.s_ge m hm c hc))
      (fun j => SparseStateOverlap.matrixOperator ((timeTwo θ s h.s_ge m hm c hc).matrix j)) t ε qT)
    (hM : NativeSignedFactor.Simulates
      (NativeSignedFactor.physOracle (mixedTwo θ ε s h.s_ge m hm c hc))
      (fun j => SparseStateOverlap.matrixOperator ((mixedTwo θ ε s h.s_ge m hm c hc).matrix j))
      t ε qM)
    (hP : NativeSignedFactor.Simulates
      (NativeSignedFactor.physOracle (precisionTwo θ ε s h.s_ge m hm c hc))
      (fun x => SparseStateOverlap.matrixOperator ((precisionTwo θ ε s h.s_ge m hm c hc).matrix x))
      t ε qP) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤ max qT (max qM qP) := by
  obtain ⟨hIT, hIM, hIP⟩ := two_instances h hm hc
  obtain ⟨ιT, _, inpT, pT, hinpT, hcT, hsimT⟩ := hT
  obtain ⟨ιM, _, inpM, pM, hinpM, hcM, hsimM⟩ := hM
  obtain ⟨ιP, _, inpP, pP, hinpP, hcP, hsimP⟩ := hP
  obtain ⟨hψT, haccT⟩ := accurate_of_endpoint_program (common_unitary _ ιT) pT inpT hinpT
    (refZero, ⟨0, hm⟩) hIT.isHermitian (norm_embedU_searchInput _ _ _ hm) fun j => (hsimT j).2
  obtain ⟨hψM, haccM⟩ := accurate_of_endpoint_program (common_unitary _ ιM) pM inpM hinpM
    (refZero, ⟨0, hm⟩) hIM.isHermitian (norm_embedU_searchInput _ _ _ hm) fun j => (hsimM j).2
  obtain ⟨-, haccP⟩ := accurate_of_endpoint_program (common_unitary _ ιP) pP inpP hinpP
    (refZero, ⟨0, hm⟩) hIP.isHermitian (norm_embedU_scalarInput _ _ hm) fun x => (hsimP x).2
  have hQT : (pT.labelCount .value : ℝ) ≤ qT :=
    (by exact_mod_cast labelCount_le_count pT .value : (pT.labelCount .value : ℝ) ≤ pT.count).trans
      hcT
  have hQM : (pM.labelCount .value : ℝ) ≤ qM :=
    (by exact_mod_cast labelCount_le_count pM .value : (pM.labelCount .value : ℝ) ≤ pM.count).trans
      hcM
  have hQP : (pP.labelCount .value : ℝ) ≤ qP :=
    (by exact_mod_cast labelCount_le_count pP .value : (pP.labelCount .value : ℝ) ≤ pP.count).trans
      hcP
  refine (two_norm_max_of_access h hm hc hθ (common_unitary _ ιT)
    (commonAccess _ (timeTwoAccess h.s_ge hm hc) ιT) pT _ hψT _
    (endpointReadout_isometry inpT hinpT _) haccT (common_unitary _ ιM)
    (commonAccess _ (mixedTwoAccess h.s_ge hm hc) ιM) pM _ hψM _
    (endpointReadout_isometry inpM hinpM _) haccM (common_unitary _ ιP)
    (commonAccess _ (precisionTwoAccess h.s_ge hm hc) ιP) pP _ _ haccP).trans
    (max_le_max hQT (max_le_max hQM hQP))

/-! ### The matching upper bound on the aligned families -/

/-- **Data meeting `TwoNormInstance` satisfy the hypotheses of `hs:thm:two-norm`** with
`η = |c|√m`, `μ = |c|` and sparsity `s₀ m`: `μ ≤ η ≤ √(s₀ m) μ`, `η²|t|/μ = θ ≥ 1`, entries at
most `μ`, row and column norms at most `η`. So they are simulated in the common form with at most
`2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` queries, `s = s₀ m`, `r_μ = L/log(e + L/θ)`. -/
theorem two_on_aligned_of {X N : Type} [Fintype N] [DecidableEq N] {B : ℕ}
    (D : Data X N (Word B) (s * m)) (hD : TwoNormInstance D c m) (hθ1 : 1 ≤ θ) (hs : 1 ≤ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε
      (2 * 10 ^ 12 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε)) := by
  have hθa := theta_eq_abs hθ (by linarith)
  have hc0 : 0 < |c| := abs_pos.mpr hc
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsqm : 1 ≤ Real.sqrt m := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hm1
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have htheta : TwoNormSimulation.thetaT (|c| * Real.sqrt m) |c| t = θ := by
    rw [TwoNormSimulation.thetaT, hθa, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    field_simp
  have hμη : |c| ≤ |c| * Real.sqrt m := le_mul_of_one_le_right hc0.le hsqm
  have hss : 1 ≤ Real.sqrt s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hs1
  have hηs : |c| * Real.sqrt m ≤ Real.sqrt ((s * m : ℕ) : ℝ) * |c| := by
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg s)]
    have h1 : Real.sqrt m ≤ Real.sqrt s * Real.sqrt m :=
      le_mul_of_one_le_left (Real.sqrt_nonneg _) hss
    have h2 := mul_le_mul_of_nonneg_left h1 hc0.le
    linarith
  have hθ1' : 1 ≤ (|c| * Real.sqrt m) ^ 2 * |t| / |c| := by
    rw [← TwoNormSimulation.thetaT, htheta]
    exact hθ1
  have key := TwoNormSimulation.two_norm_simulation D (η := |c| * Real.sqrt m) (μ := |c|) (t := t)
    hμη hηs hθ1' hε hε1 hD.isHermitian hD.row_norm_le hD.col_norm_le hD.entry_le
  rw [TwoNormSimulation.bound, htheta] at key
  exact key

/-- **The aligned families meet the hypotheses of `hs:thm:two-norm`** (`two_on_aligned_of` in
the range `HSRange θ s₀ ε`): each is simulated in the common form with at most
`2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` queries. -/
theorem two_on_aligned {X N : Type} [Fintype N] [DecidableEq N] {B : ℕ}
    (D : Data X N (Word B) (s * m)) (hD : TwoNormInstance D c m) (h : HSRange θ s ε)
    (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε
      (2 * 10 ^ 12 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε)) :=
  two_on_aligned_of D hD h.one_le_tau (by have := h.s_ge; omega) h.eps_pos h.eps_le hm hc hθ

/-- **`Θ` on the aligned two-norm families** (after Theorem `hs:thm:two-norm`: "Its matching lower
bound is established on the aligned parameter families of Proposition `hsl:prop:two-norm`"): with
`S' = √s η|t| + √(sμ|t| r_μ) + r_μ`, `s = s₀ m`, `η = |c|√m`, `μ = |c|`, `c m t = θ`,

`c₀ S' ≤ max(simulationCost_T, simulationCost_M, simulationCost_P) ≤ 2·10¹² S'`

for the enlarged time, mixed and precision families in the common query model of
`hs:thm:two-norm`. -/
theorem two_norm_theta (h : HSRange θ s ε) (hm : 0 < m) (hc : c ≠ 0) (hθ : c * m * t = θ) :
    c0 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
        Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) ≤
        max (simulationCost (timeTwo θ s h.s_ge m hm c hc) t ε)
          (max (simulationCost (mixedTwo θ ε s h.s_ge m hm c hc) t ε)
            (simulationCost (precisionTwo θ ε s h.s_ge m hm c hc) t ε)) ∧
      max (simulationCost (timeTwo θ s h.s_ge m hm c hc) t ε)
          (max (simulationCost (mixedTwo θ ε s h.s_ge m hm c hc) t ε)
            (simulationCost (precisionTwo θ ε s h.s_ge m hm c hc) t ε)) ≤
        2 * 10 ^ 12 * (Real.sqrt ((s * m : ℕ) : ℝ) * (|c| * Real.sqrt m) * |t| +
          Real.sqrt ((s * m : ℕ) * |c| * |t| * hsR θ ε) + hsR θ ε) := by
  obtain ⟨hIT, hIM, hIP⟩ := two_instances h hm hc
  have hT := two_on_aligned _ hIT h hm hc hθ
  have hM := two_on_aligned _ hIM h hm hc hθ
  have hP := two_on_aligned _ hIP h hm hc hθ
  refine ⟨?_, max_le (simulationCost_le _ hT)
    (max_le (simulationCost_le _ hM) (simulationCost_le _ hP))⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨qT, hqT', hqT⟩ := exists_simulates_lt _ hT ((le_max_left _ _).trans_lt hlt)
  obtain ⟨qM, hqM', hqM⟩ := exists_simulates_lt _ hM
    (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hlt)
  obtain ⟨qP, hqP', hqP⟩ := exists_simulates_lt _ hP
    (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hlt)
  have hmax := two_norm_main_max_simulates h hm hc hθ hqT hqM hqP
  have := max_lt hqT' (max_lt hqM' hqP')
  linarith

/-- **Exact dyadic entries**: if the coefficient is the dyadic `c = M/2^p`, every entry of a
`TwoNormInstance` is the dyadic `(M v)/2^{B+p}`. -/
theorem TwoNormInstance.dyadic_entries {X N : Type*} [Fintype N] [DecidableEq N] {B s' : ℕ}
    {D : Data X N (Word B) s'} {c : ℝ} {m : ℕ} (hD : TwoNormInstance D c m) {M : ℤ} {p : ℕ}
    (hcM : c = M / 2 ^ p) (x : X) (i j : N) :
    ∃ v : ℤ, D.matrix x i j = ((M * v : ℤ) : ℂ) / 2 ^ (B + p) := by
  obtain ⟨v, -, -, hv⟩ := hD.dyadic x i j
  refine ⟨v, ?_⟩
  rw [hv, hcM]
  push_cast
  rw [pow_add]
  field_simp

end

end OptimalLowerBounds
