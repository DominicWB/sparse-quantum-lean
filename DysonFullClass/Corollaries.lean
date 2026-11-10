import DysonFullClass.Single
import DysonFullClass.Approx
import ODELowerBoundExtensions.Dyson.Fixed

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The fixed-parameter comparison on the full time-dependent class

Manuscript, eq. `odel:eq:fixed` and the consequence after Lemma `odel:lem:dyson`: at fixed
`z = s η T` and `ḡ`, `Q_A = O(log(1/ε)/log log(1/ε))`, so "a uniform worst-case lower bound
proportional to `ḡ √s τ log(ḡ/ε)` is false under these access assumptions". Both statements are
proved here for the single heralded program of `Single.full_single`, on the full class
`Theorem.FullValid` (represented samples of either sign, arbitrary source nodes and complex
weights, hidden source norms, the integrated certificate on the clipped represented samples), with
`c_q ≥ 1` the absolute quadrature-mass constant of the model:

* `full_fixed`: for fixed `z > 0`, `ḡ ≥ 1`, `c_q ≥ 1` there are `C₀` and `0 < ε₀ < 1` (depending
  only on `z`, `ḡ`, `c_q`) with `log log (1/ε) > 0` on `(0, ε₀]`, such that for every
  `ε ∈ (0, ε₀]` and every public specification with `s η T = z` (any dimension, sparsity, access
  width, mesh, cell-to-sample map, source rule and supplied source interfaces) one heralded
  program solves every valid hidden instance with at most `C₀ log(1/ε)/log log(1/ε)` matrix
  queries (and at most `40 c_q ḡ e^z` calls of each source interface);
* `full_no_uniform`: for fixed `s`, `τ > 0`, `ḡ ≥ 1`, `c_q ≥ 1` and every `c > 0` there is
  `ε_c > 0` such that for every `ε ∈ (0, ε_c]` and every public specification with `η T = τ`, one
  heralded program solves every valid hidden instance with **fewer than**
  `c ḡ √s τ log(ḡ/ε)` matrix queries;
* `approx_fixed`, `approx_no_uniform`: the same two statements for the four-attempt protocol of
  `Approx.full_approx` (supplied preparations on temporary work registers, accurate on clean
  inputs), for its worst-case matrix queries over all histories, on every valid instance.

Neither statement improves on the joint lower bounds when `s τ` grows, and neither is a gate
bound.
-/

namespace DysonFullClass

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions
open ODELowerBoundExtensions.Dyson
open DysonSingleProgram DysonSingleProgram.Register DysonGeneralAccess DysonGeneralAccess.Model
open SparseHamiltonian.CleanWorkODE (LabelW LoadW CleanErr cleanPi ctrlL)
open SparseHamiltonian.GeneralSourceExtensions (ApproxCertificate)
open scoped InnerProduct BigOperators

/-- **Eq. `odel:eq:fixed` on the full time-dependent class.** For fixed `z > 0`, `ḡ ≥ 1` and the
model constant `c_q ≥ 1` there are `C₀` and `0 < ε₀ < 1`, uniform over dimensions, sparsities,
access widths, meshes, cell-to-sample maps, source rules, supplied source interfaces and hidden
instances, with `log log (1/ε) > 0` on `(0, ε₀]`, such that for every `ε ∈ (0, ε₀]` and every
public specification with `s η T = z`, one heralded program over the full-class access solves
every valid instance (`FullValid`) with at most `C₀ log(1/ε)/log log(1/ε)` matrix queries and at
most `40 c_q ḡ e^z` calls of each source interface. -/
theorem full_fixed (z g cq : ℝ) (hz : 0 < z) (hg : 1 ≤ g) (hcq : 1 ≤ cq) :
    ∃ C₀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      (∀ ε, 0 < ε → ε ≤ ε₀ → 0 < Real.log (Real.log (1 / ε))) ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
        {s Ks M m : ℕ} (D₀ : Data (X × Fin Ks) n Z s) (_ : 0 < M) (σ : Fin M → Fin Ks)
        (t : ℕ → ℝ) (T η : ℝ) (_ : IsMesh t M T) (_ : 0 < T) (hη : 0 < η)
        (v : Fin m → ℝ) (_ : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
        (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (_ : ∀ x, IsUnitary (Pw x))
        (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (_ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (_ : ‖seed‖ = 1),
        zParam s η T = z →
        ∃ (Jt : Type) (_ : Fintype Jt) (G : Type) (_ : NormedAddCommGroup G)
          (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
          (A : HeraldedSolver
            (fiberOracle Jt (fullOracle D₀ (fullDegree s η T g cq ε) M m Pw J ω))
            (FullValid D₀ σ t T η g cq ε hη v ω Pw J seed) G ε),
          (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
            C₀ * (Real.log (1 / ε) / Real.log (Real.log (1 / ε))) ∧
          ∀ b : Bool, (A.prog.cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
            40 * (cq * g * Real.exp z) := by
  have hcqg : 1 ≤ cq * g := by nlinarith
  obtain ⟨C, ε₁, h0, h1, hC⟩ := dyson_fixed z (cq * g) hz hcqg
  have he2 : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  refine ⟨C, min ε₁ (Real.exp (-2)), lt_min h0 (Real.exp_pos _), (min_le_left _ _).trans_lt h1,
    ?_, ?_⟩
  · intro ε hε hεle
    have h2 : (2 : ℝ) ≤ Real.log (1 / ε) := le_log_one_div 2 ε hε (hεle.trans (min_le_right _ _))
    exact Real.log_pos (by linarith)
  · intro ε hε hεle X n Z _ _ _ _ _ s Ks M m D₀ hM σ t T η hmesh hT hη v hv ω Pw hPw J hJ seed
      hSeed hz'
    have hε1 : ε ≤ 1 := hεle.trans ((min_le_left _ _).trans h1.le)
    obtain ⟨Jt, hJt, G, i1, i2, i3, A, hA, hS⟩ :=
      full_single D₀ hM σ t T η g cq ε hmesh hT hη hg hcq hε hε1 v hv ω Pw hPw J hJ seed hSeed
    rw [hz'] at hA
    refine ⟨Jt, hJt, G, i1, i2, i3, A, hA.trans (hC ε hε (hεle.trans (min_le_left _ _))), ?_⟩
    intro b
    have h := hS b
    unfold fullAmp at h
    rw [hz'] at h
    exact h

/-- `log (c_q ḡ/ε) ≤ 2 log (ḡ/ε)` once `ε ≤ 1/c_q`. -/
theorem log_cq_le {g cq ε : ℝ} (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hεq : ε ≤ 1 / cq) :
    Real.log (cq * g / ε) ≤ 2 * Real.log (g / ε) := by
  have hg0 : 0 < g := by linarith
  have hcq0 : 0 < cq := by linarith
  have hge : cq ≤ g / ε := by
    rw [le_div_iff₀ hε]
    have h1 : cq * ε ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hεq hcq0.le
      rwa [mul_one_div_cancel hcq0.ne'] at this
    linarith
  rw [mul_div_assoc, Real.log_mul hcq0.ne' (div_pos hg0 hε).ne']
  have := Real.log_le_log hcq0 hge
  linarith

/-- **No uniform lower bound proportional to `ḡ √s τ log(ḡ/ε)` on the full class** (the
consequence of eq. `odel:eq:fixed`): for fixed sparsity `s`, `τ > 0`, `ḡ ≥ 1`, the model constant
`c_q ≥ 1` and every `c > 0` there is `ε_c > 0`, independent of dimensions, access widths, meshes,
source rules, supplied source interfaces and hidden instances, such that for every
`ε ∈ (0, ε_c]` and every public specification with `η T = τ`, one heralded program over the
full-class access solves every valid instance (`FullValid`) with fewer than
`c ḡ √s τ log(ḡ/ε)` matrix queries. -/
theorem full_no_uniform (s : ℕ) (τ g cq c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ g) (hcq : 1 ≤ cq)
    (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
        {Ks M m : ℕ} (D₀ : Data (X × Fin Ks) n Z s) (_ : 0 < M) (σ : Fin M → Fin Ks)
        (t : ℕ → ℝ) (T η : ℝ) (_ : IsMesh t M T) (_ : 0 < T) (hη : 0 < η)
        (v : Fin m → ℝ) (_ : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
        (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (_ : ∀ x, IsUnitary (Pw x))
        (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (_ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (_ : ‖seed‖ = 1),
        η * T = τ →
        ∃ (Jt : Type) (_ : Fintype Jt) (G : Type) (_ : NormedAddCommGroup G)
          (_ : InnerProductSpace ℂ G) (_ : CompleteSpace G)
          (A : HeraldedSolver
            (fiberOracle Jt (fullOracle D₀ (fullDegree s η T g cq ε) M m Pw J ω))
            (FullValid D₀ σ t T η g cq ε hη v ω Pw J seed) G ε),
          (A.prog.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) <
            c * g * Real.sqrt s * τ * Real.log (g / ε) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro ε _ _ X n Z _ _ _ _ _ Ks M m D₀
    exact absurd D₀.slots_pos (lt_irrefl 0)
  · have hcqg : 1 ≤ cq * g := by nlinarith
    have hcq0 : 0 < cq := by linarith
    have hc' : 0 < c / (2 * cq) := by positivity
    obtain ⟨ε₁, hε₁, h₁⟩ := eventually_lt (s : ℝ) τ (cq * g) (c / (2 * cq))
      (Nat.cast_pos.mpr hs) hτ hcqg hc'
    refine ⟨min (min ε₁ 1) (1 / cq), lt_min (lt_min hε₁ one_pos) (by positivity), ?_⟩
    intro ε hε hεle X n Z _ _ _ _ _ Ks M m D₀ hM σ t T η hmesh hT hη v hv ω Pw hPw J hJ seed
      hSeed hτT
    have hε1 : ε ≤ 1 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hεq : ε ≤ 1 / cq := hεle.trans (min_le_right _ _)
    have hz : zParam s η T = (s : ℝ) * τ := by unfold zParam; rw [← hτT]; ring
    obtain ⟨Jt, hJt, G, i1, i2, i3, A, hA, -⟩ :=
      full_single D₀ hM σ t T η g cq ε hmesh hT hη hg hcq hε hε1 v hv ω Pw hPw J hJ seed hSeed
    rw [hz] at hA
    have hlt := h₁ ε hε (hεle.trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hlog := log_cq_le hg hcq hε hεq
    have hk : 0 ≤ c * g * Real.sqrt s * τ := by
      have : 0 < g := by linarith
      positivity
    refine ⟨Jt, hJt, G, i1, i2, i3, A, lt_of_le_of_lt hA (lt_of_lt_of_le hlt ?_)⟩
    calc c / (2 * cq) * (cq * g) * Real.sqrt s * τ * Real.log (cq * g / ε)
        = c * g * Real.sqrt s * τ * (Real.log (cq * g / ε) / 2) := by
          field_simp
      _ ≤ c * g * Real.sqrt s * τ * Real.log (g / ε) :=
          mul_le_mul_of_nonneg_left (by linarith) hk

/-- **Eq. `odel:eq:fixed` on the full class with approximate preparations**: for fixed `z > 0`,
`ḡ ≥ 1`, `c_q ≥ 1` there are `C₀` and `0 < ε₀ < 1`, uniform as in `full_fixed`, such that for
every `ε ∈ (0, ε₀]` and every public specification with `s η T = z` and supplied preparations on a
temporary work register, the public four-attempt protocol of `full_approx` satisfies
`ApproxCertificate` on every valid instance within the clean-input budget and makes at most
`C₀ log(1/ε)/log log(1/ε)` matrix queries in every history. -/
theorem approx_fixed (z g cq : ℝ) (hz : 0 < z) (hg : 1 ≤ g) (hcq : 1 ≤ cq) :
    ∃ C₀ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      (∀ ε, 0 < ε → ε ≤ ε₀ → 0 < Real.log (Real.log (1 / ε))) ∧
      ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X n Z W : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
        [Fintype W] [DecidableEq W]
        {s Ks M m : ℕ} (D₀ : Data (X × Fin Ks) n Z s) (_ : 0 < M) (σ : Fin M → Fin Ks)
        (t : ℕ → ℝ) (T η : ℝ) (_ : IsMesh t M T) (_ : 0 < T) (hη : 0 < η)
        (v : Fin m → ℝ) (_ : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ) (w₀ : W)
        (Pw : X → LabelW m W →L[ℂ] LabelW m W) (_ : ∀ x, IsUnitary (Pw x))
        (J : X → LoadW m n W →L[ℂ] LoadW m n W) (_ : ∀ x, IsUnitary (J x))
        (seed : EuclideanSpace ℂ n) (_ : ‖seed‖ = 1),
        zParam s η T = z →
        ∃ tf : ODERepeatProtocol.TrialFamily
            (fullActualOracleW D₀ (fullDegree s η T g cq ε) M m Pw J) (EuclideanSpace ℂ n),
          ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
            (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
            (y : EuclideanSpace ℂ n),
            IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
            CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
            CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
            30 * fullAmp s η T g cq * δ ≤ 1 / 400 → 30 * fullAmp s η T g cq * δ ≤ ε / 20 →
            FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x y →
            ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x y (s : ℝ) 0
              (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε ∧
            (((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.matrixCalls : ℕ) : ℝ) ≤
              C₀ * (Real.log (1 / ε) / Real.log (Real.log (1 / ε))) := by
  have hcqg : 1 ≤ cq * g := by nlinarith
  obtain ⟨C, ε₁, h0, h1, hC⟩ := dyson_fixed z (cq * g) hz hcqg
  refine ⟨C, min ε₁ (Real.exp (-2)), lt_min h0 (Real.exp_pos _), (min_le_left _ _).trans_lt h1,
    ?_, ?_⟩
  · intro ε hε hεle
    have h2 : (2 : ℝ) ≤ Real.log (1 / ε) := le_log_one_div 2 ε hε (hεle.trans (min_le_right _ _))
    exact Real.log_pos (by linarith)
  · intro ε hε hεle X n Z W _ _ _ _ _ _ _ s Ks M m D₀ hM σ t T η hmesh hT hη v hv ω w₀ Pw hPw J
      hJ seed hSeed hz'
    have hε1 : ε ≤ 1 := hεle.trans ((min_le_left _ _).trans h1.le)
    have hs : 0 < s := D₀.slots_pos
    obtain ⟨tf, -, -, htf⟩ := full_approx D₀ hM σ t T η g cq ε hmesh hT hη hg hcq hε hε1 v hv ω w₀
      Pw hPw J hJ seed hSeed
    refine ⟨tf, fun x P L δ y hP hL hδ hPc hJc hδ1 hδε hval => ?_⟩
    have hA := htf x P L δ y hP hL hδ hPc hJc hδ1 hδε hval
    refine ⟨hA, ?_⟩
    have hb := full_bound hs hT hη hg hcq hε hε1
    rw [hz'] at hb
    exact (hA.matrix_queries.trans hb).trans (hC ε hε (hεle.trans (min_le_left _ _)))

/-- **No uniform lower bound on the full class with approximate preparations**: for fixed `s`,
`τ > 0`, `ḡ ≥ 1`, `c_q ≥ 1` and every `c > 0` there is `ε_c > 0`, uniform as in
`full_no_uniform`, such that for every `ε ∈ (0, ε_c]` and every public specification with
`η T = τ` and supplied preparations on a temporary work register, the public four-attempt
protocol of `full_approx` satisfies `ApproxCertificate` on every valid instance within the
clean-input budget and makes fewer than `c ḡ √s τ log(ḡ/ε)` matrix queries in every history. -/
theorem approx_no_uniform (s : ℕ) (τ g cq c : ℝ) (hτ : 0 < τ) (hg : 1 ≤ g) (hcq : 1 ≤ cq)
    (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X n Z W : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
        [Fintype W] [DecidableEq W]
        {Ks M m : ℕ} (D₀ : Data (X × Fin Ks) n Z s) (_ : 0 < M) (σ : Fin M → Fin Ks)
        (t : ℕ → ℝ) (T η : ℝ) (_ : IsMesh t M T) (_ : 0 < T) (hη : 0 < η)
        (v : Fin m → ℝ) (_ : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ) (w₀ : W)
        (Pw : X → LabelW m W →L[ℂ] LabelW m W) (_ : ∀ x, IsUnitary (Pw x))
        (J : X → LoadW m n W →L[ℂ] LoadW m n W) (_ : ∀ x, IsUnitary (J x))
        (seed : EuclideanSpace ℂ n) (_ : ‖seed‖ = 1),
        η * T = τ →
        ∃ tf : ODERepeatProtocol.TrialFamily
            (fullActualOracleW D₀ (fullDegree s η T g cq ε) M m Pw J) (EuclideanSpace ℂ n),
          ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
            (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
            (y : EuclideanSpace ℂ n),
            IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
            CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
            CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
            30 * fullAmp s η T g cq * δ ≤ 1 / 400 → 30 * fullAmp s η T g cq * δ ≤ ε / 20 →
            FullValidAt D₀ σ t T η g cq ε hη v ω P L seed x y →
            ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x y (s : ℝ) 0
              (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε ∧
            (((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.matrixCalls : ℕ) : ℝ) <
              c * g * Real.sqrt s * τ * Real.log (g / ε) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro ε _ _ X n Z W _ _ _ _ _ _ _ Ks M m D₀
    exact absurd D₀.slots_pos (lt_irrefl 0)
  · have hcqg : 1 ≤ cq * g := by nlinarith
    have hcq0 : 0 < cq := by linarith
    have hc' : 0 < c / (2 * cq) := by positivity
    obtain ⟨ε₁, hε₁, h₁⟩ := eventually_lt (s : ℝ) τ (cq * g) (c / (2 * cq))
      (Nat.cast_pos.mpr hs) hτ hcqg hc'
    refine ⟨min (min ε₁ 1) (1 / cq), lt_min (lt_min hε₁ one_pos) (by positivity), ?_⟩
    intro ε hε hεle X n Z W _ _ _ _ _ _ _ Ks M m D₀ hM σ t T η hmesh hT hη v hv ω w₀ Pw hPw J hJ
      seed hSeed hτT
    have hε1 : ε ≤ 1 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
    have hεq : ε ≤ 1 / cq := hεle.trans (min_le_right _ _)
    have hz : zParam s η T = (s : ℝ) * τ := by unfold zParam; rw [← hτT]; ring
    obtain ⟨tf, -, -, htf⟩ := full_approx D₀ hM σ t T η g cq ε hmesh hT hη hg hcq hε hε1 v hv ω w₀
      Pw hPw J hJ seed hSeed
    refine ⟨tf, fun x P L δ y hP hL hδ hPc hJc hδ1 hδε hval => ?_⟩
    have hA := htf x P L δ y hP hL hδ hPc hJc hδ1 hδε hval
    refine ⟨hA, ?_⟩
    have hb := full_bound hs hT hη hg hcq hε hε1
    rw [hz] at hb
    have hlt := h₁ ε hε (hεle.trans ((min_le_left _ _).trans (min_le_left _ _)))
    have hlog := log_cq_le hg hcq hε hεq
    have hk : 0 ≤ c * g * Real.sqrt s * τ := by
      have : 0 < g := by linarith
      positivity
    refine lt_of_le_of_lt (hA.matrix_queries.trans hb) (lt_of_lt_of_le hlt ?_)
    calc c / (2 * cq) * (cq * g) * Real.sqrt s * τ * Real.log (cq * g / ε)
        = c * g * Real.sqrt s * τ * (Real.log (cq * g / ε) / 2) := by
          field_simp
      _ ≤ c * g * Real.sqrt s * τ * Real.log (g / ε) :=
          mul_le_mul_of_nonneg_left (by linarith) hk

end

end DysonFullClass
