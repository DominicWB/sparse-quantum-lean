import LargeSparsityCore.NativeCore
import LargeSparsityCore.NativeTwoNorm

set_option autoImplicit false

/-!
# The large-sparsity core at a separate entry scale

The clipped-transducer regime of Theorem `hs:thm:two-norm` (Appendix B, paragraph "Large `h` with
`τ_ent ≥ Lh`"): for sparse data with Hermitian `H(x)`, rows and columns of Euclidean norm at most
`η` and entries of modulus at most `μ`, the joint representation clipped at `μ` (`NativeTwoNorm`)
satisfies the hypotheses of the abstract core (`Core.CoreData`) with the real moment parameter
`σ = sμ²/η²` in place of the sparsity (`coreData_two`): "The finite-clock resolvent [eq.
`opt:eq:global-resolvent`] and spectral enclosures therefore have exactly the hypotheses used in
Appendix `opt:sec:core`, with `s` replaced analytically by `σ` and `τ` by `θ`". The native
compilation of `NativeCore` is unchanged.

* `core_native_two`: in the regime `Parameters.Regime σ θ ε`, at most `324 d` native calls for
  `e^{-i (θμ/η²) H}`.
* `core_simulation_two`: with `θ = η²|t|/μ`, at most `6972480 √(σθr_μ)` native calls for `e^{-itH}`,
  for every sign of `t`; `σθ = sμ|t|`.

With `μ = η` (`σ = s`) these are `core_native` and `core_simulation`.
-/

namespace LargeSparsityCore.Native

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048

open ContinuousLinearMap SparseHamiltonian NativeSignedFactor OrientedNativeLayout
open NativeSparseBlockEncoding OracleCircuit CayleyBlocks SparseEdgeMoments Parameters
open LabeledEncodedOracle ReuseLayerFactorization
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

omit [Fintype n] [DecidableEq n] in
/-- `ρ/s = 1/σ` for `ρ = η²/μ²` and `sμ² = ση²`. -/
theorem ratio_div {σ μ η : ℝ} (hs : 0 < s) (hμ : 0 < μ)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (c : ℝ) : c * (η ^ 2 / μ ^ 2) / s = c / σ := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    have : (s : ℝ) * μ ^ 2 = 0 := by rw [hσ]; ring
    have : (0 : ℝ) < s * μ ^ 2 := by positivity
    linarith
  field_simp
  linear_combination (-c) * hσ

/-- **The joint representation at entry scale `μ` satisfies the hypotheses of the abstract core**
with the moment parameter `σ` (`sμ² = ση²`) and `β = h`. -/
theorem coreData_two (D : Data X n Z s) {σ θ ε μ η : ℝ} (R : Regime σ θ ε) (hμ : 0 < μ)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) {x : X} (hP : Promise D η x) :
    Core.CoreData σ θ ε (Kop D μ (hval θ ε) (qval σ θ ε) x) (Dop D μ (hval θ ε) (qval σ θ ε) x)
      (Ppl D μ (hval θ ε) x) (Pmi D μ (hval θ ε) x) (Jin D) := by
  have hh := R.h_pos
  have hq := R.q_pos
  have hσ0 : 0 < σ := by linarith [R.one_le_s]
  have hK : ∀ v, ‖(Kop D μ (hval θ ε) (qval σ θ ε) x ∘L Jin D) v‖ ^ 2 ≤
      (Real.sqrt (2 * qval σ θ ε ^ 2 * (1 + hval θ ε) / σ)) ^ 2 * ‖v‖ ^ 2 := by
    intro v
    rw [Real.sq_sqrt (by positivity), comp_apply,
      ← ratio_div D.slots_pos hμ hσ (2 * qval σ θ ε ^ 2 * (1 + hval θ ε))]
    exact norm_K_input_sq_le_ratio D (qval σ θ ε) hμ hh.le hP v
  have hKn := opNorm_le_of_sq (Real.sqrt_nonneg _) hK
  refine ⟨spectral D μ (hval θ ε) (qval σ θ ε) x, Dop_isometry D μ _ _ x, Jin_isometry D, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine (norm_R1_bulk_le D hμ hh hq.le x).trans ?_
    have hQ := R.Q0_ge
    unfold Q0 at hQ ⊢
    linarith
  · apply opNorm_le_of_sq (sw_nonneg σ θ ε)
    intro v
    rw [R.sw_sq, comp_apply]
    have h := norm_Ppl_input_sq_le_ratio D hμ hh.le (x := x) hP v
    rw [show hval θ ε * (η ^ 2 / μ ^ 2) / (2 * s) = hval θ ε / 2 * (η ^ 2 / μ ^ 2) / s by ring,
      ratio_div D.slots_pos hμ hσ] at h
    refine h.trans (le_of_eq ?_)
    ring
  · apply opNorm_le_of_sq (sw_nonneg σ θ ε)
    intro v
    rw [R.sw_sq, comp_apply]
    have h := norm_Pmi_input_sq_le_ratio D hμ hh.le (x := x) hP v
    rw [show hval θ ε * (η ^ 2 / μ ^ 2) / (2 * s) = hval θ ε / 2 * (η ^ 2 / μ ^ 2) / s by ring,
      ratio_div D.slots_pos hμ hσ] at h
    refine h.trans (le_of_eq ?_)
    ring
  · apply opNorm_le_of_sq (sm_nonneg σ θ ε)
    intro v
    rw [sm, Real.sq_sqrt (by positivity), comp_apply, comp_apply, ← comp_apply,
      ← ratio_div D.slots_pos hμ hσ]
    exact norm_bulk_input_sq_le_ratio D (qval σ θ ε) hμ hh.le hP v
  · calc ‖Kop D μ (hval θ ε) (qval σ θ ε) x ∘L Jin D‖ ^ 2 ≤
          (Real.sqrt (2 * qval σ θ ε ^ 2 * (1 + hval θ ε) / σ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hKn 2
      _ = 2 * qval σ θ ε ^ 2 * (1 + hval θ ε) / σ := Real.sq_sqrt (by positivity)
  · have hJ : ‖(Jin D)†‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact Core.norm_le_one_of_isometry (Jin_isometry D)
    have h1 : Real.sqrt (2 * qval σ θ ε ^ 2 * (1 + hval θ ε) / σ) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact R.second_le_one
    calc ‖(Jin D)† ∘L Kop D μ (hval θ ε) (qval σ θ ε) x ∘L Jin D‖ ≤
          ‖(Jin D)†‖ * ‖Kop D μ (hval θ ε) (qval σ θ ε) x ∘L Jin D‖ := opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hJ (hKn.trans h1) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The known input of the core with moment parameter `σ`: the coherent smoothing preparation
followed by the fixed clean encoding (`input D τ ε` is `inputS D (↑s) τ ε`). -/
def inputS (D : Data X n Z s) (σ θ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] NativeCayleyActive.Physical n Z (steps σ θ ε) (degree σ θ ε) :=
  (embedding D (steps σ θ ε) (degree σ θ ε)).toContinuousLinearMap ∘L
    Core.input (EuclideanSpace ℂ n) (Space n Z) σ θ ε

theorem inputS_isometry (D : Data X n Z s) {σ θ ε : ℝ} (R : Regime σ θ ε) :
    (inputS D σ θ ε)† ∘L inputS D σ θ ε = 1 := by
  apply (norm_map_iff_adjoint_comp_self (inputS D σ θ ε)).mp
  intro v
  rw [inputS, comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact (norm_map_iff_adjoint_comp_self _).mpr (Core.input_isometry R) v

set_option maxHeartbeats 1000000 in
/-- **The large-sparsity core at entry scale `μ`** (proof of Theorem `hs:thm:two-norm`, clipped
transducer). -/
theorem core_native_two (D : Data X n Z s) {σ θ ε μ η : ℝ} (R : Regime σ θ ε) (hμ : 0 < μ)
    (hη : 0 < η) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hP : ∀ x, Promise D η x) (hent : ∀ x i j, ‖D.matrix x i j‖ ≤ μ) :
    (inputS D σ θ ε)† ∘L inputS D σ θ ε = 1 ∧
    ∃ p : MultiOracleCircuit.Program (NativeCayleyActive.oracle D (steps σ θ ε) (degree σ θ ε)),
      p.count ≤ 324 * degree σ θ ε ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L inputS D σ θ ε - inputS D σ θ ε ∘L NormedSpace.exp
          ((-Complex.I * ((θ * μ / η ^ 2 : ℝ) : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨p, hcount, hp⟩ := Core.core_query R
    (fun x => Kop D μ (hval θ ε) (qval σ θ ε) x) (fun x => Dop D μ (hval θ ε) (qval σ θ ε) x)
    (fun x => Ppl D μ (hval θ ε) x) (fun x => Pmi D μ (hval θ ε) x) (Jin D) (Jin_isometry D)
    (fun x => coreData_two D R hμ hσ (hP x)) (NativeCayleyActive.oracle D (steps σ θ ε)
      (degree σ θ ε)) (NativeCayleyActive.oracle_unitary D _ _)
    (embedding D (steps σ θ ε) (degree σ θ ε)).toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self _) 54
    (fun r _ => active_implementsOn D μ (hval θ ε) (qval σ θ ε) _ _ r)
  refine ⟨inputS_isometry D R, p, by omega, fun x => ⟨(hp x).1, ?_⟩⟩
  have h := (hp x).2
  rw [compression_of_entry D (qval σ θ ε) hμ R.h_pos (hH x) (hent x), smul_smul] at h
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hq := R.q_pos.ne'
  have e : -Complex.I * (aval σ θ ε : ℂ) * ((qval σ θ ε / (s * μ) : ℝ) : ℂ) =
      -Complex.I * ((θ * μ / η ^ 2 : ℝ) : ℂ) := by
    rw [mul_assoc, ← Complex.ofReal_mul]
    congr 2
    unfold aval
    have hsμ : (s : ℝ) * μ ≠ 0 := by positivity
    have hη2 : η ^ 2 ≠ 0 := by positivity
    rw [show σ * θ / qval σ θ ε * (qval σ θ ε / (s * μ)) = σ * θ / (s * μ) by field_simp,
      div_eq_div_iff hsμ hη2]
    linear_combination (-θ) * hσ
  rw [e] at h
  exact h

/-- **The clipped-transducer regime for every time.** With `θ = η²|t|/μ` in the regime
`Parameters.Regime σ θ ε` and `sμ² = ση²`, at most `6972480 √(σθr)` native calls give full-output
error at most `ε` for `e^{-itH}`; negative time uses the inverse circuit. -/
theorem core_simulation_two (D : Data X n Z s) {σ μ η t ε : ℝ} (hμ : 0 < μ) (hη : 0 < η)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (R : Regime σ (η ^ 2 * |t| / μ) ε)
    (hH : ∀ x, (D.matrix x).IsHermitian) (hP : ∀ x, Promise D η x)
    (hent : ∀ x i j, ‖D.matrix x i j‖ ≤ μ) :
    (inputS D σ (η ^ 2 * |t| / μ) ε)† ∘L inputS D σ (η ^ 2 * |t| / μ) ε = 1 ∧
    ∃ p : MultiOracleCircuit.Program (NativeCayleyActive.oracle D (steps σ (η ^ 2 * |t| / μ) ε)
        (degree σ (η ^ 2 * |t| / μ) ε)),
      (p.count : ℝ) ≤ 6972480 * Real.sqrt (σ * (η ^ 2 * |t| / μ) * rval (η ^ 2 * |t| / μ) ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L inputS D σ (η ^ 2 * |t| / μ) ε - inputS D σ (η ^ 2 * |t| / μ) ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨hin, p, hcount, hp⟩ := core_native_two D R hμ hη hσ hH hP hent
  refine ⟨hin, ?_⟩
  have hO := NativeCayleyActive.oracle_unitary D (steps σ (η ^ 2 * |t| / μ) ε)
    (degree σ (η ^ 2 * |t| / μ) ε)
  have htime : η ^ 2 * |t| / μ * μ / η ^ 2 = |t| := by field_simp
  have hcount' : (p.count : ℝ) ≤
      6972480 * Real.sqrt (σ * (η ^ 2 * |t| / μ) * rval (η ^ 2 * |t| / μ) ε) := by
    have h1 : (p.count : ℝ) ≤ 324 * (degree σ (η ^ 2 * |t| / μ) ε : ℝ) := by exact_mod_cast hcount
    have h2 := R.degree_le_sqrt
    nlinarith
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨p, hcount', fun x => ⟨(hp x).1, ?_⟩⟩
    have h := (hp x).2
    have e : ((|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_nonneg ht]
    rw [htime, e] at h
    exact h
  · refine ⟨p.adjoint, by rw [MultiOracleCircuit.Program.count_adjoint]; exact hcount',
      fun x => ⟨(p.adjoint).eval_unitary hO x, ?_⟩⟩
    have h := LabeledAdjointSimulation.program_negative_time_error p hO
      (inputS D σ (η ^ 2 * |t| / μ) ε) (inputS D σ (η ^ 2 * |t| / μ) ε)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
      (fun x => matrixOperator_star (hH x)) |t| ε (fun x => by
        have h := (hp x).2
        rw [htime] at h
        exact h) x
    have e : ((-|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_neg ht, neg_neg]
    rw [e] at h
    exact h

end

end LargeSparsityCore.Native
