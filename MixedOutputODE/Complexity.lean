import MixedOutputODE.Theorem
import GeneralODE.Complexity

/-!
# The query bound with a mixed-output solver in closed form

For a mixed-output solver with `f(κ, δ) = c κ log(2/δ)` calls, the requested
accuracy `δ = ε/(4096 g²)` costs `log(2/δ) ≤ 10 𝓛`, where
`𝓛 = 1 + log((1 + ΛT) C̄ g / ε)` is the logarithmic factor of
`GeneralODE.Complexity` (`log_mixedDelta_le`). With the released bounds on
`κ`, the Taylor degree and the native block encoding, there is a protocol
with the guarantee of `general` (in the proof, the protocol of `general`)
that uses at most `227776401506304000 c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³`
native matrix queries and at most `26292000 c (g/√q₀) C̄ (1 + ΛT) 𝓛` calls of
each source interface (`general_query_bound`): the bound
`Õ(√s ḡ_path C̄ (1 + ΛT))` of eq. `ode:eq:general`.
-/

namespace SparseHamiltonian.MixedOutputODE

noncomputable section
open NativeSparseBlockEncoding GeneralODE GeneralODE.Solver GeneralODE.Complexity
  SparseStateOverlap ODEStateNormalization OracleCircuit
open scoped Nat

section Bounds

variable {Λ T Cbar g ε : ℝ}

/-- `log(2/δ) ≤ 10 𝓛` for the mixed solver accuracy `δ = ε/(4096 g²)`. -/
theorem log_mixedDelta_le (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    Real.log (2 / mixedDelta g ε) ≤ 10 * logFactor Λ T Cbar g ε := by
  have hg0 : 0 < g := by linarith
  set Q := (1 + Λ * T) * Cbar * g / ε with hQdef
  have hQ2 := ratio_ge_two hΛ hT hC hg hε hε1
  have heq : 2 / mixedDelta g ε = 8192 * (g * (g / ε)) := by
    unfold mixedDelta
    field_simp
    ring
  have hgQ : g / ε ≤ Q := by
    apply div_le_div_of_nonneg_right _ hε.le
    have h1 : 1 ≤ 1 + Λ * T := by nlinarith [mul_pos hΛ hT]
    have : 1 ≤ (1 + Λ * T) * Cbar := by nlinarith
    nlinarith
  have hgε : g ≤ g / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hlog : Real.log (2 / mixedDelta g ε) =
      Real.log 8192 + (Real.log g + Real.log (g / ε)) := by
    rw [heq, Real.log_mul (by norm_num) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have h8192 : Real.log 8192 ≤ 91 / 10 := by
    have h : (8192 : ℝ) = 2 ^ 13 := by norm_num
    rw [h, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hlg : Real.log g ≤ Real.log Q :=
    Real.log_le_log hg0 (hgε.trans hgQ)
  have hlgε : Real.log (g / ε) ≤ Real.log Q :=
    Real.log_le_log (by positivity) hgQ
  have hL := one_le_logFactor hΛ hT hC hg hε hε1
  unfold logFactor at hL ⊢
  rw [hlog]
  linarith

end Bounds

section Budget

variable {Λ T Cbar g ε : ℝ}

/-- The matrix-query budget for `f(κ, δ) = c κ log(2/δ)`, factor by factor. -/
theorem matrixBudget_le (c q₀ : ℝ) (hc : 0 ≤ c) (hq₀ : 0 < q₀) (s : ℕ) (hs : 1 ≤ s)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    matrixBudget (fun κ δ => c * κ * Real.log (2 / δ)) q₀ s Λ T Cbar g ε ≤
      227776401506304000 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * Real.sqrt s *
        logFactor Λ T Cbar g ε ^ 3) := by
  set 𝓛 := logFactor Λ T Cbar g ε with h𝓛def
  have h𝓛 : 1 ≤ 𝓛 := one_le_logFactor hΛ hT hC hg hε hε1
  have hκ := kappa_le hΛ hT hC
  have hκ0 : 0 ≤ Plan.kappa Λ T Cbar := by linarith [Plan.one_le_kappa (Λ := Λ) (T := T) hC]
  have hδ := log_mixedDelta_le hΛ hT hC hg hε hε1
  have hδ0 : 0 ≤ Real.log (2 / mixedDelta g ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (mixedDelta_pos hg hε)]
    linarith [mixedDelta_le hg hε hε1]
  have hK := degree_le hΛ hT hC hg hε hε1
  have hK0 : (0 : ℝ) ≤ Plan.degree Λ T Cbar g ε := Nat.cast_nonneg _
  have hsh := shape_le s hs hΛ hT hC hg hε hε1
  have hsh0 : 0 ≤ ImprovedPrecisionBudget.shape (2 * (s : ℝ))
      (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
      (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε)) := by
    unfold ImprovedPrecisionBudget.shape
    have := nativeLog_nonneg hΛ hT hC hg hε hε1
    positivity
  have hsq : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
  have hq : 0 < Real.sqrt q₀ := Real.sqrt_pos.mpr hq₀
  have hg0 : 0 < g := by linarith
  have hCT : 0 ≤ Cbar * (1 + Λ * T) := by
    have : 0 ≤ Λ * T := by positivity
    have : 0 ≤ Cbar := by linarith
    positivity
  unfold matrixBudget Plan.gain
  set G := 5 * g / Real.sqrt q₀ with hG
  have hG0 : 0 ≤ G := by positivity
  have hf : c * Plan.kappa Λ T Cbar * Real.log (2 / mixedDelta g ε) ≤
      c * (4382 * (Cbar * (1 + Λ * T))) * (10 * 𝓛) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left hκ hc) hδ hδ0 (by positivity)
  have hrest : 3 * ((Plan.degree Λ T Cbar g ε : ℝ) * (1327104 *
      ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
        (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε)))) ≤
      3 * ((34 * 𝓛) * (1327104 * (192 * (Real.sqrt s * 𝓛)))) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply mul_le_mul hK (mul_le_mul_of_nonneg_left hsh (by norm_num)) (by positivity)
      (by positivity)
  calc 40 * G * (c * Plan.kappa Λ T Cbar * Real.log (2 / mixedDelta g ε) *
        (3 * ((Plan.degree Λ T Cbar g ε : ℝ) * (1327104 *
          ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
            (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε))))))
      ≤ 40 * G * (c * (4382 * (Cbar * (1 + Λ * T))) * (10 * 𝓛) *
        (3 * ((34 * 𝓛) * (1327104 * (192 * (Real.sqrt s * 𝓛)))))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul hf hrest (by positivity) (by positivity)
    _ = 227776401506304000 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * Real.sqrt s *
        𝓛 ^ 3) := by
        rw [hG]
        field_simp
        ring

/-- The source budget for `f(κ, δ) = c κ log(2/δ)`. -/
theorem sourceBudget_le (c q₀ : ℝ) (hc : 0 ≤ c) (hq₀ : 0 < q₀)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    sourceBudget (fun κ δ => c * κ * Real.log (2 / δ)) q₀ Λ T Cbar g ε ≤
      26292000 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * logFactor Λ T Cbar g ε) := by
  have hκ := kappa_le hΛ hT hC
  have hδ := log_mixedDelta_le hΛ hT hC hg hε hε1
  have hδ0 : 0 ≤ Real.log (2 / mixedDelta g ε) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (mixedDelta_pos hg hε)]
    linarith [mixedDelta_le hg hε hε1]
  have hq : 0 < Real.sqrt q₀ := Real.sqrt_pos.mpr hq₀
  have hg0 : 0 < g := by linarith
  have hCT : 0 ≤ Cbar * (1 + Λ * T) := by
    have : 0 ≤ Λ * T := by positivity
    have : 0 ≤ Cbar := by linarith
    positivity
  have h𝓛 := one_le_logFactor hΛ hT hC hg hε hε1
  unfold sourceBudget Plan.gain
  have hf : c * Plan.kappa Λ T Cbar * Real.log (2 / mixedDelta g ε) ≤
      c * (4382 * (Cbar * (1 + Λ * T))) * (10 * logFactor Λ T Cbar g ε) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hκ hc) hδ hδ0 (by positivity)
  calc 40 * (5 * g / Real.sqrt q₀) * (3 * (c * Plan.kappa Λ T Cbar *
        Real.log (2 / mixedDelta g ε)))
      ≤ 40 * (5 * g / Real.sqrt q₀) * (3 * (c * (4382 * (Cbar * (1 + Λ * T))) *
        (10 * logFactor Λ T Cbar g ε))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 26292000 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * logFactor Λ T Cbar g ε) := by
        field_simp
        ring

end Budget

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- **Theorem `ode:thm:general` with a near-optimal mixed-output solver.** If
the block-input solver uses `c κ log(2/δ)` calls and guarantees conditional
output trace distance `δ`, one protocol makes at most
`C c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` native matrix queries and at most
`C' c (g/√q₀) C̄ (1 + ΛT) 𝓛` calls of each source, in every history, where
`𝓛 = 1 + log((1 + ΛT) C̄ g / ε)`; on every valid input it succeeds with
probability at least `175/256` and, after its work register is discarded, its
conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem general_query_bound (c q₀ : ℝ) (hc : 0 ≤ c)
    (hsolver : MixedBlockSolver (fun κ δ => c * κ * Real.log (2 / δ)) q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    ∃ (Tn d w : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (prot : ODERepeatProtocol.Protocol
        (physicalOracle D J₀ Jb (Plan.arcDegree Λ T Cbar g ε) Tn d (Plan.steps Λ T)
          (Plan.degree Λ T Cbar g ε) w) (EuclideanSpace ℂ (n × W))),
      (prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          227776401506304000 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * Real.sqrt s *
            logFactor Λ T Cbar g ε ^ 3) ∧
      (∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          26292000 * (c * (g / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) * logFactor Λ T Cbar g ε)) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = unitDirection v) → (b ≠ 0 → Jb x seed = unitDirection b) →
        (∀ t, 0 ≤ t → t ≤ T → ‖NormedSpace.exp (t • ODEPublicSourceMesh.generator D x)‖ ≤ Cbar) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b t‖ ≤
            g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        MixedOutcome prot x
          (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) ε := by
  obtain ⟨Tn, d, w, W, hWf, hWd, prot, h1, h2, h3⟩ := general _ q₀ hsolver hq₀ hq₀1 D Λ T Cbar
    g ε r₀ rb hΛ hT hC hg hε hε1 hA J₀ Jb hJ₀ hJb seed hseed
  refine ⟨Tn, d, w, W, hWf, hWd, prot, h1.trans ?_, fun b => (h2 b).trans ?_, h3⟩
  · exact matrixBudget_le c q₀ hc hq₀ s D.slots_pos hΛ hT hC hg hε hε1
  · exact sourceBudget_le c q₀ hc hq₀ hΛ hT hC hg hε hε1

end

end SparseHamiltonian.MixedOutputODE
