import TimeDependentODE.Native.Simulation

/-!
# The coherent sampled-time ODE SELECT with one clean encoding

The native layer implements every active layer of the slot-dependent ODE
clock with `72` coherent sampled-time queries (`exists_native_select`). One
known final alignment gate makes the clean output equal to the clean input
(`select`). The public rescaling `γ` is chosen once from `s`, `ρ T` and `ε`,
before the branch nodes and durations; the mesh conditions
`8 s (ρ T) ≤ M` and `3 (√(2s) ρ T)³ ≤ ε M²` give the clock condition
`w ≤ 1/4` and a Cayley error at most `ε / 3`. The query count is at most
`663552 * shape (2 s) (ρ T) (log (2/ε))`, the released constant of the
time-independent ODE SELECT, and does not depend on `M`.
-/

namespace SparseHamiltonian.TimeDependentODE

namespace Select

noncomputable section

open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s M : ℕ}

/-- The rescaled step obeys the clock condition `w ≤ 1/4` under the public
mesh condition `8 s ρ T ≤ M`, for every admissible rescaling. -/
theorem step_le_quarter (γ ρ T : ℝ) (hs : (1 : ℝ) ≤ s) (hγ : 0 < γ)
    (hWidth : 1 ≤ γ * Real.sqrt (2 * (s : ℝ))) (hρT : 0 ≤ ρ * T) (hM : 0 < M)
    (hMesh : 8 * s * (ρ * T) ≤ M) : step (s : ℝ) γ ρ T M ≤ 1 / 4 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsR : (0 : ℝ) < Real.sqrt (2 * (s : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (2 * (s : ℝ)) * Real.sqrt (2 * (s : ℝ)) = 2 * s :=
    Real.mul_self_sqrt (by linarith)
  have hratio : Real.sqrt (2 * (s : ℝ)) / γ ≤ 2 * s := by
    rw [div_le_iff₀ hγ]
    nlinarith
  have htime : time (2 * (s : ℝ)) (ρ * T) γ ≤ 2 * s * (ρ * T) := by
    unfold time
    rw [mul_div_assoc]
    calc
      ρ * T * (Real.sqrt (2 * (s : ℝ)) / γ) ≤ ρ * T * (2 * s) :=
        mul_le_mul_of_nonneg_left hratio hρT
      _ = 2 * s * (ρ * T) := by ring
  unfold step
  rw [div_le_iff₀ hMR]
  linarith

/-- The explicit query count before the manuscript logarithm conversion. -/
theorem count_le_shape (γ ρ T ε : ℝ) (hγ : 0 < γ) (hρT : 0 ≤ ρ * T)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hM : 0 < M)
    (hBudget : time (2 * (s : ℝ)) (ρ * T) γ * moment γ +
      width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * T)
          (ImprovedPrecisionBudget.targetLog ε))
    (q : ℕ) (hq : q ≤ 6 * degree (s : ℝ) γ ρ T ε M * 72) :
    (q : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * T)
      (ImprovedPrecisionBudget.targetLog ε) := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hW : (M : ℝ) * step (s : ℝ) γ ρ T M * moment γ =
      time (2 * (s : ℝ)) (ρ * T) γ * moment γ := by
    unfold step
    field_simp
  have htime : 0 ≤ time (2 * (s : ℝ)) (ρ * T) γ :=
    div_nonneg (mul_nonneg hρT (Real.sqrt_nonneg _)) hγ.le
  have hdeg0 := SharpFilterSchedule.degree_le (width (2 * (s : ℝ)) γ)
    ((M : ℝ) * step (s : ℝ) γ ρ T M * moment γ) (ε / 3) (width_ge_one _ _)
    (by rw [hW]; exact mul_nonneg htime (moment_nonneg γ)) (by positivity) (by linarith)
  have hlog : 1 + SharpFilterSchedule.logBudget (ε / 3) =
      ImprovedPrecisionBudget.circuitLog ε := by
    unfold SharpFilterSchedule.logBudget ImprovedPrecisionBudget.circuitLog
    congr 2
    field_simp
  have hdeg : (degree (s : ℝ) γ ρ T ε M : ℝ) ≤ 128 * (time (2 * (s : ℝ)) (ρ * T) γ * moment γ +
      width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε) := by
    have h := hdeg0
    rw [hlog] at h
    calc
      (degree (s : ℝ) γ ρ T ε M : ℝ) ≤ 128 * ((M : ℝ) * step (s : ℝ) γ ρ T M *
          moment γ + width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε) := h
      _ = _ := by rw [hW]
  have hqR : (q : ℝ) ≤ 6 * (degree (s : ℝ) γ ρ T ε M : ℝ) * 72 := by exact_mod_cast hq
  calc
    (q : ℝ) ≤ 6 * (degree (s : ℝ) γ ρ T ε M : ℝ) * 72 := hqR
    _ ≤ 6 * (128 * (time (2 * (s : ℝ)) (ρ * T) γ * moment γ +
        width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε)) * 72 := by
      nlinarith
    _ ≤ 6 * (128 * (12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * T)
        (ImprovedPrecisionBudget.targetLog ε))) * 72 := by nlinarith
    _ = 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * T)
        (ImprovedPrecisionBudget.targetLog ε) := by ring

set_option maxRecDepth 8192 in
/-- The native coherent sampled-time ODE program at one public rescaling. -/
theorem exists_native_select (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M)
    (etaH etaD R T : ℝ) (k : ι → ℝ) (u : ι → Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i r, 0 ≤ u i r) (huT : ∀ i r, u i r ≤ T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (γ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : step (s : ℝ) γ (etaH + R * etaD) T M ≤ 1 / 4) :
    ∃ p : MultiOracleCircuit.Program
        (oracle (ι := ι) D M (degree (s : ℝ) γ (etaH + R * etaD) T ε M)),
      p.count ≤ 6 * degree (s : ℝ) γ (etaH + R * etaD) T ε M * 72 ∧
      (input D hM b0 γ (etaH + R * etaD) T ε)† ∘L input D hM b0 γ (etaH + R * etaD) T ε = 1 ∧
      (output D hM b0 γ (etaH + R * etaD) T ε)† ∘L
        output D hM b0 γ (etaH + R * etaD) T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D hM b0 γ (etaH + R * etaD) T ε -
          output D hM b0 γ (etaH + R * etaD) T ε ∘L selectEvolution D hM k u x‖ ≤
          2 * (ε / 3) + M * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 := by
  let O := oracle (ι := ι) D M (degree (s : ℝ) γ (etaH + R * etaD) T ε M)
  have hO : ∀ l x, IsUnitary (O l x) := oracle_unitary D M _
  let E : SharpClockQuery.Space (P := ODEJointNative.Public ι n)
      (V := ODEJointNative.Private ι n)
      (step (s : ℝ) γ (etaH + R * etaD) T M) (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3)
        →L[ℂ] Physical ι n Z M M (degree (s : ℝ) γ (etaH + R * etaD) T ε M) :=
    (embedding D hM b0 M (degree (s : ℝ) γ (etaH + R * etaD) T ε M)).toContinuousLinearMap
  have hE : E† ∘L E = 1 :=
    (embedding D hM b0 M (degree (s : ℝ) γ (etaH + R * etaD) T ε M)).adjoint_comp_self
  have hQ : ∀ r < 2 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
        ((M : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T M * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => TimeDependent.activeClockV (P := ODEJointNative.Public ι n)
          (actions D hM k u (etaH + R * etaD) T γ x) M
          (SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
            ((M : ℝ) * step (s : ℝ) γ (etaH + R * etaD) T M * moment γ) (ε / 3)) r) E 72 :=
    fun r _ => implementsOn D hM b0 k (rescaling γ T u) (etaH + R * etaD) M _ r
  have hCore := select_core D hM etaH etaD R T k u hH hDiss hρ hT hk hu huT
    hrH hcH hrD hcD γ ε hγ hγOne hε hεOne hStep O hO E hE 72
  obtain ⟨p, hCount, hAction⟩ := hCore hQ
  have hInIso := SharpClockQuery.input_isometry (P := ODEJointNative.Public ι n)
    (V := ODEJointNative.Private ι n) (step (s : ℝ) γ (etaH + R * etaD) T M)
    (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3) (width_ge_one _ _)
  have hOutIso := SharpClockSimulation.output_isometry (P := ODEJointNative.Public ι n)
    (V := ODEJointNative.Private ι n) (step (s : ℝ) γ (etaH + R * etaD) T M)
    (width (2 * (s : ℝ)) γ) (moment γ) M (ε / 3) (width_ge_one _ _)
  exact ⟨p, hCount, NativeSparseAttenuation.isometry_comp _ _ hInIso hE,
    NativeSparseAttenuation.isometry_comp _ _ hOutIso hE, hAction⟩

/-- The complete workspace, including the alignment spectator. -/
abbrev Workspace (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z] (s M : ℕ) (γ ρ T ε : ℝ) :=
  CleanOutputAlignment.Double (Physical ι n Z M M (degree (s : ℝ) γ ρ T ε M))

/-- Each query is one coherent sampled-time native primitive, with untouched
spectator registers. -/
abbrev alignedOracle (D : Data (X × Fin M) n Z s) (γ ρ T ε : ℝ) :
    Query → X → Workspace ι n Z s M γ ρ T ε →L[ℂ] Workspace ι n Z s M γ ρ T ε :=
  AlignedMultiOracleProgram.oracle (oracle (ι := ι) D M (degree (s : ℝ) γ ρ T ε M))

omit [DecidableEq ι] [DecidableEq Z] in
theorem alignedOracle_unitary (D : Data (X × Fin M) n Z s) (γ ρ T ε : ℝ) (l : Query) (x : X) :
    IsUnitary (alignedOracle (ι := ι) D γ ρ T ε l x) :=
  CoherentQuerySchedule.oracle_unitary _ (oracle_unitary D M _) l x

/-- The same known clean preparation at both ends of the SELECT circuit. -/
def alignedInput (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M)
    (γ ρ T ε : ℝ) : ODEJointNative.Public ι n →L[ℂ] Workspace ι n Z s M γ ρ T ε :=
  AlignedMultiOracleProgram.input (input D hM b0 γ ρ T ε)

set_option maxRecDepth 8192 in
/-- **Coherent sampled-time ODE SELECT.** One public rescaling and one clean
encoding serve every table of branch nodes `|k i| ≤ R` and slot durations
`0 ≤ u i r ≤ T`. The full output is within `ε` of the ordered branch
products, uniformly over the unknown instance, with at most
`663552 * shape (2 s) (ρ T) (log (2/ε))` queries. -/
theorem select (D : Data (X × Fin M) n Z s) (hM : 0 < M) (b0 : ι × Fin M)
    (etaH etaD R T ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + R * etaD) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hMesh : 8 * s * ((etaH + R * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T)) ^ 3 ≤ ε * (M : ℝ) ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ (k : ι → ℝ) (u : ι → Fin M → ℝ), (∀ i, |k i| ≤ R) →
        (∀ i r, 0 ≤ u i r) → (∀ i r, u i r ≤ T) →
        ∃ p : MultiOracleCircuit.Program (alignedOracle (ι := ι) D γ (etaH + R * etaD) T ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * (s : ℝ))
            ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε) ∧
          (alignedInput D hM b0 γ (etaH + R * etaD) T ε)† ∘L
            alignedInput D hM b0 γ (etaH + R * etaD) T ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L alignedInput D hM b0 γ (etaH + R * etaD) T ε -
              alignedInput D hM b0 γ (etaH + R * etaD) T ε ∘L selectEvolution D hM k u x‖ ≤
                ε := by
  have hs : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hsTwo : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  have hρT : 0 ≤ (etaH + R * etaD) * T := mul_nonneg hρ.le hT.le
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision (2 * (s : ℝ))
      ((etaH + R * etaD) * T) ε hsTwo hρT hε hεOne
  have hStep := step_le_quarter (s := s) γ (etaH + R * etaD) T hs hγ hWidth hρT hM hMesh
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hIn, hOut, hAct⟩ := exists_native_select D hM b0 etaH etaD R T k u
    hH hDiss hρ hT hk hu huT hrH hcH hrD hcD γ ε hγ hγOne hε hεOne hStep
  let q := AlignedMultiOracleProgram.program _ _ hIn hOut p
  refine ⟨q, ?_, AlignedMultiOracleProgram.input_isometry _ hIn, fun x => ⟨?_, ?_⟩⟩
  · have hqc : q.count = p.count := AlignedMultiOracleProgram.program_count _ _ hIn hOut p
    calc
      (q.count : ℝ) = (p.count : ℝ) := by exact_mod_cast hqc
      _ ≤ _ := count_le_shape γ (etaH + R * etaD) T ε hγ hρT hε hεOne hM hBudget p.count hCount
  · exact q.eval_unitary (CoherentQuerySchedule.oracle_unitary _ (oracle_unitary D M _)) x
  · have hAligned := AlignedMultiOracleProgram.program_error _ _ hIn hOut p x
      (selectEvolution D hM k u x)
    change ‖q.eval x ∘L alignedInput D hM b0 γ (etaH + R * etaD) T ε -
      alignedInput D hM b0 γ (etaH + R * etaD) T ε ∘L selectEvolution D hM k u x‖ ≤ ε
    rw [show alignedInput D hM b0 γ (etaH + R * etaD) T ε =
      AlignedMultiOracleProgram.input (input D hM b0 γ (etaH + R * etaD) T ε) from rfl,
      hAligned]
    have hCay : (M : ℝ) * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 ≤
        ε / 3 := by
      have hMsq : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      have heq : (M : ℝ) * (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T) / M) ^ 3 =
          (Real.sqrt (2 * (s : ℝ)) * ((etaH + R * etaD) * T)) ^ 3 / (M : ℝ) ^ 2 := by
        field_simp
      rw [heq, div_le_iff₀ hMsq]
      linarith
    linarith [(hAct x).2]

end

end Select

end SparseHamiltonian.TimeDependentODE
