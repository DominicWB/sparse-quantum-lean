import GeneralSourceExtensions.Approx.Recast

/-!
# Temporary work registers: clean-input errors of programs

The manuscript measures the error of an implementation with temporary work registers on inputs
whose work registers are clean (eq. `access:eq:full-output`): `A`
implements `U` within `δ` if `‖A (ψ ⊗ |0⟩) - (U ψ) ⊗ |0⟩‖ ≤ δ ‖ψ‖` for every input `ψ`, so the
output must also return the work registers to `|0⟩` up to the error. Here:

* `CleanErr c A U δ`: this bound for an embedding `c` (`c ψ = ψ ⊗ |0⟩`);
* `CleanErr.adjoint`: for unitary `A` and `U` the adjoint has the same clean-input error;
* `CleanErr.mul`: clean-input errors add along products of contractions;
* `WorkEmbedding`: an isometric clean embedding with a unitary lift `F ↦ F ⊗ 1` of fixed gates;
* `workRecast`, `eval_workRecast_clean`: a program over exact oracles, run with every fixed gate
  lifted and every oracle call replaced by an implementation with temporary work registers, has
  clean-input error at most the sum of the clean-input errors of its calls;
* `perturbed_four_work`, `work_certificate`: the released four-attempt protocol over such
  implementations, heralded on clean work registers (the output encoding `c ∘ F`), keeps the
  guarantees of `GeneralSourceExtensions.perturbed_four` and `approx_certificate`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.CleanWorkODE

noncomputable section
open ContinuousLinearMap OracleCircuit
open ODEStateNormalization (unitDirection unitDirection_norm)
open GeneralSourceODE (SourceCall)
open SparseHamiltonian.GeneralSourceExtensions (ApproxCertificate norm_adjoint_apply_le)
open scoped InnerProduct BigOperators

/-! ### Clean-input errors -/

section Clean

variable {K KW : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup KW] [InnerProductSpace ℂ KW]

/-- **Clean-input error** (the temporary-work convention, eq. `access:eq:full-output`): `A`
implements `U` within `δ` on inputs whose work registers are clean, `c ψ = ψ ⊗ |0⟩`. -/
def CleanErr (c : K →L[ℂ] KW) (A : KW →L[ℂ] KW) (U : K →L[ℂ] K) (δ : ℝ) : Prop :=
  ∀ ψ : K, ‖A (c ψ) - c (U ψ)‖ ≤ δ * ‖ψ‖

variable {c : K →L[ℂ] KW}

theorem CleanErr.mono {A : KW →L[ℂ] KW} {U : K →L[ℂ] K} {δ δ' : ℝ} (h : CleanErr c A U δ)
    (hδ : δ ≤ δ') : CleanErr c A U δ' :=
  fun ψ => (h ψ).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg ψ))

/-- An exact lift has clean-input error `0`. -/
theorem CleanErr.of_comp {A : KW →L[ℂ] KW} {U : K →L[ℂ] K} (h : A ∘L c = c ∘L U) :
    CleanErr c A U 0 := by
  intro ψ
  have e : A (c ψ) = c (U ψ) := by
    simpa only [comp_apply] using congrArg (fun F : K →L[ℂ] KW => F ψ) h
  rw [e, sub_self, norm_zero, zero_mul]

/-- A unitary is an isometry. -/
theorem unitary_norm_map [CompleteSpace K] {U : K →L[ℂ] K} (hU : IsUnitary U) (v : K) :
    ‖U v‖ = ‖v‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mpr hU.1 v

/-- The adjoint of a unitary is an isometry. -/
theorem unitary_star_norm_map [CompleteSpace K] {U : K →L[ℂ] K} (hU : IsUnitary U) (v : K) :
    ‖star U v‖ = ‖v‖ := by
  have h : adjoint (star U) ∘L star U = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_star]
    exact hU.2
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (star U)).mpr h v

/-- **The adjoint of a unitary implementation** has the clean-input error of the
implementation. -/
theorem CleanErr.adjoint [CompleteSpace K] [CompleteSpace KW] {A : KW →L[ℂ] KW} {U : K →L[ℂ] K}
    {δ : ℝ} (hA : IsUnitary A) (hU : IsUnitary U) (h : CleanErr c A U δ) :
    CleanErr c (star A) (star U) δ := by
  intro ψ
  have hUu : U (star U ψ) = ψ := by
    rw [← mul_apply_eq_comp, hU.2, one_apply_eq_self]
  have hkey : star A (c ψ) - c (star U ψ) = -(star A (A (c (star U ψ)) - c ψ)) := by
    rw [map_sub, ← mul_apply_eq_comp (star A) A, hA.1, one_apply_eq_self,
      neg_sub]
  calc ‖star A (c ψ) - c (star U ψ)‖ = ‖A (c (star U ψ)) - c ψ‖ := by
        rw [hkey, norm_neg, unitary_star_norm_map hA]
    _ = ‖A (c (star U ψ)) - c (U (star U ψ))‖ := by rw [hUu]
    _ ≤ δ * ‖star U ψ‖ := h _
    _ = δ * ‖ψ‖ := by rw [unitary_star_norm_map hU]

/-- **Clean-input errors add** along products of contractions. -/
theorem CleanErr.mul {A A' : KW →L[ℂ] KW} {U U' : K →L[ℂ] K} {δ δ' : ℝ}
    (h : CleanErr c A U δ) (h' : CleanErr c A' U' δ') (hA : ‖A‖ ≤ 1) (hU' : ‖U'‖ ≤ 1)
    (hδ : 0 ≤ δ) : CleanErr c (A * A') (U * U') (δ + δ') := by
  intro ψ
  have e : (A * A') (c ψ) - c ((U * U') ψ) =
      A (A' (c ψ) - c (U' ψ)) + (A (c (U' ψ)) - c (U (U' ψ))) := by
    simp only [mul_apply_eq_comp, map_sub]
    abel
  have h1 : ‖A (A' (c ψ) - c (U' ψ))‖ ≤ δ' * ‖ψ‖ :=
    (A.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hA).trans (h' ψ))
  have h2 : ‖A (c (U' ψ)) - c (U (U' ψ))‖ ≤ δ * ‖ψ‖ :=
    (h _).trans (mul_le_mul_of_nonneg_left
      ((U'.le_opNorm ψ).trans (mul_le_of_le_one_left (norm_nonneg _) hU')) hδ)
  rw [e]
  calc _ ≤ ‖A (A' (c ψ) - c (U' ψ))‖ + ‖A (c (U' ψ)) - c (U (U' ψ))‖ := norm_add_le _ _
    _ ≤ δ' * ‖ψ‖ + δ * ‖ψ‖ := add_le_add h1 h2
    _ = (δ + δ') * ‖ψ‖ := by ring

end Clean

/-! ### Work embeddings and programs -/

/-- **A work embedding**: the isometric embedding `ψ ↦ ψ ⊗ |0⟩` of a workspace into the workspace
with temporary work registers, with the lift `F ↦ F ⊗ 1` of fixed gates, which preserves
unitarity and commutes with the embedding. -/
structure WorkEmbedding (K KW : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [NormedAddCommGroup KW] [InnerProductSpace ℂ KW] [CompleteSpace KW] where
  /-- The embedding `ψ ↦ ψ ⊗ |0⟩`. -/
  clean : K →L[ℂ] KW
  isometry : clean† ∘L clean = 1
  /-- The lift `F ↦ F ⊗ 1`. -/
  lift : (K →L[ℂ] K) → (KW →L[ℂ] KW)
  lift_unitary : ∀ F, IsUnitary F → IsUnitary (lift F)
  lift_clean : ∀ F, lift F ∘L clean = clean ∘L F

namespace WorkEmbedding

variable {K KW : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup KW] [InnerProductSpace ℂ KW] [CompleteSpace KW]
variable (e : WorkEmbedding K KW)

theorem clean_norm (ψ : K) : ‖e.clean ψ‖ = ‖ψ‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self e.clean).mpr e.isometry ψ

theorem clean_unit {ψ : K} (hψ : ‖ψ‖ = 1) : ‖e.clean ψ‖ = 1 :=
  (e.clean_norm ψ).trans hψ

theorem adjoint_clean (ψ : K) : (e.clean†) (e.clean ψ) = ψ := by
  rw [← comp_apply, e.isometry, one_apply_eq_self]

/-- The output encoding followed by the clean work registers is an isometry. -/
theorem output_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {F : E →L[ℂ] K} (hF : F† ∘L F = 1) :
    (e.clean ∘L F)† ∘L (e.clean ∘L F) = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [adjoint_comp, comp_apply, e.adjoint_clean]
  rw [← comp_apply, hF]

end WorkEmbedding

section Programs

variable {K KW : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup KW] [InnerProductSpace ℂ KW] [CompleteSpace KW]
variable {L X Y : Type*} {O : L → X → K →L[ℂ] K} {O' : L → Y → KW →L[ℂ] KW}

/-- The same program syntax over oracles with temporary work registers: every fixed gate is
lifted, every oracle call is a call of the new oracle with the same label. -/
def workRecast (e : WorkEmbedding K KW) :
    MultiOracleCircuit.Program O → MultiOracleCircuit.Program O'
  | .fixed U hU => .fixed (e.lift U) (e.lift_unitary U hU)
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (workRecast e p) (workRecast e q)

/-- The lifted program keeps every weighted cost. -/
@[simp] theorem cost_workRecast (e : WorkEmbedding K KW) (p : MultiOracleCircuit.Program O)
    (w : L → ℕ) : (workRecast (O' := O') e p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [workRecast, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- **Clean-input error of a lifted program.** With unitary oracles, if every oracle `l` at `y`
implements the oracle at `x` within `δ · w l` on clean work registers, the lifted program at `y`
implements the program at `x` within `δ · cost w` on clean work registers; inverse calls have the
error of forward calls. -/
theorem eval_workRecast_clean (e : WorkEmbedding K KW) (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (hO' : ∀ l y, IsUnitary (O' l y)) (x : X) (y : Y)
    {δ : ℝ} (hδ : 0 ≤ δ) (w : L → ℕ)
    (h : ∀ l, CleanErr e.clean (O' l y) (O l x) (δ * w l)) :
    CleanErr e.clean ((workRecast (O' := O') e p).eval y) (p.eval x) (δ * p.cost w) := by
  induction p with
  | fixed U hU =>
      have h0 := CleanErr.of_comp (e.lift_clean U)
      simpa only [workRecast, MultiOracleCircuit.Program.eval_fixed,
        MultiOracleCircuit.Program.cost_fixed, Nat.cast_zero, mul_zero] using h0
  | query l => exact h l
  | queryAdjoint l =>
      simpa only [workRecast, MultiOracleCircuit.Program.eval_queryAdjoint,
        MultiOracleCircuit.Program.cost_queryAdjoint] using (h l).adjoint (hO' l y) (hO l x)
  | seq p q hp hq =>
      simp only [workRecast, MultiOracleCircuit.Program.eval_seq,
        MultiOracleCircuit.Program.cost_seq, Nat.cast_add, mul_add]
      exact hp.mul hq ((workRecast (O' := O') e p).eval_unitary hO' y).norm_le_one
        (q.eval_unitary hO x).norm_le_one (mul_nonneg hδ (Nat.cast_nonneg _))

end Programs

/-! ### The perturbed four-attempt protocol with temporary work registers -/

section Perturbed

variable {P R RW : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  [NormedAddCommGroup RW] [InnerProductSpace ℂ RW] [CompleteSpace RW]

variable [FiniteDimensional ℂ P]
variable {L₁ L₂ X₁ X₂ : Type*} {O₁ : L₁ → X₁ → R →L[ℂ] R} {O₂ : L₂ → X₂ → RW →L[ℂ] RW}

/-- **The perturbed four-attempt protocol with temporary work registers.** Let the trials `q₁ j`
at `x₁` have mean Born success at least `1/4` and phase-free direction error `δ` for a unit target
`v`, and let every trial `q₂ j` at `x₂`, started on the seed with clean work registers, end within
`η ≤ 1/400` of the output of `q₁ j` with clean work registers. Then four fresh trials of `q₂`,
heralded on the output flag and clean work registers, succeed with probability at least `2/3`,
and their conditional output is a density operator within trace distance `6 δ + 12 η` of
`|v⟩⟨v|`. -/
theorem perturbed_four_work (e : WorkEmbedding R RW) (q₁ : ℕ → MultiOracleCircuit.Program O₁)
    (q₂ : ℕ → MultiOracleCircuit.Program O₂) {M : ℕ} (hM : 0 < M) {ψ : R} (hψ : ‖ψ‖ = 1)
    {F : P →L[ℂ] R} (hF : F† ∘L F = 1) (x₁ : X₁) (x₂ : X₂) (v : P) (hv : ‖v‖ = 1)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη1 : η ≤ 1 / 400)
    (hU₁ : ∀ j, IsUnitary ((q₁ j).eval x₁)) (hU₂ : ∀ j, IsUnitary ((q₂ j).eval x₂))
    (hclose : ∀ j, j < M → ‖(q₂ j).eval x₂ (e.clean ψ) - e.clean ((q₁ j).eval x₁ ψ)‖ ≤ η)
    (hmean : (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range M,
      ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) / (M : ℝ))
    (hdir : ∀ j, j < M → (F†) ((q₁ j).eval x₁ ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection ((F†) ((q₁ j).eval x₁ ψ)) - v‖ ≤ δ) :
    (2 : ℝ) / 3 ≤ (ODERepeatProtocol.fourTrials q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF)).successMass x₂ ∧
    ODEMixedOutput.IsDensity
      ((ODERepeatProtocol.fourTrials q₂ M hM (e.clean ψ) (e.clean_unit hψ) (e.clean ∘L F)
        (e.output_isometry hF)).conditionalDensity x₂) ∧
    ∃ h : ((ODERepeatProtocol.fourTrials q₂ M hM (e.clean ψ) (e.clean_unit hψ) (e.clean ∘L F)
        (e.output_isometry hF)).conditionalDensity x₂ -
        ODEMixedOutput.pureOperator v).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance
        ((ODERepeatProtocol.fourTrials q₂ M hM (e.clean ψ) (e.clean_unit hψ) (e.clean ∘L F)
          (e.output_isometry hF)).conditionalDensity x₂)
        (ODEMixedOutput.pureOperator v) h ≤ 6 * δ + 12 * η := by
  let t₁ := ODERepeatProtocol.ofCircuits q₁ M hM ψ hψ F hF
  let t₂ := ODERepeatProtocol.ofCircuits q₂ M hM (e.clean ψ) (e.clean_unit hψ) (e.clean ∘L F)
    (e.output_isometry hF)
  have hu₁ : ∀ j, IsUnitary ((t₁.circuit j).eval x₁) := fun j => hU₁ j.val
  have hu₂ : ∀ j, IsUnitary ((t₂.circuit j).eval x₂) := fun j => hU₂ j.val
  have hb₁ := t₁.probability_bounds x₁ hu₁
  have hb₂ := t₂.probability_bounds x₂ hu₂
  have ha : ∀ j, ‖t₁.amplitude x₁ j‖ ≤ 1 := fun j =>
    (sq_le_one_iff₀ (norm_nonneg _)).mp (hb₁ j).2
  have ha' : ∀ j, ‖t₂.amplitude x₂ j‖ ≤ 1 := fun j =>
    (sq_le_one_iff₀ (norm_nonneg _)).mp (hb₂ j).2
  have hclose' : ∀ j : Fin t₂.choices, ‖t₂.amplitude x₂ j - t₁.amplitude x₁ j‖ ≤ η := by
    intro j
    change ‖((e.clean ∘L F)†) ((q₂ j.val).eval x₂ (e.clean ψ)) -
      (F†) ((q₁ j.val).eval x₁ ψ)‖ ≤ η
    have h1 : (F†) ((q₁ j.val).eval x₁ ψ) =
        ((e.clean ∘L F)†) (e.clean ((q₁ j.val).eval x₁ ψ)) := by
      rw [adjoint_comp, comp_apply, e.adjoint_clean]
    rw [h1, ← map_sub]
    exact (norm_adjoint_apply_le _ (e.output_isometry hF) _).trans (hclose j.val j.isLt)
  have hmean' : (1 : ℝ) / 4 ≤
      ODERepeatProbability.mean (fun j : Fin M => ‖t₁.amplitude x₁ j‖ ^ 2) := by
    unfold ODERepeatProbability.mean
    have hsum : (∑ j : Fin M, ‖t₁.amplitude x₁ j‖ ^ 2) =
        ∑ j ∈ Finset.range M,
          ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2 := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) M]
      exact Finset.sum_congr rfl (fun j _ => t₁.probability_eq_projected x₁ j)
    rw [hsum]
    exact hmean
  have hdir' : ∀ j : Fin t₁.choices, t₁.amplitude x₁ j ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection (t₁.amplitude x₁ j) - v‖ ≤ δ :=
    fun j hz => hdir j.val j.isLt hz
  obtain ⟨hS2, hD, hh, htr⟩ := GateSynth.perturb_four hM (t₁.amplitude x₁) (t₂.amplitude x₂) v hv
    hδ hη1 ha ha' hclose' hmean' hdir'
  have hsucc : (ODERepeatProtocol.fourTrials q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF)).successMass x₂ =
      ODERepeatProbability.successProbability (t₂.probability x₂) :=
    ODERepeatProtocol.Protocol.four_successMass_eq t₂ x₂
  have hdens : (ODERepeatProtocol.fourTrials q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF)).conditionalDensity x₂ =
      ODEMixedOutput.ensemble
        (ODERepeatProbability.conditionalWeight (t₂.probability x₂))
        (fun b => t₂.outputDirection x₂ b.2) :=
    ODERepeatProtocol.Protocol.four_conditionalDensity_eq t₂ x₂
  refine ⟨?_, ?_, ?_⟩
  · rw [hsucc]
    exact hS2
  · rw [hdens]
    exact hD
  · rw [hdens]
    exact ⟨hh, htr⟩

end Perturbed

/-! ### The certificate over source oracles with temporary work registers -/

section Certificate

variable {P R RW : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
  [NormedAddCommGroup RW] [InnerProductSpace ℂ RW] [CompleteSpace RW]

set_option maxHeartbeats 1000000 in
/-- **Transfer to source oracles with temporary work registers.** Let a counted two-interface
family `q` satisfy the released complete certificate at the input `x₁`, and let `q₁` over the
exact actual oracles `O₁` have the same evaluations at `x₁`, the same matrix counts, one `P_w` and
one `U_load` call per preparation call and one `P_w†` call per unpreparation call. If, at another
input `x₂`, the oracles `O₂` on the workspace with temporary work registers implement `O₁` at
`x₁` exactly on clean work registers on the matrix labels and within `δ` on the three source
labels, with `30 g δ ≤ 1/400` and `30 g δ ≤ ε/20`, then four fresh trials of the lifted family
over `O₂`, heralded on clean work registers, satisfy `ApproxCertificate` at `x₂`. -/
theorem work_certificate (e : WorkEmbedding R RW) {L X₁ X₂ : Type*}
    {O : (L ⊕ Bool) → X₁ → R →L[ℂ] R}
    {O₁ : NativeSparseBlockEncoding.Query ⊕ SourceCall → X₁ → R →L[ℂ] R}
    {O₂ : NativeSparseBlockEncoding.Query ⊕ SourceCall → X₂ → RW →L[ℂ] RW}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R} {F : P →L[ℂ] R} {x₁ : X₁}
    {target : P} {s Θ ell g ε : ℝ}
    (hCert : ODECompleteTrial.Certificate q M ψ F x₁ target s Θ ell g ε)
    (q₁ : ℕ → MultiOracleCircuit.Program O₁) (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hEval : ∀ j, (q₁ j).eval x₁ = (q j).eval x₁)
    (hMatrix : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (hWeight : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .weight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hLoad : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .load) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hUnweight : ∀ j, (q₁ j).cost (GeneralSourceODE.Oracles.calls .unweight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hSource : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.sourceCalls =
      2 * (q j).cost (ODESourceQueryBudget.sourceWeight false) +
        (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hO₁ : ∀ l y, IsUnitary (O₁ l y)) (hO₂ : ∀ l y, IsUnitary (O₂ l y))
    (x₂ : X₂) {δ : ℝ} (hδ : 0 ≤ δ)
    (hclean : ∀ l, CleanErr e.clean (O₂ l x₂) (O₁ l x₁)
      (δ * GeneralSourceODE.Oracles.sourceCalls l))
    (hδ1 : 30 * g * δ ≤ 1 / 400) (hδε : 30 * g * δ ≤ ε / 20) (hTarget : target ≠ 0) :
    ApproxCertificate
      (ODERepeatProtocol.fourTrials (fun j => workRecast (O' := O₂) e (q₁ j)) M hM
        (e.clean ψ) (e.clean_unit hψ) (e.clean ∘L F) (e.output_isometry hF)) x₂
      target s Θ ell g ε := by
  have hTrial := hCert.trial
  let q₂ : ℕ → MultiOracleCircuit.Program O₂ := fun j => workRecast (O' := O₂) e (q₁ j)
  have hcost₂ : ∀ (w : NativeSparseBlockEncoding.Query ⊕ SourceCall → ℕ) j,
      (q₂ j).cost w = (q₁ j).cost w := fun w j => cost_workRecast e (q₁ j) w
  -- Per-trial perturbation on clean work registers.
  have hclose : ∀ j, j < M →
      ‖(q₂ j).eval x₂ (e.clean ψ) - e.clean ((q₁ j).eval x₁ ψ)‖ ≤ 30 * g * δ := by
    intro j hj
    have h := eval_workRecast_clean (O' := O₂) e (q₁ j) hO₁ hO₂ x₁ x₂ hδ
      GeneralSourceODE.Oracles.sourceCalls hclean ψ
    rw [hψ, mul_one] at h
    refine h.trans ?_
    have hc : ((q₁ j).cost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ 30 * g := by
      rw [hSource j]
      push_cast
      have h1 := hTrial.source_queries j hj false
      have h2 := hTrial.source_queries j hj true
      linarith
    calc δ * ((q₁ j).cost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ δ * (30 * g) :=
          mul_le_mul_of_nonneg_left hc hδ
      _ = 30 * g * δ := by ring
  have hU₁ : ∀ j, IsUnitary ((q₁ j).eval x₁) := fun j => (q₁ j).eval_unitary hO₁ x₁
  have hU₂ : ∀ j, IsUnitary ((q₂ j).eval x₂) := fun j => (q₂ j).eval_unitary hO₂ x₂
  have hmean : (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range M,
      ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) / (M : ℝ) := by
    simp only [hEval]
    exact hTrial.mean_success
  have hdir : ∀ j, j < M → (F†) ((q₁ j).eval x₁ ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection ((F†) ((q₁ j).eval x₁ ψ)) -
        unitDirection target‖ ≤ ε / 500 := by
    intro j hj hz
    rw [hEval j] at hz ⊢
    exact hTrial.direction_error j hj hz
  have hε : 0 ≤ ε := by
    obtain ⟨_, h⟩ := hCert.conditional_error
    exact (ODEMixedOutput.hermitianTraceDistance_nonneg _ _ _).trans h
  obtain ⟨hS2, hD, hh, htr⟩ := perturbed_four_work e q₁ q₂ hM hψ hF x₁ x₂ (unitDirection target)
    (unitDirection_norm target hTarget) (δ := ε / 500) (by positivity) hδ1 hU₁ hU₂ hclose
    hmean hdir
  refine
    { success_two_thirds := hS2
      matrix_queries := ?_
      weight_calls := ?_
      load_calls := ?_
      unweight_calls := ?_
      source_calls := ?_
      output_density := hD
      conditional_error := ⟨hh, htr.trans (by linarith)⟩ }
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF) GeneralSourceODE.Oracles.matrixCalls
      (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
      (fun j hj => by rw [hcost₂, hMatrix j]; exact hTrial.matrix_queries j hj)
    calc
      _ ≤ 4 * (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) := h
      _ = 1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by ring
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF) (GeneralSourceODE.Oracles.calls .weight) (10 * g)
      (fun j hj => by rw [hcost₂, hWeight j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF) (GeneralSourceODE.Oracles.calls .load) (10 * g)
      (fun j hj => by rw [hcost₂, hLoad j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF) (GeneralSourceODE.Oracles.calls .unweight)
      (10 * g)
      (fun j hj => by rw [hcost₂, hUnweight j]; exact hTrial.source_queries j hj true)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM (e.clean ψ) (e.clean_unit hψ)
      (e.clean ∘L F) (e.output_isometry hF) GeneralSourceODE.Oracles.sourceCalls (30 * g)
      (fun j hj => by
        rw [hcost₂, hSource j]
        push_cast
        have h1 := hTrial.source_queries j hj false
        have h2 := hTrial.source_queries j hj true
        linarith)
    linarith

end Certificate

end

end SparseHamiltonian.CleanWorkODE
