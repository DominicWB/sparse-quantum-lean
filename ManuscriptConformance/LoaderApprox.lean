import ManuscriptConformance.MeshLoaderColumns
import GeneralSourceExtensions.Approx.Recast

/-!
# Approximate-completion stability of the clean-column loader (item D1)

Item D1 separates the exact case from the stability of approximate completions. This module proves
the stability for the amplified trials of the general-source mesh solvers. The trials call the
actual preparation and its literal inverse, and `U R_ψ U† = R_{Uψ}`, so the `j`-th trial depends
on the preparation only through the prepared vector `Uψ`. A perturbation of that vector by `δ`
moves the trial by at most `(4j + 1) δ`. The released perturbation argument of the four-attempt
protocol (`GeneralSourceExtensions.perturbed_four`) uses the trials only on the seed. So a loader
`Lo` that is within `δ` of a label-controlled `loader J` on the seed branch state after `P_w`
(not in operator norm, and with no assumption on `Lo` elsewhere) keeps the guarantee of `J` up to
`O(g δ)`.

* `ODEGroverActual.grover_pow_sub_le`, `ODEGroverActual.trial_sub_le`: the `j`-th Grover power of
  the actual ray moves by at most `(4j + 1) ‖φ' - φ‖` when the prepared unit vector moves from `φ`
  to `φ'` (from `projector_sub_apply_le`, `grover_sub_apply_le`, `grover_norm`, `reflect_norm`,
  `reflect_norm_two`, `norm_map_of_isUnitary`).
* `GeneralSourceExtensions.perturbed_four_seed`: `perturbed_four` with the trials close on the seed
  only; `approx_certificate_seed`: so the released complete certificate of a counted family gives
  `ApproxCertificate` for any family with its counts within `20 g δ` of it on the seed.
* `GeneralSourceODE.Compiled.program_seed_dev`: the source-loaded program moves on the public seed
  by at most the deviation of the preparation interface on the seed input.
* `MeshNative.publicTrialsS_seed_dev`: so the compiled public trials move on the seed by at most
  `(4j + 1)` times that deviation.
* `MeshOracles.columns_approx_certificate`: the released complete certificate of the public trial
  family of a label-controlled `J` gives `ApproxCertificate` for the four-attempt protocol over the
  actual oracles `P_w`, `Lo`, `P_w†`. The hypotheses are
  `‖Lo (P_w ⊗ 1)|seed state⟩ - loader J (P_w ⊗ 1)|seed state⟩‖ ≤ δ`, `20 g δ ≤ 1/400` and
  `20 g δ ≤ ε/20`. The worst-case counts are the released ones; the success probability is at
  least `2/3`; the conditional trace distance is at most `ε`.

Scope: the stability of the trial family for one approximate loader, at the level of the public
mesh trial family. The endpoints of `ode:thm:time` with approximate columns need, besides this, a
reference family fixed before the instance; they are not stated here.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ODEGroverActual

noncomputable section
open ContinuousLinearMap OracleCircuit PhaseSubspaceGates
open scoped InnerProduct

section Grover

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A unitary preserves norms. -/
theorem norm_map_of_isUnitary {U : K →L[ℂ] K} (hU : IsUnitary U) (v : K) : ‖U v‖ = ‖v‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self U).mpr hU.1 v

/-- The reflection `1 - 2Q` about an orthogonal projection preserves norms. -/
theorem reflect_norm {Q : K →L[ℂ] K} (hQ : IsOrthogonalProjection Q) (v : K) :
    ‖((1 : K →L[ℂ] K) - (2 : ℂ) • Q) v‖ = ‖v‖ := by
  have h : (1 : K →L[ℂ] K) - (2 : ℂ) • Q = phase Q (-1) := by
    simp only [phase]
    module
  rw [h]
  exact norm_map_of_isUnitary (phase_unitary Q hQ (-1) (by simp)) v

/-- The reflection `2P - 1` about an orthogonal projection preserves norms. -/
theorem reflect_norm_two {P : K →L[ℂ] K} (hP : IsOrthogonalProjection P) (v : K) :
    ‖((2 : ℂ) • P - 1) v‖ = ‖v‖ := by
  have h : ((2 : ℂ) • P - 1) v = -(((1 : K →L[ℂ] K) - (2 : ℂ) • P) v) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self]
    abel
  rw [h, norm_neg, reflect_norm hP]

/-- The Grover operator of two orthogonal projections preserves norms. -/
theorem grover_norm {P Q : K →L[ℂ] K} (hP : IsOrthogonalProjection P)
    (hQ : IsOrthogonalProjection Q) (v : K) : ‖ODEGroverPlane.grover P Q v‖ = ‖v‖ := by
  rw [ODEGroverPlane.grover, mul_apply_eq_comp, reflect_norm_two hP, reflect_norm hQ]

/-- **The ray projection is Lipschitz on unit vectors**: on every vector `w`,
`‖P_{φ'} w - P_φ w‖ ≤ 2 ‖φ' - φ‖ ‖w‖`. -/
theorem projector_sub_apply_le {φ φ' : K} (hφ : ‖φ‖ = 1) (hφ' : ‖φ'‖ = 1) (w : K) :
    ‖ODEGroverRay.projector φ' w - ODEGroverRay.projector φ w‖ ≤ 2 * ‖φ' - φ‖ * ‖w‖ := by
  rw [ODEGroverRay.projector_apply, ODEGroverRay.projector_apply]
  have e : inner ℂ φ' w • φ' - inner ℂ φ w • φ =
      inner ℂ φ' w • (φ' - φ) + inner ℂ (φ' - φ) w • φ := by
    rw [inner_sub_left, smul_sub, sub_smul]
    abel
  rw [e]
  calc ‖inner ℂ φ' w • (φ' - φ) + inner ℂ (φ' - φ) w • φ‖
      ≤ ‖inner ℂ φ' w • (φ' - φ)‖ + ‖inner ℂ (φ' - φ) w • φ‖ := norm_add_le _ _
    _ = ‖inner ℂ φ' w‖ * ‖φ' - φ‖ + ‖inner ℂ (φ' - φ) w‖ * ‖φ‖ := by
        rw [norm_smul, norm_smul]
    _ ≤ (‖φ'‖ * ‖w‖) * ‖φ' - φ‖ + (‖φ' - φ‖ * ‖w‖) * ‖φ‖ := by
        gcongr
        · exact norm_inner_le_norm _ _
        · exact norm_inner_le_norm _ _
    _ = 2 * ‖φ' - φ‖ * ‖w‖ := by
        rw [hφ, hφ']
        ring

/-- **The Grover operator of the ray is Lipschitz in the prepared vector**: on every vector `v`,
`‖G_{φ'} v - G_φ v‖ ≤ 4 ‖φ' - φ‖ ‖v‖`, for unit `φ`, `φ'` and an orthogonal projection `Q`. -/
theorem grover_sub_apply_le {Q : K →L[ℂ] K} (hQ : IsOrthogonalProjection Q) {φ φ' : K}
    (hφ : ‖φ‖ = 1) (hφ' : ‖φ'‖ = 1) (v : K) :
    ‖ODEGroverPlane.grover (ODEGroverRay.projector φ') Q v -
        ODEGroverPlane.grover (ODEGroverRay.projector φ) Q v‖ ≤ 4 * ‖φ' - φ‖ * ‖v‖ := by
  set w := ((1 : K →L[ℂ] K) - (2 : ℂ) • Q) v with hw
  have hwn : ‖w‖ = ‖v‖ := reflect_norm hQ v
  have e : ODEGroverPlane.grover (ODEGroverRay.projector φ') Q v -
        ODEGroverPlane.grover (ODEGroverRay.projector φ) Q v =
      (2 : ℂ) • (ODEGroverRay.projector φ' w - ODEGroverRay.projector φ w) := by
    simp only [ODEGroverPlane.grover, mul_apply_eq_comp, sub_apply, smul_apply,
      one_apply_eq_self, hw]
    module
  rw [e, norm_smul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have := projector_sub_apply_le hφ hφ' w
  rw [hwn] at this
  linarith

/-- **Stability of the Grover powers of the actual ray**: for unit `φ`, `φ'` and an orthogonal
projection `Q`, `‖G_{φ'}^j φ' - G_φ^j φ‖ ≤ (4j + 1) ‖φ' - φ‖`. -/
theorem grover_pow_sub_le {Q : K →L[ℂ] K} (hQ : IsOrthogonalProjection Q) {φ φ' : K}
    (hφ : ‖φ‖ = 1) (hφ' : ‖φ'‖ = 1) (j : ℕ) :
    ‖(ODEGroverPlane.grover (ODEGroverRay.projector φ') Q ^ j) φ' -
        (ODEGroverPlane.grover (ODEGroverRay.projector φ) Q ^ j) φ‖ ≤
      (4 * j + 1) * ‖φ' - φ‖ := by
  have hP := ODEGroverRay.projector_isOrthogonalProjection φ hφ
  have hP' := ODEGroverRay.projector_isOrthogonalProjection φ' hφ'
  -- the powers of `G_φ` preserve the norm of `φ`
  have hpow : ∀ i : ℕ, ‖(ODEGroverPlane.grover (ODEGroverRay.projector φ) Q ^ i) φ‖ = 1 := by
    intro i
    induction i with
    | zero => rw [pow_zero, one_apply_eq_self, hφ]
    | succ i ih => rw [pow_succ', mul_apply_eq_comp, grover_norm hP hQ, ih]
  induction j with
  | zero =>
      rw [pow_zero, pow_zero, one_apply_eq_self, one_apply_eq_self]
      simp
  | succ j ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp]
      set a := (ODEGroverPlane.grover (ODEGroverRay.projector φ') Q ^ j) φ'
      set b := (ODEGroverPlane.grover (ODEGroverRay.projector φ) Q ^ j) φ
      have e : ODEGroverPlane.grover (ODEGroverRay.projector φ') Q a -
            ODEGroverPlane.grover (ODEGroverRay.projector φ) Q b =
          ODEGroverPlane.grover (ODEGroverRay.projector φ') Q (a - b) +
            (ODEGroverPlane.grover (ODEGroverRay.projector φ') Q b -
              ODEGroverPlane.grover (ODEGroverRay.projector φ) Q b) := by
        rw [map_sub]
        abel
      rw [e]
      have h1 := grover_norm hP' hQ (a - b)
      have h2 := grover_sub_apply_le hQ hφ hφ' b
      rw [hpow j, mul_one] at h2
      calc ‖ODEGroverPlane.grover (ODEGroverRay.projector φ') Q (a - b) +
            (ODEGroverPlane.grover (ODEGroverRay.projector φ') Q b -
              ODEGroverPlane.grover (ODEGroverRay.projector φ) Q b)‖
          ≤ ‖ODEGroverPlane.grover (ODEGroverRay.projector φ') Q (a - b)‖ +
            ‖ODEGroverPlane.grover (ODEGroverRay.projector φ') Q b -
              ODEGroverPlane.grover (ODEGroverRay.projector φ) Q b‖ := norm_add_le _ _
        _ ≤ (4 * j + 1) * ‖φ' - φ‖ + 4 * ‖φ' - φ‖ := by
            rw [h1]
            exact add_le_add ih h2
        _ = (4 * ((j + 1 : ℕ) : ℝ) + 1) * ‖φ' - φ‖ := by
            push_cast
            ring

end Grover

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Stability of the actual trials in the prepared vector**: for an isometric output `F` and
operators `W`, `W'` with unit prepared vectors `Wψ`, `W'ψ`, the `j`-th actual trials satisfy
`‖trial F W' ψ j - trial F W ψ j‖ ≤ (4j + 1) ‖W'ψ - Wψ‖`. -/
theorem trial_sub_le (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (W W' : K →L[ℂ] K) (ψ : K)
    (hW : ‖W ψ‖ = 1) (hW' : ‖W' ψ‖ = 1) (j : ℕ) :
    ‖trial F W' ψ j - trial F W ψ j‖ ≤ (4 * j + 1) * ‖W' ψ - W ψ‖ := by
  unfold trial actualG
  exact grover_pow_sub_le (ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF) hW hW'
    j

end

end SparseHamiltonian.ODEGroverActual

namespace SparseHamiltonian.GeneralSourceExtensions

noncomputable section
open ContinuousLinearMap OracleCircuit
open ODEStateNormalization (unitDirection unitDirection_norm)
open GeneralSourceODE (SourceCall)
open scoped InnerProduct BigOperators

section PerturbedSeed

variable {P R : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable [FiniteDimensional ℂ P]
variable {L₁ L₂ X₁ X₂ : Type*} {O₁ : L₁ → X₁ → R →L[ℂ] R} {O₂ : L₂ → X₂ → R →L[ℂ] R}

/-- **The perturbed four-attempt protocol, closeness on the seed.** `perturbed_four` with every
trial `q₂ j` at `x₂` within `η ≤ 1/400` of `q₁ j` at `x₁` on the seed `ψ` only (both unitary),
instead of in operator norm: four fresh trials of `q₂` succeed with probability at least `2/3`, and
their conditional output is a density operator within trace distance `6 δ + 12 η` of `|v⟩⟨v|`. -/
theorem perturbed_four_seed (q₁ : ℕ → MultiOracleCircuit.Program O₁)
    (q₂ : ℕ → MultiOracleCircuit.Program O₂) {M : ℕ} (hM : 0 < M) {ψ : R} (hψ : ‖ψ‖ = 1)
    {F : P →L[ℂ] R} (hF : F† ∘L F = 1) (x₁ : X₁) (x₂ : X₂) (v : P) (hv : ‖v‖ = 1)
    {δ η : ℝ} (hδ : 0 ≤ δ) (hη1 : η ≤ 1 / 400)
    (hU₁ : ∀ j, IsUnitary ((q₁ j).eval x₁)) (hU₂ : ∀ j, IsUnitary ((q₂ j).eval x₂))
    (hclose : ∀ j, j < M → ‖(q₂ j).eval x₂ ψ - (q₁ j).eval x₁ ψ‖ ≤ η)
    (hmean : (1 : ℝ) / 4 ≤ (∑ j ∈ Finset.range M,
      ‖ODEHeraldedSuccess.successProjector F ((q₁ j).eval x₁ ψ)‖ ^ 2) / (M : ℝ))
    (hdir : ∀ j, j < M → (F†) ((q₁ j).eval x₁ ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • unitDirection ((F†) ((q₁ j).eval x₁ ψ)) - v‖ ≤ δ) :
    (2 : ℝ) / 3 ≤ (ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).successMass x₂ ∧
    ODEMixedOutput.IsDensity
      ((ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂) ∧
    ∃ h : ((ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂ -
        ODEMixedOutput.pureOperator v).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance
        ((ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂)
        (ODEMixedOutput.pureOperator v) h ≤ 6 * δ + 12 * η := by
  let t₁ := ODERepeatProtocol.ofCircuits q₁ M hM ψ hψ F hF
  let t₂ := ODERepeatProtocol.ofCircuits q₂ M hM ψ hψ F hF
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
    change ‖(F†) ((q₂ j.val).eval x₂ ψ) - (F†) ((q₁ j.val).eval x₁ ψ)‖ ≤ η
    rw [← map_sub]
    exact (norm_adjoint_apply_le F hF _).trans (hclose j.val j.isLt)
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
  have hsucc : (ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).successMass x₂ =
      ODERepeatProbability.successProbability (t₂.probability x₂) :=
    ODERepeatProtocol.Protocol.four_successMass_eq t₂ x₂
  have hdens : (ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF).conditionalDensity x₂ =
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

end PerturbedSeed

section CertificateSeed

variable {P R Y : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **Guarantee of a protocol whose trials are close to certified ones on the seed.** If a counted
two-interface family `q` has the released complete certificate at `x`, and the trials `q₂ j` over
the actual source oracles are within `20 g δ` of `q j` on the seed, with `20 g δ ≤ 1/400` and
`20 g δ ≤ ε/20`, and have the counts of `q` (one `P_w` and one `U_load` call per preparation call,
one `P_w†` call per unpreparation call), then four fresh trials of `q₂` satisfy `ApproxCertificate`
at `x`. This is `approx_certificate` with closeness on the seed in place of the oracle deviation. -/
theorem approx_certificate_seed {L : Type*} {O : (L ⊕ Bool) → Y → R →L[ℂ] R}
    {O₂ : NativeSparseBlockEncoding.Query ⊕ SourceCall → Y → R →L[ℂ] R}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R} {F : P →L[ℂ] R} {x : Y}
    {target : P} {s Θ ell g ε δ : ℝ}
    (hCert : ODECompleteTrial.Certificate q M ψ F x target s Θ ell g ε)
    (q₂ : ℕ → MultiOracleCircuit.Program O₂) (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hO : ∀ l y, IsUnitary (O l y)) (hO₂ : ∀ l y, IsUnitary (O₂ l y))
    (hMatrix : ∀ j, (q₂ j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (hWeight : ∀ j, (q₂ j).cost (GeneralSourceODE.Oracles.calls .weight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hLoad : ∀ j, (q₂ j).cost (GeneralSourceODE.Oracles.calls .load) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hUnweight : ∀ j, (q₂ j).cost (GeneralSourceODE.Oracles.calls .unweight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hSource : ∀ j, (q₂ j).cost GeneralSourceODE.Oracles.sourceCalls =
      2 * (q j).cost (ODESourceQueryBudget.sourceWeight false) +
        (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hclose : ∀ j, j < M → ‖(q₂ j).eval x ψ - (q j).eval x ψ‖ ≤ 20 * g * δ)
    (hδ1 : 20 * g * δ ≤ 1 / 400) (hδε : 20 * g * δ ≤ ε / 20) (hTarget : target ≠ 0) :
    ApproxCertificate (ODERepeatProtocol.fourTrials q₂ M hM ψ hψ F hF) x target s Θ ell g ε := by
  have hTrial := hCert.trial
  have hε : 0 ≤ ε := by
    obtain ⟨_, h⟩ := hCert.conditional_error
    exact (ODEMixedOutput.hermitianTraceDistance_nonneg _ _ _).trans h
  have hU₁ : ∀ j, IsUnitary ((q j).eval x) := fun j => (q j).eval_unitary hO x
  have hU₂ : ∀ j, IsUnitary ((q₂ j).eval x) := fun j => (q₂ j).eval_unitary hO₂ x
  obtain ⟨hS2, hD, hh, htr⟩ := perturbed_four_seed q q₂ hM hψ hF x x (unitDirection target)
    (unitDirection_norm target hTarget) (δ := ε / 500) (by positivity) hδ1 hU₁ hU₂ hclose
    hTrial.mean_success (fun j hj hz => hTrial.direction_error j hj hz)
  refine
    { success_two_thirds := hS2
      matrix_queries := ?_
      weight_calls := ?_
      load_calls := ?_
      unweight_calls := ?_
      source_calls := ?_
      output_density := hD
      conditional_error := ⟨hh, htr.trans (by linarith)⟩ }
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      GeneralSourceODE.Oracles.matrixCalls
      (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
      (fun j hj => by rw [hMatrix j]; exact hTrial.matrix_queries j hj)
    calc
      _ ≤ 4 * (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) := h
      _ = 1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by ring
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      (GeneralSourceODE.Oracles.calls .weight) (10 * g)
      (fun j hj => by rw [hWeight j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      (GeneralSourceODE.Oracles.calls .load) (10 * g)
      (fun j hj => by rw [hLoad j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      (GeneralSourceODE.Oracles.calls .unweight) (10 * g)
      (fun j hj => by rw [hUnweight j]; exact hTrial.source_queries j hj true)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q₂ M hM ψ hψ F hF
      GeneralSourceODE.Oracles.sourceCalls (30 * g) (fun j hj => by
        rw [hSource j]
        push_cast
        have h1 := hTrial.source_queries j hj false
        have h2 := hTrial.source_queries j hj true
        linarith)
    linarith

end CertificateSeed

end

end SparseHamiltonian.GeneralSourceExtensions

namespace SparseHamiltonian.GeneralSourceODE.Compiled

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- **The source-loaded program moves on the public seed by at most the deviation of its
preparation interface on the seed input**, when the unpreparation interfaces agree: every gate
after the preparation call is unitary, and the routed seed is the source embedding of the seed
input. -/
theorem program_seed_dev (p : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (S S' : Bool → X → Branch ι P N →L[ℂ] Branch ι P N) (hS : ∀ b x, IsUnitary (S b x))
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (d : Option (Fin N) × ι → ℂ) (v : P) (x : X)
    (htrue : S true x = S' true x) :
    ‖(program p S' E hE).eval x (ODECompiledSource.seed E d v) -
        (program p S E hE).eval x (ODECompiledSource.seed E d v)‖ ≤
      ‖S' false x (ODEJointLCU.coefficientInput d v) -
        S false x (ODEJointLCU.coefficientInput d v)‖ := by
  have hr : ODESourceTransport.route E (ODECompiledSource.seed E d v) =
      ODESourceTransport.sourceEmbedding (ODEJointLCU.coefficientInput d v) := by
    have h := congrArg
      (fun A : Branch ι P N →L[ℂ] ODESourceTransport.Space (Branch ι P N) K =>
        A (ODEJointLCU.coefficientInput d v)) (ODESourceTransport.route_encoded E hE)
    simp only [comp_apply] at h
    exact h
  have hs : ∀ (T : Branch ι P N →L[ℂ] Branch ι P N) (w : Branch ι P N),
      ODESourceTransport.sourceGate (K := K) T (ODESourceTransport.sourceEmbedding w) =
        ODESourceTransport.sourceEmbedding (T w) := fun T w =>
    congrArg (fun A : Branch ι P N →L[ℂ] ODESourceTransport.Space (Branch ι P N) K => A w)
      (ODESourceTransport.sourceGate_source T)
  -- The common gates after the preparation call.
  set A : ODESourceTransport.Space (Branch ι P N) K →L[ℂ]
      ODESourceTransport.Space (Branch ι P N) K :=
    ODESourceTransport.route E * ODESourceTransport.sourceGate (S true x) *
      ODESourceTransport.route E * (ODESourceTransport.matrixProgram (B := Branch ι P N) p).eval x *
      ODESourceTransport.route E with hA
  have hAU : IsUnitary A := by
    have hR := ODESourceTransport.route_unitary E hE
    have hG := ODESourceTransport.sourceGate_unitary (K := K) (S true x) (hS true x)
    have hMx : IsUnitary ((ODESourceTransport.matrixProgram (B := Branch ι P N) p).eval x) := by
      rw [ODESourceTransport.matrixProgram_eval_eq]
      exact ODESourceTransport.matrixGate_unitary _ (p.eval_unitary hO x)
    exact (((hR.mul hG).mul hR).mul hMx).mul hR
  have hU : ∀ T : Bool → X → Branch ι P N →L[ℂ] Branch ι P N, T true x = S true x →
      (program p T E hE).eval x (ODECompiledSource.seed E d v) =
        A (ODESourceTransport.sourceEmbedding (T false x (ODEJointLCU.coefficientInput d v))) := by
    intro T hT
    rw [program_eval, hT]
    simp only [mul_apply_eq_comp, hr, hs, hA]
  rw [hU S' htrue.symm, hU S rfl, ← map_sub, ← map_sub, ODEGroverActual.norm_map_of_isUnitary hAU]
  exact le_of_eq ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
    ODESourceTransport.sourceEmbedding_isometry _)

end

end SparseHamiltonian.GeneralSourceODE.Compiled

namespace SparseHamiltonian.GeneralSourceExtensions.MeshNative

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open GeneralSourceODE
open GeneralSourceODE.Native (Label SourceBasis SourceSpace sourceLayout sourceBasis dummy
  sourceFamily)
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- **The compiled public trials move on the seed by at most `(4j + 1)` times the deviation of
the preparation interface on the seed input**, when the unpreparation interfaces agree: the
trial is the actual Grover power of the source-loaded program (`trial_sub_le`), compiled
isometrically (`compile_eval`), and the program moves on the seed by at most that deviation
(`program_seed_dev`). -/
theorem publicTrialsS_seed_dev (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m N d : ℕ) (p : MultiOracleCircuit.Program (matrixOracle (ι := ι) D m N d))
    (S S' : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
    (hS : ∀ b x, IsUnitary (S b x)) (hS' : ∀ b x, IsUnitary (S' b x))
    (E : SourceSpace ι n m →L[ℂ] MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (x : X)
    (htrue : S true x = S' true x) (j : ℕ) :
    ‖(publicTrialsS D hM i0 m N d p S' E hE c seed hSeed hOutput j).eval x
        (input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) -
      (publicTrialsS D hM i0 m N d p S E hE c seed hSeed hOutput j).eval x
        (input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed))‖ ≤
      (4 * j + 1) *
        ‖S' false x (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) -
          S false x (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)‖ := by
  have key : ∀ (T : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
      (_hT : ∀ b x, IsUnitary (T b x)),
      (publicTrialsS D hM i0 m N d p T E hE c seed hSeed hOutput j).eval x ∘L input D hM i0 m N d =
        input D hM i0 m N d ∘L
          (ODECountedAmplification.program (Compiled.program p T E hE)
            (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j).eval x := by
    intro T hT
    exact ODECoordinateNativeControl.compile_eval
      (A := SourceBasis ι n m) (B := MatrixBasis ι n Z m M N d)
      (H := SourceSpace ι n m) (K := MatrixSpace ι n Z m M N d) (X := X) (L := Query)
      (sourceLayout (ι := ι) (n := n) m)
      (matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)
      (matrixOracle (ι := ι) D m N d) T (matrixOracle_unitary (ι := ι) D m N d) hT
      (sourceBasis D i0 m) (matrixBasis D hM i0 m N d) (matrixImage D hM i0 m N d)
      (matrix_valid D hM i0 m N d)
      (ODECountedAmplification.program (Compiled.program p T E hE)
        (ODECompiledSource.output E (Compiled.seedCoefficients c)) hOutput
        (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) hSeed j) x
  have key' : ∀ (T : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
      (_hT : ∀ b x, IsUnitary (T b x)),
      (publicTrialsS D hM i0 m N d p T E hE c seed hSeed hOutput j).eval x
          (input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) =
        input D hM i0 m N d
          (ODEGroverActual.trial (ODECompiledSource.output E (Compiled.seedCoefficients c))
            ((Compiled.program p T E hE).eval x)
            (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed) j) := by
    intro T hT
    rw [← comp_apply, key T hT, comp_apply,
      ODECountedAmplification.state_eq _ _ hOutput _ hSeed j x
        (Compiled.program_unitary p (matrixOracle_unitary (ι := ι) D m N d) T hT E hE x)]
  rw [key' S' hS', key' S hS, ← map_sub,
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr (input_isometry D hM i0 m N d)]
  have hU : ∀ (T : Bool → X → SourceSpace ι n m →L[ℂ] SourceSpace ι n m)
      (_hT : ∀ b x, IsUnitary (T b x)),
      ‖(Compiled.program p T E hE).eval x
        (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)‖ = 1 := by
    intro T hT
    rw [ODEGroverActual.norm_map_of_isUnitary
      (Compiled.program_unitary p (matrixOracle_unitary (ι := ι) D m N d) T hT E hE x), hSeed]
  refine (ODEGroverActual.trial_sub_le _ hOutput _ _ _ (hU S hS) (hU S' hS') j).trans ?_
  gcongr
  exact Compiled.program_seed_dev p (matrixOracle_unitary (ι := ι) D m N d) S S' hS E hE _ seed x
    htrue

end

end SparseHamiltonian.GeneralSourceExtensions.MeshNative

namespace SparseHamiltonian.GeneralSourceExtensions.MeshOracles

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open GeneralSourceODE
open GeneralSourceODE.Oracles (sourcePhysical_mul matrixCalls calls sourceCalls)
open ODEStateNormalization (unitDirection unitDirection_norm)
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Approximate-completion stability of the clean-column loader.** If the public trial family
with the label-controlled interfaces `loader J` has the released complete certificate, then the
four-attempt protocol over the actual oracles `P_w`, `Lo`, `P_w†` satisfies `ApproxCertificate`
for every unitary `Lo` within `δ` of `loader J` on the seed branch state after `P_w`, with
`20 g δ ≤ 1/400` and `20 g δ ≤ ε/20`. `Lo` is not assumed to be close to `loader J` on any other
vector. The `j`-th trials move on the seed by at most `(4j + 1) δ ≤ 20 g δ`
(`MeshNative.publicTrialsS_seed_dev`), and the four-attempt protocol uses its trials only on the
seed (`perturbed_four_seed`). -/
theorem columns_approx_certificate (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι)
    (m N d : ℕ) (p : MultiOracleCircuit.Program (MeshNative.matrixOracle (ι := ι) D m N d))
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Native.SourceSpace ι n m →L[ℂ] MeshNative.MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1)
    (x : X) {Mc : ℕ} (hMc : 0 < Mc) {target : EuclideanSpace ℂ n} {s' Θ ell g ε δ : ℝ}
    (hψ : ‖MeshNative.input D hM i0 m N d
      (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)‖ = 1)
    (hF : (MeshNative.input D hM i0 m N d ∘L
        ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      (MeshNative.input D hM i0 m N d ∘L
        ODECompiledSource.output E (Compiled.seedCoefficients c)) = 1)
    (hCert : ODECompleteTrial.Certificate
      (MeshNative.publicTrials D hM i0 m N d p Pw J φ E hE c seed hSeed hOutput) Mc
      (MeshNative.input D hM i0 m N d (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed))
      (MeshNative.input D hM i0 m N d ∘L ODECompiledSource.output E (Compiled.seedCoefficients c))
      x target s' Θ ell g ε)
    (hdev : ‖Lo x (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)) -
      Weights.loader (J x) (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed))‖ ≤ δ)
    (hδ1 : 20 * g * δ ≤ 1 / 400) (hδε : 20 * g * δ ≤ ε / 20) (hTarget : target ≠ 0) :
    ApproxCertificate (ODERepeatProtocol.fourTrials (actualTrialsL D m N d Pw Lo φ hφ
        (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed
          hSeed hOutput)) Mc hMc _ hψ _ hF) x target s' Θ ell g ε := by
  rw [MeshNative.publicTrials_eq_publicTrialsS] at hCert
  have hTrial := hCert.trial
  -- The preparation interfaces differ on the seed input by the loader deviation.
  have hprep : ‖Compiled.sourceFamilyL (ι := ι) Pw Lo φ false x
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) -
      Native.sourceFamily (ι := ι) Pw J φ false x
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)‖ ≤ δ := by
    rw [Compiled.sourceFamilyL_false, Native.sourceFamily, Compiled.sourceFamily_false]
    unfold Compiled.prepL Compiled.prep
    simp only [comp_apply]
    rw [← map_sub, ODEGroverActual.norm_map_of_isUnitary (Weights.phaseGate_unitary φ hφ)]
    exact hdev
  have hO₁ : ∀ l y, IsUnitary (MeshNative.physicalOracleS (ι := ι) D m N d
      (Native.sourceFamily Pw J φ) l y) :=
    ODECoordinateNativeControl.physicalOracle_unitary _ _ _ _
      (MeshNative.matrixOracle_unitary (ι := ι) D m N d) (Compiled.sourceFamily_unitary hPw hJ hφ)
  apply approx_certificate_seed hCert _ hMc hψ hF hO₁
    (actualOracleL_unitary (ι := ι) D m N d hPw hLo)
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute,
      implementationL_matrix, MeshNative.publicTrialsS_matrix_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute,
      implementationL_weight, MeshNative.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute,
      implementationL_load, MeshNative.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute,
      implementationL_unweight, MeshNative.publicTrialsS_source_cost]
  · intro j
    simp only [actualTrialsL, MultiOracleCircuit.Program.cost_substitute]
    rw [funext (implementationL_source D m N d Pw Lo φ hφ), Oracles.cost_add,
      NativeHermitianDilation.cost_scale]
    simp only [MeshNative.publicTrialsS_source_cost]
  · -- Every trial moves on the seed by at most `20 g δ`.
    intro j hj
    have hEval₂ : (actualTrialsL D m N d Pw Lo φ hφ
        (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed
          hSeed hOutput) j).eval x =
        (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed
          hSeed hOutput j).eval x :=
      MultiOracleCircuit.Program.eval_substitute _ _ (implementationL_eval D m N d Pw Lo φ hφ) x
    rw [hEval₂]
    have h := MeshNative.publicTrialsS_seed_dev D hM i0 m N d p (Native.sourceFamily Pw J φ)
      (Compiled.sourceFamilyL Pw Lo φ) (Compiled.sourceFamily_unitary hPw hJ hφ)
      (Compiled.sourceFamilyL_unitary hPw hLo hφ) E hE c seed hSeed hOutput x
      ((Compiled.sourceFamily_true Pw J φ x).trans (Compiled.sourceFamilyL_true Pw Lo φ x).symm) j
    have hcount := hTrial.source_queries j hj false
    rw [MeshNative.publicTrialsS_source_cost] at hcount
    push_cast at hcount
    have hj4 : (4 * (j : ℝ) + 1) ≤ 20 * g := by linarith
    have hb : (4 * (j : ℝ) + 1) * ‖Compiled.sourceFamilyL (ι := ι) Pw Lo φ false x
          (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) -
        Native.sourceFamily (ι := ι) Pw J φ false x
          (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)‖ ≤ 20 * g * δ := by
      calc _ ≤ (20 * g) * δ := mul_le_mul hj4 hprep (norm_nonneg _) (by linarith)
        _ = 20 * g * δ := by ring
    refine le_trans ?_ hb
    convert h using 2
  · exact hδ1
  · exact hδε
  · exact hTarget
end

end SparseHamiltonian.GeneralSourceExtensions.MeshOracles
