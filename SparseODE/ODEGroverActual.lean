import SparseODE.ODEGroverProgram

/-!
# Randomized amplification of the actual heralded ODE output

The projection and ray below come from the actual implemented preparation.
Every Grover power preserves its successful public direction up to one global
phase. The angle is used only in the proof, while the cutoff uses the known
bound g. Physical oracle-program implementation and costs are separate.

-/

namespace SparseHamiltonian.ODEGroverActual

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct BigOperators

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The actual initial successful amplitude. -/
def amplitude (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) : ℝ :=
  ‖ODEHeraldedSuccess.successProjector F (W ψ)‖

/-- The actual Grover operator; the prepared-ray reflection is subsequently
implemented by preparation, a fixed seed reflection, and inverse preparation. -/
def actualG (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) : K →L[ℂ] K :=
  ODEGroverPlane.grover (ODEGroverRay.projector (W ψ))
    (ODEHeraldedSuccess.successProjector F)

def trial (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) (j : ℕ) : K :=
  (actualG F W ψ ^ j) (W ψ)

def decoded (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) (j : ℕ) : P :=
  (F†) (trial F W ψ j)

def probability (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) (j : ℕ) : ℝ :=
  ‖ODEHeraldedSuccess.successProjector F (trial F W ψ j)‖ ^ 2

/-- A uniform classical choice of a trial count in `range M`. -/
def meanProbability (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) (M : ℕ) : ℝ :=
  (∑ j ∈ Finset.range M, probability F W ψ j) / (M : ℝ)

/-- Neither coordinate denominator vanishes in the promised amplitude range. -/
theorem angle_geometry (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    Real.sin (Real.arcsin a) = a ∧ 0 < Real.cos (Real.arcsin a) := by
  have hs : Real.sin (Real.arcsin a) = a :=
    Real.sin_arcsin (by linarith) (by linarith)
  refine ⟨hs, ?_⟩
  have hcircle := Real.sin_sq_add_cos_sq (Real.arcsin a)
  rw [hs] at hcircle
  have haSq : a ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    (sq_le_sq₀ ha0 (by norm_num)).mpr ha1
  by_contra hn
  have hc : Real.cos (Real.arcsin a) ≤ 0 := le_of_not_gt hn
  have hc0 := Real.cos_arcsin_nonneg a
  have hcEq : Real.cos (Real.arcsin a) = 0 := le_antisymm hc hc0
  rw [hcEq] at hcircle
  nlinarith

/-- The exact physical good component of each actual Grover trial. -/
theorem trial_projected (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < amplitude F W ψ) (ha1 : amplitude F W ψ ≤ 1 / 2) (j : ℕ) :
    ODEHeraldedSuccess.successProjector F (trial F W ψ j) =
      ((Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (amplitude F W ψ)) /
        amplitude F W ψ : ℝ) : ℂ) •
          ODEHeraldedSuccess.successProjector F (W ψ) := by
  have hUnit : ‖W ψ‖ = 1 := by
    rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hψ]
  have hQ := ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF
  obtain ⟨hs, hc⟩ := angle_geometry (amplitude F W ψ) ha0.le ha1
  have hs0 : Real.sin (Real.arcsin (amplitude F W ψ)) ≠ 0 := by
    rw [hs]
    exact ha0.ne'
  have hCompression :
      ODEGroverRay.projector (W ψ) (ODEHeraldedSuccess.successProjector F (W ψ)) =
        (Real.sin (Real.arcsin (amplitude F W ψ)) : ℂ) ^ 2 • W ψ := by
    rw [hs]
    exact ODEGroverRay.projector_good (W ψ)
      (ODEHeraldedSuccess.successProjector F) hQ
  simpa only [trial, actualG, hs] using
    ODEGroverPlane.projected_power (ODEGroverRay.projector (W ψ))
      (ODEHeraldedSuccess.successProjector F) hQ (W ψ)
      (Real.arcsin (amplitude F W ψ)) hs0 hc.ne'
      (ODEGroverRay.projector_self (W ψ) hUnit) hCompression j

/-- The previously proved finite sine-squared average applies to physical
herald probabilities, rather than to a stipulated ideal rotation. -/
theorem trial_probability (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < amplitude F W ψ) (ha1 : amplitude F W ψ ≤ 1 / 2) (j : ℕ) :
    probability F W ψ j =
      ODEGroverAverage.successProbability (Real.arcsin (amplitude F W ψ)) j := by
  have hNorm : ‖ODEHeraldedSuccess.successProjector F (trial F W ψ j)‖ =
      |Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (amplitude F W ψ))| := by
    rw [trial_projected F hF W hW ψ hψ ha0 ha1 j,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ha0]
    change |Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (amplitude F W ψ))| /
      amplitude F W ψ * amplitude F W ψ = _
    exact div_mul_cancel₀ _ ha0.ne'
  unfold probability ODEGroverAverage.successProbability
  rw [hNorm, sq_abs]

/-- Failed components can change; the decoded successful component is exactly
a real multiple of the original actual decoded output. -/
theorem decoded_multiple (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < amplitude F W ψ) (ha1 : amplitude F W ψ ≤ 1 / 2) (j : ℕ) :
    decoded F W ψ j =
      ((Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (amplitude F W ψ)) /
        amplitude F W ψ : ℝ) : ℂ) • (F†) (W ψ) := by
  exact ODEGroverDirection.decode_real_multiple F hF (W ψ) (trial F W ψ j)
    (Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (amplitude F W ψ)) /
      amplitude F W ψ) (trial_projected F hF W hW ψ hψ ha0 ha1 j)

/-- One public cutoff gives constant success probability. Every nonzero
heralded trial keeps the original error, up to a global phase, with no
iteration-count factor and no additional precision requirement. -/
theorem randomized_certificate (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (g : ℝ) (hg : 1 ≤ g)
    (haLower : 1 / (4 * g) ≤ amplitude F W ψ)
    (haUpper : amplitude F W ψ ≤ 1 / 2)
    (target : P) (η : ℝ)
    (hError : ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ ≤ η) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ meanProbability F W ψ (ODEGroverAverage.chosenIterations g) ∧
    ∀ j : ℕ, decoded F W ψ j ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection (decoded F W ψ j) - unitDirection target‖ ≤ η := by
  have hden : 0 < 4 * g := by linarith
  have ha0 : 0 < amplitude F W ψ :=
    lt_of_lt_of_le (one_div_pos.mpr hden) haLower
  have hMean (M : ℕ) : meanProbability F W ψ M =
      ODEGroverAverage.meanSuccess (Real.arcsin (amplitude F W ψ)) M := by
    unfold meanProbability ODEGroverAverage.meanSuccess
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact trial_probability F hF W hW ψ hψ ha0 haUpper j
  obtain ⟨hM, hBound, hSuccess⟩ :=
    ODEGroverAverage.promised_amplitude g (amplitude F W ψ) hg haLower haUpper
  refine ⟨hM, hBound, ?_, ?_⟩
  · rw [hMean]
    exact hSuccess
  · intro j hj
    exact ODEGroverDirection.direction_error_of_real_multiple
      ((F†) (W ψ)) (decoded F W ψ j) target
      (Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (amplitude F W ψ)) /
        amplitude F W ψ) η
      (decoded_multiple F hF W hW ψ hψ ha0 haUpper j) hj hError

end
end SparseHamiltonian.ODEGroverActual
