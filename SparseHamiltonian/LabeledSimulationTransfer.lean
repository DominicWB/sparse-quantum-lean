import SparseHamiltonian.LabeledActiveClockQuery

/-!
# Rescaling and perturbing actual native simulation programs

These results transfer a full-output certificate for the normalized weighted
clock Hamiltonian to the original unnormalized target. The physical program,
its fixed input and output encodings, and every named query count are retained.
Independent rounding and band-encoding errors receive explicit public budgets.
-/
namespace SparseHamiltonian.LabeledSimulationTransfer

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct
set_option maxHeartbeats 800000

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X Label : Type*}

omit [CompleteSpace P] in
/-- Time rescaling is an exact identity, with no approximation or query cost. -/
theorem evolution_rescale (H : P →L[ℂ] P) (t α : ℝ) :
    NormedSpace.exp ((-Complex.I * ((t * α : ℝ) : ℂ)) • H) =
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • ((α : ℂ) • H)) := by
  congr 1
  rw [smul_smul, Complex.ofReal_mul, mul_assoc]

/-- An isometric output preparation is a contraction, including a zero public
space. Thus the statement does not require a nontriviality hypothesis. -/
theorem isometry_norm_le_one (E : P →L[ℂ] K) (hE : E† ∘L E = 1) : ‖E‖ ≤ 1 := by
  apply E.opNorm_le_bound zero_le_one
  intro v
  rw [E.norm_map_iff_adjoint_comp_self.mpr hE, one_mul]

/-- A real rescaling preserves the self-adjoint generator property. -/
theorem real_smul_self_adjoint (H : P →L[ℂ] P) (α : ℝ) (hH : star H = H) :
    star ((α : ℂ) • H) = (α : ℂ) • H := by
  simp only [star_smul, hH, Complex.star_def, Complex.conj_ofReal]

/-- The same actual native program simulates the unnormalized target, losing
only the sharp time-times-generator-error term. -/
theorem rescaled_program_error {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (input output : P →L[ℂ] K)
    (H G : X → P →L[ℂ] P) (t α ε δ : ℝ)
    (hOut : output† ∘L output = 1)
    (hH : ∀ x, star (H x) = H x) (hG : ∀ x, star (G x) = G x)
    (hSim : ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * ((t * α : ℝ) : ℂ)) • G x)‖ ≤ ε)
    (hApprox : ∀ x, ‖(α : ℂ) • G x - H x‖ ≤ δ) :
    ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ ε + |t| * δ := by
  intro x
  apply HamiltonianStability.output_error_le (p.eval x ∘L input) output
    (H x) ((α : ℂ) • G x) t ε δ (isometry_norm_le_one output hOut)
    (hH x) (real_smul_self_adjoint (G x) α (hG x))
  · simpa only [evolution_rescale] using hSim x
  · exact hApprox x

omit [CompleteSpace P] in
/-- The two preprocessing errors add in operator norm; no commutation between
rounding, magnitude bands, or the target Hamiltonian is assumed. -/
theorem combined_generator_error (H Hrounded Hbands : P →L[ℂ] P)
    (δround δbands : ℝ) (hRound : ‖Hrounded - H‖ ≤ δround)
    (hBands : ‖Hbands - Hrounded‖ ≤ δbands) :
    ‖Hbands - H‖ ≤ δround + δbands := by
  exact (norm_sub_le_norm_sub_add_norm_sub Hbands Hrounded H).trans
    (by linarith)

/-- Public allocation to each of the two independent Hamiltonian errors. -/
def generatorTolerance (t ε : ℝ) : ℝ := ε / (4 * (1 + |t|))

theorem generatorTolerance_pos (t ε : ℝ) (hε : 0 < ε) :
    0 < generatorTolerance t ε := by
  unfold generatorTolerance
  positivity

/-- Half of the requested output error remains available to the clock circuit. -/
theorem split_error_le (t ε : ℝ) (hε : 0 ≤ ε) :
    ε / 2 + |t| * (generatorTolerance t ε + generatorTolerance t ε) ≤ ε := by
  have hd : 0 < 4 * (1 + |t|) := by positivity
  have hdiv : generatorTolerance t ε * (4 * (1 + |t|)) = ε := by
    exact div_mul_cancel₀ ε (ne_of_gt hd)
  have htol := div_nonneg hε (le_of_lt hd)
  change 0 ≤ generatorTolerance t ε at htol
  nlinarith

/-- The public error split preserves the same native program and achieves the
requested final full-output accuracy after both preprocessing stages. -/
theorem two_stage_program_error {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (input output : P →L[ℂ] K)
    (H Hrounded G : X → P →L[ℂ] P) (t α ε : ℝ) (hε : 0 ≤ ε)
    (hOut : output† ∘L output = 1)
    (hH : ∀ x, star (H x) = H x) (hG : ∀ x, star (G x) = G x)
    (hSim : ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * ((t * α : ℝ) : ℂ)) • G x)‖ ≤ ε / 2)
    (hRound : ∀ x, ‖Hrounded x - H x‖ ≤ generatorTolerance t ε)
    (hBands : ∀ x, ‖(α : ℂ) • G x - Hrounded x‖ ≤ generatorTolerance t ε) :
    ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ ε := by
  intro x
  exact (rescaled_program_error p input output H G t α (ε / 2)
    (generatorTolerance t ε + generatorTolerance t ε) hOut hH hG hSim
    (fun x => combined_generator_error _ _ _ _ _ (hRound x) (hBands x)) x).trans
      (split_error_le t ε hε)

omit [CompleteSpace P] in
/-- Summing independently certified band errors costs their sum, including
zero-weight bands and an exact tail band. -/
theorem sum_band_error {ι : Type*} [Fintype ι]
    (H B : ι → P →L[ℂ] P) (δ : ι → ℝ) (h : ∀ i, ‖B i - H i‖ ≤ δ i) :
    ‖(∑ i, B i) - ∑ i, H i‖ ≤ ∑ i, δ i := by
  rw [← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => h i)

omit [CompleteSpace P] in
/-- Normalized positive band weights recover the unnormalized sum exactly. -/
theorem weighted_generator_rescale {ι : Type*} [Fintype ι]
    (α : ι → ℝ) (G : ι → P →L[ℂ] P) (hTotal : (∑ i, α i) ≠ 0) :
    ((∑ i, α i : ℝ) : ℂ) • (∑ i, ((α i / ∑ j, α j : ℝ) : ℂ) • G i) =
      ∑ i, (α i : ℂ) • G i := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, ← Complex.ofReal_mul]
  congr 2
  exact mul_div_cancel₀ (α i) hTotal

end
end SparseHamiltonian.LabeledSimulationTransfer
