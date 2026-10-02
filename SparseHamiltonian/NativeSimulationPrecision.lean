import SparseHamiltonian.NativeMultiProgramClock

/-!
# Time-weighted precision transfer for actual native simulation programs

Band precision is naturally scheduled to bound its evolution contribution
`|t| * δbands`, not a stronger standalone generator tolerance. These lemmas
combine that allowance with independent rounding and simulation errors while
retaining the identical physical program and every query count.
-/

namespace SparseHamiltonian.NativeSimulationPrecision

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

section OutputDistance
variable {P K : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Direct complete-output transfer from any bound on the distance between two
logical evolutions. No generator approximation or commutation is required. -/
theorem output_error_of_distance (S F : P →L[ℂ] K) (U V : P →L[ℂ] P)
    (εsim εdistance : ℝ) (hF : ‖F‖ ≤ 1)
    (hSim : ‖S - F ∘L V‖ ≤ εsim) (hDistance : ‖V - U‖ ≤ εdistance) :
    ‖S - F ∘L U‖ ≤ εsim + εdistance := by
  have hOutput : ‖F ∘L V - F ∘L U‖ ≤ εdistance := by
    rw [← comp_sub]
    exact ((opNorm_comp_le F (V - U)).trans
      (mul_le_mul_of_nonneg_right hF (norm_nonneg _))).trans
        (by simpa using hDistance)
  exact (norm_sub_le_norm_sub_add_norm_sub S (F ∘L V) (F ∘L U)).trans
    (add_le_add hSim hOutput)

end OutputDistance

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {X Label : Type*}

/-- Half-error simulation and two independent quarter-error perturbations give
the requested full-output accuracy. Only the actual time-weighted perturbation
allowances are required, covering zero time without division by time. -/
theorem time_weighted_program_error {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (input output : P →L[ℂ] K)
    (H Hrounded G : X → P →L[ℂ] P) (t α ε δround δbands : ℝ)
    (hOut : output† ∘L output = 1)
    (hH : ∀ x, star (H x) = H x) (hG : ∀ x, star (G x) = G x)
    (hSim : ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * ((t * α : ℝ) : ℂ)) • G x)‖ ≤ ε / 2)
    (hRound : ∀ x, ‖Hrounded x - H x‖ ≤ δround)
    (hBands : ∀ x, ‖(α : ℂ) • G x - Hrounded x‖ ≤ δbands)
    (hRoundTime : |t| * δround ≤ ε / 4)
    (hBandsTime : |t| * δbands ≤ ε / 4) :
    ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ ε := by
  intro x
  have h := LabeledSimulationTransfer.rescaled_program_error p input output H G
    t α (ε / 2) (δround + δbands) hOut hH hG hSim
    (fun x => LabeledSimulationTransfer.combined_generator_error
      _ _ _ _ _ (hRound x) (hBands x)) x
  apply h.trans
  rw [mul_add]
  linarith

/-- Direct evolution-distance transfer for the very same counted native program.
This applies equally to rounding, band approximation, or a sum of such errors. -/
theorem program_error_of_evolution_distance {F : Label → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program F) (input output : P →L[ℂ] K)
    (H G : X → P →L[ℂ] P) (t εsim εdistance : ℝ)
    (hOut : output† ∘L output = 1)
    (hSim : ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • G x)‖ ≤ εsim)
    (hDistance : ∀ x,
      ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • G x) -
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ εdistance) :
    ∀ x, ‖p.eval x ∘L input - output ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • H x)‖ ≤ εsim + εdistance := by
  intro x
  exact output_error_of_distance (p.eval x ∘L input) output _ _ εsim εdistance
    (LabeledSimulationTransfer.isometry_norm_le_one output hOut) (hSim x) (hDistance x)

end
end SparseHamiltonian.NativeSimulationPrecision
