import SparseHamiltonian.ODEQueryBudget

/-!
# Counted coherent LCHS composition

The common-schedule compiler and the complex LCU preparations compose to a
single counted circuit. Its successful block has the LCHS error budget with
no factor for the number of quadrature nodes. The LCHS approximation and the
branch simulation estimates are explicit premises: this module does not yet
construct the Gaussian quadrature or a common schedule for the sparse
Hamiltonian simulator.
-/

namespace SparseHamiltonian.ODEControlledLCU

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

variable {ι L X P K : Type*} [Fintype ι]
variable [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A fixed isometric output encoding is a contraction, including on a trivial
public Hilbert space. -/
theorem isometry_norm_le_one (E : P →L[ℂ] K) (hE : E† ∘L E = 1) : ‖E‖ ≤ 1 := by
  apply opNorm_le_bound _ (by norm_num)
  intro v
  rw [E.norm_map_iff_adjoint_comp_self.mpr hE, one_mul]

/-- A full-output branch error also bounds its successful public block. -/
theorem branch_compression_error (V : K →L[ℂ] K) (J F : P →L[ℂ] K)
    (U : P →L[ℂ] P) (δ : ℝ) (hF : F† ∘L F = 1)
    (hError : ‖V ∘L J - F ∘L U‖ ≤ δ) :
    ‖F† ∘L V ∘L J - U‖ ≤ δ := by
  have hEq : F† ∘L V ∘L J - U = F† ∘L (V ∘L J - F ∘L U) := by
    rw [comp_sub]
    simp only [← comp_assoc, hF, one_def, id_comp]
  rw [hEq]
  calc
    _ ≤ ‖F†‖ * ‖V ∘L J - F ∘L U‖ := opNorm_comp_le _ _
    _ ≤ 1 * ‖V ∘L J - F ∘L U‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [adjoint.norm_map]
      exact isometry_norm_le_one F hF
    _ ≤ δ := by simpa only [one_mul] using hError

/-- Exact block of the actual coherently compiled program. -/
theorem compiled_compression (O : L → X → K →L[ℂ] K)
    (p : CoherentQuerySchedule.Schedule ι L K) (c : ι → ℂ)
    (J F : ι → P →L[ℂ] K) (x : X) :
    (ODECoherentLCU.outputEmbedding c F)† ∘L
      (p.compile O).eval x ∘L ODECoherentLCU.inputEmbedding c J =
      (ODECoherentLCU.coefficientMass c : ℂ)⁻¹ •
        ∑ i, c i • ((F i)† ∘L (p.branch O i).eval x ∘L J i) := by
  rw [CoherentQuerySchedule.Schedule.compile_eval]
  exact ODECoherentLCU.successful_compression c _ J F

/-- Undoing the known scalar normalization exposes the actual LCHS sum. -/
theorem scaled_compiled_compression (O : L → X → K →L[ℂ] K)
    (p : CoherentQuerySchedule.Schedule ι L K) (c : ι → ℂ)
    (hc : 0 < ODECoherentLCU.coefficientMass c)
    (J F : ι → P →L[ℂ] K) (x : X) :
    (ODECoherentLCU.coefficientMass c : ℂ) •
      ((ODECoherentLCU.outputEmbedding c F)† ∘L
        (p.compile O).eval x ∘L ODECoherentLCU.inputEmbedding c J) =
      ∑ i, c i • ((F i)† ∘L (p.branch O i).eval x ∘L J i) := by
  rw [compiled_compression, smul_smul]
  have hne : (ODECoherentLCU.coefficientMass c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [mul_inv_cancel₀ hne, one_smul]

/-- Analytic LCHS and full-output branch errors compose for the counted program.
This is conditional on the displayed approximation and common-schedule proofs. -/
theorem compiled_lchs_error (O : L → X → K →L[ℂ] K)
    (p : CoherentQuerySchedule.Schedule ι L K) (c : ι → ℂ)
    (hc : 0 < ODECoherentLCU.coefficientMass c)
    (J F : ι → P →L[ℂ] K) (hF : ∀ i, (F i)† ∘L F i = 1)
    (U : ι → P →L[ℂ] P) (S : P →L[ℂ] P) (x : X) (ν δ : ℝ)
    (hδ : 0 ≤ δ) (hLCHS : ‖(∑ i, c i • U i) - S‖ ≤ ν)
    (hSimulation : ∀ i, ‖(p.branch O i).eval x ∘L J i - F i ∘L U i‖ ≤ δ) :
    ‖(ODECoherentLCU.coefficientMass c : ℂ) •
      ((ODECoherentLCU.outputEmbedding c F)† ∘L
        (p.compile O).eval x ∘L ODECoherentLCU.inputEmbedding c J) - S‖ ≤
      ν + ODECoherentLCU.coefficientMass c * δ := by
  rw [scaled_compiled_compression O p c hc J F x]
  exact ODEErrorBudget.lchs_simulation_error_le c U _ S
    (ODECoherentLCU.coefficientMass c) ν δ hδ le_rfl hLCHS
    (fun i => branch_compression_error _ _ _ _ _ (hF i) (hSimulation i))

/-- One actual program, fixed clean isometries, exact query count, and a uniform
successful-block error certificate. The number of LCHS nodes never multiplies
the count. Constructing the schedule and the LCHS approximation remains a
separate mathematical task. -/
theorem controlled_lchs_certificate (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x))
    (p : CoherentQuerySchedule.Schedule ι L K) (c : ι → ℂ)
    (hc : 0 < ODECoherentLCU.coefficientMass c)
    (J F : ι → P →L[ℂ] K)
    (hJ : ∀ i, (J i)† ∘L J i = 1) (hF : ∀ i, (F i)† ∘L F i = 1)
    (U : ι → X → P →L[ℂ] P) (S : X → P →L[ℂ] P) (ν δ : ℝ)
    (hδ : 0 ≤ δ) (hLCHS : ∀ x, ‖(∑ i, c i • U i x) - S x‖ ≤ ν)
    (hSimulation : ∀ i x,
      ‖(p.branch O i).eval x ∘L J i - F i ∘L U i x‖ ≤ δ) :
    ∃ q : MultiOracleCircuit.Program (CoherentQuerySchedule.oracle (ι := ι) O),
      q.count = p.count ∧
      (ODECoherentLCU.inputEmbedding c J)† ∘L ODECoherentLCU.inputEmbedding c J = 1 ∧
      (ODECoherentLCU.outputEmbedding c F)† ∘L ODECoherentLCU.outputEmbedding c F = 1 ∧
      ∀ x, IsUnitary (q.eval x) ∧
        ‖(ODECoherentLCU.coefficientMass c : ℂ) •
          ((ODECoherentLCU.outputEmbedding c F)† ∘L
            q.eval x ∘L ODECoherentLCU.inputEmbedding c J) - S x‖ ≤
          ν + ODECoherentLCU.coefficientMass c * δ := by
  refine ⟨p.compile O, p.compile_count O,
    ODECoherentLCU.inputEmbedding_isometry c hc J hJ,
    ODECoherentLCU.outputEmbedding_isometry c hc F hF, ?_⟩
  intro x
  refine ⟨(p.compile O).eval_unitary
    (fun l y => CoherentQuerySchedule.oracle_unitary O hO l y) x, ?_⟩
  exact compiled_lchs_error O p c hc J F hF (fun i => U i x) (S x) x ν δ
    hδ (hLCHS x) (fun i => hSimulation i x)

/-- A counted common schedule satisfying the Hamiltonian resource estimate
inherits the cubic-logarithmic selected-propagator budget. This theorem remains
conditional on the schedule, branch approximation, and LCHS certificates;
it is not an end-to-end ODE solver or an amplification theorem. -/
theorem conditional_selected_query_certificate (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x))
    (p : CoherentQuerySchedule.Schedule ι L K) (c : ι → ℂ)
    (hc : 0 < ODECoherentLCU.coefficientMass c)
    (J F : ι → P →L[ℂ] K)
    (hJ : ∀ i, (J i)† ∘L J i = 1) (hF : ∀ i, (F i)† ∘L F i = 1)
    (U : ι → X → P →L[ℂ] P) (S : X → P →L[ℂ] P) (ν δ s a g ε : ℝ)
    (hδ : 0 ≤ δ) (hs : 1 ≤ s) (ha : 0 ≤ a) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hLCHS : ∀ x, ‖(∑ i, c i • U i x) - S x‖ ≤ ν)
    (hSimulation : ∀ i x,
      ‖(p.branch O i).eval x ∘L J i - F i ∘L U i x‖ ≤ δ)
    (hCount : (p.count : ℝ) ≤ 2235174912 * ODEQueryBudget.effectiveTime a g ε *
      Real.sqrt s * ODEQueryBudget.simulationLog s a g ε ^ 2) :
    ∃ q : MultiOracleCircuit.Program (CoherentQuerySchedule.oracle (ι := ι) O),
      (q.count : ℝ) ≤ 214576791552 * (1 + a) * Real.sqrt s *
        ODEQueryBudget.logBudget s a g ε ^ 3 ∧
      (ODECoherentLCU.inputEmbedding c J)† ∘L ODECoherentLCU.inputEmbedding c J = 1 ∧
      (ODECoherentLCU.outputEmbedding c F)† ∘L ODECoherentLCU.outputEmbedding c F = 1 ∧
      ∀ x, IsUnitary (q.eval x) ∧
        ‖(ODECoherentLCU.coefficientMass c : ℂ) •
          ((ODECoherentLCU.outputEmbedding c F)† ∘L
            q.eval x ∘L ODECoherentLCU.inputEmbedding c J) - S x‖ ≤
          ν + ODECoherentLCU.coefficientMass c * δ := by
  obtain ⟨q, hq, hIn, hOut, hError⟩ := controlled_lchs_certificate
    O hO p c hc J F hJ hF U S ν δ hδ hLCHS hSimulation
  refine ⟨q, ?_, hIn, hOut, hError⟩
  rw [hq]
  exact hCount.trans (ODEQueryBudget.native_selected_query_bound s a g ε
    hs ha hg hε hε1)

end
end SparseHamiltonian.ODEControlledLCU
