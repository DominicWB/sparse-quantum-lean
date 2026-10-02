import SparseODE.ODESectorTensor

/-!
# Transfer from sector calls to primitive labelled circuits

This abstract compiler layer requires an actual implementation of each
logical letter on one fixed clean isometry. Its per-letter premises are
discharged by the concrete sector compiler; they do not assert correctness
or query complexity of the final ODE solver. Matrix and supplied source
labels remain separate throughout compilation, including inverse queries.
-/

namespace SparseHamiltonian.ODEPrimitiveControlBudget

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

variable {P K H X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {O : L ⊕ Bool → X → K →L[ℂ] K}
  {F : L ⊕ Bool → X → H →L[ℂ] H}

/-- Insert the physical implementation of each letter and lift every fixed
gate through the same input-independent clean encoding. -/
def compile (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (p : MultiOracleCircuit.Program O) : MultiOracleCircuit.Program F :=
  EncodedLabeledProgram.compile J hJ circuits p

/-- Exactly three physical matrix calls replace each logical matrix call. -/
theorem matrix_cost (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (p : MultiOracleCircuit.Program O) (w : L → ℕ)
    (hCost : ∀ l, (circuits l).cost (ODESourceQueryBudget.matrixWeight w) =
      3 * ODESourceQueryBudget.matrixWeight w l) :
    (compile J hJ circuits p).cost (ODESourceQueryBudget.matrixWeight w) =
      3 * p.cost (ODESourceQueryBudget.matrixWeight w) := by
  rw [compile, EncodedLabeledProgram.compile_cost]
  calc
    p.cost (fun l => (circuits l).cost (ODESourceQueryBudget.matrixWeight w)) =
        p.cost (fun l => 3 * ODESourceQueryBudget.matrixWeight w l) :=
      congrArg p.cost (funext hCost)
    _ = _ := NativeHermitianDilation.cost_scale p _ 3

/-- Each supplied source label retains its exact count. -/
theorem source_cost (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (p : MultiOracleCircuit.Program O) (b : Bool)
    (hCost : ∀ l, (circuits l).cost (ODESourceQueryBudget.sourceWeight b) =
      ODESourceQueryBudget.sourceWeight b l) :
    (compile J hJ circuits p).cost (ODESourceQueryBudget.sourceWeight b) =
      p.cost (ODESourceQueryBudget.sourceWeight b) := by
  rw [compile, EncodedLabeledProgram.compile_cost]
  exact congrArg p.cost (funext hCost)

/-- Both source interfaces together retain their exact total count. -/
theorem source_total_cost (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (p : MultiOracleCircuit.Program O)
    (hCost : ∀ l, (circuits l).cost ODESourceQueryBudget.sourceTotalWeight =
      ODESourceQueryBudget.sourceTotalWeight l) :
    (compile J hJ circuits p).cost ODESourceQueryBudget.sourceTotalWeight =
      p.cost ODESourceQueryBudget.sourceTotalWeight := by
  rw [compile, EncodedLabeledProgram.compile_cost]
  exact congrArg p.cost (funext hCost)

/-- Correctness on the clean input holds for the whole compiled program,
including the inverses occurring inside amplification. -/
theorem state_eq (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x)) (hO : ∀ l x, IsUnitary (O l x))
    (hCircuits : ∀ l x, (circuits l).eval x ∘L J = J ∘L O l x)
    (p : MultiOracleCircuit.Program O) (x : X) (ψ : K) :
    (compile J hJ circuits p).eval x (J ψ) = J (p.eval x ψ) :=
  congrArg (fun U : K →L[ℂ] H => U ψ)
    (EncodedLabeledProgram.compile_eval J hJ circuits hF hO hCircuits p x)

/-- Successful public vectors are identical after removing the new clean
encoding. No precision or direction estimate is changed by this compiler. -/
theorem decoded_eq (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x)) (hO : ∀ l x, IsUnitary (O l x))
    (hCircuits : ∀ l x, (circuits l).eval x ∘L J = J ∘L O l x)
    (p : MultiOracleCircuit.Program O) (x : X) (ψ : K) (A : P →L[ℂ] K) :
    ((J ∘L A)†) ((compile J hJ circuits p).eval x (J ψ)) =
      (A†) (p.eval x ψ) := by
  rw [state_eq J hJ circuits hF hO hCircuits p x ψ]
  exact ODESourceHeraldLift.decode_lift J hJ A (p.eval x ψ)

/-- Hence the actual success probability of each individual trial is
unchanged, not merely bounded below by another algorithm's probability. -/
theorem projected_norm_eq (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x)) (hO : ∀ l x, IsUnitary (O l x))
    (hCircuits : ∀ l x, (circuits l).eval x ∘L J = J ∘L O l x)
    (p : MultiOracleCircuit.Program O) (x : X) (ψ : K) (A : P →L[ℂ] K) :
    ‖ODEHeraldedSuccess.successProjector (J ∘L A)
        ((compile J hJ circuits p).eval x (J ψ))‖ =
      ‖ODEHeraldedSuccess.successProjector A (p.eval x ψ)‖ := by
  rw [state_eq J hJ circuits hF hO hCircuits p x ψ]
  exact ODESourceHeraldLift.projected_norm_lift J hJ A (p.eval x ψ)

/-- Compile an already proved randomized trial family. The implementation
premises concern single oracle letters only; all program costs and physical
success/error statements below follow by the compiler and clean isometry. -/
theorem transfer_certificate (J : K →L[ℂ] H) (hJ : J† ∘L J = 1)
    (circuits : L ⊕ Bool → MultiOracleCircuit.Program F)
    (hF : ∀ l x, IsUnitary (F l x)) (hO : ∀ l x, IsUnitary (O l x))
    (hCircuits : ∀ l x, (circuits l).eval x ∘L J = J ∘L O l x)
    (hMatrixLetter : ∀ l,
      (circuits l).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) =
        3 * ODESourceQueryBudget.matrixWeight (fun _ => 1) l)
    (hSourceLetter : ∀ b l, (circuits l).cost (ODESourceQueryBudget.sourceWeight b) =
      ODESourceQueryBudget.sourceWeight b l)
    (hSourceTotalLetter : ∀ l,
      (circuits l).cost ODESourceQueryBudget.sourceTotalWeight =
        ODESourceQueryBudget.sourceTotalWeight l)
    (q : ℕ → MultiOracleCircuit.Program O) (M : ℕ)
    (ψ : K) (hψ : ‖ψ‖ = 1) (A : P →L[ℂ] K) (hA : A† ∘L A = 1)
    (x : X) (target : P) (s Θ ell g η : ℝ)
    (hMatrix : ∀ j, j < M →
      ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
    (hSource : ∀ j, j < M → ∀ b : Bool,
      ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g)
    (hSourceTotal : ∀ j, j < M →
      ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g)
    (hSuccess : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector A ((q j).eval x ψ)‖ ^ 2) / (M : ℝ))
    (hDirection : ∀ j, j < M → (A†) ((q j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection ((A†) ((q j).eval x ψ)) -
          ODEStateNormalization.unitDirection target‖ ≤ η) :
    ‖J ψ‖ = 1 ∧ (J ∘L A)† ∘L (J ∘L A) = 1 ∧
      (∀ j, j < M →
        ((compile J hJ circuits (q j)).cost
          (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
            318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) ∧
      (∀ j, j < M → ∀ b : Bool,
        ((compile J hJ circuits (q j)).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          10 * g) ∧
      (∀ j, j < M →
        ((compile J hJ circuits (q j)).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤
          20 * g) ∧
      (1 : ℝ) / 4 ≤
          (∑ j ∈ Finset.range M,
            ‖ODEHeraldedSuccess.successProjector (J ∘L A)
              ((compile J hJ circuits (q j)).eval x (J ψ))‖ ^ 2) / (M : ℝ) ∧
        ∀ j, j < M → ((J ∘L A)†)
          ((compile J hJ circuits (q j)).eval x (J ψ)) ≠ 0 →
          ∃ ω : ℂ, ‖ω‖ = 1 ∧
            ‖ω • ODEStateNormalization.unitDirection (((J ∘L A)†)
                ((compile J hJ circuits (q j)).eval x (J ψ))) -
              ODEStateNormalization.unitDirection target‖ ≤ η := by
  have hSeed : ‖J ψ‖ = 1 := by
    rw [J.norm_map_iff_adjoint_comp_self.mpr hJ, hψ]
  refine ⟨hSeed, ODESourceHeraldLift.output_isometry J hJ A hA, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [matrix_cost J hJ circuits (q j) (fun _ => 1) hMatrixLetter]
    push_cast
    calc
      3 * ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          3 * (106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell) :=
        mul_le_mul_of_nonneg_left (hMatrix j hj) (by norm_num)
      _ = _ := by ring
  · intro j hj b
    rw [source_cost J hJ circuits (q j) b (hSourceLetter b)]
    exact hSource j hj b
  · intro j hj
    rw [source_total_cost J hJ circuits (q j) hSourceTotalLetter]
    exact hSourceTotal j hj
  · have hSum :
        (∑ j ∈ Finset.range M,
          ‖ODEHeraldedSuccess.successProjector (J ∘L A)
            ((compile J hJ circuits (q j)).eval x (J ψ))‖ ^ 2) =
        ∑ j ∈ Finset.range M,
          ‖ODEHeraldedSuccess.successProjector A ((q j).eval x ψ)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact congrArg (fun r : ℝ => r ^ 2)
        (projected_norm_eq J hJ circuits hF hO hCircuits (q j) x ψ A)
    rw [hSum]
    exact hSuccess
  · intro j hj hNonzero
    have hDecode := decoded_eq J hJ circuits hF hO hCircuits (q j) x ψ A
    have hLogical : (A†) ((q j).eval x ψ) ≠ 0 := by
      intro hZero
      exact hNonzero (hDecode.trans hZero)
    obtain ⟨ω, hω, hError⟩ := hDirection j hj hLogical
    refine ⟨ω, hω, ?_⟩
    rw [hDecode]
    exact hError

end
end SparseHamiltonian.ODEPrimitiveControlBudget
