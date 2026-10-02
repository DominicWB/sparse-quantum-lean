import SparseHamiltonian.SparseFreshAttenuation

/-!
# Polynomial phase sequences on output invariant planes

The preparation unitary need not preserve an output plane. Instead, its
transported input projector and the good-output projector intertwine with
the two scalar projectors. This is the invariant-plane information actually
needed by amplitude manipulation. The intertwiner need not be injective or
isometric, so endpoint planes with a vanishing component are included.

The resulting identities apply to an actual, counted multi-oracle circuit.
All projections and phases are fixed independently of the oracle input.
This transports forward polynomials; it does not assert phase synthesis.
-/

namespace SparseHamiltonian.InvariantPhaseSequence

noncomputable section

open ContinuousLinearMap OracleCircuit ComplexAmplitudeRotation


variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

omit [CompleteSpace K] in
/-- Intertwining projectors also intertwines every fixed phase about them. -/
theorem phase_intertwines (A : K →L[ℂ] K) (B : Qubit →L[ℂ] Qubit)
    (V : Qubit →L[ℂ] K) (h : A ∘L V = V ∘L B) (z : ℂ) :
    PhaseSubspaceGates.phase A z ∘L V = V ∘L PhaseSubspaceGates.phase B z := by
  ext v
  have hv := congrArg (fun f : Qubit →L[ℂ] K => f v) h
  simp only [comp_apply] at hv
  simp only [comp_apply, PhaseSubspaceGates.phase_apply, map_add, map_smul, hv]

/-- The preparation-conjugated projector, rather than the preparation itself,
is the operator required to preserve the output plane. -/
theorem step_intertwines (U P Q : K →L[ℂ] K) (hU : IsUnitary U)
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hP : (U * P * star U) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQ : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection) (s : AmplitudePolynomialSequence.Phases) :
    PhaseSubspaceGates.step U P Q s ∘L V = V ∘L AmplitudePolynomialSequence.step x s := by
  have hR : IsUnitary (rotation (x : ℂ)) :=
    rotation_unitary _ (by simpa using hx)
  rw [PhaseSubspaceGates.step, ← PhaseSubspaceGates.phase_conjugate P U hU, AmplitudePolynomialSequence.step_eq_subspace,
    PhaseSubspaceGates.step, ← PhaseSubspaceGates.phase_conjugate AmplitudePolynomialSequence.cleanProjection _ hR]
  have hp := phase_intertwines _ _ V hP s.1.val
  have hq := phase_intertwines _ _ V hQ s.2.val
  ext v
  have hpv := congrArg (fun f : Qubit →L[ℂ] K => f (PhaseSubspaceGates.phase AmplitudePolynomialSequence.cleanProjection s.2.val v)) hp
  have hqv := congrArg (fun f : Qubit →L[ℂ] K => f v) hq
  simp only [comp_apply] at hqv
  simpa only [comp_apply, mul_apply_eq_comp, hqv] using hpv

/-- Every finite phase product preserves the same (possibly degenerate) plane. -/
theorem sequence_intertwines (U P Q : K →L[ℂ] K) (hU : IsUnitary U)
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hP : (U * P * star U) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQ : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection) (ss : List AmplitudePolynomialSequence.Phases) :
    PhaseSubspaceGates.sequence U P Q ss ∘L V =
      V ∘L PhaseSubspaceGates.sequence (rotation (x : ℂ)) AmplitudePolynomialSequence.cleanProjection AmplitudePolynomialSequence.cleanProjection ss := by
  induction ss with
  | nil => ext v; simp [PhaseSubspaceGates.sequence]
  | cons s ss ih =>
      have hs := step_intertwines U P Q hU x hx V hP hQ s
      rw [AmplitudePolynomialSequence.step_eq_subspace] at hs
      ext v
      have hsv := congrArg (fun f : Qubit →L[ℂ] K =>
        f (PhaseSubspaceGates.sequence (rotation (x : ℂ)) AmplitudePolynomialSequence.cleanProjection AmplitudePolynomialSequence.cleanProjection ss v)) hs
      have ihv := congrArg (fun f : Qubit →L[ℂ] K => f v) ih
      simp only [comp_apply] at ihv
      simpa only [PhaseSubspaceGates.sequence, comp_apply, mul_apply_eq_comp, ihv] using hsv

/-- Transport the entire prepared state, including the bad coordinate. -/
theorem prepared_column (U P Q : K →L[ℂ] K) (hU : IsUnitary U)
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hP : (U * P * star U) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQ : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : U v = V (rotation (x : ℂ) clean)) (ss : List AmplitudePolynomialSequence.Phases) :
    (PhaseSubspaceGates.sequence U P Q ss * U) v =
      V (AmplitudePolynomialSequence.column x (AmplitudePolynomialSequence.polynomials ss).1 (AmplitudePolynomialSequence.polynomials ss).2) := by
  have h := congrArg (fun f : Qubit →L[ℂ] K => f (rotation (x : ℂ) clean))
    (sequence_intertwines U P Q hU x hx V hP hQ ss)
  simp only [comp_apply] at h
  rw [mul_apply_eq_comp, hv, h]
  rw [← mul_apply_eq_comp, ← AmplitudePolynomialSequence.sequence_eq_subspace, AmplitudePolynomialSequence.sequence_column x hx ss]

/-- The good projection of a polynomial column has only its good polynomial. -/
theorem cleanProjection_column (x : ℝ) (A B : Polynomial ℂ) :
    AmplitudePolynomialSequence.cleanProjection (AmplitudePolynomialSequence.column x A B) = A.eval (x : ℂ) • clean := by
  apply PiLp.ext
  intro b
  cases b <;> simp [AmplitudePolynomialSequence.cleanProjection]

/-- The physical good output acquires the same complex polynomial gain. -/
theorem prepared_good (U P Q : K →L[ℂ] K) (hU : IsUnitary U)
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hP : (U * P * star U) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQ : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : U v = V (rotation (x : ℂ) clean)) (ss : List AmplitudePolynomialSequence.Phases) :
    Q ((PhaseSubspaceGates.sequence U P Q ss * U) v) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (x : ℂ) • V clean := by
  rw [prepared_column U P Q hU x hx V hP hQ v hv ss]
  have h := congrArg (fun f : Qubit →L[ℂ] K =>
    f (AmplitudePolynomialSequence.column x (AmplitudePolynomialSequence.polynomials ss).1 (AmplitudePolynomialSequence.polynomials ss).2)) hQ
  simpa only [comp_apply, cleanProjection_column, map_smul] using h

omit [CompleteSpace K] in
/-- The initial good component uses the original scalar signal. -/
theorem initial_good (U Q : K →L[ℂ] K) (x : ℝ) (V : Qubit →L[ℂ] K)
    (hQV : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : U v = V (rotation (x : ℂ) clean)) :
    Q (U v) = (x : ℂ) • V clean := by
  have h := congrArg (fun f : Qubit →L[ℂ] K => f (rotation (x : ℂ) clean)) hQV
  have hc : AmplitudePolynomialSequence.cleanProjection (rotation (x : ℂ) clean) =
      (x : ℂ) • clean := by
    apply PiLp.ext
    intro b
    cases b <;> simp [AmplitudePolynomialSequence.cleanProjection]
  simpa only [comp_apply, hc, map_smul, hv] using h

/-- A relative scalar approximation becomes a relative error on the physical
good component, including a zero signal. No division by the signal is used. -/
theorem prepared_good_error (U P Q : K →L[ℂ] K) (hU : IsUnitary U)
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hPV : (U * P * star U) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQV : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : U v = V (rotation (x : ℂ) clean))
    (ss : List AmplitudePolynomialSequence.Phases) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (x : ℂ) - gain * (x : ℂ)‖ ≤
      δ * |x|) :
    ‖Q ((PhaseSubspaceGates.sequence U P Q ss * U) v) - gain • Q (U v)‖ ≤
      δ * ‖Q (U v)‖ := by
  rw [prepared_good U P Q hU x hx V hPV hQV v hv ss, initial_good U Q x V hQV v hv,
    smul_smul, ← sub_smul, norm_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (δ * |x|) * ‖V clean‖ := mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    _ = _ := by ring

/-- The one-oracle syntax has exactly the transported full output. -/
theorem preparedProgram_column (O : X → K →L[ℂ] K) (P Q : K →L[ℂ] K)
    (hP : PhaseSubspaceGates.IsOrthogonalProjection P) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (ss : List AmplitudePolynomialSequence.Phases) (y : X) (hO : IsUnitary (O y))
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hPV : (O y * P * star (O y)) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQV : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : O y v = V (rotation (x : ℂ) clean)) :
    (PhaseSubspaceGates.preparedProgram O P Q hP hQ ss).eval y v =
      V (AmplitudePolynomialSequence.column x (AmplitudePolynomialSequence.polynomials ss).1 (AmplitudePolynomialSequence.polynomials ss).2) := by
  rw [PhaseSubspaceGates.preparedProgram_eval]
  exact prepared_column (O y) P Q hO x hx V hPV hQV v hv ss

/-- Replace each preparation and inverse by its actual multi-oracle program. -/
def nativeStep {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (s : AmplitudePolynomialSequence.Phases) : MultiOracleCircuit.Program O :=
  .seq (.seq (.seq p (.fixed (PhaseSubspaceGates.phase P s.1.val)
    (PhaseSubspaceGates.phase_unitary P hP s.1.val s.1.property))) p.adjoint)
    (.fixed (PhaseSubspaceGates.phase Q s.2.val) (PhaseSubspaceGates.phase_unitary Q hQ s.2.val s.2.property))

/-- A product of the native two-preparation steps. -/
def nativeSequence {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) : List AmplitudePolynomialSequence.Phases → MultiOracleCircuit.Program O
  | [] => MultiOracleCircuit.Program.identity
  | s :: ss => .seq (nativeStep p P Q hP hQ s) (nativeSequence p P Q hP hQ ss)

/-- The complete native phase circuit includes one initial preparation. -/
def nativePrepared {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases) : MultiOracleCircuit.Program O :=
  .seq (nativeSequence p P Q hP hQ ss) p

@[simp] theorem nativeStep_eval {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (s : AmplitudePolynomialSequence.Phases) (y : X) :
    (nativeStep p P Q hP hQ s).eval y = PhaseSubspaceGates.step (p.eval y) P Q s := by
  simp only [nativeStep, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
    MultiOracleCircuit.Program.eval_adjoint, PhaseSubspaceGates.step]

@[simp] theorem nativeStep_cost {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (s : AmplitudePolynomialSequence.Phases) (w : L → ℕ) :
    (nativeStep p P Q hP hQ s).cost w = 2 * p.cost w := by
  simp [nativeStep, two_mul]

@[simp] theorem nativeSequence_eval {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases) (y : X) :
    (nativeSequence p P Q hP hQ ss).eval y = PhaseSubspaceGates.sequence (p.eval y) P Q ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [nativeSequence, MultiOracleCircuit.Program.eval_seq, nativeStep_eval, ih, PhaseSubspaceGates.sequence]

@[simp] theorem nativeSequence_cost {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases) (w : L → ℕ) :
    (nativeSequence p P Q hP hQ ss).cost w = 2 * ss.length * p.cost w := by
  induction ss with
  | nil => simp [nativeSequence]
  | cons s ss ih =>
      simp only [nativeSequence, MultiOracleCircuit.Program.cost_seq, nativeStep_cost, ih, List.length_cons]
      ring

@[simp] theorem nativePrepared_eval {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases) (y : X) :
    (nativePrepared p P Q hP hQ ss).eval y = PhaseSubspaceGates.sequence (p.eval y) P Q ss * p.eval y := by
  simp only [nativePrepared, MultiOracleCircuit.Program.eval_seq, nativeSequence_eval]

/-- Every assigned query cost, including each individual oracle label, scales
by precisely the odd phase-sequence length. -/
@[simp] theorem nativePrepared_cost {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases) (w : L → ℕ) :
    (nativePrepared p P Q hP hQ ss).cost w = (2 * ss.length + 1) * p.cost w := by
  simp only [nativePrepared, MultiOracleCircuit.Program.cost_seq, nativeSequence_cost]
  ring

@[simp] theorem nativePrepared_count {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases) :
    (nativePrepared p P Q hP hQ ss).count = (2 * ss.length + 1) * p.count := by
  have h := nativePrepared_cost p P Q hP hQ ss (fun _ => 1)
  simpa using h

@[simp] theorem nativePrepared_labelCount [DecidableEq L]
    {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases) (l : L) :
    (nativePrepared p P Q hP hQ ss).labelCount l =
      (2 * ss.length + 1) * p.labelCount l :=
  nativePrepared_cost p P Q hP hQ ss _

/-- Polynomial transport for the actual native-oracle circuit. -/
theorem nativePrepared_column {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases)
    (y : X) (hO : ∀ l y, IsUnitary (O l y))
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hPV : (p.eval y * P * star (p.eval y)) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQV : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : p.eval y v = V (rotation (x : ℂ) clean)) :
    (nativePrepared p P Q hP hQ ss).eval y v =
      V (AmplitudePolynomialSequence.column x (AmplitudePolynomialSequence.polynomials ss).1 (AmplitudePolynomialSequence.polynomials ss).2) := by
  rw [nativePrepared_eval]
  exact prepared_column (p.eval y) P Q (p.eval_unitary hO y) x hx V hPV hQV v hv ss

/-- Good-output polynomial identity with the actual native query implementation. -/
theorem nativePrepared_good {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases)
    (y : X) (hO : ∀ l y, IsUnitary (O l y))
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hPV : (p.eval y * P * star (p.eval y)) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQV : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : p.eval y v = V (rotation (x : ℂ) clean)) :
    Q ((nativePrepared p P Q hP hQ ss).eval y v) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (x : ℂ) • V clean := by
  rw [nativePrepared_eval]
  exact prepared_good (p.eval y) P Q (p.eval_unitary hO y) x hx V hPV hQV v hv ss

/-- Relative amplification error is certified for the counted native program. -/
theorem nativePrepared_good_error {O : L → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O)
    (P Q : K →L[ℂ] K) (hP : PhaseSubspaceGates.IsOrthogonalProjection P)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (ss : List AmplitudePolynomialSequence.Phases)
    (y : X) (hO : ∀ l y, IsUnitary (O l y))
    (x : ℝ) (hx : |x| ≤ 1) (V : Qubit →L[ℂ] K)
    (hPV : (p.eval y * P * star (p.eval y)) ∘L V =
      V ∘L (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection * star (rotation (x : ℂ))))
    (hQV : Q ∘L V = V ∘L AmplitudePolynomialSequence.cleanProjection)
    (v : K) (hv : p.eval y v = V (rotation (x : ℂ) clean)) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (x : ℂ) - gain * (x : ℂ)‖ ≤
      δ * |x|) :
    ‖Q ((nativePrepared p P Q hP hQ ss).eval y v) - gain • Q (p.eval y v)‖ ≤
      δ * ‖Q (p.eval y v)‖ := by
  rw [nativePrepared_eval]
  exact prepared_good_error (p.eval y) P Q (p.eval_unitary hO y) x hx V hPV hQV v hv ss gain δ herr

end
end SparseHamiltonian.InvariantPhaseSequence
