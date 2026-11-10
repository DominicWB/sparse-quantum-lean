import GeneralSourceODE.Native
import SparseODE.ODECompleteSuccess

/-!
# The supplied source oracles, counted separately

The general source interface supplies the weight preparation `P_w`, the
loading oracle `U_load` and the adjoint `P_w†`, each with its supported
enable control (`SourceCall`, `actualOracle`). The public phases are a known
gate (`phaseGate`). Each call of the counted preparation interface of
`Native.physicalOracle` is exactly one `P_w` call, one `U_load` call and the
public phase gate; each call of the counted unpreparation interface is one
`P_w†` call (`implementation`, `implementation_eval`). Substituting these
implementations into any program preserves its evaluation and turns its two
interface counts into the separate counts of `P_w`, `U_load` and `P_w†`
(`actualTrials`).

The released four-trial protocol only uses the trial evaluations, the public
seed and the public output flag, so its success probability and conditional
output are unchanged by the substitution
(`fourTrials_successMass_congr`, `fourTrials_conditionalDensity_congr`).
`actual_certificate` transfers the released complete certificate to the
protocol over the actual oracles (`ActualCertificate`): success at least
`2/3`, conditional trace distance at most `ε`, at most
`1274019840 g (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and at most `40 g` calls
of each of `P_w`, `U_load` and `P_w†`, `120 g` in total.
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

/-- The supplied source operations, each counted separately: the weight
preparation `P_w`, the loading oracle `U_load`, and the adjoint `P_w†`. -/
inductive SourceCall
  | weight
  | load
  | unweight
  deriving DecidableEq

namespace Oracles

section Counting

variable {L : Type*}

/-- Primitive matrix calls. -/
def matrixCalls : L ⊕ SourceCall → ℕ := Sum.elim (fun _ => 1) (fun _ => 0)

/-- Calls of one supplied source operation. -/
def calls (k : SourceCall) : L ⊕ SourceCall → ℕ :=
  Sum.elim (fun _ => 0) (fun k' => if k' = k then 1 else 0)

/-- Calls of all supplied source operations. -/
def sourceCalls : L ⊕ SourceCall → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

end Counting

section Costs

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

theorem cost_add (p : MultiOracleCircuit.Program O) (w v : L → ℕ) :
    p.cost (fun l => w l + v l) = p.cost w + p.cost v := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      simp only [MultiOracleCircuit.Program.cost_seq, hp, hq]
      ring

end Costs

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- The supplied source operations on the source register. -/
def sourceOperation (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    SourceCall → X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m
  | .weight, x => Weights.act (Pw x)
  | .load, x => Weights.loader (J x)
  | .unweight, x => Weights.act ((Pw x)†)

omit [DecidableEq ι] [DecidableEq n] in
theorem sourceOperation_unitary {Pw : X → Weights.LabelOp (Option (Fin m))}
    (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hJ : ∀ x a, IsUnitary (J x a)) :
    ∀ k x, IsUnitary (sourceOperation (ι := ι) Pw J k x)
  | .weight, x => Weights.act_unitary (hPw x)
  | .load, x => Weights.loader_unitary (J x) (hJ x)
  | .unweight, x => Weights.act_unitary (Compiled.adjoint_unitary (hPw x))

/-- The actual primitive oracles: ordinary coherent sampled-time matrix calls
with fixed spectators, and the three supplied source operations with their
supported enable control. -/
def actualOracle (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ SourceCall → X →
      Native.PhysicalSpace ι n Z m M d →L[ℂ] Native.PhysicalSpace ι n Z m M d :=
  Sum.elim
    (fun l => NativeMaskedOracle.oracle (ι := Native.SourceBasis ι n m)
      (fun x => (Native.matrixLayout (ι := ι) (n := n) (Z := Z) m M d).conjStarAlgEquiv
        (Native.matrixOracle (ι := ι) D m d l x)))
    (fun k x => ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
      ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
        (sourceOperation Pw J k x)))

omit [DecidableEq ι] [DecidableEq Z] in
theorem actualOracle_unitary (D : Data (X × Fin M) n Z s) (m d : ℕ)
    {Pw : X → Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hJ : ∀ x a, IsUnitary (J x a)) :
    ∀ l x, IsUnitary (actualOracle (ι := ι) D m d Pw J l x) := by
  intro l x
  cases l with
  | inl l =>
      exact NativeMaskedOracle.oracle_unitary _
        (fun y => (Native.matrixOracle_unitary (ι := ι) D m d l y).transport
          (Native.matrixLayout (ι := ι) (n := n) (Z := Z) m M d)) x
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _
        ((sourceOperation_unitary hPw hJ k x).transport
          (Native.sourceLayout (ι := ι) (n := n) m))

/-- The public phase gate on the enabled source sector. -/
def phaseGate (m M d : ℕ) (φ : Option (Fin m) → ℂ) :
    Native.PhysicalSpace ι n Z m M d →L[ℂ] Native.PhysicalSpace ι n Z m M d :=
  ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
    ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
      (Weights.phaseGate (ι := ι) (P := EuclideanSpace ℂ n) φ))

omit [DecidableEq ι] [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem phaseGate_unitary (m M d : ℕ) {φ : Option (Fin m) → ℂ} (hφ : ∀ a, ‖φ a‖ = 1) :
    IsUnitary (phaseGate (ι := ι) (n := n) (Z := Z) m M d φ) :=
  ODESectorTensor.sourcePhysical_unitary _
    ((Weights.phaseGate_unitary φ hφ).transport (Native.sourceLayout (ι := ι) (n := n) m))

omit [DecidableEq ι] in
/-- The enabled source call is multiplicative. -/
theorem sourcePhysical_mul {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (S₁ S₂ : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :
    ODESectorTensor.sourcePhysical (B := B) (S₁ * S₂) =
      ODESectorTensor.sourcePhysical (B := B) S₁ * ODESectorTensor.sourcePhysical S₂ := by
  unfold ODESectorTensor.sourcePhysical
  rw [← map_mul]
  congr 1
  change _ = (WeightedClock.diagonal _).comp (WeightedClock.diagonal _)
  rw [WeightedClock.diagonal_comp]
  congr 1
  funext w
  split_ifs
  · rfl
  · rfl

/-- Each counted interface call as a program over the actual oracles: the
preparation is `P_w`, then `U_load`, then the public phases; the
unpreparation is `P_w†`. -/
def implementation (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) :
    Query ⊕ Bool → MultiOracleCircuit.Program (actualOracle (ι := ι) D m d Pw J)
  | .inl l => .query (.inl l)
  | .inr false => .seq (.fixed (phaseGate m M d φ) (phaseGate_unitary m M d hφ))
      (.seq (.query (.inr .load)) (.query (.inr .weight)))
  | .inr true => .query (.inr .unweight)

/-- The implementations are exact. -/
theorem implementation_eval (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) (x : X) :
    (implementation (ι := ι) D m d Pw J φ hφ l).eval x =
      Native.physicalOracle (ι := ι) D m d Pw J φ l x := by
  rcases l with l | b
  · rfl
  · cases b with
    | true => rfl
    | false =>
        change phaseGate m M d φ *
            (ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
                (Weights.loader (J x))) *
            ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
                (Weights.act (Pw x)))) =
          ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
              (Compiled.prep (Pw x) (J x) φ))
        rw [phaseGate, ← sourcePhysical_mul, ← sourcePhysical_mul, ← map_mul, ← map_mul]
        rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_matrix (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m d Pw J φ hφ l).cost matrixCalls =
      ODESourceQueryBudget.matrixWeight (fun _ => 1) l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_weight (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m d Pw J φ hφ l).cost (calls .weight) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_load (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m d Pw J φ hφ l).cost (calls .load) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_unweight (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m d Pw J φ hφ l).cost (calls .unweight) =
      ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_source (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m d Pw J φ hφ l).cost sourceCalls =
      2 * ODESourceQueryBudget.sourceWeight false l +
        ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

/-- The trial family over the actual oracles. -/
def actualTrials (D : Data (X × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (q : ℕ → MultiOracleCircuit.Program (Native.physicalOracle (ι := ι) D m d Pw J φ)) :
    ℕ → MultiOracleCircuit.Program (actualOracle (ι := ι) D m d Pw J) :=
  fun j => (q j).substitute (implementation D m d Pw J φ hφ)

section Congruence

variable {E K Y L L' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → Y → K →L[ℂ] K} {O' : L' → Y → K →L[ℂ] K}

theorem ofCircuits_meanSuccess (q : ℕ → MultiOracleCircuit.Program O)
    (q' : ℕ → MultiOracleCircuit.Program O') (M : ℕ) (hM : 0 < M) (ψ : K) (hψ : ‖ψ‖ = 1)
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (y : Y) (h : ∀ j, (q' j).eval y = (q j).eval y) :
    (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).meanSuccess y =
      (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).meanSuccess y := by
  change (∑ j : Fin M, ‖(F†) ((q' j.val).eval y ψ)‖ ^ 2) / (M : ℝ) =
    (∑ j : Fin M, ‖(F†) ((q j.val).eval y ψ)‖ ^ 2) / (M : ℝ)
  simp_rw [h]

theorem ofCircuits_oneTrialDensity (q : ℕ → MultiOracleCircuit.Program O)
    (q' : ℕ → MultiOracleCircuit.Program O') (M : ℕ) (hM : 0 < M) (ψ : K) (hψ : ‖ψ‖ = 1)
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (y : Y) (h : ∀ j, (q' j).eval y = (q j).eval y) :
    (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).oneTrialDensity y =
      (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).oneTrialDensity y := by
  change ODEMixedOutput.ensemble (fun j : Fin M => ‖(F†) ((q' j.val).eval y ψ)‖ ^ 2 / (M : ℝ))
      (fun j : Fin M => ODEStateNormalization.unitDirection ((F†) ((q' j.val).eval y ψ))) =
    ODEMixedOutput.ensemble (fun j : Fin M => ‖(F†) ((q j.val).eval y ψ)‖ ^ 2 / (M : ℝ))
      (fun j : Fin M => ODEStateNormalization.unitDirection ((F†) ((q j.val).eval y ψ)))
  simp_rw [h]

/-- The success probability of the four-trial protocol depends only on the
trial evaluations. -/
theorem fourTrials_successMass_congr (q : ℕ → MultiOracleCircuit.Program O)
    (q' : ℕ → MultiOracleCircuit.Program O') (M : ℕ) (hM : 0 < M) (ψ : K) (hψ : ‖ψ‖ = 1)
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (y : Y) (h : ∀ j, (q' j).eval y = (q j).eval y) :
    (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF).successMass y =
      (ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).successMass y := by
  unfold ODERepeatProtocol.fourTrials
  rw [ODERepeatProtocol.Protocol.repeat_successMass,
    ODERepeatProtocol.Protocol.repeat_successMass,
    ofCircuits_meanSuccess q q' M hM ψ hψ F hF y h]

theorem repeat_successDensity_congr (q : ℕ → MultiOracleCircuit.Program O)
    (q' : ℕ → MultiOracleCircuit.Program O') (M : ℕ) (hM : 0 < M) (ψ : K) (hψ : ‖ψ‖ = 1)
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (y : Y) (h : ∀ j, (q' j).eval y = (q j).eval y)
    (r : ℕ) :
    (ODERepeatProtocol.Protocol.repeatTrials
        (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF) r).successDensity y =
      (ODERepeatProtocol.Protocol.repeatTrials
        (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) r).successDensity y := by
  induction r with
  | zero => rfl
  | succ r ih =>
      change (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).oneTrialDensity y +
          ((1 - (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).meanSuccess y : ℝ) : ℂ) •
            (ODERepeatProtocol.Protocol.repeatTrials
              (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF) r).successDensity y =
        (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).oneTrialDensity y +
          ((1 - (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).meanSuccess y : ℝ) : ℂ) •
            (ODERepeatProtocol.Protocol.repeatTrials
              (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) r).successDensity y
      rw [ofCircuits_oneTrialDensity q q' M hM ψ hψ F hF y h,
        ofCircuits_meanSuccess q q' M hM ψ hψ F hF y h, ih]

/-- The conditional output of the four-trial protocol depends only on the
trial evaluations. -/
theorem fourTrials_conditionalDensity_congr (q : ℕ → MultiOracleCircuit.Program O)
    (q' : ℕ → MultiOracleCircuit.Program O') (M : ℕ) (hM : 0 < M) (ψ : K) (hψ : ‖ψ‖ = 1)
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1) (y : Y) (h : ∀ j, (q' j).eval y = (q j).eval y) :
    (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF).conditionalDensity y =
      (ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).conditionalDensity y := by
  unfold ODERepeatProtocol.Protocol.conditionalDensity
  rw [fourTrials_successMass_congr q q' M hM ψ hψ F hF y h]
  unfold ODERepeatProtocol.fourTrials
  rw [repeat_successDensity_congr q q' M hM ψ hψ F hF y h 4]

end Congruence

section Certificate

variable {P R Y : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- Complete operational guarantee of a protocol over the actual oracles:
the matrix queries and the calls of `P_w`, `U_load` and `P_w†` are counted
separately, worst case over all histories. -/
structure ActualCertificate {O : Query ⊕ SourceCall → Y → R →L[ℂ] R}
    (A : ODERepeatProtocol.Protocol O P) (y : Y) (target : P) (s Θ ell g ε : ℝ) :
    Prop where
  success_lower : (175 : ℝ) / 256 ≤ A.successMass y
  success_two_thirds : (2 : ℝ) / 3 ≤ A.successMass y
  matrix_queries :
    (A.worstCost matrixCalls : ℝ) ≤ 1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell
  weight_calls : (A.worstCost (calls .weight) : ℝ) ≤ 40 * g
  load_calls : (A.worstCost (calls .load) : ℝ) ≤ 40 * g
  unweight_calls : (A.worstCost (calls .unweight) : ℝ) ≤ 40 * g
  source_calls : (A.worstCost sourceCalls : ℝ) ≤ 120 * g
  output_density : ODEMixedOutput.IsDensity (A.conditionalDensity y)
  conditional_error :
    ∃ h : (A.conditionalDensity y -
        ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection target)).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (A.conditionalDensity y)
        (ODEMixedOutput.pureOperator (ODEStateNormalization.unitDirection target)) h ≤ ε

/-- The released complete certificate of a counted two-interface family
transfers to any family over the actual oracles with the same evaluations,
the same matrix counts, one `P_w` and one `U_load` call per preparation call
and one `P_w†` call per unpreparation call. -/
theorem actual_certificate {L : Type*} {O : (L ⊕ Bool) → Y → R →L[ℂ] R}
    {O' : Query ⊕ SourceCall → Y → R →L[ℂ] R}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : R} {F : P →L[ℂ] R} {y : Y}
    {target : P} {s Θ ell g ε : ℝ}
    (hCert : ODECompleteTrial.Certificate q M ψ F y target s Θ ell g ε)
    (q' : ℕ → MultiOracleCircuit.Program O') (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hEval : ∀ j, (q' j).eval y = (q j).eval y)
    (hMatrix : ∀ j, (q' j).cost matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))
    (hWeight : ∀ j, (q' j).cost (calls .weight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hLoad : ∀ j, (q' j).cost (calls .load) =
      (q j).cost (ODESourceQueryBudget.sourceWeight false))
    (hUnweight : ∀ j, (q' j).cost (calls .unweight) =
      (q j).cost (ODESourceQueryBudget.sourceWeight true))
    (hSource : ∀ j, (q' j).cost sourceCalls =
      2 * (q j).cost (ODESourceQueryBudget.sourceWeight false) +
        (q j).cost (ODESourceQueryBudget.sourceWeight true)) :
    ActualCertificate (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF) y target s Θ ell g ε := by
  have hSucc := fourTrials_successMass_congr q q' M hM ψ hψ F hF y hEval
  have hDens := fourTrials_conditionalDensity_congr q q' M hM ψ hψ F hF y hEval
  have hAlg : ODECompleteTrial.algorithm hCert.trial =
      ODERepeatProtocol.fourTrials q M hM ψ hψ F hF := rfl
  have hSucc' : (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF).successMass y =
      (ODECompleteTrial.algorithm hCert.trial).successMass y := by
    rw [hAlg]
    exact hSucc
  have hDens' : (ODERepeatProtocol.fourTrials q' M hM ψ hψ F hF).conditionalDensity y =
      (ODECompleteTrial.algorithm hCert.trial).conditionalDensity y := by
    rw [hAlg]
    exact hDens
  have hTrial := hCert.trial
  refine
    { success_lower := ?_
      success_two_thirds := ?_
      matrix_queries := ?_
      weight_calls := ?_
      load_calls := ?_
      unweight_calls := ?_
      source_calls := ?_
      output_density := ?_
      conditional_error := ?_ }
  · rw [hSucc']
    exact hCert.success_lower
  · rw [hSucc']
    exact hCert.success_two_thirds
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF matrixCalls
      (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
      (fun j hj => by rw [hMatrix j]; exact hTrial.matrix_queries j hj)
    calc
      _ ≤ 4 * (318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell) := h
      _ = 1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by ring
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF (calls .weight)
      (10 * g) (fun j hj => by rw [hWeight j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF (calls .load)
      (10 * g) (fun j hj => by rw [hLoad j]; exact hTrial.source_queries j hj false)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF (calls .unweight)
      (10 * g) (fun j hj => by rw [hUnweight j]; exact hTrial.source_queries j hj true)
    linarith
  · have h := ODERepeatProtocol.fourTrials_worstCost_le q' M hM ψ hψ F hF sourceCalls
      (30 * g) (fun j hj => by
        rw [hSource j]
        push_cast
        have h1 := hTrial.source_queries j hj false
        have h2 := hTrial.source_queries j hj true
        linarith)
    linarith
  · rw [hDens']
    exact hCert.output_density
  · rw [hDens']
    exact hCert.conditional_error

end Certificate

end Oracles

end

end SparseHamiltonian.GeneralSourceODE
