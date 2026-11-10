import GeneralSourceExtensions.Mesh.Native
import GeneralSourceExtensions.Approx.Pullback

/-!
# The supplied source oracles on `N` slots

The actual oracles of `GeneralSourceODE.Oracles` on the primitive workspace of the SELECT on `N`
slots: the coherent sampled-time matrix calls with fixed spectators, and the supplied `P_w`,
`U_load` and `P_w†` with their supported enable control (`actualOracle`). Each call of the counted
preparation interface is one `P_w` call, one `U_load` call and the public phase gate; each call of
the counted unpreparation interface is one `P_w†` call (`implementation`, `implementation_eval`).
Substituting these implementations turns a counted trial family into one over the actual oracles
with the same evaluations and the separate counts (`actualTrials`).

For approximate preparations, `actualOracle_pullback_matrix` and `actualOracle_dev` are the
`N`-slot forms of the corresponding statements of `Approx/Pullback`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.MeshOracles

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open GeneralSourceODE
open GeneralSourceODE.Oracles (sourceOperation sourceOperation_unitary sourcePhysical_mul
  matrixCalls calls sourceCalls)
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

variable {ι X Y n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- The actual primitive oracles on `N` slots. -/
def actualOracle (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    Query ⊕ SourceCall → X →
      MeshNative.PhysicalSpace ι n Z m M N d →L[ℂ] MeshNative.PhysicalSpace ι n Z m M N d :=
  Sum.elim
    (fun l => NativeMaskedOracle.oracle (ι := Native.SourceBasis ι n m)
      (fun x => (MeshNative.matrixLayout (ι := ι) (n := n) (Z := Z) m M N d).conjStarAlgEquiv
        (MeshNative.matrixOracle (ι := ι) D m N d l x)))
    (fun k x => ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
      ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
        (sourceOperation Pw J k x)))

omit [DecidableEq ι] [DecidableEq Z] in
theorem actualOracle_unitary (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    {Pw : X → Weights.LabelOp (Option (Fin m))} (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (hJ : ∀ x a, IsUnitary (J x a)) :
    ∀ l x, IsUnitary (actualOracle (ι := ι) D m N d Pw J l x) := by
  intro l x
  cases l with
  | inl l =>
      exact NativeMaskedOracle.oracle_unitary _
        (fun y => (MeshNative.matrixOracle_unitary (ι := ι) D m N d l y).transport
          (MeshNative.matrixLayout (ι := ι) (n := n) (Z := Z) m M N d)) x
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _
        ((sourceOperation_unitary hPw hJ k x).transport
          (Native.sourceLayout (ι := ι) (n := n) m))

/-- The public phase gate on the enabled source sector. -/
def phaseGate (m M N d : ℕ) (φ : Option (Fin m) → ℂ) :
    MeshNative.PhysicalSpace ι n Z m M N d →L[ℂ] MeshNative.PhysicalSpace ι n Z m M N d :=
  ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
    ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
      (Weights.phaseGate (ι := ι) (P := EuclideanSpace ℂ n) φ))

omit [DecidableEq ι] [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem phaseGate_unitary (m M N d : ℕ) {φ : Option (Fin m) → ℂ} (hφ : ∀ a, ‖φ a‖ = 1) :
    IsUnitary (phaseGate (ι := ι) (n := n) (Z := Z) m M N d φ) :=
  ODESectorTensor.sourcePhysical_unitary _
    ((Weights.phaseGate_unitary φ hφ).transport (Native.sourceLayout (ι := ι) (n := n) m))

/-- Each counted interface call as a program over the actual oracles. -/
def implementation (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) :
    Query ⊕ Bool → MultiOracleCircuit.Program (actualOracle (ι := ι) D m N d Pw J)
  | .inl l => .query (.inl l)
  | .inr false => .seq (.fixed (phaseGate m M N d φ) (phaseGate_unitary m M N d hφ))
      (.seq (.query (.inr .load)) (.query (.inr .weight)))
  | .inr true => .query (.inr .unweight)

/-- The implementations are exact. -/
theorem implementation_eval (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) (x : X) :
    (implementation (ι := ι) D m N d Pw J φ hφ l).eval x =
      MeshNative.physicalOracle (ι := ι) D m N d Pw J φ l x := by
  rcases l with l | b
  · rfl
  · cases b with
    | true => rfl
    | false =>
        change phaseGate m M N d φ *
            (ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
                (Weights.loader (J x))) *
            ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
              ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
                (Weights.act (Pw x)))) =
          ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
              (Compiled.prep (Pw x) (J x) φ))
        rw [phaseGate, ← sourcePhysical_mul, ← sourcePhysical_mul, ← map_mul, ← map_mul]
        rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_matrix (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m N d Pw J φ hφ l).cost matrixCalls =
      ODESourceQueryBudget.matrixWeight (fun _ => 1) l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_weight (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m N d Pw J φ hφ l).cost (calls .weight) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_load (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m N d Pw J φ hφ l).cost (calls .load) =
      ODESourceQueryBudget.sourceWeight false l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_unweight (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m N d Pw J φ hφ l).cost (calls .unweight) =
      ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
theorem implementation_source (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1) (l : Query ⊕ Bool) :
    (implementation (ι := ι) D m N d Pw J φ hφ l).cost sourceCalls =
      2 * ODESourceQueryBudget.sourceWeight false l +
        ODESourceQueryBudget.sourceWeight true l := by
  rcases l with l | b
  · rfl
  · cases b <;> rfl

/-- The trial family over the actual oracles. -/
def actualTrials (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle (ι := ι) D m N d Pw J φ)) :
    ℕ → MultiOracleCircuit.Program (actualOracle (ι := ι) D m N d Pw J) :=
  fun j => (q j).substitute (implementation D m N d Pw J φ hφ)

/-! ### Approximate preparations on `N` slots -/

omit [DecidableEq ι] [DecidableEq Z] in
/-- On the matrix labels, the actual oracles of the pulled-back data at `y` are those of the
original data at `f y`. -/
theorem actualOracle_pullback_matrix (D : Data (X × Fin M) n Z s) (f : Y → X) (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Pw' : Y → Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (l : Query) (y : Y) :
    actualOracle (ι := ι) D m N d Pw J (Sum.inl l) (f y) =
      actualOracle (ι := ι) (pullback D f) m N d Pw' J' (Sum.inl l) y := by
  cases l <;> rfl

omit [DecidableEq ι] [DecidableEq Z] in
/-- **The actual oracles move by the errors of the supplied operations** (`N` slots). -/
theorem actualOracle_dev (D : Data (X × Fin M) n Z s) (D' : Data (Y × Fin M) n Z s)
    (m N d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Pw' : Y → Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (x : X) (y : Y)
    (hmat : ∀ l, actualOracle (ι := ι) D m N d Pw J (Sum.inl l) x =
      actualOracle (ι := ι) D' m N d Pw' J' (Sum.inl l) y)
    {δ : ℝ} (hδ : 0 ≤ δ) (hP : ‖Pw x - Pw' y‖ ≤ δ) (hJ : ∀ a, ‖J x a - J' y a‖ ≤ δ) :
    ∀ l, ‖actualOracle (ι := ι) D m N d Pw J l x -
      actualOracle (ι := ι) D' m N d Pw' J' l y‖ ≤ δ * sourceCalls l := by
  rintro (l | k)
  · rw [hmat l, sub_self, norm_zero]
    simp [sourceCalls]
  · have hS : ∀ S S' : Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m, ‖S - S'‖ ≤ δ →
        ‖ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv S) -
          ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv S')‖ ≤ δ :=
      fun S S' h => (norm_sourcePhysical_sub_le _ _).trans ((norm_conj_sub_le _ _ _).trans h)
    simp only [sourceCalls, Sum.elim_inr, Nat.cast_one, mul_one]
    cases k with
    | weight => exact hS _ _ ((norm_act_sub_le _ _).trans hP)
    | load => exact hS _ _ (norm_loader_sub_le _ _ hδ hJ)
    | unweight =>
        refine hS _ _ ((norm_act_sub_le _ _).trans ?_)
        rw [← map_sub, LinearIsometryEquiv.norm_map]
        exact hP

end

end SparseHamiltonian.GeneralSourceExtensions.MeshOracles
