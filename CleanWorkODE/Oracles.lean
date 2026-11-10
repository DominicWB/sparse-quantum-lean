import CleanWorkODE.Registers

/-!
# The supplied source oracles with temporary work registers

The general source interface supplies `P_w`, `U_load` and `P_w†` (eq.
`ode:eq:source-interface-preparation` and the paragraph after it). Here they may use a temporary
work register with basis `W`: the supplied weight preparation acts on the label and work registers
(`LabelW m W`), the supplied loader on the label, data and work registers (`LoadW m n W`), and
`P_w†` is the adjoint of the supplied `P_w`. On the primitive workspace with the work register
adjoined to the source register (`PhysW`), the actual oracles are the coherent sampled-time matrix
calls with the work register as a spectator (`liftPi`) and the supplied operations with the
remaining source registers as spectators (`liftAct`), enabled on the inactive matrix sector
(`actualOracleW`).

`actualOracleW_clean`: if the supplied `P_w` and `U_load` are within `δ` of exact preparations
`P` and `∑_a |a⟩⟨a| ⊗ L(a)` on a clean work register (the manuscript's clean-input errors), every
actual oracle implements the corresponding exact oracle of `GeneralSourceExtensions.MeshOracles`
within `δ` (`0` on the matrix labels) on a clean work register.
-/

set_option autoImplicit false

namespace SparseHamiltonian.CleanWorkODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open GeneralSourceODE
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000

/-- The label register with the work register. -/
abbrev LabelW (m : ℕ) (W : Type*) := EuclideanSpace ℂ (Option (Fin m) × W)

/-- The label and data registers with the work register. -/
abbrev LoadW (m : ℕ) (n W : Type*) := EuclideanSpace ℂ ((Option (Fin m) × n) × W)

/-- The primitive workspace on `N` slots with the work register adjoined to the source
register. -/
abbrev PhysW (ι n Z W : Type*) [Fintype ι] [Fintype n] [Fintype Z] [Fintype W] (m M N d : ℕ) :=
  ODESectorTensor.Physical (Native.SourceBasis ι n m × W) (MeshNative.MatrixBasis ι n Z m M N d)

theorem isUnitary_star {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {U : K →L[ℂ] K} (hU : IsUnitary U) : IsUnitary (star U) :=
  ⟨by rw [star_star]; exact hU.2, by rw [star_star]; exact hU.1⟩

variable {ι X Y n Z W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  [Fintype W] [DecidableEq W]
  {s M : ℕ}

/-- **The supplied source operations with a temporary work register** on the source register:
`P_w ⊗ 1` on the label and work registers, `U_load ⊗ 1` on the label, data and work registers, and
the adjoint `P_w† ⊗ 1`. -/
def sourceOpW {m : ℕ} (Pw : X → LabelW m W →L[ℂ] LabelW m W)
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) :
    SourceCall → X → EuclideanSpace ℂ (Native.SourceBasis ι n m × W) →L[ℂ]
      EuclideanSpace ℂ (Native.SourceBasis ι n m × W)
  | .weight, x => liftAct labelSplit (Pw x)
  | .load, x => liftAct loadSplit (J x)
  | .unweight, x => liftAct labelSplit (star (Pw x))

omit [DecidableEq ι] [DecidableEq n] [DecidableEq W] in
theorem sourceOpW_unitary {m : ℕ} {Pw : X → LabelW m W →L[ℂ] LabelW m W}
    (hPw : ∀ x, IsUnitary (Pw x)) {J : X → LoadW m n W →L[ℂ] LoadW m n W}
    (hJ : ∀ x, IsUnitary (J x)) : ∀ k x, IsUnitary (sourceOpW (ι := ι) Pw J k x)
  | .weight, x => liftAct_unitary _ (hPw x)
  | .load, x => liftAct_unitary _ (hJ x)
  | .unweight, x => liftAct_unitary _ (isUnitary_star (hPw x))

/-- **The actual primitive oracles with a temporary work register**, on `N` slots: the coherent
sampled-time matrix calls with the work register as a spectator, and the supplied operations with
their supported enable control. -/
def actualOracleW (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W) :
    Query ⊕ SourceCall → X → PhysW ι n Z W m M N d →L[ℂ] PhysW ι n Z W m M N d :=
  Sum.elim
    (fun l x => liftPi (MeshOracles.actualOracle (ι := ι) D m N d (fun _ => 1) (fun _ _ => 1)
      (Sum.inl l) x))
    (fun k x => ODESectorTensor.sourcePhysical (A := Native.SourceBasis ι n m × W)
      (B := MeshNative.MatrixBasis ι n Z m M N d) (sourceOpW (ι := ι) Pw J k x))

omit [DecidableEq ι] [DecidableEq Z] [DecidableEq W] in
theorem actualOracleW_unitary (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    {Pw : X → LabelW m W →L[ℂ] LabelW m W} (hPw : ∀ x, IsUnitary (Pw x))
    {J : X → LoadW m n W →L[ℂ] LoadW m n W} (hJ : ∀ x, IsUnitary (J x)) :
    ∀ l x, IsUnitary (actualOracleW (ι := ι) D m N d Pw J l x) := by
  intro l x
  cases l with
  | inl l =>
      exact liftPi_unitary (MeshOracles.actualOracle_unitary (ι := ι) D m N d
        (fun _ => isUnitary_one) (fun _ _ => isUnitary_one) (Sum.inl l) x)
  | inr k =>
      exact ODESectorTensor.sourcePhysical_unitary _ (sourceOpW_unitary hPw hJ k x)

omit [DecidableEq ι] [DecidableEq Z] [DecidableEq W] in
theorem actualOracleW_inl (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W)
    (l : Query) (x : X) :
    actualOracleW (ι := ι) D m N d Pw J (Sum.inl l) x =
      liftPi (MeshOracles.actualOracle (ι := ι) D m N d (fun _ => 1) (fun _ _ => 1)
        (Sum.inl l) x) := rfl

omit [DecidableEq ι] [DecidableEq Z] [DecidableEq W] in
theorem actualOracleW_inr (D : Data (X × Fin M) n Z s) (m N d : ℕ)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W)
    (k : SourceCall) (x : X) :
    actualOracleW (ι := ι) D m N d Pw J (Sum.inr k) x =
      ODESectorTensor.sourcePhysical (A := Native.SourceBasis ι n m × W)
        (B := MeshNative.MatrixBasis ι n Z m M N d) (sourceOpW (ι := ι) Pw J k x) := rfl

omit [DecidableEq ι] [DecidableEq Z] [DecidableEq W] in
theorem actualOracle_inr (D' : Data (Y × Fin M) n Z s) (m N d : ℕ)
    (Pw' : Y → Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (k : SourceCall) (y : Y) :
    MeshOracles.actualOracle (ι := ι) D' m N d Pw' J' (Sum.inr k) y =
      ODESectorTensor.sourcePhysical (B := MeshNative.MatrixBasis ι n Z m M N d)
        ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
          (GeneralSourceODE.Oracles.sourceOperation Pw' J' k y)) := rfl

omit [DecidableEq ι] [DecidableEq Z] in
set_option maxHeartbeats 4000000 in
/-- **The actual oracles keep the clean-input errors of the supplied operations.** If the matrix
oracles agree and the supplied `P_w` and `U_load` are within `δ` of `P` and
`∑_a |a⟩⟨a| ⊗ L(a)` on a clean work register, every actual oracle with the work register
implements the actual oracle of `GeneralSourceExtensions.MeshOracles` for `P`, `L` within `δ` on
the three source labels, and exactly on the matrix labels, on a clean work register. -/
theorem actualOracleW_clean (D : Data (X × Fin M) n Z s) (D' : Data (Y × Fin M) n Z s)
    (m N d : ℕ) (w₀ : W) (Pw : X → LabelW m W →L[ℂ] LabelW m W)
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (Pw' : Y → Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (x : X) (y : Y)
    (hmat : ∀ l, MeshOracles.actualOracle (ι := ι) D m N d (fun _ => 1) (fun _ _ => 1)
        (Sum.inl l) x = MeshOracles.actualOracle (ι := ι) D' m N d Pw' J' (Sum.inl l) y)
    (hPw : IsUnitary (Pw x)) (hP : IsUnitary (Pw' y)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hPc : CleanErr (cleanPi (V := ℂ) w₀) (Pw x) (Pw' y) δ)
    (hJc : CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL (J' y)) δ) :
    ∀ l, CleanErr (cleanPi w₀) (actualOracleW (ι := ι) D m N d Pw J l x)
      (MeshOracles.actualOracle (ι := ι) D' m N d Pw' J' l y)
      (δ * GeneralSourceODE.Oracles.sourceCalls l) := by
  rintro (l | k)
  · have h0 := CleanErr.of_comp (liftPi_clean w₀
      (MeshOracles.actualOracle (ι := ι) D m N d (fun _ => 1) (fun _ _ => 1) (Sum.inl l) x))
    have e : δ * (GeneralSourceODE.Oracles.sourceCalls
        (Sum.inl l : Query ⊕ SourceCall) : ℝ) = 0 := by
      simp [GeneralSourceODE.Oracles.sourceCalls]
    rw [e, actualOracleW_inl, ← hmat l]
    exact h0
  · have e : δ * (GeneralSourceODE.Oracles.sourceCalls
        (Sum.inr k : Query ⊕ SourceCall) : ℝ) = δ := by
      simp [GeneralSourceODE.Oracles.sourceCalls]
    rw [e, actualOracleW_inr, actualOracle_inr]
    cases k with
    | weight =>
        exact sourcePhysical_clean w₀ _ _ hδ
          (liftAct_clean w₀ labelSplit (Pw x) (Pw' y)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv (Weights.act (Pw' y)))
            (slice_act (Pw' y)) hδ hPc)
    | load =>
        exact sourcePhysical_clean w₀ _ _ hδ
          (liftAct_clean w₀ loadSplit (J x) (ctrlL (J' y))
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv (Weights.loader (J' y)))
            (slice_loader (J' y)) hδ hJc)
    | unweight =>
        exact sourcePhysical_clean w₀ _ _ hδ
          (liftAct_clean w₀ labelSplit (star (Pw x)) (star (Pw' y))
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv
              (Weights.act (star (Pw' y))))
            (slice_act (star (Pw' y))) hδ (hPc.adjoint hPw hP))

end

end SparseHamiltonian.CleanWorkODE
