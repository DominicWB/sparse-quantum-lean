import GeneralSourceExtensions.Approx.Norms
import GeneralSourceODE.Theorem

/-!
# Exact preparation instances

The released general-source theorem quantifies over one family of supplied oracles `P_w`,
`U_load`, given as functions of the unknown input. An approximately implemented interface has,
for each instance, exact unitary preparations near the supplied ones, which need not be functions
of the input alone. They are made part of the input:

* `pullback`: the sparse data read through a map of inputs; its scale, slots and decoder are
  those of the original data, so the public tables (`Index`, `lchsCoefficients`, …) agree
  definitionally;
* `Inst X n m`: an input of `X` together with a unitary weight preparation and unitary loaders,
  with projections `Inst.input`, `Inst.weight`, `Inst.loader`;
* `actualOracle_pullback_matrix`: on the matrix labels the actual oracles of the pulled-back data
  at an instance are those of the original data at its input;
* `actualOracle_dev`: if the matrix oracles agree, the actual oracles move by at most `δ` on the
  three source labels when the supplied weight preparation and every loader move by at most `δ`
  in operator norm, and not at all on the matrix labels.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open GeneralSourceODE
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X Y n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The sparse data read through a map of inputs. -/
def pullback (D : Data (X × Fin M) n Z s) (f : Y → X) : Data (Y × Fin M) n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix := fun y => D.matrix (f y.1, y.2)
  table := fun y => D.table (f y.1, y.2)
  decode := D.decode
  decode_bound := D.decode_bound
  decoded := fun y => D.decoded (f y.1, y.2)
  rowloc := fun y => D.rowloc (f y.1, y.2)
  colloc := fun y => D.colloc (f y.1, y.2)
  row_injective := fun y => D.row_injective (f y.1, y.2)
  column_injective := fun y => D.column_injective (f y.1, y.2)
  row_covers := fun y => D.row_covers (f y.1, y.2)
  column_covers := fun y => D.column_covers (f y.1, y.2)
  rowOracle := fun y => D.rowOracle (f y.1, y.2)
  columnOracle := fun y => D.columnOracle (f y.1, y.2)
  row_unitary := fun y => D.row_unitary (f y.1, y.2)
  column_unitary := fun y => D.column_unitary (f y.1, y.2)
  row_valid := fun y => D.row_valid (f y.1, y.2)
  column_valid := fun y => D.column_valid (f y.1, y.2)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem pullback_matrix (D : Data (X × Fin M) n Z s) (f : Y → X) (y : Y × Fin M) :
    (pullback D f).matrix y = D.matrix (f y.1, y.2) := rfl

/-- **Exact preparation instances**: an input of `X` with a unitary weight preparation and
unitary label-controlled loaders. -/
abbrev Inst (X n : Type*) [Fintype n] (m : ℕ) :=
  {p : X × Weights.LabelOp (Option (Fin m)) ×
      (Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) //
    IsUnitary p.2.1 ∧ ∀ a, IsUnitary (p.2.2 a)}

namespace Inst

variable {m : ℕ}

/-- The input of an instance. -/
def input (p : Inst X n m) : X := p.1.1

/-- The exact weight preparation of an instance. -/
def weight (p : Inst X n m) : Weights.LabelOp (Option (Fin m)) := p.1.2.1

/-- The exact loaders of an instance. -/
def loader (p : Inst X n m) :
    Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := p.1.2.2

omit [DecidableEq n] in
theorem weight_unitary (p : Inst X n m) : IsUnitary (weight p) := p.2.1

omit [DecidableEq n] in
theorem loader_unitary (p : Inst X n m) (a : Option (Fin m)) : IsUnitary (loader p a) := p.2.2 a

/-- The instance with input `x` and exact preparations `P`, `L`. -/
def mk (x : X) (P : Weights.LabelOp (Option (Fin m)))
    (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hP : IsUnitary P) (hL : ∀ a, IsUnitary (L a)) : Inst X n m :=
  ⟨(x, P, L), hP, hL⟩

end Inst

omit [DecidableEq Z] in
/-- On the matrix labels, the actual oracles of the pulled-back data at `y` are those of the
original data at `f y`. -/
theorem actualOracle_pullback_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (f : Y → X) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Pw' : Y → Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (l : Query) (y : Y) :
    Oracles.actualOracle (ι := ι) D m d Pw J (Sum.inl l) (f y) =
      Oracles.actualOracle (ι := ι) (pullback D f) m d Pw' J' (Sum.inl l) y := by
  cases l <;> rfl

omit [DecidableEq Z] in
set_option maxHeartbeats 1000000 in
/-- **The actual oracles move by the errors of the supplied operations.** If the matrix oracles
agree, every source label moves by at most `δ` when the weight preparation and every loader move
by at most `δ`. -/
theorem actualOracle_dev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Data (X × Fin M) n Z s) (D' : Data (Y × Fin M) n Z s) (m d : ℕ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Pw' : Y → Weights.LabelOp (Option (Fin m)))
    (J' : Y → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (x : X) (y : Y)
    (hmat : ∀ l, Oracles.actualOracle (ι := ι) D m d Pw J (Sum.inl l) x =
      Oracles.actualOracle (ι := ι) D' m d Pw' J' (Sum.inl l) y)
    {δ : ℝ} (hδ : 0 ≤ δ) (hP : ‖Pw x - Pw' y‖ ≤ δ) (hJ : ∀ a, ‖J x a - J' y a‖ ≤ δ) :
    ∀ l, ‖Oracles.actualOracle (ι := ι) D m d Pw J l x -
      Oracles.actualOracle (ι := ι) D' m d Pw' J' l y‖ ≤ δ * Oracles.sourceCalls l := by
  rintro (l | k)
  · rw [hmat l, sub_self, norm_zero]
    simp [Oracles.sourceCalls]
  · have hS : ∀ S S' : Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m, ‖S - S'‖ ≤ δ →
        ‖ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv S) -
          ODESectorTensor.sourcePhysical (B := Native.MatrixBasis ι n Z m M d)
            ((Native.sourceLayout (ι := ι) (n := n) m).conjStarAlgEquiv S')‖ ≤ δ :=
      fun S S' h => (norm_sourcePhysical_sub_le _ _).trans ((norm_conj_sub_le _ _ _).trans h)
    simp only [Oracles.sourceCalls, Sum.elim_inr, Nat.cast_one, mul_one]
    cases k with
    | weight => exact hS _ _ ((norm_act_sub_le _ _).trans hP)
    | load => exact hS _ _ (norm_loader_sub_le _ _ hδ hJ)
    | unweight =>
        refine hS _ _ ((norm_act_sub_le _ _).trans ?_)
        rw [← map_sub, LinearIsometryEquiv.norm_map]
        exact hP

end

end SparseHamiltonian.GeneralSourceExtensions
