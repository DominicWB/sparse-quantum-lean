import ManuscriptConformance.Defs
import SparseHamiltonian.EncodedLabeledProgram
import SparseHamiltonian.NativeSparseMaskedAccess

/-!
# Value access by a reversible writer specified on clean targets (handover item B4)

Section `hs:sec:control` lets the value oracle be any reversible writer of the stored word into a
clean target register, with its supplied inverse; XOR-writing is an example. The package's sparse
data `NativeSparseBlockEncoding.Data` use the additive lookup `z ↦ z + w_ij` on every target.
Here the additive lookup is implemented from a writer `W` that is specified only on a clean target:

  `W |a, 0⟩ = c_a |a, w_a⟩`  for every address `a = (i, j)`, with any phases `c_a`,

and is otherwise an arbitrary unitary on the address and target registers. The circuit writes the
word into one extra clean scratch register (`W`), adds the scratch word to the value target (a
fixed permutation, `adder`), and erases the scratch register with the literal inverse (`W†`):
two writer calls. On every state whose scratch register is clean, including arbitrary dirty value
targets and flags, it acts exactly as the additive lookup and returns the scratch register to its
clean word (`value_intertwines`); the phases `c_a` cancel. The locators are unchanged, with the
scratch register a spectator.

`Impl` records such an implementation of a whole family of primitive calls on a fixed isometric
encoding, and is preserved by the fixed register layers from which the physical oracle families of
the package are built (`Impl.conj`, `Impl.diag`, `Impl.spectator`, `Impl.maskedProgram`). Every
physical call of the converted family is the primitive call under one fixed unital
star-algebra homomorphism `Φ` (spectator registers), recorded in the statement.
-/

namespace SparseHamiltonian.WriterAccess

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct

/-! ### The primitive conversion -/

/-- The labels of the writer access: the two supplied locators and the supplied writer. -/
inductive WQuery where
  | row
  | column
  | writer
  deriving DecidableEq

section Primitive
variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- The primitive workspace with one more value-sized scratch register (the outer index). -/
abbrev Space (n Z : Type*) [Fintype n] [Fintype Z] :=
  PiLp 2 (fun _ : Z => SparseFlagEmbedding.Space (n × n) Z)

/-- The writer's register: the address and the scratch word. -/
abbrev WReg (n Z : Type*) := EuclideanSpace ℂ ((n × n) × Z)

/-- Route the address and the scratch word to the writer; the value target and the flag are
spectators. -/
def basisW (n Z : Type*) : Z × (((n × n) × Z) × Fin 3) ≃ (Z × Fin 3) × ((n × n) × Z) where
  toFun w := ((w.2.1.2, w.2.2), (w.2.1.1, w.1))
  invFun w := (w.2.2, ((w.2.1, w.1.1), w.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fixed layout of the writer call. -/
def layoutW : Space n Z ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Z × Fin 3 => WReg n Z) :=
  (LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Z => RegisterEquivalences.productFlatten ((n × n) × Z) (Fin 3))).trans
    ((RegisterEquivalences.productFlatten Z (((n × n) × Z) × Fin 3)).trans
      ((LookupOracle.permutationUnitary (basisW n Z)).trans
        (RegisterEquivalences.productFlatten (Z × Fin 3) ((n × n) × Z)).symm))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem layoutW_apply (y : Space n Z) (z : Z) (f : Fin 3) (a : n × n) (t : Z) :
    layoutW y (z, f) (a, t) = y t (a, z) f := rfl

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem layoutW_symm_apply (u : PiLp 2 (fun _ : Z × Fin 3 => WReg n Z)) (t : Z)
    (a : n × n) (z : Z) (f : Fin 3) :
    layoutW.symm u t (a, z) f = u (z, f) (a, t) := rfl

/-- One call of the supplied writer, on the address and the scratch register. -/
def writerOp (W : WReg n Z →L[ℂ] WReg n Z) : Space n Z →L[ℂ] Space n Z :=
  (layoutW (n := n) (Z := Z)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Z × Fin 3 => W))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem writerOp_apply (W : WReg n Z →L[ℂ] WReg n Z) (y : Space n Z) (t : Z) (a : n × n)
    (z : Z) (f : Fin 3) :
    writerOp W y t (a, z) f = W (layoutW y (z, f)) (a, t) := rfl

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem writerOp_unitary (W : WReg n Z →L[ℂ] WReg n Z) (hW : IsUnitary W) :
    IsUnitary (writerOp (n := n) (Z := Z) W) :=
  (CoherentQuerySchedule.diagonal_unitary (fun _ : Z × Fin 3 => W) (fun _ => hW)).transport
    (layoutW (n := n) (Z := Z)).symm

/-- Add the scratch word to the value target: a fixed permutation of the basis. -/
def adder : Space n Z →L[ℂ] Space n Z :=
  WeightedClock.diagonal (fun t : Z =>
    LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit)
      (fun (_ : PUnit.{1}) (_ : n × n) => t) PUnit.unit)

omit [DecidableEq n] [DecidableEq Z] in
@[simp] theorem adder_apply (y : Space n Z) (t : Z) (a : n × n) (z : Z) :
    adder y t (a, z) = y t (a, z - t) := rfl

omit [DecidableEq n] [DecidableEq Z] in
theorem adder_unitary : IsUnitary (adder (n := n) (Z := Z)) :=
  CoherentQuerySchedule.diagonal_unitary _
    (fun _ => LookupControlledGate.oracle_unitary _ _)

/-- The scratch register in its zero word. -/
def clean : SparseFlagEmbedding.Space (n × n) Z →L[ℂ] Space n Z :=
  WeightedClock.boundary (fun t : Z => if t = 0 then 1 else 0) (fun _ => 1)

omit [DecidableEq n] in
theorem clean_apply (v : SparseFlagEmbedding.Space (n × n) Z) (t : Z) :
    clean v t = if t = 0 then v else 0 := by
  rw [clean, WeightedClock.boundary_apply]
  split_ifs <;> simp

omit [DecidableEq n] in
theorem clean_isometry : (clean (n := n) (Z := Z))† ∘L clean = 1 :=
  WeightedClock.boundary_isometry _ (fun t => by split_ifs <;> norm_num)
    (by simp) _ (fun _ => by ext v; simp)

omit [DecidableEq n] in
/-- The locator calls keep the scratch register as a spectator. -/
theorem diagonal_clean (U : SparseFlagEmbedding.Space (n × n) Z →L[ℂ]
    SparseFlagEmbedding.Space (n × n) Z) :
    WeightedClock.diagonal (fun _ : Z => U) ∘L clean = clean ∘L U := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro t
  rw [comp_apply, comp_apply, WeightedClock.diagonal_apply, clean_apply, clean_apply]
  split_ifs <;> simp

/-- **The writer on a clean scratch register.** If the writer writes the word `tab a` into a clean
target with the phase `c a`, its call on a clean scratch register puts `c a` times the amplitude on
the scratch word `tab a`. -/
theorem writerOp_clean (W : WReg n Z →L[ℂ] WReg n Z) (c : n × n → ℂ) (tab : n × n → Z)
    (hW : ∀ a, W (EuclideanSpace.single (a, (0 : Z)) 1) = c a • EuclideanSpace.single (a, tab a) 1)
    (v : SparseFlagEmbedding.Space (n × n) Z) (t : Z) (a : n × n) (z : Z) (f : Fin 3) :
    writerOp W (clean v) t (a, z) f = if t = tab a then c a * v (a, z) f else 0 := by
  have hu : layoutW (clean v) (z, f) =
      ∑ a' : n × n, v (a', z) f • EuclideanSpace.single (a', (0 : Z)) (1 : ℂ) := by
    ext ⟨a', t'⟩
    rw [layoutW_apply, clean_apply]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      PiLp.single_apply, Prod.mk.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero]
    by_cases ht : t' = 0
    · subst ht
      simp
    · simp [ht]
  rw [writerOp_apply, hu, map_sum]
  simp only [map_smul, hW]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    PiLp.single_apply, Prod.mk.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases ht : t = tab a
  · subst ht
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hb
      rw [if_neg]
      exact fun h => hb h.1.symm
    · intro h
      exact absurd (Finset.mem_univ a) h
  · rw [if_neg ht]
    apply Finset.sum_eq_zero
    intro a' _
    split_ifs with h
    · exact absurd (by rw [h.1]; exact h.2) ht
    · rfl

/-- The additive lookup of a table, as in `NativeSparseBlockEncoding.oracles`. -/
abbrev lookup (tab : n × n → Z) :
    SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) (fun (_ : PUnit.{1}) => tab)
    PUnit.unit

/-- Adding the scratch word after the writer is the writer after the additive lookup, on a clean
scratch register. -/
theorem adder_writer_clean (W : WReg n Z →L[ℂ] WReg n Z) (c : n × n → ℂ) (tab : n × n → Z)
    (hW : ∀ a, W (EuclideanSpace.single (a, (0 : Z)) 1) =
      c a • EuclideanSpace.single (a, tab a) 1) :
    adder ∘L writerOp W ∘L clean = writerOp W ∘L clean ∘L lookup tab := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro t
  apply PiLp.ext
  intro az
  apply PiLp.ext
  intro f
  rcases az with ⟨a, z⟩
  simp only [comp_apply, adder_apply]
  rw [writerOp_clean W c tab hW, writerOp_clean W c tab hW]
  split_ifs with h
  · subst h
    rfl
  · rfl

/-- **The two-call conversion.** Writer, adder, inverse writer: on every state with a clean
scratch register, exactly the additive lookup, with the scratch register returned to its clean
word. -/
theorem convert_clean (W : WReg n Z →L[ℂ] WReg n Z) (hWu : IsUnitary W) (c : n × n → ℂ)
    (tab : n × n → Z)
    (hW : ∀ a, W (EuclideanSpace.single (a, (0 : Z)) 1) =
      c a • EuclideanSpace.single (a, tab a) 1) :
    (writerOp W)† ∘L adder ∘L writerOp W ∘L clean = clean ∘L lookup tab := by
  have hU := (writerOp_unitary (n := n) (Z := Z) W hWu).1
  rw [star_eq_adjoint, mul_def] at hU
  rw [adder_writer_clean W c tab hW, ← comp_assoc, hU, one_def, id_comp]

/-- The writer family: the supplied locators with the scratch register a spectator, and the
supplied writer `W x` on the address and scratch registers. -/
def writerOracles (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z) :
    WQuery → X → Space n Z →L[ℂ] Space n Z
  | .row, x => WeightedClock.diagonal (fun _ : Z => oracles D .rowLocation x)
  | .column, x => WeightedClock.diagonal (fun _ : Z => oracles D .columnLocation x)
  | .writer, x => writerOp (W x)

omit [DecidableEq Z] in
theorem writerOracles_unitary (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (m : WQuery) (x : X) : IsUnitary (writerOracles D W m x) := by
  cases m with
  | row => exact CoherentQuerySchedule.diagonal_unitary _ (fun _ => oracles_unitary D _ x)
  | column => exact CoherentQuerySchedule.diagonal_unitary _ (fun _ => oracles_unitary D _ x)
  | writer => exact writerOp_unitary _ (hWu x)

/-- One locator call for each locator; writer, adder and inverse writer for the value call. -/
def circuits (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z) :
    Query → MultiOracleCircuit.Program (writerOracles D W)
  | .rowLocation => .query .row
  | .columnLocation => .query .column
  | .value => .seq (.queryAdjoint .writer) (.seq (.fixed adder adder_unitary) (.query .writer))

/-- The weighted cost of each primitive call: one locator call, or two writer calls. -/
def wcost : Query → (WQuery → ℕ) → ℕ
  | .rowLocation, w => w .row
  | .columnLocation, w => w .column
  | .value, w => w .writer + w .writer

omit [DecidableEq Z] in
theorem circuits_cost (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z) (l : Query)
    (w : WQuery → ℕ) : (circuits D W l).cost w = wcost l w := by
  cases l <;> simp [circuits, wcost]

/-- Every primitive call is implemented on the clean scratch register. -/
theorem circuits_intertwines (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1) (l : Query) (x : X) :
    (circuits D W l).eval x ∘L clean = clean ∘L oracles D l x := by
  cases l with
  | rowLocation => exact diagonal_clean _
  | columnLocation => exact diagonal_clean _
  | value =>
    change (star (writerOp (W x)) * (adder * writerOp (W x))) ∘L clean = clean ∘L lookup (D.table x)
    rw [star_eq_adjoint, mul_def, mul_def]
    simpa only [comp_assoc] using convert_clean (W x) (hWu x) (c x) (D.table x) (hW x)

end Primitive

/-! ### Implementations of whole families of calls on a fixed encoding -/

section Impl
variable {K K' K₂ : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]
  {X L M : Type*}

/-- `circ l` implements the call `O l` exactly on the fixed isometric encoding `E`, over the
unitary family `Ow`, at the weighted cost `c l`. -/
structure Impl (O : L → X → K →L[ℂ] K) (Ow : M → X → K' →L[ℂ] K') (E : K →L[ℂ] K')
    (circ : L → MultiOracleCircuit.Program Ow) (c : L → (M → ℕ) → ℕ) : Prop where
  iso : E† ∘L E = 1
  unitary : ∀ l x, IsUnitary (O l x)
  unitaryW : ∀ m x, IsUnitary (Ow m x)
  intertwines : ∀ l x, (circ l).eval x ∘L E = E ∘L O l x
  cost : ∀ l w, (circ l).cost w = c l w

/-- The same program in every branch of a finite index. -/
def diagProg (ι : Type*) [Fintype ι] {Ow : M → X → K' →L[ℂ] K'} :
    MultiOracleCircuit.Program Ow →
      MultiOracleCircuit.Program (fun m x => WeightedClock.diagonal (fun _ : ι => Ow m x))
  | .fixed U hU => .fixed _
      (CoherentQuerySchedule.diagonal_unitary (fun _ : ι => U) (fun _ => hU))
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (diagProg ι p) (diagProg ι q)

@[simp] theorem diagProg_cost (ι : Type*) [Fintype ι] {Ow : M → X → K' →L[ℂ] K'}
    (p : MultiOracleCircuit.Program Ow) (w : M → ℕ) :
    (diagProg ι p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [diagProg, MultiOracleCircuit.Program.cost_seq, hp, hq]

theorem diagProg_eval (ι : Type*) [Fintype ι] {Ow : M → X → K' →L[ℂ] K'}
    (p : MultiOracleCircuit.Program Ow) (x : X) :
    (diagProg ι p).eval x = WeightedClock.diagonal (fun _ : ι => p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact WeightedClock.diagonal_adjoint _
  | seq p q hp hq =>
    simp only [diagProg, MultiOracleCircuit.Program.eval_seq, hp, hq]
    exact WeightedClock.diagonal_comp _ _

/-- The diagonal embedding over a finite index, a unital star-algebra homomorphism: the other
branches are spectators. -/
def diagHom (ι : Type*) [Fintype ι] :
    (K' →L[ℂ] K') →⋆ₐ[ℂ] (PiLp 2 (fun _ : ι => K') →L[ℂ] PiLp 2 (fun _ : ι => K')) where
  toFun A := WeightedClock.diagonal (fun _ : ι => A)
  map_one' := WeightedClock.diagonal_one
  map_mul' A B := (WeightedClock.diagonal_comp (fun _ : ι => A) (fun _ => B)).symm
  map_zero' := by ext; rfl
  map_add' A B := by ext; rfl
  commutes' r := by
    ext v i
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := (WeightedClock.diagonal_adjoint (fun _ : ι => A)).symm

theorem diagHom_apply (ι : Type*) [Fintype ι] (A : K' →L[ℂ] K') :
    diagHom (K' := K') ι A = WeightedClock.diagonal (fun _ : ι => A) := rfl

namespace Impl
variable {O : L → X → K →L[ℂ] K} {Ow : M → X → K' →L[ℂ] K'} {E : K →L[ℂ] K'}
  {circ : L → MultiOracleCircuit.Program Ow} {c : L → (M → ℕ) → ℕ}

theorem congr (h : Impl O Ow E circ c) {O' : L → X → K →L[ℂ] K}
    (hO : ∀ l x, O l x = O' l x) : Impl O' Ow E circ c := by
  have hO' : O = O' := funext fun l => funext fun x => hO l x
  subst hO'
  exact h

/-- A fixed change of coordinates of the physical workspace. -/
theorem conj (h : Impl O Ow E circ c) (f : K ≃ₗᵢ[ℂ] K₂) :
    Impl (fun l x => f.conjStarAlgEquiv (O l x)) Ow
      (E ∘L f.symm.toLinearIsometry.toContinuousLinearMap) circ c where
  iso := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc (E†), h.iso, one_def, id_comp]
    exact LinearIsometry.adjoint_comp_self _
  unitary l x := (h.unitary l x).transport f
  unitaryW := h.unitaryW
  intertwines l x := by
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun T : K →L[ℂ] K' => T (f.symm v)) (h.intertwines l x)
    simp only [comp_apply] at hv
    simp only [comp_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
      LinearIsometryEquiv.symm_apply_apply]
    exact hv
  cost := h.cost

/-- Diagonal over a finite index. -/
theorem diag (h : Impl O Ow E circ c) (ι : Type*) [Fintype ι] :
    Impl (fun l x => WeightedClock.diagonal (fun _ : ι => O l x))
      (fun m x => WeightedClock.diagonal (fun _ : ι => Ow m x))
      (FiniteReferenceLift.lift (R := ι) E) (fun l => diagProg ι (circ l)) c where
  iso := FiniteReferenceLift.lift_isometry E h.iso
  unitary l x := CoherentQuerySchedule.diagonal_unitary _ (fun _ => h.unitary l x)
  unitaryW m x := CoherentQuerySchedule.diagonal_unitary _ (fun _ => h.unitaryW m x)
  intertwines l x := by
    rw [diagProg_eval, ← FiniteReferenceLift.lift_eq_diagonal,
      ← FiniteReferenceLift.lift_eq_diagonal, FiniteReferenceLift.lift_comp, h.intertwines,
      ← FiniteReferenceLift.lift_comp]
  cost l w := by rw [diagProg_cost, h.cost]

/-- Fixed spectator registers (`LookupFromBasisOracle.spectator`). -/
theorem spectator {B : Type*} [Fintype B] [DecidableEq B] (S : Type*) [Fintype S]
    {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B}
    {E : EuclideanSpace ℂ B →L[ℂ] K'} (h : Impl F Ow E circ c) :
    Impl (fun l x => LookupFromBasisOracle.spectator (S := S) (F l x))
      (fun m x => WeightedClock.diagonal (fun _ : S => Ow m x))
      (FiniteReferenceLift.lift (R := S) E ∘L
        (RegisterEquivalences.productFlatten S B).symm.toLinearIsometry.toContinuousLinearMap)
      (fun l => diagProg S (circ l)) c :=
  (h.diag S).conj (RegisterEquivalences.productFlatten S B)

/-- The masked native layer of `NativeMaskedProgram.oracle` (all branches active, the control,
dummy and reference registers spectators). -/
theorem maskedProgram {B : Type*} [Fintype B] [DecidableEq B] (ι : Type*) [Fintype ι]
    {F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B}
    {E : EuclideanSpace ℂ B →L[ℂ] K'} (h : Impl F Ow E circ c) :
    Impl (NativeMaskedProgram.oracle (ι := ι) F)
      (fun m x => WeightedClock.diagonal (fun _ : ι =>
        WeightedClock.diagonal (fun _ : (Bool × B) × B => Ow m x)))
      (FiniteReferenceLift.lift (R := ι) (FiniteReferenceLift.lift (R := (Bool × B) × B) E ∘L
        (RegisterEquivalences.productFlatten ((Bool × B) × B) B).symm.toLinearIsometry.toContinuousLinearMap))
      (fun l => diagProg ι (diagProg ((Bool × B) × B) (circ l))) c := by
  refine ((h.spectator ((Bool × B) × B)).diag ι).congr fun l x => ?_
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rfl

end Impl

/-! ### Transfer of a whole program -/

/-- Every call of a program over `O` replaced by its implementation: the compiled program over
`Ow` acts as the program on the encoding, at the weighted cost of its calls. -/
theorem transfer {O : L → X → K →L[ℂ] K} {Ow : M → X → K' →L[ℂ] K'} {E : K →L[ℂ] K'}
    {circ : L → MultiOracleCircuit.Program Ow} {c : L → (M → ℕ) → ℕ}
    (h : Impl O Ow E circ c) (p : MultiOracleCircuit.Program O) :
    (∀ w, (EncodedLabeledProgram.compile E h.iso circ p).cost w = p.cost (fun l => c l w)) ∧
    (∀ x, (EncodedLabeledProgram.compile E h.iso circ p).eval x ∘L E = E ∘L p.eval x) ∧
    (∀ x, IsUnitary ((EncodedLabeledProgram.compile E h.iso circ p).eval x)) := by
  refine ⟨fun w => ?_, fun x => ?_, fun x => ?_⟩
  · rw [EncodedLabeledProgram.compile_cost]
    simp only [h.cost]
  · exact EncodedLabeledProgram.compile_eval E h.iso circ h.unitaryW h.unitary h.intertwines p x
  · exact (EncodedLabeledProgram.compile E h.iso circ p).eval_unitary h.unitaryW x

/-- The norm of an encoded vector. -/
theorem norm_encode {E : K →L[ℂ] K'} (hE : E† ∘L E = 1) (v : K) : ‖E v‖ = ‖v‖ :=
  (E.norm_map_iff_adjoint_comp_self).mpr hE v

/-- The full-output error passes to the compiled program on the encoded input. -/
theorem fullOutputError_encode {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    {A : K →L[ℂ] K} {A' : K' →L[ℂ] K'} {E : K →L[ℂ] K'} (hE : E† ∘L E = 1)
    (hA : A' ∘L E = E ∘L A) {J : P →L[ℂ] K} {V : P →L[ℂ] P} {ε : ℝ}
    (h : ManuscriptConformance.FullOutputError A J V ε) :
    ManuscriptConformance.FullOutputError A' (E ∘L J) V ε := by
  intro ψ hψ
  have e : A' ((E ∘L J) ψ) - (E ∘L J) (V ψ) = E (A (J ψ) - J (V ψ)) := by
    rw [map_sub]
    exact congrArg (· - E (J (V ψ))) (congrArg (fun T : K →L[ℂ] K' => T (J ψ)) hA)
  rw [e, norm_encode hE]
  exact h ψ hψ

/-- The same with an untouched reference register. -/
theorem referenceOutputError_encode {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    (R : Type) [Fintype R]
    {A : K →L[ℂ] K} {A' : K' →L[ℂ] K'} {E : K →L[ℂ] K'} (hE : E† ∘L E = 1)
    (hA : A' ∘L E = E ∘L A) {J : P →L[ℂ] K} {V : P →L[ℂ] P} {ε : ℝ}
    (h : ManuscriptConformance.ReferenceOutputError R A J V ε) :
    ManuscriptConformance.ReferenceOutputError R A' (E ∘L J) V ε := by
  intro ψ hψ
  have hL : FiniteReferenceLift.lift (R := R) A' ∘L FiniteReferenceLift.lift E =
      FiniteReferenceLift.lift E ∘L FiniteReferenceLift.lift A := by
    rw [FiniteReferenceLift.lift_comp, hA, ← FiniteReferenceLift.lift_comp]
  have e : FiniteReferenceLift.lift A' (FiniteReferenceLift.lift (E ∘L J) ψ) -
      FiniteReferenceLift.lift (E ∘L J) (FiniteReferenceLift.lift V ψ) =
      FiniteReferenceLift.lift E (FiniteReferenceLift.lift A (FiniteReferenceLift.lift J ψ) -
        FiniteReferenceLift.lift J (FiniteReferenceLift.lift V ψ)) := by
    rw [← FiniteReferenceLift.lift_comp, map_sub]
    congr 1
    exact congrArg (fun T => T (FiniteReferenceLift.lift J ψ)) hL
  rw [e, norm_encode (FiniteReferenceLift.lift_isometry E hE)]
  exact h ψ hψ

end Impl

/-! ### The primitive implementation and the flattened primitives -/

section Base
variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- The writer implementation of the primitive sparse calls. -/
theorem impl_writer (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1) :
    Impl (oracles D) (writerOracles D W) clean (circuits D W) wcost where
  iso := clean_isometry
  unitary l x := oracles_unitary D l x
  unitaryW := writerOracles_unitary D W hWu
  intertwines := circuits_intertwines D W hWu c hW
  cost := circuits_cost D W

/-- The same for the flattened primitives `NativeSparseMaskedAccess.flatOracle`. -/
theorem impl_flat (D : Data X n Z s) (W : X → WReg n Z →L[ℂ] WReg n Z)
    (hWu : ∀ x, IsUnitary (W x)) (c : X → n × n → ℂ)
    (hW : ∀ x a, W x (EuclideanSpace.single (a, (0 : Z)) 1) =
      c x a • EuclideanSpace.single (a, D.table x a) 1) :
    Impl (NativeSparseMaskedAccess.flatOracle D) (writerOracles D W)
      (clean ∘L (NativeSparseMaskedAccess.layout (n := n) (Z := Z)).symm.toLinearIsometry.toContinuousLinearMap)
      (circuits D W) wcost :=
  (impl_writer D W hWu c hW).conj NativeSparseMaskedAccess.layout

/-- The weighted cost of the converted calls, label by label: one row call per row call, one
column call per column call, two writer calls per value call. -/
theorem cost_wcost {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {Xo : Type*} {O : Query → Xo → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (w : WQuery → ℕ) :
    p.cost (fun l => wcost l w) = w .row * p.labelCount .rowLocation +
      w .column * p.labelCount .columnLocation + 2 * w .writer * p.labelCount .value := by
  induction p with
  | fixed U hU => simp [MultiOracleCircuit.Program.labelCount]
  | query l => cases l <;> simp [MultiOracleCircuit.Program.labelCount, wcost, two_mul]
  | queryAdjoint l => cases l <;> simp [MultiOracleCircuit.Program.labelCount, wcost, two_mul]
  | seq p q hp hq =>
    simp only [MultiOracleCircuit.Program.cost_seq, MultiOracleCircuit.Program.labelCount] at hp hq ⊢
    rw [hp, hq]
    ring

/-- At most twice the calls. -/
theorem cost_wcost_one_le {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {Xo : Type*} {O : Query → Xo → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) :
    p.cost (fun l => wcost l (fun _ => 1)) ≤ 2 * p.count := by
  induction p with
  | fixed U hU => simp
  | query l => cases l <;> simp [wcost]
  | queryAdjoint l => cases l <;> simp [wcost]
  | seq p q hp hq =>
    simp only [MultiOracleCircuit.Program.cost_seq, MultiOracleCircuit.Program.count_seq]
    omega

end Base

end
end SparseHamiltonian.WriterAccess
