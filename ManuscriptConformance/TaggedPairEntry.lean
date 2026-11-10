import SparseODE.ODENativeCayley

/-!
# Lemma `ode:lem:tags`: the native circuit for an arbitrary supported pair entry

`SparseODE.ODENativeCayley.program` implements the tagged Cayley action only for the LCHS
branches `K_k = H + kD`. Here the entry rule is an arbitrary public function `f i j (G i j) (G j i)`
of the two original entries and the known edge `(i, j)`: Lemma `ode:lem:tags` asks only that `K`
be computable from `G_ij`, `G_ji` and known data.

The circuit is the same as before with the scalar arithmetic of `f` in place of the LCHS entry:
the original row, column and value calls are unchanged (`24` native calls: `6` row, `6` column and
`12` value calls), the tag and both value words are restored, and the clean encoding is
independent of the unknown matrix, of `f` and of the Cayley parameters. `pairMatrix_lchsRule`
shows that `K_k = H + kD` is the instance `f = lchsRule k`.

The moment bounds with `p = 2s` need only that `K` is Hermitian and vanishes outside
`supp(G) ∪ supp(G†)` (`ODEFixedTaggedMoments.native_moment_certificate`); for the rule they follow
from `f i j 0 0 = 0` and `f j i v u = star (f i j u v)` (`pairMatrix_support`,
`pairMatrix_isHermitian`). The exact action itself needs neither.
-/

namespace SparseHamiltonian.ODETaggedPairEntry

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding ODETaggedValueDecoder
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- A public rule computing the entry `(i, j)` of `K` from the two original entries
`G i j`, `G j i` and the known edge. -/
abbrev PairRule (n : Type*) := n → n → ℂ → ℂ → ℂ

section Matrix
variable {n : Type*}

/-- The matrix computed entrywise by the rule. -/
def pairMatrix (f : PairRule n) (M : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => f i j (M i j) (M j i)

@[simp] theorem pairMatrix_apply (f : PairRule n) (M : Matrix n n ℂ) (i j : n) :
    pairMatrix f M i j = f i j (M i j) (M j i) := rfl

/-- A rule vanishing on two zero entries gives a matrix supported on
`supp(G) ∪ supp(G†)`. -/
theorem pairMatrix_support (f : PairRule n) (hf : ∀ i j, f i j 0 0 = 0)
    (M : Matrix n n ℂ) (i j : n) (h₀ : M i j = 0) (h₁ : M j i = 0) :
    pairMatrix f M i j = 0 := by
  rw [pairMatrix_apply, h₀, h₁, hf]

/-- A conjugate-symmetric rule gives a Hermitian matrix. -/
theorem pairMatrix_isHermitian (f : PairRule n)
    (hf : ∀ i j u v, f j i v u = star (f i j u v)) (M : Matrix n n ℂ) :
    (pairMatrix f M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [pairMatrix_apply]
  rw [hf i j (M i j) (M j i), star_star]

/-- The LCHS branch rule. -/
def lchsRule (k : ℝ) : PairRule n := fun _ _ u v => entry k u v

theorem lchsRule_zero (k : ℝ) (i j : n) : lchsRule k i j 0 0 = 0 := by
  simp [lchsRule, entry]

theorem lchsRule_conj (k : ℝ) (i j : n) (u v : ℂ) :
    lchsRule k j i v u = star (lchsRule k i j u v) := by
  simp only [lchsRule, entry, star_add, star_mul', star_div₀, Complex.star_def,
    map_sub, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.conj_conj]
  ring

/-- `K_k = H + kD` is the instance `f = lchsRule k`. -/
theorem pairMatrix_lchsRule (k : ℝ) (M : Matrix n n ℂ) :
    pairMatrix (lchsRule k) M = ODEMatrixEnergy.lchsHamiltonian M k := by
  ext i j
  rw [pairMatrix_apply, ODEMatrixEnergy.lchsHamiltonian_entry]
  rfl

end Matrix

section Decoder
variable {n : Type*}

/-- An entry shared by both supports is split in half; absent supports vanish. -/
def taggedEntry (f : PairRule n) (e : n × n) (a : Bool) (u v : ℂ) : ℂ :=
  if a then
    if v = 0 then 0 else if u = 0 then f e.1 e.2 u v else f e.1 e.2 u v / 2
  else
    if u = 0 then 0 else if v = 0 then f e.1 e.2 u v else f e.1 e.2 u v / 2

/-- The public scalar arithmetic reproduces the verified tagged matrix of the rule,
including cancellation and unmatched zero padding. -/
theorem taggedEntry_eq (M : Matrix n n ℂ) (f : PairRule n) (a : Bool) (i j : n) :
    taggedEntry f (i, j) a (M i j) (M j i) =
      ODETaggedSupport.tagValue M (pairMatrix f M) a i j := by
  cases a <;> by_cases h₀ : M i j = 0 <;> by_cases h₁ : M j i = 0 <;>
    simp only [taggedEntry, ODETaggedSupport.tagValue,
      ODETaggedSupport.tagZero, ODETaggedSupport.tagOne, pairMatrix_apply, h₀, h₁,
      Bool.false_eq_true, if_false, if_true]

variable [Fintype n] [DecidableEq n] {X Z : Type*} {s : ℕ}

/-- Unknown data enter only through the two value words; the rule and the edge are public. -/
def decodedEntry (D : Data X n Z s) (f : PairRule n) (a : Address n) (u v : Z) : ℂ :=
  taggedEntry f (edge a) (tag a) (D.decode (edge a) v) (D.decode (edge a).swap u)

/-- The exact tagged entry of the rule selected by an actual input instance. -/
def actualEntry (D : Data X n Z s) (f : PairRule n) (x : X) (a : Address n) : ℂ :=
  ODETaggedSupport.tagValue (D.matrix x) (pairMatrix f (D.matrix x))
    (tag a) (edge a).1 (edge a).2

theorem decodedEntry_correct (D : Data X n Z s) (f : PairRule n) (x : X) (a : Address n) :
    decodedEntry D f a (table D x (exchange n a)) (table D x a) = actualEntry D f x a := by
  unfold decodedEntry table actualEntry
  rw [edge_exchange]
  rcases h : edge a with ⟨i, j⟩
  change taggedEntry f (i, j) (tag a) (D.decode (i, j) (D.table x (i, j)))
      (D.decode (j, i) (D.table x (j, i))) =
    ODETaggedSupport.tagValue (D.matrix x) (pairMatrix f (D.matrix x)) (tag a) i j
  rw [D.decoded, D.decoded]
  exact taggedEntry_eq (D.matrix x) f (tag a) i j

/-- Exact rotation for every pair of codes, including dirty scratch inputs. -/
def gates (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (a : Address n) (u v : Z) :
    ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit :=
  ExactEdgeCayley.action ((scale s γ ρ : ℂ) * decodedEntry D f a u v)

theorem gates_unitary (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ)
    (a : Address n) (u v : Z) : IsUnitary (gates D f γ ρ a u v) :=
  ExactEdgeCayley.action_unitary _

theorem gates_correct (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) (a : Address n) :
    gates D f γ ρ a (table D x (exchange n a)) (table D x a) =
      ExactEdgeCayley.action ((scale s γ ρ : ℂ) * actualEntry D f x a) := by
  unfold gates
  rw [decodedEntry_correct]

/-- The LCHS gates are the gates of `lchsRule k`. -/
theorem gates_lchsRule (D : Data X n Z s) (k γ ρ : ℝ) :
    gates D (lchsRule k) γ ρ = ODETaggedValueDecoder.gates D k γ ρ := rfl

end Decoder

section Value
variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Compute both entries, rotate, and uncompute, over the original additive lookup. -/
def valueProgram (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    Program (ODETaggedValueProgram.oracle D) :=
  ODEPairedValueQuery.program (exchange n) (gates D f γ ρ)
    (gates_unitary D f γ ρ) (table D)

omit [DecidableEq Z] in
theorem valueProgram_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (valueProgram D f γ ρ).count = 4 :=
  ODEPairedValueQuery.program_count (exchange n) (gates D f γ ρ)
    (gates_unitary D f γ ρ) (table D)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem actualEntry_eq_entries (D : Data X n Z s) (f : PairRule n) (x : X) (a : Address n) :
    actualEntry D f x a =
      ODETaggedCayley.entries (D.matrix x) (pairMatrix f (D.matrix x)) a := by
  cases a <;> rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem scaledEntry_correct (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X)
    (a : Address n) :
    (scale s γ ρ : ℂ) * actualEntry D f x a =
      ODETaggedCayley.scaledEntries (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ a := by
  have hscale : scale s γ ρ = γ * (Real.sqrt (2 * (s : ℝ)) / ρ) := by
    unfold scale
    ring
  rw [actualEntry_eq_entries, hscale]
  rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem logical_eq_diagonal (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    ODEPairedValueQuery.logical (exchange n) (gates D f γ ρ) (table D) x =
      WeightedClock.diagonal (fun a => ExactEdgeCayley.action
        (ODETaggedCayley.scaledEntries (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ a)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro a
  simp only [ODEPairedValueQuery.logical_apply, WeightedClock.diagonal_apply,
    gates_correct, scaledEntry_correct]

/-- Exact encoded correctness of the four value queries; both value registers return to zero. -/
theorem valueProgram_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (valueProgram D f γ ρ).eval x ∘L
        (ODETaggedValueProgram.clean (n := n) (Z := Z)).toContinuousLinearMap =
      (ODETaggedValueProgram.clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        ODETaggedCayley.action (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg
    (fun F : ODEPairedValueQuery.Public (Address n) ExactEdgeCayley.Qubit →L[ℂ]
        ODETaggedValueProgram.Space n Z => F (ODETaggedCayley.regroup v))
    (ODEPairedValueQuery.program_intertwines (exchange n) (gates D f γ ρ)
      (gates_unitary D f γ ρ) (table D) x)
  change (valueProgram D f γ ρ).eval x (ODETaggedValueProgram.clean v) = _ at h
  rw [logical_eq_diagonal] at h
  change (valueProgram D f γ ρ).eval x (ODETaggedValueProgram.clean v) =
    ODETaggedValueProgram.clean
      (ODETaggedCayley.action (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ v)
  change (valueProgram D f γ ρ).eval x (ODETaggedValueProgram.clean v) =
    ODEPairedValueQuery.clean (ODETaggedCayley.regroup
      (ODETaggedCayley.action (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ v))
  rw [ODETaggedCayley.regroup_action]
  exact h

omit [DecidableEq Z] in
/-- Reinterpreting identical oracle operators changes no evaluated gate. -/
private theorem retarget_eval (D : Data X n Z s)
    (p : Program (fun x => (ODETaggedValueOracle.layout (n := n) (Z := Z)).conjStarAlgEquiv
      (ODETaggedValueProgram.oracle D x))) (x : X) :
    (p.retarget (ODETaggedValueOracle.oracle D)).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => exact (ODETaggedValueOracle.oracle_conjugate D x).symm
  | queryAdjoint =>
    simp only [Program.retarget, Program.eval_queryAdjoint,
      ODETaggedValueOracle.oracle_conjugate]
  | seq p q hp hq =>
    simp only [Program.retarget, Program.eval_seq, hp, hq]

/-- The same fixed syntax on the original matrix-entry primitive, with the tag and the
first value word moved into its untouched payload. -/
def oracleProgram (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    Program (ODETaggedValueOracle.oracle D) :=
  ((valueProgram D f γ ρ).transport
    (ODETaggedValueOracle.layout (n := n) (Z := Z))).retarget (ODETaggedValueOracle.oracle D)

omit [DecidableEq Z] in
theorem oracleProgram_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (oracleProgram D f γ ρ).count = 4 := by
  rw [oracleProgram, Program.count_retarget, Program.count_transport, valueProgram_count]

omit [DecidableEq Z] in
theorem oracleProgram_eval (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (oracleProgram D f γ ρ).eval x =
      ODETaggedValueOracle.layout.conjStarAlgEquiv ((valueProgram D f γ ρ).eval x) := by
  rw [oracleProgram, retarget_eval, Program.eval_transport]

theorem oracleProgram_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (oracleProgram D f γ ρ).eval x ∘L
        (ODETaggedValueOracle.clean (n := n) (Z := Z)).toContinuousLinearMap =
      (ODETaggedValueOracle.clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        ODETaggedCayley.action (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ := by
  rw [oracleProgram_eval]
  apply ContinuousLinearMap.ext
  intro v
  change ODETaggedValueOracle.layout ((valueProgram D f γ ρ).eval x
      (ODETaggedValueOracle.layout.symm
        (ODETaggedValueOracle.layout (ODETaggedValueProgram.clean v)))) =
    ODETaggedValueOracle.layout (ODETaggedValueProgram.clean
      (ODETaggedCayley.action (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ v))
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact congrArg ODETaggedValueOracle.layout (congrArg
    (fun F : ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedValueProgram.Space n Z => F v)
    (valueProgram_intertwines D f γ ρ x))

/-- Lift the fixed gate syntax into the common locator/value workspace; every oracle letter
stays one native value query. -/
def singleProgram (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    OracleCircuit.Program (ODENativeLayout.logicalOracle D .value) :=
  EncodedOracle.compile
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).adjoint_comp_self
    (.query : OracleCircuit.Program (ODENativeLayout.logicalOracle D .value))
    (oracleProgram D f γ ρ)

omit [DecidableEq Z] in
theorem singleProgram_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (singleProgram D f γ ρ).count = 4 := by
  rw [singleProgram, EncodedOracle.compile_count, oracleProgram_count,
    OracleCircuit.Program.count_query]

omit [DecidableEq Z] in
theorem singleProgram_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (singleProgram D f γ ρ).eval x ∘L
        (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap =
      (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap ∘L
        (oracleProgram D f γ ρ).eval x := by
  exact EncodedOracle.compile_eval
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap
    (ODENativeLayout.valueEmbedding (n := n) (Z := Z)).adjoint_comp_self
    (.query : OracleCircuit.Program (ODENativeLayout.logicalOracle D .value))
    (fun x => ODENativeLayout.logicalOracle_unitary D .value x)
    (ODETaggedValueOracle.oracle_unitary D)
    (ODENativeLayout.value_intertwines D)
    (oracleProgram D f γ ρ) x

/-- Every occurrence of the original value primitive carries its literal label. -/
def nativeValueProgram (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    MultiOracleCircuit.Program (ODENativeLayout.logicalOracle D) :=
  MultiOracleCircuit.Program.embed .value (singleProgram D f γ ρ)

omit [DecidableEq Z] in
theorem nativeValueProgram_eval (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (nativeValueProgram D f γ ρ).eval x = (singleProgram D f γ ρ).eval x := by
  simp only [nativeValueProgram, MultiOracleCircuit.Program.eval_embed]

omit [DecidableEq Z] in
theorem nativeValueProgram_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (nativeValueProgram D f γ ρ).count = 4 := by
  rw [nativeValueProgram, MultiOracleCircuit.Program.count_embed, singleProgram_count]

omit [DecidableEq Z] in
theorem nativeValueProgram_cost (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ)
    (w : Query → ℕ) : (nativeValueProgram D f γ ρ).cost w = 4 * w .value := by
  rw [nativeValueProgram, MultiOracleCircuit.Program.cost_embed, singleProgram_count]

/-- The native value program realizes the exact tagged Cayley action of the rule on the
common clean encoding and restores all value work registers. -/
theorem nativeValueProgram_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (nativeValueProgram D f γ ρ).eval x ∘L
        (ODENativeValue.clean (n := n) (Z := Z)).toContinuousLinearMap =
      (ODENativeValue.clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        ODETaggedCayley.action (D.matrix x) (pairMatrix f (D.matrix x)) s ρ γ := by
  change (nativeValueProgram D f γ ρ).eval x ∘L
      ((ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap ∘L
        (ODETaggedValueOracle.clean (n := n) (Z := Z)).toContinuousLinearMap) =
    ((ODENativeLayout.valueEmbedding (n := n) (Z := Z)).toContinuousLinearMap ∘L
        (ODETaggedValueOracle.clean (n := n) (Z := Z)).toContinuousLinearMap) ∘L _
  rw [nativeValueProgram_eval, ← comp_assoc, singleProgram_intertwines, comp_assoc,
    oracleProgram_intertwines, comp_assoc]

end Value

section Native
variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Locate, compute both entries and rotate, then undo the locator transport. -/
def logicalProgram (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    MultiOracleCircuit.Program (ODENativeLayout.logicalOracle D) :=
  NativeCleanConjugation.program (ODENativeLocator.locatorProgram D)
    (nativeValueProgram D f γ ρ)

omit [DecidableEq Z] in
@[simp] theorem logicalProgram_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (logicalProgram D f γ ρ).count = 8 := by
  rw [logicalProgram, NativeCleanConjugation.program_count,
    ODENativeLocator.locatorProgram_count, nativeValueProgram_count]

omit [DecidableEq Z] in
@[simp] theorem logicalProgram_cost (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ)
    (w : Query → ℕ) :
    (logicalProgram D f γ ρ).cost w =
      2 * w .rowLocation + 2 * w .columnLocation + 4 * w .value := by
  rw [logicalProgram, NativeCleanConjugation.program_cost,
    ODENativeLocator.locatorProgram_cost, nativeValueProgram_cost]
  omega

/-- Exact clean action of the conjugated circuit on all tagged edges. -/
theorem logicalProgram_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (logicalProgram D f γ ρ).eval x ∘L
        (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap =
      (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap ∘L
        ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ := by
  have h := NativeCleanConjugation.program_intertwines
    (ODENativeLayout.logicalOracle_unitary D)
    (ODENativeLocator.locatorProgram D) (nativeValueProgram D f γ ρ)
    (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap
    (ODETaggedLocators.locator D)
    (fun y => ODETaggedCayley.action (D.matrix y) (pairMatrix f (D.matrix y)) s ρ γ)
    (ODETaggedLocators.locator_unitary D)
    (ODENativeLocator.locatorProgram_intertwines D)
    (nativeValueProgram_intertwines D f γ ρ) x
  simpa only [logicalProgram, ODEFixedTaggedMoments.action,
    UnitaryCayleyTransport.conjugate, star_eq_adjoint, mul_def, comp_assoc] using h

/-- Three ordinary native calls implement each controlled logical letter. -/
def compiledProgram (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    MultiOracleCircuit.Program
      (NativeMaskedProgram.oracle (ι := ODENativeLayout.Branch Z)
        (NativeSparseMaskedAccess.flatOracle D)) :=
  NativeMaskedProgram.compile (NativeSparseMaskedAccess.flatOracle D)
    (NativeSparseMaskedAccess.cleanBasis D) id ODENativeLayout.masks
    (logicalProgram D f γ ρ)

@[simp] theorem compiledProgram_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (compiledProgram D f γ ρ).count = 24 := by
  rw [compiledProgram, NativeMaskedProgram.compile_count, logicalProgram_count]

@[simp] theorem compiledProgram_cost (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ)
    (w : Query → ℕ) :
    (compiledProgram D f γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [compiledProgram, NativeMaskedProgram.compile_cost, logicalProgram_cost]
  simp only [id_eq]
  omega

/-- All coherent control is discharged by the original valid-slot promises. -/
theorem compiledProgram_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (compiledProgram D f γ ρ).eval x ∘L (ODENativeCayley.compiledClean D).toContinuousLinearMap =
      (ODENativeCayley.compiledClean D).toContinuousLinearMap ∘L
        ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ := by
  let E := (NativeMaskedOracle.input (ι := ODENativeLayout.Branch Z)
    (NativeSparseMaskedAccess.cleanBasis D)).toContinuousLinearMap
  let C := (ODENativeLayout.clean (n := n) (Z := Z)).toContinuousLinearMap
  have hp : (compiledProgram D f γ ρ).eval x ∘L E =
      E ∘L (logicalProgram D f γ ρ).eval x :=
    NativeSparseMaskedAccess.compile_eval D id ODENativeLayout.masks
      (logicalProgram D f γ ρ) x
  change (compiledProgram D f γ ρ).eval x ∘L (E ∘L C) =
    (E ∘L C) ∘L ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ
  calc
    _ = ((compiledProgram D f γ ρ).eval x ∘L E) ∘L C := by simp only [comp_assoc]
    _ = (E ∘L (logicalProgram D f γ ρ).eval x) ∘L C := by rw [hp]
    _ = E ∘L ((logicalProgram D f γ ρ).eval x ∘L C) := by simp only [comp_assoc]
    _ = E ∘L (C ∘L ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ) := by
      rw [logicalProgram_intertwines]
    _ = _ := by simp only [comp_assoc]

/-- The final literal program over the original row, column and value calls only. -/
def program (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    MultiOracleCircuit.Program (ODENativeCayley.oracle D) :=
  FlatBranchNativeAccess.flatten (NativeSparseMaskedAccess.flatOracle D)
    (compiledProgram D f γ ρ)

@[simp] theorem program_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (program D f γ ρ).count = 24 := by
  rw [program, FlatBranchNativeAccess.flatten_count, compiledProgram_count]

@[simp] theorem program_cost (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (w : Query → ℕ) :
    (program D f γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [program, FlatBranchNativeAccess.flatten_cost, compiledProgram_cost]

@[simp] theorem program_row_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (program D f γ ρ).labelCount .rowLocation = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

@[simp] theorem program_column_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (program D f γ ρ).labelCount .columnLocation = 6 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

@[simp] theorem program_value_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) :
    (program D f γ ρ).labelCount .value = 12 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  decide

/-- Exact full-output semantics, with every scratch register restored. -/
theorem program_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (program D f γ ρ).eval x ∘L (ODENativeCayley.clean D).toContinuousLinearMap =
      (ODENativeCayley.clean D).toContinuousLinearMap ∘L
        ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ :=
  FlatBranchNativeAccess.flatten_intertwines (NativeSparseMaskedAccess.flatOracle D)
    (compiledProgram D f γ ρ) (ODENativeCayley.compiledClean D)
    (ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ)
    x (compiledProgram_intertwines D f γ ρ x)

theorem program_unitary (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    IsUnitary ((program D f γ ρ).eval x) :=
  (program D f γ ρ).eval_unitary (ODENativeCayley.oracle_unitary D) x

/-- The literal adjoint circuit implements the inverse action at the same label counts. -/
theorem program_adjoint_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (x : X) :
    (program D f γ ρ).adjoint.eval x ∘L (ODENativeCayley.clean D).toContinuousLinearMap =
      (ODENativeCayley.clean D).toContinuousLinearMap ∘L
        (ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ)† := by
  rw [MultiOracleCircuit.Program.eval_adjoint]
  exact EncodedOracle.adjoint_intertwines _ _ _
    (program_unitary D f γ ρ x)
    (ODEFixedTaggedMoments.action_unitary D x (pairMatrix f (D.matrix x)) ρ γ)
    (program_intertwines D f γ ρ x)

theorem program_adjoint_cost (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (w : Query → ℕ) :
    (program D f γ ρ).adjoint.cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value := by
  rw [MultiOracleCircuit.Program.cost_adjoint, program_cost]

/-- The released LCHS circuit is literally the instance `f = lchsRule k`. -/
theorem program_lchsRule (D : Data X n Z s) (k γ ρ : ℝ) :
    program D (lchsRule k) γ ρ = ODENativeCayley.program D k γ ρ := rfl

end Native
end
end SparseHamiltonian.ODETaggedPairEntry
