import TimeDependentLowerBoundExtensions.Measured.Assembly
import TimeDependentLowerBoundExtensions.BlockEncoding.Access
import SparseHamiltonian.NativeHermitianDilation

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Block-encoding calls as fixed products of native calls

The time-indexed block-encoding model (eqs. `hs:eq:blockspecial`, `hs:eq:blockadditive` of the
manuscript: coherent and
controlled access to Hermitian unitaries `O_r` with `J† O_r J = H̃_r / α_BE`) on the hard instances
of Theorem `hsl:thm:main`: every sample is `beOp D x`, the Hermitian dilation `diag(W, W†) ∘ swap`
of the released six-query block encoding `W = (program D).eval x`
(`TimeDependentLowerBoundExtensions.BlockEncoding.beOp`).

* `beSector D (q, b)`: the native query `q` in the sector `b` of the dilation qubit (the identity
  in the other sector), in the coordinates `beLayout`; admissible with the value-query weight
  (`admissible_beSector`).
* `beProgram D`: the program over `beSector D` that runs `W†` in the sector `false`, the fixed
  swap and `W` in the sector `false`, the factorisation
  `SparseHamiltonian.NativeHermitianDilation.masked_swap` of the dilation; it computes `beOp D x`
  exactly on the same space (`eval_beProgram`) with `8` value calls (`cost_beProgram`: four in
  `W`, four in `W†`).
* `nativeCompiles_beOp`, `nativeCompiles_primitive`, `nativeCompiles_aligned`,
  `nativeCompiles_calls_aligned`: native compilations of cost `8` of `beOp D`, of the controlled
  time-indexed oracle `TimeDependentExtensions.BlockEncoding.primitive (beConst D M)` (a control
  mask), of the released aligned family `TimeDependentExtensions.BlockEncoding.alignedOracle`
  (a spectator wrapper, `beWrap`) and of its call forms.
-/

namespace TimeDependentLowerBoundExtensions.Measured

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds
open TimeDependentLowerBoundExtensions.BlockEncoding
open AdaptiveHamiltonianLowerBound.Access (Admissible valueWeight)
open scoped InnerProduct InnerProductSpace

variable {X : Type} {N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- The sector map: an operator on the native space placed in the sector `b` of the dilation
qubit, the identity in the other sector, in the coordinates `beLayout`. -/
def sectorLift (N Z : Type) [Fintype N] [Fintype Z] (b : Bool)
    (A : SparseFlagEmbedding.Space (N × N) Z →L[ℂ] SparseFlagEmbedding.Space (N × N) Z) :
    EuclideanSpace ℂ (BEBasis N Z) →L[ℂ] EuclideanSpace ℂ (BEBasis N Z) :=
  (beLayout N Z).symm.conjStarAlgEquiv (MaskedProgram.masked (fun c : Bool => c == b) A)

omit [DecidableEq N] [AddCommGroup Z] [DecidableEq Z] in
/-- The sector map is a masked lift. -/
theorem isMaskedLift_sectorLift (b : Bool) : IsMaskedLift (sectorLift N Z b) :=
  (isMaskedLift_masked Bool (fun c : Bool => c == b)).conj (beLayout N Z).symm

/-- **The sector family**: the native query `q` in the sector `b` of the dilation qubit. -/
def beSector (D : Data X N Z s) :
    Query × Bool → X → EuclideanSpace ℂ (BEBasis N Z) →L[ℂ] EuclideanSpace ℂ (BEBasis N Z) :=
  fun c x => sectorLift N Z c.2 (oracles D c.1 x)

omit [DecidableEq Z] in
/-- **The sector family is admissible** with the value-query weight, for data with
input-independent locators. -/
theorem admissible_beSector (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (c : Query × Bool) :
    Admissible D (beSector D c) (valueWeight c.1) :=
  (isMaskedLift_sectorLift c.2).admissible (AdaptiveHamiltonianLowerBound.Access.admissible_oracles D hrow hcol c.1)

omit [DecidableEq N] [AddCommGroup Z] [DecidableEq Z] in
/-- The fixed swap of the dilation qubit in the coordinates `beLayout` is unitary. -/
theorem beSwap_unitary :
    IsUnitary ((beLayout N Z).symm.conjStarAlgEquiv
      (HermitianDilation.swap :
        HermitianDilation.Double (SparseFlagEmbedding.Space (N × N) Z) →L[ℂ] _)) :=
  HermitianDilation.swap_unitary.transport (beLayout N Z).symm

/-- **The block-encoding program**: in time order, `W†` in the sector `false`, the fixed swap,
and `W` in the sector `false` (the factorisation
`SparseHamiltonian.NativeHermitianDilation.masked_swap` of the dilation). -/
def beProgram (D : Data X N Z s) : MultiOracleCircuit.Program (beSector D) :=
  .seq (.seq (liftProgram (isMaskedLift_sectorLift false) (fun q => (q, false)) (program D))
      (.fixed _ beSwap_unitary))
    (liftProgram (isMaskedLift_sectorLift false) (fun q => (q, false)) (program D).adjoint)

omit [DecidableEq Z] in
/-- **The block-encoding program computes `beOp D x`** on every input. -/
theorem eval_beProgram (D : Data X N Z s) (x : X) : (beProgram D).eval x = beOp D x := by
  rw [beProgram, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_seq,
    eval_liftProgram (isMaskedLift_sectorLift false) (fun q => (q, false)) (fun _ _ => rfl),
    eval_liftProgram (isMaskedLift_sectorLift false) (fun q => (q, false)) (fun _ _ => rfl),
    MultiOracleCircuit.Program.eval_adjoint, MultiOracleCircuit.Program.eval_fixed]
  simp only [sectorLift, beOp, ← map_mul]
  congr 1
  have hm : (fun c : Bool => c == false) = (fun b : Bool => !b) := by
    funext c
    cases c <;> rfl
  rw [hm, ← NativeHermitianDilation.masked_swap, MaskedProgram.masked_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint]
  rfl

omit [DecidableEq Z] in
/-- **The block-encoding program makes `8` value calls** (four in `W`, four in `W†`). -/
theorem cost_beProgram (D : Data X N Z s) :
    (beProgram D).cost (fun c => valueWeight c.1) = 8 := by
  simp only [beProgram, MultiOracleCircuit.Program.cost_seq, cost_liftProgram,
    MultiOracleCircuit.Program.cost_adjoint, MultiOracleCircuit.Program.cost_fixed, program_cost]
  rfl

omit [DecidableEq Z] in
/-- **Native compilation of the dilated block encoding**, cost `8`. -/
theorem nativeCompiles_beOp (D : Data X N Z s) (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') :
    NativeCompiles D (fun (_ : Unit) (x : X) => beOp D x) 8 :=
  ⟨Query × Bool, beSector D, fun c => valueWeight c.1, fun _ => beProgram D,
    admissible_beSector D hrow hcol, fun _ x => eval_beProgram D x,
    fun _ => (cost_beProgram D).le⟩

/-- **Native compilation of the controlled time-indexed oracle of the constant family**
(`|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`, any number `M` of samples), cost `8`. -/
theorem nativeCompiles_primitive (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M : ℕ) :
    NativeCompiles D (TimeDependentExtensions.BlockEncoding.primitive (beConst D M)) 8 := by
  have h := (nativeCompiles_beOp D hrow hcol).map
    ((isMaskedLift_masked (Bool × Fin M) (fun c : Bool × Fin M => c.1)).conj
      (TimeDependentExtensions.BlockEncoding.layout (BEBasis N Z) M))
  exact h

/-- **Native compilation of the released aligned block-encoding family of the constant family**
(any number `M` of samples, slot count `Nsl` and schedule), cost `8`. -/
theorem nativeCompiles_aligned (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M Nsl : ℕ) (α T ε : ℝ) :
    NativeCompiles D
      (TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) Nsl α T ε) 8 := by
  have h := (nativeCompiles_primitive D hrow hcol M).map
    (isMaskedLift_of_isWrap (isWrap_beWrap (B₀ := BEBasis N Z) M Nsl
      (TimeDependentExtensions.BlockEncoding.degree Nsl α T ε)))
  exact h

/-- **Native compilation of all call forms of the released aligned block-encoding family**,
cost `8`. -/
theorem nativeCompiles_calls_aligned (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M Nsl : ℕ) (α T ε : ℝ) :
    NativeCompiles D (AdaptiveODELowerBound.Access.callFamily
      (TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) Nsl α T ε)) 8 :=
  (nativeCompiles_aligned D hrow hcol M Nsl α T ε).callFamily

end

end TimeDependentLowerBoundExtensions.Measured
