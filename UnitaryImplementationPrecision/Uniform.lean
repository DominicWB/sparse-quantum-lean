import UnitaryImplementationPrecision.Inexact

/-!
# Corollary `hs:cor:unitary` with inexact entries, uniformly over the intended unitary

In the query model the circuit does not know the intended unitary `U`: it sees only the inexact
table. `implementation_inexact` already builds its program from the table and the public
parameters; this module states that reading directly. The inexact endpoint is applied to the
table read on the admissible pairs of an instance and a unitary within `ε/(π N)` entrywise of
its represented matrix (`Table.comap`); the oracle on a pair is the oracle on its instance, so
the same gate sequence, read over the original instances (`reindex`, `reindex_eval`,
`reindex_count`), is one program built from `T` and `ε` alone.

* `implementation_inexact_uniform`: one program over `inexactOracle T γ ε`, with at most
  `995328 π (√N + √(N ℓ) + ℓ)` table queries and the isometric encoding `inexactInput T γ ε`,
  such that for every instance `x`, `p.eval x` is unitary and, for every unitary `V` with
  `‖T.matrix x i j - V i j‖ ≤ ε/(π N)` for all `i`, `j`, the error against `V` is at most `ε`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

namespace SparseHamiltonian.UnitaryPrecision

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

section Reindex
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {X Y : Type*}

/-- The same gate sequence, read over another oracle family: fixed gates are kept and each
oracle call (or inverse call) stays a call of the new oracle. -/
def reindex {O : X → K →L[ℂ] K} {O' : Y → K →L[ℂ] K} :
    OracleCircuit.Program O' → OracleCircuit.Program O
  | .fixed U hU => .fixed U hU
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (reindex p) (reindex q)

/-- Where the two oracles agree, the reindexed program has the same operator. -/
theorem reindex_eval {O : X → K →L[ℂ] K} {O' : Y → K →L[ℂ] K}
    (p : OracleCircuit.Program O') (x : X) (y : Y) (h : O x = O' y) :
    (reindex (O := O) p).eval x = p.eval y := by
  induction p with
  | fixed U hU => rfl
  | query => exact h
  | queryAdjoint => exact congrArg star h
  | seq p q hp hq => exact congrArg₂ (· * ·) hp hq

/-- Reindexing keeps the number of oracle and inverse-oracle calls. -/
theorem reindex_count {O : X → K →L[ℂ] K} {O' : Y → K →L[ℂ] K}
    (p : OracleCircuit.Program O') : (reindex (O := O) p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => exact congrArg₂ (· + ·) hp hq

end Reindex

variable {X Y n Z : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The table read through a map of instances: the same decoder, and on `y` the table and the
represented matrix of the instance `f y`. -/
def Table.comap (T : Table X n Z) (f : Y → X) : Table Y n Z where
  matrix y := T.matrix (f y)
  table y := T.table (f y)
  decode := T.decode
  scale := T.scale
  scale_pos := T.scale_pos
  decode_bound := T.decode_bound
  decoded y := T.decoded (f y)

/-- Corollary `hs:cor:unitary` with inexact entries, uniformly over the intended unitary: one
program built from the table and `ε` alone has error at most `ε` against every unitary within
`ε/(π N)` entrywise of the represented matrix. -/
theorem implementation_inexact_uniform (T : Table X n Z) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (inexactOracle T γ ε),
        (p.count : ℝ) ≤ 995328 * Real.pi *
          (Real.sqrt (Fintype.card n : ℝ) +
            Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (inexactInput T γ ε)† ∘L inexactInput T γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ V : Matrix n n ℂ, IsUnitary (SparseStateOverlap.matrixOperator V) →
            (∀ i j, ‖T.matrix x i j - V i j‖ ≤ ε / (Real.pi * Fintype.card n)) →
            ‖p.eval x ∘L inexactInput T γ ε - inexactInput T γ ε ∘L
              SparseStateOverlap.matrixOperator V‖ ≤ ε := by
  -- the admissible pairs of an instance and an intended unitary
  let Pairs := {q : X × Matrix n n ℂ // IsUnitary (SparseStateOverlap.matrixOperator q.2) ∧
    ∀ i j, ‖T.matrix q.1 i j - q.2 i j‖ ≤ ε / (Real.pi * Fintype.card n)}
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
    implementation_inexact (T.comap (fun q : Pairs => q.1.1)) (fun q => q.1.2) (fun q => q.2.1)
      ε hε hεHalf (fun q i j => q.2.2 i j)
  have hE : inexactInput (T.comap (fun q : Pairs => q.1.1)) γ ε = inexactInput T γ ε := rfl
  rw [hE] at hInput hAction
  refine ⟨γ, hγ, hγOne, reindex p, ?_, hInput, fun x => ⟨?_, fun V hV hClose => ?_⟩⟩
  · rw [reindex_count]
    exact hCount
  · exact (reindex p).eval_unitary
      (fun x => Table.oracle_unitary T γ 2 (Real.pi / 2) (ε / 2) x) x
  · rw [reindex_eval p x ⟨(x, V), hV, hClose⟩ rfl]
    exact (hAction ⟨(x, V), hV, hClose⟩).2

end

end SparseHamiltonian.UnitaryPrecision
