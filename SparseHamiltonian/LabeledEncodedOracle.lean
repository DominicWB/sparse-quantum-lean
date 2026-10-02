import SparseHamiltonian.DyadicAdditiveAlphabet

/-!
# Encoded implementation certificates retaining every native label

The physical syntax names its row, column, or value primitive explicitly.
All implementations use a single fixed clean encoding. There is no implicit
SELECT primitive and no query-dependent preparation among the fixed gates.
-/
namespace SparseHamiltonian.LabeledEncodedOracle
noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- A physical multi-oracle circuit implements the logical action on one
fixed encoded subspace, with all native calls counted. -/
def ImplementsOn (O : L → X → K →L[ℂ] K) (F : X → P →L[ℂ] P)
    (E : P →L[ℂ] K) (q : ℕ) : Prop :=
  ∃ p : MultiOracleCircuit.Program O, (∀ x, p.eval x ∘L E = E ∘L F x) ∧ p.count ≤ q

namespace ImplementsOn

variable {O : L → X → K →L[ℂ] K} {F G : X → P →L[ℂ] P}
  {E : P →L[ℂ] K} {q r : ℕ}

/-- Fixed logical unitaries extend to fixed physical unitaries. -/
theorem fixed (hE : E† ∘L E = 1) (U : P →L[ℂ] P) (hU : IsUnitary U) :
    ImplementsOn O (fun _ => U) E 0 :=
  ⟨.fixed (SubspaceOracle.lift E U) (SubspaceOracle.lift_unitary E hE U hU),
    fun _ => EncodedOracle.lift_comp E hE U, le_rfl⟩

omit [CompleteSpace P] in
/-- The identity needs no oracle calls, for any fixed encoding. -/
theorem identity : ImplementsOn O (fun _ => 1) E 0 := by
  refine ⟨MultiOracleCircuit.Program.identity, fun _ => ?_, le_rfl⟩
  simp only [MultiOracleCircuit.Program.eval_identity, one_def, id_comp, comp_id]

omit [CompleteSpace P] in
/-- The same physical circuit establishes every larger query allowance. -/
theorem mono (h : ImplementsOn O F E q) (hqr : q ≤ r) :
    ImplementsOn O F E r := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, hp, hq.trans hqr⟩

omit [CompleteSpace P] in
/-- Pointwise equal logical families have the same implementation. -/
theorem congr (h : ImplementsOn O F E q) (hFG : ∀ x, F x = G x) :
    ImplementsOn O G E q := by
  obtain ⟨p, hp, hq⟩ := h
  exact ⟨p, fun x => by rw [← hFG x]; exact hp x, hq⟩

omit [CompleteSpace P] in
/-- Composition does not require control over the complement of the encoding. -/
theorem mul (hF : ImplementsOn O F E q) (hG : ImplementsOn O G E r) :
    ImplementsOn O (fun x => F x * G x) E (q + r) := by
  obtain ⟨p, hp, hq⟩ := hF
  obtain ⟨t, ht, hr⟩ := hG
  refine ⟨.seq p t, fun x => ?_, Nat.add_le_add hq hr⟩
  change (p.eval x ∘L t.eval x) ∘L E = E ∘L (F x ∘L G x)
  rw [comp_assoc, ht, ← comp_assoc, hp, comp_assoc]


end ImplementsOn

/-- Substitution of a single logical oracle by a labeled physical program.
This is an encoded syntactic compilation, not an extra physical primitive. -/
theorem ImplementsOn.trans {O : L → X → K →L[ℂ] K} {F G : X → P →L[ℂ] P}
    {E : P →L[ℂ] K} {q r : ℕ} (hE : E† ∘L E = 1)
    (hO : ∀ l x, IsUnitary (O l x)) (hF : ∀ x, IsUnitary (F x))
    (hFimpl : ImplementsOn O F E q) (hGimpl : OracleCircuit.Implements F G r) :
    ImplementsOn O G E (r * q) := by
  obtain ⟨p, hp, hq⟩ := hFimpl
  obtain ⟨a, ha, hr⟩ := hGimpl
  let logical : Unit → X → P →L[ℂ] P := fun _ => F
  let a' : MultiOracleCircuit.Program logical := MultiOracleCircuit.Program.embed () a
  let circuits : Unit → MultiOracleCircuit.Program O := fun _ => p
  refine ⟨EncodedLabeledProgram.compile E hE circuits a', ?_, ?_⟩
  · intro x
    rw [EncodedLabeledProgram.compile_eval E hE circuits hO
      (fun _ x => hF x) (fun _ x => hp x)]
    simp only [a', MultiOracleCircuit.Program.eval_embed, ha]
  · rw [EncodedLabeledProgram.compile_count]
    change a'.cost (fun _ => p.count) ≤ r * q
    rw [MultiOracleCircuit.Program.cost_const]
    simp only [a', MultiOracleCircuit.Program.count_embed]
    exact Nat.mul_le_mul hr hq

end
end SparseHamiltonian.LabeledEncodedOracle
