import GeneralODE.Block.Standard
import SparseHamiltonian.MultiOracleTransport

/-!
# Lifting programs along star-algebra homomorphisms

A star-algebra homomorphism `φ` between operator algebras maps a program to a
program with the same syntax: fixed gates are mapped by `φ`, query labels are
renamed by `r`.  When the target oracle family is `φ` of the source family
along `r`, evaluation commutes with `φ`.  Query counts and weighted costs are
unchanged up to renaming.
-/

namespace SparseHamiltonian.MultiOracleCircuit.Program

noncomputable section
open OracleCircuit

variable {H K X L M : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → H →L[ℂ] H} {O' : M → X → K →L[ℂ] K}

/-- Lift a program along a star-algebra homomorphism, renaming its labels. -/
def mapHom (φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (r : L → M) :
    Program O → Program O'
  | .fixed U hU => .fixed (φ U) (GeneralODE.Registers.isUnitary_map φ hU)
  | .query l => .query (r l)
  | .queryAdjoint l => .queryAdjoint (r l)
  | .seq p q => .seq (mapHom φ r p) (mapHom φ r q)

theorem eval_mapHom (φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (r : L → M)
    (hO : ∀ l x, O' (r l) x = φ (O l x)) (p : Program O) (x : X) :
    (mapHom (O' := O') φ r p).eval x = φ (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => exact hO l x
  | queryAdjoint l =>
      change star (O' (r l) x) = φ (star (O l x))
      rw [hO, map_star]
  | seq p q hp hq =>
      change (mapHom φ r p).eval x * (mapHom φ r q).eval x = φ (p.eval x * q.eval x)
      rw [hp, hq, map_mul]

@[simp] theorem count_mapHom (φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (r : L → M)
    (p : Program O) : (mapHom (O' := O') φ r p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [mapHom, count_seq, hp, hq]

@[simp] theorem cost_mapHom (φ : (H →L[ℂ] H) →⋆ₐ[ℂ] (K →L[ℂ] K)) (r : L → M)
    (p : Program O) (w : M → ℕ) :
    (mapHom (O' := O') φ r p).cost w = p.cost (fun l => w (r l)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [mapHom, cost_seq, hp, hq]

end

end SparseHamiltonian.MultiOracleCircuit.Program
