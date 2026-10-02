import SparseODE.ODESourceBranches

/-!
# All source branches from two supplied state preparations

Only the initial vector and the constant forcing vector need separate
preparation maps. Every positive-weight forcing branch has the direction
of the same forcing vector. This is a statement about the supplied maps;
it makes no circuit-compilation or preparation-query assertion.

-/

namespace SparseHamiltonian.ODESourcePreparations

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
  [CompleteSpace P]

/-- The initial preparation on `none`, and one common forcing preparation
on every quadrature label. -/
def branch (J₀ Jb : P →L[ℂ] P) (N : ℕ) : Option (Fin N) → P →L[ℂ] P
  | none => J₀
  | some _ => Jb

/-- The two input isometries give an isometry on every source branch. -/
theorem branch_isometry (J₀ Jb : P →L[ℂ] P) (N : ℕ)
    (hJ₀ : J₀† ∘L J₀ = 1) (hJb : Jb† ∘L Jb = 1)
    (a : Option (Fin N)) :
    (branch J₀ Jb N a)† ∘L branch J₀ Jb N a = 1 := by
  cases a with
  | none => exact hJ₀
  | some i => exact hJb

omit [CompleteSpace P] in
/-- Two state-preparation promises suffice for every nonzero source branch.
Zero initial/forcing vectors and zero quadrature weights need no promise. -/
theorem branch_prepares (J₀ Jb : P →L[ℂ] P) (seed v b : P)
    (T : ℝ) (hT : 0 ≤ T) (N : ℕ)
    (hInitial : v ≠ 0 → J₀ seed = ODEStateNormalization.unitDirection v)
    (hForcing : b ≠ 0 → Jb seed = ODEStateNormalization.unitDirection b) :
    ∀ a : Option (Fin N), ODESourceBranches.sourceVector v b T N a ≠ 0 →
      branch J₀ Jb N a seed =
        ODEStateNormalization.unitDirection (ODESourceBranches.sourceVector v b T N a) := by
  classical
  intro a ha
  cases a with
  | none => exact hInitial ha
  | some i =>
      have hb : b ≠ 0 := by
        intro hbzero
        apply ha
        simp only [ODESourceBranches.sourceVector, hbzero, _root_.smul_zero]
      have hw : ODESourceQuadrature.weight T N i ≠ 0 := by
        intro hwzero
        apply ha
        simp only [ODESourceBranches.sourceVector, hwzero, Complex.ofReal_zero,
          _root_.zero_smul]
      have hwpos : 0 < ODESourceQuadrature.weight T N i :=
        lt_of_le_of_ne (ODESourceQuadrature.weight_nonneg T hT N i) (Ne.symm hw)
      change Jb seed = ODEStateNormalization.unitDirection
        ((ODESourceQuadrature.weight T N i : ℂ) • b)
      rw [hForcing hb, Complex.coe_smul,
        ODEHeraldedSuccess.unitDirection_pos_smul
          (ODESourceQuadrature.weight T N i) hwpos]

end
end SparseHamiltonian.ODESourcePreparations
