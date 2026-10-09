import DeferredMeasurementLowerBounds.Model.Measured
import SparseLinearSystems.Protocol.Tree

set_option autoImplicit false

/-!
# One-step rules for measured algorithms

Unfolding rules for the instrument and output nodes of `Measured`, a finite maximum shifted by a
constant, the two herald sectors of a unit vector, unit run states of unitary programs, and the
transcript law of a test node of `SparseLinearSystems.Protocol.Tree`. They are used by the
translation of adaptive protocols into measured algorithms.
-/

namespace DeferredMeasurementLowerBounds.Model

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit SparseLinearSystems.Protocol
open scoped InnerProduct

variable {K E F X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

omit [CompleteSpace E] in
/-- A finite maximum of a function shifted by a constant. -/
theorem finsetSup_add_const {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℕ) (c : ℕ) :
    s.sup (fun j => g j + c) = s.sup g + c := by
  apply le_antisymm
  · exact Finset.sup_le fun j hj => Nat.add_le_add_right (Finset.le_sup hj) c
  · obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_sup s hs g
    rw [he]
    exact Finset.le_sup (f := fun j => g j + c) hi

/-- The heralded output of an instrument is the sum over its outcomes. -/
theorem successDensity_instrument (n : ℕ) (A : Fin n → K →L[ℂ] K)
    (hA : ∑ j, (A j)† ∘L A j = 1) (next : Fin n → Measured O E) (x : X) (φ : K) :
    (Measured.instrument n A hA next).successDensity x φ =
      ∑ j, (next j).successDensity x (A j φ) := rfl

/-- The success mass of an instrument is the sum over its outcomes. -/
theorem successMass_instrument (n : ℕ) (A : Fin n → K →L[ℂ] K)
    (hA : ∑ j, (A j)† ∘L A j = 1) (next : Fin n → Measured O E) (x : X) (φ : K) :
    (Measured.instrument n A hA next).successMass x φ =
      ∑ j, (next j).successMass x (A j φ) := rfl

/-- The worst-case cost of an instrument is the maximum over its outcomes. -/
theorem worstCost_instrument (n : ℕ) (A : Fin n → K →L[ℂ] K)
    (hA : ∑ j, (A j)† ∘L A j = 1) (next : Fin n → Measured O E) (w : L → ℕ) :
    (Measured.instrument n A hA next).worstCost w = Finset.univ.sup fun j => (next j).worstCost w :=
  rfl

/-- The heralded output of the output node. -/
theorem successDensity_output (out : E →L[ℂ] K) (h : out† ∘L out = 1) (x : X) (φ : K) :
    (Measured.output (O := O) out h).successDensity x φ = ODEMixedOutput.pureOperator ((out†) φ) :=
  rfl

/-- The success mass of the output node. -/
theorem successMass_output (out : E →L[ℂ] K) (h : out† ∘L out = 1) (x : X) (φ : K) :
    (Measured.output (O := O) out h).successMass x φ = ‖(out†) φ‖ ^ 2 := rfl

/-- The output node is free. -/
theorem worstCost_output (out : E →L[ℂ] K) (h : out† ∘L out = 1) (w : L → ℕ) :
    (Measured.output (O := O) out h).worstCost w = 0 := rfl

/-- The two herald sectors of a unit vector: success mass `‖G† v‖²`, failure mass its
complement. -/
theorem herald_norms {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : H →L[ℂ] K) (hG : G† ∘L G = 1) {v : K} (hv : ‖v‖ = 1) :
    ‖G ((G†) v)‖ ^ 2 = ‖(G†) v‖ ^ 2 ∧ ‖v - G ((G†) v)‖ ^ 2 = 1 - ‖(G†) v‖ ^ 2 := by
  have hPart := ODERepeatProtocol.herald_probability_partition G hG v
  rw [hv] at hPart
  refine ⟨by rw [G.norm_map_iff_adjoint_comp_self.mpr hG], by linarith⟩

/-- A fresh run of a unitary program on a unit seed gives a unit vector. -/
theorem norm_eval_seed (hO : ∀ l x, IsUnitary (O l x)) (p : MultiOracleCircuit.Program O)
    (x : X) {ψ : K} (hψ : ‖ψ‖ = 1) : ‖p.eval x ψ‖ = 1 := by
  rw [(p.eval x).norm_map_iff_adjoint_comp_self.mpr
    (MultiOracleCircuit.Program.eval_unitary p hO x).1, hψ]

/-- The heralded output of a test node of the tree model. -/
theorem tree_successDensity_test (t : TestRun O F) (s f : Tree O F E) (x : X) :
    (Tree.test t s f).successDensity x = ((t.probability x : ℝ) : ℂ) • s.successDensity x +
      ((1 - t.probability x : ℝ) : ℂ) • f.successDensity x := by
  rw [Tree.successDensity, Tree.expect]
  rfl

/-- The success mass of a test node of the tree model. -/
theorem tree_successMass_test (t : TestRun O F) (s f : Tree O F E) (x : X) :
    (Tree.test t s f).successMass x =
      t.probability x * s.successMass x + (1 - t.probability x) * f.successMass x := by
  rw [Tree.successMass, Tree.expect_real_test]
  rfl

end

end DeferredMeasurementLowerBounds.Model
