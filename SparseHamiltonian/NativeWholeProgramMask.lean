import SparseHamiltonian.SharpLabeledActiveClockQuery

/-!
# Native masking of whole programs

Unlike a distributed involution clock, these adapters apply the source program
itself on every active chronological cell. They require no involution promise.
Every logical native call is compiled using three ordinary calls with fixed
native labels. The common clean encoding is independent of the reuse index.

-/

namespace SparseHamiltonian.NativeWholeProgramMask

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {ι B X L : Type*} [Fintype ι] [Fintype B] [DecidableEq B]
  (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)

/-- Compile the whole source program under a fixed branch predicate. Neither
its primitive label nor its direction is selected by the branch register. -/
def program (a : B) (active : ι → Bool) (p : MultiOracleCircuit.Program F) :
    MultiOracleCircuit.Program (NativeMaskedProgram.oracle (ι := ι) F) :=
  NativeMaskedProgram.compile F a id (fun _ => active)
    (NativeHermitianDilation.maskedProgram active p)

@[simp] theorem program_count (a : B) (active : ι → Bool)
    (p : MultiOracleCircuit.Program F) :
    (program F a active p).count = 3 * p.count := by
  rw [program, NativeMaskedProgram.compile_count]
  change (NativeHermitianDilation.maskedProgram active p).count * 3 = _
  rw [NativeHermitianDilation.maskedProgram_count]
  omega

/-- Every primitive's exact assigned cost is retained by masking. -/
@[simp] theorem program_cost (a : B) (active : ι → Bool)
    (p : MultiOracleCircuit.Program F) (w : L → ℕ) :
    (program F a active p).cost w = 3 * p.cost w := by
  rw [program, NativeMaskedProgram.compile_cost]
  change (NativeHermitianDilation.maskedProgram active p).cost (fun l => 3 * w l) = _
  rw [NativeHermitianDilation.maskedProgram_cost, NativeHermitianDilation.cost_scale]

@[simp] theorem program_labelCount [DecidableEq L] (a : B) (active : ι → Bool)
    (p : MultiOracleCircuit.Program F) (l : L) :
    (program F a active p).labelCount l = 3 * p.labelCount l :=
  program_cost F a active p _

/-- Full coherent correctness, including restoration of the dummy ancillas.
The unknown image is a proof witness and is absent from the program. -/
theorem program_intertwines (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) =
      EuclideanSpace.single (image l x) 1)
    (active : ι → Bool) (p : MultiOracleCircuit.Program F) (x : X) :
    (program F a active p).eval x ∘L
        (NativeMaskedOracle.input (ι := ι) a).toContinuousLinearMap =
      (NativeMaskedOracle.input a).toContinuousLinearMap ∘L
        MaskedProgram.masked active (p.eval x) := by
  rw [program, NativeMaskedProgram.compile_eval F hF a image hvalid,
    NativeHermitianDilation.maskedProgram_eval]
  rfl

/-- No clean-input restriction is needed for physical unitarity. -/
theorem program_unitary (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (active : ι → Bool) (p : MultiOracleCircuit.Program F) (x : X) :
    IsUnitary ((program F a active p).eval x) :=
  (program F a active p).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y) x

end
end SparseHamiltonian.NativeWholeProgramMask
