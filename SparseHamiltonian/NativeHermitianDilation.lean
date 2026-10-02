import SparseHamiltonian.NativeAttenuatedLayout

/-!
# Globally involutory native Hermitian dilation

Only the controlled preparation is compiled. The final physical program is
`C swap C†`, which is a Hermitian involution on the entire physical workspace,
including inputs outside the clean encoding. Every masked primitive uses the
proved three-query native implementation. The resulting exact weighted cost
is six times the original program's cost.
-/
namespace SparseHamiltonian.NativeHermitianDilation

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

section Logical
variable {ι K X L : Type*} [Fintype ι]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- Mask a labeled program without making its native label coherent. -/
def maskedProgram (active : ι → Bool) : MultiOracleCircuit.Program O →
    MultiOracleCircuit.Program (fun l x => MaskedProgram.masked active (O l x))
  | .fixed U hU => .fixed _ (MaskedProgram.masked_unitary active U hU)
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (maskedProgram active p) (maskedProgram active q)

@[simp] theorem maskedProgram_count (active : ι → Bool) (p : MultiOracleCircuit.Program O) :
    (maskedProgram active p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [maskedProgram, MultiOracleCircuit.Program.count_seq, hp, hq]

@[simp] theorem maskedProgram_cost (active : ι → Bool) (p : MultiOracleCircuit.Program O)
    (w : L → ℕ) : (maskedProgram active p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [maskedProgram, MultiOracleCircuit.Program.cost_seq, hp, hq]

/-- Logical masking applies to the whole program, including its fixed gates. -/
theorem maskedProgram_eval (active : ι → Bool) (p : MultiOracleCircuit.Program O) (x : X) :
    (maskedProgram active p).eval x = MaskedProgram.masked active (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact MaskedProgram.masked_adjoint active _
  | seq p q hp hq =>
    simp only [maskedProgram, MultiOracleCircuit.Program.eval_seq, hp, hq]
    exact (MaskedProgram.masked_mul active _ _).symm

omit [Fintype ι] in
/-- Uniform multiplication of all label costs multiplies the full additive cost. -/
theorem cost_scale (p : MultiOracleCircuit.Program O) (w : L → ℕ) (c : ℕ) :
    p.cost (fun l => c * w l) = c * p.cost w := by
  induction p with
  | fixed U hU => simp
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [MultiOracleCircuit.Program.cost_seq, hp, hq, Nat.mul_add]

omit [Fintype ι] in
/-- Conjugating the fixed swap by a one-sided controlled unitary gives the
standard Hermitian dilation. -/
theorem masked_swap (U : K →L[ℂ] K) :
    MaskedProgram.masked (fun b : Bool => !b) U ∘L HermitianDilation.swap ∘L
      (MaskedProgram.masked (fun b : Bool => !b) U)† = HermitianDilation.dilation U := by
  rw [MaskedProgram.masked_adjoint]
  ext v b
  cases b <;> simp [MaskedProgram.masked_apply, HermitianDilation.swap_apply]

end Logical

variable {B X L : Type*} [Fintype B] [DecidableEq B]
  (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)

/-- The physical oracle family retains every original native label. -/
abbrev oracle := NativeMaskedProgram.oracle (ι := Bool) F

/-- Actual controlled original program, compiled from ordinary native calls. -/
def controlled (a : B) (p : MultiOracleCircuit.Program F) :
    MultiOracleCircuit.Program (oracle F) :=
  NativeMaskedProgram.compile F a id (fun _ b => !b) (maskedProgram (fun b : Bool => !b) p)

@[simp] theorem controlled_count (a : B) (p : MultiOracleCircuit.Program F) :
    (controlled F a p).count = 3 * p.count := by
  rw [controlled, NativeMaskedProgram.compile_count]
  change (maskedProgram (fun b : Bool => !b) p).count * 3 = _
  rw [maskedProgram_count]
  omega

@[simp] theorem controlled_cost (a : B) (p : MultiOracleCircuit.Program F) (w : L → ℕ) :
    (controlled F a p).cost w = 3 * p.cost w := by
  rw [controlled, NativeMaskedProgram.compile_cost]
  change (maskedProgram (fun b : Bool => !b) p).cost (fun l => 3 * w l) = _
  rw [maskedProgram_cost, cost_scale]

/-- Conjugation of a fixed physical swap ensures an exact full-space involution. -/
def program (a : B) (p : MultiOracleCircuit.Program F) :
    MultiOracleCircuit.Program (oracle F) :=
  .seq (controlled F a p)
    (.seq (.fixed HermitianDilation.swap HermitianDilation.swap_unitary)
      (controlled F a p).adjoint)

@[simp] theorem program_count (a : B) (p : MultiOracleCircuit.Program F) :
    (program F a p).count = 6 * p.count := by simp [program]; ring

@[simp] theorem program_cost (a : B) (p : MultiOracleCircuit.Program F) (w : L → ℕ) :
    (program F a p).cost w = 6 * p.cost w := by simp [program]; ring

@[simp] theorem program_labelCount [DecidableEq L] (a : B)
    (p : MultiOracleCircuit.Program F) (l : L) :
    (program F a p).labelCount l = 6 * p.labelCount l := program_cost F a p _

/-- The controlled implementation is physically unitary on all inputs. -/
theorem controlled_unitary (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (p : MultiOracleCircuit.Program F) (x : X) : IsUnitary ((controlled F a p).eval x) :=
  (controlled F a p).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y) x

/-- Full physical unitary identities, without a clean-input restriction. -/
theorem program_unitary (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (p : MultiOracleCircuit.Program F) (x : X) : IsUnitary ((program F a p).eval x) :=
  (program F a p).eval_unitary
    (fun l y => NativeMaskedOracle.oracle_unitary (F l) (hF l) y) x

/-- Physical evaluation is a conjugate of the fixed Boolean swap. -/
theorem program_eval (a : B) (p : MultiOracleCircuit.Program F) (x : X) :
    (program F a p).eval x = (controlled F a p).eval x ∘L HermitianDilation.swap ∘L
      ((controlled F a p).eval x)† := by
  simp only [program, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
    MultiOracleCircuit.Program.eval_adjoint, star_eq_adjoint, ← mul_def]

/-- Self-adjointness holds even outside the clean simulation subspace. -/
theorem program_selfAdjoint (a : B) (p : MultiOracleCircuit.Program F) (x : X) :
    ((program F a p).eval x)† = (program F a p).eval x := by
  rw [program_eval]
  simp only [adjoint_comp, adjoint_adjoint, HermitianDilation.swap_selfAdjoint, comp_assoc]

/-- The actual native program squares to the identity on its full workspace. -/
theorem program_involution (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (p : MultiOracleCircuit.Program F) (x : X) :
    (program F a p).eval x ∘L (program F a p).eval x = 1 := by
  have h := (program_unitary F hF a p x).1
  change ((program F a p).eval x)† ∘L (program F a p).eval x = 1 at h
  rwa [program_selfAdjoint] at h

/-- The physical swap respects the common clean encoding. -/
theorem swap_input (a : B) :
    HermitianDilation.swap ∘L (NativeMaskedOracle.input (ι := Bool) a).toContinuousLinearMap =
      (NativeMaskedOracle.input a).toContinuousLinearMap ∘L HermitianDilation.swap := by
  ext v b
  simp only [comp_apply, HermitianDilation.swap_apply, NativeMaskedOracle.input_apply,
    LinearIsometry.coe_toContinuousLinearMap]

/-- The compiled controlled program agrees with its logical action on the
fixed clean encoding, using only the native basis-image promise. -/
theorem controlled_intertwines (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (x : X) :
    (controlled F a p).eval x ∘L (NativeMaskedOracle.input (ι := Bool) a).toContinuousLinearMap =
      (NativeMaskedOracle.input a).toContinuousLinearMap ∘L
        MaskedProgram.masked (fun b : Bool => !b) (p.eval x) := by
  rw [controlled, NativeMaskedProgram.compile_eval F hF a image hvalid,
    maskedProgram_eval]
  rfl

/-- Complete logical dilation semantics on the same encoding for every input. -/
theorem program_intertwines (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (x : X) :
    (program F a p).eval x ∘L (NativeMaskedOracle.input (ι := Bool) a).toContinuousLinearMap =
      (NativeMaskedOracle.input a).toContinuousLinearMap ∘L HermitianDilation.dilation (p.eval x) := by
  have hC := controlled_intertwines F hF a image hvalid p x
  have hCa := EncodedOracle.adjoint_intertwines _ _ _
    (controlled_unitary F hF a p x)
    (MaskedProgram.masked_unitary _ _ (p.eval_unitary hF x)) hC
  simp only [star_eq_adjoint] at hCa
  rw [program_eval, comp_assoc, comp_assoc, hCa, ← comp_assoc HermitianDilation.swap,
    swap_input, comp_assoc, ← comp_assoc ((controlled F a p).eval x), hC]
  simp only [comp_assoc, masked_swap]

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The public input adds only a fixed plus register and the fixed clean ancillas. -/
def input (a : B) (E : P →L[ℂ] EuclideanSpace ℂ B) :
    P →L[ℂ] NativeMaskedOracle.Physical Bool B :=
  (NativeMaskedOracle.input (ι := Bool) a).toContinuousLinearMap ∘L
    HermitianDilation.encodedPlus E

/-- The common public encoding remains isometric. -/
theorem input_isometry (a : B) (E : P →L[ℂ] EuclideanSpace ℂ B) (hE : E† ∘L E = 1) :
    (input a E)† ∘L input a E = 1 := by
  have hI := (NativeMaskedOracle.input (ι := Bool) a).adjoint_comp_self
  have hP := HermitianDilation.encodedPlus_isometry E hE
  have hv (v : NativeMaskedOracle.Logical Bool B) :
      ((NativeMaskedOracle.input (ι := Bool) a).toContinuousLinearMap†)
        ((NativeMaskedOracle.input a) v) = v :=
    congrArg (fun T : NativeMaskedOracle.Logical Bool B →L[ℂ]
      NativeMaskedOracle.Logical Bool B => T v) hI
  ext v
  simp only [input, adjoint_comp, comp_apply, LinearIsometry.coe_toContinuousLinearMap, hv]
  exact congrArg (fun T : P →L[ℂ] P => T v) hP


/-- The full native dilation compresses to the Hermitian part of the original block. -/
theorem compression (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (E : P →L[ℂ] EuclideanSpace ℂ B) (x : X) :
    (input a E)† ∘L (program F a p).eval x ∘L input a E =
      HermitianDilation.hermitianPart (E† ∘L p.eval x ∘L E) := by
  have hI := (NativeMaskedOracle.input (ι := Bool) a).adjoint_comp_self
  have hJ := program_intertwines F hF a image hvalid p x
  have hIv (v : NativeMaskedOracle.Logical Bool B) :
      ((NativeMaskedOracle.input (ι := Bool) a).toContinuousLinearMap†)
        ((NativeMaskedOracle.input a) v) = v :=
    congrArg (fun T : NativeMaskedOracle.Logical Bool B →L[ℂ]
      NativeMaskedOracle.Logical Bool B => T v) hI
  have hJv (v : NativeMaskedOracle.Logical Bool B) :
      (program F a p).eval x ((NativeMaskedOracle.input a) v) =
        (NativeMaskedOracle.input a) (HermitianDilation.dilation (p.eval x) v) :=
    congrArg (fun T : NativeMaskedOracle.Logical Bool B →L[ℂ]
      NativeMaskedOracle.Physical Bool B => T v) hJ
  calc
    _ = (HermitianDilation.encodedPlus E)† ∘L HermitianDilation.dilation (p.eval x) ∘L
        HermitianDilation.encodedPlus E := by
      ext v
      simp only [input, adjoint_comp, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        hJv, hIv]
    _ = _ := HermitianDilation.encodedPlus_compression _ E


/-- A Hermitian compressed block is preserved exactly by the native dilation. -/
theorem compression_eq (hF : ∀ l x, IsUnitary (F l x)) (a : B)
    (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (p : MultiOracleCircuit.Program F) (E : P →L[ℂ] EuclideanSpace ℂ B) (x : X)
    (hH : (E† ∘L p.eval x ∘L E)† = E† ∘L p.eval x ∘L E) :
    (input a E)† ∘L (program F a p).eval x ∘L input a E = E† ∘L p.eval x ∘L E := by
  rw [compression F hF a image hvalid p E x, HermitianDilation.hermitianPart, hH]
  module

end
end SparseHamiltonian.NativeHermitianDilation
