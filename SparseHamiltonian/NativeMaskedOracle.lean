import SparseHamiltonian.FractionalAnglePolynomialODE

/-!
# Native queries under arbitrary fixed branch masks

The branch register is a spectator of every physical native query. A fixed
clean encoding works for all masks. The mask is computed into a clean control
bit, the three-query native-control construction is executed, and the control
is erased. No controlled native oracle or coherent selection among different
native oracle labels is included in the physical query model.
-/

namespace SparseHamiltonian.NativeMaskedOracle

noncomputable section
open ContinuousLinearMap OracleCircuit NativeControlledOracle LookupOracle
open scoped InnerProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {ι B X : Type*} [Fintype ι] [Fintype B] [DecidableEq B]

abbrev Logical (ι B : Type*) [Fintype ι] [Fintype B] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℂ B)
abbrev Physical (ι B : Type*) [Fintype ι] [Fintype B] :=
  PiLp 2 (fun _ : ι => EuclideanSpace ℂ (Workspace B))

/-- Append the same clean control, dummy and reference in every branch. This
encoding is independent of the branch mask and of the unknown oracle input. -/
def input (a : B) : Logical ι B →ₗᵢ[ℂ] Physical ι B where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun i => packet false a a (v i))
      map_add' := by intro v w; apply PiLp.ext; intro i; exact map_add (packet false a a) _ _
      map_smul' := by intro z v; apply PiLp.ext; intro i; exact map_smul (packet false a a) z _ }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      _ = ∑ i, ‖packet false a a (v i)‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
      _ = ∑ i, ‖v i‖ ^ 2 := Finset.sum_congr rfl (fun i _ =>
        congrArg (fun z : ℝ => z ^ 2) ((packet false a a).norm_map (v i)))
      _ = _ := (PiLp.norm_sq_eq_of_L2 _ v).symm

@[simp] theorem input_apply (a : B) (v : Logical ι B) (i : ι) :
    input a v i = packet false a a (v i) := rfl

/-- Toggle only the control bit, leaving all other registers untouched. -/
def toggle (b : Bool) : Workspace B ≃ Workspace B where
  toFun v := (((if b then !v.1.1.1 else v.1.1.1, v.1.1.2), v.1.2), v.2)
  invFun v := (((if b then !v.1.1.1 else v.1.1.1, v.1.1.2), v.1.2), v.2)
  left_inv v := by rcases v with ⟨⟨⟨c,d⟩,r⟩,p⟩; cases b <;> cases c <;> rfl
  right_inv v := by rcases v with ⟨⟨⟨c,d⟩,r⟩,p⟩; cases b <;> cases c <;> rfl

/-- Toggle acts correctly on an arbitrary coherent payload. -/
theorem toggle_packet (b c : Bool) (d r : B) (v : EuclideanSpace ℂ B) :
    permutationUnitary (toggle b) (packet c d r v) =
      packet (if b then !c else c) d r v := by
  ext ⟨⟨⟨c',d'⟩,r'⟩,p⟩
  cases b <;> cases c <;> cases c' <;> simp [toggle, packet_apply]

/-- The fixed branch-controlled toggle. -/
def maskGate (active : ι → Bool) : Physical ι B →L[ℂ] Physical ι B :=
  WeightedClock.diagonal (fun i => (permutationUnitary (toggle (B := B) (active i))).toContinuousLinearMap)

omit [Fintype B] [DecidableEq B] in
theorem diagonal_unitary
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (U : ι → K →L[ℂ] K) (hU : ∀ i, IsUnitary (U i)) :
    IsUnitary (WeightedClock.diagonal U) := by
  constructor
  · change (WeightedClock.diagonal U)† ∘L WeightedClock.diagonal U = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [show ∀ i, (U i)† ∘L U i = 1 from fun i => (hU i).1,
      WeightedClock.diagonal_one]
  · change WeightedClock.diagonal U ∘L (WeightedClock.diagonal U)† = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [show ∀ i, U i ∘L (U i)† = 1 from fun i => (hU i).2,
      WeightedClock.diagonal_one]

omit [DecidableEq B] in
/-- A fixed mask gate is a unitary on the entire physical workspace. -/
theorem maskGate_unitary (active : ι → Bool) : IsUnitary (maskGate (B := B) active) :=
  diagonal_unitary _ (fun i => permutationUnitary_unitary (toggle (B := B) (active i)))

/-- Every branch receives the same native call. The extra branch, control,
dummy and reference registers are spectators of the original native oracle. -/
abbrev oracle (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X) :
    Physical ι B →L[ℂ] Physical ι B :=
  MaskedProgram.masked (fun _ : ι => true) (NativeControlledOracle.oracle F x)

omit [DecidableEq B] in
/-- This oracle is fully unitary; its branch register never selects an oracle. -/
theorem oracle_unitary (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X) : IsUnitary (oracle (ι := ι) F x) :=
  MaskedProgram.masked_unitary _ _ (NativeControlledOracle.oracle_unitary F hF x)

/-- Compute the mask, implement controlled native access, and erase the mask. -/
def program (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (active : ι → Bool) : Program (oracle (ι := ι) F) :=
  .seq (.fixed _ (maskGate_unitary active))
    (.seq (MaskedProgram.compile (fun _ : ι => true) (NativeControlledOracle.program F a))
      (.fixed _ (maskGate_unitary active)))

/-- The branch-mask size has no effect on the three ordinary native calls. -/
@[simp] theorem program_count
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (active : ι → Bool) : (program F a active).count = 3 := by
  change 0 + ((MaskedProgram.compile (fun _ : ι => true)
    (NativeControlledOracle.program F a)).count + 0) = 3
  rw [zero_add, add_zero]
  exact (MaskedProgram.compile_count (fun _ : ι => true)
    (NativeControlledOracle.program F a)).trans (NativeControlledOracle.program_count F a)

/-- A useful coordinate identity for the full physical circuit. -/
theorem program_apply
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (active : ι → Bool) (x : X) (v : Physical ι B) (i : ι) :
    (program F a active).eval x v i =
      permutationUnitary (toggle (active i)) ((NativeControlledOracle.program F a).eval x
        (permutationUnitary (toggle (active i)) (v i))) := by
  simp only [program, Program.eval_seq, Program.eval_fixed]
  have h := MaskedProgram.compile_eval (fun _ : ι => true)
    (NativeControlledOracle.program F a) x
  rw [h]
  rfl

/-- Exact full-output correctness. The same fixed clean encoding is used for
every mask; in particular a sequence of clock steps can change its mask. -/
theorem program_intertwines
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (active : ι → Bool) (x : X) :
    (program F a active).eval x ∘L (input (ι := ι) a).toContinuousLinearMap =
      (input a).toContinuousLinearMap ∘L MaskedProgram.masked active (F x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change (program F a active).eval x (input a v) i =
    input a (MaskedProgram.masked active (F x) v) i
  rw [program_apply, input_apply, toggle_packet, input_apply, MaskedProgram.masked_apply]
  cases h : active i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [NativeControlledOracle.program_packet_false F hF x a (image x) (hvalid x), toggle_packet]
    rfl
  · simp only [↓reduceIte, Bool.not_false]
    rw [NativeControlledOracle.program_packet_true F hF x a (image x) (hvalid x), toggle_packet]
    rfl

/-- All fixed branch masks have a three-query implementation under one physical
native oracle and one common, mask-independent clean encoding. -/
theorem three_query_mask
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (active : ι → Bool) :
    EncodedOracle.ImplementsOn (oracle (ι := ι) F)
      (fun x => MaskedProgram.masked active (F x)) (input a).toContinuousLinearMap 3 :=
  ⟨program F a active, program_intertwines F hF a image hvalid active, by simp⟩

/-- Inverse masked access uses the adjoint of the same three-call program. -/
theorem three_query_inverse_mask
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (active : ι → Bool) :
    EncodedOracle.ImplementsOn (oracle (ι := ι) F)
      (fun x => star (MaskedProgram.masked active (F x))) (input a).toContinuousLinearMap 3 :=
  (three_query_mask F hF a image hvalid active).adjoint (oracle_unitary F hF)
    (fun x => MaskedProgram.masked_unitary active (F x) (hF x))

end
end SparseHamiltonian.NativeMaskedOracle
