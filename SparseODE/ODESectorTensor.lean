import SparseODE.ODESectorCoordinates

/-!
# A tensor-register encoding of the source/matrix direct sum

The source and matrix sectors have disjoint values of a physical control bit.
Every matrix query can consequently act on a genuine payload register with
the source register as a spectator. A supplied controlled source call acts on
the source register, with the matrix and reference registers as spectators.
The encoding and all register changes are independent of the unknown input.
-/

namespace SparseHamiltonian.ODESectorTensor

noncomputable section
open ContinuousLinearMap OracleCircuit NativeControlledOracle
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 1000000

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

abbrev Logical (A B : Type*) [Fintype A] [Fintype B] :=
  ODESourceTransport.Space (EuclideanSpace ℂ A) (EuclideanSpace ℂ B)

abbrev Physical (A B : Type*) [Fintype A] [Fintype B] :=
  PiLp 2 (fun _ : A => EuclideanSpace ℂ (NativeControlledOracle.Workspace B))

/-- The inactive native payload and both reference registers are initialized. -/
def sourceSeed (b0 : B) : EuclideanSpace ℂ (Workspace B) :=
  packet false b0 b0 (EuclideanSpace.single b0 1)

theorem sourceSeed_norm (b0 : B) : ‖sourceSeed b0‖ = 1 := by
  change ‖packet false b0 b0 (EuclideanSpace.single b0 1)‖ = 1
  rw [LinearIsometry.norm_map]
  simp

theorem sourceSeed_inner (b0 : B) : inner ℂ (sourceSeed b0) (sourceSeed b0) = 1 := by
  simp [sourceSeed, packet_single]

theorem sourceSeed_packet (b0 : B) (v : EuclideanSpace ℂ B) :
    inner ℂ (sourceSeed b0) (packet true b0 b0 v) = 0 := by
  simp [sourceSeed, packet_single, EuclideanSpace.inner_single_left, packet_apply]

theorem packet_sourceSeed (b0 : B) (v : EuclideanSpace ℂ B) :
    inner ℂ (packet true b0 b0 v) (sourceSeed b0) = 0 := by
  rw [← inner_conj_symm]
  simp only [sourceSeed_packet, map_zero]

/-- Embed the source in the inactive sector and the matrix in the active
sector. The source-register reference is used only in the active sector. -/
def input (a0 : A) (b0 : B) : Logical A B →L[ℂ] Physical A B :=
  CoherentQuerySchedule.rectangular (fun _ : A => ODEGroverRay.ray (sourceSeed b0)) ∘L
      WithLp.fstL 2 ℂ (EuclideanSpace ℂ A) (EuclideanSpace ℂ B) +
    WeightedClock.boundary (fun a : A => if a = a0 then 1 else 0)
      (fun _ : A => (packet true b0 b0).toContinuousLinearMap) ∘L
      WithLp.sndL 2 ℂ (EuclideanSpace ℂ A) (EuclideanSpace ℂ B)

@[simp] theorem input_apply (a0 : A) (b0 : B) (v : Logical A B) (a : A) :
    input a0 b0 v a = v.fst a • sourceSeed b0 +
      if a = a0 then packet true b0 b0 v.snd else 0 := by
  change v.fst a • sourceSeed b0 +
    (Real.sqrt (if a = a0 then 1 else 0) : ℂ) • packet true b0 b0 v.snd = _
  by_cases ha : a = a0 <;> simp [ha]

theorem input_inner (a0 : A) (b0 : B) (v w : Logical A B) :
    inner ℂ (input a0 b0 v) (input a0 b0 w) = inner ℂ v w := by
  have hcoord (a : A) :
      inner ℂ (input a0 b0 v a) (input a0 b0 w a) =
        inner ℂ (v.fst a) (w.fst a) +
          if a = a0 then inner ℂ v.snd w.snd else 0 := by
    by_cases ha : a = a0
    · simp [input_apply, ha, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, sourceSeed_norm, sourceSeed_packet,
        packet_sourceSeed, (packet true b0 b0).inner_map_map, RCLike.inner_apply]
    · simp [input_apply, ha, inner_smul_left, inner_smul_right,
        sourceSeed_norm, RCLike.inner_apply]
  rw [PiLp.inner_apply, WithLp.prod_inner_apply]
  simp_rw [hcoord]
  rw [Finset.sum_add_distrib]
  simp [PiLp.inner_apply]

theorem input_isometry (a0 : A) (b0 : B) :
    (input a0 b0)† ∘L input a0 b0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  simp only [comp_apply, adjoint_inner_left, input_inner, one_def, id_apply]

/-- Fixed exchange of source and native workspace coordinates. -/
def transpose : Physical A B ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : Workspace B => EuclideanSpace ℂ A) :=
  ((RegisterEquivalences.productFlatten A (Workspace B)).trans
    (LookupOracle.permutationUnitary (Equiv.prodComm A (Workspace B)))).trans
      (RegisterEquivalences.productFlatten (Workspace B) A).symm

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem transpose_apply (v : Physical A B) (w : Workspace B) (a : A) :
    transpose v w a = v a w := rfl

omit [DecidableEq A] [DecidableEq B] in
@[simp] theorem transpose_symm_apply
    (v : PiLp 2 (fun _ : Workspace B => EuclideanSpace ℂ A))
    (a : A) (w : Workspace B) : (transpose (A := A) (B := B)).symm v a w = v w a := rfl

/-- One supplied source call, enabled on the inactive matrix sector. -/
def sourcePhysical (S : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :
    Physical A B →L[ℂ] Physical A B :=
  (transpose (A := A) (B := B)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun w : Workspace B => if w.1.1.1 then 1 else S))

omit [DecidableEq A] [DecidableEq B] in
theorem sourcePhysical_unitary
    (S : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) (hS : IsUnitary S) :
    IsUnitary (sourcePhysical (B := B) S) := by
  have hD : IsUnitary (WeightedClock.diagonal
      (fun w : Workspace B => if w.1.1.1 then (1 : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) else S)) := by
    apply CoherentQuerySchedule.diagonal_unitary
    intro w
    cases w.1.1.1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact hS
    · exact isUnitary_one
  exact hD.transport (transpose (A := A) (B := B)).symm

omit [DecidableEq A] [DecidableEq B] in
theorem sourcePhysical_apply
    (S : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A)
    (v : Physical A B) (a : A) (w : Workspace B) :
    sourcePhysical S v a w =
      ((if w.1.1.1 then (1 : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) else S)
        (transpose v w)) a := rfl

theorem input_false (a0 : A) (b0 : B) (v : Logical A B) (a : A) (d r p : B) :
    input a0 b0 v a (((false, d), r), p) =
      if d = b0 ∧ r = b0 ∧ p = b0 then v.fst a else 0 := by
  by_cases hd : d = b0 <;> by_cases hr : r = b0 <;> by_cases hp : p = b0 <;>
    by_cases ha : a = a0 <;>
    simp [input_apply, sourceSeed, packet_apply, hd, hr, hp, ha, Prod.ext_iff]

theorem input_true (a0 : A) (b0 : B) (v : Logical A B) (a : A) (d r p : B) :
    input a0 b0 v a (((true, d), r), p) =
      if a = a0 ∧ d = b0 ∧ r = b0 then v.snd p else 0 := by
  by_cases hd : d = b0 <;> by_cases hr : r = b0 <;> by_cases ha : a = a0 <;>
    simp [input_apply, sourceSeed, packet_apply, hd, hr, ha, Prod.ext_iff]

theorem source_intertwines (a0 : A) (b0 : B)
    (S : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :
    sourcePhysical S ∘L input a0 b0 =
      input a0 b0 ∘L ODESourceTransport.sourceGate (K := EuclideanSpace ℂ B) S := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro a
  apply PiLp.ext
  intro w
  rcases w with ⟨⟨⟨c, d⟩, r⟩, p⟩
  cases c with
  | false =>
      have hSlice : transpose (input a0 b0 v) (((false, d), r), p) =
          if d = b0 ∧ r = b0 ∧ p = b0 then v.fst else 0 := by
        apply PiLp.ext
        intro a'
        by_cases h : d = b0 ∧ r = b0 ∧ p = b0 <;>
          simp only [transpose_apply, input_false, h, true_and, ↓reduceIte, PiLp.zero_apply]
      simp only [comp_apply, sourcePhysical_apply, Bool.false_eq_true, ↓reduceIte,
        hSlice, input_false, ODESourceTransport.sourceGate_apply, WithLp.fst]
      by_cases h : d = b0 ∧ r = b0 ∧ p = b0 <;>
        simp only [h, true_and, ↓reduceIte, map_zero, PiLp.zero_apply]
  | true =>
      simp only [comp_apply, sourcePhysical_apply, ↓reduceIte, one_def, id_apply,
        transpose_apply, input_true, ODESourceTransport.sourceGate_apply, WithLp.snd]

end
end SparseHamiltonian.ODESectorTensor
