import SparseHamiltonian.RelativeAmplitudeError

/-!
# Coherent control from one exact native basis-image promise

The physical oracle is the supplied unitary with spectator registers. Three
queries, including one inverse query, implement controlled application on a
clean subspace. The image of one fixed basis vector may depend on the unknown
input, but its phase must be exactly one. No permutation promise is made on
other inputs and no controlled-query primitive is granted.
-/

namespace SparseHamiltonian.NativeControlledOracle

noncomputable section
set_option maxRecDepth 2000
open ContinuousLinearMap OracleCircuit LookupOracle
open scoped InnerProduct

variable {B X : Type*} [Fintype B] [DecidableEq B]

/-- The spectator registers hold control, dummy, and reference; payload is last. -/
abbrev Workspace (B : Type*) := ((Bool × B) × B) × B

/-- One native oracle call, with all three other registers as spectators. -/
def oracle (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X) :
    EuclideanSpace ℂ (Workspace B) →L[ℂ] EuclideanSpace ℂ (Workspace B) :=
  LookupFromBasisOracle.spectator (S := (Bool × B) × B) (F x)

/-- Fixed swap routing the query register to the reference. -/
def referenceSwap : Workspace B ≃ Workspace B where
  toFun v := ((v.1.1, v.2), v.1.2)
  invFun v := ((v.1.1, v.2), v.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Route inactive branches to a dummy, leaving the active payload in place. -/
def inactiveSwap : Workspace B ≃ Workspace B where
  toFun v := if v.1.1.1 then v else (((false, v.2), v.1.2), v.1.1.2)
  invFun v := if v.1.1.1 then v else (((false, v.2), v.1.2), v.1.1.2)
  left_inv v := by rcases v with ⟨⟨⟨c,d⟩,r⟩,p⟩; cases c <;> rfl
  right_inv v := by rcases v with ⟨⟨⟨c,d⟩,r⟩,p⟩; cases c <;> rfl

/-- Erase the inactive dummy image using the reference as a classical label.
This reversible gate depends only on the fixed clean label, not on the oracle. -/
def cleanup (a : B) : Workspace B ≃ Workspace B where
  toFun v := (((v.1.1.1, if v.1.1.1 then v.1.1.2 else
    Equiv.swap a v.1.2 v.1.1.2), v.1.2), v.2)
  invFun v := (((v.1.1.1, if v.1.1.1 then v.1.1.2 else
    Equiv.swap a v.1.2 v.1.1.2), v.1.2), v.2)
  left_inv v := by rcases v with ⟨⟨⟨c,d⟩,r⟩,p⟩; cases c <;> simp
  right_inv v := by rcases v with ⟨⟨⟨c,d⟩,r⟩,p⟩; cases c <;> simp

/-- One ordinary query routed to the reference by two fixed swaps. -/
def referenceProgram (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    Program (oracle F) :=
  .seq (.fixed _ (permutationUnitary_unitary (referenceSwap (B := B))))
    (.seq .query (.fixed _ (permutationUnitary_unitary (referenceSwap (B := B)))))

/-- Complete reference preparation, dummy routing, cleanup, and unpreparation. -/
def program (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (a : B) :
    Program (oracle F) :=
  .seq (referenceProgram F).adjoint
    (.seq (.fixed _ (permutationUnitary_unitary (cleanup a)))
      (.seq (.fixed _ (permutationUnitary_unitary (inactiveSwap (B := B))))
        (.seq .query
          (.seq (.fixed _ (permutationUnitary_unitary (inactiveSwap (B := B))))
            (referenceProgram F)))))

omit [DecidableEq B] in
@[simp] theorem referenceProgram_count
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    (referenceProgram F).count = 1 := rfl

@[simp] theorem program_count
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (a : B) :
    (program F a).count = 3 := rfl

omit [DecidableEq B] in
theorem oracle_unitary (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X) : IsUnitary (oracle F x) :=
  LookupFromBasisOracle.spectator_unitary (F x) (hF x)

theorem program_unitary (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (x : X) :
    IsUnitary ((program F a).eval x) :=
  (program F a).eval_unitary (oracle_unitary F hF) x

/-- A payload with fixed values in the three spectator registers. -/
def packet (c : Bool) (d r : B) :
    EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ (Workspace B) :=
  (permutationUnitary (Equiv.prodComm B ((Bool × B) × B))).toLinearIsometry.comp
    (CleanValueEmbedding.embedding (I := B) (K := ℂ) ((c,d),r))

@[simp] theorem packet_apply (c : Bool) (d r : B) (v : EuclideanSpace ℂ B)
    (s : (Bool × B) × B) (p : B) :
    packet c d r v (s,p) = if s = ((c,d),r) then v p else 0 := rfl

@[simp] theorem packet_single (c : Bool) (d r p : B) :
    packet c d r (EuclideanSpace.single p 1) =
      EuclideanSpace.single (((c,d),r),p) 1 := by
  ext ⟨s,q⟩
  by_cases hs : s = ((c,d),r) <;> by_cases hq : q = p <;>
    simp [hs, hq, Prod.ext_iff]

/-- The single physical query acts on an arbitrary payload. -/
theorem oracle_packet (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (x : X) (c : Bool) (d r : B) (v : EuclideanSpace ℂ B) :
    oracle F x (packet c d r v) = packet c d r (F x v) := by
  ext ⟨s,p⟩
  have hs : ((RegisterEquivalences.productFlatten ((Bool × B) × B) B).symm
      (packet c d r v)) s = if s = ((c,d),r) then v else 0 := by
    ext q
    by_cases h : s = ((c,d),r) <;> simp [h]
  change F x (((RegisterEquivalences.productFlatten ((Bool × B) × B) B).symm
    (packet c d r v)) s) p = _
  rw [hs]
  by_cases h : s = ((c,d),r) <;> simp [h]

/-- A promised reference transition holds for every coherent payload. -/
theorem referenceProgram_packet
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X)
    (a b : B) (h : F x (EuclideanSpace.single a 1) = EuclideanSpace.single b 1)
    (c : Bool) (d : B) (v : EuclideanSpace ℂ B) :
    (referenceProgram F).eval x (packet c d a v) = packet c d b v := by
  have he : (referenceProgram F).eval x ∘L (packet c d a).toContinuousLinearMap =
      (packet c d b).toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun B ℂ).toBasis.ext
    intro p
    change (referenceProgram F).eval x (packet c d a ((EuclideanSpace.basisFun B ℂ) p)) = _
    rw [EuclideanSpace.basisFun_apply, packet_single]
    change permutationUnitary referenceSwap (oracle F x
      (permutationUnitary referenceSwap (EuclideanSpace.single (((c,d),a),p) 1))) = _
    rw [permutationUnitary_single]
    change permutationUnitary referenceSwap (oracle F x
      (EuclideanSpace.single (((c,d),p),a) 1)) = _
    unfold oracle
    rw [LookupFromBasisOracle.spectator_single (F x) a b 1 h ((c,d),p),
      permutationUnitary_single]
    simp [referenceSwap, EuclideanSpace.basisFun_apply]
  exact congrArg (fun G : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ (Workspace B) => G v) he

/-- The inverse query erases the reference, using two-sided unitarity. -/
theorem referenceProgram_adjoint_packet
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X)
    (a b : B) (h : F x (EuclideanSpace.single a 1) = EuclideanSpace.single b 1)
    (c : Bool) (d : B) (v : EuclideanSpace ℂ B) :
    (referenceProgram F).adjoint.eval x (packet c d b v) = packet c d a v := by
  rw [← referenceProgram_packet F x a b h c d v, Program.eval_adjoint]
  exact congrArg (fun G => G (packet c d a v))
    ((referenceProgram F).eval_unitary (oracle_unitary F hF) x).1

@[simp] theorem inactiveSwap_packet_true (d r : B) (v : EuclideanSpace ℂ B) :
    permutationUnitary inactiveSwap (packet true d r v) = packet true d r v := by
  ext ⟨⟨⟨c,d'⟩,r'⟩,p⟩
  cases c <;> simp [inactiveSwap, packet_apply]

@[simp] theorem cleanup_packet_true (a d r : B) (v : EuclideanSpace ℂ B) :
    permutationUnitary (cleanup a) (packet true d r v) = packet true d r v := by
  ext ⟨⟨⟨c,d'⟩,r'⟩,p⟩
  cases c <;> simp [cleanup, packet_apply]

/-- Active control applies the arbitrary native unitary and erases both ancillas. -/
theorem program_packet_true
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X)
    (a b : B) (h : F x (EuclideanSpace.single a 1) = EuclideanSpace.single b 1)
    (v : EuclideanSpace ℂ B) :
    (program F a).eval x (packet true a a v) = packet true a a (F x v) := by
  change (referenceProgram F).adjoint.eval x
    (permutationUnitary (cleanup a) (permutationUnitary inactiveSwap
      (oracle F x (permutationUnitary inactiveSwap
        ((referenceProgram F).eval x (packet true a a v)))))) = _
  rw [referenceProgram_packet F x a b h, inactiveSwap_packet_true, oracle_packet,
    inactiveSwap_packet_true, cleanup_packet_true,
    referenceProgram_adjoint_packet F hF x a b h]

/-- Inactive control leaves the payload unchanged, with both ancillas erased. -/
theorem program_packet_false_single
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X)
    (a b : B) (h : F x (EuclideanSpace.single a 1) = EuclideanSpace.single b 1)
    (p : B) :
    (program F a).eval x (packet false a a (EuclideanSpace.single p 1)) =
      packet false a a (EuclideanSpace.single p 1) := by
  change (referenceProgram F).adjoint.eval x
    (permutationUnitary (cleanup a) (permutationUnitary inactiveSwap
      (oracle F x (permutationUnitary inactiveSwap
        ((referenceProgram F).eval x (packet false a a (EuclideanSpace.single p 1))))))) = _
  rw [referenceProgram_packet F x a b h, packet_single, permutationUnitary_single]
  change (referenceProgram F).adjoint.eval x
    (permutationUnitary (cleanup a) (permutationUnitary inactiveSwap
      (LookupFromBasisOracle.spectator (F x) (EuclideanSpace.single (((false,p),b),a) 1)))) = _
  rw [LookupFromBasisOracle.spectator_single (F x) a b 1 h ((false,p),b),
    permutationUnitary_single, permutationUnitary_single]
  change (referenceProgram F).adjoint.eval x
    (EuclideanSpace.single (((false,Equiv.swap a b b),b),p) 1) = _
  rw [Equiv.swap_apply_right, ← packet_single,
    referenceProgram_adjoint_packet F hF x a b h]

/-- The clean-space certificate is linear, hence applies to coherent payloads. -/
theorem program_packet_false
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X)
    (a b : B) (h : F x (EuclideanSpace.single a 1) = EuclideanSpace.single b 1)
    (v : EuclideanSpace ℂ B) :
    (program F a).eval x (packet false a a v) = packet false a a v := by
  have he : (program F a).eval x ∘L (packet false a a).toContinuousLinearMap =
      (packet false a a).toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun B ℂ).toBasis.ext
    intro p
    change (program F a).eval x (packet false a a ((EuclideanSpace.basisFun B ℂ) p)) =
      packet false a a ((EuclideanSpace.basisFun B ℂ) p)
    rw [EuclideanSpace.basisFun_apply]
    exact program_packet_false_single F hF x a b h p
  exact congrArg (fun G : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ (Workspace B) => G v) he

/-- Fixed layout from a public control/payload pair and two clean ancillas. -/
def inputWiring : ((Bool × B) × (B × B)) ≃ Workspace B where
  toFun v := (((v.1.1,v.2.1),v.2.2),v.1.2)
  invFun v := ((v.1.1.1,v.2),(v.1.1.2,v.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Canonical encoding with reference and dummy both equal to the fixed label. -/
def input (a : B) :
    EuclideanSpace ℂ (Bool × B) →ₗᵢ[ℂ] EuclideanSpace ℂ (Workspace B) :=
  (permutationUnitary inputWiring).toLinearIsometry.comp
    (CleanValueEmbedding.embedding (I := Bool × B) (K := ℂ) (a,a))

@[simp] theorem input_apply (a : B) (v : EuclideanSpace ℂ (Bool × B))
    (c : Bool) (d r p : B) :
    input a v (((c,d),r),p) = if (d,r) = (a,a) then v (c,p) else 0 := rfl

@[simp] theorem input_single (a : B) (c : Bool) (p : B) :
    input a (EuclideanSpace.single (c,p) 1) = packet c a a (EuclideanSpace.single p 1) := by
  ext ⟨⟨⟨c',d⟩,r⟩,p'⟩
  by_cases hc : c' = c <;> by_cases hd : d = a <;> by_cases hr : r = a <;>
    simp [hc, hd, hr, Prod.ext_iff]

/-- The desired logical controlled unitary, which is a target rather than a
primitive admitted in the physical query program. -/
def controlled (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X) :
    EuclideanSpace ℂ (Bool × B) →L[ℂ] EuclideanSpace ℂ (Bool × B) :=
  (RegisterEquivalences.productFlatten Bool B).conjStarAlgEquiv
    (WeightedClock.diagonal (fun c : Bool => if c then F x else 1))

omit [DecidableEq B] in
/-- The target has two-sided unitarity, including the inactive branch. -/
theorem controlled_unitary
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (x : X) : IsUnitary (controlled F x) := by
  let G : Bool → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B :=
    fun c => if c then F x else 1
  have hl (c : Bool) : (G c)† ∘L G c = 1 := by
    cases c
    · exact isUnitary_one.1
    · exact (hF x).1
  have hr (c : Bool) : G c ∘L (G c)† = 1 := by
    cases c
    · exact isUnitary_one.2
    · exact (hF x).2
  have hd : IsUnitary (WeightedClock.diagonal G) := by
    constructor
    · change (WeightedClock.diagonal G)† ∘L WeightedClock.diagonal G = 1
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      simp only [hl, WeightedClock.diagonal_one]
    · change WeightedClock.diagonal G ∘L (WeightedClock.diagonal G)† = 1
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      simp only [hr, WeightedClock.diagonal_one]
  exact hd.transport (RegisterEquivalences.productFlatten Bool B)

/-- Coordinate formula for the target on one logical computational basis state. -/
theorem controlled_single_apply
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X)
    (c c' : Bool) (p p' : B) :
    controlled F x (EuclideanSpace.single (c,p) 1) (c',p') =
      if c' = c then ((if c then F x else 1) (EuclideanSpace.single p 1)) p' else 0 := by
  have hs : ((RegisterEquivalences.productFlatten Bool B).symm
      (EuclideanSpace.single (c,p) 1)) c' =
      if c' = c then EuclideanSpace.single p 1 else 0 := by
    ext q
    by_cases hc : c' = c <;> simp [hc]
  change (if c' then F x else 1)
    (((RegisterEquivalences.productFlatten Bool B).symm (EuclideanSpace.single (c,p) 1)) c') p' = _
  rw [hs]
  by_cases hc : c' = c
  · subst c'
    simp
  · simp [hc]

/-- The ideal output is represented with all physical ancillas clean. -/
theorem input_controlled_single
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (x : X)
    (a : B) (c : Bool) (p : B) :
    input a (controlled F x (EuclideanSpace.single (c,p) 1)) =
      packet c a a ((if c then F x else 1) (EuclideanSpace.single p 1)) := by
  ext ⟨⟨⟨c',d⟩,r⟩,p'⟩
  rw [input_apply, controlled_single_apply, packet_apply]
  by_cases hc : c' = c <;> by_cases hd : d = a <;> by_cases hr : r = a <;>
    simp [hc, hd, hr, Prod.ext_iff]

/-- Exact coherent control, including all output workspace, from three ordinary
queries. The unknown label is used only as a proof witness and never supplied
to the program or its fixed gates. -/
theorem program_intertwines
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (x : X) :
    (program F a).eval x ∘L (input a).toContinuousLinearMap =
      (input a).toContinuousLinearMap ∘L controlled F x := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Bool × B) ℂ).toBasis.ext
  intro cp
  rcases cp with ⟨c,p⟩
  change (program F a).eval x (input a ((EuclideanSpace.basisFun (Bool × B) ℂ) (c,p))) =
    input a (controlled F x ((EuclideanSpace.basisFun (Bool × B) ℂ) (c,p)))
  rw [EuclideanSpace.basisFun_apply, input_single, input_controlled_single]
  cases c
  · exact program_packet_false F hF x a (image x) (hvalid x) _
  · exact program_packet_true F hF x a (image x) (hvalid x) _

/-- Counted clean-subspace implementation with no coherent native oracle granted. -/
theorem three_query_control
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1) :
    EncodedOracle.ImplementsOn (oracle F) (controlled F) (input a).toContinuousLinearMap 3 :=
  ⟨program F a, program_intertwines F hF a image hvalid, le_rfl⟩

/-- The same three calls, reversed, implement controlled inverse application. -/
theorem three_query_inverse_control
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1) :
    EncodedOracle.ImplementsOn (oracle F) (fun x => star (controlled F x))
      (input a).toContinuousLinearMap 3 :=
  (three_query_control F hF a image hvalid).adjoint
    (oracle_unitary F hF) (controlled_unitary F hF)

/-- Compile an arbitrary circuit using controlled native calls. All source free
unitaries are lifted through the same fixed clean encoding. -/
def compile (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (a : B)
    (p : Program (controlled F)) : Program (oracle F) :=
  EncodedOracle.compile (input a).toContinuousLinearMap
    (input a).adjoint_comp_self (program F a) p

/-- The complete circuit incurs exactly a factor of three in oracle calls. -/
@[simp] theorem compile_count
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) (a : B)
    (p : Program (controlled F)) : (compile F a p).count = p.count * 3 := by
  unfold compile
  rw [EncodedOracle.compile_count, program_count]

/-- Compiled filters or walks remain exact on all coherent clean inputs. -/
theorem compile_eval
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1)
    (p : Program (controlled F)) (x : X) :
    (compile F a p).eval x ∘L (input a).toContinuousLinearMap =
      (input a).toContinuousLinearMap ∘L p.eval x :=
  EncodedOracle.compile_eval (input a).toContinuousLinearMap
    (input a).adjoint_comp_self (program F a) (oracle_unitary F hF)
    (controlled_unitary F hF) (program_intertwines F hF a image hvalid) p x

/-- Main constructive certificate: unitary circuit, exact count, fixed isometric
encoding, and full coherent output correctness. -/
theorem certificate
    (F : X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ x, IsUnitary (F x)) (a : B) (image : X → B)
    (hvalid : ∀ x, F x (EuclideanSpace.single a 1) = EuclideanSpace.single (image x) 1) :
    (program F a).count = 3 ∧
    (input a).toContinuousLinearMap† ∘L (input a).toContinuousLinearMap = 1 ∧
    ∀ x, IsUnitary ((program F a).eval x) ∧
      (program F a).eval x ∘L (input a).toContinuousLinearMap =
        (input a).toContinuousLinearMap ∘L controlled F x :=
  ⟨program_count F a, (input a).adjoint_comp_self, fun x =>
    ⟨program_unitary F hF a x, program_intertwines F hF a image hvalid x⟩⟩

end
end SparseHamiltonian.NativeControlledOracle
