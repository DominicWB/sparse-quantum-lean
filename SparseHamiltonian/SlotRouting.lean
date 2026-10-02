import SparseHamiltonian.ReuseQuery

/-!
# Fixed routing of every reuse slot to one oracle interface

A public-coordinate swap fixes the shared private register and carries the
reference local subspace to any selected slot. Thus the complete reuse circuit
uses one fixed extended oracle, rather than a different primitive for each slot.
-/

namespace SparseHamiltonian.SlotRouting

noncomputable section
open ContinuousLinearMap OracleCircuit ReuseSchedule SubspaceOracle ChronologicalResolvent

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The fixed permutation of two public coordinates. -/
def publicSwap {n : ℕ} (r₀ r : Fin n) :
    BlockOperator.H n P →L[ℂ] BlockOperator.H n P :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ P (Equiv.swap r₀ r)).toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace P] in
@[simp] theorem publicSwap_apply {n : ℕ} (r₀ r j : Fin n) (x : BlockOperator.H n P) :
    publicSwap r₀ r x j = x (Equiv.swap r₀ r j) := by
  simp [publicSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

omit [CompleteSpace P] in
@[simp] theorem publicSwap_norm {n : ℕ} (r₀ r : Fin n) (x : BlockOperator.H n P) :
    ‖publicSwap r₀ r x‖ = ‖x‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ P (Equiv.swap r₀ r)).norm_map x

/-- Route a selected public slot to the reference slot without changing the
shared private register. This map is independent of every oracle input. -/
def route {n : ℕ} (r₀ r : Fin n) : Space n P V →L[ℂ] Space n P V :=
  GlobalColligation.blockMap 1 0 0 (publicSwap r₀ r)

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem route_fst {n : ℕ} (r₀ r : Fin n) (x : Space n P V) :
    (route r₀ r x).fst = x.fst := by
  simp [route]

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem route_snd {n : ℕ} (r₀ r j : Fin n) (x : Space n P V) :
    (route r₀ r x).snd j = x.snd (Equiv.swap r₀ r j) := by
  simp [route]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The routing permutation preserves the full Hilbert norm. -/
theorem route_norm {n : ℕ} (r₀ r : Fin n) (x : Space n P V) :
    ‖route r₀ r x‖ = ‖x‖ := by
  apply GlobalColligation.blockMap_norm
  intro v p
  simp

omit [CompleteSpace P] [CompleteSpace V] in
/-- Applying the routing swap twice is exactly identity. -/
theorem route_sq {n : ℕ} (r₀ r : Fin n) :
    (route r₀ r : Space n P V →L[ℂ] Space n P V) * route r₀ r = 1 := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (route r₀ r (route r₀ r x)).fst = x.fst
    simp
  · apply PiLp.ext
    intro j
    change (route r₀ r (route r₀ r x)).snd j = x.snd j
    simp

/-- The actual fixed routing is two-sided unitary, without a dimension assumption. -/
theorem route_unitary {n : ℕ} (r₀ r : Fin n) :
    IsUnitary (route r₀ r : Space n P V →L[ℂ] Space n P V) := by
  have hLeft : star (route r₀ r : Space n P V →L[ℂ] Space n P V) * route r₀ r = 1 :=
    (route r₀ r : Space n P V →L[ℂ] Space n P V).norm_map_iff_adjoint_comp_self.mp
      (route_norm (P := P) (V := V) r₀ r)
  have hStar : star (route r₀ r : Space n P V →L[ℂ] Space n P V) = route r₀ r := by
    calc
      star (route r₀ r) = star (route r₀ r) * (route r₀ r * route r₀ r) := by rw [route_sq, mul_one]
      _ = route r₀ r := by rw [← mul_assoc, hLeft, one_mul]
  exact ⟨hLeft, by rw [hStar, route_sq]⟩

omit [CompleteSpace P] [CompleteSpace V] in
/-- The fixed swap carries the reference embedded local register to the selected one. -/
theorem route_embedding {n : ℕ} (r₀ r : Fin n) :
    (route r₀ r : Space n P V →L[ℂ] Space n P V) ∘L slotEmbedding r₀ = slotEmbedding r := by
  ext x
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (route r₀ r (slotEmbedding r₀ x)).fst = (slotEmbedding r x).fst
    simp
  · apply PiLp.ext
    intro j
    change (route r₀ r (slotEmbedding r₀ x)).snd j = (slotEmbedding r x).snd j
    simp only [route_snd, slotEmbedding_snd]
    have hiff : Equiv.swap r₀ r j = r₀ ↔ j = r := by
      constructor
      · intro h
        have h' := congrArg (Equiv.swap r₀ r) h
        simpa using h'
      · rintro rfl
        simp
    simp only [hiff]

/-- A slot interaction uses the same reference oracle at unchanged local cost;
the slot choice is implemented by two fixed routing gates. -/
theorem slotInteraction_implements_reference {X : Type*}
    (O : X → WithLp 2 (V × P) →L[ℂ] WithLp 2 (V × P))
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V) {q n : ℕ}
    (h : Implements O (fun x => GlobalColligation.blockMap (D x) (C x) (B x) (A x)) q)
    (r₀ r : Fin n) :
    Implements (fun x => lift (slotEmbedding r₀) (O x))
      (fun x => slotInteraction (A x) (B x) (C x) (D x) r) q := by
  have hr := routed_lift_implements h (slotEmbedding r₀)
    (slotEmbedding_adjoint_comp r₀) (route r₀ r) (route_unitary r₀ r)
  rw [route_embedding] at hr
  exact hr.congr (fun x => (SubspaceOracle.slotInteraction_eq_lift (A x) (B x) (C x) (D x) r).symm)

/-- The concrete full reuse construction requires at most `n*q` queries to one
fixed extended oracle when its local block has a `q`-query uniform implementation. -/
theorem fullReuse_implements_reference {X : Type*}
    (O : X → WithLp 2 (V × P) →L[ℂ] WithLp 2 (V × P))
    (A : X → P →L[ℂ] P) (B : X → V →L[ℂ] P)
    (C : X → P →L[ℂ] V) (D : X → V →L[ℂ] V) {q n : ℕ}
    (h : Implements O (fun x => GlobalColligation.blockMap (D x) (C x) (B x) (A x)) q)
    (r₀ : Fin n) :
    Implements (fun x => lift (slotEmbedding r₀) (O x))
      (fun x => CoherentReuse.fullReuse (A x) (B x) (C x) (D x) n) (n * q) := by
  have hp := SynchronizedSelect.implements_product_uniform
    (fun x => lift (slotEmbedding r₀) (O x))
    (fun r x => ReuseQuery.slotStep (A x) (B x) (C x) (D x) n r) q n
    (fun r hr => by
      simpa only [ReuseQuery.slotStep, dif_pos hr] using
        slotInteraction_implements_reference O A B C D h r₀ ⟨r, hr⟩)
  exact hp.congr (fun x => (ReuseQuery.fullReuse_eq_product (A x) (B x) (C x) (D x) n).symm)

end
end SparseHamiltonian.SlotRouting
