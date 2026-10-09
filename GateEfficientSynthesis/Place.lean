import GateEfficientSynthesis.Hypothesis

/-!
# Synthesis of one placed elementary gate

The synthesis hypothesis is stated for the canonical gates on their own wires. A gate `g` of a
circuit on the wires `V` has its controls and target on arbitrary wires; its literal controls may
repeat a wire (`GateOK` does not exclude it).

* Normalisation: two literals on one wire with different values never fire, so the gate is the
  identity (`gateOp_conflict`); otherwise removing repeated literals (`List.dedup`) leaves the
  gate unchanged (`gateOp_dedup`) and its control wires distinct (`nodup_fst_dedup`).
* Placement: the canonical wires are placed on the control wires and the target
  (`place`, `placeEmb`); renaming the wires of a canonical synthesis along this injective
  placement keeps the gates valid gates of `𝒢` and transfers the error bound (`approxOn_place`).
* `exists_rep`: under `Synthesis 𝒢 X L`, every valid gate on `V` is approximated within every
  `ζ > 0`, in the full-output convention with the clean ancillas `X`, by at most `L ζ` valid
  gates of `𝒢` on `V ⊕ X` (payload `ℂ`); `approxOn_rep` transfers the bound to every payload.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap GateCircuit GateNative
open scoped InnerProduct

/-! ### Normalising the controls -/

section Controls

variable {V : Type*}

/-- Two literals on the same wire with different values. -/
def Conflict (cs : List (V × Bool)) : Prop := ∃ c ∈ cs, ∃ c' ∈ cs, c.1 = c'.1 ∧ c.2 ≠ c'.2

theorem ctrlOK_conflict {cs : List (V × Bool)} (h : Conflict cs) (x : Cfg V) :
    ctrlOK cs x = false := by
  obtain ⟨c, hc, c', hc', h1, h2⟩ := h
  by_contra hx
  have hx' : ctrlOK cs x = true := by simpa using hx
  rw [ctrlOK_iff] at hx'
  apply h2
  rw [← hx' c hc, ← hx' c' hc', h1]

variable [DecidableEq V]

theorem ctrlOK_dedup (cs : List (V × Bool)) (x : Cfg V) : ctrlOK cs.dedup x = ctrlOK cs x := by
  apply Bool.eq_iff_iff.mpr
  rw [ctrlOK_iff, ctrlOK_iff]
  simp only [List.mem_dedup]

theorem nodup_fst_dedup {cs : List (V × Bool)} (h : ¬ Conflict cs) :
    (cs.dedup.map Prod.fst).Nodup := by
  apply List.Nodup.map_on _ (List.nodup_dedup cs)
  intro x hx y hy hxy
  apply Prod.ext hxy
  by_contra hne
  exact h ⟨x, List.mem_dedup.mp hx, y, List.mem_dedup.mp hy, hxy, hne⟩

variable [Fintype V]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A gate with conflicting literals is the identity. -/
theorem gateOp_conflict {cs : List (V × Bool)} (h : Conflict cs) (t : V)
    (u : Matrix Bool Bool ℂ) : gateOp (Q := Q) cs t u = 1 := by
  unfold gateOp
  simp only [ctrlOK_conflict h, Bool.false_eq_true, if_false]
  exact condOp_one t

/-- Repeated literals do not change a gate. -/
theorem gateOp_dedup (cs : List (V × Bool)) (t : V) (u : Matrix Bool Bool ℂ) :
    gateOp (Q := Q) cs.dedup t u = gateOp cs t u := by
  unfold gateOp
  congr 1
  funext x
  rw [ctrlOK_dedup]

end Controls

/-! ### Placing a canonical synthesis -/

section Place

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

/-- The wires of the canonical gate in the circuit: the control wires of `cs` and the
target `t`. -/
def place (cs : List (V × Bool)) (t : V) : CW cs.length → V
  | Sum.inl i => (cs.get i).1
  | Sum.inr _ => t

/-- The control values of `cs`. -/
def pols (cs : List (V × Bool)) : Fin cs.length → Bool := fun i => (cs.get i).2

omit [Fintype V] [DecidableEq V] in
theorem place_injective {cs : List (V × Bool)} {t : V} (hnd : (cs.map Prod.fst).Nodup)
    (ht : ∀ c ∈ cs, c.1 ≠ t) : Function.Injective (place cs t) := by
  intro a b hab
  rcases a with i | ⟨⟩ <;> rcases b with j | ⟨⟩
  · have h1 : (cs.map Prod.fst).get ⟨i, by simp⟩ = (cs.map Prod.fst).get ⟨j, by simp⟩ := by
      simpa [place] using hab
    have h2 := (List.Nodup.get_inj_iff hnd).mp h1
    have h3 : (i : ℕ) = j := Fin.mk.inj h2
    exact congrArg Sum.inl (Fin.ext h3)
  · exact absurd hab (ht _ (List.get_mem cs i))
  · exact absurd hab.symm (ht _ (List.get_mem cs j))
  · rfl

/-- The placement of the canonical wires and the ancillas. -/
def placeEmb (cs : List (V × Bool)) (t : V) (hnd : (cs.map Prod.fst).Nodup)
    (ht : ∀ c ∈ cs, c.1 ≠ t) : CW cs.length ⊕ X ↪ V ⊕ X :=
  ⟨Sum.map (place cs t) id, (place_injective hnd ht).sumMap Function.injective_id⟩

omit [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] in
/-- The canonical gate, placed, is the gate with the controls `cs` and the target `t`. -/
theorem map_canon (cs : List (V × Bool)) (t : V) (u : Matrix Bool Bool ℂ) :
    GateODE.Gate.map (fun c => (Sum.inl (place cs t c) : V ⊕ X)) (canon cs.length (pols cs) u) =
      GateODE.Gate.map Sum.inl (⟨cs, t, u⟩ : Gate V) := by
  simp only [GateODE.Gate.map, canon, List.map_map]
  congr 1
  conv_rhs => rw [← List.map_get_finRange cs, List.map_map]
  rfl

omit [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] in
/-- Renaming the wires along an embedding keeps a gate valid. -/
theorem gateOK_map {A W : Type*} (f : A ↪ W) {g : Gate A} (hg : GateOK 3 g) :
    GateOK 3 (GateODE.Gate.map f g) :=
  NInstr.valid_map (Y := Empty) (J := Empty) f (NInstr.gate g) hg

variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The placed canonical gate, the identity on the ancillas. -/
theorem localOp_liftB_canon (cs : List (V × Bool)) (t : V) (u : Matrix Bool Bool ℂ)
    (hnd : (cs.map Prod.fst).Nodup) (ht : ∀ c ∈ cs, c.1 ≠ t) :
    localOp (placeEmb (X := X) cs t hnd ht) (placeEmb cs t hnd ht).injective
        (fun _ => liftB (X := X) (Gate.op (Q := Q) (canon cs.length (pols cs) u))) =
      liftB (X := X) (gateOp (Q := Q) cs t u) := by
  have hρ : Function.Injective (fun c => (Sum.inl (place cs t c) : V ⊕ X)) :=
    Sum.inl_injective.comp (place_injective hnd ht)
  unfold liftB
  rw [GateODE.localOp_localOp' (placeEmb cs t hnd ht).injective Sum.inl_injective
      (fun c => (Sum.inl (place cs t c) : V ⊕ X)) hρ (fun _ => rfl)
      (fun _ _ => Gate.op (Q := Q) (canon cs.length (pols cs) u)),
    GateODE.Gate.map_op hρ, map_canon, ← GateODE.Gate.map_op Sum.inl_injective]
  rfl

/-- **Placement transfers a canonical synthesis.** -/
theorem approxOn_place (cs : List (V × Bool)) (t : V) (u : Matrix Bool Bool ℂ)
    (hnd : (cs.map Prod.fst).Nodup) (ht : ∀ c ∈ cs, c.1 ≠ t)
    (gs : List (Gate (CW cs.length ⊕ X))) {η : ℝ} (hη : 0 ≤ η)
    (h : ApproxOn (Q := Q) CleanX (gRun gs)
      (liftB (X := X) (Gate.op (canon cs.length (pols cs) u))) η) :
    ApproxOn (Q := Q) CleanX (gRun (gs.map (GateODE.Gate.map (placeEmb cs t hnd ht))))
      (liftB (X := X) (gateOp cs t u)) η := by
  have hS : ∀ y : Cfg (V ⊕ X), CleanX y →
      CleanX (fun a : CW cs.length ⊕ X => y (placeEmb cs t hnd ht a)) := by
    intro y hy x
    exact hy x
  have h1 := approxOn_localOp (placeEmb cs t hnd ht).injective (fun _ => gRun (Q := Q) gs)
    (fun _ => liftB (X := X) (Gate.op (Q := Q) (canon cs.length (pols cs) u))) hη hS
    (fun _ => h)
  rw [← gRun_map_gates, localOp_liftB_canon] at h1
  exact h1

/-- **Every valid gate is synthesised** under `Synthesis 𝒢 X L`, on its own wires and the clean
ancillas `X` (payload `ℂ`). -/
theorem exists_rep {𝒢 : Set Kind} {L : ℝ → ℕ} (hS : Synthesis 𝒢 X L) (g : Gate V)
    (hg : GateOK 3 g) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ gs : List (Gate (V ⊕ X)), (∀ h ∈ gs, GateOK 3 h ∧ GateOf 𝒢 h) ∧ gs.length ≤ L ζ ∧
      ApproxOn (Q := ℂ) CleanX (gRun gs) (liftB (X := X) (Gate.op g)) ζ := by
  classical
  by_cases hc : Conflict g.cs
  · refine ⟨[], by simp, by simp, ?_⟩
    have h1 : Gate.op (Q := ℂ) g = 1 := gateOp_conflict hc g.t g.u
    rw [h1, liftB_one, gRun_nil]
    intro ψ _
    rw [sub_self, norm_zero]
    exact mul_nonneg hζ.le (norm_nonneg _)
  · have hnd := nodup_fst_dedup hc
    have ht : ∀ c ∈ g.cs.dedup, c.1 ≠ g.t := fun c hc' => hg.2.1 c (List.mem_dedup.mp hc')
    have hn : g.cs.dedup.length ≤ 3 := (List.dedup_sublist _).length_le.trans hg.1
    obtain ⟨gs, hgs, hlen, happ⟩ := hS.2 g.cs.dedup.length hn (pols g.cs.dedup) g.u hg.2.2 ζ hζ
    refine ⟨gs.map (GateODE.Gate.map (placeEmb g.cs.dedup g.t hnd ht)), ?_, ?_, ?_⟩
    · intro h hh
      obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
      exact ⟨gateOK_map _ (hgs h0 hh0).1, (hgs h0 hh0).2.map _⟩
    · rw [List.length_map]
      exact hlen
    · have e : Gate.op (Q := ℂ) g = gateOp g.cs.dedup g.t g.u := (gateOp_dedup g.cs g.t g.u).symm
      rw [e]
      exact approxOn_place g.cs.dedup g.t g.u hnd ht gs hζ.le happ

/-- The lifted gate as a one-gate list. -/
theorem liftB_op_eq (g : Gate V) :
    liftB (X := X) (Gate.op (Q := Q) g) = gRun [GateODE.Gate.map Sum.inl g] := by
  rw [gRun_singleton]
  exact GateODE.Gate.map_op Sum.inl_injective g

/-- **Payload transfer of a gate synthesis.** -/
theorem approxOn_rep (g : Gate V) (hg : GateOK 3 g) (gs : List (Gate (V ⊕ X)))
    (hgs : ∀ h ∈ gs, GateOK 3 h) {η : ℝ} (hη : 0 ≤ η)
    (h : ApproxOn (Q := ℂ) CleanX (gRun gs) (liftB (X := X) (Gate.op g)) η) :
    ApproxOn (Q := Q) CleanX (gRun gs) (liftB (X := X) (Gate.op g)) η := by
  rw [liftB_op_eq] at h ⊢
  refine approxOn_gRun_payload CleanX gs _ (fun h hh => (hgs h hh).2.1) ?_ hη h
  intro h hh c hc
  simp only [List.mem_singleton] at hh
  subst hh
  simp only [GateODE.Gate.map, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  intro e
  exact hg.2.1 c' hc' (Sum.inl_injective e)

end Place

end

end SparseHamiltonian.GateSynth
