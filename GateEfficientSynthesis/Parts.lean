import GateEfficientSynthesis.Circuit

/-!
# The synthesis hypothesis from single-qubit synthesis and the decomposition of controlled gates

The paper uses "a gate set admitting single-qubit synthesis of length `O(log(1/ζ))` at accuracy
`ζ`" and decomposes controlled known gates before synthesis. `Synthesis.of_parts` derives the
synthesis hypothesis `Synthesis` from these two results of other papers, stated as
`OneQubitSynthesis 𝒢 X₁ L` (the case without controls, with the clean ancillas `X₁`) and
`ControlDecomposition 𝒢 X₂ K` (every one-qubit unitary with at most three controls acts on the
clean ancillas `X₂` exactly as a product of at most `K` gates, each a gate of `𝒢` or
uncontrolled): every elementary gate is approximated within `ζ` by at most `K (L(ζ/(K+1)) + 1)`
gates of `𝒢` with the clean ancillas `X₂ ⊕ X₁`. The proof decomposes the gate, synthesises every
uncontrolled gate of the decomposition at accuracy `ζ/(K+1)` (`approxOn_replace`), and
reassociates the ancilla wires.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open scoped InnerProduct

section Parts

variable {W X₁ X₂ : Type*} [Fintype W] [DecidableEq W] [Fintype X₁] [DecidableEq X₁]
  [Fintype X₂] [DecidableEq X₂]
variable {𝒢 : Set Kind} {L : ℝ → ℕ} {K : ℕ}

omit [Fintype W] [DecidableEq W] [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] in
theorem pols_nil : pols ([] : List (W × Bool)) = Fin.elim0 := funext (fun i => i.elim0)

/-- The gate rule of the second stage: a gate of `𝒢` is kept, an uncontrolled valid gate is
synthesised at accuracy `η`, other gates are dropped (they do not occur). -/
def partRep (h1 : OneQubitSynthesis 𝒢 X₁ L) (η : ℝ) (g : Gate W) : List (Gate (W ⊕ X₁)) :=
  open Classical in
  if GateOf 𝒢 g then [GateODE.Gate.map Sum.inl g]
  else if h : g.cs = [] ∧ UnitaryMat g.u ∧ 0 < η then
    (Classical.choose (h1.2 g.u h.2.1 η h.2.2)).map
      (GateODE.Gate.map (placeEmb (X := X₁) ([] : List (W × Bool)) g.t List.nodup_nil
        (by simp)))
  else []

/-- The second stage consists of valid gates of `𝒢`, is at most `L η + 1` gates long and is
within `η` for every valid gate that is a gate of `𝒢` or has no controls. -/
theorem partRep_spec (h1 : OneQubitSynthesis 𝒢 X₁ L) {η : ℝ} (hη : 0 < η) (g : Gate W)
    (hg : GateOK 3 g) (hk : GateOf 𝒢 g ∨ g.cs = []) :
    (∀ h ∈ partRep h1 η g, GateOK 3 h ∧ GateOf 𝒢 h) ∧ (partRep h1 η g).length ≤ L η + 1 ∧
      ApproxOn (Q := ℂ) CleanX (gRun (partRep h1 η g)) (liftB (X := X₁) (Gate.op g)) η := by
  classical
  by_cases hg𝒢 : GateOf 𝒢 g
  · simp only [partRep, if_pos hg𝒢]
    refine ⟨?_, by simp, ?_⟩
    · intro h hh
      simp only [List.mem_singleton] at hh
      subst hh
      exact ⟨gateOK_map ⟨Sum.inl, Sum.inl_injective⟩ hg, hg𝒢.map ⟨Sum.inl, Sum.inl_injective⟩⟩
    · rw [liftB_op_eq]
      exact (ApproxOn.of_agrees (fun ψ _ => rfl)).mono hη.le
  · have hcs : g.cs = [] := hk.resolve_left hg𝒢
    have h : g.cs = [] ∧ UnitaryMat g.u ∧ 0 < η := ⟨hcs, hg.2.2, hη⟩
    simp only [partRep, if_neg hg𝒢, dif_pos h]
    obtain ⟨hgs, hlen, happ⟩ := Classical.choose_spec (h1.2 g.u h.2.1 η h.2.2)
    refine ⟨?_, ?_, ?_⟩
    · intro h' hh
      obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
      exact ⟨gateOK_map _ (hgs h0 hh0).1, (hgs h0 hh0).2.map _⟩
    · rw [List.length_map]
      omega
    · have hge : g = ⟨[], g.t, g.u⟩ := by
        cases g
        simp only at hcs
        subst hcs
        rfl
      have happ' : ApproxOn (Q := ℂ) CleanX
          (gRun (Classical.choose (h1.2 g.u h.2.1 η h.2.2)))
          (liftB (X := X₁) (Gate.op (canon ([] : List (W × Bool)).length
            (pols ([] : List (W × Bool))) g.u))) η := by
        rw [pols_nil]
        exact happ
      have h2 := approxOn_place (X := X₁) ([] : List (W × Bool)) g.t g.u List.nodup_nil
        (by simp) _ hη.le happ'
      have e : Gate.op (Q := ℂ) g = gateOp [] g.t g.u := by
        rw [Gate.op, hcs]
      rw [e]
      exact h2

omit [Fintype W] [DecidableEq W] [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] in
theorem replace_nGatesOf (rep : Gate W → List (Gate (W ⊕ X₁))) (gs : List (Gate W)) :
    replace (Y := Empty) (J := Empty) rep (nGatesOf gs) = nGatesOf (gs.flatMap rep) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [nGatesOf, List.map_cons, replace, List.flatMap_cons, List.map_append] at ih ⊢
      rw [ih]

/-- The reassociation of the ancilla wires. -/
def assocE {n : ℕ} : (CW n ⊕ X₂) ⊕ X₁ ↪ CW n ⊕ (X₂ ⊕ X₁) :=
  (Equiv.sumAssoc (CW n) X₂ X₁).toEmbedding

omit [Fintype W] [DecidableEq W] [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] in
theorem gate_map_map {A B C : Type*} (f : B → C) (g : A → B) (h : Gate A) :
    GateODE.Gate.map f (GateODE.Gate.map g h) = GateODE.Gate.map (f ∘ g) h := by
  simp [GateODE.Gate.map, List.map_map, Function.comp_def]

/-- The doubly lifted canonical gate, with the ancillas reassociated, is the lifted gate. -/
theorem localOp_assoc_liftB {n : ℕ} (O : Gate (CW n)) :
    localOp (assocE (X₁ := X₁) (X₂ := X₂)) (assocE (X₁ := X₁) (X₂ := X₂)).injective
        (fun _ => liftB (X := X₁) (liftB (X := X₂) (Gate.op (Q := ℂ) O))) =
      liftB (X := X₂ ⊕ X₁) (Gate.op (Q := ℂ) O) := by
  rw [liftB_op_eq (X := X₂), gRun_singleton, liftB_op_eq (X := X₁),
    ← gRun_map_gates (assocE (X₁ := X₁) (X₂ := X₂)), List.map_singleton, gate_map_map,
    gate_map_map, liftB_op_eq (X := X₂ ⊕ X₁)]
  rfl

/-- **The synthesis hypothesis from its two parts.** Single-qubit synthesis with the clean
ancillas `X₁` and length `L`, and the exact decomposition of controlled gates with the clean
ancillas `X₂` into at most `K` gates, give elementary-gate synthesis with the clean ancillas
`X₂ ⊕ X₁` and length `K (L(ζ/(K+1)) + 1)`. -/
theorem Synthesis.of_parts (h1 : OneQubitSynthesis 𝒢 X₁ L) (h2 : ControlDecomposition 𝒢 X₂ K) :
    Synthesis 𝒢 (X₂ ⊕ X₁) (fun ζ => K * (L (ζ / (K + 1)) + 1)) := by
  classical
  refine ⟨h1.1, ?_⟩
  intro n hn p u hu ζ hζ
  obtain ⟨ds, hds, hlen, happ⟩ := h2 n hn p u hu
  have hK' : (0 : ℝ) < K + 1 := by positivity
  have hη : 0 < ζ / (K + 1) := div_pos hζ hK'
  set η := ζ / (K + 1) with hηdef
  set gs := ds.flatMap (partRep (W := CW n ⊕ X₂) h1 η) with hgs
  have hmem : ∀ g, NInstr.gate g ∈ (nGatesOf (Y := Empty) (J := Empty) ds) → g ∈ ds := by
    intro g hg
    simpa [nGatesOf] using hg
  have hspec := fun g (hg : NInstr.gate g ∈ (nGatesOf (Y := Empty) (J := Empty) ds)) =>
    partRep_spec h1 hη g (hds g (hmem g hg)).1 (hds g (hmem g hg)).2
  have hvalid : ∀ i ∈ (nGatesOf (Y := Empty) (J := Empty) ds), i.Valid :=
    valid_nGatesOf ds (fun g hg => (hds g hg).1)
  have hA := approxOn_replace (R := ℂ) (Y := Empty) (J := Empty) (fun j => j.elim)
    (fun j => j.elim) (partRep h1 η) hη.le (nGatesOf ds) hvalid
    (fun g hg h hh => ((hspec g hg).1 h hh).1) (fun g hg => (hspec g hg).2.2)
  rw [replace_nGatesOf, nrun_nGatesOf, nrun_nGatesOf, nGatesN_nGatesOf] at hA
  have hlenR : (ds.length : ℝ) * η ≤ ζ := by
    have h0 : (ds.length : ℝ) ≤ K := by exact_mod_cast hlen
    rw [hηdef, mul_div_assoc', div_le_iff₀ hK']
    nlinarith
  refine ⟨gs.map (GateODE.Gate.map (assocE (X₁ := X₁) (X₂ := X₂))), ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨h0, hh0, rfl⟩ := List.mem_map.mp hh
    obtain ⟨g, hg, hh1⟩ := List.mem_flatMap.mp hh0
    have := (partRep_spec h1 hη g (hds g hg).1 (hds g hg).2).1 h0 hh1
    exact ⟨gateOK_map _ this.1, this.2.map _⟩
  · rw [List.length_map, hgs]
    have hle := nGatesN_replace_le (Y := Empty) (J := Empty) (partRep h1 η) (nGatesOf ds)
      (L η + 1) (fun g hg => (hspec g hg).2.1)
    rw [replace_nGatesOf, nGatesN_nGatesOf, nGatesN_nGatesOf] at hle
    exact hle.trans (Nat.mul_le_mul_right _ hlen)
  · -- Combine the two stages on `(CW n ⊕ X₂) ⊕ X₁`, then reassociate the ancillas.
    have hB : ApproxOn (Q := ℂ) (fun y : Cfg ((CW n ⊕ X₂) ⊕ X₁) =>
        CleanX y ∧ CleanX (fun a : CW n ⊕ X₂ => y (Sum.inl a))) (gRun gs)
        (liftB (X := X₁) (liftB (X := X₂) (Gate.op (Q := ℂ) (canon n p u)))) ζ := by
      have hC := approxOn_localOp (Q := ℂ) (Sum.inl_injective : Function.Injective
        (Sum.inl : CW n ⊕ X₂ → (CW n ⊕ X₂) ⊕ X₁)) (fun _ => gRun (Q := ℂ) ds)
        (fun _ => liftB (X := X₂) (Gate.op (Q := ℂ) (canon n p u))) le_rfl
        (SA := fun y => CleanX y) (SW := fun y => CleanX y ∧
          CleanX (fun a : CW n ⊕ X₂ => y (Sum.inl a)))
        (fun y hy => hy.2) (fun _ => happ)
      intro ψ hψ
      have hψ1 : Supp CleanX ψ := fun y hy => hψ y (fun h => hy h.1)
      have e1 := hA ψ hψ1
      have e2 := hC ψ hψ
      have e4 : (localOp Sum.inl Sum.inl_injective (fun _ => gRun (Q := ℂ) ds) :
          Reg ((CW n ⊕ X₂) ⊕ X₁) ℂ →L[ℂ] Reg ((CW n ⊕ X₂) ⊕ X₁) ℂ) =
          liftB (X := X₁) (gRun ds) := rfl
      have e5 : (localOp Sum.inl Sum.inl_injective
          (fun _ => liftB (X := X₂) (Gate.op (Q := ℂ) (canon n p u))) :
          Reg ((CW n ⊕ X₂) ⊕ X₁) ℂ →L[ℂ] Reg ((CW n ⊕ X₂) ⊕ X₁) ℂ) =
          liftB (X := X₁) (liftB (X := X₂) (Gate.op (Q := ℂ) (canon n p u))) := rfl
      rw [e4, e5, zero_mul] at e2
      calc ‖gRun gs ψ - liftB (X := X₁) (liftB (X := X₂) (Gate.op (Q := ℂ) (canon n p u))) ψ‖
          ≤ ‖gRun gs ψ - liftB (X := X₁) (gRun ds) ψ‖ +
            ‖liftB (X := X₁) (gRun ds) ψ - liftB (X := X₁) (liftB (X := X₂)
              (Gate.op (Q := ℂ) (canon n p u))) ψ‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ (ds.length : ℝ) * η * ‖ψ‖ + 0 := add_le_add e1 e2
        _ ≤ ζ * ‖ψ‖ := by
            rw [add_zero]
            exact mul_le_mul_of_nonneg_right hlenR (norm_nonneg _)
    have hS : ∀ y : Cfg (CW n ⊕ (X₂ ⊕ X₁)), CleanX y →
        (fun y : Cfg ((CW n ⊕ X₂) ⊕ X₁) => CleanX y ∧
          CleanX (fun a : CW n ⊕ X₂ => y (Sum.inl a)))
          (fun a => y (assocE (X₁ := X₁) (X₂ := X₂) a)) := by
      intro y hy
      exact ⟨fun x => hy (Sum.inr x), fun x => hy (Sum.inl x)⟩
    have hD := approxOn_localOp (Q := ℂ) (assocE (X₁ := X₁) (X₂ := X₂)).injective
      (fun _ => gRun (Q := ℂ) gs)
      (fun _ => liftB (X := X₁) (liftB (X := X₂) (Gate.op (Q := ℂ) (canon n p u)))) hζ.le
      hS (fun _ => hB)
    rw [← gRun_map_gates, localOp_assoc_liftB] at hD
    exact hD

/-- **The length of `Synthesis.of_parts` is logarithmic** if the single-qubit synthesis length
is: if `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, then on `(0, 1]`
`K (L(ζ/(K+1)) + 1) ≤ K c₁ log(1/ζ) + K (c₁ log(K+1) + c₀ + 1)`. -/
theorem of_parts_len_le {c₀ c₁ : ℝ}
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) (K : ℕ) {ζ : ℝ}
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((K * (L (ζ / (K + 1)) + 1) : ℕ) : ℝ) ≤
      K * c₁ * Real.log (1 / ζ) + K * (c₁ * Real.log (K + 1) + c₀ + 1) := by
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 := hL (ζ / (K + 1)) (div_pos hζ hK1) (by rw [div_le_one hK1]; linarith)
  have e : Real.log (1 / (ζ / (K + 1))) = Real.log (K + 1) + Real.log (1 / ζ) := by
    rw [one_div_div, Real.log_div (ne_of_gt hK1) (ne_of_gt hζ), one_div, Real.log_inv]
    ring
  rw [e] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hK0
  push_cast
  nlinarith

end Parts

end

end SparseHamiltonian.GateSynth
