import GateEfficientSynthesisTrials.Register

/-!
# The synthesised preparation approximates the released one

Let the native preparation `prepN` be within `δ` of the lifted released preparation
`liftB (conj Urel)` on clean work wires (`ApproxOn CleanX`, as in `GateNative.noutcome`). Then
the synthesised preparation `synthPrep hS η prepN` on the trial register is within `η + δ` of
the lifted released preparation of the trial register, on clean work wires
(`synthPrep_approx`): the synthesis moves the full output by at most `η` on clean synthesis
ancillas (`GateSynth.synthC_approxOn`), the native error is lifted to the synthesis ancillas
(`approxOn_localOp`), the errors add on the vectors with both clean (`approxOn_trans`,
`approxOn_restrict`), and both sides are transported to the trial register along `embS`
(`approxOn_localOp`, `liftB_embS`). This is the full-output (clean-ancilla) error of the
implemented preparation unitary; the inverse is its exact adjoint.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynthTrials

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth

/-! ### Approximate agreement -/

section Approx

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- Errors of approximate agreement add. -/
theorem approxOn_trans {S : Cfg W → Prop} {C₁ C₂ C₃ : Reg W Q →L[ℂ] Reg W Q} {δ₁ δ₂ : ℝ}
    (h₁ : ApproxOn S C₁ C₂ δ₁) (h₂ : ApproxOn S C₂ C₃ δ₂) : ApproxOn S C₁ C₃ (δ₁ + δ₂) := by
  intro ψ hψ
  calc ‖C₁ ψ - C₃ ψ‖ = ‖(C₁ ψ - C₂ ψ) + (C₂ ψ - C₃ ψ)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖C₁ ψ - C₂ ψ‖ + ‖C₂ ψ - C₃ ψ‖ := norm_add_le _ _
    _ ≤ δ₁ * ‖ψ‖ + δ₂ * ‖ψ‖ := add_le_add (h₁ ψ hψ) (h₂ ψ hψ)
    _ = (δ₁ + δ₂) * ‖ψ‖ := by ring

/-- Approximate agreement on fewer vectors. -/
theorem approxOn_restrict {S₁ S₂ : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q} {δ : ℝ}
    (h : ApproxOn S₁ C O δ) (hS : ∀ y, S₂ y → S₁ y) : ApproxOn S₂ C O δ := by
  intro ψ hψ
  exact h ψ (fun y hy => hψ y (fun h2 => hy (hS y h2)))

end Approx

/-! ### Transport to the trial register -/

section Transport

variable {a m r K k l f : ℕ} {S Zs Z Y J X : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

omit [Fintype Y] [DecidableEq Y] in
/-- **The lifted released operator, transported along `embS`, is the lifted released operator of
the trial register.** -/
theorem liftB_embS (C : Reg (GateODE.AW a m r K k l f ⊕ S) ℂ →L[ℂ]
      Reg (GateODE.AW a m r K k l f ⊕ S) ℂ) :
    localOp (embS (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
        (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) (X := X))
        (embS).injective
        (fun _ => liftB (X := X) (liftB (X := XW Z bT bP A ⊕ OX Zs nP) C)) =
      liftB (X := XW Z bT bP A ⊕ OX (SX Zs nP X) (sPool a m r K k l f S Zs nP Z bT bP A X)) C := by
  have hρ : Function.Injective (fun v : GateODE.AW a m r K k l f ⊕ S =>
      (Sum.inl (Sum.inl v) : HWO a m r K k l f S Zs nP Z bT bP A ⊕ X)) :=
    fun _ _ h => Sum.inl_injective (Sum.inl_injective h)
  have e1 : liftB (X := X) (liftB (X := XW Z bT bP A ⊕ OX Zs nP) C) =
      localOp (fun v : GateODE.AW a m r K k l f ⊕ S =>
        (Sum.inl (Sum.inl v) : HWO a m r K k l f S Zs nP Z bT bP A ⊕ X)) hρ (fun _ => C) := by
    unfold liftB
    exact GateODE.localOp_localOp' Sum.inl_injective Sum.inl_injective _ hρ (fun _ => rfl)
      (fun _ _ => C)
  rw [e1]
  unfold liftB
  exact GateODE.localOp_localOp' (embS).injective hρ _ Sum.inl_injective (fun _ => rfl)
    (fun _ _ => C)

/-- **The synthesised preparation is within `η + δ` of the lifted released preparation** on
clean work wires of the trial register, if the native preparation is within `δ` on clean
work wires of the native register. -/
theorem synthPrep_approx (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hprim : ∀ j, IsUnitary (prim j))
    (Urel : Reg (GateODE.AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (GateODE.AW a m r K k l f) (Reg S ℂ))
    {δ : ℝ} (hδ : 0 ≤ δ) (hA : ApproxOn CleanX (nrun prim prepN) (liftB (conj Urel)) δ) :
    ApproxOn CleanX (nrun prim (synthPrep hS η prepN)) (liftB (conj Urel)) (η + δ) := by
  have hN : (0 : ℝ) < nGatesN prepN + 1 := by positivity
  have hζ : 0 < η / (nGatesN prepN + 1) := div_pos hη hN
  -- the synthesis, on clean synthesis ancillas
  have h1 : ApproxOn CleanX (nrun prim (synthBudget hS η prepN))
      (liftB (X := X) (nrun prim prepN)) η := by
    refine (synthC_approxOn prim hS hζ prepN hvalid hprim).mono ?_
    rw [mul_div_assoc', div_le_iff₀ hN]
    nlinarith
  -- the native error, lifted to the synthesis ancillas
  have h2 : ApproxOn (fun y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A ⊕ X) =>
        CleanX y ∧ CleanX (fun v => y (Sum.inl v)))
      (liftB (X := X) (nrun prim prepN)) (liftB (X := X) (liftB (conj Urel))) δ :=
    approxOn_localOp Sum.inl_injective (fun _ => nrun prim prepN)
      (fun _ => liftB (conj Urel)) hδ (fun _ hy => hy.2) (fun _ => hA)
  have h3 := approxOn_trans (approxOn_restrict h1 (fun _ hy => hy.1)) h2
  -- transport along the placement
  have h4 := approxOn_localOp (embS (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) (X := X)).injective
    (fun _ => nrun prim (synthBudget hS η prepN))
    (fun _ => liftB (X := X) (liftB (conj Urel))) (by positivity)
    (SW := CleanX)
    (fun y hy => ⟨fun x => hy _, fun o => by rcases o with x | o <;> exact hy _⟩)
    (fun _ => h3)
  rw [synthPrep, nrun_map, ← liftB_embS]
  exact h4

end Transport

end

end SparseHamiltonian.GateSynthTrials
