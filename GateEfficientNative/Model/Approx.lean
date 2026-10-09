import GateEfficientNative.Model.Instr

/-!
# Approximate agreement on clean configurations

`ApproxOn S C O δ` states that the actual operator `C` is within `δ` of the
ideal operator `O` on every vector supported on the configurations `S`
(typically: every added work wire is zero).  This is the full-output error
convention of the paper: the error includes any residual work-register state.

* `ApproxOn.comp`: errors add along products, when the ideal operator
  preserves `S` and both operators are contractions;
* `ApproxOn.adjoint`: the inverse of the actual unitary approximates the
  inverse of the ideal unitary with the same error;
* `approxOn_localOp`, `agrees_localOp`: both statements transfer from the
  exposed wires to the whole register;
* `norm_comp_sub_le`: the clean-embedding form `‖C ∘ ι - ι ∘ U‖ ≤ δ`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open scoped InnerProduct BigOperators

section ClearCfg

variable {W A : Type*} [DecidableEq W] [Fintype A]

theorem clearCfg_apply_out (ι : A → W) (x : Cfg W) (w : W) (hw : ∀ a, ι a ≠ w) :
    clearCfg ι x w = x w :=
  GateODE.overwrite_apply_out ι x _ w hw

theorem clearCfg_apply_ι {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (a : A) :
    clearCfg ι x (ι a) = false :=
  GateODE.overwrite_apply_ι hι x _ a

end ClearCfg

section Approx

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The actual operator `C` is within `δ` of the ideal `O` on `S`-supported vectors. -/
def ApproxOn (S : Cfg W → Prop) (C O : Reg W Q →L[ℂ] Reg W Q) (δ : ℝ) : Prop :=
  ∀ ψ, Supp S ψ → ‖C ψ - O ψ‖ ≤ δ * ‖ψ‖

omit [CompleteSpace Q] in
theorem ApproxOn.of_agrees {S : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q}
    (h : Agrees S C O) : ApproxOn S C O 0 := by
  intro ψ hψ
  rw [h ψ hψ, sub_self, norm_zero, zero_mul]

omit [CompleteSpace Q] in
theorem ApproxOn.mono {S : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q} {δ δ' : ℝ}
    (h : ApproxOn S C O δ) (hδ : δ ≤ δ') : ApproxOn S C O δ' := by
  intro ψ hψ
  exact (h ψ hψ).trans (mul_le_mul_of_nonneg_right hδ (norm_nonneg _))

omit [CompleteSpace Q] in
theorem ApproxOn.congr_left {S : Cfg W → Prop} {C C' O : Reg W Q →L[ℂ] Reg W Q} {δ : ℝ}
    (h : ApproxOn S C O δ) (hC : Agrees S C' C) : ApproxOn S C' O δ := by
  intro ψ hψ
  rw [hC ψ hψ]
  exact h ψ hψ

omit [CompleteSpace Q] in
theorem ApproxOn.congr_right {S : Cfg W → Prop} {C O O' : Reg W Q →L[ℂ] Reg W Q} {δ : ℝ}
    (h : ApproxOn S C O δ) (hO : Agrees S O' O) : ApproxOn S C O' δ := by
  intro ψ hψ
  rw [hO ψ hψ]
  exact h ψ hψ

omit [CompleteSpace Q] in
/-- Errors add along products. -/
theorem ApproxOn.comp {S : Cfg W → Prop} {C₁ C₂ O₁ O₂ : Reg W Q →L[ℂ] Reg W Q} {δ₁ δ₂ : ℝ}
    (h₁ : ApproxOn S C₁ O₁ δ₁) (hO₁ : Preserves S O₁) (hO₁n : ∀ ψ, ‖O₁ ψ‖ ≤ ‖ψ‖)
    (h₂ : ApproxOn S C₂ O₂ δ₂) (hC₂n : ∀ ψ, ‖C₂ ψ‖ ≤ ‖ψ‖) (hδ₂ : 0 ≤ δ₂) :
    ApproxOn S (C₂ ∘L C₁) (O₂ ∘L O₁) (δ₁ + δ₂) := by
  intro ψ hψ
  have e : (C₂ ∘L C₁) ψ - (O₂ ∘L O₁) ψ = C₂ (C₁ ψ - O₁ ψ) + (C₂ (O₁ ψ) - O₂ (O₁ ψ)) := by
    simp only [comp_apply, map_sub]
    abel
  rw [e]
  calc ‖C₂ (C₁ ψ - O₁ ψ) + (C₂ (O₁ ψ) - O₂ (O₁ ψ))‖
      ≤ ‖C₂ (C₁ ψ - O₁ ψ)‖ + ‖C₂ (O₁ ψ) - O₂ (O₁ ψ)‖ := norm_add_le _ _
    _ ≤ δ₁ * ‖ψ‖ + δ₂ * ‖O₁ ψ‖ :=
        add_le_add ((hC₂n _).trans (h₁ ψ hψ)) (h₂ _ (hO₁ ψ hψ))
    _ ≤ δ₁ * ‖ψ‖ + δ₂ * ‖ψ‖ := by
        gcongr
        exact hO₁n ψ
    _ = (δ₁ + δ₂) * ‖ψ‖ := by ring

/-- The actual inverse approximates the ideal inverse with the same error. -/
theorem ApproxOn.adjoint {S : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q} {δ : ℝ}
    (h : ApproxOn S C O δ) (hC : IsUnitary C) (hO : IsUnitary O) (hOs : Preserves S (O†)) :
    ApproxOn S (C†) (O†) δ := by
  intro ψ hψ
  have hCC : (C†) ∘L C = 1 := by
    have := hC.1; rwa [star_eq_adjoint, mul_def] at this
  have hOO : O ∘L (O†) = 1 := by
    have := hO.2; rwa [star_eq_adjoint, mul_def] at this
  have e : (C†) ψ - (O†) ψ = -((C†) (C ((O†) ψ) - O ((O†) ψ))) := by
    have h1 : (C†) (C ((O†) ψ)) = (O†) ψ := by
      rw [← comp_apply, hCC, one_apply_eq_self]
    have h2 : O ((O†) ψ) = ψ := by
      rw [← comp_apply, hOO, one_apply_eq_self]
    rw [map_sub, h1, h2]
    abel
  have hiso : ∀ φ, ‖(C†) φ‖ = ‖φ‖ := by
    intro φ
    have hu : IsUnitary (C†) := by simpa [star_eq_adjoint] using hC.adjoint
    have h1 : (C†)† ∘L (C†) = 1 := by
      have := hu.1; rwa [star_eq_adjoint, mul_def] at this
    exact ((C†).norm_map_iff_adjoint_comp_self).mpr h1 φ
  have hisoO : ‖(O†) ψ‖ = ‖ψ‖ := by
    have hu : IsUnitary (O†) := by simpa [star_eq_adjoint] using hO.adjoint
    have h1 : (O†)† ∘L (O†) = 1 := by
      have := hu.1; rwa [star_eq_adjoint, mul_def] at this
    exact ((O†).norm_map_iff_adjoint_comp_self).mpr h1 ψ
  rw [e, norm_neg, hiso]
  calc ‖C ((O†) ψ) - O ((O†) ψ)‖ ≤ δ * ‖(O†) ψ‖ := h _ (hOs ψ hψ)
    _ = δ * ‖ψ‖ := by rw [hisoO]

omit [CompleteSpace Q] in
/-- The clean-embedding form of approximate agreement. -/
theorem norm_comp_sub_le {S : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q} {δ : ℝ}
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    (ι : P →L[ℂ] Reg W Q) (U : P →L[ℂ] P) (h : ApproxOn S C O δ) (hδ : 0 ≤ δ)
    (hι : ∀ p, Supp S (ι p)) (hιn : ∀ p, ‖ι p‖ = ‖p‖) (hO : O ∘L ι = ι ∘L U) :
    ‖C ∘L ι - ι ∘L U‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro p
  have e : (C ∘L ι - ι ∘L U) p = C (ι p) - O (ι p) := by
    rw [sub_apply, comp_apply, ← hO, comp_apply]
  rw [e, ← hιn p]
  exact h _ (hι p)

end Approx

/-! ### Transfer along exposed wires -/

section Transfer

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [Fintype W] [DecidableEq A] [InnerProductSpace ℂ Q] [CompleteSpace Q] in
/-- The slices of an `SW`-supported vector are `SA`-supported. -/
theorem supp_slice {ι : A → W} (hι : Function.Injective ι) {SA : Cfg A → Prop}
    {SW : Cfg W → Prop} (hS : ∀ y, SW y → SA (fun a => y (ι a))) {ψ : Reg W Q}
    (hψ : Supp SW ψ) (x : Cfg W) : Supp SA (slice ι ψ x) := by
  intro b hb
  rw [slice_apply]
  apply hψ
  intro h
  apply hb
  have := hS _ h
  have hb' : (fun a => overwrite ι x b (ι a)) = b :=
    funext (fun a => GateODE.overwrite_apply_ι hι x b a)
  rwa [hb'] at this

/-- Exact agreement transfers from the exposed wires. -/
theorem agrees_localOp {ι : A → W} (hι : Function.Injective ι)
    (F G : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) {SA : Cfg A → Prop} {SW : Cfg W → Prop}
    (hS : ∀ y, SW y → SA (fun a => y (ι a))) (h : ∀ x, Agrees SA (F x) (G x)) :
    Agrees SW (localOp ι hι F) (localOp ι hι G) := by
  intro ψ hψ
  ext x
  rw [localOp_apply, localOp_apply, h _ _ (supp_slice hι hS hψ x)]

omit [CompleteSpace Q] in
/-- The norm of a register vector is the sum of the norms of its slices
over the outside configurations. -/
theorem norm_sq_eq_sum_slices {ι : A → W} (hι : Function.Injective ι) (ψ : Reg W Q) :
    ‖ψ‖ ^ 2 = ∑ x' : Cfg (Out ι), ‖slice ι ψ (joinCfg ι x' (fun _ => false))‖ ^ 2 := by
  have h := (layout (Q := Q) ι hι).norm_map ψ
  rw [← h, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro x' _
  congr 2
  apply PiLp.ext
  intro b
  rw [layout_apply, slice_apply]
  simp only [overwrite, outPart_joinCfg]

/-- Approximate agreement transfers from the exposed wires. -/
theorem approxOn_localOp {ι : A → W} (hι : Function.Injective ι)
    (F G : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) {SA : Cfg A → Prop} {SW : Cfg W → Prop}
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hS : ∀ y, SW y → SA (fun a => y (ι a))) (h : ∀ x, ApproxOn SA (F x) (G x) δ) :
    ApproxOn SW (localOp ι hι F) (localOp ι hι G) δ := by
  intro ψ hψ
  rw [← sub_apply, GateODE.localOp_sub]
  have hsq : ‖localOp ι hι (fun x => F x - G x) ψ‖ ^ 2 ≤ (δ * ‖ψ‖) ^ 2 := by
    rw [norm_sq_eq_sum_slices hι (localOp ι hι (fun x => F x - G x) ψ),
      mul_pow, norm_sq_eq_sum_slices hι ψ, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x' _
    set y := joinCfg ι x' (fun _ => false) with hy
    have hslice : slice ι (localOp ι hι (fun x => F x - G x) ψ) y =
        (F (clearCfg ι y) - G (clearCfg ι y)) (slice ι ψ y) := by
      apply PiLp.ext
      intro b
      rw [slice_apply, localOp_apply]
      have hc : clearCfg ι (overwrite ι y b) = clearCfg ι y := by
        simp only [clearCfg, overwrite, outPart_joinCfg]
      have hs : slice ι ψ (overwrite ι y b) = slice ι ψ y := by
        apply PiLp.ext
        intro b'
        simp only [slice_apply, overwrite_overwrite]
      have hb : (fun a => overwrite ι y b (ι a)) = b :=
        funext (fun a => GateODE.overwrite_apply_ι hι y b a)
      rw [hc, hs, hb]
    rw [hslice, sub_apply]
    have h1 := h (clearCfg ι y) (slice ι ψ y) (supp_slice hι hS hψ y)
    have h2 : 0 ≤ ‖F (clearCfg ι y) (slice ι ψ y) - G (clearCfg ι y) (slice ι ψ y)‖ :=
      norm_nonneg _
    calc ‖F (clearCfg ι y) (slice ι ψ y) - G (clearCfg ι y) (slice ι ψ y)‖ ^ 2
        ≤ (δ * ‖slice ι ψ y‖) ^ 2 := pow_le_pow_left₀ h2 h1 2
      _ = δ ^ 2 * ‖slice ι ψ y‖ ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg _))).mp hsq

/-- `localOp` preserves a predicate that is stable under overwriting the
exposed wires. -/
theorem preserves_localOp' {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) (S : Cfg W → Prop)
    (hS : ∀ y b, S y → S (overwrite ι y b)) : Preserves S (localOp ι hι F) :=
  preserves_localOp S ι hι F hS

end Transfer

/-! ### Contractions -/

section Contract

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A unitary does not increase norms. -/
theorem IsUnitary.norm_apply_le {U : Reg W Q →L[ℂ] Reg W Q} (hU : IsUnitary U) (ψ : Reg W Q) :
    ‖U ψ‖ ≤ ‖ψ‖ := by
  have h1 : U† ∘L U = 1 := by
    have := hU.1; rwa [star_eq_adjoint, mul_def] at this
  exact (((U).norm_map_iff_adjoint_comp_self).mpr h1 ψ).le

end Contract

end

end SparseHamiltonian.GateNative
