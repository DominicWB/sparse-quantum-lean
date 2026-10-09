import GateEfficientHamiltonian.Circuit.Theorem

/-!
# Exposing wires twice, renaming gates, and payload-controlled operators

Three register facts used to embed the released gate-level Hamiltonian
simulator in a larger register.

* `localOp_localOp`: exposing the wires of `ι` and then, inside them, the
  wires of `κ` is the same as exposing the wires of `ι ∘ κ` directly.
* `localOp_gateOp`: an elementary gate on the exposed wires is the elementary
  gate with renamed wires on the whole register.
* `pctl`: an operator on the payload, applied exactly on the configurations
  satisfying a list of literals.  It models the controlled calls of the
  supplied source interfaces and the public seed reflection.

The block estimate for operators that act independently on every
configuration of the unexposed wires is `localOp_branch_error`
(`Model/Block`).
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open scoped InnerProduct BigOperators

/-! ### Configuration identities -/

section Cfg

variable {W A B : Type*} [DecidableEq W] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
theorem overwrite_apply_ι {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (b : Cfg A)
    (a : A) : overwrite ι x b (ι a) = b a :=
  joinCfg_apply_ι hι _ b a

omit [DecidableEq A] in
theorem overwrite_apply_out (ι : A → W) (x : Cfg W) (b : Cfg A) (w : W)
    (hw : ∀ a, ι a ≠ w) : overwrite ι x b w = x w :=
  joinCfg_apply_out ι (outPart ι x) b ⟨w, hw⟩

omit [DecidableEq B] in
/-- Overwriting the wires of `ι ∘ κ` inside the slice of `ι`. -/
theorem overwrite_overwrite_comp {ι : A → W} (hι : Function.Injective ι) {κ : B → A}
    (hκ : Function.Injective κ) (z : Cfg W) (b : Cfg B) :
    overwrite ι z (overwrite κ (fun a => z (ι a)) b) = overwrite (ι ∘ κ) z b := by
  funext w
  by_cases hw : ∃ a, ι a = w
  · obtain ⟨a, rfl⟩ := hw
    rw [overwrite_apply_ι hι]
    by_cases ha : ∃ c, κ c = a
    · obtain ⟨c, rfl⟩ := ha
      rw [overwrite_apply_ι hκ]
      exact (overwrite_apply_ι (hι.comp hκ) z b c).symm
    · have hout : ∀ c, (ι ∘ κ) c ≠ ι a := fun c hc => ha ⟨c, hι hc⟩
      rw [overwrite_apply_out κ _ b a (fun c hc => ha ⟨c, hc⟩),
        overwrite_apply_out (ι ∘ κ) z b _ hout]
  · have hout : ∀ c, (ι ∘ κ) c ≠ w := fun c hc => hw ⟨κ c, hc⟩
    rw [overwrite_apply_out ι z _ w (fun a ha => hw ⟨a, ha⟩),
      overwrite_apply_out (ι ∘ κ) z b w hout]

omit [DecidableEq A] [DecidableEq B] in
theorem clearCfg_clearCfg_comp {ι : A → W} (hι : Function.Injective ι) {κ : B → A}
    (z : Cfg W) : clearCfg ι (clearCfg (ι ∘ κ) z) = clearCfg ι z := by
  unfold clearCfg
  funext w
  by_cases hw : ∃ a, ι a = w
  · obtain ⟨a, rfl⟩ := hw
    rw [overwrite_apply_ι hι, overwrite_apply_ι hι]
  · have hout : ∀ c, (ι ∘ κ) c ≠ w := fun c hc => hw ⟨κ c, hc⟩
    rw [overwrite_apply_out ι _ _ w (fun a ha => hw ⟨a, ha⟩),
      overwrite_apply_out ι _ _ w (fun a ha => hw ⟨a, ha⟩),
      overwrite_apply_out (ι ∘ κ) z _ w hout]

omit [Fintype A] [DecidableEq B] in
theorem clearCfg_comp_restrict {ι : A → W} (hι : Function.Injective ι) {κ : B → A}
    (hκ : Function.Injective κ) (z : Cfg W) :
    clearCfg κ (fun a => clearCfg (ι ∘ κ) z (ι a)) = clearCfg κ (fun a => z (ι a)) := by
  unfold clearCfg
  funext a
  by_cases ha : ∃ c, κ c = a
  · obtain ⟨c, rfl⟩ := ha
    rw [overwrite_apply_ι hκ, overwrite_apply_ι hκ]
  · have hout : ∀ c, (ι ∘ κ) c ≠ ι a := fun c hc => ha ⟨c, hι hc⟩
    rw [overwrite_apply_out κ _ _ a (fun c hc => ha ⟨c, hc⟩),
      overwrite_apply_out κ _ _ a (fun c hc => ha ⟨c, hc⟩),
      overwrite_apply_out (ι ∘ κ) z _ _ hout]

end Cfg

/-! ### Nested exposure -/

section Nested

variable {W A B : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- Exposing `ι` and then `κ` exposes `ι ∘ κ`; the inner selector reads the
configuration of the remaining wires of the slice. -/
theorem localOp_localOp {ι : A → W} (hι : Function.Injective ι) {κ : B → A}
    (hκ : Function.Injective κ) (G : Cfg W → Cfg A → (Reg B Q →L[ℂ] Reg B Q)) :
    localOp ι hι (fun x => localOp κ hκ (G x)) =
      localOp (ι ∘ κ) (hι.comp hκ)
        (fun z => G (clearCfg ι z) (clearCfg κ (fun a => z (ι a)))) := by
  ext ψ z
  rw [localOp_apply, localOp_apply, localOp_apply, clearCfg_clearCfg_comp hι,
    clearCfg_comp_restrict hι hκ]
  have hs : slice κ (slice ι ψ z) (fun a => z (ι a)) = slice (ι ∘ κ) ψ z := by
    apply PiLp.ext
    intro c
    simp only [slice_apply]
    rw [overwrite_overwrite_comp hι hκ]
  rw [hs]
  rfl

/-- `localOp_localOp` for any injection that agrees with `ι ∘ κ`. -/
theorem localOp_localOp' {ι : A → W} (hι : Function.Injective ι) {κ : B → A}
    (hκ : Function.Injective κ) (ρ : B → W) (hρ : Function.Injective ρ)
    (hρικ : ∀ b, ρ b = ι (κ b)) (G : Cfg W → Cfg A → (Reg B Q →L[ℂ] Reg B Q)) :
    localOp ι hι (fun x => localOp κ hκ (G x)) =
      localOp ρ hρ (fun z => G (clearCfg ι z) (clearCfg κ (fun a => z (ι a)))) := by
  have h : ρ = ι ∘ κ := funext hρικ
  subst h
  exact localOp_localOp hι hκ G

omit [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A] in
theorem ctrlOK_map (e : A → W) (cs : List (A × Bool)) (x : Cfg W) :
    ctrlOK (cs.map (fun c => (e c.1, c.2))) x = ctrlOK cs (fun a => x (e a)) := by
  unfold ctrlOK
  rw [List.all_map]
  rfl

omit [Fintype W] [Fintype A] in
theorem update_comp_injective {e : A → W} (he : Function.Injective e) (x : Cfg W) (t : A)
    (b : Bool) : (fun a => Function.update x (e t) b (e a)) = Function.update (fun a => x (e a)) t b := by
  funext a
  by_cases ha : a = t
  · subst ha; simp
  · rw [Function.update_of_ne (fun h => ha (he h)), Function.update_of_ne ha]

/-- Renaming the wires of an elementary gate. -/
def Gate.map (e : A → W) (g : Gate A) : Gate W :=
  ⟨g.cs.map (fun c => (e c.1, c.2)), e g.t, g.u⟩

/-- An elementary gate on exposed wires is the renamed elementary gate. -/
theorem localOp_gateOp {e : A → W} (he : Function.Injective e) (cs : List (A × Bool)) (t : A)
    (u : Matrix Bool Bool ℂ) :
    localOp e he (fun _ => gateOp (Q := Q) cs t u) =
      gateOp (cs.map (fun c => (e c.1, c.2))) (e t) u := by
  unfold gateOp condOp
  rw [localOp_localOp' he (single_injective t) (fun _ : Unit => e t) (single_injective (e t))
    (fun _ => rfl)]
  apply localOp_congr
  intro z
  simp only [clearCfg_single, ctrlOK_map]
  rw [update_comp_injective he, Function.update_idem]

theorem Gate.map_op {e : A → W} (he : Function.Injective e) (g : Gate A) :
    localOp e he (fun _ => g.op (Q := Q)) = (Gate.map e g).op := by
  exact localOp_gateOp he g.cs g.t g.u

end Nested

/-! ### Linearity and the block estimate -/

section Block

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

theorem localOp_sub {ι : A → W} (hι : Function.Injective ι)
    (F G : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) :
    localOp ι hι F - localOp ι hι G = localOp ι hι (fun x => F x - G x) := by
  ext ψ x
  simp only [sub_apply, localOp_apply, PiLp.sub_apply]

/-- The register vector carrying `φ` on the exposed wires at the outside
configuration of `x`. -/
def put (ι : A → W) (hι : Function.Injective ι) (x : Cfg W) (φ : Reg A Q) : Reg W Q :=
  (layout ι hι).symm (WithLp.toLp 2 (Pi.single (outPart ι x) φ))

omit [CompleteSpace Q] in
theorem put_apply {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (φ : Reg A Q)
    (y : Cfg W) :
    put ι hι x φ y = if outPart ι y = outPart ι x then φ (fun a => y (ι a)) else 0 := by
  rw [put, layout_symm_apply]
  by_cases h : outPart ι y = outPart ι x
  · rw [if_pos h]
    change (Pi.single (outPart ι x) φ : Cfg (Out ι) → Reg A Q) (outPart ι y) _ = _
    rw [h, Pi.single_eq_same]
  · rw [if_neg h]
    change (Pi.single (outPart ι x) φ : Cfg (Out ι) → Reg A Q) (outPart ι y) _ = _
    rw [Pi.single_eq_of_ne h]
    rfl

theorem localOp_put {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) (x : Cfg W) (φ : Reg A Q) :
    localOp ι hι F (put ι hι x φ) = put ι hι x (F (clearCfg ι x) φ) := by
  apply PiLp.ext
  intro y
  rw [localOp_apply, put_apply]
  have hslice : slice ι (put ι hι x φ) y =
      if outPart ι y = outPart ι x then φ else 0 := by
    apply PiLp.ext
    intro b
    rw [slice_apply, put_apply]
    have hout : outPart ι (overwrite ι y b) = outPart ι y := outPart_joinCfg ι _ b
    have hb : (fun a => overwrite ι y b (ι a)) = b := funext (fun a => overwrite_apply_ι hι y b a)
    rw [hout, hb]
    split_ifs <;> rfl
  rw [hslice]
  by_cases h : outPart ι y = outPart ι x
  · rw [if_pos h, if_pos h]
    have hc : clearCfg ι y = clearCfg ι x := by
      simp only [clearCfg, overwrite, h]
    rw [hc]
  · rw [if_neg h, if_neg h, map_zero]
    rfl

omit [CompleteSpace Q] in
theorem norm_put {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (φ : Reg A Q) :
    ‖put ι hι x φ‖ = ‖φ‖ := by
  rw [put, LinearIsometryEquiv.norm_map]
  rw [PiLp.norm_eq_of_L2]
  rw [Finset.sum_eq_single (outPart ι x)]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [CompleteSpace Q] in
/-- Sums of `put` vectors at distinct outside configurations are orthogonal. -/
theorem norm_sum_put_sq {ι : A → W} (hι : Function.Injective ι) {Λ : Type*} [Fintype Λ]
    (c : Λ → Cfg W) (hc : ∀ i j, outPart ι (c i) = outPart ι (c j) → i = j)
    (φ : Λ → Reg A Q) :
    ‖∑ i, put ι hι (c i) (φ i)‖ ^ 2 = ∑ i, ‖φ i‖ ^ 2 := by
  classical
  have hsum : ∑ i, put ι hι (c i) (φ i) =
      (layout ι hι).symm (WithLp.toLp 2 (∑ i, Pi.single (outPart ι (c i)) (φ i))) := by
    simp only [put, ← map_sum, WithLp.toLp_sum]
  rw [hsum, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
  have hcoord : ∀ y : Cfg (Out ι),
      ‖(∑ i, Pi.single (outPart ι (c i)) (φ i) : Cfg (Out ι) → Reg A Q) y‖ ^ 2 =
        ∑ i, if outPart ι (c i) = y then ‖φ i‖ ^ 2 else 0 := by
    intro y
    rw [Finset.sum_apply]
    by_cases hy : ∃ i, outPart ι (c i) = y
    · obtain ⟨i, rfl⟩ := hy
      rw [Finset.sum_eq_single i, Pi.single_eq_same, Finset.sum_eq_single i, if_pos rfl]
      · intro j _ hj
        rw [if_neg]
        intro h
        exact hj (hc j i h)
      · intro h; exact absurd (Finset.mem_univ i) h
      · intro j _ hj
        rw [Pi.single_eq_of_ne]
        intro h
        exact hj (hc i j h).symm
      · intro h; exact absurd (Finset.mem_univ i) h
    · push Not at hy
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · simp
      · intro i _
        rw [if_neg (hy i)]
      · intro i _
        rw [Pi.single_eq_of_ne (Ne.symm (hy i))]
  change ∑ y, ‖(∑ i, Pi.single (outPart ι (c i)) (φ i) : Cfg (Out ι) → Reg A Q) y‖ ^ 2 = _
  simp only [hcoord]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_ite_eq]
  simp

end Block

/-! ### Payload-controlled operators -/

section Payload

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The payload operator `O` on the configurations satisfying the literals
`cs`, and the identity elsewhere. -/
def pctl (cs : List (W × Bool)) (O : Q →L[ℂ] Q) : Reg W Q →L[ℂ] Reg W Q :=
  ofCoords (fun x => if ctrlOK cs x then O ∘L coord x else coord x)

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem pctl_apply (cs : List (W × Bool)) (O : Q →L[ℂ] Q) (ψ : Reg W Q) (x : Cfg W) :
    pctl cs O ψ x = if ctrlOK cs x then O (ψ x) else ψ x := by
  rw [pctl, ofCoords_apply]
  split_ifs <;> rfl

omit [DecidableEq W] [CompleteSpace Q] in
theorem pctl_bas (cs : List (W × Bool)) (O : Q →L[ℂ] Q) (x : Cfg W) (q : Q) :
    pctl cs O (bas x q) = if ctrlOK cs x then bas x (O q) else bas x q := by
  apply PiLp.ext
  intro y
  rw [pctl_apply]
  by_cases hy : y = x
  · subst hy
    split_ifs <;> simp
  · by_cases hc : ctrlOK cs x = true <;> by_cases hcy : ctrlOK cs y = true <;> simp [hy, hc, hcy]

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem pctl_comp (cs : List (W × Bool)) (O O' : Q →L[ℂ] Q) :
    pctl cs O ∘L pctl cs O' = pctl cs (O ∘L O') := by
  ext ψ x
  simp only [comp_apply, pctl_apply]
  split_ifs <;> rfl

omit [Fintype W] [DecidableEq W] [CompleteSpace Q] in
theorem pctl_one (cs : List (W × Bool)) : pctl cs (1 : Q →L[ℂ] Q) = 1 := by
  ext ψ x
  rw [pctl_apply]
  split_ifs <;> rfl

theorem pctl_adjoint (cs : List (W × Bool)) (O : Q →L[ℂ] Q) :
    (pctl cs O)† = pctl cs (O†) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_right ℂ
  intro φ
  rw [adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [pctl_apply, pctl_apply]
  split_ifs
  · rw [adjoint_inner_left]
  · rfl

theorem pctl_isUnitary (cs : List (W × Bool)) (O : Q →L[ℂ] Q) (hO : IsUnitary O) :
    IsUnitary (pctl (W := W) cs O) := by
  constructor
  · rw [star_eq_adjoint, pctl_adjoint, mul_def, pctl_comp, ← star_eq_adjoint, ← mul_def,
      hO.1, pctl_one]
  · rw [star_eq_adjoint, pctl_adjoint, mul_def, pctl_comp, ← star_eq_adjoint, ← mul_def,
      hO.2, pctl_one]

/-- A payload-controlled operator never changes a configuration. -/
theorem pres2_pctl (S : Cfg W → Prop) (cs : List (W × Bool)) (O : Q →L[ℂ] Q) :
    Pres2 S (pctl cs O) := by
  constructor
  · intro ψ hψ x hx
    rw [pctl_apply, hψ x hx]
    split_ifs <;> simp
  · rw [pctl_adjoint]
    intro ψ hψ x hx
    rw [pctl_apply, hψ x hx]
    split_ifs <;> simp

end Payload

end

end SparseHamiltonian.GateODE
