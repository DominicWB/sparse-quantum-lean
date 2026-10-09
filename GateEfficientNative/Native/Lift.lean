import GateEfficientNative.Native.Private

/-!
# Lifting native implementations into a larger register

* `selOp Dfam`: the selected private operation of a family `Dfam` (indexed by
  the configuration of the selection wires) on the flattened private register
  `Fin a ⊕ S`.
* `localOp_ctrlIdeal_selOp`: the enable-controlled selected operation of a
  native implementation, placed in a larger register, is the flattened
  enable-controlled oracle call on the ancilla and system wires.
* `approxOn_flatMap`: substituting implementations for the instructions of a
  circuit adds their errors (`ApproxOn` telescoping on clean work wires).
* `localOp_ctrl_gRun`, `ctrlGates_agrees`: a gate list on exposed wires,
  enabled by an outside wire, is the list of gates with one more control; a
  gate with three controls receives the enable through the released AND chain
  on three clean flags (`ctrlGate`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (localOp_localOp localOp_localOp' overwrite_apply_ι overwrite_apply_out ctrlOK_map)
open scoped InnerProduct BigOperators

/-! ### Selected private operations -/

section Sel

variable {Sel S : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype S] [DecidableEq S] {a : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The selected private operation of a family on the flattened private register. -/
def selOp (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))) :
    Reg (Sel ⊕ (Fin a ⊕ S)) R →L[ℂ] Reg (Sel ⊕ (Fin a ⊕ S)) R :=
  localOp Sum.inr Sum.inr_injective (fun y => conj (Dfam (fun s => y (Sum.inl s))))

theorem selOp_isUnitary (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)))
    (hD : ∀ w, IsUnitary (Dfam w)) : IsUnitary (selOp Dfam) :=
  localOp_isUnitary _ _ (fun _ => conj_isUnitary (hD _))

theorem selOp_adjoint (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))) :
    (selOp Dfam)† = selOp (fun w => (Dfam w)†) := by
  unfold selOp
  rw [localOp_adjoint]
  congr 1
  funext y
  rw [conj_adjoint]

end Sel

/-! ### The lifted enable-controlled operation -/

section LiftIdeal

variable {Sel Z S : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype Z] [DecidableEq Z]
  [Fintype S] [DecidableEq S] {a bT bP A : ℕ}
variable {Vb : Type*} [Fintype Vb] [DecidableEq Vb]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem ite_localOp_one {W B : Type*} [Fintype W] [DecidableEq W] [Fintype B] [DecidableEq B]
    {ι : B → W} (hι : Function.Injective ι) (p : Bool) (O : Reg B R →L[ℂ] Reg B R) :
    (if p then localOp ι hι (fun _ => O) else 1) =
      localOp ι hι (fun _ => if p then O else (1 : Reg B R →L[ℂ] Reg B R)) := by
  cases p
  · simp only [Bool.false_eq_true, if_false]
    exact (localOp_one hι).symm
  · rfl

/-- **The enable-controlled selected operation, lifted.**  Placed along
`eP`, it is the operation that applies the flattened `Dfam` of the selection
read from the selection wires to the private wires, when the enable wire is
set. -/
theorem localOp_ctrlIdeal_selOp (eP : PWr Sel (Fin a ⊕ S) Z bT bP A ↪ Vb)
    (Dfam : Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))) :
    localOp eP eP.injective (fun _ => ctrlIdeal (selOp Dfam)) =
      localOp (fun p => eP (selPR (Sum.inr p)))
        (fun _ _ h => Sum.inr_injective (selPR.injective (eP.injective h)))
        (fun w => if w (eP enW) then conj (Dfam (fun s => w (eP (selPR (Sum.inl s))))) else 1) := by
  unfold ctrlIdeal selOp
  have h1 : (fun y : Cfg (PWr Sel (Fin a ⊕ S) Z bT bP A) =>
      if y enW then localOp Sum.inr Sum.inr_injective
        (fun y' => conj (Dfam (fun s => y' (Sum.inl s)))) else 1) =
      (fun y => localOp Sum.inr Sum.inr_injective
        (fun y' : Cfg (Sel ⊕ (Fin a ⊕ S)) =>
          if y enW then conj (Dfam (fun s => y' (Sum.inl s))) else 1)) := by
    funext y
    cases hy : y enW
    · simp only [Bool.false_eq_true, if_false]
      exact (localOp_one _).symm
    · rfl
  rw [h1, localOp_localOp selPR.injective Sum.inr_injective
    (fun y y' => if y enW then conj (Dfam (fun s => y' (Sum.inl s))) else 1)]
  rw [localOp_localOp' eP.injective (selPR.injective.comp Sum.inr_injective)
    (fun p => eP (selPR (Sum.inr p)))
    (fun p q h => Sum.inr_injective (selPR.injective (eP.injective h))) (fun _ => rfl)
    (fun _ z => if clearCfg selPR z enW then
      conj (Dfam (fun s => clearCfg Sum.inr (fun c => z (selPR c)) (Sum.inl s))) else 1)]
  apply localOp_congr
  intro w
  set w' := clearCfg (fun p => eP (selPR (Sum.inr p))) w with hw'
  have hen : clearCfg selPR (clearCfg (selPR ∘ Sum.inr) (fun c => w' (eP c))) enW =
      w' (eP enW) :=
    (clearCfg_apply_out selPR _ enW (fun p hp => by simp [selPR, enW] at hp)).trans
      (clearCfg_apply_out (selPR ∘ Sum.inr) _ enW (fun p hp => by simp [selPR, enW] at hp))
  have hsel : (fun s => clearCfg Sum.inr (fun a => clearCfg (selPR ∘ Sum.inr)
      (fun c => w' (eP c)) (selPR a)) (Sum.inl s)) = (fun s => w' (eP (selPR (Sum.inl s)))) := by
    funext s
    exact (clearCfg_apply_out Sum.inr _ (Sum.inl s) (fun p hp => by cases hp)).trans
      (clearCfg_apply_out (selPR ∘ Sum.inr) _ (selPR (Sum.inl s))
        (fun p hp => by simp [selPR] at hp))
  simp only [hen, hsel]

end LiftIdeal

/-! ### Telescoping substitution -/

section Telescope

variable {V Y J : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

/-- The product of operators along a list; the head acts first. -/
def prodOps {α : Type*} (O : α → Reg V R →L[ℂ] Reg V R) : List α → Reg V R →L[ℂ] Reg V R
  | [] => 1
  | a :: l => prodOps O l ∘L O a

/-- Substituted circuits of contractions are contractions. -/
theorem nrun_flatMap_le {α : Type*} (M : α → List (NInstr V Y J)) (l : List α)
    (hM : ∀ a ∈ l, ∀ ψ, ‖nrun prim (M a) ψ‖ ≤ ‖ψ‖) (ψ : Reg V R) :
    ‖nrun prim (l.flatMap M) ψ‖ ≤ ‖ψ‖ := by
  induction l generalizing ψ with
  | nil => simp
  | cons a l ih =>
      rw [List.flatMap_cons, nrun_append, comp_apply]
      exact (ih (fun b hb => hM b (List.mem_cons_of_mem a hb)) _).trans (hM a List.mem_cons_self ψ)

/-- Substituting implementations instruction by instruction adds the errors. -/
theorem approxOn_flatMap {α : Type*} (S : Cfg V → Prop) (M : α → List (NInstr V Y J))
    (O : α → Reg V R →L[ℂ] Reg V R) (δ : α → ℝ) (l : List α)
    (h : ∀ a ∈ l, ApproxOn S (nrun prim (M a)) (O a) (δ a))
    (hO : ∀ a ∈ l, Preserves S (O a)) (hOn : ∀ a ∈ l, ∀ ψ, ‖O a ψ‖ ≤ ‖ψ‖)
    (hM : ∀ a ∈ l, ∀ ψ, ‖nrun prim (M a) ψ‖ ≤ ‖ψ‖) (hδ : ∀ a ∈ l, 0 ≤ δ a) :
    ApproxOn S (nrun prim (l.flatMap M)) (prodOps O l) ((l.map δ).sum) := by
  induction l with
  | nil =>
      intro ψ _
      simp [prodOps]
  | cons a l ih =>
      have ih' := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
        (fun b hb => hO b (List.mem_cons_of_mem a hb))
        (fun b hb => hOn b (List.mem_cons_of_mem a hb))
        (fun b hb => hM b (List.mem_cons_of_mem a hb))
        (fun b hb => hδ b (List.mem_cons_of_mem a hb))
      have hcontr : ∀ ψ, ‖nrun prim (l.flatMap M) ψ‖ ≤ ‖ψ‖ :=
        nrun_flatMap_le prim M l (fun b hb => hM b (List.mem_cons_of_mem a hb))
      have hsum : 0 ≤ (l.map δ).sum :=
        List.sum_nonneg (fun x hx => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
          exact hδ b (List.mem_cons_of_mem a hb))
      rw [List.flatMap_cons, nrun_append, prodOps, List.map_cons, List.sum_cons]
      exact (h a List.mem_cons_self).comp (hO a List.mem_cons_self) (hOn a List.mem_cons_self) ih'
        hcontr hsum

/-- The operator of a circuit is the product of its instruction operators. -/
theorem nrun_eq_prodOps (is : List (NInstr V Y J)) :
    nrun prim is = prodOps (fun i => i.eval prim) is := by
  induction is with
  | nil => rfl
  | cons i is ih => rw [nrun_cons, ih]; rfl

end Telescope

/-! ### Enabled gate lists -/

section Ctrl

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A gate on exposed wires with one more control on the outside wire `w₀`. -/
def ctrlMap (w₀ : V) (e : A → V) (g : Gate A) : Gate V :=
  ⟨(w₀, true) :: g.cs.map (fun c => (e c.1, c.2)), e g.t, g.u⟩

/-- An enabled elementary gate on exposed wires. -/
theorem localOp_ctrl_gateOp {e : A → V} (he : Function.Injective e) (w₀ : V)
    (hw₀ : ∀ a, e a ≠ w₀) (g : Gate A) (hg : ∀ c ∈ g.cs, c.1 ≠ g.t) :
    localOp e he (fun y => if y w₀ then gateOp (Q := Q) g.cs g.t g.u else 1) =
      (ctrlMap w₀ e g).op := by
  unfold gateOp
  rw [localOp_ite_condOp he w₀ hw₀ g.t _ (fun x b => by simp only [ctrlOK_update g.cs g.t hg])]
  unfold Gate.op gateOp ctrlMap
  congr 1
  funext y
  simp only [ctrlOK_cons, ctrlOK_map]
  cases hy : y w₀ <;> simp

/-- An enabled gate list on exposed wires is the list with one more control. -/
theorem localOp_ctrl_gRun {e : A → V} (he : Function.Injective e) (w₀ : V)
    (hw₀ : ∀ a, e a ≠ w₀) (gs : List (Gate A)) (hgs : ∀ g ∈ gs, ∀ c ∈ g.cs, c.1 ≠ g.t) :
    localOp e he (fun y => if y w₀ then gRun (Q := Q) gs else 1) =
      gRun (gs.map (ctrlMap w₀ e)) := by
  induction gs with
  | nil =>
      simp only [gRun_nil, ite_self, List.map_nil]
      exact localOp_one he
  | cons g gs ih =>
      have hsplit : (fun y : Cfg V => if y w₀ then gRun (Q := Q) (g :: gs) else 1) =
          (fun y => (if y w₀ then gRun (Q := Q) gs else 1) ∘L
            (if y w₀ then gateOp (Q := Q) g.cs g.t g.u else 1)) := by
        funext y
        cases hy : y w₀
        · simp only [Bool.false_eq_true, if_false]
          exact (Sim.one_comp' _).symm
        · rfl
      rw [hsplit, ← localOp_comp, ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')),
        localOp_ctrl_gateOp he w₀ hw₀ g (hgs g List.mem_cons_self), List.map_cons, gRun_cons]

/-- One enabled gate with at most three controls of its own, as elementary
gates: one more control when it has at most two, the released AND chain on
the flags `fl` otherwise. -/
def ctrlGate (w₀ : V) (fl : List V) (h : Gate V) : List (Gate V) :=
  if h.cs.length ≤ 2 then [⟨(w₀, true) :: h.cs, h.t, h.u⟩]
  else mcGate ((w₀, true) :: h.cs) fl h.t h.u

theorem ctrlGate_agrees (w₀ : V) (fl : List V) (h : Gate V) (hlen : h.cs.length ≤ 3)
    (hfl : 3 ≤ fl.length) (hnd : fl.Nodup) (hw₀t : w₀ ≠ h.t) (hct : ∀ c ∈ h.cs, c.1 ≠ h.t)
    (hft : ∀ f ∈ fl, f ≠ h.t) (hw₀f : ∀ f ∈ fl, w₀ ≠ f) (hcf : ∀ c ∈ h.cs, ∀ f ∈ fl, c.1 ≠ f)
    (S : Cfg V → Prop) (hS : ∀ x, S x → ∀ f ∈ fl, x f = false)
    (hSt : ∀ x b, S x → S (Function.update x h.t b)) :
    Agrees S (gRun (Q := Q) (ctrlGate w₀ fl h)) (gateOp ((w₀, true) :: h.cs) h.t h.u) := by
  unfold ctrlGate
  split_ifs with h2
  · rw [gRun_singleton]
    exact Agrees.refl _ _
  · apply mcGate_agrees _ fl h.t h.u (by simp; omega) hnd
    · intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hw₀t
      · exact hct l hl
    · exact hft
    · intro l hl f hf
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hw₀f f hf
      · exact hcf l hl f hf
    · exact hS
    · exact hSt

omit [Fintype V] [DecidableEq V] in
theorem ctrlGate_ok (w₀ : V) (fl : List V) (h : Gate V) (hh : GateOK 3 h) (hnd : fl.Nodup)
    (hw₀t : w₀ ≠ h.t) (hft : ∀ f ∈ fl, f ≠ h.t) (hw₀f : ∀ f ∈ fl, w₀ ≠ f)
    (hcf : ∀ c ∈ h.cs, ∀ f ∈ fl, c.1 ≠ f) : ∀ g ∈ ctrlGate w₀ fl h, GateOK 3 g := by
  unfold ctrlGate
  split_ifs with h2
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst hg
    refine ⟨by simp; omega, ?_, hh.2.2⟩
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hw₀t
    · exact hh.2.1 c hc
  · intro g hg
    refine (mcGate_valid _ fl h.t h.u hh.2.2 hnd ?_ hft ?_ g hg).mono (by norm_num)
    · intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hw₀t
      · exact hh.2.1 l hl
    · intro l hl f hf
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact hw₀f f hf
      · exact hcf l hl f hf

omit [Fintype V] [DecidableEq V] in
theorem ctrlGate_length (w₀ : V) (fl : List V) (h : Gate V) (hlen : h.cs.length ≤ 3)
    (hfl : 3 ≤ fl.length) : (ctrlGate w₀ fl h).length ≤ 7 := by
  unfold ctrlGate
  split_ifs with h2
  · simp
  · have h3 : h.cs.length = 3 := by omega
    simp only [mcGate, List.length_append, gInv_length, List.length_cons, List.length_nil]
    rw [andChain_length _ _ _ (by omega)]
    omega

end Ctrl

end

end SparseHamiltonian.GateNative
