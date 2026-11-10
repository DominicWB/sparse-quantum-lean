import GeneralSparseODE.Embed
import GateEfficientNative.ODE.Constant
import GateEfficientNative.ODE.Time

/-!
# Source circuits on the padded system register

A source circuit of the general problem acts on control wires `C`, the `k` qubits of the index
register and scratch `Zs` (`(C ⊕ Fin k) ⊕ Zs`), calling the supplied primitives. On the padded
system register of `k + 1` qubits it acts on the low wires and leaves the marker untouched
(`liftC`, along `liftE`). Its ideal, a family of operators on the system selected by the control
wires, becomes the same family on the low wires, the identity on the marker (`lowOp`):

* `liftB_ctl_lowOp`: the lifted ideal of a control-selected family is the family of the lifts;
* `approxOn_liftC`: a source circuit within `ζ` of its ideal on clean scratch gives a lifted circuit
  within `ζ` of the lifted ideal on clean scratch;
* `srcIdeal_lowOp`, `approxOn_liftSrc`: the controlled source preparations (`srcIdeal`);
* `loadIdeal_lowOp`, `approxOn_liftLoad`: the controlled loading of the time-dependent solver
  (`loadIdeal`);
* `valid_liftC`, `nGatesN_liftC`, `nCallsN_liftC`: validity and counts are unchanged.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct

section Wires

variable (C Zs : Type*) (k : ℕ)

theorem liftE_injective : Function.Injective
    (Sum.map (Sum.map id Fin.castSucc) id : (C ⊕ Fin k) ⊕ Zs → (C ⊕ Fin (k + 1)) ⊕ Zs) :=
  Sum.map_injective.2 ⟨Sum.map_injective.2 ⟨Function.injective_id, Fin.castSucc_injective k⟩,
    Function.injective_id⟩

/-- **The wires of a source circuit on the padded system register**: the control wires, the low
`k` system wires and the scratch. -/
def liftE : (C ⊕ Fin k) ⊕ Zs ↪ (C ⊕ Fin (k + 1)) ⊕ Zs :=
  ⟨Sum.map (Sum.map id Fin.castSucc) id, liftE_injective C Zs k⟩

end Wires

section Circuits

variable {C Zs Y J : Type*} {k : ℕ}

/-- **The source circuit on the padded system register.** -/
def liftC (Cc : List (NInstr ((C ⊕ Fin k) ⊕ Zs) Y J)) :
    List (NInstr ((C ⊕ Fin (k + 1)) ⊕ Zs) Y J) :=
  Cc.map (NInstr.map (liftE C Zs k))

theorem valid_liftC (Cc : List (NInstr ((C ⊕ Fin k) ⊕ Zs) Y J)) (h : ∀ i ∈ Cc, i.Valid) :
    ∀ i ∈ liftC Cc, i.Valid :=
  valid_map_list _ Cc h

theorem nGatesN_liftC (Cc : List (NInstr ((C ⊕ Fin k) ⊕ Zs) Y J)) :
    nGatesN (liftC Cc) = nGatesN Cc :=
  nGatesN_map _ Cc

theorem nCallsN_liftC (p : J → Bool) (Cc : List (NInstr ((C ⊕ Fin k) ⊕ Zs) Y J)) :
    nCallsN p (liftC Cc) = nCallsN p Cc :=
  nCallsN_map _ _ Cc

end Circuits

section Ideal

variable {C Zs : Type*} [Fintype C] [DecidableEq C] [Fintype Zs] [DecidableEq Zs] {k : ℕ}

/-- **The lifted ideal of a control-selected family**: the family `F` of operators on the system,
selected by the control wires, on the low wires of the padded system register (the identity on the
marker), is the lift of the family on the `k` system wires. -/
theorem liftB_ctl_lowOp (F : Cfg C → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) :
    liftB (X := Zs) (localOp (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) Sum.inr_injective
        (fun y => lowOp (F (fun c => y (Sum.inl c))))) =
      localOp (liftE C Zs k) (liftE C Zs k).injective
        (fun _ => liftB (X := Zs) (localOp (Sum.inr : Fin k → C ⊕ Fin k) Sum.inr_injective
          (fun y => F (fun c => y (Sum.inl c))))) := by
  set ρ : Fin k → (C ⊕ Fin (k + 1)) ⊕ Zs := fun i => Sum.inl (Sum.inr (Fin.castSucc i)) with hρ
  have hρi : Function.Injective ρ := by
    intro i j h
    simp only [hρ, Sum.inl.injEq, Sum.inr.injEq] at h
    exact Fin.castSucc_injective k h
  unfold liftB lowOp
  have hL1 : localOp (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) Sum.inr_injective
      (fun y => localOp (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
        (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).injective (fun _ => F (fun c => y (Sum.inl c)))) =
      localOp ((Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) ∘ (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)))
        (Sum.inr_injective.comp (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).injective)
        (fun z => F (fun c => clearCfg (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) z (Sum.inl c))) :=
    GateODE.localOp_localOp Sum.inr_injective (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).injective
      (fun y' _ => F (fun c => y' (Sum.inl c)))
  have hL : localOp (Sum.inl : C ⊕ Fin (k + 1) → (C ⊕ Fin (k + 1)) ⊕ Zs) Sum.inl_injective
      (fun _ => localOp ((Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) ∘
        (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)))
        (Sum.inr_injective.comp (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).injective)
        (fun z => F (fun c => clearCfg (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) z (Sum.inl c)))) =
      localOp ρ hρi (fun w => F (fun c => clearCfg (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1))
        (clearCfg ((Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) ∘
          (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) (fun a => w (Sum.inl a))) (Sum.inl c))) :=
    GateODE.localOp_localOp' Sum.inl_injective _ ρ hρi (fun _ => rfl)
      (fun _ z => F (fun c => clearCfg (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) z (Sum.inl c)))
  have hR1 : localOp (Sum.inl : C ⊕ Fin k → (C ⊕ Fin k) ⊕ Zs) Sum.inl_injective
      (fun _ => localOp (Sum.inr : Fin k → C ⊕ Fin k) Sum.inr_injective
        (fun y => F (fun c => y (Sum.inl c)))) =
      localOp ((Sum.inl : C ⊕ Fin k → (C ⊕ Fin k) ⊕ Zs) ∘ (Sum.inr : Fin k → C ⊕ Fin k))
        (Sum.inl_injective.comp Sum.inr_injective)
        (fun z => F (fun c => clearCfg (Sum.inr : Fin k → C ⊕ Fin k)
          (fun a => z (Sum.inl a)) (Sum.inl c))) :=
    GateODE.localOp_localOp Sum.inl_injective Sum.inr_injective
      (fun _ y => F (fun c => y (Sum.inl c)))
  have hR : localOp (liftE C Zs k) (liftE C Zs k).injective
      (fun _ => localOp ((Sum.inl : C ⊕ Fin k → (C ⊕ Fin k) ⊕ Zs) ∘ (Sum.inr : Fin k → C ⊕ Fin k))
        (Sum.inl_injective.comp Sum.inr_injective)
        (fun z => F (fun c => clearCfg (Sum.inr : Fin k → C ⊕ Fin k)
          (fun a => z (Sum.inl a)) (Sum.inl c)))) =
      localOp ρ hρi (fun w => F (fun c => clearCfg (Sum.inr : Fin k → C ⊕ Fin k)
        (fun a => clearCfg ((Sum.inl : C ⊕ Fin k → (C ⊕ Fin k) ⊕ Zs) ∘
          (Sum.inr : Fin k → C ⊕ Fin k)) (fun a' => w (liftE C Zs k a')) (Sum.inl a))
          (Sum.inl c))) :=
    GateODE.localOp_localOp' (liftE C Zs k).injective _ ρ hρi (fun _ => rfl)
      (fun _ z => F (fun c => clearCfg (Sum.inr : Fin k → C ⊕ Fin k)
        (fun a => z (Sum.inl a)) (Sum.inl c)))
  have hmid : localOp ρ hρi (fun w => F (fun c => clearCfg (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1))
        (clearCfg ((Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) ∘
          (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) (fun a => w (Sum.inl a))) (Sum.inl c))) =
      localOp ρ hρi (fun w => F (fun c => clearCfg (Sum.inr : Fin k → C ⊕ Fin k)
        (fun a => clearCfg ((Sum.inl : C ⊕ Fin k → (C ⊕ Fin k) ⊕ Zs) ∘
          (Sum.inr : Fin k → C ⊕ Fin k)) (fun a' => w (liftE C Zs k a')) (Sum.inl a))
          (Sum.inl c))) := by
    congr 1
    funext w
    congr 1
    funext c
    have e1 : ∀ x : Cfg (C ⊕ Fin (k + 1)),
        clearCfg (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) x (Sum.inl c) = x (Sum.inl c) :=
      fun x => GateNative.clearCfg_apply_out _ x _ (fun a h => by cases h)
    have e2 : ∀ x : Cfg (C ⊕ Fin (k + 1)),
        clearCfg ((Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) ∘
          (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))) x (Sum.inl c) = x (Sum.inl c) :=
      fun x => GateNative.clearCfg_apply_out _ x _ (fun a h => by cases h)
    have e3 : ∀ x : Cfg (C ⊕ Fin k),
        clearCfg (Sum.inr : Fin k → C ⊕ Fin k) x (Sum.inl c) = x (Sum.inl c) :=
      fun x => GateNative.clearCfg_apply_out _ x _ (fun a h => by cases h)
    have e4 : ∀ x : Cfg ((C ⊕ Fin k) ⊕ Zs),
        clearCfg ((Sum.inl : C ⊕ Fin k → (C ⊕ Fin k) ⊕ Zs) ∘ (Sum.inr : Fin k → C ⊕ Fin k)) x
          (Sum.inl (Sum.inl c)) = x (Sum.inl (Sum.inl c)) :=
      fun x => GateNative.clearCfg_apply_out _ x _ (fun a h => by cases h)
    rw [e1, e2, e3, e4]
    rfl
  calc localOp (Sum.inl : C ⊕ Fin (k + 1) → (C ⊕ Fin (k + 1)) ⊕ Zs) Sum.inl_injective
        (fun _ => localOp (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) Sum.inr_injective
          (fun y => localOp (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))
            (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).injective
              (fun _ => F (fun c => y (Sum.inl c)))))
      = localOp (Sum.inl : C ⊕ Fin (k + 1) → (C ⊕ Fin (k + 1)) ⊕ Zs) Sum.inl_injective
          (fun _ => localOp ((Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) ∘
            (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)))
            (Sum.inr_injective.comp (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)).injective)
            (fun z => F (fun c => clearCfg (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) z
              (Sum.inl c)))) := by rw [hL1]
    _ = _ := hL
    _ = _ := hmid
    _ = _ := hR.symm
    _ = localOp (liftE C Zs k) (liftE C Zs k).injective
          (fun _ => localOp (Sum.inl : C ⊕ Fin k → (C ⊕ Fin k) ⊕ Zs) Sum.inl_injective
            (fun _ => localOp (Sum.inr : Fin k → C ⊕ Fin k) Sum.inr_injective
              (fun y => F (fun c => y (Sum.inl c))))) := by rw [hR1]

/-- **The source preparation on the low wires**: the controlled source preparation of `lowOp O` is
the controlled source preparation of `O`, written as a control-selected family. -/
theorem srcIdeal_lowOp (c : Bool) (O : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) :
    srcIdeal c (lowOp O) = localOp (Sum.inr : Fin (k + 1) → Unit ⊕ Fin (k + 1)) Sum.inr_injective
      (fun y => lowOp ((fun w : Cfg Unit => if w () = c then O else 1) (fun u => y (Sum.inl u)))) := by
  unfold srcIdeal
  congr 1
  funext y
  show (if y (Sum.inl ()) = c then lowOp O else 1) =
    lowOp (if y (Sum.inl ()) = c then O else 1)
  split_ifs
  · rfl
  · exact lowOp_one.symm

theorem srcIdeal_eq (c : Bool) (O : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) :
    srcIdeal c O = localOp (Sum.inr : Fin k → Unit ⊕ Fin k) Sum.inr_injective
      (fun y => (fun w : Cfg Unit => if w () = c then O else 1) (fun u => y (Sum.inl u))) := rfl

/-- **A circuit within `ζ` of a control-selected family on clean scratch** gives the lifted
circuit within `ζ` of the lifted family on clean scratch. -/
theorem approxOn_liftC {Y J : Type*} [Fintype Y] [DecidableEq Y] (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (Cc : List (NInstr ((C ⊕ Fin k) ⊕ Zs) Y J)) (F : Cfg C → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    {ζ : ℝ} (hζ : 0 ≤ ζ)
    (h : ApproxOn CleanX (nrun prim Cc) (liftB (X := Zs) (localOp (Sum.inr : Fin k → C ⊕ Fin k)
      Sum.inr_injective (fun y => F (fun c => y (Sum.inl c))))) ζ) :
    ApproxOn CleanX (nrun prim (liftC Cc)) (liftB (X := Zs)
      (localOp (Sum.inr : Fin (k + 1) → C ⊕ Fin (k + 1)) Sum.inr_injective
        (fun y => lowOp (F (fun c => y (Sum.inl c)))))) ζ := by
  rw [liftB_ctl_lowOp, liftC, nrun_map]
  refine approxOn_localOp _ _ _ hζ ?_ (fun _ => h)
  intro y hy z
  exact hy z

/-- **The lifted source circuits** are within `ζ` of the source preparations of the lifted
interfaces. -/
theorem approxOn_liftSrc {Y J : Type*} [Fintype Y] [DecidableEq Y]
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Cc : List (NInstr ((Unit ⊕ Fin k) ⊕ Zs) Y J))
    (c : Bool) (O : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (h : ApproxOn CleanX (nrun prim Cc) (liftB (X := Zs) (srcIdeal c O)) ζ) :
    ApproxOn CleanX (nrun prim (liftC Cc)) (liftB (X := Zs) (srcIdeal c (lowOp O))) ζ := by
  rw [srcIdeal_lowOp]
  exact approxOn_liftC prim Cc (fun w : Cfg Unit => if w () = c then O else 1) hζ h

/-- **The lifted loading circuit** is within `ζ` of the controlled loading of the lifted
interfaces. -/
theorem approxOn_liftLoad {Y J : Type*} [Fintype Y] [DecidableEq Y] {m : ℕ}
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Cc : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) Y J))
    (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (h : ApproxOn CleanX (nrun prim Cc) (liftB (X := Zs) (loadIdeal Jl)) ζ) :
    ApproxOn CleanX (nrun prim (liftC Cc)) (liftB (X := Zs) (loadIdeal (fun l => lowOp (Jl l))))
      ζ :=
  approxOn_liftC prim Cc (fun w => Jl (srcLab w)) hζ h

end Ideal

end

end SparseHamiltonian.GeneralSparseODE
