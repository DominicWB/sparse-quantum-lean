import GeneralSparseAccess.Compare

/-!
# Controlled calls with a reference prepared on clean wires

The manuscript's controlled reversible access (Lemma `access:lem:control`):
a supplied unitary `G` with a known valid input mapped to a basis state `y₀` with phase one is
controlled with three calls. One call writes `y₀ = G|0⟩` into a clean reference register, the
controlled-call gadget of `GateEfficientBinary` (`gadget`, one call) applies `G` on the target
exactly when the control wire holds `pol`, and one inverse call returns the reference to `|0⟩`
(`ctrlRef_agrees`). Only `G|0⟩ = |y₀⟩` and the unitarity of `G` enter the proof.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (put put_apply overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct

section Put

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
/-- `put` as a sum of basis vectors. -/
theorem put_eq_sum_bas {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) (φ : Reg A Q) :
    put ι hι x φ = ∑ d, bas (overwrite ι x d) (φ d) := by
  apply PiLp.ext
  intro y
  rw [put_apply, WithLp.ofLp_sum, Finset.sum_apply]
  by_cases hy : outPart ι y = outPart ι x
  · rw [if_pos hy, Finset.sum_eq_single (fun a => y (ι a))]
    · rw [bas_apply, if_pos]
      have := joinCfg_self hι y
      rw [overwrite, ← hy, this]
    · intro d _ hd
      rw [bas_apply, if_neg]
      intro h
      apply hd
      funext a
      rw [h, overwrite_apply_ι hι]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hy]
    symm
    apply Finset.sum_eq_zero
    intro d _
    rw [bas_apply, if_neg]
    intro h
    apply hy
    rw [h]
    exact outPart_joinCfg ι _ d

end Put

section Ref

variable {V E Y J : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The wires of a controlled call with a reference: the target, the dummy and the reference are
injective and pairwise disjoint, and the control is on none of them. -/
structure RefLayout (c : V) (T Dm Rf : E → V) : Prop where
  inj_T : Function.Injective T
  inj_Dm : Function.Injective Dm
  inj_Rf : Function.Injective Rf
  T_ne_Dm : ∀ e e', T e ≠ Dm e'
  T_ne_Rf : ∀ e e', T e ≠ Rf e'
  Dm_ne_Rf : ∀ e e', Dm e ≠ Rf e'
  T_ne_c : ∀ e, T e ≠ c
  Dm_ne_c : ∀ e, Dm e ≠ c
  Rf_ne_c : ∀ e, Rf e ≠ c

/-- **The controlled call with a reference** (`access:lem:control`): a call on a clean reference
register, the controlled-call gadget and the inverse call on the reference. -/
def ctrlRef (c : V) (pol : Bool) (T Dm Rf : E → V) (callT callR callR' : List (NInstr V Y J)) :
    List (NInstr V Y J) :=
  callR ++ gadget c pol T Dm Rf callT ++ callR'

/-- **The controlled call with a reference acts as `G` controlled on `c = pol`** on clean dummy and
reference registers, for every unitary `G` mapping the clean input to the basis state `y₀`. -/
theorem ctrlRef_agrees (prim : J → Reg Y R →L[ℂ] Reg Y R) (G : Reg E R →L[ℂ] Reg E R)
    (hG : IsUnitary G) (y0 : Cfg E) (hG0 : ∀ q, G (bas (fun _ => false) q) = bas y0 q)
    {c : V} (pol : Bool) {T Dm Rf : E → V} (L : RefLayout c T Dm Rf)
    (callT callR callR' : List (NInstr V Y J))
    (hcT : nrun prim callT = localOp T L.inj_T (fun _ => G))
    (hcR : nrun prim callR = localOp Rf L.inj_Rf (fun _ => G))
    (hcR' : nrun prim callR' = localOp Rf L.inj_Rf (fun _ => G†)) :
    Agrees (fun x => (∀ e, x (Dm e) = false) ∧ ∀ e, x (Rf e) = false)
      (nrun prim (ctrlRef c pol T Dm Rf callT callR callR'))
      (localOp T L.inj_T (fun x => if x c = pol then G else 1)) := by
  have hGadj : ∀ q, (G†) (bas y0 q) = bas (fun _ => false) q := by
    intro q
    rw [← hG0 q]
    have h1 : G† ∘L G = 1 := by
      have := hG.1
      rwa [star_eq_adjoint, mul_def] at this
    have := congrArg (fun F : Reg E R →L[ℂ] Reg E R => F (bas (fun _ => false) q)) h1
    simpa using this
  have hGd := gadget_agrees prim G y0 hG0 c pol T Dm Rf L.inj_T L.inj_Dm L.T_ne_Dm L.T_ne_Rf
    L.Dm_ne_Rf L.T_ne_c L.Dm_ne_c callT hcT
  apply agrees_of_bas
  rintro x ⟨hxD, hxR⟩ q
  have hxR0 : (fun e => x (Rf e)) = fun _ => false := funext hxR
  unfold ctrlRef
  rw [nrun_append, nrun_append, hcR, hcR', comp_apply, comp_apply]
  -- the reference is prepared
  rw [localOp_bas L.inj_Rf, hxR0, hG0, put_bas L.inj_Rf]
  set x' := overwrite Rf x y0 with hx'
  have hx'D : ∀ e, x' (Dm e) = false := fun e => by
    rw [hx', overwrite_apply_out Rf x y0 _ (fun e' h => L.Dm_ne_Rf e e' h.symm)]
    exact hxD e
  have hx'R : ∀ e, x' (Rf e) = y0 e := fun e => overwrite_apply_ι L.inj_Rf x y0 e
  rw [hGd _ (supp_bas x' ⟨hx'D, hx'R⟩ q)]
  -- both sides through the target
  rw [localOp_bas L.inj_T, localOp_bas L.inj_T]
  have hc1 : clearCfg T x' c = x c := by
    change overwrite T x' (fun _ => false) c = x c
    rw [overwrite_apply_out T _ _ c L.T_ne_c, hx',
      overwrite_apply_out Rf x y0 c L.Rf_ne_c]
  have hc2 : clearCfg T x c = x c := by
    change overwrite T x (fun _ => false) c = x c
    exact overwrite_apply_out T _ _ c L.T_ne_c
  have hT' : (fun e => x' (T e)) = fun e => x (T e) := funext fun e => by
    rw [hx', overwrite_apply_out Rf x y0 _ (fun e' h => L.T_ne_Rf e e' h.symm)]
  rw [hc1, hc2, hT']
  set φ := (if x c = pol then G else 1) (bas (fun e => x (T e)) q)
  -- the inverse call returns the reference
  rw [put_eq_sum_bas L.inj_T, put_eq_sum_bas L.inj_T, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [localOp_bas L.inj_Rf]
  have hR : (fun e => overwrite T x' d (Rf e)) = y0 := funext fun e => by
    rw [overwrite_apply_out T x' d _ (fun e' h => L.T_ne_Rf e' e h), hx'R]
  rw [hR, hGadj, put_bas L.inj_Rf]
  congr 1
  funext w
  by_cases hw : ∃ e, Rf e = w
  · obtain ⟨e, rfl⟩ := hw
    rw [overwrite_apply_ι L.inj_Rf, overwrite_apply_out T x d _ (fun e' h => L.T_ne_Rf e' e h)]
    exact (hxR e).symm
  · have hw' : ∀ e, Rf e ≠ w := fun e h => hw ⟨e, h⟩
    rw [overwrite_apply_out Rf _ _ w hw']
    by_cases hwT : ∃ e, T e = w
    · obtain ⟨e, rfl⟩ := hwT
      rw [overwrite_apply_ι L.inj_T, overwrite_apply_ι L.inj_T]
    · have hwT' : ∀ e, T e ≠ w := fun e h => hwT ⟨e, h⟩
      rw [overwrite_apply_out T _ d w hwT', overwrite_apply_out T _ d w hwT', hx',
        overwrite_apply_out Rf x y0 w hw']

end Ref

end

end SparseHamiltonian.GeneralSparseAccess
