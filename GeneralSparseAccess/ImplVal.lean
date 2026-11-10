import GeneralSparseAccess.Implement

/-!
# The padded value oracle from the supplied one

The implementation `implVal` of the padded value oracle (two calls of the supplied value oracle,
the comparisons of the two index words with `N`, the validity flag and the controlled copy of the
stored word or of the public zero word) and its action on clean ancillas (`implVal_clean`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (put put_apply overwrite_apply_ι overwrite_apply_out adjIf
  localOp_localOp localOp_localOp')
open SparseHamiltonian.GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open QData (lowE mw₁ mw₂ evalid maskE maskF lowE_injective lowE_ne_mw₁ lowE_ne_mw₂ mw₁_ne_mw₂)
open scoped InnerProduct
open IW

section ValueImpl

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The implementation of the padded value oracle**. -/
def implVal (N : ℕ) (z₀ : Cfg (VW b)) : List (NInstr (IW k b) (PY k b) Query) :=
  nGatesOf (vflagC N) ++ [NInstr.call Query.value false posV] ++ nGatesOf (copyC z₀) ++
    [NInstr.call Query.value false posV] ++ nGatesOf (vflagC N).reverse

/-- The configuration map of a supplied value call. -/
def valMap (x : X) : Cfg (IW k b) ≃ Cfg (IW k b) :=
  alongEquiv posV (xorEquiv (fun d => D.table x d))

theorem valMap_sc (x : X) (z : Cfg (IW k b)) (w : VW b) :
    valMap D x z (sc w) = (z (sc w) ^^ D.table x (fun a => z (tl a)) w) := by
  change alongEquiv posV _ z (posV (Sum.inr w)) = _
  rw [alongEquiv_apply_in]
  rfl

theorem valMap_out (x : X) (z : Cfg (IW k b)) (u : IW k b) (hu : ∀ w, sc w ≠ u) :
    valMap D x z u = z u := by
  by_cases ht : ∃ a, tl a = u
  · obtain ⟨a, rfl⟩ := ht
    change alongEquiv posV _ z (posV (Sum.inl a)) = _
    rw [alongEquiv_apply_in]
    rfl
  · apply alongEquiv_apply_out
    rintro (a | w) h
    · exact ht ⟨a, h⟩
    · exact hu w h

theorem nrun_valCall (x : X) (z : Cfg (IW k b)) (q : R) :
    nrun (D.prims (R := R) x) [NInstr.call Query.value false posV] (bas z q) =
      bas (valMap D x z) q := by
  rw [nrun_singleton, NInstr.eval_call]
  change localOp posV posV.injective (fun _ => D.prims x Query.value) (bas z q) = _
  rw [D.prims_val, localOp_permOp, permOp_bas]
  rfl

theorem classical_copyC (z₀ : Cfg (VW b)) : Classical (copyC (k := k) z₀) := by
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨w, -, hw⟩
  obtain ⟨ht, hc⟩ := copyW_target z₀ w g hw
  unfold copyW at hw
  simp only [List.mem_cons] at hw
  refine ⟨?_, fun c hcs h => ?_⟩
  · rcases hw with rfl | hw
    · rfl
    · split_ifs at hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rw [hw]
      · simp at hw
  · rw [ht] at h
    rcases hc c hcs with h' | h' <;> rw [h'] at h <;> simp [g₂, sc, v] at h

theorem classical_vflagC_rev (N : ℕ) : Classical (vflagC (k := k) (b := b) N).reverse :=
  fun g hg => classical_vflagC N g (List.mem_reverse.mp hg)

/-- **The padded value oracle on clean ancillas**: the XOR of the padded stored word. -/
theorem implVal_clean (hN : N < 2 ^ (k + 1)) (z₀ : Cfg (VW b)) (x : X) :
    nrun (D.prims (R := R) x) (implVal N z₀) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L permOp (xorEquiv (fun d => D.ptable z₀ x (phiE (Equiv.refl _) d))) := by
  apply ext_bas_clm'
  intro y q
  rw [comp_apply, comp_apply, cleanEmb_bas, permOp_bas, cleanEmb_bas]
  unfold implVal
  rw [nrun_append, nrun_append, nrun_append, nrun_append, comp_apply, comp_apply, comp_apply,
    comp_apply]
  simp only [nrun_nGatesOf]
  rw [gRun_classical_bas _ (classical_vflagC N), nrun_valCall,
    gRun_classical_bas _ (classical_copyC z₀), nrun_valCall,
    gRun_classical_bas _ (classical_vflagC_rev N)]
  congr 1
  set z : Cfg (IW k b) := Sum.elim y (fun _ => false) with hz
  set z1 := cfgRun (vflagC N) z with hz1
  obtain ⟨hg2, hout⟩ := cfgRun_vflagC (k := k) (b := b) hN z (fun j => rfl) (fun j => rfl) rfl rfl
  rw [← hz1] at hg2 hout
  set vp := vpair N z with hvp
  set tb := D.table x (fun a => z (tl a)) with htb
  set z2 := valMap D x z1 with hz2
  set z3 := cfgRun (copyC z₀) z2 with hz3
  set z4 := valMap D x z3 with hz4
  set newV : Cfg (VW b) := fun w => y (Sum.inr w) ^^ (if vp then tb w else z₀ w) with hnewV
  have hz1tl : (fun a => z1 (tl a)) = fun a => z (tl a) := funext fun a =>
    hout _ (fun j => by simp [bA, tl, e]) (fun j => by simp [bB, tl, e]) (by simp [g₁, tl, e])
      (by simp [g₂, tl, e])
  have hz1sc : ∀ w, z1 (sc w) = false := fun w => by
    rw [hout _ (fun j => by simp [bA, sc]) (fun j => by simp [bB, sc]) (by simp [g₁, sc])
      (by simp [g₂, sc])]
    rfl
  have hz1v : ∀ w, z1 (v w) = y (Sum.inr w) := fun w => by
    rw [hout _ (fun j => by simp [bA, v]) (fun j => by simp [bB, v]) (by simp [g₁, v])
      (by simp [g₂, v])]
    rfl
  have hL := cfgRun_copyList (k := k) z₀ ((Finset.univ : Finset (VW b)).toList)
    (Finset.nodup_toList _) z2
  have hz4eq : z4 = overwrite v z1 newV := by
    funext u
    by_cases hv : ∃ w, v w = u
    · obtain ⟨w, rfl⟩ := hv
      rw [overwrite_apply_ι v_injective, hz4, valMap_out D x z3 _ (fun w' => sc_ne_v w' w), hz3,
        copyC, hL.1 w (Finset.mem_toList.mpr (Finset.mem_univ w))]
      rw [hz2, valMap_out D x z1 _ (fun w' => sc_ne_v w' w), hz1v]
      unfold copyBit
      rw [valMap_out D x z1 _ (fun w' => by simp [g₂, sc]), hg2, valMap_sc, hz1sc, hz1tl]
      simp only [hnewV]
      by_cases hvp' : vp = true
      · rw [if_pos hvp', hvp']
        simp [htb]
      · rw [Bool.not_eq_true] at hvp'
        rw [if_neg (by rw [hvp']; simp), hvp']
        simp
    · have hv' : ∀ w, v w ≠ u := fun w h => hv ⟨w, h⟩
      rw [overwrite_apply_out v z1 newV u hv']
      by_cases hs : ∃ w, sc w = u
      · obtain ⟨w, rfl⟩ := hs
        rw [hz4, valMap_sc, hz3, copyC, hL.2 _ (fun w' _ => sc_ne_v w w'), hz2, valMap_sc, hz1sc]
        have h3 : (fun a => cfgRun (List.flatMap (copyW z₀) (Finset.univ : Finset (VW b)).toList)
            (valMap D x z1) (tl a)) = fun a => z1 (tl a) := funext fun a => by
          rw [hL.2 _ (fun w' _ => by simp [tl, e, v]), hz2, valMap_out D x z1 _ (fun w' => by
            simp [tl, e, sc])]
        rw [h3, Bool.false_xor, Bool.xor_self]
      · have hs' : ∀ w, sc w ≠ u := fun w h => hs ⟨w, h⟩
        rw [hz4, valMap_out D x z3 u hs', hz3, copyC,
          hL.2 u (fun w _ h => hv' w h.symm), hz2, valMap_out D x z1 u hs']
  rw [hz4eq, cfgRun_overwrite_comm _ v_injective (fun g hg => vflagC_avoids_v N g
      (List.mem_reverse.mp hg)), hz1, cfgRun_reverse_cancel _ (classical_vflagC N)]
  -- the final configuration
  funext u
  rcases u with (w | w) | a
  · rw [overwrite_apply_out v z newV _ (fun w' h => by simp [v] at h)]
    rfl
  · change overwrite v z newV (v w) = _
    rw [overwrite_apply_ι v_injective]
    change _ = (y (Sum.inr w) ^^
      D.ptable z₀ x (phiE (Equiv.refl _) (fun e' => y (Sum.inl e'))) w)
    simp only [hnewV]
    congr 1
    have hph : phiE (Equiv.refl _) (fun e' => y (Sum.inl e')) =
        ((fun j => y (Sum.inl (Sum.inl j)) : Cfg (Fin (k + 1))),
          (fun j => y (Sum.inl (Sum.inr j)) : Cfg (Fin (k + 1)))) := rfl
    rw [hph]
    unfold QData.ptable
    have hvp2 : vp = decide (PValid N (fun j => y (Sum.inl (Sum.inl j))) ∧
        PValid N (fun j => y (Sum.inl (Sum.inr j)))) := by
      have hm1 : z (e (mw₁ k)) = mark (fun j => y (Sum.inl (Sum.inl j))) := rfl
      have hm2 : z (e (mw₂ k)) = mark (fun j => y (Sum.inl (Sum.inr j))) := rfl
      have hl1 : (fun i => z (xA i)) = lo (fun j => y (Sum.inl (Sum.inl j))) := rfl
      have hl2 : (fun i => z (xB i)) = lo (fun j => y (Sum.inl (Sum.inr j))) := rfl
      rw [hvp]
      unfold vpair
      rw [hm1, hm2, hl1, hl2]
      unfold PValid
      rcases Bool.eq_false_or_eq_true (mark (fun j => y (Sum.inl (Sum.inl j)))) with a | a <;>
        rcases Bool.eq_false_or_eq_true (mark (fun j => y (Sum.inl (Sum.inr j)))) with c | c <;>
        simp [a, c]
    have htb2 : tb = D.table x (edgeW k (lo (fun j => y (Sum.inl (Sum.inl j))))
        (lo (fun j => y (Sum.inl (Sum.inr j))))) := by
      rw [htb]
      congr 1
      funext a
      rcases a with j | j <;> rfl
    rw [hvp2, htb2]
    by_cases hP : PValid N (fun j => y (Sum.inl (Sum.inl j))) ∧
        PValid N (fun j => y (Sum.inl (Sum.inr j)))
    · rw [if_pos (decide_eq_true hP), if_pos hP]
    · rw [if_neg (fun h => hP (of_decide_eq_true h)), if_neg hP]
  · rw [overwrite_apply_out v z newV _ (fun w' h => by simp [v] at h)]
    rfl

end ValueImpl

end

end SparseHamiltonian.GeneralSparseAccess
