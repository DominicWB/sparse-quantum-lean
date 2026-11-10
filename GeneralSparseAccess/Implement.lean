import GeneralSparseAccess.PaddedData
import GeneralSparseAccess.CtrlRef
import GeneralSparseAccess.Subst

/-!
# The circuits implementing the padded oracles

The wires of an implementation (`IW k b`): the padded register `PY (k + 1) b` and the clean
ancillas `AW k b` (two borrow chains, two flags, the dummy and the reference of a controlled call,
and a scratch value register), with the positions of the supplied calls (`posT`, `posR`, `posV`).
The building blocks of `implP` (module `ImplOK`):

* the mask (`maskC`: two comparisons with `N` and `s`, the flip of the position marker unless the
  first index and the position are valid, and the uncomputation): on clean ancillas the
  permutation `maskY` of the padded register (`gRun_maskC_cleanEmb`);
* the controlled supplied locator with a reference (`ctrlRef`, three calls) after the mask: on
  clean ancillas the supplied locator on the low wires when the marker of the position is clear,
  after the mask (`maskCtrl_clean`);
* the exchange of the two index registers (`swapRegs`, three controlled NOT gates per bit:
  `gRun_swapRegs_cleanEmb`);
* the circuits of the value oracle: the validity flag of the pair (`vflagC`: two comparisons with
  `N`, `cfgRun_vflagC`) and the controlled copy of the scratch word or of the public zero word
  `z₀` (`copyC`, `cfgRun_copyList`).
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

/-! ### The wires -/

/-- The ancillas of the padded oracles: two borrow chains, two flags, the dummy and the reference
of the controlled call, and a scratch value register. -/
abbrev AW (k b : ℕ) := ((Fin (k + 2) ⊕ Fin (k + 2)) ⊕ (Unit ⊕ Unit)) ⊕ ((EW k ⊕ EW k) ⊕ VW b)

/-- The wires of an implementation: the padded register and the ancillas. -/
abbrev IW (k b : ℕ) := PY (k + 1) b ⊕ AW k b

namespace IW

variable {k b : ℕ}

/-- An edge wire of the padded register. -/
def e (w : EW (k + 1)) : IW k b := Sum.inl (Sum.inl w)
/-- A value wire of the padded register. -/
def v (w : VW b) : IW k b := Sum.inl (Sum.inr w)
/-- The first borrow chain. -/
def bA (j : Fin (k + 2)) : IW k b := Sum.inr (Sum.inl (Sum.inl (Sum.inl j)))
/-- The second borrow chain. -/
def bB (j : Fin (k + 2)) : IW k b := Sum.inr (Sum.inl (Sum.inl (Sum.inr j)))
/-- The first flag. -/
def g₁ : IW k b := Sum.inr (Sum.inl (Sum.inr (Sum.inl ())))
/-- The validity flag. -/
def g₂ : IW k b := Sum.inr (Sum.inl (Sum.inr (Sum.inr ())))
/-- The dummy register of the controlled call. -/
def dm (w : EW k) : IW k b := Sum.inr (Sum.inr (Sum.inl (Sum.inl w)))
/-- The reference register of the controlled call. -/
def rf (w : EW k) : IW k b := Sum.inr (Sum.inr (Sum.inl (Sum.inr w)))
/-- The scratch value register. -/
def sc (w : VW b) : IW k b := Sum.inr (Sum.inr (Sum.inr w))

/-- The low wires of the edge register (the target of the supplied locators). -/
def tl (w : EW k) : IW k b := e (lowE k w)

/-- The low word of the first index. -/
def xA (j : Fin k) : IW k b := tl (Sum.inl j)

/-- The low word of the second index. -/
def xB (j : Fin k) : IW k b := tl (Sum.inr j)

/-- The top borrow wire of the first chain. -/
abbrev topA : IW k b := bA ⟨k + 1, by omega⟩

/-- The top borrow wire of the second chain. -/
abbrev topB : IW k b := bB ⟨k + 1, by omega⟩

theorem e_injective : Function.Injective (e (k := k) (b := b)) := fun _ _ h => by
  simpa [e] using h

theorem tl_injective : Function.Injective (tl (k := k) (b := b)) :=
  e_injective.comp (lowE_injective k)

theorem rf_injective : Function.Injective (rf (k := k) (b := b)) := fun _ _ h => by
  simpa [rf] using h

theorem dm_injective : Function.Injective (dm (k := k) (b := b)) := fun _ _ h => by
  simpa [dm] using h

theorem bA_injective : Function.Injective (bA (k := k) (b := b)) := fun _ _ h => by
  simpa [bA] using h

theorem bB_injective : Function.Injective (bB (k := k) (b := b)) := fun _ _ h => by
  simpa [bB] using h

theorem sc_injective : Function.Injective (sc (k := k) (b := b)) := fun _ _ h => by
  simpa [sc] using h

theorem v_injective : Function.Injective (v (k := k) (b := b)) := fun _ _ h => by
  simpa [v] using h

/-- The layout of the first comparison. -/
theorem layoutA : CmpLayout (xA (k := k) (b := b)) bA :=
  ⟨fun i j h => by simpa [xA, tl, e, lowE] using h, bA_injective,
    fun i j h => by simp [xA, tl, e, bA] at h⟩

/-- The layout of the second comparison. -/
theorem layoutB : CmpLayout (xB (k := k) (b := b)) bB :=
  ⟨fun i j h => by simpa [xB, tl, e, lowE] using h, bB_injective,
    fun i j h => by simp [xB, tl, e, bB] at h⟩

/-- The layout of the controlled call. -/
theorem refLayout : RefLayout (e (k := k) (b := b) (mw₂ k)) tl dm rf where
  inj_T := tl_injective
  inj_Dm := dm_injective
  inj_Rf := rf_injective
  T_ne_Dm := fun _ _ h => by simp [tl, e, dm] at h
  T_ne_Rf := fun _ _ h => by simp [tl, e, rf] at h
  Dm_ne_Rf := fun _ _ h => by simp [dm, rf] at h
  T_ne_c := fun w h => lowE_ne_mw₂ k w (by simpa [tl, e] using h)
  Dm_ne_c := fun _ h => by simp [dm, e] at h
  Rf_ne_c := fun _ h => by simp [rf, e] at h

end IW

open IW

/-! ### Positions of the supplied calls -/

section Pos

variable {k b : ℕ}

/-- A supplied call on the low wires of the edge register and the value wires. -/
def posT : PY k b ↪ IW k b :=
  ⟨Sum.elim tl v, tl_injective.sumElim v_injective (fun _ _ h => by simp [tl, e, v] at h)⟩

/-- A supplied call on the reference register and the value wires. -/
def posR : PY k b ↪ IW k b :=
  ⟨Sum.elim rf v, rf_injective.sumElim v_injective (fun _ _ h => by simp [rf, v] at h)⟩

/-- A supplied value call on the low wires of the edge register and the scratch register. -/
def posV : PY k b ↪ IW k b :=
  ⟨Sum.elim tl sc, tl_injective.sumElim sc_injective (fun _ _ h => by simp [tl, e, sc] at h)⟩

end Pos

/-! ### The mask -/

section Mask

variable {k b : ℕ}

/-- **The mask circuit**: compare the low words with `N` and `s`, flip the marker of the position
unless the first index and the position are valid, and uncompute the comparisons. -/
def maskC (N s : ℕ) : List (Gate (IW k b)) :=
  ltChain N xA bA ++ ltChain s xB bB ++
    [⟨[], e (mw₂ k), pauliX⟩, ⟨[(e (mw₁ k), false), (topA, true), (topB, true)], e (mw₂ k), pauliX⟩] ++
    (ltChain s xB bB).reverse ++ (ltChain N xA bA).reverse

/-- A borrow chain on the word `xw` and the borrow wires `bw` does not read or write a wire outside
them. -/
theorem ltChain_avoids {r : ℕ} {W : Type*} [DecidableEq W] (c : ℕ) {xw : Fin r → W}
    {bw : Fin (r + 2) → W} (w : W) (hx : ∀ i, xw i ≠ w)
    (hb : ∀ j, bw j ≠ w) : ∀ g ∈ ltChain c xw bw, g.t ≠ w ∧ ∀ cc ∈ g.cs, cc.1 ≠ w := by
  intro g hg
  obtain ⟨j, -, hj⟩ := target_chainUpTo c xw bw (r + 1) g hg
  refine ⟨by rw [hj]; exact hb j, ?_⟩
  intro cc hcc
  exact ctrl_chainUpTo c xw bw (r + 1) g hg cc hcc w hx hb

theorem ltChain_reverse_avoids {r : ℕ} {W : Type*} [DecidableEq W] (c : ℕ) {xw : Fin r → W}
    {bw : Fin (r + 2) → W} (w : W) (hx : ∀ i, xw i ≠ w)
    (hb : ∀ j, bw j ≠ w) : ∀ g ∈ (ltChain c xw bw).reverse, g.t ≠ w ∧ ∀ cc ∈ g.cs, cc.1 ≠ w :=
  fun g hg => ltChain_avoids c w hx hb g (List.mem_reverse.mp hg)

theorem e_ne_xA (w : EW (k + 1)) (hw : ∀ a, lowE k a ≠ w) (i : Fin k) :
    xA (b := b) i ≠ e w := fun h => hw _ (by simpa [xA, tl, e] using h)

theorem e_ne_xB (w : EW (k + 1)) (hw : ∀ a, lowE k a ≠ w) (i : Fin k) :
    xB (b := b) i ≠ e w := fun h => hw _ (by simpa [xB, tl, e] using h)

@[simp] theorem bA_ne_e (j : Fin (k + 2)) (w : EW (k + 1)) : bA (b := b) j ≠ e w := by
  simp [bA, e]
@[simp] theorem bB_ne_e (j : Fin (k + 2)) (w : EW (k + 1)) : bB (b := b) j ≠ e w := by
  simp [bB, e]
@[simp] theorem bA_ne_bB (j j' : Fin (k + 2)) : bA (b := b) j ≠ bB j' := by simp [bA, bB]
@[simp] theorem bB_ne_bA (j j' : Fin (k + 2)) : bB (b := b) j ≠ bA j' := by simp [bA, bB]
@[simp] theorem xA_ne_bB (i : Fin k) (j : Fin (k + 2)) : xA (b := b) i ≠ bB j := by
  simp [xA, tl, e, bB]
@[simp] theorem xB_ne_bA (i : Fin k) (j : Fin (k + 2)) : xB (b := b) i ≠ bA j := by
  simp [xB, tl, e, bA]

/-- **The mask circuit on clean borrow chains** flips the marker of the position unless the
first index and the position are valid (`maskF`). -/
theorem cfgRun_maskC {N s : ℕ} (hN : N < 2 ^ (k + 1)) (hs : s < 2 ^ (k + 1)) (z : Cfg (IW k b))
    (hA : ∀ j, z (bA j) = false) (hB : ∀ j, z (bB j) = false) :
    cfgRun (maskC N s) z = Function.update z (e (mw₂ k))
      (z (e (mw₂ k)) ^^ !evalid N s (fun w => z (e w))) := by
  set q : IW k b := e (mw₂ k) with hq
  have hqA : ∀ i, xA (b := b) i ≠ q := e_ne_xA (mw₂ k) (lowE_ne_mw₂ k)
  have hqB : ∀ i, xB (b := b) i ≠ q := e_ne_xB (mw₂ k) (lowE_ne_mw₂ k)
  have hbAq : ∀ j, bA (b := b) j ≠ q := fun j => bA_ne_e j _
  have hbBq : ∀ j, bB (b := b) j ≠ q := fun j => bB_ne_e j _
  set z1 := cfgRun (ltChain N xA bA) z with hz1
  set z2 := cfgRun (ltChain s xB bB) z1 with hz2
  have h1A : z1 topA = decide (wordValue (fun i => z (xA i)) < N) :=
    cfgRun_ltChain_top N layoutA hN z hA
  have h1B : ∀ j, z1 (bB j) = false := fun j => by
    rw [hz1, cfgRun_ltChain_out N xA bA z _ (fun j' => bA_ne_bB j' j)]
    exact hB j
  have h1x : (fun i => z1 (xB i)) = fun i => z (xB i) := funext fun i => by
    rw [hz1, cfgRun_ltChain_out N xA bA z _ (fun j' => (xB_ne_bA i j').symm)]
  have h2B : z2 topB = decide (wordValue (fun i => z (xB i)) < s) := by
    rw [hz2, cfgRun_ltChain_top s layoutB hs z1 h1B, h1x]
  have h2A : z2 topA = z1 topA := by
    rw [hz2, cfgRun_ltChain_out s xB bB z1 _ (fun j => bB_ne_bA j _)]
  have h2m : z2 (e (mw₁ k)) = z (e (mw₁ k)) := by
    rw [hz2, cfgRun_ltChain_out s xB bB z1 _ (fun j => bB_ne_e j _), hz1,
      cfgRun_ltChain_out N xA bA z _ (fun j => bA_ne_e j _)]
  have h2q : z2 q = z q := by
    rw [hz2, cfgRun_ltChain_out s xB bB z1 _ hbBq, hz1, cfgRun_ltChain_out N xA bA z _ hbAq]
  have hmq : e (b := b) (mw₁ k) ≠ q := fun h => mw₁_ne_mw₂ k (e_injective h)
  have htAq : topA (k := k) (b := b) ≠ q := hbAq _
  have htBq : topB (k := k) (b := b) ≠ q := hbBq _
  -- the middle gates
  have hmid : cfgRun [⟨[], q, pauliX⟩,
      ⟨[(e (mw₁ k), false), (topA, true), (topB, true)], q, pauliX⟩] z2 =
      Function.update z2 q (z q ^^ !evalid N s (fun w => z (e w))) := by
    simp only [cfgRun]
    unfold flipCfg
    simp only [ctrlOK_nil, if_true, ctrlOK_cons, ctrlOK_nil]
    rw [Function.update_of_ne hmq, Function.update_of_ne htAq, Function.update_of_ne htBq,
      h2m, h2A, h1A, h2B, h2q]
    unfold evalid
    have ex1 : (fun j => z (e (lowE k (Sum.inl j)))) = fun i => z (xA i) := rfl
    have ex2 : (fun j => z (e (lowE k (Sum.inr j)))) = fun i => z (xB i) := rfl
    rw [ex1, ex2]
    rcases Bool.eq_false_or_eq_true (z (e (mw₁ k))) with hm | hm <;>
      rcases Bool.eq_false_or_eq_true (decide (wordValue (fun i => z (xA i)) < N)) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (decide (wordValue (fun i => z (xB i)) < s)) with hb' | hb' <;>
      rcases Bool.eq_false_or_eq_true (z q) with hz | hz <;>
      simp [hm, ha, hb', hz, Function.update_idem]
  unfold maskC
  rw [cfgRun_append, cfgRun_append, cfgRun_append, cfgRun_append, ← hz1, ← hz2, hmid,
    cfgRun_update _ q (ltChain_reverse_avoids s q hqB hbBq),
    cfgRun_reverse_cancel _ (classical_ltChain s layoutB),
    cfgRun_update _ q (ltChain_reverse_avoids N q hqA hbAq),
    cfgRun_reverse_cancel _ (classical_ltChain N layoutA)]

theorem classical_maskC (N s : ℕ) : Classical (maskC (k := k) (b := b) N s) := by
  have hq1 : e (b := b) (mw₁ k) ≠ e (mw₂ k) := fun h => mw₁_ne_mw₂ k (e_injective h)
  have hqA : topA (k := k) (b := b) ≠ e (mw₂ k) := bA_ne_e _ _
  have hqB : topB (k := k) (b := b) ≠ e (mw₂ k) := bB_ne_e _ _
  unfold maskC
  refine classical_append (classical_append (classical_append (classical_append
    (classical_ltChain N layoutA) (classical_ltChain s layoutB)) ?_) ?_) ?_
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨rfl, by simp⟩
    · refine ⟨rfl, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl)
      · exact hq1
      · exact hqA
      · exact hqB
  · exact fun g hg => classical_ltChain s layoutB g (List.mem_reverse.mp hg)
  · exact fun g hg => classical_ltChain N layoutA g (List.mem_reverse.mp hg)

theorem gateOK_maskC (N s : ℕ) : ∀ g ∈ maskC (k := k) (b := b) N s, GateOK 3 g := by
  intro g hg
  have hc := classical_maskC (k := k) (b := b) N s g hg
  refine ⟨?_, hc.2, by rw [hc.1]; exact pauliX_unitary⟩
  unfold maskC at hg
  simp only [List.mem_append, List.mem_reverse] at hg
  rcases hg with (((h | h) | h) | h) | h
  · exact (gateOK_ltChain N layoutA g h).1
  · exact (gateOK_ltChain s layoutB g h).1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp
  · exact (gateOK_ltChain s layoutB g h).1
  · exact (gateOK_ltChain N layoutA g h).1

theorem length_maskC_le (N s : ℕ) : (maskC (k := k) (b := b) N s).length ≤ 8 * (k + 1) + 2 := by
  unfold maskC
  simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil]
  have h1 := length_ltChain_le N (xA (k := k) (b := b)) bA
  have h2 := length_ltChain_le s (xB (k := k) (b := b)) bB
  omega

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The mask on the edge register of the padded register. -/
def maskY (N s : ℕ) : Cfg (PY (k + 1) b) ≃ Cfg (PY (k + 1) b) :=
  alongEquiv ⟨Sum.inl, Sum.inl_injective⟩ (maskE N s)

theorem maskY_apply (N s : ℕ) (y : Cfg (PY (k + 1) b)) :
    maskY N s y = Sum.elim (maskF N s (fun w => y (Sum.inl w))) (fun w => y (Sum.inr w)) := by
  funext w
  rcases w with w | w
  · exact alongEquiv_apply_in ⟨Sum.inl, Sum.inl_injective⟩ (maskE N s) y w
  · exact alongEquiv_apply_out ⟨Sum.inl, Sum.inl_injective⟩ (maskE N s) y (Sum.inr w)
      (fun a h => by cases h)

/-- **The mask circuit on clean ancillas** is the permutation `maskY` of the padded register. -/
theorem gRun_maskC_cleanEmb {N s : ℕ} (hN : N < 2 ^ (k + 1)) (hs : s < 2 ^ (k + 1)) :
    gRun (Q := R) (maskC (k := k) (b := b) N s) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L permOp (maskY N s) := by
  apply ext_bas_clm'
  intro y q
  rw [comp_apply, comp_apply, cleanEmb_bas, gRun_classical_bas _ (classical_maskC N s),
    permOp_bas, cleanEmb_bas]
  congr 1
  rw [cfgRun_maskC hN hs _ (fun j => rfl) (fun j => rfl), maskY_apply]
  funext w
  rcases w with (w | w) | w
  · by_cases hw : w = mw₂ k
    · subst hw
      rw [show (Sum.inl (Sum.inl (mw₂ k)) : IW k b) = e (mw₂ k) from rfl, Function.update_self]
      change _ = maskF N s (fun w => y (Sum.inl w)) (mw₂ k)
      unfold maskF
      rw [Function.update_self]
      rfl
    · have hne : (Sum.inl (Sum.inl w) : IW k b) ≠ e (mw₂ k) := fun h => hw (by
        simpa [e] using h)
      rw [Function.update_of_ne hne]
      change y (Sum.inl w) = maskF N s (fun w => y (Sum.inl w)) w
      unfold maskF
      rw [Function.update_of_ne hw]
  · have hne : (Sum.inl (Sum.inr w) : IW k b) ≠ e (mw₂ k) := fun h => by simp [e] at h
    rw [Function.update_of_ne hne]
    rfl
  · have hne : (Sum.inr w : IW k b) ≠ e (mw₂ k) := fun h => by simp [e] at h
    rw [Function.update_of_ne hne]
    rfl

end Mask

/-! ### Supplied calls -/

section Calls

variable {k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- A supplied operation on the edge register, called on the wires `pos`, acts on the wires
`pos ∘ inl`. -/
theorem localOp_pos_inl (pos : PY k b ↪ IW k b) (T : EW k → IW k b) (hT : Function.Injective T)
    (hTp : ∀ w, T w = pos (Sum.inl w)) (G : Reg (EW k) R →L[ℂ] Reg (EW k) R) :
    localOp pos pos.injective (fun _ => localOp (Sum.inl : EW k → PY k b) Sum.inl_injective
      (fun _ => G)) = localOp T hT (fun _ => G) :=
  localOp_localOp' pos.injective Sum.inl_injective T hT hTp (fun _ _ => G)

theorem binW_zero : binW k 0 = fun _ => false := by
  funext j
  simp [binW]

theorem edgeW_binW_zero : edgeW k (binW k 0) (binW k 0) = fun _ => false := by
  funext w
  rcases w with j | j <;> simp [edgeW, binW]

omit [CompleteSpace R] in
/-- Supported on clean ancillas, hence on a clean dummy and reference. -/
theorem supp_cleanEmb_ref (ψ : Reg (PY (k + 1) b) R) :
    Supp (fun x : Cfg (IW k b) => (∀ w, x (dm w) = false) ∧ ∀ w, x (rf w) = false)
      (cleanEmb (X := AW k b) ψ) := by
  intro y hy
  rw [cleanEmb_apply, if_neg]
  intro h
  apply hy
  exact ⟨fun w => congrFun h _, fun w => congrFun h _⟩

end Calls

/-! ### The padded locators -/

section Loc

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The reference of a supplied locator: the image of the all-zero edge. -/
def refW (loc : Fin N → Fin s → Fin N) (hN : 0 < N) (hs : 0 < s) : Cfg (EW k) :=
  edgeW k (binW k 0) (binW k (loc ⟨0, hN⟩ ⟨0, hs⟩))

/-- A supplied locator maps the all-zero edge to its reference. -/
theorem qlift_zero (F : EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k)))
    (loc : Fin N → Fin s → Fin N) (hN : 0 < N) (hs : 0 < s)
    (hF : F (EuclideanSpace.single (edgeW k (binW k 0) (binW k 0)) 1) =
      EuclideanSpace.single (refW loc hN hs) 1) (q : R) :
    qlift (Equiv.refl _) F (bas (fun _ => false) q) = bas (refW loc hN hs) q := by
  apply qlift_bas_single (Equiv.refl _) F (fun _ => false) (refW loc hN hs)
  change F (EuclideanSpace.single (fun _ => false) 1) = _
  rw [← edgeW_binW_zero]
  exact hF

/-- **The controlled supplied locator** on the padded register: the supplied locator on the low
wires when the marker of the position is clear. -/
def ctlE (G : Reg (EW k) R →L[ℂ] Reg (EW k) R) : Reg (EW (k + 1)) R →L[ℂ] Reg (EW (k + 1)) R :=
  localOp (lowE k) (lowE_injective k) (fun z => if z (mw₂ k) then 1 else G)

/-- The controlled call of the gadget, on the wires of an implementation, is the controlled
locator on the padded register. -/
theorem gadgetCtl_eq (G : Reg (EW k) R →L[ℂ] Reg (EW k) R) :
    localOp tl tl_injective (fun x : Cfg (IW k b) => if x (e (mw₂ k)) = false then G else 1) =
      liftB (X := AW k b) (localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
        (fun _ => ctlE G)) := by
  unfold liftB ctlE
  rw [localOp_localOp Sum.inl_injective (lowE_injective k)
      (fun _ z => if z (mw₂ k) then 1 else G),
    localOp_localOp' Sum.inl_injective (Sum.inl_injective.comp (lowE_injective k)) tl
      tl_injective (fun _ => rfl)]
  apply localOp_congr
  intro z
  have hz : clearCfg (lowE k) (fun a => clearCfg (Sum.inl ∘ lowE k)
      (fun a => clearCfg tl z (Sum.inl a)) (Sum.inl a)) (mw₂ k) = z (e (mw₂ k)) := by
    change overwrite (lowE k) _ (fun _ => false) (mw₂ k) = _
    rw [overwrite_apply_out _ _ _ _ (lowE_ne_mw₂ k)]
    change overwrite (Sum.inl ∘ lowE k) _ (fun _ => false) (Sum.inl (mw₂ k)) = _
    rw [overwrite_apply_out (Sum.inl ∘ lowE k) _ _ _
      (fun a h => lowE_ne_mw₂ k a (Sum.inl_injective h))]
    change overwrite tl z (fun _ => false) (e (mw₂ k)) = _
    exact overwrite_apply_out _ _ _ _ (fun a h => lowE_ne_mw₂ k a (by simpa [tl, e] using h))
  have hz' : clearCfg tl z (e (mw₂ k)) = z (e (mw₂ k)) := by
    change overwrite tl z (fun _ => false) (e (mw₂ k)) = _
    exact overwrite_apply_out _ _ _ _ (fun a h => lowE_ne_mw₂ k a (by simpa [tl, e] using h))
  rw [hz', hz]
  cases z (e (mw₂ k)) <;> rfl

/-- **A padded locator from a controlled supplied locator.** For a supplied locator `F` with the
reference `refW`, the mask and the controlled call with a reference act on clean ancillas as the
controlled locator after the mask. -/
theorem maskCtrl_clean (F : EuclideanSpace ℂ (Cfg (EW k)) →L[ℂ] EuclideanSpace ℂ (Cfg (EW k)))
    (hFu : IsUnitary F) (loc : Fin N → Fin s → Fin N) (hN0 : 0 < N) (hs0 : 0 < s)
    (hF0 : F (EuclideanSpace.single (edgeW k (binW k 0) (binW k 0)) 1) =
      EuclideanSpace.single (refW loc hN0 hs0) 1)
    (hN : N < 2 ^ (k + 1)) (hs : s < 2 ^ (k + 1)) (prim : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R)
    (j : Query) (hj : prim j = localOp Sum.inl Sum.inl_injective (fun _ => qlift (Equiv.refl _) F)) :
    nrun prim (nGatesOf (maskC N s) ++ ctrlRef (e (mw₂ k)) false tl dm rf
        [NInstr.call j false posT] [NInstr.call j false posR] [NInstr.call j true posR]) ∘L
        cleanEmb (X := AW k b) =
      cleanEmb ∘L (localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
        (fun _ => ctlE (qlift (R := R) (Equiv.refl _) F)) ∘L permOp (maskY N s)) := by
  set G := qlift (R := R) (Equiv.refl (Cfg (EW k))) F with hG
  have hGu : IsUnitary G := qlift_isUnitary _ hFu
  have hcT : nrun prim [NInstr.call j false posT] = localOp tl tl_injective (fun _ => G) := by
    rw [nrun_singleton, NInstr.eval_call]
    change localOp posT posT.injective (fun _ => prim j) = _
    rw [hj]
    exact localOp_pos_inl posT tl tl_injective (fun _ => rfl) G
  have hcR : nrun prim [NInstr.call j false posR] = localOp rf rf_injective (fun _ => G) := by
    rw [nrun_singleton, NInstr.eval_call]
    change localOp posR posR.injective (fun _ => prim j) = _
    rw [hj]
    exact localOp_pos_inl posR rf rf_injective (fun _ => rfl) G
  have hcR' : nrun prim [NInstr.call j true posR] = localOp rf rf_injective (fun _ => G†) := by
    rw [nrun_singleton, NInstr.eval_call]
    change localOp posR posR.injective (fun _ => (prim j)†) = _
    rw [hj, localOp_adjoint]
    exact localOp_pos_inl posR rf rf_injective (fun _ => rfl) (G†)
  have hA := ctrlRef_agrees prim G hGu (refW loc hN0 hs0) (qlift_zero F loc hN0 hs0 hF0) false
    refLayout _ _ _ hcT hcR hcR'
  rw [nrun_append, nrun_nGatesOf, comp_assoc, gRun_maskC_cleanEmb hN hs, ← comp_assoc]
  have hB : nrun prim (ctrlRef (e (mw₂ k)) false tl dm rf [NInstr.call j false posT]
      [NInstr.call j false posR] [NInstr.call j true posR]) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L localOp (Sum.inl : EW (k + 1) → PY (k + 1) b) Sum.inl_injective
        (fun _ => ctlE G) := by
    apply ContinuousLinearMap.ext
    intro ψ
    rw [comp_apply, hA _ (supp_cleanEmb_ref ψ), gadgetCtl_eq, ← comp_apply (liftB _),
      liftB_cleanEmb, comp_apply]
  rw [hB, comp_assoc]

end Loc

/-! ### The exchange of the two index registers -/

section Swap

variable {W : Type*} [DecidableEq W]

/-- Three controlled NOT gates exchanging the wires `a` and `b`. -/
def swap3 (a b : W) : List (Gate W) :=
  [⟨[(a, true)], b, pauliX⟩, ⟨[(b, true)], a, pauliX⟩, ⟨[(a, true)], b, pauliX⟩]

theorem cfgRun_swap3 {a b : W} (hab : a ≠ b) (z : Cfg W) :
    cfgRun (swap3 a b) z = fun w => if w = a then z b else if w = b then z a else z w := by
  funext w
  simp only [swap3, cfgRun]
  unfold flipCfg
  simp only [ctrlOK_cons, ctrlOK_nil]
  by_cases hwa : w = a
  · subst hwa
    rcases Bool.eq_false_or_eq_true (z w) with h1 | h1 <;>
      rcases Bool.eq_false_or_eq_true (z b) with h2 | h2 <;>
      simp [hab, Ne.symm hab, h1, h2]
  · by_cases hwb : w = b
    · subst hwb
      rcases Bool.eq_false_or_eq_true (z a) with h1 | h1 <;>
        rcases Bool.eq_false_or_eq_true (z w) with h2 | h2 <;>
        simp [hab, Ne.symm hab, h1, h2]
    · split_ifs <;> simp [Function.update_apply, hwa, hwb]

omit [DecidableEq W] in
theorem classical_swap3 {a b : W} (hab : a ≠ b) : Classical (swap3 a b) := by
  intro g hg
  simp only [swap3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> refine ⟨rfl, ?_⟩ <;> simp [hab, Ne.symm hab]

omit [DecidableEq W] in
theorem gateOK_swap3 {a b : W} (hab : a ≠ b) : ∀ g ∈ swap3 a b, GateOK 3 g := by
  intro g hg
  have hc := classical_swap3 hab g hg
  refine ⟨?_, hc.2, by rw [hc.1]; exact pauliX_unitary⟩
  simp only [swap3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp

end Swap

section SwapRegs

variable {k b : ℕ}

/-- The exchange of the two index registers on the wires of an implementation. -/
def swapW : IW k b → IW k b
  | Sum.inl (Sum.inl (Sum.inl j)) => Sum.inl (Sum.inl (Sum.inr j))
  | Sum.inl (Sum.inl (Sum.inr j)) => Sum.inl (Sum.inl (Sum.inl j))
  | w => w

/-- The wires of the index pairs of a list of positions. -/
def InPairs (l : List (Fin (k + 1))) (w : IW k b) : Prop :=
  ∃ j ∈ l, w = e (Sum.inl j) ∨ w = e (Sum.inr j)

instance (l : List (Fin (k + 1))) : DecidablePred (InPairs (b := b) l) := fun w => by
  unfold InPairs
  infer_instance

/-- The gates exchanging the index pairs of a list of positions. -/
def swapList (l : List (Fin (k + 1))) : List (Gate (IW k b)) :=
  l.flatMap (fun j => swap3 (e (Sum.inl j)) (e (Sum.inr j)))

/-- **The exchange of the two index registers**: three controlled NOT gates per bit. -/
def swapRegs (k b : ℕ) : List (Gate (IW k b)) := swapList (List.finRange (k + 1))

theorem e_inl_ne_e_inr (j : Fin (k + 1)) : e (b := b) (Sum.inl j) ≠ e (Sum.inr j) := by
  simp [e]

theorem swapW_inPairs {l : List (Fin (k + 1))} {w : IW k b} (h : InPairs l w) :
    InPairs l (swapW w) := by
  obtain ⟨j, hj, rfl | rfl⟩ := h
  · exact ⟨j, hj, Or.inr rfl⟩
  · exact ⟨j, hj, Or.inl rfl⟩

theorem cfgRun_swapList (l : List (Fin (k + 1))) (hl : l.Nodup) (z : Cfg (IW k b))
    (w : IW k b) :
    cfgRun (swapList l) z w = if InPairs l w then z (swapW w) else z w := by
  induction l generalizing z w with
  | nil =>
      have : ¬ InPairs ([] : List (Fin (k + 1))) w := by simp [InPairs]
      simp [swapList, cfgRun, this]
  | cons j l ih =>
      rw [List.nodup_cons] at hl
      have hrest : swapList (b := b) (j :: l) =
          swap3 (e (b := b) (Sum.inl j)) (e (Sum.inr j)) ++ swapList l := by
        simp [swapList, List.flatMap_cons]
      rw [hrest, cfgRun_append, cfgRun_swap3 (e_inl_ne_e_inr j)]
      rw [ih hl.2]
      have hnot : ∀ {j' : Fin (k + 1)}, j' ∈ l → j' ≠ j := fun h h' => hl.1 (h' ▸ h)
      by_cases hw : InPairs l w
      · have hw' : InPairs (j :: l) w := by
          obtain ⟨j', hj', h⟩ := hw
          exact ⟨j', List.mem_cons_of_mem j hj', h⟩
        have hsw := swapW_inPairs hw
        have h1 : swapW w ≠ e (b := b) (Sum.inl j) := by
          intro h
          obtain ⟨j', hj', h'⟩ := hsw
          rw [h] at h'
          rcases h' with h' | h' <;> simp [e] at h'
          exact hnot hj' h'.symm
        have h2 : swapW w ≠ e (b := b) (Sum.inr j) := by
          intro h
          obtain ⟨j', hj', h'⟩ := hsw
          rw [h] at h'
          rcases h' with h' | h' <;> simp [e] at h'
          exact hnot hj' h'.symm
        simp only [if_pos hw, if_pos hw', if_neg h1, if_neg h2]
      · simp only [if_neg hw]
        by_cases hwa : w = e (Sum.inl j)
        · have hw' : InPairs (j :: l) w := ⟨j, List.mem_cons_self, Or.inl hwa⟩
          subst hwa
          simp only [if_pos hw']
          rfl
        · by_cases hwb : w = e (Sum.inr j)
          · have hw' : InPairs (j :: l) w := ⟨j, List.mem_cons_self, Or.inr hwb⟩
            subst hwb
            simp only [if_neg hwa, if_pos hw']
            rfl
          · have hw' : ¬ InPairs (j :: l) w := by
              rintro ⟨j', hj', h'⟩
              rcases List.mem_cons.mp hj' with rfl | hj''
              · rcases h' with h' | h'
                · exact hwa h'
                · exact hwb h'
              · exact hw ⟨j', hj'', h'⟩
            simp only [if_neg hwa, if_neg hwb, if_neg hw']

/-- The exchange of the two index registers on configurations. -/
theorem cfgRun_swapRegs (z : Cfg (IW k b)) : cfgRun (swapRegs k b) z = fun w => z (swapW w) := by
  funext w
  rw [swapRegs, cfgRun_swapList _ (List.nodup_finRange _)]
  split_ifs with h
  · rfl
  · rcases w with ((j | j) | v) | a
    · exact absurd ⟨j, List.mem_finRange j, Or.inl rfl⟩ h
    · exact absurd ⟨j, List.mem_finRange j, Or.inr rfl⟩ h
    · rfl
    · rfl

theorem classical_swapList (l : List (Fin (k + 1))) : Classical (swapList (b := b) l) := by
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨j, -, hj⟩
  exact classical_swap3 (e_inl_ne_e_inr j) g hj

theorem gateOK_swapRegs : ∀ g ∈ swapRegs k b, GateOK 3 g := by
  intro g hg
  rcases List.mem_flatMap.mp hg with ⟨j, -, hj⟩
  exact gateOK_swap3 (e_inl_ne_e_inr j) g hj

theorem length_swapList (l : List (Fin (k + 1))) : (swapList (b := b) l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      have hrest : swapList (b := b) (j :: l) =
          swap3 (e (b := b) (Sum.inl j)) (e (Sum.inr j)) ++ swapList l := by
        simp [swapList, List.flatMap_cons]
      rw [hrest, List.length_append, ih, List.length_cons]
      simp [swap3]
      ring

theorem length_swapRegs : (swapRegs k b).length = 3 * (k + 1) := by
  rw [swapRegs, length_swapList, List.length_finRange]

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The exchange of the two index registers of the padded register. -/
def swapY (k b : ℕ) : Cfg (PY (k + 1) b) ≃ Cfg (PY (k + 1) b) :=
  alongEquiv ⟨Sum.inl, Sum.inl_injective⟩ (QData.swapE k)

/-- **The register exchange on clean ancillas.** -/
theorem gRun_swapRegs_cleanEmb :
    gRun (Q := R) (swapRegs k b) ∘L cleanEmb (X := AW k b) = cleanEmb ∘L permOp (swapY k b) := by
  apply ext_bas_clm'
  intro y q
  rw [comp_apply, comp_apply, cleanEmb_bas, swapRegs,
    gRun_classical_bas _ (classical_swapList (List.finRange (k + 1))), permOp_bas, cleanEmb_bas]
  congr 1
  rw [← swapRegs, cfgRun_swapRegs]
  funext w
  rcases w with ((j | j) | w) | w
  · exact (alongEquiv_apply_in ⟨Sum.inl, Sum.inl_injective⟩ (QData.swapE k) y (Sum.inl j)).symm
  · exact (alongEquiv_apply_in ⟨Sum.inl, Sum.inl_injective⟩ (QData.swapE k) y (Sum.inr j)).symm
  · exact (alongEquiv_apply_out ⟨Sum.inl, Sum.inl_injective⟩ (QData.swapE k) y (Sum.inr w)
      (fun a h => by cases h)).symm
  · rfl

end SwapRegs

/-! ### The padded value oracle -/

section Value

variable {k b : ℕ}

/-- **The validity flag**: compare both low words with `N`, then `g₂ = [valid pair]`. -/
def vflagC (N : ℕ) : List (Gate (IW k b)) :=
  ltChain N xA bA ++ ltChain N xB bB ++
    [⟨[(e (mw₁ k), false), (topA, true)], g₁, pauliX⟩,
      ⟨[(g₁, true), (e (mw₂ k), false), (topB, true)], g₂, pauliX⟩]

/-- The copy of the scratch word into the value wire `w` on a valid pair, and of the zero word
`z₀` otherwise. -/
def copyW (z₀ : Cfg (VW b)) (w : VW b) : List (Gate (IW k b)) :=
  ⟨[(g₂, true), (sc w, true)], v w, pauliX⟩ ::
    (if z₀ w then [⟨[(g₂, false)], v w, pauliX⟩] else [])

/-- The copy of the stored word into the value wires. -/
def copyC (z₀ : Cfg (VW b)) : List (Gate (IW k b)) :=
  ((Finset.univ : Finset (VW b)).toList).flatMap (copyW z₀)

@[simp] theorem g₂_ne_v (w : VW b) : g₂ (k := k) ≠ v w := by simp [g₂, v]
@[simp] theorem sc_ne_v (w w' : VW b) : sc (k := k) w ≠ v w' := by simp [sc, v]
@[simp] theorem g₁_ne_g₂ : g₁ (k := k) (b := b) ≠ g₂ := by simp [g₁, g₂]

/-- The copy bit of the value wire `w`. -/
def copyBit (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (w : VW b) : Bool :=
  (z g₂ && z (sc w)) ^^ (!z g₂ && z₀ w)

theorem flipCfg_eq_update {W : Type*} [DecidableEq W] (cs : List (W × Bool)) (t : W)
    (x : Cfg W) : flipCfg cs t x = Function.update x t (x t ^^ ctrlOK cs x) := by
  unfold flipCfg
  split_ifs with h
  · rw [h, Bool.xor_true]
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.xor_false, Function.update_eq_self]

theorem cfgRun_copyW (z₀ : Cfg (VW b)) (w : VW b) (z : Cfg (IW k b)) :
    cfgRun (copyW z₀ w) z = Function.update z (v w) (z (v w) ^^ copyBit z₀ z w) := by
  have h1 : (g₂ : IW k b) ≠ v w := g₂_ne_v w
  have h2 : (sc w : IW k b) ≠ v w := sc_ne_v w w
  unfold copyW copyBit
  by_cases hz : z₀ w = true
  · simp only [hz, if_true, cfgRun, flipCfg_eq_update, ctrlOK_cons, ctrlOK_nil,
      Function.update_self, Function.update_idem, Function.update_of_ne h1]
    congr 1
    rcases Bool.eq_false_or_eq_true (z g₂) with a | a <;>
      rcases Bool.eq_false_or_eq_true (z (sc w)) with c | c <;>
      rcases Bool.eq_false_or_eq_true (z (v w)) with d | d <;> simp [a, c, d]
  · simp only [Bool.not_eq_true] at hz
    simp only [hz, Bool.false_eq_true, if_false, cfgRun, flipCfg_eq_update, ctrlOK_cons,
      ctrlOK_nil]
    congr 1
    rcases Bool.eq_false_or_eq_true (z g₂) with a | a <;>
      rcases Bool.eq_false_or_eq_true (z (sc w)) with c | c <;> simp [a, c]

theorem copyW_target (z₀ : Cfg (VW b)) (w : VW b) :
    ∀ g ∈ copyW (k := k) z₀ w, g.t = v w ∧ ∀ c ∈ g.cs, (c.1 = g₂ ∨ c.1 = sc w) := by
  intro g hg
  unfold copyW at hg
  simp only [List.mem_cons] at hg
  rcases hg with rfl | hg
  · refine ⟨rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · split_ifs at hg
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      refine ⟨rfl, ?_⟩
      simp
    · simp at hg

/-- The copy list on the value wires of a list of distinct words. -/
theorem cfgRun_copyList (z₀ : Cfg (VW b)) (L : List (VW b)) (hL : L.Nodup) (z : Cfg (IW k b)) :
    (∀ w ∈ L, cfgRun (L.flatMap (copyW z₀)) z (v w) = (z (v w) ^^ copyBit z₀ z w)) ∧
    (∀ u, (∀ w ∈ L, u ≠ v w) → cfgRun (L.flatMap (copyW z₀)) z u = z u) := by
  induction L generalizing z with
  | nil => exact ⟨fun w hw => by simp at hw, fun u _ => rfl⟩
  | cons w0 L ih =>
      rw [List.nodup_cons] at hL
      rw [List.flatMap_cons, cfgRun_append, cfgRun_copyW]
      obtain ⟨ih1, ih2⟩ := ih hL.2 (Function.update z (v w0) (z (v w0) ^^ copyBit z₀ z w0))
      have hcb : ∀ w, copyBit z₀ (Function.update z (v w0) (z (v w0) ^^ copyBit z₀ z w0)) w =
          copyBit z₀ z w := by
        intro w
        unfold copyBit
        rw [Function.update_of_ne (g₂_ne_v w0), Function.update_of_ne (sc_ne_v w w0)]
      refine ⟨fun w hw => ?_, fun u hu => ?_⟩
      · rcases List.mem_cons.mp hw with rfl | hw'
        · rw [ih2 _ (fun w' hw' h => hL.1 (by rw [v_injective h]; exact hw')),
            Function.update_self]
        · rw [ih1 w hw', hcb, Function.update_of_ne]
          intro h
          exact hL.1 (by rw [← v_injective h]; exact hw')
      · rw [ih2 u (fun w hw => hu w (List.mem_cons_of_mem w0 hw)),
          Function.update_of_ne (hu w0 List.mem_cons_self)]

/-- A classical list on wires off the range of `ι` commutes with overwriting that range. -/
theorem cfgRun_overwrite_comm {W A : Type*} [DecidableEq W] [Fintype A] (gs : List (Gate W))
    {ι : A → W} (hι : Function.Injective ι)
    (h : ∀ g ∈ gs, (∀ a, ι a ≠ g.t) ∧ ∀ c ∈ g.cs, ∀ a, ι a ≠ c.1) (z : Cfg W) (d : Cfg A) :
    cfgRun gs (overwrite ι z d) = overwrite ι (cfgRun gs z) d := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      simp only [cfgRun]
      obtain ⟨h1, h2⟩ := h g List.mem_cons_self
      have hc : ctrlOK g.cs (overwrite ι z d) = ctrlOK g.cs z := by
        apply Bool.eq_iff_iff.mpr
        rw [ctrlOK_iff, ctrlOK_iff]
        constructor
        · intro hh c hc
          rw [← overwrite_apply_out ι z d c.1 (fun a => h2 c hc a)]
          exact hh c hc
        · intro hh c hc
          rw [overwrite_apply_out ι z d c.1 (fun a => h2 c hc a)]
          exact hh c hc
      have hfl : flipCfg g.cs g.t (overwrite ι z d) = overwrite ι (flipCfg g.cs g.t z) d := by
        rw [flipCfg_eq_update, flipCfg_eq_update, hc, overwrite_apply_out ι z d g.t h1,
          overwrite_update_out hι z d g.t _ h1]
      rw [hfl]
      exact ih (fun g' hg' => h g' (List.mem_cons_of_mem g hg')) _

end Value

section ValueSpec

variable {k b : ℕ}

/-- The validity of the pair of index words held by the edge wires. -/
def vpair (N : ℕ) (z : Cfg (IW k b)) : Bool :=
  ((!z (e (mw₁ k))) && decide (wordValue (fun i => z (xA i)) < N)) &&
    (!z (e (mw₂ k))) && decide (wordValue (fun i => z (xB i)) < N)

theorem classical_vflagC (N : ℕ) : Classical (vflagC (k := k) (b := b) N) := by
  unfold vflagC
  refine classical_append (classical_append (classical_ltChain N layoutA)
    (classical_ltChain N layoutB)) ?_
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl) <;> simp [e, g₁, bA]
  · refine ⟨rfl, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) <;> simp [e, g₁, g₂, bB]

/-- The wires read or written by the validity flag are not value wires. -/
theorem vflagC_avoids_v (N : ℕ) : ∀ g ∈ vflagC (k := k) (b := b) N,
    (∀ w, v w ≠ g.t) ∧ ∀ c ∈ g.cs, ∀ w, v w ≠ c.1 := by
  intro g hg
  unfold vflagC at hg
  simp only [List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · refine ⟨fun w h => ?_, fun c hc w h => ?_⟩
    · obtain ⟨j, -, hj⟩ := target_chainUpTo N xA bA (k + 1) g hg
      rw [hj] at h
      simp [bA, v] at h
    · exact ctrl_chainUpTo N xA bA (k + 1) g hg c hc (v w) (fun i => by simp [xA, tl, e, v])
        (fun j => by simp [bA, v]) h.symm
  · refine ⟨fun w h => ?_, fun c hc w h => ?_⟩
    · obtain ⟨j, -, hj⟩ := target_chainUpTo N xB bB (k + 1) g hg
      rw [hj] at h
      simp [bB, v] at h
    · exact ctrl_chainUpTo N xB bB (k + 1) g hg c hc (v w) (fun i => by simp [xB, tl, e, v])
        (fun j => by simp [bB, v]) h.symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · refine ⟨fun w h => by simp [g₁, v] at h, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl) w h <;> simp [e, v, bA] at h
    · refine ⟨fun w h => by simp [g₂, v] at h, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl) w h <;> simp [e, v, g₁, bB] at h

/-- **The validity flag on clean ancillas**: `g₂` ends with the validity of the pair, and only the
borrow chains and the flags change. -/
theorem cfgRun_vflagC {N : ℕ} (hN : N < 2 ^ (k + 1)) (z : Cfg (IW k b))
    (hA : ∀ j, z (bA j) = false) (hB : ∀ j, z (bB j) = false) (hg1 : z g₁ = false)
    (hg2 : z g₂ = false) :
    cfgRun (vflagC N) z g₂ = vpair N z ∧
      ∀ u, (∀ j, bA j ≠ u) → (∀ j, bB j ≠ u) → g₁ ≠ u → g₂ ≠ u → cfgRun (vflagC N) z u = z u := by
  set z1 := cfgRun (ltChain N xA bA) z with hz1
  set z2 := cfgRun (ltChain N xB bB) z1 with hz2
  have h1A : z1 topA = decide (wordValue (fun i => z (xA i)) < N) :=
    cfgRun_ltChain_top N layoutA hN z hA
  have h1B : ∀ j, z1 (bB j) = false := fun j => by
    rw [hz1, cfgRun_ltChain_out N xA bA z _ (fun j' => bA_ne_bB j' j)]
    exact hB j
  have h1x : (fun i => z1 (xB i)) = fun i => z (xB i) := funext fun i => by
    rw [hz1, cfgRun_ltChain_out N xA bA z _ (fun j' => (xB_ne_bA i j').symm)]
  have h2B : z2 topB = decide (wordValue (fun i => z (xB i)) < N) := by
    rw [hz2, cfgRun_ltChain_top N layoutB hN z1 h1B, h1x]
  have hout2 : ∀ u, (∀ j, bA j ≠ u) → (∀ j, bB j ≠ u) → z2 u = z u := fun u hu1 hu2 => by
    rw [hz2, cfgRun_ltChain_out N xB bB z1 u hu2, hz1, cfgRun_ltChain_out N xA bA z u hu1]
  have h2A : z2 topA = z1 topA := by
    rw [hz2, cfgRun_ltChain_out N xB bB z1 _ (fun j => bB_ne_bA j _)]
  have hm1 : z2 (e (mw₁ k)) = z (e (mw₁ k)) := hout2 _ (fun j => bA_ne_e j _) (fun j => bB_ne_e j _)
  have hm2 : z2 (e (mw₂ k)) = z (e (mw₂ k)) := hout2 _ (fun j => bA_ne_e j _) (fun j => bB_ne_e j _)
  have hzg1 : z2 g₁ = false := by
    rw [hout2 _ (fun j => by simp [bA, g₁]) (fun j => by simp [bB, g₁])]
    exact hg1
  have hzg2 : z2 g₂ = false := by
    rw [hout2 _ (fun j => by simp [bA, g₂]) (fun j => by simp [bB, g₂])]
    exact hg2
  have hne1 : (g₁ : IW k b) ≠ e (mw₁ k) := by simp [g₁, e]
  have hne2 : (g₁ : IW k b) ≠ topA := by simp [g₁, bA]
  have hne3 : (g₂ : IW k b) ≠ g₁ := by simp [g₁, g₂]
  have hne4 : (g₂ : IW k b) ≠ e (mw₂ k) := by simp [g₂, e]
  have hne5 : (g₂ : IW k b) ≠ topB := by simp [g₂, bB]
  have hfull : cfgRun (vflagC N) z = cfgRun
      [⟨[(e (mw₁ k), false), (topA, true)], g₁, pauliX⟩,
        ⟨[(g₁, true), (e (mw₂ k), false), (topB, true)], g₂, pauliX⟩] z2 := by
    unfold vflagC
    rw [cfgRun_append, cfgRun_append]
  rw [hfull]
  simp only [cfgRun, flipCfg_eq_update, ctrlOK_cons, ctrlOK_nil]
  refine ⟨?_, fun u hu1 hu2 hu3 hu4 => ?_⟩
  · have hg1e2 : e (b := b) (mw₂ k) ≠ g₁ := by simp [g₁, e]
    have hg1tB : (topB : IW k b) ≠ g₁ := by simp [g₁, bB]
    simp only [Function.update_self, Function.update_of_ne hg1e2, Function.update_of_ne hg1tB,
      Function.update_of_ne hne3, hzg1, hzg2, hm1, hm2, h2A, h1A, h2B]
    unfold vpair
    rcases Bool.eq_false_or_eq_true (z (e (mw₁ k))) with a | a <;>
      rcases Bool.eq_false_or_eq_true (z (e (mw₂ k))) with c | c <;>
      rcases Bool.eq_false_or_eq_true (decide (wordValue (fun i => z (xA i)) < N)) with d | d <;>
      rcases Bool.eq_false_or_eq_true (decide (wordValue (fun i => z (xB i)) < N)) with f | f <;>
      simp [a, c, d, f]
  · rw [Function.update_of_ne (Ne.symm hu4), Function.update_of_ne (Ne.symm hu3)]
    exact hout2 u hu1 hu2

end ValueSpec

end

end SparseHamiltonian.GeneralSparseAccess
