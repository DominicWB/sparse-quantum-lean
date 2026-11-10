import GeneralDecoder.Arith
import GeneralSparseAccess.Compare

/-!
# The rotation arithmetic with the validity of the index pair

The padded data with a validity decoder (`QData.padDataE`) decode an entry as `val w` on a pair of
valid index words and as `0` otherwise. The manuscript computes the validity predicate
`[i < N] ∧ [j < N]` on the indices and selects the zero-entry rotation on an invalid pair
"independently of the returned encoding" (Section `hs:sec:gates`, before Theorem `hs:thm:gates`).
`RotWordArith.flagLift N ar`
does this for a rotation arithmetic `ar` of `dec` on the value word: on the base wires of the
binary private operation on `k + 1`-bit index words it

1. computes the validity of the pair of index words on the index wires into a flag (`validC`: the
   comparisons of the two low words with `N` on clean borrow wires and the two clear markers),
2. runs `ar` on the value word into scratch words,
3. copies the scratch words into the angle words controlled on the flag (`flagCopies`),
4. uncomputes `ar` and the validity.

`flagLift_ok`: the arithmetic hypothesis of the native theorem for the decoder
`if valid then dec w else 0` (`flagDec`); `flagLift_length`, `flagLift_A`: its gates and work
wires.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess (ltChain CmpLayout cfgRun_ltChain_top
  cfgRun_ltChain_out cfgRun_reverse_cancel classical_ltChain gateOK_ltChain length_ltChain_le)
open SparseHamiltonian.GatePointerEncoding (wordValue)
open GateOptimalBinary (cfgRun_map classical_map)
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)

/-! ### Classical gate lists -/

section Classical

variable {W : Type*} [DecidableEq W]

theorem flipCfg_update' (cs : List (W × Bool)) (t : W) (x : Cfg W) :
    flipCfg cs t x = Function.update x t (x t ^^ ctrlOK cs x) := by
  unfold flipCfg
  split_ifs with h
  · rw [h, Bool.xor_true]
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.xor_false, Function.update_eq_self]

omit [DecidableEq W] in
theorem classical_reverse {gs : List (Gate W)} (h : Classical gs) : Classical gs.reverse :=
  fun g hg => h g (List.mem_reverse.mp hg)

omit [DecidableEq W] in
theorem classical_append {gs hs : List (Gate W)} (h1 : Classical gs) (h2 : Classical hs) :
    Classical (gs ++ hs) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h1 g h
  · exact h2 g h

/-- The controlled copy of the wire `src i` into `tgt i` under the flag `fl`. -/
def copyG {ι : Type*} (fl : W) (src tgt : ι → W) (i : ι) : Gate W :=
  ⟨[(fl, true), (src i, true)], tgt i, pauliX⟩

/-- **Controlled copies**: on distinct targets, outside the flag and the sources, each target is
XOR-ed with `flag ∧ source`, and no other wire changes. -/
theorem cfgRun_copies {ι : Type*} (fl : W) (src tgt : ι → W) (L : List ι) (hL : L.Nodup)
    (hinj : ∀ i ∈ L, ∀ j ∈ L, tgt i = tgt j → i = j) (hfl : ∀ i ∈ L, tgt i ≠ fl)
    (hsrc : ∀ i ∈ L, ∀ j ∈ L, tgt i ≠ src j) (z : Cfg W) :
    (∀ i ∈ L, cfgRun (L.map (copyG fl src tgt)) z (tgt i) = (z (tgt i) ^^ (z fl && z (src i)))) ∧
      ∀ u, (∀ i ∈ L, tgt i ≠ u) → cfgRun (L.map (copyG fl src tgt)) z u = z u := by
  induction L generalizing z with
  | nil => exact ⟨fun i hi => by simp at hi, fun u _ => rfl⟩
  | cons i0 L ih =>
      rw [List.nodup_cons] at hL
      have hinj' : ∀ i ∈ L, ∀ j ∈ L, tgt i = tgt j → i = j := fun i hi j hj h =>
        hinj i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj) h
      have hfl' : ∀ i ∈ L, tgt i ≠ fl := fun i hi => hfl i (List.mem_cons_of_mem _ hi)
      have hsrc' : ∀ i ∈ L, ∀ j ∈ L, tgt i ≠ src j := fun i hi j hj =>
        hsrc i (List.mem_cons_of_mem _ hi) j (List.mem_cons_of_mem _ hj)
      set z' := Function.update z (tgt i0) (z (tgt i0) ^^ (z fl && z (src i0))) with hz'
      have hstep : cfgRun ((i0 :: L).map (copyG fl src tgt)) z =
          cfgRun (L.map (copyG fl src tgt)) z' := by
        rw [List.map_cons]
        show cfgRun (L.map (copyG fl src tgt))
          (flipCfg [(fl, true), (src i0, true)] (tgt i0) z) = _
        have hc : ctrlOK [(fl, true), (src i0, true)] z = (z fl && z (src i0)) := by
          simp only [ctrlOK_cons, ctrlOK_nil]
          cases z fl <;> cases z (src i0) <;> rfl
        rw [flipCfg_update', hc]
      obtain ⟨ih1, ih2⟩ := ih hL.2 hinj' hfl' hsrc' z'
      have hne0 : ∀ i ∈ L, tgt i ≠ tgt i0 := fun i hi h =>
        hL.1 (by rw [hinj i (List.mem_cons_of_mem _ hi) i0 List.mem_cons_self h] at hi; exact hi)
      have hfl0 : fl ≠ tgt i0 := (hfl i0 List.mem_cons_self).symm
      rw [hstep]
      refine ⟨fun i hi => ?_, fun u hu => ?_⟩
      · rcases List.mem_cons.mp hi with rfl | hi
        · rw [ih2 _ hne0, hz', Function.update_self]
        · rw [ih1 i hi, hz', Function.update_of_ne (hne0 i hi),
            Function.update_of_ne hfl0,
            Function.update_of_ne (Ne.symm (hsrc i0 List.mem_cons_self i
              (List.mem_cons_of_mem _ hi)))]
      · rw [ih2 u (fun i hi => hu i (List.mem_cons_of_mem _ hi)), hz',
          Function.update_of_ne (Ne.symm (hu i0 List.mem_cons_self))]

omit [DecidableEq W] in
theorem classical_copies {ι : Type*} (fl : W) (src tgt : ι → W) (L : List ι)
    (hfl : ∀ i ∈ L, tgt i ≠ fl) (hsrc : ∀ i ∈ L, tgt i ≠ src i) :
    Classical (L.map (copyG fl src tgt)) := by
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hg
  refine ⟨rfl, fun c hc => ?_⟩
  simp only [copyG, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact (hfl i hi).symm
  · exact (hsrc i hi).symm

/-- A mapped classical gate list acts on the embedded wires as the gate list. -/
theorem cfgRun_map_apply {A : Type*} [Fintype A] [DecidableEq A] {e : A → W}
    (he : Function.Injective e) (gs : List (Gate A)) (y : Cfg W) (a : A) :
    cfgRun (gs.map (GateODE.Gate.map e)) y (e a) = cfgRun gs (fun a => y (e a)) a := by
  rw [cfgRun_map he, overwrite_apply_ι he]

/-- A mapped classical gate list does not change the wires outside the embedding. -/
theorem cfgRun_map_out {A : Type*} [Fintype A] [DecidableEq A] {e : A → W}
    (he : Function.Injective e) (gs : List (Gate A)) (y : Cfg W) (w : W) (hw : ∀ a, e a ≠ w) :
    cfgRun (gs.map (GateODE.Gate.map e)) y w = y w := by
  rw [cfgRun_map he, overwrite_apply_out _ _ _ _ hw]

end Classical

/-! ### The validity of the pair of index words -/

/-- The work wires of the validity circuit: two borrow chains and two flags. -/
abbrev FW (k : ℕ) := (Fin (k + 2) ⊕ Fin (k + 2)) ⊕ (Unit ⊕ Unit)

/-- The wires of the validity circuit: the edge word of `k + 1`-bit index words and the work. -/
abbrev WF (k : ℕ) := EW (k + 1) ⊕ FW k

namespace WF

variable {k : ℕ}

/-- The low word of the first index. -/
def xA (j : Fin k) : WF k := Sum.inl (Sum.inl (Fin.castSucc j))
/-- The low word of the second index. -/
def xB (j : Fin k) : WF k := Sum.inl (Sum.inr (Fin.castSucc j))
/-- The marker of the first index. -/
def m₁ : WF k := Sum.inl (Sum.inl (Fin.last k))
/-- The marker of the second index. -/
def m₂ : WF k := Sum.inl (Sum.inr (Fin.last k))
/-- The first borrow chain. -/
def bA (j : Fin (k + 2)) : WF k := Sum.inr (Sum.inl (Sum.inl j))
/-- The second borrow chain. -/
def bB (j : Fin (k + 2)) : WF k := Sum.inr (Sum.inl (Sum.inr j))
/-- The first flag. -/
def g₁ : WF k := Sum.inr (Sum.inr (Sum.inl ()))
/-- The validity flag. -/
def g₂ : WF k := Sum.inr (Sum.inr (Sum.inr ()))
/-- The last borrow wire of the first chain. -/
abbrev topA : WF k := bA ⟨k + 1, by omega⟩
/-- The last borrow wire of the second chain. -/
abbrev topB : WF k := bB ⟨k + 1, by omega⟩

theorem layoutA : CmpLayout (xA (k := k)) bA where
  inj_x := fun i j h => Fin.castSucc_injective _ (Sum.inl_injective (Sum.inl_injective h))
  inj_b := fun i j h => Sum.inl_injective (Sum.inl_injective (Sum.inr_injective h))
  x_ne_b := fun i j h => by simp [xA, bA] at h

theorem layoutB : CmpLayout (xB (k := k)) bB where
  inj_x := fun i j h => Fin.castSucc_injective _ (Sum.inr_injective (Sum.inl_injective h))
  inj_b := fun i j h => Sum.inr_injective (Sum.inl_injective (Sum.inr_injective h))
  x_ne_b := fun i j h => by simp [xB, bB] at h

end WF

variable {k : ℕ}

/-- **The validity circuit**: compare both low words with `N`, then `g₂ = [valid pair]`. -/
def validC (N : ℕ) : List (Gate (WF k)) :=
  ltChain N WF.xA WF.bA ++ ltChain N WF.xB WF.bB ++
    [⟨[(WF.m₁, false), (WF.topA, true)], WF.g₁, pauliX⟩,
      ⟨[(WF.g₁, true), (WF.m₂, false), (WF.topB, true)], WF.g₂, pauliX⟩]

/-- **The validity of the pair of index words** of an edge word: both markers clear and both low
words below `N`. -/
def evalidW (N : ℕ) (ew : Cfg (EW (k + 1))) : Bool :=
  (!ew (Sum.inl (Fin.last k)) &&
      decide (wordValue (fun j : Fin k => ew (Sum.inl (Fin.castSucc j))) < N)) &&
    (!ew (Sum.inr (Fin.last k)) &&
      decide (wordValue (fun j : Fin k => ew (Sum.inr (Fin.castSucc j))) < N))

theorem classical_validC (N : ℕ) : Classical (validC (k := k) N) := by
  unfold validC
  refine classical_append (classical_append (classical_ltChain N WF.layoutA)
    (classical_ltChain N WF.layoutB)) ?_
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · refine ⟨rfl, fun c hc => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp [WF.m₁, WF.topA, WF.bA, WF.g₁]
  · refine ⟨rfl, fun c hc => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp [WF.m₂, WF.topB, WF.bB, WF.g₁, WF.g₂]

theorem gateOK_validC (N : ℕ) : ∀ g ∈ validC (k := k) N, g.cs.length ≤ 3 := by
  intro g hg
  unfold validC at hg
  simp only [List.mem_append] at hg
  rcases hg with (h | h) | h
  · exact (gateOK_ltChain N WF.layoutA g h).1
  · exact (gateOK_ltChain N WF.layoutB g h).1
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp

theorem length_validC_le (N : ℕ) : (validC (k := k) N).length ≤ 4 * (k + 1) + 2 := by
  unfold validC
  simp only [List.length_append, List.length_cons, List.length_nil]
  have h1 := length_ltChain_le N (WF.xA (k := k)) WF.bA
  have h2 := length_ltChain_le N (WF.xB (k := k)) WF.bB
  omega

/-- **The validity circuit on clean work wires**: the flag `g₂` ends with the validity of the pair,
and the edge word is unchanged. -/
theorem cfgRun_validC {N : ℕ} (hN : N < 2 ^ (k + 1)) (z : Cfg (WF k))
    (hF : ∀ f, z (Sum.inr f) = false) :
    cfgRun (validC N) z WF.g₂ = evalidW N (fun e => z (Sum.inl e)) ∧
      ∀ e, cfgRun (validC N) z (Sum.inl e) = z (Sum.inl e) := by
  have hA : ∀ j, z (WF.bA j) = false := fun j => hF _
  have hB : ∀ j, z (WF.bB j) = false := fun j => hF _
  set z1 := cfgRun (ltChain N WF.xA WF.bA) z with hz1
  set z2 := cfgRun (ltChain N WF.xB WF.bB) z1 with hz2
  have h1A : z1 WF.topA = decide (wordValue (fun i => z (WF.xA i)) < N) :=
    cfgRun_ltChain_top N WF.layoutA hN z hA
  have h1B : ∀ j, z1 (WF.bB j) = false := fun j => by
    rw [hz1, cfgRun_ltChain_out N WF.xA WF.bA z _ (fun j' => by simp [WF.bA, WF.bB])]
    exact hB j
  have h1x : (fun i => z1 (WF.xB i)) = fun i => z (WF.xB i) := funext fun i => by
    rw [hz1, cfgRun_ltChain_out N WF.xA WF.bA z _ (fun j' => by simp [WF.bA, WF.xB])]
  have h2B : z2 WF.topB = decide (wordValue (fun i => z (WF.xB i)) < N) := by
    rw [hz2, cfgRun_ltChain_top N WF.layoutB hN z1 h1B, h1x]
  have hout2 : ∀ u, (∀ j, WF.bA j ≠ u) → (∀ j, WF.bB j ≠ u) → z2 u = z u := fun u hu1 hu2 => by
    rw [hz2, cfgRun_ltChain_out N WF.xB WF.bB z1 u hu2, hz1,
      cfgRun_ltChain_out N WF.xA WF.bA z u hu1]
  have h2A : z2 WF.topA = z1 WF.topA := by
    rw [hz2, cfgRun_ltChain_out N WF.xB WF.bB z1 _ (fun j => by simp [WF.bA, WF.bB, WF.topA])]
  have hm1 : z2 WF.m₁ = z WF.m₁ :=
    hout2 _ (fun j => by simp [WF.bA, WF.m₁]) (fun j => by simp [WF.bB, WF.m₁])
  have hm2 : z2 WF.m₂ = z WF.m₂ :=
    hout2 _ (fun j => by simp [WF.bA, WF.m₂]) (fun j => by simp [WF.bB, WF.m₂])
  have hzg1 : z2 WF.g₁ = false := by
    rw [hout2 _ (fun j => by simp [WF.bA, WF.g₁]) (fun j => by simp [WF.bB, WF.g₁])]
    exact hF _
  have hzg2 : z2 WF.g₂ = false := by
    rw [hout2 _ (fun j => by simp [WF.bA, WF.g₂]) (fun j => by simp [WF.bB, WF.g₂])]
    exact hF _
  have hne3 : (WF.g₂ : WF k) ≠ WF.g₁ := by simp [WF.g₁, WF.g₂]
  have hfull : cfgRun (validC N) z = cfgRun
      [⟨[(WF.m₁, false), (WF.topA, true)], WF.g₁, pauliX⟩,
        ⟨[(WF.g₁, true), (WF.m₂, false), (WF.topB, true)], WF.g₂, pauliX⟩] z2 := by
    unfold validC
    rw [cfgRun_append, cfgRun_append]
  rw [hfull]
  simp only [cfgRun, flipCfg_update', ctrlOK_cons, ctrlOK_nil]
  refine ⟨?_, fun e => ?_⟩
  · have hg1e2 : (WF.m₂ : WF k) ≠ WF.g₁ := by simp [WF.g₁, WF.m₂]
    have hg1tB : (WF.topB : WF k) ≠ WF.g₁ := by simp [WF.g₁, WF.topB, WF.bB]
    simp only [Function.update_self, Function.update_of_ne hg1e2, Function.update_of_ne hg1tB,
      Function.update_of_ne hne3, hzg1, hzg2, hm1, hm2, h2A, h1A, h2B]
    unfold evalidW
    change _ = ((!z WF.m₁ && decide (wordValue (fun i => z (WF.xA i)) < N)) &&
      (!z WF.m₂ && decide (wordValue (fun i => z (WF.xB i)) < N)))
    rcases Bool.eq_false_or_eq_true (z WF.m₁) with a | a <;>
      rcases Bool.eq_false_or_eq_true (z WF.m₂) with c | c <;>
      rcases Bool.eq_false_or_eq_true (decide (wordValue (fun i => z (WF.xA i)) < N)) with d | d <;>
      rcases Bool.eq_false_or_eq_true (decide (wordValue (fun i => z (WF.xB i)) < N)) with f | f <;>
      simp [a, c, d, f]
  · rw [Function.update_of_ne (by simp [WF.g₂]), Function.update_of_ne (by simp [WF.g₁])]
    exact hout2 _ (fun j => by simp [WF.bA]) (fun j => by simp [WF.bB])

/-! ### The wrapper -/

section Wrapper

variable {b : ℕ}

/-- The scratch of the arithmetic as a block of work wires. -/
def eAW (bT bP A : ℕ) : AWr bT bP A ≃ Fin (bT + bP + A) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl _)).trans finSumFinEquiv

/-- The number of work wires of the wrapper: the scratch of the arithmetic and the validity. -/
def flagA (k bT bP A : ℕ) : ℕ := bT + bP + A + Fintype.card (FW k)

theorem card_FW (k : ℕ) : Fintype.card (FW k) = 2 * k + 6 := by
  simp only [FW, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  ring

/-- The scratch wires of the arithmetic among the work wires. -/
def sAW {bT bP A : ℕ} (a : AWr bT bP A) : Fin (flagA k bT bP A) :=
  Fin.castAdd _ (eAW bT bP A a)

/-- The work wires of the validity among the work wires. -/
def sFW {bT bP A : ℕ} (f : FW k) : Fin (flagA k bT bP A) :=
  Fin.natAdd _ (Fintype.equivFin (FW k) f)

theorem sAW_injective {bT bP A : ℕ} : Function.Injective (sAW (k := k) (bT := bT) (bP := bP)
    (A := A)) := fun _ _ h => (eAW bT bP A).injective (Fin.castAdd_injective _ _ h)

theorem sFW_injective {bT bP A : ℕ} : Function.Injective (sFW (k := k) (bT := bT) (bP := bP)
    (A := A)) := fun _ _ h => (Fintype.equivFin (FW k)).injective (Fin.natAdd_injective _ _ h)

theorem sAW_ne_sFW {bT bP A : ℕ} (a : AWr bT bP A) (f : FW k) : sAW (k := k) a ≠ sFW f := by
  intro h
  have := congrArg Fin.val h
  simp only [sAW, sFW, Fin.val_castAdd, Fin.val_natAdd] at this
  have h1 := (eAW bT bP A a).isLt
  omega

/-- The wires of the wrapper: the base wires and the arithmetic wires. -/
abbrev WW (k b bT bP A : ℕ) := BW (k + 1) b ⊕ AWr bT bP (flagA k bT bP A)

/-- The wires of the arithmetic `ar` inside the wrapper. -/
def ιA {bT bP A : ℕ} : VW b ⊕ AWr bT bP A → WW k b bT bP A :=
  Sum.elim (fun v => Sum.inl (vB v)) (fun a => Sum.inr (Sum.inr (sAW a)))

/-- The wires of the validity circuit inside the wrapper. -/
def ιF {bT bP A : ℕ} : WF k → WW k b bT bP A :=
  Sum.elim (fun e => Sum.inl (tB e)) (fun f => Sum.inr (Sum.inr (sFW f)))

theorem ιA_injective {bT bP A : ℕ} : Function.Injective (ιA (k := k) (b := b) (bT := bT)
    (bP := bP) (A := A)) := by
  rintro (v | a) (v' | a') h <;> simp only [ιA, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (vB_injective (Sum.inl_injective h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (sAW_injective (Sum.inr_injective (Sum.inr_injective h)))

theorem ιF_injective {bT bP A : ℕ} : Function.Injective (ιF (k := k) (b := b) (bT := bT)
    (bP := bP) (A := A)) := by
  rintro (e | f) (e' | f') h <;> simp only [ιF, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (tB_injective (Sum.inl_injective h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (sFW_injective (Sum.inr_injective (Sum.inr_injective h)))

theorem ιA_ne_ιF {bT bP A : ℕ} (u : VW b ⊕ AWr bT bP A) (w : WF k) :
    ιA (k := k) u ≠ ιF w := by
  rcases u with v | a <;> rcases w with e | f <;> simp only [ιA, ιF, Sum.elim_inl, Sum.elim_inr]
  · exact fun h => tB_ne_vB e v (Sum.inl_injective h).symm
  · exact fun h => by cases h
  · exact fun h => by cases h
  · exact fun h => sAW_ne_sFW a f (Sum.inr_injective (Sum.inr_injective h))

/-- The angle-word output wire `j`. -/
def oT {bT bP A : ℕ} (j : Fin bT) : WW k b bT bP A := Sum.inr (Sum.inl (Sum.inl j))
/-- The phase-word output wire `j`. -/
def oP {bT bP A : ℕ} (j : Fin bP) : WW k b bT bP A := Sum.inr (Sum.inl (Sum.inr j))

/-- The source and target wires of the controlled copies. -/
def cpSrc {bT bP A : ℕ} : Fin bT ⊕ Fin bP → WW k b bT bP A :=
  fun j => ιA (Sum.inr (Sum.inl j))

def cpTgt {bT bP A : ℕ} : Fin bT ⊕ Fin bP → WW k b bT bP A :=
  fun j => Sum.inr (Sum.inl j)

/-- The copies of the scratch words into the output words under the validity flag. -/
def flagCopies (k b bT bP A : ℕ) : List (Gate (WW k b bT bP A)) :=
  ((Finset.univ : Finset (Fin bT ⊕ Fin bP)).toList).map
    (copyG (ιF WF.g₂) cpSrc cpTgt)

/-- **The rotation arithmetic with the validity of the index pair.** -/
def RotWordArith.flagLift (N : ℕ) {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}
    (ar : RotWordArith b dec ζ bT bP A) : Arith (BW (k + 1) b) where
  bT := bT
  bP := bP
  A := flagA k bT bP A
  circ := (validC N).map (GateODE.Gate.map ιF) ++ ar.circ.map (GateODE.Gate.map ιA) ++
    flagCopies k b bT bP A ++ (ar.circ.map (GateODE.Gate.map ιA)).reverse ++
    ((validC N).map (GateODE.Gate.map ιF)).reverse
  tw := fun y => if evalidW N (eword y) then ar.tw (vword y) else fun _ => false
  pw := fun y => if evalidW N (eword y) then ar.pw (vword y) else fun _ => false

/-- The decoder with the validity of the index pair. -/
def flagDec (N : ℕ) (dec : Cfg (VW b) → ℂ) (y : Cfg (BW (k + 1) b)) : ℂ :=
  if evalidW N (eword y) then dec (vword y) else 0

end Wrapper

/-! ### The arithmetic hypothesis of the wrapper -/

section WrapperOK

variable {b : ℕ} {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}

@[simp] theorem RotWordArith.flagLift_bT (N : ℕ) (ar : RotWordArith b dec ζ bT bP A) :
    (ar.flagLift (k := k) N).bT = bT := rfl

@[simp] theorem RotWordArith.flagLift_bP (N : ℕ) (ar : RotWordArith b dec ζ bT bP A) :
    (ar.flagLift (k := k) N).bP = bP := rfl

@[simp] theorem RotWordArith.flagLift_A (N : ℕ) (ar : RotWordArith b dec ζ bT bP A) :
    (ar.flagLift (k := k) N).A = flagA k bT bP A := rfl

theorem length_flagCopies : (flagCopies k b bT bP A).length = bT + bP := by
  simp [flagCopies]

/-- **The gates of the wrapper**: twice the validity circuit and the arithmetic, and the copies. -/
theorem RotWordArith.flagLift_length (N : ℕ) (ar : RotWordArith b dec ζ bT bP A) :
    (ar.flagLift (k := k) N).circ.length =
      2 * (validC (k := k) N).length + 2 * ar.circ.length + (bT + bP) := by
  simp only [RotWordArith.flagLift, List.length_append, List.length_reverse, List.length_map,
    length_flagCopies]
  ring

theorem cpTgt_ne_ιF (j : Fin bT ⊕ Fin bP) (w : WF k) :
    (cpTgt j : WW k b bT bP A) ≠ ιF w := by
  rcases w with e | f <;> simp [cpTgt, ιF]

theorem cpTgt_ne_ιA (j : Fin bT ⊕ Fin bP) (a : VW b ⊕ AWr bT bP A) :
    (cpTgt j : WW k b bT bP A) ≠ ιA a := by
  rcases a with v | a <;> simp [cpTgt, ιA]

theorem cpTgt_injective : Function.Injective (cpTgt (k := k) (b := b) (bT := bT) (bP := bP)
    (A := A)) := fun _ _ h => Sum.inl_injective (Sum.inr_injective h)

theorem cpSrc_eq (j : Fin bT ⊕ Fin bP) :
    (cpSrc j : WW k b bT bP A) = ιA (Sum.inr (Sum.inl j)) := rfl

/-- **The arithmetic hypothesis of the native theorem for the validity decoder**, from a rotation
arithmetic on the value word. -/
theorem RotWordArith.flagLift_ok (N : ℕ) (hN : N < 2 ^ (k + 1))
    (ar : RotWordArith b dec ζ bT bP A) :
    ArithOK (ar.flagLift (k := k) N) (Sum.inl (Sum.inr (oPR (k + 1)))) (flagDec N dec) ζ where
  elem g hg := by
    change g ∈ (validC (k := k) N).map (GateODE.Gate.map
        (ιF (k := k) (b := b) (bT := bT) (bP := bP) (A := A))) ++
      ar.circ.map (GateODE.Gate.map (ιA (k := k) (b := b) (bT := bT) (bP := bP) (A := A))) ++
      flagCopies k b bT bP A ++
      (ar.circ.map (GateODE.Gate.map (ιA (k := k) (b := b) (bT := bT) (bP := bP)
        (A := A)))).reverse ++
      ((validC (k := k) N).map (GateODE.Gate.map
        (ιF (k := k) (b := b) (bT := bT) (bP := bP) (A := A)))).reverse at hg
    rcases List.mem_append.mp hg with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h
            simpa [GateODE.Gate.map] using gateOK_validC N g' hg'
          · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h
            simpa [GateODE.Gate.map] using ar.elem g' hg'
        · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
          simp [copyG]
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 (List.mem_reverse.mp h)
        simpa [GateODE.Gate.map] using ar.elem g' hg'
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 (List.mem_reverse.mp h)
      simpa [GateODE.Gate.map] using gateOK_validC N g' hg'
  classical := by
    have hF : Classical ((validC (k := k) N).map (GateODE.Gate.map
        (ιF (k := k) (b := b) (bT := bT) (bP := bP) (A := A)))) :=
      classical_map ιF_injective (classical_validC N)
    have hA' : Classical (ar.circ.map (GateODE.Gate.map
        (ιA (k := k) (b := b) (bT := bT) (bP := bP) (A := A)))) :=
      classical_map ιA_injective ar.classical
    have hC : Classical (flagCopies k b bT bP A) :=
      classical_copies _ _ _ _ (fun j _ => cpTgt_ne_ιF j _) (fun j _ => cpTgt_ne_ιA j _)
    exact classical_append (classical_append (classical_append (classical_append hF hA') hC)
      (classical_reverse hA')) (classical_reverse hF)
  compute x := by
    set fF := ιF (k := k) (b := b) (bT := bT) (bP := bP) (A := A) with hfF
    set fA := ιA (k := k) (b := b) (bT := bT) (bP := bP) (A := A) with hfA
    have hFi : Function.Injective fF := ιF_injective
    have hAi : Function.Injective fA := ιA_injective
    set cF := (validC (k := k) N).map (GateODE.Gate.map fF) with hcF
    set cA := ar.circ.map (GateODE.Gate.map fA) with hcA
    set cC := flagCopies k b bT bP A with hcC
    set z0 : Cfg (WW k b bT bP A) := Sum.elim x (fun _ => false) with hz0
    change cfgRun (cF ++ cA ++ cC ++ cA.reverse ++ cF.reverse) z0 =
      Sum.elim x (Sum.elim (Sum.elim (if evalidW N (eword x) then ar.tw (vword x) else
        fun _ => false) (if evalidW N (eword x) then ar.pw (vword x) else fun _ => false))
        (fun _ => false))
    rw [cfgRun_append, cfgRun_append, cfgRun_append, cfgRun_append]
    set z1 := cfgRun cF z0 with hz1
    set z2 := cfgRun cA z1 with hz2
    set z3 := cfgRun cC z2 with hz3
    set z4 := cfgRun cA.reverse z3 with hz4
    -- the validity run on the restricted configuration
    have hz0F : (fun w => z0 (fF w)) = Sum.elim (eword x) (fun _ => false) := by
      funext w
      rcases w with e | f <;> rfl
    set zF := cfgRun (validC (k := k) N) (fun w => z0 (fF w)) with hzF
    obtain ⟨hflag, -⟩ := cfgRun_validC (k := k) hN (fun w => z0 (fF w)) (fun f => rfl)
    have hfl : zF WF.g₂ = evalidW N (eword x) := by
      rw [hzF, hflag]
      rfl
    have h1F : ∀ w, z1 (fF w) = zF w := fun w => cfgRun_map_apply hFi _ _ w
    have h1o : ∀ u, (∀ w, fF w ≠ u) → z1 u = z0 u := fun u hu => cfgRun_map_out hFi _ _ u hu
    -- the arithmetic run
    have hz1A : (fun a => z1 (fA a)) = Sum.elim (vword x) (fun _ => false) := by
      funext a
      rw [h1o _ (fun w h => ιA_ne_ιF a w h.symm)]
      rcases a with v | a <;> rfl
    have h2A : ∀ a, z2 (fA a) = Sum.elim (vword x)
        (Sum.elim (Sum.elim (ar.tw (vword x)) (ar.pw (vword x))) (fun _ => false)) a := by
      intro a
      rw [hz2, hcA, cfgRun_map_apply hAi, hz1A, ar.compute]
    have h2o : ∀ u, (∀ a, fA a ≠ u) → z2 u = z1 u := fun u hu => cfgRun_map_out hAi _ _ u hu
    -- the copies
    have hL := (Finset.univ : Finset (Fin bT ⊕ Fin bP)).nodup_toList
    obtain ⟨h3T, h3o⟩ := cfgRun_copies (fF WF.g₂) (cpSrc (k := k) (b := b) (A := A))
      (cpTgt (k := k) (b := b) (A := A)) _ hL (fun i _ j _ h => cpTgt_injective h)
      (fun j _ => cpTgt_ne_ιF j _) (fun i _ j _ => by rw [cpSrc_eq]; exact cpTgt_ne_ιA i _) z2
    change (∀ j ∈ _, z3 (cpTgt j) = _) at h3T
    change ∀ u, _ → z3 u = z2 u at h3o
    -- the inverse arithmetic
    have hrevA : cA.reverse = ar.circ.reverse.map (GateODE.Gate.map fA) := by
      rw [hcA, List.map_reverse]
    have hz3A : (fun a => z3 (fA a)) = cfgRun ar.circ (Sum.elim (vword x) (fun _ => false)) := by
      funext a
      rw [h3o _ (fun j _ => cpTgt_ne_ιA j a), h2A, ar.compute]
    have h4A : ∀ a, z4 (fA a) = Sum.elim (vword x) (fun _ => false) a := by
      intro a
      rw [hz4, hrevA, cfgRun_map_apply hAi, hz3A, cfgRun_reverse_cancel _ ar.classical]
    have h4o : ∀ u, (∀ a, fA a ≠ u) → z4 u = z3 u := fun u hu => by
      rw [hz4, hrevA]
      exact cfgRun_map_out hAi _ _ u hu
    -- the inverse validity
    have hrevF : cF.reverse = (validC (k := k) N).reverse.map (GateODE.Gate.map fF) := by
      rw [hcF, List.map_reverse]
    have hz4F : (fun w => z4 (fF w)) = zF := by
      funext w
      rw [h4o _ (fun a h => ιA_ne_ιF a w h), h3o _ (fun j _ => cpTgt_ne_ιF j w),
        h2o _ (fun a h => ιA_ne_ιF a w h), h1F]
    have h5F : ∀ w, cfgRun cF.reverse z4 (fF w) = z0 (fF w) := by
      intro w
      rw [hrevF, cfgRun_map_apply hFi, hz4F, hzF,
        cfgRun_reverse_cancel _ (classical_validC N)]
    have h5o : ∀ u, (∀ w, fF w ≠ u) → cfgRun cF.reverse z4 u = z4 u := fun u hu => by
      rw [hrevF]
      exact cfgRun_map_out hFi _ _ u hu
    -- the final configuration
    funext u
    by_cases huF : ∃ w, fF w = u
    · obtain ⟨w, rfl⟩ := huF
      rw [h5F]
      rcases w with e | f <;> rfl
    by_cases huA : ∃ a, fA a = u
    · obtain ⟨a, rfl⟩ := huA
      rw [h5o _ (fun w h => huF ⟨w, h⟩), h4A]
      rcases a with v | a <;> rfl
    push Not at huF huA
    rw [h5o _ huF, h4o _ huA]
    by_cases huC : ∃ j, cpTgt (k := k) (b := b) (A := A) j = u
    · obtain ⟨j, rfl⟩ := huC
      rw [h3T j (Finset.mem_toList.mpr (Finset.mem_univ j)), h2o _ huA, h1o _ huF,
        show fF WF.g₂ = fF WF.g₂ from rfl]
      have hzfl : z2 (fF WF.g₂) = evalidW N (eword x) := by
        rw [h2o _ (fun a h => ιA_ne_ιF a WF.g₂ h), h1F, hfl]
      rw [hzfl, cpSrc_eq, h2A]
      rcases j with j | j <;>
        · simp only [cpTgt, hz0, Sum.elim_inr, Sum.elim_inl, Bool.false_xor]
          by_cases hv : evalidW N (eword x) <;> simp [hv]
    · push Not at huC
      rw [h3o _ (fun j _ => huC j), h2o _ huA, h1o _ huF]
      rcases u with p | ((j | j) | i)
      · rfl
      · exact absurd rfl (huC (Sum.inl j))
      · exact absurd rfl (huC (Sum.inr j))
      · rfl
  tw_indep x v := by
    change (if evalidW N (eword (Function.update x (Sum.inl (Sum.inr (oPR (k + 1)))) v)) then
        ar.tw (vword (Function.update x (Sum.inl (Sum.inr (oPR (k + 1)))) v)) else
        fun _ => false) = (if evalidW N (eword x) then ar.tw (vword x) else fun _ => false)
    rw [show (Sum.inl (Sum.inr (oPR (k + 1))) : BW (k + 1) b) = oB from rfl, eword_update_oB,
      vword_update_oB]
  pw_indep x v := by
    change (if evalidW N (eword (Function.update x (Sum.inl (Sum.inr (oPR (k + 1)))) v)) then
        ar.pw (vword (Function.update x (Sum.inl (Sum.inr (oPR (k + 1)))) v)) else
        fun _ => false) = (if evalidW N (eword x) then ar.pw (vword x) else fun _ => false)
    rw [show (Sum.inl (Sum.inr (oPR (k + 1))) : BW (k + 1) b) = oB from rfl, eword_update_oB,
      vword_update_oB]
  theta x := by
    change |thetaVal (if evalidW N (eword x) then ar.tw (vword x) else fun _ => false) -
      2 * Real.arctan ‖flagDec N dec x‖| ≤ ζ
    unfold flagDec
    by_cases hv : evalidW N (eword x)
    · rw [if_pos hv, if_pos hv]
      exact ar.theta (vword x)
    · rw [if_neg hv, if_neg hv]
      have h0 : thetaVal (fun _ : Fin bT => false) = 0 := by simp [thetaVal]
      rw [h0, norm_zero, Real.arctan_zero, mul_zero, sub_zero, abs_zero]
      exact (abs_nonneg _).trans (ar.theta (fun _ => false))
  phi x hx := by
    unfold flagDec at hx
    by_cases hv : evalidW N (eword x)
    · rw [if_pos hv] at hx
      change ∃ m : ℤ, |phiVal (if evalidW N (eword x) then ar.pw (vword x) else
        fun _ => false) - Complex.arg (flagDec N dec x) - 2 * Real.pi * m| ≤ ζ
      unfold flagDec
      rw [if_pos hv, if_pos hv]
      exact ar.phi (vword x) hx
    · rw [if_neg hv] at hx
      exact absurd rfl hx

end WrapperOK

end

end SparseHamiltonian.GeneralDecoder
