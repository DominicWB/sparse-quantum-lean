import GeneralDecoder.Flag
import GeneralDecoder.MainNative

/-!
# Word arithmetic with the validity of the index pair, on general base wires

`GeneralDecoder.Flag` wraps a rotation arithmetic of the value word with the validity of the index
pair on the base wires of the bounded private operation. The native operations of the
signed-factor and clipped regimes of Theorem `gate:thm:main` read further inputs (the branch and
the flag of the clipped regime), and on an invalid pair the clipped rotation of the zero entry is
not the zero rotation: its decoded value is `y(g, f, 0, 0) = 2q [g][f]`. This file wraps a word
arithmetic `WordArith I` on input wires `ιI : I → B` of general base wires `B` with the validity of
the pair of index words on edge wires `ιE : EW (k + 1) → B`:

1. compute the validity of the pair into a flag (`validC`);
2. run the arithmetic on the inputs into scratch words;
3. compute the angle flag `valid ∨ [g]` for an optional input bit `g` (`ftGates`);
4. copy the scratch angle word into the angle word under the angle flag, and the scratch phase
   word into the phase word under the validity flag (`copiesG`);
5. uncompute the angle flag, the arithmetic and the validity.

`WordArith.flagLiftG_compute`: the wrapper writes the angle word `[valid ∨ g] tw` and the phase
word `[valid] pw` and restores its work wires. `flagLiftG_factorOK` and `flagLiftG_rotOK`: the
arithmetic hypotheses of the native factor (`FactorArithOK`) and of the native rotation
(`ArithOK`) for the decoders that are the decoder of the arithmetic on a valid pair and the
zero-entry value otherwise.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
  GateOptimalPrecision
open SparseHamiltonian.GeneralSparseAccess (cfgRun_reverse_cancel)
open GateOptimalBinary (cfgRun_map classical_map)
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)

/-! ### Word arithmetic and its accuracy -/

/-- **A reversible word arithmetic on input wires `I`**: a circuit of controlled NOT gates with at
most three controls on the inputs and `bT + bP + A` arithmetic wires that writes an angle word and
a phase word of the inputs, restoring its work wires. -/
structure WordArith (I : Type*) [DecidableEq I] (bT bP A : ℕ) where
  /-- The circuit. -/
  circ : List (Gate (I ⊕ AWr bT bP A))
  /-- The angle word. -/
  tw : Cfg I → Fin bT → Bool
  /-- The phase word. -/
  pw : Cfg I → Fin bP → Bool
  elem : ∀ g ∈ circ, g.cs.length ≤ 3
  classical : Classical circ
  compute : ∀ w : Cfg I, cfgRun circ (Sum.elim w (fun _ => false)) =
    Sum.elim w (Sum.elim (Sum.elim (tw w) (pw w)) (fun _ => false))

/-- **The accuracy of a factor arithmetic** (as in `GateOptimalPrecision.FactorArithOK`): for every
input either the decoded entry is below the threshold `ξ²/16` and the angle is zero, or `sin² α`
is within `ξ²` of its modulus and `e^{iφ}` within `ξ` of its phase. -/
def FactorAcc {I : Type*} (dec : Cfg I → ℂ) (ξ : ℝ) {bT bP : ℕ} (tw : Cfg I → Fin bT → Bool)
    (pw : Cfg I → Fin bP → Bool) : Prop :=
  ∀ w, (‖dec w‖ ≤ ξ ^ 2 / 16 ∧ alphaVal (tw w) = 0) ∨
    (|Real.sin (alphaVal (tw w)) ^ 2 - ‖dec w‖| ≤ ξ ^ 2 ∧
      ‖Complex.exp (phiVal (pw w) * Complex.I) - NativeSignedFactor.phase (dec w)‖ ≤ ξ)

/-- **The accuracy of a rotation arithmetic** (as in `GateNative.ArithOK`): the angle word within
`ζ` of `2 arctan |dec|` and, for a nonzero decoded value, the phase word within `ζ` of its
argument modulo `2π`. -/
def RotAcc {I : Type*} (dec : Cfg I → ℂ) (ζ : ℝ) {bT bP : ℕ} (tw : Cfg I → Fin bT → Bool)
    (pw : Cfg I → Fin bP → Bool) : Prop :=
  (∀ w, |thetaVal (tw w) - 2 * Real.arctan ‖dec w‖| ≤ ζ) ∧
    ∀ w, dec w ≠ 0 → ∃ m : ℤ, |phiVal (pw w) - Complex.arg (dec w) - 2 * Real.pi * m| ≤ ζ

theorem alphaVal_false (n : ℕ) : alphaVal (fun _ : Fin n => false) = 0 := by
  simp [alphaVal]

theorem thetaVal_false (n : ℕ) : thetaVal (fun _ : Fin n => false) = 0 := by
  simp [thetaVal]

theorem phiVal_false (n : ℕ) : phiVal (fun _ : Fin n => false) = 0 := by
  simp [phiVal]

/-! ### The wires of the wrapper -/

section Wires

variable {B I : Type*} {k bT bP A : ℕ}

/-- The wires of the wrapper: the base wires, the two words and the work of the wrapper (the
scratch of the arithmetic, the validity and the angle flag). -/
abbrev WWG (B : Type*) (k bT bP A : ℕ) := B ⊕ AWr bT bP (flagA k bT bP A + 1)

/-- The inputs and the scratch of the arithmetic inside the wrapper. -/
def gA (ιI : I → B) : I ⊕ AWr bT bP A → WWG B k bT bP A :=
  Sum.elim (fun i => Sum.inl (ιI i)) (fun a => Sum.inr (Sum.inr (Fin.castSucc (sAW (k := k) a))))

/-- The edge word and the work of the validity inside the wrapper. -/
def gF (ιE : EW (k + 1) → B) : WF k → WWG B k bT bP A :=
  Sum.elim (fun e => Sum.inl (ιE e))
    (fun f => Sum.inr (Sum.inr (Fin.castSucc (sFW (bT := bT) (bP := bP) (A := A) f))))

/-- The angle flag. -/
abbrev gFT : WWG B k bT bP A := Sum.inr (Sum.inr (Fin.last _))

/-- The scratch angle word. -/
abbrev srcT (ιI : I → B) (j : Fin bT) : WWG B k bT bP A := gA (A := A) ιI (Sum.inr (Sum.inl (Sum.inl j)))

/-- The scratch phase word. -/
abbrev srcP (ιI : I → B) (j : Fin bP) : WWG B k bT bP A := gA (A := A) ιI (Sum.inr (Sum.inl (Sum.inr j)))

/-- The angle word. -/
abbrev tgtT (j : Fin bT) : WWG B k bT bP A := Sum.inr (Sum.inl (Sum.inl j))

/-- The phase word. -/
abbrev tgtP (j : Fin bP) : WWG B k bT bP A := Sum.inr (Sum.inl (Sum.inr j))

theorem gA_injective {ιI : I → B} (hI : Function.Injective ιI) :
    Function.Injective (gA (k := k) (bT := bT) (bP := bP) (A := A) ιI) := by
  rintro (i | a) (i' | a') h <;> simp only [gA, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (hI (Sum.inl_injective h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (sAW_injective (Fin.castSucc_injective _
      (Sum.inr_injective (Sum.inr_injective h))))

theorem gF_injective {ιE : EW (k + 1) → B} (hE : Function.Injective ιE) :
    Function.Injective (gF (bT := bT) (bP := bP) (A := A) ιE) := by
  rintro (e | f) (e' | f') h <;> simp only [gF, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (hE (Sum.inl_injective h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (sFW_injective (Fin.castSucc_injective _
      (Sum.inr_injective (Sum.inr_injective h))))

theorem gA_ne_gF {ιE : EW (k + 1) → B} {ιI : I → B} (hEI : ∀ e i, ιE e ≠ ιI i)
    (u : I ⊕ AWr bT bP A) (w : WF k) : gA (k := k) ιI u ≠ gF ιE w := by
  rcases u with i | a <;> rcases w with e | f <;> simp only [gA, gF, Sum.elim_inl, Sum.elim_inr]
  · exact fun h => hEI e i (Sum.inl_injective h).symm
  · exact fun h => by cases h
  · exact fun h => by cases h
  · exact fun h => sAW_ne_sFW a f (Fin.castSucc_injective _
      (Sum.inr_injective (Sum.inr_injective h)))

theorem gA_ne_gFT {ιI : I → B} (u : I ⊕ AWr bT bP A) :
    gA (k := k) ιI u ≠ (gFT : WWG B k bT bP A) := by
  rcases u with i | a <;> simp only [gA, gFT, Sum.elim_inl, Sum.elim_inr]
  · exact fun h => by cases h
  · intro h
    have := congrArg Fin.val (Sum.inr_injective (Sum.inr_injective h))
    simp only [Fin.val_castSucc, Fin.val_last] at this
    exact absurd this (Fin.is_lt _).ne

theorem gF_ne_gFT {ιE : EW (k + 1) → B} (w : WF k) :
    gF (bT := bT) (bP := bP) (A := A) ιE w ≠ (gFT : WWG B k bT bP A) := by
  rcases w with e | f <;> simp only [gF, gFT, Sum.elim_inl, Sum.elim_inr]
  · exact fun h => by cases h
  · intro h
    have := congrArg Fin.val (Sum.inr_injective (Sum.inr_injective h))
    simp only [Fin.val_castSucc, Fin.val_last] at this
    exact absurd this (Fin.is_lt _).ne

theorem tgtT_ne_gA {ιI : I → B} (j : Fin bT) (u : I ⊕ AWr bT bP A) :
    (tgtT j : WWG B k bT bP A) ≠ gA ιI u := by
  rcases u with i | a <;> simp [tgtT, gA]

theorem tgtP_ne_gA {ιI : I → B} (j : Fin bP) (u : I ⊕ AWr bT bP A) :
    (tgtP j : WWG B k bT bP A) ≠ gA ιI u := by
  rcases u with i | a <;> simp [tgtP, gA]

theorem tgtT_ne_gF {ιE : EW (k + 1) → B} (j : Fin bT) (w : WF k) :
    (tgtT j : WWG B k bT bP A) ≠ gF ιE w := by
  rcases w with e | f <;> simp [tgtT, gF]

theorem tgtP_ne_gF {ιE : EW (k + 1) → B} (j : Fin bP) (w : WF k) :
    (tgtP j : WWG B k bT bP A) ≠ gF ιE w := by
  rcases w with e | f <;> simp [tgtP, gF]

theorem tgtT_ne_gFT (j : Fin bT) : (tgtT j : WWG B k bT bP A) ≠ gFT := by simp [tgtT, gFT]

theorem tgtP_ne_gFT (j : Fin bP) : (tgtP j : WWG B k bT bP A) ≠ gFT := by simp [tgtP, gFT]

theorem tgtT_injective : Function.Injective (tgtT (B := B) (k := k) (bT := bT) (bP := bP) (A := A)) :=
  fun _ _ h => Sum.inl_injective (Sum.inl_injective (Sum.inr_injective h))

theorem tgtP_injective : Function.Injective (tgtP (B := B) (k := k) (bT := bT) (bP := bP) (A := A)) :=
  fun _ _ h => Sum.inr_injective (Sum.inl_injective (Sum.inr_injective h))

theorem tgtT_ne_tgtP (i : Fin bT) (j : Fin bP) : (tgtT i : WWG B k bT bP A) ≠ tgtP j := by
  simp [tgtT, tgtP]

end Wires

/-! ### The wrapper -/

section Wrapper

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] {k bT bP A : ℕ}

/-- The optional input bit of the angle flag. -/
def gBit (ιI : I → B) (gT : Option I) (x : Cfg B) : Bool :=
  match gT with
  | none => false
  | some g => x (ιI g)

omit [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] in
theorem gBit_comp {B' : Type*} (ιI : I → B) (gT : Option I) (z : Cfg B') (x : Cfg B)
    (f : B → B') (h : ∀ i, z (f (ιI i)) = x (ιI i)) :
    gBit (fun i => f (ιI i)) gT z = gBit ιI gT x := by
  cases gT with
  | none => rfl
  | some g => exact h g

/-- The gates of the angle flag `valid ∨ [g]`. -/
def ftGates (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I) : List (Gate (WWG B k bT bP A)) :=
  match gT with
  | none => [⟨[(gF ιE WF.g₂, true)], gFT, pauliX⟩]
  | some g => [⟨[(gF ιE WF.g₂, true)], gFT, pauliX⟩,
      ⟨[(gF ιE WF.g₂, false), (Sum.inl (ιI g), true)], gFT, pauliX⟩]

/-- The copies of the scratch words: the angle word under the angle flag, the phase word under the
validity flag. -/
def copiesG (ιE : EW (k + 1) → B) (ιI : I → B) : List (Gate (WWG B k bT bP A)) :=
  ((Finset.univ : Finset (Fin bT)).toList.map (copyG gFT (srcT (A := A) ιI) tgtT)) ++
    ((Finset.univ : Finset (Fin bP)).toList.map (copyG (gF ιE WF.g₂) (srcP (A := A) ιI) tgtP))

/-- **The word arithmetic with the validity of the index pair** on the base wires `B`, with edge
wires `ιE`, input wires `ιI` and an optional input bit `gT` enabling the angle word on an invalid
pair. -/
def WordArith.flagLiftG (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I)
    (ar : WordArith I bT bP A) : Arith B where
  bT := bT
  bP := bP
  A := flagA k bT bP A + 1
  circ := (validC N).map (GateODE.Gate.map (gF ιE)) ++ ar.circ.map (GateODE.Gate.map (gA ιI)) ++
    ftGates ιE ιI gT ++ copiesG ιE ιI ++ (ftGates ιE ιI gT).reverse ++
    (ar.circ.map (GateODE.Gate.map (gA ιI))).reverse ++
    ((validC N).map (GateODE.Gate.map (gF ιE))).reverse
  tw := fun y => if (evalidW N (fun e => y (ιE e)) || gBit ιI gT y) then
    ar.tw (fun i => y (ιI i)) else fun _ => false
  pw := fun y => if evalidW N (fun e => y (ιE e)) then ar.pw (fun i => y (ιI i)) else fun _ => false

omit [Fintype B] [DecidableEq B] [Fintype I] in
@[simp] theorem WordArith.flagLiftG_bT (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B)
    (gT : Option I) (ar : WordArith I bT bP A) : (ar.flagLiftG N ιE ιI gT).bT = bT := rfl

omit [Fintype B] [DecidableEq B] [Fintype I] in
@[simp] theorem WordArith.flagLiftG_bP (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B)
    (gT : Option I) (ar : WordArith I bT bP A) : (ar.flagLiftG N ιE ιI gT).bP = bP := rfl

omit [Fintype B] [DecidableEq B] [Fintype I] in
@[simp] theorem WordArith.flagLiftG_A (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B)
    (gT : Option I) (ar : WordArith I bT bP A) :
    (ar.flagLiftG N ιE ιI gT).A = flagA k bT bP A + 1 := rfl

omit [Fintype B] [DecidableEq B] [Fintype I] in
/-- The angle word of the wrapper reads only the edge and the input wires. -/
theorem WordArith.flagLiftG_tw_congr (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I)
    (ar : WordArith I bT bP A) {y y' : Cfg B} (hE : ∀ e, y (ιE e) = y' (ιE e))
    (hI : ∀ i, y (ιI i) = y' (ιI i)) :
    (ar.flagLiftG N ιE ιI gT).tw y = (ar.flagLiftG N ιE ιI gT).tw y' := by
  have h1 : (fun e => y (ιE e)) = fun e => y' (ιE e) := funext hE
  have h2 : (fun i => y (ιI i)) = fun i => y' (ιI i) := funext hI
  have h3 : gBit ιI gT y = gBit ιI gT y' := by
    cases gT with
    | none => rfl
    | some g => exact hI g
  show (if (evalidW N (fun e => y (ιE e)) || gBit ιI gT y) then ar.tw (fun i => y (ιI i)) else
      fun _ => false) =
    (if (evalidW N (fun e => y' (ιE e)) || gBit ιI gT y') then ar.tw (fun i => y' (ιI i)) else
      fun _ => false)
  rw [h1, h2, h3]

omit [Fintype B] [DecidableEq B] [Fintype I] in
/-- The phase word of the wrapper reads only the edge and the input wires. -/
theorem WordArith.flagLiftG_pw_congr (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I)
    (ar : WordArith I bT bP A) {y y' : Cfg B} (hE : ∀ e, y (ιE e) = y' (ιE e))
    (hI : ∀ i, y (ιI i) = y' (ιI i)) :
    (ar.flagLiftG N ιE ιI gT).pw y = (ar.flagLiftG N ιE ιI gT).pw y' := by
  have h1 : (fun e => y (ιE e)) = fun e => y' (ιE e) := funext hE
  have h2 : (fun i => y (ιI i)) = fun i => y' (ιI i) := funext hI
  show (if evalidW N (fun e => y (ιE e)) then ar.pw (fun i => y (ιI i)) else fun _ => false) =
    (if evalidW N (fun e => y' (ιE e)) then ar.pw (fun i => y' (ιI i)) else fun _ => false)
  rw [h1, h2]

omit [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] in
theorem length_ftGates_le (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I) :
    (ftGates (bT := bT) (bP := bP) (A := A) ιE ιI gT).length ≤ 2 := by
  cases gT <;> simp [ftGates]

omit [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] in
theorem length_copiesG (ιE : EW (k + 1) → B) (ιI : I → B) :
    (copiesG (bT := bT) (bP := bP) (A := A) ιE ιI).length = bT + bP := by
  simp [copiesG]

omit [Fintype B] [DecidableEq B] [Fintype I] in
/-- **The gates of the wrapper**: twice the validity circuit, the arithmetic and the angle flag,
and the copies. -/
theorem WordArith.flagLiftG_length (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I)
    (ar : WordArith I bT bP A) :
    (ar.flagLiftG N ιE ιI gT).circ.length ≤
      2 * (validC (k := k) N).length + 2 * ar.circ.length + 4 + (bT + bP) := by
  have h := length_ftGates_le (bT := bT) (bP := bP) (A := A) ιE ιI gT
  simp only [WordArith.flagLiftG, List.length_append, List.length_reverse, List.length_map,
    length_copiesG]
  omega

omit [Fintype B] [Fintype I] [DecidableEq I] in
theorem cfgRun_ftGates (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I)
    (z : Cfg (WWG B k bT bP A)) :
    cfgRun (ftGates ιE ιI gT) z = Function.update z gFT
      (z gFT ^^ (z (gF ιE WF.g₂) || gBit (fun i => Sum.inl (ιI i) : I → WWG B k bT bP A) gT z)) := by
  have hg2 : (gF (bT := bT) (bP := bP) (A := A) ιE WF.g₂ : WWG B k bT bP A) ≠ gFT :=
    gF_ne_gFT _
  cases gT with
  | none =>
      simp only [ftGates, cfgRun, flipCfg_update', ctrlOK_cons, ctrlOK_nil, gBit, Bool.or_false]
      congr 2
      cases z (gF ιE WF.g₂) <;> rfl
  | some g =>
      have hgi : (Sum.inl (ιI g) : WWG B k bT bP A) ≠ gFT := by simp [gFT]
      simp only [ftGates, cfgRun, flipCfg_update', ctrlOK_cons, ctrlOK_nil, gBit,
        Function.update_of_ne hg2, Function.update_of_ne hgi, Function.update_self,
        Function.update_idem]
      congr 1
      cases z (gF ιE WF.g₂) <;> cases z (Sum.inl (ιI g)) <;> cases z gFT <;> rfl

omit [Fintype B] [Fintype I] [DecidableEq I] in
theorem cfgRun_ftGates_reverse (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I)
    (z : Cfg (WWG B k bT bP A)) :
    cfgRun (ftGates ιE ιI gT).reverse z = Function.update z gFT
      (z gFT ^^ (z (gF ιE WF.g₂) || gBit (fun i => Sum.inl (ιI i) : I → WWG B k bT bP A) gT z)) := by
  have hg2 : (gF (bT := bT) (bP := bP) (A := A) ιE WF.g₂ : WWG B k bT bP A) ≠ gFT :=
    gF_ne_gFT _
  cases gT with
  | none =>
      simp only [ftGates, List.reverse_cons, List.reverse_nil, List.nil_append, cfgRun,
        flipCfg_update', ctrlOK_cons, ctrlOK_nil, gBit, Bool.or_false]
      congr 2
      cases z (gF ιE WF.g₂) <;> rfl
  | some g =>
      have hgi : (Sum.inl (ιI g) : WWG B k bT bP A) ≠ gFT := by simp [gFT]
      simp only [ftGates, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, cfgRun, flipCfg_update', ctrlOK_cons, ctrlOK_nil, gBit,
        Function.update_of_ne hg2, Function.update_self, Function.update_idem]
      congr 1
      cases z (gF ιE WF.g₂) <;> cases z (Sum.inl (ιI g)) <;> cases z gFT <;> rfl

omit [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] in
theorem classical_ftGates (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I) :
    Classical (ftGates (bT := bT) (bP := bP) (A := A) ιE ιI gT) := by
  have hg2 : (gF (bT := bT) (bP := bP) (A := A) ιE WF.g₂ : WWG B k bT bP A) ≠ gFT :=
    gF_ne_gFT _
  intro g hg
  cases gT with
  | none =>
      simp only [ftGates, List.mem_singleton] at hg
      subst hg
      refine ⟨rfl, fun c hc => ?_⟩
      simp only [List.mem_singleton] at hc
      subst hc
      exact hg2
  | some i =>
      simp only [ftGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · refine ⟨rfl, fun c hc => ?_⟩
        simp only [List.mem_singleton] at hc
        subst hc
        exact hg2
      · refine ⟨rfl, fun c hc => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact hg2
        · simp [gFT]

omit [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] in
theorem gateOK_ftGates (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I) :
    ∀ g ∈ ftGates (bT := bT) (bP := bP) (A := A) ιE ιI gT, g.cs.length ≤ 3 := by
  intro g hg
  cases gT with
  | none =>
      simp only [ftGates, List.mem_singleton] at hg
      subst hg
      simp
  | some i =>
      simp only [ftGates, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> simp

omit [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] in
theorem classical_copiesG (ιE : EW (k + 1) → B) (ιI : I → B) :
    Classical (copiesG (bT := bT) (bP := bP) (A := A) ιE ιI) := by
  refine classical_append ?_ ?_
  · exact classical_copies _ _ _ _ (fun j _ => tgtT_ne_gFT j)
      (fun j _ => tgtT_ne_gA j _)
  · exact classical_copies _ _ _ _ (fun j _ => tgtP_ne_gF j _)
      (fun j _ => tgtP_ne_gA j _)

omit [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I] in
theorem gateOK_copiesG (ιE : EW (k + 1) → B) (ιI : I → B) :
    ∀ g ∈ copiesG (bT := bT) (bP := bP) (A := A) ιE ιI, g.cs.length ≤ 3 := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    simp [copyG]
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    simp [copyG]

omit [Fintype B] [DecidableEq B] [Fintype I] in
/-- The gates of the wrapper have at most three controls. -/
theorem WordArith.flagLiftG_elem (N : ℕ) (ιE : EW (k + 1) → B) (ιI : I → B) (gT : Option I)
    (ar : WordArith I bT bP A) : ∀ g ∈ (ar.flagLiftG N ιE ιI gT).circ, g.cs.length ≤ 3 := by
  intro g hg
  change g ∈ (validC (k := k) N).map (GateODE.Gate.map (gF (bT := bT) (bP := bP) (A := A) ιE)) ++
      ar.circ.map (GateODE.Gate.map (gA (k := k) ιI)) ++
      ftGates ιE ιI gT ++ copiesG ιE ιI ++ (ftGates ιE ιI gT).reverse ++
      (ar.circ.map (GateODE.Gate.map (gA (k := k) ιI))).reverse ++
      ((validC (k := k) N).map (GateODE.Gate.map (gF (bT := bT) (bP := bP) (A := A) ιE))).reverse
    at hg
  rcases List.mem_append.mp hg with h | h
  · rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h
              simpa [GateODE.Gate.map] using gateOK_validC N g' hg'
            · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 h
              simpa [GateODE.Gate.map] using ar.elem g' hg'
          · exact gateOK_ftGates ιE ιI gT g h
        · exact gateOK_copiesG ιE ιI g h
      · exact gateOK_ftGates ιE ιI gT g (List.mem_reverse.mp h)
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 (List.mem_reverse.mp h)
      simpa [GateODE.Gate.map] using ar.elem g' hg'
  · obtain ⟨g', hg', rfl⟩ := List.mem_map.1 (List.mem_reverse.mp h)
    simpa [GateODE.Gate.map] using gateOK_validC N g' hg'

omit [Fintype B] [DecidableEq B] [Fintype I] in
/-- The wrapper is a classical circuit. -/
theorem WordArith.flagLiftG_classical (N : ℕ) {ιE : EW (k + 1) → B}
    (hE : Function.Injective ιE) {ιI : I → B} (hI : Function.Injective ιI) (gT : Option I)
    (ar : WordArith I bT bP A) : Classical (ar.flagLiftG N ιE ιI gT).circ := by
  have hF : Classical ((validC (k := k) N).map (GateODE.Gate.map
      (gF (bT := bT) (bP := bP) (A := A) ιE))) :=
    classical_map (gF_injective hE) (classical_validC N)
  have hA' : Classical (ar.circ.map (GateODE.Gate.map (gA (k := k) ιI))) :=
    classical_map (gA_injective hI) ar.classical
  have hT := classical_ftGates (bT := bT) (bP := bP) (A := A) ιE ιI gT
  have hC := classical_copiesG (bT := bT) (bP := bP) (A := A) ιE ιI
  exact classical_append (classical_append (classical_append (classical_append (classical_append
    (classical_append hF hA') hT) hC) (classical_reverse hT)) (classical_reverse hA'))
    (classical_reverse hF)

omit [Fintype B] in
/-- **The wrapper on clean work wires**: it writes the angle word `[valid ∨ g] tw` and the phase
word `[valid] pw` of the inputs and restores its work wires. -/
theorem WordArith.flagLiftG_compute (N : ℕ) (hN : N < 2 ^ (k + 1)) {ιE : EW (k + 1) → B}
    (hE : Function.Injective ιE) {ιI : I → B} (hI : Function.Injective ιI)
    (hEI : ∀ e i, ιE e ≠ ιI i) (gT : Option I) (ar : WordArith I bT bP A) (x : Cfg B) :
    cfgRun (ar.flagLiftG N ιE ιI gT).circ (Sum.elim x (fun _ => false)) =
      Sum.elim x ((ar.flagLiftG N ιE ιI gT).out x) := by
  set fF := gF (bT := bT) (bP := bP) (A := A) ιE with hfF
  set fA := gA (k := k) (bT := bT) (bP := bP) (A := A) ιI with hfA
  have hFi : Function.Injective fF := gF_injective hE
  have hAi : Function.Injective fA := gA_injective hI
  set cF := (validC (k := k) N).map (GateODE.Gate.map fF) with hcF
  set cA := ar.circ.map (GateODE.Gate.map fA) with hcA
  set cT := ftGates (bT := bT) (bP := bP) (A := A) ιE ιI gT with hcT
  set cC := copiesG (bT := bT) (bP := bP) (A := A) ιE ιI with hcC
  set z0 : Cfg (WWG B k bT bP A) := Sum.elim x (fun _ => false) with hz0
  set val := evalidW N (fun e => x (ιE e)) with hval
  set gb := gBit ιI gT x with hgb
  change cfgRun (cF ++ cA ++ cT ++ cC ++ cT.reverse ++ cA.reverse ++ cF.reverse) z0 =
    Sum.elim x (Sum.elim (Sum.elim (if (val || gb) then ar.tw (fun i => x (ιI i)) else
      fun _ => false) (if val then ar.pw (fun i => x (ιI i)) else fun _ => false))
      (fun _ => false))
  rw [cfgRun_append, cfgRun_append, cfgRun_append, cfgRun_append, cfgRun_append, cfgRun_append]
  set z1 := cfgRun cF z0 with hz1
  set z2 := cfgRun cA z1 with hz2
  set z3 := cfgRun cT z2 with hz3
  set z4 := cfgRun cC z3 with hz4
  set z5 := cfgRun cT.reverse z4 with hz5
  set z6 := cfgRun cA.reverse z5 with hz6
  -- the validity run
  set zF := cfgRun (validC (k := k) N) (fun w => z0 (fF w)) with hzF
  obtain ⟨hflag, -⟩ := cfgRun_validC (k := k) hN (fun w => z0 (fF w)) (fun f => rfl)
  have hfl : zF WF.g₂ = val := by
    rw [hzF, hflag]
    rfl
  have h1F : ∀ w, z1 (fF w) = zF w := fun w => cfgRun_map_apply hFi _ _ w
  have h1o : ∀ u, (∀ w, fF w ≠ u) → z1 u = z0 u := fun u hu => cfgRun_map_out hFi _ _ u hu
  -- the arithmetic run
  have hz1A : (fun a => z1 (fA a)) = Sum.elim (fun i => x (ιI i)) (fun _ => false) := by
    funext a
    rw [h1o _ (fun w h => gA_ne_gF hEI a w h.symm)]
    rcases a with i | a <;> rfl
  have h2A : ∀ a, z2 (fA a) = Sum.elim (fun i => x (ιI i))
      (Sum.elim (Sum.elim (ar.tw (fun i => x (ιI i))) (ar.pw (fun i => x (ιI i))))
        (fun _ => false)) a := by
    intro a
    rw [hz2, hcA, cfgRun_map_apply hAi, hz1A, ar.compute]
  have h2o : ∀ u, (∀ a, fA a ≠ u) → z2 u = z1 u := fun u hu => cfgRun_map_out hAi _ _ u hu
  have h2g : z2 (gF (bT := bT) (bP := bP) (A := A) ιE WF.g₂) = val := by
    rw [h2o _ (fun a h => gA_ne_gF hEI a WF.g₂ h), h1F, hfl]
  have h2b : gBit (fun i => Sum.inl (ιI i) : I → WWG B k bT bP A) gT z2 = gb :=
    gBit_comp ιI gT z2 x Sum.inl (fun i => h2A (Sum.inl i))
  have h2T : z2 gFT = false := by
    rw [h2o _ (fun a => gA_ne_gFT a), h1o _ (fun w => gF_ne_gFT w)]
    rfl
  -- the angle flag
  have h3 : z3 = Function.update z2 gFT (val || gb) := by
    rw [hz3, hcT, cfgRun_ftGates, h2g, h2b, h2T, Bool.false_xor]
  have h3o : ∀ u, u ≠ gFT → z3 u = z2 u := fun u hu => by
    rw [h3, Function.update_of_ne hu]
  have h3T : z3 gFT = (val || gb) := by rw [h3, Function.update_self]
  -- the copies
  have hLT := (Finset.univ : Finset (Fin bT)).nodup_toList
  have hLP := (Finset.univ : Finset (Fin bP)).nodup_toList
  obtain ⟨h3'T, h3'o⟩ := cfgRun_copies (gFT : WWG B k bT bP A) (srcT (A := A) ιI) tgtT _ hLT
    (fun i _ j _ h => tgtT_injective h) (fun j _ => tgtT_ne_gFT j)
    (fun i _ j _ => tgtT_ne_gA i _) z3
  obtain ⟨h4P, h4o⟩ := cfgRun_copies (fF WF.g₂) (srcP (A := A) ιI) tgtP _ hLP
    (fun i _ j _ h => tgtP_injective h) (fun j _ => tgtP_ne_gF j _)
    (fun i _ j _ => tgtP_ne_gA i _)
    (cfgRun ((Finset.univ : Finset (Fin bT)).toList.map
      (copyG (gFT : WWG B k bT bP A) (srcT (A := A) ιI) tgtT)) z3)
  have hz4e : z4 = cfgRun ((Finset.univ : Finset (Fin bP)).toList.map
      (copyG (fF WF.g₂) (srcP (A := A) ιI) tgtP))
      (cfgRun ((Finset.univ : Finset (Fin bT)).toList.map
        (copyG (gFT : WWG B k bT bP A) (srcT (A := A) ιI) tgtT)) z3) := by
    rw [hz4]
    exact cfgRun_append _ _ _
  have h4o' : ∀ u, (∀ j : Fin bT, tgtT j ≠ u) → (∀ j : Fin bP, tgtP j ≠ u) → z4 u = z3 u :=
    fun u hT hP => by
      rw [hz4e, h4o u (fun j _ => hP j), h3'o u (fun j _ => hT j)]
  -- the inverse angle flag
  have h4g : z4 (gF (bT := bT) (bP := bP) (A := A) ιE WF.g₂) = val := by
    rw [h4o' _ (fun j => tgtT_ne_gF j _) (fun j => tgtP_ne_gF j _),
      h3o _ (gF_ne_gFT _), h2g]
  have h4b : gBit (fun i => Sum.inl (ιI i) : I → WWG B k bT bP A) gT z4 = gb :=
    gBit_comp ιI gT z4 x Sum.inl (fun i => by
      show z4 (fA (Sum.inl i)) = _
      rw [h4o' _ (fun j => tgtT_ne_gA j (Sum.inl i)) (fun j => tgtP_ne_gA j (Sum.inl i)),
        h3o _ (gA_ne_gFT (Sum.inl i))]
      exact h2A (Sum.inl i))
  have h4T : z4 gFT = (val || gb) := by
    rw [h4o' _ (fun j => tgtT_ne_gFT j) (fun j => tgtP_ne_gFT j), h3T]
  have h5 : z5 = Function.update z4 gFT false := by
    rw [hz5, hcT, cfgRun_ftGates_reverse, h4g, h4b, h4T, Bool.xor_self]
  have h5o : ∀ u, u ≠ gFT → z5 u = z4 u := fun u hu => by
    rw [h5, Function.update_of_ne hu]
  -- the inverse arithmetic
  have hrevA : cA.reverse = ar.circ.reverse.map (GateODE.Gate.map fA) := by
    rw [hcA, List.map_reverse]
  have hz5A : (fun a => z5 (fA a)) = cfgRun ar.circ (Sum.elim (fun i => x (ιI i))
      (fun _ => false)) := by
    funext a
    rw [h5o _ (gA_ne_gFT a), h4o' _ (fun j => tgtT_ne_gA j a) (fun j => tgtP_ne_gA j a),
      h3o _ (gA_ne_gFT a), h2A, ar.compute]
  have h6A : ∀ a, z6 (fA a) = Sum.elim (fun i => x (ιI i)) (fun _ => false) a := by
    intro a
    rw [hz6, hrevA, cfgRun_map_apply hAi, hz5A, cfgRun_reverse_cancel _ ar.classical]
  have h6o : ∀ u, (∀ a, fA a ≠ u) → z6 u = z5 u := fun u hu => by
    rw [hz6, hrevA]
    exact cfgRun_map_out hAi _ _ u hu
  -- the inverse validity
  have hrevF : cF.reverse = (validC (k := k) N).reverse.map (GateODE.Gate.map fF) := by
    rw [hcF, List.map_reverse]
  have hz6F : (fun w => z6 (fF w)) = zF := by
    funext w
    rw [h6o _ (fun a h => gA_ne_gF hEI a w h), h5o _ (gF_ne_gFT w),
      h4o' _ (fun j => tgtT_ne_gF j w) (fun j => tgtP_ne_gF j w), h3o _ (gF_ne_gFT w),
      h2o _ (fun a h => gA_ne_gF hEI a w h), h1F]
  have h7F : ∀ w, cfgRun cF.reverse z6 (fF w) = z0 (fF w) := by
    intro w
    rw [hrevF, cfgRun_map_apply hFi, hz6F, hzF, cfgRun_reverse_cancel _ (classical_validC N)]
  have h7o : ∀ u, (∀ w, fF w ≠ u) → cfgRun cF.reverse z6 u = z6 u := fun u hu => by
    rw [hrevF]
    exact cfgRun_map_out hFi _ _ u hu
  -- the final configuration
  funext u
  by_cases huF : ∃ w, fF w = u
  · obtain ⟨w, rfl⟩ := huF
    rw [h7F]
    rcases w with e | f <;> rfl
  push Not at huF
  by_cases huA : ∃ a, fA a = u
  · obtain ⟨a, rfl⟩ := huA
    rw [h7o _ huF, h6A]
    rcases a with i | a <;> rfl
  push Not at huA
  rw [h7o _ huF, h6o _ huA]
  by_cases huT : u = gFT
  · subst huT
    rw [h5, Function.update_self]
    rfl
  rw [h5o _ huT]
  by_cases huTT : ∃ j, tgtT (B := B) (k := k) (bP := bP) (A := A) j = u
  · obtain ⟨j, rfl⟩ := huTT
    rw [hz4e, h4o _ (fun j' _ => (tgtT_ne_tgtP j j').symm),
      h3'T j (Finset.mem_toList.mpr (Finset.mem_univ j)), h3T]
    have e1 : z3 (srcT (A := A) ιI j) = ar.tw (fun i => x (ιI i)) j := by
      rw [h3o _ (gA_ne_gFT _)]
      exact h2A (Sum.inr (Sum.inl (Sum.inl j)))
    have e2 : z3 (tgtT j) = false := by
      rw [h3o _ (tgtT_ne_gFT j), h2o _ (fun a h => tgtT_ne_gA j a h.symm),
        h1o _ (fun w h => tgtT_ne_gF j w h.symm)]
      rfl
    rw [e1, e2, Bool.false_xor]
    change _ = (if (val || gb) then ar.tw (fun i => x (ιI i)) else fun _ => false) j
    by_cases hv : (val || gb) = true
    · rw [if_pos hv, hv, Bool.true_and]
    · rw [if_neg hv, Bool.eq_false_iff.mpr hv, Bool.false_and]
  push Not at huTT
  by_cases huTP : ∃ j, tgtP (B := B) (k := k) (bT := bT) (A := A) j = u
  · obtain ⟨j, rfl⟩ := huTP
    rw [hz4e, h4P j (Finset.mem_toList.mpr (Finset.mem_univ j)),
      h3'o _ (fun j' _ => tgtT_ne_tgtP j' j), h3'o _ (fun j' _ => tgtT_ne_gF j' WF.g₂),
      h3'o _ (fun j' _ => tgtT_ne_gA j' _)]
    have e1 : z3 (srcP (A := A) ιI j) = ar.pw (fun i => x (ιI i)) j := by
      rw [h3o _ (gA_ne_gFT _)]
      exact h2A (Sum.inr (Sum.inl (Sum.inr j)))
    have e2 : z3 (tgtP j) = false := by
      rw [h3o _ (tgtP_ne_gFT j), h2o _ (fun a h => tgtP_ne_gA j a h.symm),
        h1o _ (fun w h => tgtP_ne_gF j w h.symm)]
      rfl
    have e3 : z3 (fF WF.g₂) = val := by
      rw [h3o _ (gF_ne_gFT _)]
      exact h2g
    rw [e1, e2, e3, Bool.false_xor]
    change _ = (if val then ar.pw (fun i => x (ιI i)) else fun _ => false) j
    by_cases hv : val = true
    · rw [if_pos hv, hv, Bool.true_and]
    · rw [if_neg hv, Bool.eq_false_iff.mpr hv, Bool.false_and]
  push Not at huTP
  rw [h4o' _ huTT huTP, h3o _ huT, h2o _ huA, h1o _ huF]
  rcases u with p | ((j | j) | i)
  · rfl
  · exact absurd rfl (huTT j)
  · exact absurd rfl (huTP j)
  · rfl

end Wrapper

/-! ### The arithmetic hypotheses of the native operations -/

section Hyp

variable {I : Type*} [Fintype I] [DecidableEq I] {k bT bP A : ℕ}

/-- **The factor arithmetic hypothesis for a decoder with the validity of the index pair**: for a
native factor whose decoded entry is the decoder `dec` of the inputs on a valid pair and zero
otherwise, and whose arithmetic is the wrapper of a word arithmetic of accuracy `ξ` for `dec`
(without the optional input bit), `FactorArithOK`. -/
theorem flagLiftG_factorOK {PR Z Y J : Type*} [Fintype PR] [DecidableEq PR] [Fintype Z]
    [DecidableEq Z] (N : ℕ) (hN : N < 2 ^ (k + 1)) {ιE : EW (k + 1) → NB Empty PR Z}
    (hE : Function.Injective ιE) {ιI : I → NB Empty PR Z} (hI : Function.Injective ιI)
    (hEI : ∀ e i, ιE e ≠ ιI i) {decI : Cfg I → ℂ} {ξ : ℝ} (ar : WordArith I bT bP A)
    (hacc : FactorAcc decI ξ ar.tw ar.pw) (W : List (NInstr (NB Empty PR Z) Y J))
    (loc : Fin 3 ↪ PR) (dec : Cfg (NB Empty PR Z) → ℂ)
    (hdec : ∀ y, dec y = if evalidW N (fun e => y (ιE e)) then decI (fun i => y (ιI i)) else 0)
    (hlocE : ∀ i e, (Sum.inl (Sum.inr (loc i)) : NB Empty PR Z) ≠ ιE e)
    (hlocI : ∀ i j, (Sum.inl (Sum.inr (loc i)) : NB Empty PR Z) ≠ ιI j) :
    FactorArithOK (⟨W, loc, dec, (ar.flagLiftG N ιE ιI none).circ,
      (ar.flagLiftG N ιE ιI none).tw, (ar.flagLiftG N ιE ιI none).pw⟩ :
        FactorOp PR Z Y J bT bP (flagA k bT bP A + 1)) ξ where
  elem g hg := ar.flagLiftG_elem N ιE ιI none g hg
  classical := ar.flagLiftG_classical N hE hI none
  compute x := ar.flagLiftG_compute N hN hE hI hEI none x
  tw_indep x c := ar.flagLiftG_tw_congr N ιE ιI none
    (fun e => overwrite_apply_out _ _ _ _ (fun i => hlocE i e))
    (fun j => overwrite_apply_out _ _ _ _ (fun i => hlocI i j))
  pw_indep x c := ar.flagLiftG_pw_congr N ιE ιI none
    (fun e => overwrite_apply_out _ _ _ _ (fun i => hlocE i e))
    (fun j => overwrite_apply_out _ _ _ _ (fun i => hlocI i j))
  acc x := by
    show (‖dec x‖ ≤ ξ ^ 2 / 16 ∧ alphaVal ((ar.flagLiftG N ιE ιI none).tw x) = 0) ∨
      (|Real.sin (alphaVal ((ar.flagLiftG N ιE ιI none).tw x)) ^ 2 - ‖dec x‖| ≤ ξ ^ 2 ∧
        ‖Complex.exp (phiVal ((ar.flagLiftG N ιE ιI none).pw x) * Complex.I) -
          NativeSignedFactor.phase (dec x)‖ ≤ ξ)
    rw [hdec]
    by_cases hv : evalidW N (fun e => x (ιE e)) = true
    · have h1 : (ar.flagLiftG N ιE ιI none).tw x = ar.tw (fun i => x (ιI i)) := by
        simp [WordArith.flagLiftG, gBit, hv]
      have h2 : (ar.flagLiftG N ιE ιI none).pw x = ar.pw (fun i => x (ιI i)) := by
        simp [WordArith.flagLiftG, hv]
      rw [h1, h2, if_pos hv]
      exact hacc _
    · have h1 : (ar.flagLiftG N ιE ιI none).tw x = fun _ => false := by
        simp [WordArith.flagLiftG, gBit, hv]
      rw [h1, if_neg hv, norm_zero]
      left
      exact ⟨by positivity, alphaVal_false bT⟩

/-- **The rotation arithmetic hypothesis for a decoder with the validity of the index pair**: for
a native rotation whose decoded value is the decoder `decI` of the inputs on a valid pair and a
zero-entry value `dec0` otherwise, and whose arithmetic is the wrapper of a word arithmetic of
accuracy `ζ` for `decI` with the optional input bit `g`: if `dec0` has the modulus of `decI` when
`g` is set, vanishes when `g` is clear and has argument zero when nonzero, `ArithOK`. -/
theorem flagLiftG_rotOK {Bw : Type*} [Fintype Bw] [DecidableEq Bw] (N : ℕ)
    (hN : N < 2 ^ (k + 1)) {ιE : EW (k + 1) → Bw} (hE : Function.Injective ιE) {ιI : I → Bw}
    (hI : Function.Injective ιI) (hEI : ∀ e i, ιE e ≠ ιI i) (g : I) {decI dec0 : Cfg I → ℂ}
    {ζ : ℝ} (ar : WordArith I bT bP A) (hacc : RotAcc decI ζ ar.tw ar.pw) (o : Bw)
    (hoE : ∀ e, ιE e ≠ o) (hoI : ∀ i, ιI i ≠ o) (dec : Cfg Bw → ℂ)
    (hdec : ∀ y, dec y = if evalidW N (fun e => y (ιE e)) then decI (fun i => y (ιI i))
      else dec0 (fun i => y (ιI i)))
    (h0g : ∀ w, w g = true → ‖dec0 w‖ = ‖decI w‖) (h0ng : ∀ w, w g = false → dec0 w = 0)
    (h0arg : ∀ w, dec0 w ≠ 0 → Complex.arg (dec0 w) = 0) :
    ArithOK (ar.flagLiftG N ιE ιI (some g)) o dec ζ where
  elem := ar.flagLiftG_elem N ιE ιI (some g)
  classical := ar.flagLiftG_classical N hE hI (some g)
  compute x := ar.flagLiftG_compute N hN hE hI hEI (some g) x
  tw_indep x v := ar.flagLiftG_tw_congr N ιE ιI (some g)
    (fun e => Function.update_of_ne (hoE e) _ _) (fun i => Function.update_of_ne (hoI i) _ _)
  pw_indep x v := ar.flagLiftG_pw_congr N ιE ιI (some g)
    (fun e => Function.update_of_ne (hoE e) _ _) (fun i => Function.update_of_ne (hoI i) _ _)
  theta x := by
    have hζ : 0 ≤ ζ := (abs_nonneg _).trans (hacc.1 (fun _ => false))
    rw [hdec]
    by_cases hv : evalidW N (fun e => x (ιE e)) = true
    · have h1 : (ar.flagLiftG N ιE ιI (some g)).tw x = ar.tw (fun i => x (ιI i)) := by
        simp [WordArith.flagLiftG, gBit, hv]
      rw [h1, if_pos hv]
      exact hacc.1 _
    · by_cases hg : x (ιI g) = true
      · have h1 : (ar.flagLiftG N ιE ιI (some g)).tw x = ar.tw (fun i => x (ιI i)) := by
          simp [WordArith.flagLiftG, gBit, hg]
        rw [h1, if_neg hv, h0g (fun i => x (ιI i)) hg]
        exact hacc.1 _
      · have h1 : (ar.flagLiftG N ιE ιI (some g)).tw x = fun _ => false := by
          simp [WordArith.flagLiftG, gBit, hv, hg]
        rw [h1, if_neg hv, h0ng (fun i => x (ιI i)) (by simpa using hg), thetaVal_false,
          norm_zero, Real.arctan_zero, mul_zero, sub_zero, abs_zero]
        exact hζ
  phi x hx := by
    have hζ : 0 ≤ ζ := (abs_nonneg _).trans (hacc.1 (fun _ => false))
    rw [hdec] at hx ⊢
    by_cases hv : evalidW N (fun e => x (ιE e)) = true
    · have h2 : (ar.flagLiftG N ιE ιI (some g)).pw x = ar.pw (fun i => x (ιI i)) := by
        simp [WordArith.flagLiftG, hv]
      rw [if_pos hv] at hx ⊢
      rw [h2]
      exact hacc.2 _ hx
    · have h2 : (ar.flagLiftG N ιE ιI (some g)).pw x = fun _ => false := by
        simp [WordArith.flagLiftG, hv]
      rw [if_neg hv] at hx ⊢
      rw [h2]
      refine ⟨0, ?_⟩
      rw [phiVal_false, h0arg _ hx]
      simpa using hζ

end Hyp

end

end SparseHamiltonian.GeneralDecoder
