import GateOptimalPrecision.LocalGates

/-!
# The native factor

The factor `U_B` of the signed factorisation has the native form of the paragraph "Sparse
preparation and the joint private operation" of Section `gate:sec:native`: "We compute the value
word while retaining the entry indices, perform the local operation on its three separate qubits,
and uncompute the value." In query-free coordinates a public compute circuit `W` of elementary gates
and primitive calls writes the entry data into clean scratch wires, the stable signed factor `U(c)`
of the paragraph "A stable constant-dimensional signed factor" of Section `gate:sec:native` (`uMat`)
acts on the flag, orientation and sign qubits for the decoded entry `c` (a public function of the
private register and the scratch), and `W†` uncomputes.

**Wires** (`PWr Empty PR Z bT bP A`, as for the baseline private operation): an unused enable
wire, the private register `PR` (ancillas and system), the scratch `Z`, the angle word (`bT`
bits), the phase word (`bP` bits) and `A` arithmetic work wires.

**Hypotheses.**

* Public (`FactorOp.Public`): the compute circuit is valid, the decoder does not read the three
  local qubits, and `‖c‖ ≤ 1`.
* Arithmetic (`FactorArithOK`): the reversible arithmetic (controlled NOT gates with at most three
  controls) writes the angle word `α̃` and the phase word `φ̃` on clean arithmetic wires,
  independently of the three local qubits, and restores its work wires; for every configuration
  either `‖c‖ ≤ ξ²/16` and `α(α̃) = 0` (the threshold), or `|sin² α(α̃) - ‖c‖| ≤ ξ²` and
  `|e^{iφ(φ̃)} - c/|c|| ≤ ξ` (`alphaVal`, `phiVal`).
* Instance (`FactorNativeOK`): `W† U(c) W` acts as the factor `U_B` on clean scratch.

**Implementation** (`factorMacro`): `W`, the arithmetic, the local factor gates of `LocalGates`
(`2 b_P + b_T + 4` elementary gates), the inverse arithmetic and `W†`; no enable wire is used.
**Error** (`factorMacro_approx`): on clean scratch and arithmetic wires it is within `3ξ` of `U_B`
in the full-output convention; its literal inverse is within `3ξ` of `U_B†`
(`factorMacro_inv_approx`).

The proof composes `arith_block_agrees` (the arithmetic, a block operation read from the words and
the inverse arithmetic act as the block read from the computed words), `gRun_locGates`,
`norm_uImpl_sub_le` with the payload bound `norm_matOp_blk_le`, and the native identity.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open GateODE (localOp_localOp localOp_localOp' put put_apply localOp_put bas_eq_put
  overwrite_apply_ι overwrite_apply_out)
open NativeSignedFactor (phase)
open scoped InnerProduct InnerProductSpace BigOperators

/-! ### Blocks of base wires under the arithmetic -/

section ArithBlock

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- A vector placed at the outside configuration of `x` is the sum of the basis vectors of its
entries. -/
theorem put_eq_sum_bas {W : Type*} [Fintype W] [DecidableEq W] {ι : B → W}
    (hι : Function.Injective ι) (x : Cfg W) (φ : Reg B R) :
    put ι hι x φ = ∑ c, bas (overwrite ι x c) (φ c) := by
  apply PiLp.ext
  intro y
  rw [put_apply, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [bas_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single (fun a => y (ι a))]
    · rw [if_pos]
      show y = joinCfg ι (outPart ι x) (fun a => y (ι a))
      rw [← h, joinCfg_self hι]
    · intro c _ hc
      rw [if_neg]
      intro hy
      apply hc
      rw [hy]
      funext a
      exact (overwrite_apply_ι hι x c a).symm
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · symm
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg]
    intro hy
    apply h
    rw [hy]
    exact outPart_joinCfg ι _ c

variable {Sel PR Z : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR]
  [Fintype Z] [DecidableEq Z]

omit [DecidableEq B] [Fintype Sel] [Fintype PR] [Fintype Z] in
/-- Clean arithmetic wires stay clean when base wires are overwritten. -/
theorem cleanA_overwrite {bT bP A : ℕ} {E : B → PWr Sel PR Z bT bP A} {e : B → NB Sel PR Z}
    (hEe : ∀ a, E a = vEmb (e a)) (y : Cfg (PWr Sel PR Z bT bP A)) (hy : CleanA y) (c : Cfg B) :
    CleanA (overwrite E y c) := by
  intro w
  rw [overwrite_apply_out E y c _ (fun a h => by rw [hEe] at h; simp [vEmb] at h)]
  exact hy w

omit [DecidableEq B] [Fintype Sel] [Fintype PR] [Fintype Z] in
/-- The arithmetic output commutes with overwriting base wires it does not read. -/
theorem arOut_overwrite (ar : Arith (NB Sel PR Z)) {e : B → NB Sel PR Z}
    {E : B → PWr Sel PR Z ar.bT ar.bP ar.A} (hE : Function.Injective E)
    (hEe : ∀ a, E a = vEmb (e a)) (hout : ∀ x c, ar.out (overwrite e x c) = ar.out x)
    (y : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A)) (c : Cfg B) :
    arOut ar (overwrite E y c) = overwrite E (arOut ar y) c := by
  have he : Function.Injective e := fun a b h => hE (by rw [hEe, hEe, h])
  have hv : (fun n => overwrite E y c (vEmb n)) = overwrite e (fun n => y (vEmb n)) c := by
    funext n
    by_cases hn : ∃ a, e a = n
    · obtain ⟨a, rfl⟩ := hn
      rw [← hEe, overwrite_apply_ι hE, overwrite_apply_ι he]
    · push Not at hn
      rw [overwrite_apply_out E y c _ (fun a h => hn a (vEmb.injective (by rw [← hEe]; exact h))),
        overwrite_apply_out e _ c n hn]
  have hout' : ∀ w, (∀ a, E a ≠ w) → overwrite E (arOut ar y) c w = arOut ar y w :=
    fun w hw => overwrite_apply_out E _ c w hw
  funext w
  rcases w with u | n | w'
  · have h1 : ∀ a, E a ≠ Sum.inl u := fun a h => by rw [hEe] at h; simp [vEmb] at h
    rw [hout' _ h1]
    show overwrite E y c enW = y enW
    exact overwrite_apply_out E y c enW (fun a h => by rw [hEe] at h; simp [vEmb, enW] at h)
  · show overwrite E y c (vEmb n) = overwrite E (arOut ar y) c (vEmb n)
    by_cases hn : ∃ a, e a = n
    · obtain ⟨a, rfl⟩ := hn
      rw [← hEe, overwrite_apply_ι hE, overwrite_apply_ι hE]
    · push Not at hn
      have h2 : ∀ a, E a ≠ vEmb n := fun a h => hn a (vEmb.injective (by rw [← hEe]; exact h))
      rw [overwrite_apply_out E y c _ h2, overwrite_apply_out E _ c _ h2]
      rfl
  · have h3 : ∀ a, E a ≠ Sum.inr (Sum.inr w') := fun a h => by rw [hEe] at h; simp [vEmb] at h
    rw [hout' _ h3]
    show ar.out (fun n => overwrite E y c (vEmb n)) w' = ar.out (fun n => y (vEmb n)) w'
    rw [hv, hout]

/-- **The arithmetic, a block operation and the inverse arithmetic** act on clean arithmetic wires
as the block operation selected by the computed words, provided the words do not depend on the
block. -/
theorem arith_block_agrees (ar : Arith (NB Sel PR Z)) (hcl : Classical ar.circ)
    (hcomp : ∀ x : Cfg (NB Sel PR Z), cfgRun ar.circ (Sum.elim x (fun _ => false)) =
      Sum.elim x (ar.out x))
    {e : B → NB Sel PR Z} {E : B → PWr Sel PR Z ar.bT ar.bP ar.A} (hE : Function.Injective E)
    (hEe : ∀ a, E a = vEmb (e a)) (hout : ∀ x c, ar.out (overwrite e x c) = ar.out x)
    (F : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A) → (Reg B R →L[ℂ] Reg B R)) :
    Agrees CleanA
      (gRun (Q := R) (gInv (ar.circ.map (GateODE.Gate.map aEmb))) ∘L localOp E hE F ∘L
        gRun (ar.circ.map (GateODE.Gate.map aEmb)))
      (localOp E hE (fun y => F (arOut ar y))) := by
  have hU : AllUnitary (ar.circ.map (GateODE.Gate.map (aEmb (Sel := Sel) (PR := PR) (Z := Z)
      (bT := ar.bT) (bP := ar.bP) (A := ar.A)))) := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    show UnitaryMat g'.u
    rw [(hcl g' hg').1]
    exact pauliX_unitary
  have hinv := gRun_gInv_comp (Q := R) _ hU
  have hA := arith_bas (R := R) ar hcl hcomp
  have hback : ∀ y', CleanA y' → ∀ q : R,
      gRun (Q := R) (gInv (ar.circ.map (GateODE.Gate.map aEmb))) (bas (arOut ar y') q) =
        bas y' q := by
    intro y' hy' q
    rw [← hA y' hy' q, ← comp_apply, hinv, one_apply_eq_self]
  apply agrees_of_bas
  intro y hy q
  rw [comp_apply, comp_apply, hA y hy q, localOp_bas, localOp_bas, put_eq_sum_bas,
    put_eq_sum_bas, map_sum]
  have hclr : clearCfg E (arOut ar y) = arOut ar (clearCfg E y) :=
    (arOut_overwrite ar hE hEe hout y _).symm
  have hloc : (fun a => arOut ar y (E a)) = (fun a => y (E a)) := by
    funext a
    rw [hEe]
    rfl
  rw [hclr, hloc]
  apply Finset.sum_congr rfl
  intro c _
  rw [← arOut_overwrite ar hE hEe hout, hback _ (cleanA_overwrite hEe y hy c)]

end ArithBlock

/-! ### Public data and hypotheses -/

/-- The public data of a native factor: the compute circuit `W`, the flag, orientation and sign
qubits `loc 0`, `loc 1`, `loc 2` of the private register, the public decoder of the entry `c`, and
the reversible arithmetic with its angle and phase words. -/
structure FactorOp (PR Z Y J : Type*) (bT bP A : ℕ) where
  /-- The compute circuit: the entry data into the scratch. -/
  W : List (NInstr (NB Empty PR Z) Y J)
  /-- The flag, orientation and sign qubits. -/
  loc : Fin 3 ↪ PR
  /-- The decoded entry `c`. -/
  dec : Cfg (NB Empty PR Z) → ℂ
  /-- The reversible arithmetic on the base wires, the two words and `A` work wires. -/
  circ : List (Gate (NB Empty PR Z ⊕ AWr bT bP A))
  /-- The angle word. -/
  tw : Cfg (NB Empty PR Z) → Fin bT → Bool
  /-- The phase word. -/
  pw : Cfg (NB Empty PR Z) → Fin bP → Bool

section Wires

variable {PR Z Y J : Type*} {bT bP A : ℕ}

/-- The three local qubits among the base wires. -/
def FactorOp.locB (fo : FactorOp PR Z Y J bT bP A) : Fin 3 → NB Empty PR Z :=
  fun a => Sum.inl (Sum.inr (fo.loc a))

theorem FactorOp.locB_injective (fo : FactorOp PR Z Y J bT bP A) :
    Function.Injective fo.locB :=
  fun _ _ h => fo.loc.injective (Sum.inr_injective (Sum.inl_injective h))

/-- The three local qubits among the implementation wires. -/
def FactorOp.locW (fo : FactorOp PR Z Y J bT bP A) : Fin 3 → PWr Empty PR Z bT bP A :=
  fun a => tgtW (fo.loc a)

theorem FactorOp.locW_injective (fo : FactorOp PR Z Y J bT bP A) :
    Function.Injective fo.locW :=
  fun _ _ h => fo.loc.injective (by simpa [FactorOp.locW, tgtW] using h)

/-- The arithmetic as arithmetic data of the baseline. -/
abbrev FactorOp.ar (fo : FactorOp PR Z Y J bT bP A) : Arith (NB Empty PR Z) :=
  ⟨bT, bP, A, fo.circ, fo.tw, fo.pw⟩

/-- The arithmetic gates on the implementation wires. -/
def FactorOp.arG (fo : FactorOp PR Z Y J bT bP A) : List (Gate (PWr Empty PR Z bT bP A)) :=
  fo.circ.map (GateODE.Gate.map aEmb)

end Wires

/-- **Public conditions**: the compute circuit is valid, the decoder does not read the three local
qubits, and `‖c‖ ≤ 1`. -/
structure FactorOp.Public {PR Z Y J : Type*} [DecidableEq PR] [DecidableEq Z] {bT bP A : ℕ}
    (fo : FactorOp PR Z Y J bT bP A) : Prop where
  valid : ∀ i ∈ fo.W, i.Valid
  dec_indep : ∀ x (c : Cfg (Fin 3)), fo.dec (overwrite fo.locB x c) = fo.dec x
  dec_le : ∀ x, ‖fo.dec x‖ ≤ 1

/-- **The arithmetic hypothesis.** The reversible arithmetic consists of controlled NOT gates with
at most three controls; on clean arithmetic wires it writes the angle and phase words,
independently of the three local qubits; and either the entry is below the threshold `ξ²/16` and
the angle is zero, or the magnitude `sin² α` is within `ξ²` of `‖c‖` and the phase `e^{iφ}`
within `ξ` of `c/|c|`. -/
structure FactorArithOK {PR Z Y J : Type*} [DecidableEq PR] [DecidableEq Z] {bT bP A : ℕ}
    (fo : FactorOp PR Z Y J bT bP A) (ξ : ℝ) : Prop where
  elem : ∀ g ∈ fo.circ, g.cs.length ≤ 3
  classical : Classical fo.circ
  compute : ∀ x : Cfg (NB Empty PR Z), cfgRun fo.circ (Sum.elim x (fun _ => false)) =
    Sum.elim x (fo.ar.out x)
  tw_indep : ∀ x (c : Cfg (Fin 3)), fo.tw (overwrite fo.locB x c) = fo.tw x
  pw_indep : ∀ x (c : Cfg (Fin 3)), fo.pw (overwrite fo.locB x c) = fo.pw x
  acc : ∀ x, (‖fo.dec x‖ ≤ ξ ^ 2 / 16 ∧ alphaVal (fo.tw x) = 0) ∨
    (|Real.sin (alphaVal (fo.tw x)) ^ 2 - ‖fo.dec x‖| ≤ ξ ^ 2 ∧
      ‖Complex.exp (phiVal (fo.pw x) * Complex.I) - phase (fo.dec x)‖ ≤ ξ)

/-! ### The macro -/

section Macro

variable {PR Z Y J : Type*} {bT bP A : ℕ}

/-- **The native factor**: compute, arithmetic, the local factor gates, inverse arithmetic,
uncompute. -/
def factorMacro (fo : FactorOp PR Z Y J bT bP A) : List (NInstr (PWr Empty PR Z bT bP A) Y J) :=
  fo.W.map (NInstr.map vEmb) ++ nGatesOf fo.arG ++ nGatesOf (locGates fo.locW twW pwW) ++
    nGatesOf (gInv fo.arG) ++ ninv (fo.W.map (NInstr.map vEmb))

theorem factorMacro_nGates (fo : FactorOp PR Z Y J bT bP A) :
    nGatesN (factorMacro fo) = 2 * nGatesN fo.W + 2 * fo.circ.length + (2 * bP + bT + 4) := by
  simp only [factorMacro, FactorOp.arG, nGatesN_append, nGatesN_map, nGatesN_ninv,
    nGatesN_nGatesOf, List.length_map, gInv_length, locGates_length]
  ring

theorem factorMacro_nCalls (p : J → Bool) (fo : FactorOp PR Z Y J bT bP A) :
    nCallsN p (factorMacro fo) = 2 * nCallsN p fo.W := by
  simp only [factorMacro, nCallsN_append, nCallsN_map, nCallsN_ninv, nCallsN_nGatesOf]
  ring

theorem locW_ne_twW (fo : FactorOp PR Z Y J bT bP A) (j : Fin bT) (a : Fin 3) :
    fo.locW a ≠ twW j := by
  simp [FactorOp.locW, tgtW, twW]

theorem locW_ne_pwW (fo : FactorOp PR Z Y J bT bP A) (j : Fin bP) (a : Fin 3) :
    fo.locW a ≠ pwW j := by
  simp [FactorOp.locW, tgtW, pwW]

theorem factorMacro_valid (fo : FactorOp PR Z Y J bT bP A) (hW : ∀ i ∈ fo.W, i.Valid)
    (helem : ∀ g ∈ fo.circ, g.cs.length ≤ 3) (hcl : Classical fo.circ) :
    ∀ i ∈ factorMacro fo, i.Valid := by
  have hV := valid_map_list (vEmb (Sel := Empty) (PR := PR) (Z := Z) (bT := bT) (bP := bP)
    (A := A)) fo.W hW
  have hA := classical_map_ok (aEmb (Sel := Empty) (PR := PR) (Z := Z) (bT := bT) (bP := bP)
    (A := A)) fo.circ helem hcl
  have hL := locGates_ok fo.locW_injective (fun j a => locW_ne_twW fo j a)
    (fun j a => locW_ne_pwW fo j a)
  intro i hi
  simp only [factorMacro, List.mem_append] at hi
  rcases hi with (((h | h) | h) | h) | h
  · exact hV i h
  · exact valid_nGatesOf _ hA i h
  · exact valid_nGatesOf _ (fun g hg => (hL g hg).mono (by norm_num)) i h
  · exact valid_nGatesOf _ (gInv_ok _ hA) i h
  · exact valid_ninv _ hV i h

end Macro

/-! ### The estimate -/

section Estimate

variable {PR Z Y J : Type*} [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The decoded factor `U(c)` on the three local qubits of the base wires. -/
def Udec (fo : FactorOp PR Z Y J bT bP A) : Reg (NB Empty PR Z) R →L[ℂ] Reg (NB Empty PR Z) R :=
  localOp fo.locB fo.locB_injective (fun x => matOp (blk (uMat (fo.dec x))))

/-- **The native identity** (instance hypothesis): `W† U(c) W` acts as the factor `U_B` on clean
scratch. -/
def FactorNativeOK (prim : J → Reg Y R →L[ℂ] Reg Y R) (fo : FactorOp PR Z Y J bT bP A)
    (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) : Prop :=
  (nrun prim fo.W)† ∘L Udec fo ∘L nrun prim fo.W ∘L cleanEmb = cleanEmb ∘L Usel

/-- The local factor read from the words computed from the base configuration. -/
def Util (fo : FactorOp PR Z Y J bT bP A) :
    Reg (PWr Empty PR Z bT bP A) R →L[ℂ] Reg (PWr Empty PR Z bT bP A) R :=
  localOp fo.locW fo.locW_injective (fun y => matOp (blk (uImpl
    (alphaVal (fo.tw (fun n => y (vEmb n)))) (phiVal (fo.pw (fun n => y (vEmb n)))))))

/-- The decoded factor on the implementation wires. -/
def Uid (fo : FactorOp PR Z Y J bT bP A) :
    Reg (PWr Empty PR Z bT bP A) R →L[ℂ] Reg (PWr Empty PR Z bT bP A) R :=
  localOp fo.locW fo.locW_injective (fun y => matOp (blk (uMat (fo.dec (fun n => y (vEmb n))))))

omit [Fintype Y] [DecidableEq Y] in
/-- The arithmetic, the local factor gates and the inverse arithmetic act as the local factor read
from the computed words. -/
theorem arith_loc_agrees (fo : FactorOp PR Z Y J bT bP A) {ξ : ℝ} (har : FactorArithOK fo ξ) :
    Agrees CleanA
      (gRun (Q := R) (gInv fo.arG) ∘L gRun (locGates fo.locW twW pwW) ∘L gRun fo.arG)
      (Util fo) := by
  rw [gRun_locGates fo.locW_injective twW pwW (fun j a => locW_ne_twW fo j a)
    (fun j a => locW_ne_pwW fo j a)]
  have hout : ∀ x c, fo.ar.out (overwrite fo.locB x c) = fo.ar.out x := by
    intro x c
    show Sum.elim (Sum.elim (fo.tw (overwrite fo.locB x c)) (fo.pw (overwrite fo.locB x c)))
      (fun _ => false) = Sum.elim (Sum.elim (fo.tw x) (fo.pw x)) (fun _ => false)
    rw [har.tw_indep, har.pw_indep]
  exact arith_block_agrees (R := R) fo.ar har.classical har.compute fo.locW_injective
    (fun _ => rfl) hout (fun y => matOp (blk (uImpl (alphaVal (fun j => y (twW j)))
      (phiVal (fun j => y (pwW j))))))

omit [Fintype Y] [DecidableEq Y] in
/-- **The computed words give the decoded factor within `3ξ`.** -/
theorem Util_approx (fo : FactorOp PR Z Y J bT bP A) (hpub : fo.Public) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (har : FactorArithOK fo ξ) :
    ApproxOn (fun _ => True) (Util (R := R) fo) (Uid fo) (3 * ξ) := by
  apply approxOn_localOp _ _ _ (by linarith) (SA := fun _ => True) (fun _ _ => trivial)
  intro y ψ _
  show ‖matOp (blk (uImpl _ _)) ψ - matOp (blk (uMat _)) ψ‖ ≤ 3 * ξ * ‖ψ‖
  rw [← sub_apply, ← matOp_sub', ← blk_sub]
  refine (norm_matOp_blk_le _ ψ).trans ?_
  gcongr
  exact norm_uImpl_sub_le (hpub.dec_le _) (alphaVal_nonneg _) (alphaVal_le _) hξ (har.acc _)

omit [Fintype Y] [DecidableEq Y] in
/-- The decoded factor on the implementation wires is the decoded factor on the base wires. -/
theorem Uid_eq_localOp (fo : FactorOp PR Z Y J bT bP A) (hpub : fo.Public) :
    Uid (R := R) fo = localOp vEmb vEmb.injective (fun _ => Udec fo) := by
  unfold Uid Udec
  rw [localOp_localOp' vEmb.injective fo.locB_injective fo.locW fo.locW_injective (fun _ => rfl)
    (fun _ x => matOp (blk (uMat (fo.dec x))))]
  refine congrArg (localOp fo.locW fo.locW_injective) (funext fun z => ?_)
  exact congrArg (fun d => matOp (Q := R) (blk (uMat d)))
    (hpub.dec_indep (fun a => z (vEmb a)) (fun _ => false)).symm

variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

/-- A native identity as agreement on clean scratch. -/
theorem agrees_of_native {W : List (NInstr (NB Empty PR Z) Y J)}
    {Lid : Reg (NB Empty PR Z) R →L[ℂ] Reg (NB Empty PR Z) R}
    {Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R}
    (hN : (nrun prim W)† ∘L Lid ∘L nrun prim W ∘L cleanEmb = cleanEmb ∘L Usel) :
    Agrees CleanX ((nrun prim W)† ∘L Lid ∘L nrun prim W) (liftB Usel) := by
  intro ψ hψ
  rw [eq_cleanEmb_of_supp ψ hψ]
  have h1 := congrArg (fun F => F (WithLp.toLp 2 (fun b => ψ (Sum.elim b (fun _ => false)))))
    hN
  have h2 := congrArg (fun F => F (WithLp.toLp 2 (fun b => ψ (Sum.elim b (fun _ => false)))))
    (liftB_cleanEmb (X := Z) Usel)
  simp only [comp_apply] at h1 h2 ⊢
  rw [h1, h2]

/-- The unconditional ideal on the implementation wires: `U_B` on the private register. -/
def uncIdeal (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) :
    Reg (PWr Empty PR Z bT bP A) R →L[ℂ] Reg (PWr Empty PR Z bT bP A) R :=
  localOp selPR selPR.injective (fun _ => Usel)

/-- A conjugated local operation agrees with the unconditional ideal on clean scratch. -/
theorem factor_agrees {W : List (NInstr (NB Empty PR Z) Y J)}
    {Lid : Reg (NB Empty PR Z) R →L[ℂ] Reg (NB Empty PR Z) R}
    {Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R}
    (hN : (nrun prim W)† ∘L Lid ∘L nrun prim W ∘L cleanEmb = cleanEmb ∘L Usel) :
    Agrees (CleanP (bT := bT) (bP := bP) (A := A))
      (localOp vEmb vEmb.injective (fun _ => (nrun prim W)† ∘L Lid ∘L nrun prim W))
      (uncIdeal Usel) := by
  have hA := agrees_localOp (Q := R) (vEmb (Sel := Empty) (PR := PR) (Z := Z) (bT := bT)
    (bP := bP) (A := A)).injective
    (fun _ => (nrun prim W)† ∘L Lid ∘L nrun prim W)
    (fun _ => liftB Usel) (SA := CleanX) (SW := CleanP)
    (fun y hy z => hy.1 z) (fun _ => agrees_of_native prim hN)
  refine fun ψ hψ => (hA ψ hψ).trans ?_
  have hsplit : (fun _ : Cfg (PWr Empty PR Z bT bP A) => liftB (X := Z) Usel) =
      (fun _ => localOp Sum.inl Sum.inl_injective (fun _ => Usel)) := rfl
  rw [hsplit, localOp_localOp' vEmb.injective Sum.inl_injective selPR selPR.injective
    (fun _ => rfl) (fun _ _ => Usel)]
  rfl

/-- **The native factor is within `3ξ` of `U_B`** on clean scratch and arithmetic wires. -/
theorem factorMacro_approx (hprim : ∀ j, IsUnitary (prim j)) (fo : FactorOp PR Z Y J bT bP A)
    (hpub : fo.Public) {ξ : ℝ} (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) (hN : FactorNativeOK prim fo Usel) :
    ApproxOn CleanP (nrun prim (factorMacro fo)) (uncIdeal Usel) (3 * ξ) := by
  have hVu : IsUnitary (nrun prim fo.W) := nrun_isUnitary prim hprim _ hpub.valid
  obtain ⟨V', hV'⟩ : ∃ V' : Reg (PWr Empty PR Z bT bP A) R →L[ℂ] Reg (PWr Empty PR Z bT bP A) R,
      V' = localOp vEmb vEmb.injective (fun _ => nrun prim fo.W) := ⟨_, rfl⟩
  have hV'u : IsUnitary V' := by
    rw [hV']
    exact localOp_isUnitary _ _ (fun _ => hVu)
  have hrun : nrun prim (factorMacro fo) = V'† ∘L (gRun (Q := R) (gInv fo.arG) ∘L
      gRun (locGates fo.locW twW pwW) ∘L gRun fo.arG) ∘L V' := by
    simp only [factorMacro, nrun_append, nrun_ninv, nrun_map, nrun_nGatesOf]
    rw [hV']
    simp only [comp_assoc]
  have hid : (V'†) ∘L Uid fo ∘L V' =
      localOp vEmb vEmb.injective (fun _ => (nrun prim fo.W)† ∘L Udec fo ∘L nrun prim fo.W) := by
    rw [Uid_eq_localOp fo hpub, hV', localOp_adjoint, localOp_comp, localOp_comp]
  have hag := factor_agrees prim (Lid := Udec fo) hN (bT := bT) (bP := bP) (A := A)
  have hrt := arith_loc_agrees (R := R) fo har
  have happ := Util_approx (R := R) fo hpub hξ har
  intro ψ hψ
  have hψA : Supp CleanA ψ := fun y hy => hψ y (fun h => hy h.2)
  have hVψ : Supp CleanA (V' ψ) := by
    rw [hV']
    apply preserves_localOp CleanA _ vEmb.injective (fun _ => nrun prim fo.W) _ ψ hψA
    intro y b hy w
    rw [overwrite_apply_out _ y b _ (fun n hn => by simp [vEmb] at hn)]
    exact hy w
  have e1 : nrun prim (factorMacro fo) ψ = (V'†) (Util fo (V' ψ)) := by
    rw [hrun, comp_apply, comp_apply, hrt _ hVψ]
  have e2 : uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel ψ =
      (V'†) (Uid fo (V' ψ)) := by
    rw [← hag ψ hψ, ← hid, comp_apply, comp_apply]
  have hVadj : IsUnitary (V'†) := by simpa [star_eq_adjoint] using hV'u.adjoint
  have hiso : ‖V' ψ‖ = ‖ψ‖ := by
    have h1 : V'† ∘L V' = 1 := by
      have := hV'u.1; rwa [star_eq_adjoint, mul_def] at this
    exact (V'.norm_map_iff_adjoint_comp_self).mpr h1 ψ
  rw [e1, e2, ← map_sub]
  calc ‖(V'†) (Util fo (V' ψ) - Uid fo (V' ψ))‖
      ≤ ‖Util fo (V' ψ) - Uid fo (V' ψ)‖ := IsUnitary.norm_apply_le hVadj _
    _ ≤ 3 * ξ * ‖V' ψ‖ := happ _ (fun _ h => absurd trivial h)
    _ = 3 * ξ * ‖ψ‖ := by rw [hiso]

theorem uncIdeal_adjoint (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) :
    (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel)† = uncIdeal (Usel†) := by
  unfold uncIdeal
  rw [localOp_adjoint]

/-- **The literal inverse of the native factor is within `3ξ` of `U_B†`.** -/
theorem factorMacro_inv_approx (hprim : ∀ j, IsUnitary (prim j)) (fo : FactorOp PR Z Y J bT bP A)
    (hpub : fo.Public) {ξ : ℝ} (hξ : 0 ≤ ξ) (har : FactorArithOK fo ξ)
    (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) (hU : IsUnitary Usel)
    (hN : FactorNativeOK prim fo Usel) :
    ApproxOn CleanP (nrun prim (ninv (factorMacro fo)))
      (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) (Usel†)) (3 * ξ) := by
  rw [nrun_ninv, ← uncIdeal_adjoint]
  have hC : IsUnitary (nrun prim (factorMacro fo)) :=
    nrun_isUnitary prim hprim _ (factorMacro_valid fo hpub.valid har.elem har.classical)
  have hO : IsUnitary (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel) :=
    localOp_isUnitary _ _ (fun _ => hU)
  have hOs : Preserves CleanP ((uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel)†) := by
    rw [uncIdeal_adjoint]
    unfold uncIdeal
    apply preserves_localOp
    intro y b hy
    constructor
    · intro z
      rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
      exact hy.1 z
    · intro w
      rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
      exact hy.2 w
  exact (factorMacro_approx prim hprim fo hpub hξ har Usel hN).adjoint hC hO hOs

end Estimate

end

end GateOptimalPrecision
