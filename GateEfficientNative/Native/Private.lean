import GateEfficientNative.Native.Rotation

/-!
# The native private Cayley operation

In query-free coordinates the private operation has the native form
`D = V† R_val V` (paper: `D₀ = F† O_val† R_val O_val F`): a public *compute
circuit* `V` of elementary gates and primitive oracle calls writes the
entry data into clean scratch wires, the edge rotation `R_val = D_edge(z)` of
`hs:eq:edge` acts on the orientation wire for the *decoded entry* `z` (a
public function of the selection wires, the private register and the
scratch), and `V†` uncomputes.  An external enable bit controls only the
middle rotation.

**Wires** (`PWr Sel PR Z bT bP A`): the enable wire, the selection wires `Sel`
(time slot or LCHS label, empty for a constant Hamiltonian), the private
register `PR` (ancillas and system), the scratch `Z`, the angle words
(`bT` and `bP` bits) and `A` arithmetic work wires.

**Hypotheses.**

* Public (`NativeOp.Public`, `ArithOK`): the compute circuit is valid, the
  decoder does not read the orientation wire, and the reversible arithmetic
  `Arith` (controlled NOT gates with at most three controls) writes angle
  words `θ̃`, `φ̃` with `|θ̃ - 2 arctan |z|| ≤ ζ` and `φ̃ = arg z` up to `ζ`
  modulo `2π` (when `z ≠ 0`), restoring its work wires.
* Instance (`NativeOK`): `V† R_val V` acts as the selected private operation
  `Dsel` on clean scratch.

**Implementation** (`privMacro`): `V`, the arithmetic, the bit-controlled
rotation circuit of `Native/Rotation` under the enable wire, the inverse
arithmetic and `V†`.  **Error** (`privMacro_approx`): on clean scratch and
arithmetic wires, it is within `4ζ` of the enable-controlled `Dsel`
(`ctrlIdeal`), in the full-output convention.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (localOp_localOp localOp_localOp' put put_apply localOp_put bas_eq_put
  overwrite_apply_ι overwrite_apply_out update_comp_injective)
open scoped InnerProduct BigOperators

/-! ### Wires -/

/-- Base wires: selection wires, the private register, scratch wires. -/
abbrev NB (Sel PR Z : Type*) := (Sel ⊕ PR) ⊕ Z

/-- Arithmetic wires: the two angle words and the work wires. -/
abbrev AWr (bT bP A : ℕ) := (Fin bT ⊕ Fin bP) ⊕ Fin A

/-- The wires of a private implementation. -/
abbrev PWr (Sel PR Z : Type*) (bT bP A : ℕ) := Unit ⊕ (NB Sel PR Z ⊕ AWr bT bP A)

section Wires

variable {Sel PR Z : Type*} {bT bP A : ℕ}

/-- The base wires inside the implementation wires. -/
def vEmb : NB Sel PR Z ↪ PWr Sel PR Z bT bP A :=
  ⟨fun n => Sum.inr (Sum.inl n), fun _ _ h => Sum.inl_injective (Sum.inr_injective h)⟩

/-- Base and arithmetic wires inside the implementation wires. -/
def aEmb : (NB Sel PR Z ⊕ AWr bT bP A) ↪ PWr Sel PR Z bT bP A :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Selection wires and private register inside the implementation wires. -/
def selPR : (Sel ⊕ PR) ↪ PWr Sel PR Z bT bP A :=
  ⟨fun p => Sum.inr (Sum.inl (Sum.inl p)),
    fun _ _ h => Sum.inl_injective (Sum.inl_injective (Sum.inr_injective h))⟩

/-- The enable wire. -/
def enW : PWr Sel PR Z bT bP A := Sum.inl ()

/-- The orientation wire. -/
def tgtW (o : PR) : PWr Sel PR Z bT bP A := Sum.inr (Sum.inl (Sum.inl (Sum.inr o)))

/-- The wires of the word `θ̃`. -/
def twW (j : Fin bT) : PWr Sel PR Z bT bP A := Sum.inr (Sum.inr (Sum.inl (Sum.inl j)))

/-- The wires of the word `φ̃`. -/
def pwW (j : Fin bP) : PWr Sel PR Z bT bP A := Sum.inr (Sum.inr (Sum.inl (Sum.inr j)))

/-- Clean scratch and arithmetic wires. -/
def CleanP (y : Cfg (PWr Sel PR Z bT bP A)) : Prop :=
  (∀ z, y (Sum.inr (Sum.inl (Sum.inr z))) = false) ∧ (∀ w, y (Sum.inr (Sum.inr w)) = false)

/-- Clean arithmetic wires. -/
def CleanA (y : Cfg (PWr Sel PR Z bT bP A)) : Prop := ∀ w, y (Sum.inr (Sum.inr w)) = false

end Wires

/-! ### Public data and hypotheses -/

/-- The public data of a native private operation: the compute circuit `V`,
the orientation wire `o` of the private register, and the public decoder of
the represented entry `z`. -/
structure NativeOp (Sel PR Z Y J : Type*) where
  V : List (NInstr (NB Sel PR Z) Y J)
  o : PR
  dec : Cfg (NB Sel PR Z) → ℂ

/-- Public reversible arithmetic at one accuracy: a circuit on the base wires,
the two angle words and `A` work wires, with its output words. -/
structure Arith (B : Type*) where
  bT : ℕ
  bP : ℕ
  A : ℕ
  circ : List (Gate (B ⊕ AWr bT bP A))
  tw : Cfg B → Fin bT → Bool
  pw : Cfg B → Fin bP → Bool

/-- The output configuration of the arithmetic wires. -/
def Arith.out {B : Type*} (ar : Arith B) (x : Cfg B) : Cfg (AWr ar.bT ar.bP ar.A) :=
  Sum.elim (Sum.elim (ar.tw x) (ar.pw x)) (fun _ => false)

/-- Public conditions on the compute circuit and the decoder. -/
structure NativeOp.Public {Sel PR Z Y J : Type*} [DecidableEq Sel] [DecidableEq PR]
    [DecidableEq Z] (nd : NativeOp Sel PR Z Y J) : Prop where
  valid : ∀ i ∈ nd.V, i.Valid
  dec_indep : ∀ x b, nd.dec (Function.update x (Sum.inl (Sum.inr nd.o)) b) = nd.dec x

/-- **The arithmetic hypothesis.**  The reversible arithmetic consists of
controlled NOT gates with at most three controls; on clean arithmetic wires
it writes the angle words, independently of the orientation wire, and they
approximate `θ = 2 arctan |z|` and `φ = arg z` (modulo `2π`, for `z ≠ 0`)
within `ζ`. -/
structure ArithOK {B : Type*} [DecidableEq B] (ar : Arith B) (o : B) (dec : Cfg B → ℂ)
    (ζ : ℝ) : Prop where
  elem : ∀ g ∈ ar.circ, g.cs.length ≤ 3
  classical : Classical ar.circ
  compute : ∀ x : Cfg B, cfgRun ar.circ (Sum.elim x (fun _ => false)) = Sum.elim x (ar.out x)
  tw_indep : ∀ x b, ar.tw (Function.update x o b) = ar.tw x
  pw_indep : ∀ x b, ar.pw (Function.update x o b) = ar.pw x
  theta : ∀ x, |thetaVal (ar.tw x) - 2 * Real.arctan ‖dec x‖| ≤ ζ
  phi : ∀ x, dec x ≠ 0 →
    ∃ k : ℤ, |phiVal (ar.pw x) - Complex.arg (dec x) - 2 * Real.pi * k| ≤ ζ

variable {Sel PR Z Y J : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The decoded edge rotation on the orientation wire. -/
def Rdec (nd : NativeOp Sel PR Z Y J) : Reg (NB Sel PR Z) R →L[ℂ] Reg (NB Sel PR Z) R :=
  condOp (Sum.inl (Sum.inr nd.o)) (fun x => edgeMat (nd.dec x))

/-- **The native identity** (instance hypothesis): `V† R_val V` acts as the
selected private operation `Dsel` on clean scratch. -/
def NativeOK (prim : J → Reg Y R →L[ℂ] Reg Y R) (nd : NativeOp Sel PR Z Y J)
    (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) : Prop :=
  (nrun prim nd.V)† ∘L Rdec nd ∘L nrun prim nd.V ∘L cleanEmb = cleanEmb ∘L Dsel

/-- The enable-controlled selected private operation. -/
def ctrlIdeal {bT bP A : ℕ} (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) :
    Reg (PWr Sel PR Z bT bP A) R →L[ℂ] Reg (PWr Sel PR Z bT bP A) R :=
  localOp selPR selPR.injective (fun y => if y enW then Dsel else 1)

/-- **The native implementation** of the enable-controlled private operation. -/
def privMacro (nd : NativeOp Sel PR Z Y J) (ar : Arith (NB Sel PR Z)) :
    List (NInstr (PWr Sel PR Z ar.bT ar.bP ar.A) Y J) :=
  nd.V.map (NInstr.map vEmb) ++
    nGatesOf (ar.circ.map (GateODE.Gate.map aEmb)) ++
    nGatesOf (rotGates enW (tgtW nd.o) twW pwW) ++
    nGatesOf (gInv (ar.circ.map (GateODE.Gate.map aEmb))) ++
    ninv (nd.V.map (NInstr.map vEmb))

/-! ### Counts and validity -/

omit [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] in
theorem privMacro_nGates (nd : NativeOp Sel PR Z Y J) (ar : Arith (NB Sel PR Z)) :
    nGatesN (privMacro nd ar) =
      2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) := by
  simp only [privMacro, nGatesN_append, nGatesN_map, nGatesN_ninv, nGatesN_nGatesOf,
    List.length_map, gInv_length, rotGates_length]
  ring

omit [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] in
theorem privMacro_nCalls (p : J → Bool) (nd : NativeOp Sel PR Z Y J)
    (ar : Arith (NB Sel PR Z)) :
    nCallsN p (privMacro nd ar) = 2 * nCallsN p nd.V := by
  simp only [privMacro, nCallsN_append, nCallsN_map, nCallsN_ninv, nCallsN_nGatesOf]
  ring

omit [Fintype Sel] [Fintype PR] [Fintype Z] [Fintype Y] [DecidableEq Y] in
theorem classical_map_ok {B W : Type*} (e : B ↪ W) (gs : List (Gate B))
    (helem : ∀ g ∈ gs, g.cs.length ≤ 3) (hcl : Classical gs) :
    ∀ g ∈ gs.map (GateODE.Gate.map e), GateOK 3 g := by
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨hu, ht⟩ := hcl g' hg'
  refine ⟨by simpa [GateODE.Gate.map] using helem g' hg', ?_, ?_⟩
  · intro c hc
    simp only [GateODE.Gate.map, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    intro h
    exact ht c' hc' (e.injective h)
  · show UnitaryMat g'.u
    rw [hu]
    exact pauliX_unitary

omit [Fintype Sel] [Fintype PR] [Fintype Z] [Fintype Y] [DecidableEq Y] in
theorem privMacro_valid (nd : NativeOp Sel PR Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Sel PR Z)) (helem : ∀ g ∈ ar.circ, g.cs.length ≤ 3)
    (hcl : Classical ar.circ) : ∀ i ∈ privMacro nd ar, i.Valid := by
  have hV := valid_map_list (vEmb (bT := ar.bT) (bP := ar.bP) (A := ar.A)) nd.V hnd.valid
  have hA := classical_map_ok (aEmb (Sel := Sel) (PR := PR) (Z := Z) (bT := ar.bT) (bP := ar.bP)
    (A := ar.A)) ar.circ helem hcl
  have hR := rotGates_ok (W := PWr Sel PR Z ar.bT ar.bP ar.A) enW (tgtW nd.o) twW pwW
    (by simp [enW, tgtW]) (fun j => by simp [twW, tgtW]) (fun j => by simp [pwW, tgtW])
  intro i hi
  simp only [privMacro, List.mem_append] at hi
  rcases hi with (((h | h) | h) | h) | h
  · exact hV i h
  · exact valid_nGatesOf _ hA i h
  · exact valid_nGatesOf _ hR i h
  · exact valid_nGatesOf _ (gInv_ok _ hA) i h
  · exact valid_ninv _ hV i h

/-! ### Basis vectors under exposed operators -/

section Basis

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

omit [CompleteSpace Q] in
theorem put_bas {ι : A → W} (hι : Function.Injective ι) (y : Cfg W) (c : Cfg A) (q : Q) :
    put ι hι y (bas c q) = bas (overwrite ι y c) q := by
  rw [bas_eq_put hι (overwrite ι y c) q]
  have h1 : (fun a => overwrite ι y c (ι a)) = c := funext (fun a => overwrite_apply_ι hι y c a)
  rw [h1]
  simp only [put, overwrite, outPart_joinCfg]

theorem localOp_bas {ι : A → W} (hι : Function.Injective ι) (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q))
    (y : Cfg W) (q : Q) :
    localOp ι hι F (bas y q) = put ι hι y (F (clearCfg ι y) (bas (fun a => y (ι a)) q)) := by
  rw [bas_eq_put hι y q, localOp_put]

/-- A renamed gate list acts as the original on the exposed wires. -/
theorem gRun_map_gates (e : A ↪ W) (gs : List (Gate A)) :
    gRun (Q := Q) (gs.map (GateODE.Gate.map e)) = localOp e e.injective (fun _ => gRun gs) := by
  induction gs with
  | nil => exact (localOp_one e.injective).symm
  | cons g gs ih =>
      rw [List.map_cons, gRun_cons, ih, ← GateODE.Gate.map_op e.injective g,
        localOp_comp, gRun_cons]

end Basis

/-! ### Controlled rotations on exposed wires -/

section CondLocal

variable {W A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A one-qubit operation on exposed wires, enabled by an outside wire, is
the enabled operation on the whole register. -/
theorem localOp_ite_condOp {e : A → W} (he : Function.Injective e) (w₀ : W)
    (hw₀ : ∀ a, e a ≠ w₀) (t : A) (u : Cfg A → Matrix Bool Bool ℂ)
    (hu : ∀ x b, u (Function.update x t b) = u x) :
    localOp e he (fun y => if y w₀ then condOp (Q := Q) t u else 1) =
      condOp (e t) (fun y => if y w₀ then u (fun a => y (e a)) else 1) := by
  have h1 : (fun y : Cfg W => if y w₀ then condOp (Q := Q) t u else 1) =
      (fun y => condOp t (fun x => if y w₀ then u x else 1)) := by
    funext y
    by_cases hy : y w₀ = true
    · simp only [hy, if_true]
    · simp only [hy, Bool.false_eq_true, if_false]
      exact (condOp_one t).symm
  rw [h1]
  unfold condOp
  rw [localOp_localOp' he (single_injective t) (fun _ : Unit => e t) (single_injective (e t))
    (fun _ => rfl)]
  apply localOp_congr
  intro z
  have h2 : clearCfg e (Function.update z (e t) false) w₀ = Function.update z (e t) false w₀ :=
    clearCfg_apply_out e _ w₀ hw₀
  simp only [clearCfg_single]
  rw [hu, h2]

end CondLocal

/-! ### The core estimate -/

section Core

/-- The configuration after the arithmetic: the angle words and clean work wires. -/
def arOut (ar : Arith (NB Sel PR Z)) (y : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A)) :
    Cfg (PWr Sel PR Z ar.bT ar.bP ar.A) :=
  Sum.elim (fun _ => y enW) (Sum.elim (fun n => y (vEmb n)) (ar.out (fun n => y (vEmb n))))

omit [Fintype Sel] [Fintype PR] [Fintype Z] in
theorem Arith.out_update (ar : Arith (NB Sel PR Z)) (o : NB Sel PR Z)
    (h1 : ∀ x b, ar.tw (Function.update x o b) = ar.tw x)
    (h2 : ∀ x b, ar.pw (Function.update x o b) = ar.pw x) (x : Cfg (NB Sel PR Z)) (b : Bool) :
    ar.out (Function.update x o b) = ar.out x := by
  unfold Arith.out
  rw [h1, h2]

omit [Fintype Sel] [Fintype PR] [Fintype Z] [Fintype Y] [DecidableEq Y] in
theorem arOut_update (nd : NativeOp Sel PR Z Y J) (ar : Arith (NB Sel PR Z))
    (h1 : ∀ x b, ar.tw (Function.update x (Sum.inl (Sum.inr nd.o)) b) = ar.tw x)
    (h2 : ∀ x b, ar.pw (Function.update x (Sum.inl (Sum.inr nd.o)) b) = ar.pw x)
    (y : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A)) (b : Bool) :
    arOut ar (Function.update y (tgtW nd.o) b) = Function.update (arOut ar y) (tgtW nd.o) b := by
  have hv : (fun n => Function.update y (tgtW nd.o) b (vEmb n)) =
      Function.update (fun n => y (vEmb n)) (Sum.inl (Sum.inr nd.o)) b :=
    update_comp_injective (vEmb (Sel := Sel) (PR := PR) (Z := Z) (bT := ar.bT) (bP := ar.bP)
      (A := ar.A)).injective y _ b
  funext w
  rcases w with u | n | w'
  · simp [arOut, enW, tgtW, Function.update_apply]
  · simp only [arOut, Sum.elim_inr, Sum.elim_inl]
    simp only [Function.update_apply, tgtW, vEmb, Function.Embedding.coeFn_mk]
    by_cases hn : n = Sum.inl (Sum.inr nd.o)
    · subst hn; simp
    · have : (Sum.inr (Sum.inl n) : PWr Sel PR Z ar.bT ar.bP ar.A) ≠
          Sum.inr (Sum.inl (Sum.inl (Sum.inr nd.o))) := by
        intro h
        exact hn (Sum.inl_injective (Sum.inr_injective h))
      simp [this]
  · simp only [arOut, Sum.elim_inr]
    rw [hv, Arith.out_update ar _ h1 h2]
    simp [tgtW]

theorem arith_bas (ar : Arith (NB Sel PR Z)) (hcl : Classical ar.circ)
    (hcomp : ∀ x : Cfg (NB Sel PR Z), cfgRun ar.circ (Sum.elim x (fun _ => false)) =
      Sum.elim x (ar.out x))
    (y : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A)) (hy : CleanA y) (q : R) :
    gRun (ar.circ.map (GateODE.Gate.map aEmb)) (bas y q) = bas (arOut ar y) q := by
  rw [gRun_map_gates, localOp_bas]
  beta_reduce
  have hya : (fun c => y (aEmb c)) = Sum.elim (fun n => y (vEmb n)) (fun _ => false) := by
    funext c
    cases c with
    | inl n => rfl
    | inr w => exact hy w
  rw [hya, gRun_classical_bas _ hcl, hcomp, put_bas]
  congr 1
  funext w
  rcases w with u | c
  · exact overwrite_apply_out _ y _ _ (fun c hc => by cases hc)
  · exact overwrite_apply_ι aEmb.injective y _ c

/-- The rotation read from the angle words of the base configuration. -/
def Rtil (nd : NativeOp Sel PR Z Y J) (ar : Arith (NB Sel PR Z)) :
    Reg (PWr Sel PR Z ar.bT ar.bP ar.A) R →L[ℂ] Reg (PWr Sel PR Z ar.bT ar.bP ar.A) R :=
  condOp (tgtW nd.o) (fun y => if y enW then
    angMat (thetaVal (ar.tw (fun n => y (vEmb n)))) (phiVal (ar.pw (fun n => y (vEmb n))))
    else 1)

/-- The decoded rotation on the implementation wires. -/
def Rid (nd : NativeOp Sel PR Z Y J) {bT bP A : ℕ} :
    Reg (PWr Sel PR Z bT bP A) R →L[ℂ] Reg (PWr Sel PR Z bT bP A) R :=
  condOp (tgtW nd.o) (fun y => if y enW then edgeMat (nd.dec (fun n => y (vEmb n))) else 1)

omit [Fintype Y] [DecidableEq Y] in
/-- Arithmetic, rotation and inverse arithmetic act as the rotation read from
the computed angle words. -/
theorem arith_rot_agrees (nd : NativeOp Sel PR Z Y J) (ar : Arith (NB Sel PR Z)) {ζ : ℝ}
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ) :
    Agrees CleanA
      (gRun (Q := R) (gInv (ar.circ.map (GateODE.Gate.map aEmb))) ∘L
        gRun (rotGates enW (tgtW nd.o) twW pwW) ∘L gRun (ar.circ.map (GateODE.Gate.map aEmb)))
      (Rtil nd ar) := by
  have hok := classical_map_ok (aEmb (Sel := Sel) (PR := PR) (Z := Z) (bT := ar.bT)
    (bP := ar.bP) (A := ar.A)) ar.circ har.elem har.classical
  have hinv : gRun (Q := R) (gInv (ar.circ.map (GateODE.Gate.map aEmb))) ∘L
      gRun (ar.circ.map (GateODE.Gate.map aEmb)) = 1 :=
    gRun_gInv_comp _ (fun g hg => (hok g hg).2.2)
  have hA := arith_bas (R := R) ar har.classical har.compute
  apply agrees_of_bas
  intro y hy q
  rw [comp_apply, comp_apply, hA y hy q, gRun_rotGates, condOp_bas, Rtil, condOp_bas, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul]
  have hclean : CleanA (Function.update y (tgtW nd.o) b) := by
    intro w
    rw [Function.update_of_ne (by simp [tgtW])]
    exact hy w
  have hback : gRun (Q := R) (gInv (ar.circ.map (GateODE.Gate.map aEmb)))
      (bas (Function.update (arOut ar y) (tgtW nd.o) b) q) =
      bas (Function.update y (tgtW nd.o) b) q := by
    rw [← arOut_update nd ar har.tw_indep har.pw_indep, ← hA _ hclean q, ← comp_apply, hinv,
      one_apply_eq_self]
  rw [hback]
  congr 1
  have hv : (fun n => Function.update y (tgtW nd.o) false (vEmb n)) =
      Function.update (fun n => y (vEmb n)) (Sum.inl (Sum.inr nd.o)) false :=
    update_comp_injective (vEmb (Sel := Sel) (PR := PR) (Z := Z) (bT := ar.bT) (bP := ar.bP)
      (A := ar.A)).injective y _ false
  have hen : Function.update (arOut ar y) (tgtW nd.o) false enW = Function.update y (tgtW nd.o)
      false enW := by
    simp [enW, tgtW, arOut]
  have htw : (fun j => Function.update (arOut ar y) (tgtW nd.o) false (twW j)) =
      ar.tw (fun n => y (vEmb n)) := by
    funext j
    simp [twW, tgtW, arOut, Arith.out]
  have hpw : (fun j => Function.update (arOut ar y) (tgtW nd.o) false (pwW j)) =
      ar.pw (fun n => y (vEmb n)) := by
    funext j
    simp [pwW, tgtW, arOut, Arith.out]
  have hcol : arOut ar y (tgtW nd.o) = y (tgtW nd.o) := rfl
  simp only [hen, htw, hpw, hcol, hv, har.tw_indep, har.pw_indep]

omit [Fintype Y] [DecidableEq Y] in
/-- The computed angles give the decoded edge rotation within `4ζ`. -/
theorem Rtil_approx (nd : NativeOp Sel PR Z Y J) (ar : Arith (NB Sel PR Z)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ) :
    ApproxOn (fun _ => True) (Rtil (R := R) nd ar) (Rid nd) (4 * ζ) := by
  apply norm_condOp_sub_le _ _ _ _ (by linarith)
  intro y
  by_cases hy : y enW = true
  · simp only [hy, if_true]
    rw [edgeMat_eq_angMat]
    set x := fun n => y (vEmb n)
    refine (frob2_angMat_sub_le _ _ _ _ ζ ζ (har.theta x) ?_).trans (by linarith)
    by_cases hd : nd.dec x = 0
    · rw [hd]
      simp [hζ]
    · obtain ⟨k, hk⟩ := har.phi x hd
      have hper : Complex.exp ((phiVal (ar.pw x) : ℂ) * Complex.I) =
          Complex.exp (((phiVal (ar.pw x) - 2 * Real.pi * k : ℝ) : ℂ) * Complex.I) := by
        have h2 := Complex.exp_int_mul_two_pi_mul_I k
        rw [show (((phiVal (ar.pw x) - 2 * Real.pi * k : ℝ) : ℂ) * Complex.I) =
          (phiVal (ar.pw x) : ℂ) * Complex.I - (k : ℂ) * (2 * Real.pi * Complex.I) by
            push_cast; ring, Complex.exp_sub, h2, div_one]
      rw [hper]
      have h3 := norm_exp_sub_exp_le (phiVal (ar.pw x) - 2 * Real.pi * k) (Complex.arg (nd.dec x))
      have h4 : |phiVal (ar.pw x) - 2 * Real.pi * k - Complex.arg (nd.dec x)| ≤ ζ := by
        rw [show phiVal (ar.pw x) - 2 * Real.pi * k - Complex.arg (nd.dec x) =
          phiVal (ar.pw x) - Complex.arg (nd.dec x) - 2 * Real.pi * k by ring]
        exact hk
      calc |Real.sin (2 * Real.arctan ‖nd.dec x‖)| *
            ‖Complex.exp (((phiVal (ar.pw x) - 2 * Real.pi * k : ℝ) : ℂ) * Complex.I) -
              Complex.exp ((Complex.arg (nd.dec x) : ℂ) * Complex.I)‖
          ≤ 1 * ζ := mul_le_mul (Real.abs_sin_le_one _) (h3.trans h4) (norm_nonneg _) zero_le_one
        _ = ζ := one_mul ζ
  · simp only [hy, Bool.false_eq_true, if_false, sub_self]
    simp [frob2]
    linarith

end Core

/-! ### The main estimate -/

section Main

variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

omit [Fintype Y] [DecidableEq Y] in
/-- The decoded rotation enabled by the outside enable wire, on the base wires. -/
theorem Rid_eq_localOp (nd : NativeOp Sel PR Z Y J) (hnd : nd.Public) {bT bP A : ℕ} :
    Rid (R := R) (bT := bT) (bP := bP) (A := A) nd =
      localOp vEmb vEmb.injective (fun y => if y enW then Rdec nd else 1) := by
  unfold Rid Rdec
  rw [localOp_ite_condOp vEmb.injective enW (fun a => by simp [vEmb, enW]) _ _
    (fun x b => by rw [hnd.dec_indep])]
  rfl

omit [Fintype Sel] [Fintype PR] [Fintype Z] [CompleteSpace R] in
/-- Clean vectors are clean embeddings. -/
theorem eq_cleanEmb_of_supp {B X : Type*} [Fintype B] [DecidableEq B] [Fintype X]
    [DecidableEq X] (ψ : Reg (B ⊕ X) R) (hψ : Supp CleanX ψ) :
    ψ = cleanEmb (WithLp.toLp 2 (fun b => ψ (Sum.elim b (fun _ => false)))) := by
  apply PiLp.ext
  intro y
  rw [cleanEmb_apply]
  split_ifs with h
  · have hy : y = Sum.elim (fun b => y (Sum.inl b)) (fun _ => false) := by
      funext v
      cases v with
      | inl b => rfl
      | inr x => exact congrFun h x
    conv_lhs => rw [hy]
  · apply hψ
    intro hc
    apply h
    funext x
    exact hc x

/-- The native identity as agreement on clean scratch. -/
theorem agrees_of_nativeOK (nd : NativeOp Sel PR Z Y J)
    (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) (hN : NativeOK prim nd Dsel) :
    Agrees CleanX ((nrun prim nd.V)† ∘L Rdec nd ∘L nrun prim nd.V) (liftB Dsel) := by
  intro ψ hψ
  rw [eq_cleanEmb_of_supp ψ hψ]
  have h1 := congrArg (fun F => F (WithLp.toLp 2 (fun b => ψ (Sum.elim b (fun _ => false))))) hN
  have h2 := congrArg (fun F => F (WithLp.toLp 2 (fun b => ψ (Sum.elim b (fun _ => false)))))
    (liftB_cleanEmb (X := Z) Dsel)
  simp only [comp_apply] at h1 h2 ⊢
  rw [h1, h2]

/-- The enable-controlled native operation agrees with the ideal on clean scratch. -/
theorem native_agrees (nd : NativeOp Sel PR Z Y J) (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R)
    (hN : NativeOK prim nd Dsel) {bT bP A : ℕ} :
    Agrees (CleanP (bT := bT) (bP := bP) (A := A))
      (localOp vEmb vEmb.injective (fun y =>
        if y enW then (nrun prim nd.V)† ∘L Rdec nd ∘L nrun prim nd.V else 1))
      (ctrlIdeal Dsel) := by
  have hA := agrees_localOp (Q := R) (vEmb (Sel := Sel) (PR := PR) (Z := Z) (bT := bT) (bP := bP)
    (A := A)).injective
    (fun y => if y enW then (nrun prim nd.V)† ∘L Rdec nd ∘L nrun prim nd.V else 1)
    (fun y => if y enW then liftB Dsel else 1) (SA := CleanX) (SW := CleanP)
    (fun y hy z => hy.1 z) (by
      intro y
      by_cases h : y enW = true
      · simp only [h, if_true]
        exact agrees_of_nativeOK prim nd Dsel hN
      · simp only [h, Bool.false_eq_true, if_false]
        exact Agrees.refl _ _)
  refine fun ψ hψ => (hA ψ hψ).trans ?_
  have hsplit : (fun y : Cfg (PWr Sel PR Z bT bP A) => if y enW then liftB (X := Z) Dsel else 1) =
      (fun y => localOp Sum.inl Sum.inl_injective (fun _ => if y enW then Dsel else 1)) := by
    funext y
    by_cases h : y enW = true
    · simp only [h, if_true]; rfl
    · simp only [h, Bool.false_eq_true, if_false]
      exact (localOp_one _).symm
  rw [hsplit, localOp_localOp' vEmb.injective Sum.inl_injective selPR selPR.injective
    (fun _ => rfl) (fun y _ => if y enW then Dsel else 1)]
  unfold ctrlIdeal
  refine DFunLike.congr_fun ?_ ψ
  apply localOp_congr
  intro z
  have h : clearCfg vEmb (clearCfg selPR z) enW = clearCfg selPR z enW :=
    overwrite_apply_out _ _ _ enW (fun a => by simp [vEmb, enW])
  simp only [h]

/-- **The native implementation of the enable-controlled private operation**
is within `4ζ` of it on clean scratch and arithmetic wires. -/
theorem privMacro_approx (hprim : ∀ j, IsUnitary (prim j)) (nd : NativeOp Sel PR Z Y J)
    (hnd : nd.Public) (ar : Arith (NB Sel PR Z)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) (hN : NativeOK prim nd Dsel) :
    ApproxOn CleanP (nrun prim (privMacro nd ar)) (ctrlIdeal Dsel) (4 * ζ) := by
  have hVu : IsUnitary (nrun prim nd.V) := nrun_isUnitary prim hprim _ hnd.valid
  obtain ⟨V', hV'⟩ : ∃ V' : Reg (PWr Sel PR Z ar.bT ar.bP ar.A) R →L[ℂ]
      Reg (PWr Sel PR Z ar.bT ar.bP ar.A) R,
      V' = localOp vEmb vEmb.injective (fun _ => nrun prim nd.V) := ⟨_, rfl⟩
  have hV'u : IsUnitary V' := by
    rw [hV']
    exact localOp_isUnitary _ _ (fun _ => hVu)
  have hrun : nrun prim (privMacro nd ar) =
      V'† ∘L (gRun (Q := R) (gInv (ar.circ.map (GateODE.Gate.map aEmb))) ∘L
        gRun (rotGates enW (tgtW nd.o) twW pwW) ∘L gRun (ar.circ.map (GateODE.Gate.map aEmb)))
        ∘L V' := by
    simp only [privMacro, nrun_append, nrun_ninv, nrun_map, nrun_nGatesOf]
    rw [hV']
    simp only [comp_assoc]
  have hid : (V'†) ∘L Rid nd ∘L V' =
      localOp vEmb vEmb.injective
        (fun y => if y enW then (nrun prim nd.V)† ∘L Rdec nd ∘L nrun prim nd.V else 1) := by
    rw [Rid_eq_localOp nd hnd, hV', localOp_adjoint, localOp_comp, localOp_comp]
    refine congrArg (localOp vEmb vEmb.injective) (funext fun y => ?_)
    by_cases h : y enW = true
    · simp only [h, if_true]
    · simp only [h, Bool.false_eq_true, if_false]
      rw [Sim.one_comp']
      have := hVu.1
      rwa [star_eq_adjoint, mul_def] at this
  have hag := native_agrees prim nd Dsel hN (bT := ar.bT) (bP := ar.bP) (A := ar.A)
  have hrt := arith_rot_agrees (R := R) nd ar har
  have happ := Rtil_approx (R := R) nd ar hζ har
  intro ψ hψ
  have hψA : Supp CleanA ψ := fun y hy => hψ y (fun h => hy h.2)
  have hVψ : Supp CleanA (V' ψ) := by
    rw [hV']
    apply preserves_localOp CleanA _ vEmb.injective (fun _ => nrun prim nd.V) _ ψ hψA
    intro y b hy w
    rw [overwrite_apply_out _ y b _ (fun n hn => by simp [vEmb] at hn)]
    exact hy w
  have e1 : nrun prim (privMacro nd ar) ψ = (V'†) (Rtil nd ar (V' ψ)) := by
    rw [hrun, comp_apply, comp_apply, hrt _ hVψ]
  have e2 : ctrlIdeal Dsel ψ = (V'†) (Rid nd (V' ψ)) := by
    rw [← hag ψ hψ, ← hid, comp_apply, comp_apply]
  have hVadj : IsUnitary (V'†) := by simpa [star_eq_adjoint] using hV'u.adjoint
  have hiso : ‖V' ψ‖ = ‖ψ‖ := by
    have h1 : V'† ∘L V' = 1 := by
      have := hV'u.1; rwa [star_eq_adjoint, mul_def] at this
    exact (V'.norm_map_iff_adjoint_comp_self).mpr h1 ψ
  rw [e1, e2, ← map_sub]
  calc ‖(V'†) (Rtil nd ar (V' ψ) - Rid nd (V' ψ))‖
      ≤ ‖Rtil nd ar (V' ψ) - Rid nd (V' ψ)‖ := IsUnitary.norm_apply_le hVadj _
    _ ≤ 4 * ζ * ‖V' ψ‖ := happ _ (fun _ h => absurd trivial h)
    _ = 4 * ζ * ‖ψ‖ := by rw [hiso]

/-- The adjoint of the enable-controlled operation. -/
theorem ctrlIdeal_adjoint {bT bP A : ℕ} (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) :
    (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Dsel)† = ctrlIdeal (Dsel†) := by
  unfold ctrlIdeal
  rw [localOp_adjoint]
  refine congrArg (localOp selPR selPR.injective) (funext fun y => ?_)
  split_ifs
  · rfl
  · simp

/-- The literal inverse of the native implementation implements the inverse. -/
theorem privMacro_inv_approx (hprim : ∀ j, IsUnitary (prim j)) (nd : NativeOp Sel PR Z Y J)
    (hnd : nd.Public) (ar : Arith (NB Sel PR Z)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) (hD : IsUnitary Dsel)
    (hN : NativeOK prim nd Dsel) :
    ApproxOn CleanP (nrun prim (ninv (privMacro nd ar)))
      (ctrlIdeal (Z := Z) (bT := ar.bT) (bP := ar.bP) (A := ar.A) (Dsel†)) (4 * ζ) := by
  rw [nrun_ninv, ← ctrlIdeal_adjoint]
  have hC : IsUnitary (nrun prim (privMacro nd ar)) :=
    nrun_isUnitary prim hprim _ (privMacro_valid nd hnd ar har.elem har.classical)
  have hO : IsUnitary (ctrlIdeal (Z := Z) (bT := ar.bT) (bP := ar.bP) (A := ar.A) Dsel) := by
    apply localOp_isUnitary
    intro y
    split_ifs
    · exact hD
    · exact isUnitary_one
  have hOs : Preserves CleanP ((ctrlIdeal (Z := Z) (bT := ar.bT) (bP := ar.bP) (A := ar.A)
      Dsel)†) := by
    rw [ctrlIdeal_adjoint]
    unfold ctrlIdeal
    apply preserves_localOp
    intro y b hy
    constructor
    · intro z
      rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
      exact hy.1 z
    · intro w
      rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
      exact hy.2 w
  exact (privMacro_approx prim hprim nd hnd ar hζ har Dsel hN).adjoint hC hO hOs

end Main

end

end SparseHamiltonian.GateNative
