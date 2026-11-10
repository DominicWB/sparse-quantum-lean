import GateOptimalPrecision.NativeMain
import GateEfficientSelective.HamMacro

/-!
# The clipped regime with a factor-conjugated native private call

The private Cayley unitary of the clipped joint representation built from sparse oracles
(`GateOptimalBinary.clippedIface`) is `D = U_f† C U_f`: the stable signed factor `U_f = U(c₂)` of
the correction branch, conjugated by the locator, and the edge rotation `C` of the located value,
also conjugated by the locator (Section `gate:sec:native`, paragraph "Sparse preparation and the
joint private operation"). The unitary `D` itself is not of the compute–rotate–uncompute form of
`GateOptimalPrecision.CayleyNative`. Its pieces are native: the rotation `C` has that form (a native
rotation, `NativeOp`), and `U_f` is a native factor (`FactorOp`, as in the signed regime). The
product is supplied as the enable-controlled private circuit of
`SparseHamiltonian.GateSelective.hcircP`:

* `ClipNative`: the native data, with the native identities `W† U(c) W = U_f` (`FactorNativeOK`)
  and `V† R V = C` (`NativeOK`) and the arithmetic hypotheses of both (`FactorArithOK`, `ArithOK`)
  at accuracies `ξ` and `ζ`, on the same arithmetic wires;
* `ClipNative.pc`: the native factor, the native rotation, and the literal inverse of the native
  factor; `pc_approx`: within `6ξ + 4ζ` of the enable-controlled `D` on clean work wires;
* `clip_transfer`, `clip_claims`: the transfer of `GateOptimalPrecision.cayley_claims` with this
  private circuit: `NativeClaims` with the calls and gates of one native private call `pc` and
  full-output error `ε + 2·10¹¹ Q (6ξ + 4ζ)`;
* `gate_optimal_native_clip`, `gate_optimal_native_clip_total`: Theorem `gate:thm:main`, native
  form, with the factor-conjugated native private call in the clipped regime.

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateSelective GateOptimalPrecision
open LargeSparsityCore LargeSparsityCore.Parameters CayleyClockInterface
open GateODE (overwrite_apply_out)
open Complex (I)
open scoped InnerProduct InnerProductSpace BigOperators ComplexOrder

variable {S Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The native data -/

/-- **Native data for a factor-conjugated private operation** `D = U_f† C U_f` with the boundary
`U_J`: the elementary gates `UJg` of `U_J`; the native factor `fo` of `U_f` with its public
conditions, its arithmetic of accuracy `ξ` (`FactorArithOK`) and the native identity
`W† U(c) W = U_f` on clean scratch (`FactorNativeOK`); the native rotation `nd` of `C` with its
public conditions, its angle arithmetic of accuracy `ζ` on the same arithmetic wires (`ArithOK`)
and the native identity `V† R V = C` on clean scratch (`NativeOK`). -/
structure ClipNative (prim : J → Reg Y R →L[ℂ] Reg Y R) {a : ℕ}
    (UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (Z : Type*) [Fintype Z] [DecidableEq Z]
    (bT bP A : ℕ) (ξ ζ : ℝ) where
  /-- The elementary gates of `U_J`. -/
  UJg : List (Gate (Fin a ⊕ S))
  ok : ∀ g ∈ UJg, GateOK 3 g
  boundary : UJop (R := R) UJg = UJ
  /-- The factor. -/
  Uf : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)
  /-- The rotation. -/
  Cf : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)
  unitaryU : IsUnitary Uf
  unitaryC : IsUnitary Cf
  split : D = Uf† ∘L Cf ∘L Uf
  /-- The native factor. -/
  fo : FactorOp (Fin a ⊕ S) Z Y J bT bP A
  fpub : fo.Public
  farith : FactorArithOK fo ξ
  fnative : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => Uf))
  /-- The native rotation. -/
  nd : NativeOp Empty (Fin a ⊕ S) Z Y J
  cpub : nd.Public
  /-- The angle arithmetic of the rotation. -/
  circ : List (Gate (NB Empty (Fin a ⊕ S) Z ⊕ AWr bT bP A))
  tw : Cfg (NB Empty (Fin a ⊕ S) Z) → Fin bT → Bool
  pw : Cfg (NB Empty (Fin a ⊕ S) Z) → Fin bP → Bool
  carith : ArithOK (⟨bT, bP, A, circ, tw, pw⟩ : Arith (NB Empty (Fin a ⊕ S) Z))
    (Sum.inl (Sum.inr nd.o)) nd.dec ζ
  cnative : NativeOK prim nd (selOp (fun _ : Cfg Empty => Cf))

namespace ClipNative

variable {prim : J → Reg Y R →L[ℂ] Reg Y R} {a : ℕ} {UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)}
  {Z : Type*} [Fintype Z] [DecidableEq Z] {bT bP A : ℕ} {ξ ζ : ℝ}

/-- The angle arithmetic of the rotation. -/
abbrev ar (N : ClipNative prim UJ D Z bT bP A ξ ζ) : Arith (NB Empty (Fin a ⊕ S) Z) :=
  ⟨bT, bP, A, N.circ, N.tw, N.pw⟩

/-- **The native private call**: the native factor, the native rotation and the literal inverse
of the native factor. -/
def pc (N : ClipNative prim UJ D Z bT bP A ξ ζ) :
    List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J) :=
  factorMacro N.fo ++ privMacro N.nd N.ar ++ ninv (factorMacro N.fo)

/-- The primitive calls of kind `p` of one native private call. -/
def calls (N : ClipNative prim UJ D Z bT bP A ξ ζ) (p : J → Bool) : ℕ := nCallsN p N.pc

/-- The elementary gates of one native boundary call and one native private call. -/
def cost (N : ClipNative prim UJ D Z bT bP A ξ ζ) : ℕ := 7 * N.UJg.length + nGatesN N.pc

theorem calls_eq (N : ClipNative prim UJ D Z bT bP A ξ ζ) (p : J → Bool) :
    N.calls p = 4 * nCallsN p N.fo.W + 2 * nCallsN p N.nd.V := by
  simp only [calls, pc, nCallsN_append, nCallsN_ninv, factorMacro_nCalls]
  rw [privMacro_nCalls p N.nd N.ar]
  ring

theorem pc_nGates (N : ClipNative prim UJ D Z bT bP A ξ ζ) :
    nGatesN N.pc = 2 * (2 * nGatesN N.fo.W + 2 * N.fo.circ.length + (2 * bP + bT + 4)) +
      (2 * nGatesN N.nd.V + 2 * N.circ.length + (2 * bP + bT + 1)) := by
  simp only [pc, nGatesN_append, nGatesN_ninv, factorMacro_nGates]
  rw [privMacro_nGates N.nd N.ar]
  ring

theorem pc_valid (N : ClipNative prim UJ D Z bT bP A ξ ζ) : ∀ i ∈ N.pc, i.Valid := by
  have hF := factorMacro_valid N.fo N.fpub.valid N.farith.elem N.farith.classical
  have hP := privMacro_valid N.nd N.cpub N.ar N.carith.elem N.carith.classical
  intro i hi
  simp only [pc, List.mem_append] at hi
  rcases hi with (h | h) | h
  · exact hF i h
  · exact hP i h
  · exact valid_ninv _ hF i h

end ClipNative

/-! ### The ideal of the native private call -/

section Ideal

variable {PR Z : Type*} [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z] {bT bP A : ℕ}

theorem preserves_selPR (F : Cfg (PWr Empty PR Z bT bP A) → (Reg (Empty ⊕ PR) R →L[ℂ]
    Reg (Empty ⊕ PR) R)) : Preserves CleanP (localOp selPR selPR.injective F) := by
  apply preserves_localOp
  intro y b hy
  constructor
  · intro z
    rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
    exact hy.1 z
  · intro w
    rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
    exact hy.2 w

/-- **The ideal of the native private call**: `U† (ctrl C) U = ctrl (U† C U)` for an
unconditional isometry `U`. -/
theorem ideal_conj (U C : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) (hU : U† ∘L U = 1) :
    uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) (U†) ∘L
        (ctrlIdeal C ∘L uncIdeal U) =
      ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) (U† ∘L C ∘L U) := by
  unfold uncIdeal ctrlIdeal
  rw [localOp_comp, localOp_comp]
  apply localOp_congr
  intro y
  by_cases h : clearCfg selPR y enW = true
  · simp only [h, if_true]
  · simp only [h, Bool.false_eq_true, if_false]
    rw [Sim.one_comp']
    exact hU

end Ideal

theorem selOp_const_comp {a : ℕ} (O O' : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :
    selOp (Sel := Empty) (a := a) (S := S) (R := R) (fun _ => O) ∘L
        selOp (Sel := Empty) (a := a) (S := S) (R := R) (fun _ => O') =
      selOp (Sel := Empty) (a := a) (S := S) (R := R) (fun _ => O ∘L O') := by
  unfold selOp
  rw [localOp_comp]
  apply localOp_congr
  intro y
  rw [conj_comp]

theorem selOp_split {a : ℕ} (Uf Cf : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :
    (selOp (Sel := Empty) (a := a) (S := S) (R := R) (fun _ => Uf))† ∘L
        (selOp (Sel := Empty) (a := a) (S := S) (R := R) (fun _ => Cf) ∘L
          selOp (Sel := Empty) (a := a) (S := S) (R := R) (fun _ => Uf)) =
      selOp (Sel := Empty) (a := a) (S := S) (R := R) (fun _ => Uf† ∘L Cf ∘L Uf) := by
  rw [selOp_adjoint, selOp_const_comp, selOp_const_comp]

namespace ClipNative

variable {prim : J → Reg Y R →L[ℂ] Reg Y R} {a : ℕ} {UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)}
  {Z : Type*} [Fintype Z] [DecidableEq Z] {bT bP A : ℕ} {ξ ζ : ℝ}

/-- The selected factor. -/
def Usel (N : ClipNative prim UJ D Z bT bP A ξ ζ) :
    Reg (Empty ⊕ (Fin a ⊕ S)) R →L[ℂ] Reg (Empty ⊕ (Fin a ⊕ S)) R :=
  selOp (fun _ : Cfg Empty => N.Uf)

/-- The selected rotation. -/
def Csel (N : ClipNative prim UJ D Z bT bP A ξ ζ) :
    Reg (Empty ⊕ (Fin a ⊕ S)) R →L[ℂ] Reg (Empty ⊕ (Fin a ⊕ S)) R :=
  selOp (fun _ : Cfg Empty => N.Cf)

theorem Usel_isUnitary (N : ClipNative prim UJ D Z bT bP A ξ ζ) : IsUnitary N.Usel :=
  selOp_isUnitary _ (fun _ => N.unitaryU)

theorem Csel_isUnitary (N : ClipNative prim UJ D Z bT bP A ξ ζ) : IsUnitary N.Csel :=
  selOp_isUnitary _ (fun _ => N.unitaryC)

theorem sel_split (N : ClipNative prim UJ D Z bT bP A ξ ζ) :
    N.Usel† ∘L (N.Csel ∘L N.Usel) = selOp (fun _ : Cfg Empty => D) := by
  rw [Usel, Csel, selOp_split]
  exact congrArg selOp (funext fun _ => N.split.symm)

/-- **The native private call is within `6ξ + 4ζ` of the enable-controlled private operation** on
clean work wires: `3ξ` for each native factor and `4ζ` for the native rotation. -/
theorem pc_approx (hprim : ∀ j, IsUnitary (prim j)) (N : ClipNative prim UJ D Z bT bP A ξ ζ)
    (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) :
    ApproxOn CleanP (nrun prim N.pc) (ctrlIdeal (selOp (fun _ : Cfg Empty => D)))
      (6 * ξ + 4 * ζ) := by
  have hUu := N.Usel_isUnitary
  have hCu := N.Csel_isUnitary
  have hUU : N.Usel† ∘L N.Usel = 1 := by
    have := hUu.1
    rwa [star_eq_adjoint, mul_def] at this
  have hF := factorMacro_valid N.fo N.fpub.valid N.farith.elem N.farith.classical
  have hP := privMacro_valid N.nd N.cpub N.ar N.carith.elem N.carith.classical
  have hPu : IsUnitary (nrun prim (privMacro N.nd N.ar)) := nrun_isUnitary prim hprim _ hP
  have hFiu : IsUnitary (nrun prim (ninv (factorMacro N.fo))) :=
    nrun_isUnitary prim hprim _ (valid_ninv _ hF)
  have h1 := factorMacro_approx prim hprim N.fo N.fpub hξ N.farith N.Usel N.fnative
  have h2 := privMacro_approx prim hprim N.nd N.cpub N.ar hζ N.carith N.Csel N.cnative
  have h3 := factorMacro_inv_approx prim hprim N.fo N.fpub hξ N.farith N.Usel hUu N.fnative
  have hO1u : IsUnitary (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) N.Usel) :=
    localOp_isUnitary _ _ (fun _ => hUu)
  have hO1s : Preserves CleanP (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) N.Usel) :=
    preserves_selPR _
  have h12 : ApproxOn (CleanP (Sel := Empty) (PR := Fin a ⊕ S) (Z := Z) (bT := bT) (bP := bP)
      (A := A)) (nrun prim (privMacro N.nd N.ar) ∘L nrun prim (factorMacro N.fo))
      (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) N.Csel ∘L uncIdeal N.Usel)
      (3 * ξ + 4 * ζ) :=
    ApproxOn.comp h1 hO1s (fun ψ => IsUnitary.norm_apply_le hO1u ψ) h2
      (fun ψ => IsUnitary.norm_apply_le hPu ψ) (by linarith)
  have hO12u : IsUnitary (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) N.Csel ∘L
      uncIdeal N.Usel) := isUnitary_comp (ctrlIdeal_isUnitary N.Csel hCu) hO1u
  have hO12s : Preserves CleanP (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) N.Csel ∘L
      uncIdeal N.Usel) := by
    unfold ctrlIdeal uncIdeal
    rw [localOp_comp]
    exact preserves_selPR _
  have h123 : ApproxOn (CleanP (Sel := Empty) (PR := Fin a ⊕ S) (Z := Z) (bT := bT) (bP := bP)
      (A := A)) (nrun prim (ninv (factorMacro N.fo)) ∘L
        (nrun prim (privMacro N.nd N.ar) ∘L nrun prim (factorMacro N.fo)))
      (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) (N.Usel†) ∘L
        (ctrlIdeal N.Csel ∘L uncIdeal N.Usel)) (3 * ξ + 4 * ζ + 3 * ξ) :=
    ApproxOn.comp h12 hO12s (fun ψ => IsUnitary.norm_apply_le hO12u ψ) h3
      (fun ψ => IsUnitary.norm_apply_le hFiu ψ) (by linarith)
  have hrun : nrun prim N.pc = nrun prim (ninv (factorMacro N.fo)) ∘L
      (nrun prim (privMacro N.nd N.ar) ∘L nrun prim (factorMacro N.fo)) := by
    simp only [pc, nrun_append]
  have hid : uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) (N.Usel†) ∘L
      (ctrlIdeal N.Csel ∘L uncIdeal N.Usel) = ctrlIdeal (selOp (fun _ : Cfg Empty => D)) := by
    rw [ideal_conj N.Usel N.Csel hUU, N.sel_split]
  rw [hrun, ← hid]
  exact h123.mono (by linarith)

end ClipNative

/-! ### The transfer -/

/-- The native circuit of a released circuit with sector-controlled oracle calls and the
factor-conjugated native private call. -/
def clipNativeOf {a m r K : ℕ} {Z : Type*} {bT bP A : ℕ} (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (l : List (Instr (Wire a m r K))) :
    List (NInstr (HW (Wire a m r K) S Empty Z bT bP A) Y J) :=
  hcircP (wireRel a m r K) (noSel _) UJg pc l

/-- **Native transfer with the factor-conjugated native private call**: for every valid released
circuit `l` with sector-controlled oracle calls whose full output is within `ε₀` of a target `U`
(run with `U_J = UJop UJg` and the private operation `D`), the native circuit is valid and unitary,
makes exactly `nPriv l` copies of the primitive calls of `pc`, has at most
`nGates l + 7 C_J nUJ l + nGatesN pc · nPriv l` elementary gates on
`|wires of l| + |S| + |Z| + b_T + b_P + A + 3` wires, and is within `ε₀ + (6ξ + 4ζ) nPriv l` of
`U` on the system embedding. -/
theorem clip_transfer {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j)) {UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)}
    {Z : Type*} [Fintype Z] [DecidableEq Z] {bT bP A : ℕ} {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (N : ClipNative prim UJ D Z bT bP A ξ ζ) (hD : IsUnitary D)
    (l : List (Instr (Wire a m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i)
    (U : Reg S R →L[ℂ] Reg S R) {ε₀ : ℝ}
    (hrel : ‖run (simSem (P := Reg S R) UJ D) l ∘L io - io ∘L U‖ ≤ ε₀) :
    (∀ i ∈ clipNativeOf N.UJg N.pc l, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (clipNativeOf N.UJg N.pc l) = nPriv l * N.calls p) ∧
    nGatesN (clipNativeOf N.UJg N.pc l) ≤ nGates l + nUJ l * (7 * N.UJg.length) +
      nPriv l * nGatesN N.pc ∧
    Fintype.card (HW (Wire a m r K) S Empty Z bT bP A) =
      Fintype.card (Wire a m r K) + Fintype.card S + (Fintype.card Z + bT + bP + A + 3) ∧
    IsUnitary (nrun prim (clipNativeOf N.UJg N.pc l)) ∧
    ‖nrun prim (clipNativeOf N.UJg N.pc l) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L U‖ ≤ ε₀ + (nPriv l : ℝ) * (6 * ξ + 4 * ζ) := by
  unfold clipNativeOf
  rw [← N.boundary] at hrel
  have hpcV := N.pc_valid
  have hvN := hcircP_valid (X' := Empty) (wireRel a m r K) (noSel _) N.UJg N.ok N.pc hpcV l hv
  refine ⟨hvN, fun p => hcircP_nCalls p _ _ N.UJg N.pc l, ?_, ?_,
    nrun_isUnitary prim hprim _ hvN, ?_⟩
  · have h1 := hcircP_nGates (X' := Empty) (wireRel a m r K) (noSel _) N.UJg N.pc l
    have h2 := hcircP_nil_nGates (X' := Empty) (Z := Z) (bT := bT) (bP := bP) (A := A) (Y := Y)
      (J := J) (wireRel a m r K) (noSel _) N.UJg N.ok l
    rw [mul_one] at h2
    omega
  · rw [card_HW]
    simp only [Fintype.card_empty, add_zero]
  · have hDu : ∀ w, IsUnitary (constFam D false w) := fun _ => hD
    have hDadj : ∀ w, constFam D true w = (constFam D false w)† := fun _ => rfl
    have hpc : ApproxOn CleanP (nrun prim N.pc) (ctrlIdeal (selOp (constFam D false)))
        (6 * ξ + 4 * ζ) := N.pc_approx hprim hξ hζ
    have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := m) (r := r) (K := K)) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    exact hcircP_error (X' := Empty) prim hprim (wireRel _ _ _ _) (noSel _) N.UJg N.ok N.pc hpcV
      (by linarith) (constFam D) hDu hDadj hpc l hv io hio U _
      (prodOps_evalSel_const N.UJg D l hsec) hrel

/-- **The native claims of a sector-controlled circuit with the factor-conjugated native private
call**: from the exact-gate claims and the native data. -/
theorem clip_claims (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    {a m r K : ℕ} {UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)} {Z : Type*} [Fintype Z]
    [DecidableEq Z] {bT bP A : ℕ} {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (N : ClipNative prim UJ D Z bT bP A ξ ζ) (hD : IsUnitary D)
    (l : List (Instr (Wire a m r K))) (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i)
    {H : Reg S R →L[ℂ] Reg S R} {t ε Q : ℝ} (hG : GateClaims (P := Reg S R) UJ D l H t ε Q) :
    NativeClaims prim (clipNativeOf N.UJg N.pc l) H t ε Q N.calls N.cost
      (ε + 2 * 10 ^ 11 * Q * (6 * ξ + 4 * ζ)) := by
  obtain ⟨hv, hcalls, hgates, hcard, hu, herr⟩ :=
    clip_transfer prim hprim hξ hζ N hD l hG.valid hsec _ hG.error
  have hpriv := hG.priv
  refine ⟨hv, hu, fun p => ?_, ?_, ?_, hG.mesh, hG.labels, ?_⟩
  · rw [hcalls p]
    have hc : (0 : ℝ) ≤ (N.calls p : ℝ) := Nat.cast_nonneg _
    calc ((nPriv l * N.calls p : ℕ) : ℝ) = (nPriv l : ℝ) * (N.calls p : ℝ) := by push_cast; ring
      _ ≤ 2 * 10 ^ 11 * Q * (N.calls p : ℝ) := mul_le_mul_of_nonneg_right hpriv hc
  · have h1 : (nGatesN (clipNativeOf N.UJg N.pc l) : ℝ) ≤ (nGates l : ℝ) +
        (nUJ l : ℝ) * ((7 * N.UJg.length : ℕ) : ℝ) + (nPriv l : ℝ) * (nGatesN N.pc : ℝ) := by
      exact_mod_cast hgates
    have h2 := mul_le_mul_of_nonneg_right hG.uj (Nat.cast_nonneg (7 * N.UJg.length))
    have h3 := mul_le_mul_of_nonneg_right hpriv (Nat.cast_nonneg (nGatesN N.pc))
    have e : (2 : ℝ) * 10 ^ 11 * Q * (N.cost : ℝ) =
        2 * 10 ^ 11 * Q * ((7 * N.UJg.length : ℕ) : ℝ) + 2 * 10 ^ 11 * Q * (nGatesN N.pc : ℝ) := by
      unfold ClipNative.cost
      push_cast
      ring
    rw [e]
    linarith only [h1, h2, h3, hG.gates]
  · rw [hcard]
    have := hG.wires
    omega
  · have h4 := mul_le_mul_of_nonneg_right hpriv (by linarith : (0 : ℝ) ≤ 6 * ξ + 4 * ζ)
    linarith only [herr, h4]

/-! ### Theorem `gate:thm:main`, native form, with the factor-conjugated clipped call -/

/-- **Theorem `gate:thm:main` (gate-efficient optimal-precision simulation), native form, with the
factor-conjugated native private call in the clipped regime.** As
`GateOptimalPrecision.gate_optimal_native`, with the native data of the clipped regime given as
`ClipNative` (factor arithmetic accuracy `ξ`, angle accuracy `ζ`): the clipped circuit makes
`2·10¹¹ Q_μ` times the primitive calls of one native private call `pc` and has full-output error
`ε + 2·10¹¹ Q_μ (6ξ + 4ζ)`. The native factor of the signed regime has accuracy `ξ`. -/
theorem gate_optimal_native_clip [FiniteDimensional ℂ R] {ZB ZS ZC : Type*} [Fintype ZB]
    [DecidableEq ZB] [Fintype ZS] [DecidableEq ZS] [Fintype ZC] [DecidableEq ZC]
    {bT bP A bT' bP' A' : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    {H : Reg S R →L[ℂ] Reg S R} (hH : star H = H)
    (IB : hval θ ε < 10 ^ 4 → BoundedIface (Reg S R) σ (Real.sqrt s * η) H)
    (NB : ∀ hb : hval θ ε < 10 ^ 4, CayleyNative prim (IB hb).UJ (bdPriv (IB hb).K σ θ ε) ZB ζ)
    (IS : 10 ^ 4 ≤ hval θ ε → σ * θ < Lval ε * hval θ ε →
      SignedIface (Reg S R) (s * μ) (Real.sqrt σ)⁻¹ H)
    (NS : ∀ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      FactorNative prim (IS h1 h2).UJ (IS h1 h2).U ZS bT bP A ξ)
    (IC : Regime σ θ ε → ClippedIface (Reg S R) σ θ ε (s * μ / qval σ θ ε) H)
    (NC : ∀ Rg : Regime σ θ ε, ClipNative prim (IC Rg).UJ (IC Rg).D ZC bT' bP' A' ξ ζ) :
    (∃ hb : hval θ ε < 10 ^ 4,
      NativeClaims prim (nativeOf (NB hb).UJg (NB hb).nd (NB hb).ar (bdSigned (IB hb).a σ θ ε t))
        H t ε (Qmu s η μ t ε) (NB hb).calls (NB hb).cost
        (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (4 * ζ))) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ ε) (h2 : σ * θ < Lval ε * hval θ ε),
      NativeClaims prim
        (factorNativeOf (NS h1 h2).UJg (NS h1 h2).fo
          (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * μ) (Real.sqrt σ)⁻¹ t ε)) H t ε
        (Qmu s η μ t ε) (NS h1 h2).calls (NS h1 h2).cost
        (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (3 * ξ))) ∨
    (∃ Rg : Regime σ θ ε,
      NativeClaims prim (clipNativeOf (NC Rg).UJg (NC Rg).pc (clipSigned (IC Rg).a σ θ ε t)) H t ε
        (Qmu s η μ t ε) (NC Rg).calls (NC Rg).cost
        (ε + 2 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ))) := by
  rcases gate_optimal_simulation hμη hηs hσ hθd hθ hε hε1 hH IB IS IC with
    ⟨hh, hG⟩ | ⟨hh, hc, hG⟩ | ⟨Rg, hG⟩
  · exact Or.inl ⟨hh, cayley_claims prim hprim hζ (NB hh)
      (cayleyGate_isUnitary (scaled_self_adjoint (IB hh).K _ (IB hh).self)) _
      (secOK_bdSigned _ _ _ _ _) hG⟩
  · exact Or.inr (Or.inl ⟨hh, hc, factor_claims prim hprim hξ (NS hh hc) (IS hh hc).unitaryU _
      (uncOK_sgCircuit _ _ _ _ _ _ _) hG⟩)
  · exact Or.inr (Or.inr ⟨Rg, clip_claims prim hprim hξ hζ (NC Rg) (IC Rg).unitaryD _
      (secOK_clipSigned _ _ _ _ _) hG⟩)

/-- **Theorem `gate:thm:main`, native form with the factor-conjugated clipped call, total error
`ε`**: the exact-gate construction at accuracy `ε/2` and the arithmetic accuracies `ξ`, `ζ` with
`8·10¹¹ Q_μ (6ξ + 4ζ) ≤ ε` (`Q_μ` at `ε`); the native circuit of each regime satisfies
`NativeClaims` at `ε/2` with the count parameter `2 Q_μ`, and its full output is within `ε` of
`e^{-itH}`. -/
theorem gate_optimal_native_clip_total [FiniteDimensional ℂ R] {ZB ZS ZC : Type*} [Fintype ZB]
    [DecidableEq ZB] [Fintype ZS] [DecidableEq ZS] [Fintype ZC] [DecidableEq ZC]
    {bT bP A bT' bP' A' : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    {ξ ζ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ) {s : ℕ} {η μ t ε σ θ : ℝ}
    (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2)
    (hθd : θ = η ^ 2 * |t| / μ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 32)
    (hδε : 8 * 10 ^ 11 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) ≤ ε)
    {H : Reg S R →L[ℂ] Reg S R} (hH : star H = H)
    (IB : hval θ (ε / 2) < 10 ^ 4 → BoundedIface (Reg S R) σ (Real.sqrt s * η) H)
    (NB : ∀ hb : hval θ (ε / 2) < 10 ^ 4,
      CayleyNative prim (IB hb).UJ (bdPriv (IB hb).K σ θ (ε / 2)) ZB ζ)
    (IS : 10 ^ 4 ≤ hval θ (ε / 2) → σ * θ < Lval (ε / 2) * hval θ (ε / 2) →
      SignedIface (Reg S R) (s * μ) (Real.sqrt σ)⁻¹ H)
    (NS : ∀ (h1 : 10 ^ 4 ≤ hval θ (ε / 2)) (h2 : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      FactorNative prim (IS h1 h2).UJ (IS h1 h2).U ZS bT bP A ξ)
    (IC : Regime σ θ (ε / 2) →
      ClippedIface (Reg S R) σ θ (ε / 2) (s * μ / qval σ θ (ε / 2)) H)
    (NC : ∀ Rg : Regime σ θ (ε / 2), ClipNative prim (IC Rg).UJ (IC Rg).D ZC bT' bP' A' ξ ζ) :
    (∃ hb : hval θ (ε / 2) < 10 ^ 4,
      NativeClaims prim
        (nativeOf (NB hb).UJg (NB hb).nd (NB hb).ar (bdSigned (IB hb).a σ θ (ε / 2) t)) H t
        (ε / 2) (2 * Qmu s η μ t ε) (NB hb).calls (NB hb).cost ε) ∨
    (∃ (h1 : 10 ^ 4 ≤ hval θ (ε / 2)) (h2 : σ * θ < Lval (ε / 2) * hval θ (ε / 2)),
      NativeClaims prim
        (factorNativeOf (NS h1 h2).UJg (NS h1 h2).fo
          (sgCircuit (IS h1 h2).a (IS h1 h2).f (IS h1 h2).z (s * μ) (Real.sqrt σ)⁻¹ t (ε / 2)))
        H t (ε / 2) (2 * Qmu s η μ t ε) (NS h1 h2).calls (NS h1 h2).cost ε) ∨
    (∃ Rg : Regime σ θ (ε / 2),
      NativeClaims prim
        (clipNativeOf (NC Rg).UJg (NC Rg).pc (clipSigned (IC Rg).a σ θ (ε / 2) t)) H t
        (ε / 2) (2 * Qmu s η μ t ε) (NC Rg).calls (NC Rg).cost ε) := by
  have hε' : 0 < ε / 2 := by linarith
  have hε1' : ε / 2 ≤ 1 / 64 := by linarith
  obtain ⟨hμ, hη, -, -, hST, hSq⟩ := two_norm_params hμη hηs hσ hθd hθ
  have hQ0 := Qmu_nonneg hθd hST hSq hθ hε' hε1'
  have hQle : Qmu s η μ t (ε / 2) ≤ 2 * Qmu s η μ t ε :=
    Qmu_half_le hη.le hμ (by rw [← hθd]; linarith) hε (by linarith)
  have hδ : 0 ≤ 6 * ξ + 4 * ζ := by linarith
  have hδQ : Qmu s η μ t (ε / 2) * (6 * ξ + 4 * ζ) ≤ 2 * Qmu s η μ t ε * (6 * ξ + 4 * ζ) :=
    mul_le_mul_of_nonneg_right hQle hδ
  have hQ1 : 0 ≤ Qmu s η μ t (ε / 2) * ξ := mul_nonneg hQ0 hξ
  have hQ2 : 0 ≤ Qmu s η μ t (ε / 2) * ζ := mul_nonneg hQ0 hζ
  have h6 : ε / 2 + 2 * 10 ^ 11 * Qmu s η μ t (ε / 2) * (6 * ξ + 4 * ζ) ≤ ε := by nlinarith
  have h4 : ε / 2 + 2 * 10 ^ 11 * Qmu s η μ t (ε / 2) * (4 * ζ) ≤ ε := by nlinarith
  have h3 : ε / 2 + 2 * 10 ^ 11 * Qmu s η μ t (ε / 2) * (3 * ξ) ≤ ε := by nlinarith
  rcases gate_optimal_native_clip prim hprim hξ hζ hμη hηs hσ hθd hθ hε' hε1' hH IB NB IS NS IC NC
    with ⟨hh, hN⟩ | ⟨h1, h2, hN⟩ | ⟨Rg, hN⟩
  · exact Or.inl ⟨hh, hN.weaken hε' hQ0 hQle h4⟩
  · exact Or.inr (Or.inl ⟨h1, h2, hN.weaken hε' hQ0 hQle h3⟩)
  · exact Or.inr (Or.inr ⟨Rg, hN.weaken hε' hQ0 hQle h6⟩)

end

end GateOptimalBinary
