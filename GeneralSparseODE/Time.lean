import GeneralSparseODE.Constant
import GeneralSparseODE.SubstSlot
import SourceAccuracyODE.Time

/-!
# The time-dependent gate solver for sparse access of general size

The released time-dependent gate solver from time-indexed binary sparse data
(`ZeroTimeGateODE.btprepC`, `SourceAccuracyODE.binary_time_outcome_nonneg`, represented samples of
any sign) on the padded data of a time-indexed general sparse access
`D : GeneralSparseAccess.QData (X × Fin (2^m)) N s k b` (the sample of slot `r` on input `x` is
`D.matrix (x, r)`; `QData.padData`: `k + 1`-bit index words, `2^⌈log₂ s⌉` slots, the stored words
decoded by `val = c₀(X + iY)`), with

* the coherent sampled-time supplied oracles `primsTG D x = Σ_w |w⟩⟨w| ⊗ D.prims (x, w)`
  (`GateBinary.slotPrim`), which the protocol and the source circuits call;
* the private operation calling them: every padded call of the released compute circuit replaced
  by the implementation `GeneralSparseAccess.implP` from the supplied oracles, the ancillas added
  to its scratch, every call also reading the slot wires (`GPubT.nd`, `substSlot`);
* the arithmetic of the released solver on the base wires (`GPubT.ar`, `liftA`);
* the loading circuit of the general problem on the `k` qubits of the index register, placed on the
  low wires of the padded system register (`liftC`), and the weight-preparation circuit unchanged.

`GPubT` is the public data: the index bits `k`, the sparsity `s ≤ 2^k`, the stored bits and the
public parameters of `GateBinaryODETime.PubT` (`GPubT.pub`: `k + 1` system qubits, `⌈log₂ s⌉`
slot bits). `GPubT.prep`: the direct source assembly in the zero case
(`ZeroTimeGateODE.BTZeroCase`), the native preparation otherwise.

`RobustRestG`: the remaining instance conditions of `RepresentedSampleODE.GateTime.RobustRest` on
the index register (loading, weight preparation, generator path, forcing, solution, the budgets),
with the generator path within `δ_G` of the lifts `padLift D (x, r)` of the samples extended by
zero to the `2^k` index words; `RobustRestG.padded` transfers them to the padded problem along the
marker embedding (`Embed`).

`general_time_outcome`: for every input whose samples have the released energy bounds, loading and
weight-preparation circuits within `ζ_s` and the source budget `98304 q* ζ + 3 ζ_s ≤ 13 ν` of
`SourceAccuracyODE`, and the conditions `RobustRestG`, the protocol `nprotocol (q.prep N z₀ loadC
wpC) (2g)` has the guarantees `WOutcome … (ε / 100)` for the supplied oracles, against the marker
embedding of `x(T)`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.OracleCircuit
open GateBinaryODE (SZ4 mLift computeV4 computeV4_valid computeV4_nGates computeV4_nCalls oW
  elift4 act4 nativeOK4 hadUJ4_ok)
open GateBinaryODETime (PubT privFamT privFamT_word decOK_T HsT LsT)
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase tzprepC btpublicOK_of btparams_ok0
  btzeroCase_params)
open SourceAccuracyODE (WOutcome)
open RepresentedSampleODE.GateTime (RobustRest robust_instanceOK robust_tzInstanceOK repairedLs)
open GatePointerEncoding (wordValue wordEquivFin)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct

/-! ### The coherent sampled-time supplied oracles -/

section Prims

variable {X : Type*} {N s k b m : ℕ}

/-- **The coherent sampled-time supplied oracles**: at the slot word `w` of the slot wires, the
supplied oracles of the sample `wordEquivFin m w`. -/
def primsTG (D : QData (X × Fin (2 ^ m)) N s k b) (x : X) :
    Query → Reg (Fin m ⊕ PY k b) ℂ →L[ℂ] Reg (Fin m ⊕ PY k b) ℂ :=
  slotPrim (fun w => D.prims (R := ℂ) (x, wordEquivFin m w))

theorem primsTG_isUnitary (D : QData (X × Fin (2 ^ m)) N s k b) (x : X) (j : Query) :
    IsUnitary (primsTG D x j) :=
  slotPrim_isUnitary _ (fun w j => D.prims_isUnitary (x, wordEquivFin m w) j) j

end Prims

/-! ### The public data -/

/-- **The public data of the time-dependent solver for sparse access of general size**: the index
bits `k`, the sparsity `s ≤ 2^k`, the stored bits `b` and the public parameters of the solver from
time-indexed binary data (mesh exponent `m`). -/
structure GPubT where
  /-- The index bits of the general access (`N ≤ 2^k`). -/
  k : ℕ
  /-- The sparsity. -/
  s : ℕ
  /-- The sparsity fits the index register. -/
  hs : s ≤ 2 ^ k
  /-- The stored bits of each component. -/
  b : ℕ
  /-- The decoder scale. -/
  c0 : ℝ
  /-- The energy bound of the Hamiltonian part of every sample. -/
  etaH : ℝ
  /-- The energy bound of the dissipative part of every sample. -/
  etaD : ℝ
  /-- The Cayley rescaling. -/
  γ : ℝ
  /-- The time. -/
  T : ℝ
  /-- The public amplification bound. -/
  g : ℝ
  /-- The accuracy. -/
  ε : ℝ
  /-- The time-slot bits: `2^m` time slots. -/
  m : ℕ
  /-- The arithmetic accuracy. -/
  ζ : ℝ

namespace GPubT

variable (q : GPubT)

/-- **The public data of the padded problem**: `k + 1` system qubits and `⌈log₂ s⌉` slot bits. -/
def pub : PubT where
  kx := q.k + 1
  σ := sbP q.s
  hσ := (sbP_le q.hs).trans (Nat.le_succ q.k)
  b := q.b
  c0 := q.c0
  etaH := q.etaH
  etaD := q.etaD
  γ := q.γ
  T := q.T
  g := q.g
  ε := q.ε
  m := q.m
  ζ := q.ζ

/-- **The private operation calling the supplied oracles**: the released label- and slot-selected
operation of the padded problem with every padded call replaced by its implementation from the
supplied oracles (`substSlot`). -/
def nd (N : ℕ) (z₀ : Cfg (VW q.b)) :
    NativeOp (TSel q.pub.params.m q.pub.params.l q.pub.params.m)
      (Fin q.pub.params.a ⊕ Fin (q.k + 1)) (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)
      (Fin q.m ⊕ PY q.k q.b) Query :=
  substSlot (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1)) q.pub.nd.dec
    (implP N q.s z₀)

/-- **The arithmetic** of the released operation on the base wires. -/
def ar : Arith (NB (TSel q.pub.params.m q.pub.params.l q.pub.params.m)
    (Fin q.pub.params.a ⊕ Fin (q.k + 1)) (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b)) :=
  liftA q.pub.ar

/-- **The preparation of the general problem**: the direct source assembly in the zero case, the
native preparation with the operation calling the supplied oracles otherwise; the loading circuit
on the low wires of the padded system register. -/
def prep {Zs : Type*} [Fintype Zs] [DecidableEq Zs] (N : ℕ) (z₀ : Cfg (VW q.b))
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query)) :
    List (NInstr (TNW q.pub.params (Fin (q.k + 1)) Zs
      (SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) q.ar.bT q.ar.bP q.ar.A)
      (Fin q.m ⊕ PY q.k q.b) Query) :=
  if BTZeroCase q.pub then tzprepC (liftC loadC) wpC
  else tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC

theorem nd_public (N : ℕ) (z₀ : Cfg (VW q.b)) : (q.nd N z₀).Public :=
  substSlot_public _ (computeV4_valid _ _ _ _) _ _ q.pub.nd_public.dec_indep (valid_implP N q.s z₀)

theorem ar_ok (hq : q.pub.OK) (N : ℕ) (z₀ : Cfg (VW q.b)) :
    ArithOK q.ar (Sum.inl (Sum.inr (q.nd N z₀).o)) (q.nd N z₀).dec q.ζ :=
  arithOK_liftA q.pub.ar _ _ _ (q.pub.ar_ok hq)

/-- The compute circuit has at most `28 (k + 1) + 2 + 6 implG k b` gates. -/
theorem nd_nGates (N : ℕ) (z₀ : Cfg (VW q.b)) :
    nGatesN (q.nd N z₀).V ≤ 28 * (q.k + 1) + 2 + implG q.k q.b * 6 := by
  have h := nGatesN_substSlot_le (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
    q.pub.nd.dec (implP N q.s z₀) (implG q.k q.b) (nGatesN_implP_le N q.s z₀)
  have hg : nGatesN (computeV4 (q.k + 1) q.b q.m q.pub.params.l) = 28 * (q.k + 1) + 2 :=
    computeV4_nGates (q.k + 1) q.b q.m q.pub.params.l
  have hc : nCallsN (fun _ => true) (computeV4 (q.k + 1) q.b q.m q.pub.params.l) = 6 := by
    have := computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.m) (lq := q.pub.params.l)
      (fun _ => true)
    simp only [if_true] at this
    exact this
  rw [hg, hc] at h
  exact h

/-- The compute circuit makes at most `6` supplied calls of each kind it calls. -/
theorem nd_nCalls (N : ℕ) (z₀ : Cfg (VW q.b)) (c : Query → Bool) :
    nCallsN c (q.nd N z₀).V ≤ 6 * ((if c Query.rowLocation then 1 else 0) +
      (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0)) := by
  have h := nCallsN_substSlot_le (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
    q.pub.nd.dec (kindOK_implP (k := q.k) (b := q.b) N q.s z₀) c
  have hc := computeV4_nCalls (k := q.k + 1) (b := q.b) (kq := q.m) (lq := q.pub.params.l) c
  have h' : nCallsN c (q.nd N z₀).V ≤ 3 * nCallsN c (computeV4 (q.k + 1) q.b q.m q.pub.params.l) :=
    h
  rw [hc] at h'
  omega

variable {X : Type*} {N : ℕ}

/-- **The native identity of the operation calling the supplied oracles**: for the decoder
`c₀(X + iY)` and a public word `z₀` decoded as `0`, `V† R_val V` acts on clean scratch, for the
coherent sampled-time supplied oracles, as the label- and slot-selected family `privFamT` of the
padded data. -/
theorem nativeOK (hq : q.pub.OK) (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b)
    (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0) (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z)
    (x : X) :
    NativeOK (primsTG D x) (q.nd N z₀)
      (selOp (tlabFam (P := Reg (Fin (q.k + 1)) ℂ)
        (privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl (Cfg (Fin (q.k + 1)))) x q.pub.rho
          q.pub.γ) false)) := by
  have hrange := padData_range D z₀ hz₀
  have hdecP : ∀ e z, (D.padData z₀ hz₀).decode e z = (q.pub.c0 : ℂ) * gauss z := fun e z =>
    (padData_decode D z₀ hz₀ e z).trans (hdec z)
  obtain ⟨k0, hk0⟩ : ∃ m, (D.padData z₀ hz₀).slot m = zIdx (Equiv.refl (Cfg (Fin (q.k + 1)))) := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  have hOK : ∀ w : Cfg (Fin q.m),
      NativeOK (prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w))
        (GateBinaryODETime.atSlot2 (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (oW (q.k + 1))
          q.pub.nd.dec w)
        (selOp (labFam (fun z => elift4 (R := ℂ) (Equiv.refl _)
          (act4 (D.padData z₀ hz₀) (x, wordEquivFin q.m w) (q.pub.params.nodeW z.2) q.pub.rho
            (q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1) (wordValue w)))) false)) := by
    intro w
    exact nativeOK4 (kq := q.m) (lq := q.pub.params.l) (D.padData z₀ hz₀) (Equiv.refl _) k0 hk0
      (x, wordEquivFin q.m w) (fun z => q.pub.params.nodeW z.2)
      (fun z => q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1) (wordValue w)) q.pub.rho _
      rfl rfl
      (GateBinaryODETime.atSlot2_public _ (computeV4_valid _ _ _ _) _ _ q.pub.nd_public.dec_indep w)
      (decOK_T q.pub.params (D.padData z₀ hz₀) (Equiv.refl _) k0 x q.c0 hq.c0_pos.ne' hdecP
        q.pub.rho q.pub.γ (q.pub.rho_pos hq).ne' q.pub.F
        (GateBinaryODETime.hRoundT_ne q.pub.params q.pub.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos
          (q.pub.ε_le_one hq) (q.pub.TD_nonneg hq)) w)
  have h := nativeOK_substSlot (fun w => D.prims (R := ℂ) (x, wordEquivFin q.m w))
    (fun w => prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w))
    (fun w j => D.prims_isUnitary (x, wordEquivFin q.m w) j)
    (fun w j => prims_isUnitary (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w) j)
    (fun w => implOK D z₀ hz₀ (x, wordEquivFin q.m w))
    (computeV4 (q.k + 1) q.b q.m q.pub.params.l) (computeV4_valid _ _ _ _) (oW (q.k + 1))
    q.pub.nd.dec q.pub.nd_public.dec_indep
    (fun w => labFam (fun z => elift4 (R := ℂ) (Equiv.refl _)
      (act4 (D.padData z₀ hz₀) (x, wordEquivFin q.m w) (q.pub.params.nodeW z.2) q.pub.rho
        (q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1) (wordValue w)))) false) hOK
  have hfam : (fun y : Cfg (TSel q.pub.params.m q.pub.params.l q.pub.params.m) =>
      labFam (fun z => elift4 (R := ℂ) (Equiv.refl _) (act4 (D.padData z₀ hz₀)
        (x, wordEquivFin q.m (fun i => y (Sum.inr i))) (q.pub.params.nodeW z.2) q.pub.rho
          (q.pub.γ * TimeDependentODE.mask (q.pub.params.start z.1)
            (wordValue (fun i => y (Sum.inr i)))))) false (fun s => y (Sum.inl s))) =
      tlabFam (P := Reg (Fin (q.k + 1)) ℂ)
        (privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl (Cfg (Fin (q.k + 1)))) x q.pub.rho
          q.pub.γ) false := by
    funext y
    simp only [labFam, tlabFam, GateODE.adjIf, SlotSim.adjT, Bool.false_eq_true, if_false]
    rw [privFamT_word]
    rfl
  exact (congrArg (fun F => NativeOK (primsTG D x) (q.nd N z₀) (selOp F)) hfam).mp h

end GPubT

/-! ### The source data along the marker embedding -/

section Source

variable {k : ℕ}

theorem zsrc_markEmb (p : GateODE.Time.TParams) (x0 : Reg (Fin k) ℂ) (bs : ℕ → Reg (Fin k) ℂ)
    (s : Bool × (Fin p.m → Bool)) :
    p.zsrc (markEmb k x0) (fun r => markEmb k (bs r)) s = markEmb k (p.zsrc x0 bs s) := by
  unfold GateODE.Time.TParams.zsrc
  split_ifs
  · exact (map_smul _ _ _).symm
  · rfl
  · exact (map_zero _).symm

theorem mass_markEmb (p : GateODE.Time.TParams) (x0 : Reg (Fin k) ℂ) (bs : ℕ → Reg (Fin k) ℂ) :
    p.mass (markEmb k x0) (fun r => markEmb k (bs r)) = p.mass x0 bs := by
  unfold GateODE.Time.TParams.mass ODESourceBranches.mass
  apply Finset.sum_congr rfl
  intro s _
  rw [zsrc_markEmb, norm_markEmb]

theorem srcAmp_markEmb (p : GateODE.Time.TParams) (x0 : Reg (Fin k) ℂ) (bs : ℕ → Reg (Fin k) ℂ)
    (s : Bool × (Fin p.m → Bool)) :
    p.srcAmp (markEmb k x0) (fun r => markEmb k (bs r)) s = p.srcAmp x0 bs s := by
  unfold GateODE.Time.TParams.srcAmp
  rw [zsrc_markEmb, norm_markEmb, mass_markEmb]

end Source

/-! ### The instance conditions on the index register -/

section Rest

variable {X : Type*} {N : ℕ}

/-- **The remaining instance conditions on the index register** (represented samples of any sign):
those of `RepresentedSampleODE.GateTime.RobustRest` for the loading `Jl`, the generator path `G`,
the forcing `b`, the solution `x` and the forcing samples `b_r` on the `k` qubits of the index
register, with the generator path within `δ_G` of the lifts `padLift D (x, r)` of the samples
extended by zero to the `2^k` index words at the slot times, for the released public parameters
`q.pub.params` of the padded problem: the source amplitudes, the mass, the radius `R` and `ν` do not
depend on the sparsity, and the discretisation condition `disc` has the parameters
`λ_H = √(4s') η_H / γ`, `λ_D = √(4s') η_D / γ` of the `s' = 2^⌈log₂ s⌉` padded slots. The conditions
depend on the sparse access `D` (of any stored bits `b`) only through the lifts `padLift D (x, r)`
of its matrix. -/
structure RobustRestG (q : GPubT) {b : ℕ} (D : QData (X × Fin (2 ^ q.m)) N q.s q.k b) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (bf xs : ℝ → Reg (Fin q.k) ℂ)
    (bs : ℕ → Reg (Fin q.k) ℂ) (βG δG βb δb bmax : ℝ) : Prop where
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) = ((q.pub.params.srcAmp (xs 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : xs 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.k)) = unitDirection (xs 0)
  forcing_load : ∀ w : Fin q.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.k)) = unitDirection (bs (wordValue w))
  solves : TimeDependentODE.SolvesODE G bf xs 0 q.T
  accretive : ∀ u ∈ Set.Icc 0 q.T, TimeDependentODE.Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  sampleG : ∀ (r : ℕ) (hr : r < 2 ^ q.m),
    ‖G (r * q.T / ((2 ^ q.m : ℕ) : ℝ)) - padLift D (x, ⟨r, hr⟩)‖ ≤ δG
  lipb : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖bf u - bf u'‖ ≤ βb * |u - u'|
  sampleb : ∀ r : ℕ, r < 2 ^ q.m → ‖bf (r * q.T / ((2 ^ q.m : ℕ) : ℝ)) - bs r‖ ≤ δb
  boundb : ∀ u ∈ Set.Icc 0 q.T, ‖bf u‖ ≤ bmax
  βG_nonneg : 0 ≤ βG
  βb_nonneg : 0 ≤ βb
  target_ne : xs q.T ≠ 0
  budget : q.pub.params.mass (xs 0) bs ≤ q.g * ‖xs q.T‖
  disc : q.pub.params.discretisation βG (3 * δG) βb δb bmax ‖xs 0‖ ≤
    q.ε * q.pub.params.mass (xs 0) bs / (2000 * q.g)
  branch : 6 * q.pub.params.R * q.T * δG ≤ q.pub.params.nu

/-- **The instance conditions of the padded problem**: the conditions on the index register give
those of `RobustRest` for the padded data along the marker embedding (the loading on the low wires,
the zero extension of the generator path, the marker embeddings of the forcing, the solution and
the forcing samples). -/
theorem RobustRestG.padded {q : GPubT} {D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b} {x : X}
    {Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ}
    {Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ}
    {G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ} {bf xs : ℝ → Reg (Fin q.k) ℂ}
    {bs : ℕ → Reg (Fin q.k) ℂ} {βG δG βb δb bmax : ℝ} (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hR : RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax) :
    RobustRest q.pub (D.padData z₀ hz₀) (Equiv.refl _) x (fun c => lowOp (Jl c)) Wp
      (fun u => zext (G u)) (fun u => markEmb q.k (bf u)) (fun u => markEmb q.k (xs u))
      (fun r => markEmb q.k (bs r)) βG δG βb δb bmax := by
  have hseed : ∀ c, lowOp (Jl c) (seedV (S := Fin (q.k + 1))) =
      markEmb q.k (Jl c (seedV (S := Fin q.k))) := by
    intro c
    rw [seedV_markEmb, ← comp_apply, lowOp_markEmb, comp_apply]
  have hne0 : ∀ y : Reg (Fin q.k) ℂ, markEmb q.k y ≠ 0 → y ≠ 0 := by
    intro y hy h0
    apply hy
    rw [h0, map_zero]
  refine ⟨fun c => lowOp_isUnitary (hR.load_unitary c), hR.prep_left, hR.prep_right, ?_, ?_, ?_,
    solves_zext hR.solves, fun u hu => accretive_zext (hR.accretive u hu), ?_, ?_, ?_, ?_, ?_,
    hR.βG_nonneg, hR.βb_nonneg, ?_, ?_, ?_, hR.branch⟩
  · intro w
    have h := hR.prep w
    rw [← srcAmp_markEmb] at h
    exact h
  · intro hx
    show lowOp (Jl (false, fun _ => false)) (seedV (S := Fin (q.k + 1))) =
      unitDirection (markEmb q.k (xs 0))
    rw [unitDirection_markEmb, ← hR.init_load (hne0 _ hx)]
    exact hseed _
  · intro w hw
    have hw' : bs (wordValue (r := q.m) w) ≠ 0 := hne0 _ hw
    have e : lowOp (Jl (true, w)) (seedV (S := Fin (q.k + 1))) =
        markEmb q.k (unitDirection (bs (wordValue (r := q.m) w))) := by
      rw [← hR.forcing_load w hw']
      exact hseed _
    rw [← unitDirection_markEmb] at e
    exact e
  · intro u hu u' hu'
    show ‖zext (G u) - zext (G u')‖ ≤ βG * |u - u'|
    rw [zext_sub]
    exact (norm_zext_le _).trans (hR.lipG u hu u' hu')
  · intro r hr
    show ‖zext (G (r * q.T / ((2 ^ q.m : ℕ) : ℝ))) -
      mLift (D.padData z₀ hz₀) (Equiv.refl _) (x, ⟨r, hr⟩)‖ ≤ δG
    rw [mLift_padData, zext_sub]
    exact (norm_zext_le _).trans (hR.sampleG r hr)
  · intro u hu u' hu'
    show ‖markEmb q.k (bf u) - markEmb q.k (bf u')‖ ≤ βb * |u - u'|
    rw [← map_sub, norm_markEmb]
    exact hR.lipb u hu u' hu'
  · intro r hr
    show ‖markEmb q.k (bf (r * q.T / ((2 ^ q.m : ℕ) : ℝ))) - markEmb q.k (bs r)‖ ≤ δb
    rw [← map_sub, norm_markEmb]
    exact hR.sampleb r hr
  · intro u hu
    show ‖markEmb q.k (bf u)‖ ≤ bmax
    rw [norm_markEmb]
    exact hR.boundb u hu
  · intro h0
    apply hR.target_ne
    have h1 : markEmb q.k (xs q.T) = 0 := h0
    have := congrArg (lowPart q.k) h1
    rwa [← comp_apply (lowPart q.k) (markEmb q.k), lowPart_markEmb, map_zero] at this
  · show q.pub.params.mass (markEmb q.k (xs 0)) (fun r => markEmb q.k (bs r)) ≤
      q.g * ‖markEmb q.k (xs q.T)‖
    rw [mass_markEmb, norm_markEmb]
    exact hR.budget
  · show q.pub.params.discretisation βG (3 * δG) βb δb bmax ‖markEmb q.k (xs 0)‖ ≤
      q.ε * q.pub.params.mass (markEmb q.k (xs 0)) (fun r => markEmb q.k (bs r)) / (2000 * q.g)
    rw [norm_markEmb, mass_markEmb]
    exact hR.disc

end Rest

/-! ### The outcome -/

section Outcome

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general time-dependent solver** (every `T ≥ 0`, represented samples of any
sign): for public data with `BTPublicOK0 q.pub` and the public rescaling outside the zero case,
time-indexed sparse access of general size with the decoder `c₀(X + iY)`, a public word `z₀`
decoded as `0`, every input whose samples have the released energy bounds on `ℂ^N`, loading and
weight-preparation circuits calling the coherent sampled-time supplied oracles within `ζ_s` of the
controlled loading of `J_l` on the `k`-qubit index register and of `W_p`, the source budget
`98304 q* ζ + 3 ζ_s ≤ 13 ν` and the conditions `RobustRestG`, the protocol
`nprotocol (q.prep N z₀ loadC wpC) (2g)` has the guarantees `WOutcome … (ε / 100)` for the
supplied oracles, against the marker embedding of `x(T)`. -/
theorem general_time_outcome (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ) (bf xs : ℝ → Reg (Fin q.k) ℂ)
    (bs : ℕ → Reg (Fin q.k) ℂ) (βG δG βb δb bmax ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 13 * q.pub.params.nu)
    (hR : RobustRestG q D x Jl Wp G bf xs bs βG δG βb δb bmax) :
    WOutcome (q.prep N z₀ loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (primsTG D x) (markEmb q.k (xs q.T)) := by
  -- the padded data and the padded instance
  have hrange := padData_range D z₀ hz₀
  have hrH' : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro r i
    rw [padData_zpad, hamiltonianPart_zpad]
    exact zpad_row_le D.hN _ (hrH r) i
  have hcH' : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro r j
    rw [padData_zpad, hamiltonianPart_zpad]
    exact zpad_col_le D.hN _ (hcH r) j
  have hrD' : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaD ^ 2 := by
    intro r i
    rw [padData_zpad, dissipativePart_zpad]
    exact zpad_row_le D.hN _ (hrD r) i
  have hcD' : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaD ^ 2 := by
    intro r j
    rw [padData_zpad, dissipativePart_zpad]
    exact zpad_col_le D.hN _ (hcD r) j
  have hR' := hR.padded z₀ hz₀
  have hloadV' : ∀ i ∈ liftC loadC, i.Valid := valid_liftC _ hloadV
  have hload' : ApproxOn CleanX (nrun (primsTG D x) (liftC loadC))
      (liftB (loadIdeal (fun c => lowOp (Jl c)))) ζs :=
    approxOn_liftLoad (primsTG D x) loadC Jl hζs hload
  have hε0 : (0 : ℝ) < q.ε := hq.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hq.ε_half
  have hg1 : (1 : ℝ) ≤ q.g := hq.g_ge
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith
  have hQ1 : 1 ≤ GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg
      (by linarith) hε2 (by linarith)
  by_cases hz : BTZeroCase q.pub
  · -- the direct source assembly
    have hp := btparams_ok0 hq
    have hpr : q.prep N z₀ loadC wpC = tzprepC (liftC loadC) wpC := by
      rw [GPubT.prep, if_pos hz]
      rfl
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        q.ζ := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hI := robust_tzInstanceOK q.pub hq (D.padData z₀ hz₀) (Equiv.refl _) x hrH' hcH' hrD'
      hcD' (fun c => lowOp (Jl c)) Wp (fun u => zext (G u)) (fun u => markEmb q.k (bf u))
      (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r)) βG δG βb δb bmax hR'
    rw [hpr]
    exact SourceAccuracyODE.native_time_zero_outcome (S := Fin (q.k + 1)) (Zs := Zs)
      (Z := SZ4 (q.k + 1) q.b ⊕ GeneralSparseAccess.AW q.k q.b) (Y := Fin q.m ⊕ PY q.k q.b)
      (J := Query) q.pub.params q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K
      q.pub.params.l q.pub.params.f q.ar.bT q.ar.bP q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos
      hq.ε_half hp.lamH_nonneg hp.lamD_nonneg (btzeroCase_params hq hz) (liftC loadC) hloadV' wpC
      hwpV (primsTG D x) (fun c => lowOp (Jl c)) Wp (HsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (repairedLs (LsT (D.padData z₀ hz₀) (Equiv.refl _) x) δG) (fun u => zext (G u))
      (fun u => markEmb q.k (bf u)) (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r))
      βG (3 * δG) βb δb bmax ζs (primsTG_isUnitary D x) hζs hload' hwp (by linarith) hI
  · -- the native preparation
    have hP := btpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -⟩ := GateODEBudget.binary_ode_time_sizes q.pub hP (hγ hz)
    have hd' : (q.pub.params.d : ℝ) ≤
        4096 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := hd
    have hpr : q.prep N z₀ loadC wpC =
        tnprepC q.pub.params q.pub.UJg (q.nd N z₀) q.ar (liftC loadC) wpC := by
      rw [GPubT.prep, if_neg hz]
    have hbud' : 24 * (q.pub.params.d : ℝ) * q.ζ + 3 * ζs ≤ 13 * q.pub.params.nu := by
      have hζ0 : (0 : ℝ) ≤ q.ζ := hP.ζ_pos.le
      have := mul_le_mul_of_nonneg_right hd' hζ0
      linarith
    rw [hpr]
    exact SourceAccuracyODE.native_time_outcome q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (q.nd N z₀) (q.nd_public N z₀) q.ar q.ζ hP.ζ_pos.le
      (q.ar_ok hP N z₀) (liftC loadC) hloadV' wpC hwpV (primsTG D x) (primsTG_isUnitary D x)
      ⟨UJop (R := ℂ) q.pub.UJg,
        privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl _) x q.pub.rho q.pub.γ,
        fun c => lowOp (Jl c), Wp⟩
      rfl (q.nativeOK hP D z₀ hz₀ hdec x) ζs hζs hload' hwp hbud'
      (HsT (D.padData z₀ hz₀) (Equiv.refl _) x) (LsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (fun u => zext (G u)) (fun u => markEmb q.k (bf u)) (fun u => markEmb q.k (xs u))
      (fun r => markEmb q.k (bs r)) βG δG βb δb bmax
      (robust_instanceOK q.pub hP (D.padData z₀ hz₀) (Equiv.refl _) hrange x hrH' hcH' hrD' hcD'
        (fun c => lowOp (Jl c)) Wp (fun u => zext (G u)) (fun u => markEmb q.k (bf u))
        (fun u => markEmb q.k (xs u)) (fun r => markEmb q.k (bs r)) βG δG βb δb bmax hR')

end Outcome

end

end SparseHamiltonian.GeneralSparseODE
