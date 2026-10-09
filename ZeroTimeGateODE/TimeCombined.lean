import ZeroTimeGateODE.Time

/-!
# The native solver for every `T ≥ 0`, time-dependent coefficients

The released native time-dependent solver `GateNative.native_ode_time_solver` takes public data
`GateODE.Time.TParams` with `PublicOK`, which requires `T > 0` and `λ_H + R λ_D > 0`.  For every
`T ≥ 0` and all bounds `λ_H, λ_D ≥ 0` (`TPublicOK0`, with the released mesh condition, which
holds automatically in the zero case, `mesh_of_zeroCase`), one circuit per public parameter
choice on the released register `GateNative.TNW p`:

`ctprepC p … = if TZeroCase p then tzprepC loadC wpC else tnprepC p UJg nd ar loadC wpC`,

with `TZeroCase p` the zero case `T = 0 ∨ λ_H + R λ_D = 0`.  The released protocol
`nprotocol (ctprepC p …) (2g)` has the released public conclusions with the counts
`if TZeroCase p then <direct source assembly> else <released>`, and the guarantees `NOutcome`
against `x(T)` (`native_ode_time_solver_nonneg`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Label)
open GateODE.Time (TParams TOracles)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### Public data for every `T ≥ 0` -/

/-- The public conditions for every `T ≥ 0`: the released `GateODE.Time.TParams.PublicOK` with
`0 ≤ T` in place of `0 < T` and without `0 < λ_H + R λ_D`. -/
structure TPublicOK0 (p : TParams) : Prop where
  T_nonneg : 0 ≤ p.T
  g_ge : 1 ≤ p.g
  ε_pos : 0 < p.ε
  ε_half : p.ε ≤ 1 / 2
  lamH_nonneg : 0 ≤ p.lamH
  lamD_nonneg : 0 ≤ p.lamD
  Q_ge : 1 ≤ p.Q
  qbar_nonneg : 0 ≤ p.qbar
  qbar_le : p.qbar ≤ p.Q
  mesh : TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m

/-- **The time-dependent zero case**: zero time or a known zero generator. -/
abbrev TZeroCase (p : TParams) : Prop := p.T = 0 ∨ p.lamH + p.R * p.lamD = 0

/-- The released public conditions give those for every `T ≥ 0`. -/
theorem tpublicOK0_of {p : TParams} (hp : p.PublicOK) : TPublicOK0 p :=
  ⟨hp.T_pos.le, hp.g_ge, hp.ε_pos, hp.ε_half, hp.lamH_nonneg, hp.lamD_nonneg, hp.Q_ge,
    hp.qbar_nonneg, hp.qbar_le, hp.mesh⟩

/-- Outside the zero case the conditions for every `T ≥ 0` are the released ones. -/
theorem tpublicOK_of {p : TParams} (hp : TPublicOK0 p) (hz : ¬ TZeroCase p) : p.PublicOK := by
  have hT : p.T ≠ 0 := fun h => hz (Or.inl h)
  have hE : p.lamH + p.R * p.lamD ≠ 0 := fun h => hz (Or.inr h)
  have hR : 0 < p.R := GateODE.AnalyticLCHS.radius_pos (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos)
    (p.acc_le_one (hp.ε_half.trans (by norm_num)))
  have hE0 : 0 ≤ p.lamH + p.R * p.lamD :=
    add_nonneg hp.lamH_nonneg (mul_nonneg hR.le hp.lamD_nonneg)
  exact ⟨lt_of_le_of_ne hp.T_nonneg (Ne.symm hT), hp.g_ge, hp.ε_pos, hp.ε_half, hp.lamH_nonneg,
    hp.lamD_nonneg, lt_of_le_of_ne hE0 (Ne.symm hE), hp.Q_ge, hp.qbar_nonneg, hp.qbar_le,
    hp.mesh⟩

/-- In the zero case the released mesh condition holds for every mesh: the common simulation
time is zero and one step suffices. -/
theorem mesh_of_zeroCase (p : TParams) (hz : TZeroCase p) :
    TimeSchedule.steps p.tau (p.nu / 3) ≤ 2 ^ p.m := by
  have hτ : p.tau = 0 := by
    rcases hz with h | h
    · simp [GateODE.Time.TParams.tau, h]
    · simp [GateODE.Time.TParams.tau, h]
  have hs : TimeSchedule.steps p.tau (p.nu / 3) = 1 := by
    simp [TimeSchedule.steps, TimeSchedule.threshold, hτ]
  rw [hs]
  exact Nat.one_le_two_pow

/-! ### The circuit and the solver -/

section Main

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The native time-dependent preparation for every `T ≥ 0`**: the direct source assembly
in the zero case, the released native preparation otherwise, on the released register. -/
def ctprepC (p : TParams) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z))
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) :
    List (NInstr (TNW p S Zs Z ar.bT ar.bP ar.A) Y J) :=
  if TZeroCase p then tzprepC loadC wpC else tnprepC p UJg nd ar loadC wpC

/-- **Native gate-efficient dissipative ODE solver for every `T ≥ 0`, time-dependent
coefficients** (Theorem `ode:thm:gates`, time-dependent part, with its remark on zero time and a
known zero generator).

For public data `p` with `TPublicOK0 p` and the released public native data, the protocol
`nprotocol (ctprepC p UJg nd ar loadC wpC) (2g)` on the released register `TNW p` has valid
trials; one preparation uses at most `if TZeroCase p then |loadC| + 2 |wpC| else
prepGates + 84 d C_J + 6 d G_C + |loadC| + 2 |wpC|` gates and at most
`if TZeroCase p then calls(loadC) + 2 calls(wpC) else 12 d calls(V) + calls(loadC) +
2 calls(wpC)` calls of every kind; every history uses at most `40 · 2g` times these per
preparation plus `20 · 2g (4 n + 3)` gates; the register has the released qubit count.  For
every instance with unitary primitive oracles and loading and weight-preparation circuits within
`ζs`, the protocol has the guarantees `NOutcome` against `x(T)`, under `3 ζs ≤ ν` and the
zero-case conditions `TZInstanceOK` in the zero case, and under the released conditions
(`NativeOK`, `24 d ζ + 3 ζs ≤ ν`, `InstanceOK`) otherwise. -/
theorem native_ode_time_solver_nonneg (p : TParams) (hp : TPublicOK0 p)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (ctprepC p UJg nd ar loadC wpC) j, i.Valid) ∧
    nGatesN (ctprepC p UJg nd ar loadC wpC) ≤
      (if TZeroCase p then nGatesN loadC + 2 * nGatesN wpC
      else p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar + nGatesN loadC +
        2 * nGatesN wpC) ∧
    (∀ q : J → Bool, nCallsN q (ctprepC p UJg nd ar loadC wpC) ≤
      (if TZeroCase p then nCallsN q loadC + 2 * nCallsN q wpC
      else 12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC)) ∧
    ((nprotocol (ctprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (ctprepC p UJg nd ar loadC wpC) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool,
      ((nprotocol (ctprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.ratio * nCallsN q (ctprepC p UJg nd ar loadC wpC)) ∧
    Fintype.card (TNW p S Zs Z ar.bT ar.bP ar.A) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      (if TZeroCase p then 3 * ζs ≤ p.nu ∧
        TZInstanceOK p (seedV (S := S)) Jl Wp Hs Ls G b x bs βG δG βb δb bmax
      else NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) ∧
        24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu ∧
        p.InstanceOK (seedV (S := S))
          (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
          Hs Ls G b x bs βG δG βb δb bmax) →
      NOutcome (ctprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  by_cases hz : TZeroCase p
  · obtain ⟨hV, hG, hC, hWG, hWC, -, hcard, hout⟩ := native_ode_time_solver_zero (S := S)
      (Zs := Zs) (Z := Z) (Y := Y) (J := J) p p.a p.m p.r p.K p.l p.f ar.bT ar.bP ar.A
      hp.T_nonneg hp.g_ge hp.ε_pos hp.ε_half hp.lamH_nonneg hp.lamD_nonneg hz loadC hloadV wpC
      hwpV
    refine ⟨?_, ?_, ?_, ?_, ?_, hcard, ?_⟩
    · rw [ctprepC, if_pos hz]
      exact hV
    · rw [ctprepC, if_pos hz, if_pos hz]
      exact hG.le
    · intro q
      rw [ctprepC, if_pos hz, if_pos hz]
      exact (hC q).le
    · rw [ctprepC, if_pos hz, hG]
      exact hWG
    · intro q
      rw [ctprepC, if_pos hz, hC q]
      exact hWC q
    · intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hcase
      rw [if_pos hz] at hcase
      rw [ctprepC, if_pos hz]
      exact hout prim Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hcase.1
        hcase.2
  · have hP := tpublicOK_of hp hz
    obtain ⟨hV, hG, hC, hWG, hWC, hcard, hout⟩ :=
      native_ode_time_solver p hP UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
    refine ⟨?_, ?_, ?_, ?_, ?_, hcard, ?_⟩
    · rw [ctprepC, if_neg hz]
      exact hV
    · rw [ctprepC, if_neg hz, if_neg hz]
      exact hG
    · intro q
      rw [ctprepC, if_neg hz, if_neg hz]
      exact hC q
    · rw [ctprepC, if_neg hz]
      exact hWG
    · intro q
      rw [ctprepC, if_neg hz]
      exact hWC q
    · intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hcase
      rw [if_neg hz] at hcase
      obtain ⟨hN, hbud, hI⟩ := hcase
      rw [ctprepC, if_neg hz]
      exact hout prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbud hI

end Main

end

end SparseHamiltonian.ZeroTimeGateODE
