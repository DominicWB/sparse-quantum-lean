import ZeroTimeGateODE.Constant

/-!
# The native solver for every `T ≥ 0`, constant coefficients

The released native solver `GateNative.native_ode_solver` takes the public data
`GateODE.Params` with `PublicOK`, which requires `T > 0` and `λ_H + R λ_D > 0`.  For every
`T ≥ 0` and every pair of bounds `λ_H, λ_D ≥ 0` (`PublicOK0`), one circuit per public parameter
choice on the released register `GateNative.NW p`:

`cprepC p … = if ZeroCase p then zprepC (srcRot T r₀ r_b) srcC else nprepC p UJg nd ar srcC`,

where `ZeroCase p` is `T = 0 ∨ λ_H + R λ_D = 0` (zero time or a known zero generator,
`zeroCase_iff`).  The released protocol `nprotocol (cprepC p …) g` has the released public
conclusions with the counts `if ZeroCase p then <direct source assembly> else <released>`, and
the guarantees `NOutcome` against the released target `x(T)` under the released instance
conditions in the positive case and under the zero-case conditions `ZInstanceOK` (the source
part of the released `InstanceOK` and the norm bounds of the generator, implied by
`InstanceOK`, `zInstanceOK_of`) in the zero case (`native_ode_solver_nonneg`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Label Oracles wiring Params)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### Public data for every `T ≥ 0` -/

/-- The public conditions for every `T ≥ 0`: the released `GateODE.Params.PublicOK` with
`0 ≤ T` in place of `0 < T` and without `0 < λ_H + R λ_D`. -/
structure PublicOK0 (p : Params) : Prop where
  T_nonneg : 0 ≤ p.T
  g_ge : 1 ≤ p.g
  ε_pos : 0 < p.ε
  ε_half : p.ε ≤ 1 / 2
  lamH_nonneg : 0 ≤ p.lamH
  lamD_nonneg : 0 ≤ p.lamD
  Q_ge : 1 ≤ p.Q
  qbar_nonneg : 0 ≤ p.qbar
  qbar_le : p.qbar ≤ p.Q
  r₀_nonneg : 0 ≤ p.r₀
  rb_nonneg : 0 ≤ p.rb
  B_pos : 0 < p.B

/-- **The zero case**: zero time or a known zero generator (the public bounds give
`λ_H + R λ_D = 0`, `R = radius g ε > 0`). -/
abbrev ZeroCase (p : Params) : Prop := p.T = 0 ∨ p.lamH + p.R * p.lamD = 0

/-- The released public conditions give those for every `T ≥ 0`. -/
theorem publicOK0_of {p : Params} (hp : p.PublicOK) : PublicOK0 p :=
  ⟨hp.T_pos.le, hp.g_ge, hp.ε_pos, hp.ε_half, hp.lamH_nonneg, hp.lamD_nonneg, hp.Q_ge,
    hp.qbar_nonneg, hp.qbar_le, hp.r₀_nonneg, hp.rb_nonneg, hp.B_pos⟩

/-- Outside the zero case the conditions for every `T ≥ 0` are the released ones. -/
theorem publicOK_of {p : Params} (hp : PublicOK0 p) (hz : ¬ ZeroCase p) : p.PublicOK := by
  have hT : p.T ≠ 0 := fun h => hz (Or.inl h)
  have hE : p.lamH + p.R * p.lamD ≠ 0 := fun h => hz (Or.inr h)
  have hR : 0 < p.R := GateODE.AnalyticLCHS.radius_pos hp.g_ge hp.ε_pos
    (hp.ε_half.trans (by norm_num))
  have hE0 : 0 ≤ p.lamH + p.R * p.lamD :=
    add_nonneg hp.lamH_nonneg (mul_nonneg hR.le hp.lamD_nonneg)
  exact ⟨lt_of_le_of_ne hp.T_nonneg (Ne.symm hT), hp.g_ge, hp.ε_pos, hp.ε_half, hp.lamH_nonneg,
    hp.lamD_nonneg, lt_of_le_of_ne hE0 (Ne.symm hE), hp.Q_ge, hp.qbar_nonneg, hp.qbar_le,
    hp.r₀_nonneg, hp.rb_nonneg, hp.B_pos⟩

/-- The zero case is zero time or zero public bounds of both parts of the generator. -/
theorem zeroCase_iff {p : Params} (hp : PublicOK0 p) :
    ZeroCase p ↔ p.T = 0 ∨ (p.lamH = 0 ∧ p.lamD = 0) := by
  have hR : 0 < p.R := GateODE.AnalyticLCHS.radius_pos hp.g_ge hp.ε_pos
    (hp.ε_half.trans (by norm_num))
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      have h1 := hp.lamH_nonneg
      have h2 : 0 ≤ p.R * p.lamD := mul_nonneg hR.le hp.lamD_nonneg
      have h3 : p.lamH = 0 := by linarith
      refine ⟨h3, ?_⟩
      rw [h3, zero_add] at h
      rcases mul_eq_zero.mp h with h4 | h4
      · exact absurd h4 hR.ne'
      · exact h4
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · right
      rw [h1, h2, mul_zero, add_zero]

/-! ### Instance conditions in the zero case -/

section Instance

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The conditions on an instance in the zero case**: the source part of the released
`GateODE.Params.InstanceOK` (unitary source interfaces, public norms, the preparation promises of
the seed `v`, a nonzero target and `B ≤ g ‖x(T)‖`) and the norm bounds `‖H‖ ≤ λ_H`,
`‖L‖ ≤ λ_D`; no condition on `U_J` or on private operations. -/
structure ZInstanceOK (p : Params) (v : P) (Jsrc : Bool → P →L[ℂ] P) (H L : P →L[ℂ] P)
    (x0 b : P) : Prop where
  src_unitary : ∀ c, IsUnitary (Jsrc c)
  normH : ‖H‖ ≤ p.lamH
  normL : ‖L‖ ≤ p.lamD
  init_norm : ‖x0‖ = p.r₀
  forcing_norm : ‖b‖ = p.rb
  init_prep : x0 ≠ 0 → Jsrc false v = unitDirection x0
  forcing_prep : b ≠ 0 → Jsrc true v = unitDirection b
  target_ne : p.target H L x0 b ≠ 0
  budget : p.B ≤ p.g * ‖p.target H L x0 b‖

/-- The released instance conditions imply the zero-case conditions. -/
theorem zInstanceOK_of {p : Params} {v : P} {σ : Oracles p.a (Label p.k p.l) P}
    {H L : P →L[ℂ] P} {x0 b : P} (hI : p.InstanceOK v σ H L x0 b) :
    ZInstanceOK p v σ.J H L x0 b :=
  ⟨hI.src_unitary, hI.select.normH, hI.select.normL, hI.init_norm, hI.forcing_norm,
    hI.init_prep, hI.forcing_prep, hI.target_ne, hI.budget⟩

/-- **In the zero case the released target is `x₀ + T b`**: `x₀` at `T = 0`, `x₀ + T b` for a
known zero generator. -/
theorem target_zero {p : Params} (hp : PublicOK0 p) (hz : ZeroCase p) (H L : P →L[ℂ] P)
    (x0 b : P) (hH : ‖H‖ ≤ p.lamH) (hL : ‖L‖ ≤ p.lamD) :
    p.target H L x0 b = x0 + p.T • b := by
  apply zero_target
  rcases (zeroCase_iff hp).mp hz with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr (generator_zero H L p.lamH p.lamD hH hL h1 h2)

end Instance

/-! ### The circuit and the solver -/

section Main

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The native preparation for every `T ≥ 0`**: the direct source assembly in the zero case,
the released native preparation otherwise, on the released register. -/
def cprepC (p : Params) (UJg : List (Gate (Fin p.a ⊕ S)))
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z))
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    List (NInstr (NW p S Zs Z ar.bT ar.bP ar.A) Y J) :=
  if ZeroCase p then zprepC (srcRot p.T p.r₀ p.rb) srcC else nprepC p UJg nd ar srcC

/-- **Zero-case guarantees on the released register** (remark of `ode:thm:gates`): in the zero
case the protocol `nprotocol (cprepC p …) g` has the guarantees `NOutcome` against the
released target `x(T)` under the zero-case conditions and `2 ζs ≤ ν`. -/
theorem native_zero_outcome_params (p : Params) (hp : PublicOK0 p) (hz : ZeroCase p)
    (UJg : List (Gate (Fin p.a ⊕ S))) (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z))
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ)
    (H L : Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ) (ζs : ℝ) (hprim : ∀ j, IsUnitary (prim j))
    (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbudget : 2 * ζs ≤ p.nu) (hI : ZInstanceOK p (seedV (S := S)) Jsrc H L x0 b) :
    NOutcome (cprepC p UJg nd ar srcC) p.g p.ε hp.g_ge prim (p.target H L x0 b) := by
  have ht := target_zero hp hz H L x0 b hI.normH hI.normL
  have hne := hI.target_ne
  have hbud := hI.budget
  rw [ht] at hne hbud ⊢
  have h := native_zero_outcome (Z := Z) p.a p.m p.r p.K p.k p.l p.f ar.bT ar.bP ar.A p.T p.g p.ε
    p.r₀ p.rb hp.T_nonneg hp.g_ge hp.ε_pos hp.ε_half hp.r₀_nonneg hp.rb_nonneg hp.B_pos srcC hsrcV
    prim Jsrc x0 b ζs hprim hI.src_unitary hζs hsrc hbudget hI.init_norm hI.forcing_norm
    hI.init_prep hI.forcing_prep hne hbud
  rw [cprepC, if_pos hz]
  exact h

/-- **Native gate-efficient dissipative ODE solver for every `T ≥ 0`, constant coefficients**
(Theorem `ode:thm:gates` with its remark on zero time and a known zero generator).

For public data `p` with `PublicOK0 p` (`T ≥ 0`, `λ_H, λ_D ≥ 0` and the other released public
conditions) and the released public native data (`U_J` gates, a public native private
operation `nd`, arithmetic `ar` with `ArithOK` at accuracy `ζ`, valid source circuits), the
protocol `nprotocol (cprepC p UJg nd ar srcC) g` on the released register `NW p` has valid
trials; one preparation uses at most `if ZeroCase p then |srcC 0| + |srcC 1| + 2 else
prepGates + 84 d C_J + 6 d G_C + |srcC 0| + |srcC 1|` gates and at most
`if ZeroCase p then calls(srcC 0) + calls(srcC 1) else 12 d calls(V) + calls(srcC 0) +
calls(srcC 1)` calls of every kind; every history uses at most `40 g` times these per
preparation plus `20 g (4 n + 3)` gates; the register has the released qubit count.  For
every instance with unitary primitive oracles and source circuits within `ζs` of the
controlled source interfaces, the protocol has the guarantees `NOutcome` against the released
target `x(T)`, under `2 ζs ≤ ν` and the zero-case conditions `ZInstanceOK` in the zero case,
and under the released conditions (`NativeOK`, `24 d ζ + 2 ζs ≤ ν`, `InstanceOK`) otherwise. -/
theorem native_ode_solver_nonneg (p : Params) (hp : PublicOK0 p)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) :
    (∀ j, ∀ i ∈ trialN (cprepC p UJg nd ar srcC) j, i.Valid) ∧
    nGatesN (cprepC p UJg nd ar srcC) ≤
      (if ZeroCase p then nGatesN (srcC false) + nGatesN (srcC true) + 2
      else p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar +
        nGatesN (srcC false) + nGatesN (srcC true)) ∧
    (∀ q : J → Bool, nCallsN q (cprepC p UJg nd ar srcC) ≤
      (if ZeroCase p then nCallsN q (srcC false) + nCallsN q (srcC true)
      else 12 * p.d * nCallsN q nd.V + nCallsN q (srcC false) + nCallsN q (srcC true))) ∧
    ((nprotocol (cprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost wGateN : ℝ) ≤
      40 * p.g * nGatesN (cprepC p UJg nd ar srcC) +
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool, ((nprotocol (cprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost (wCallN q) : ℝ) ≤
      40 * p.g * nCallsN q (cprepC p UJg nd ar srcC)) ∧
    Fintype.card (NW p S Zs Z ar.bT ar.bP ar.A) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.k p.l → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (H L : Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ)
      (ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      (if ZeroCase p then 2 * ζs ≤ p.nu ∧ ZInstanceOK p (seedV (S := S)) Jsrc H L x0 b
      else NativeOK prim nd (selOp (labFam D false)) ∧ 24 * (p.d : ℝ) * ζ + 2 * ζs ≤ p.nu ∧
        p.InstanceOK (seedV (S := S))
          (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b) →
      NOutcome (cprepC p UJg nd ar srcC) p.g p.ε hp.g_ge prim (p.target H L x0 b) := by
  by_cases hz : ZeroCase p
  · have hZ := native_ode_solver_zero (S := S) (Zs := Zs) (Z := Z) (Y := Y) (J := J) p.a p.m p.r
      p.K p.k p.l p.f ar.bT ar.bP ar.A p.T p.g p.ε p.r₀ p.rb hp.T_nonneg hp.g_ge hp.ε_pos
      hp.ε_half hp.r₀_nonneg hp.rb_nonneg hp.B_pos srcC hsrcV
    obtain ⟨hV, hG, hC, hWG, hWC, -, hcard, -⟩ := hZ
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [cprepC, if_pos hz]
      exact hV
    · rw [cprepC, if_pos hz, if_pos hz]
      exact hG.le
    · intro q
      rw [cprepC, if_pos hz, if_pos hz]
      exact (hC q).le
    · rw [cprepC, if_pos hz, hG]
      exact hWG
    · intro q
      rw [cprepC, if_pos hz, hC q]
      exact hWC q
    · exact hcard
    · intro prim D Jsrc H L x0 b ζs hprim hζs hsrc hcase
      rw [if_pos hz] at hcase
      exact native_zero_outcome_params p hp hz UJg nd ar srcC hsrcV prim Jsrc H L x0 b ζs hprim
        hζs hsrc hcase.1 hcase.2
  · have hP := publicOK_of hp hz
    obtain ⟨hV, hG, hC, hWG, hWC, hcard, hout⟩ :=
      native_ode_solver p hP UJg hUJg nd hnd ar ζ hζ har srcC hsrcV
    refine ⟨?_, ?_, ?_, ?_, ?_, hcard, ?_⟩
    · rw [cprepC, if_neg hz]
      exact hV
    · rw [cprepC, if_neg hz, if_neg hz]
      exact hG
    · intro q
      rw [cprepC, if_neg hz, if_neg hz]
      exact hC q
    · rw [cprepC, if_neg hz]
      exact hWG
    · intro q
      rw [cprepC, if_neg hz]
      exact hWC q
    · intro prim D Jsrc H L x0 b ζs hprim hζs hsrc hcase
      rw [if_neg hz] at hcase
      obtain ⟨hN, hbud, hI⟩ := hcase
      rw [cprepC, if_neg hz]
      exact hout prim D Jsrc H L x0 b ζs hprim hN hζs hsrc hbud hI

end Main

end

end SparseHamiltonian.ZeroTimeGateODE
