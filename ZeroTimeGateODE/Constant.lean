import ZeroTimeGateODE.Assembly
import SparseODE.ODEZeroEnergy

/-!
# Zero time or a known zero generator: the native solver, constant coefficients

The remark of Theorem `ode:thm:gates`: "Zero time or a known zero generator uses direct source
assembly and needs no matrix calls."  For `x' = A x + b`, `A = -(L + iH)`, at `T = 0` the
solution is `x₀`, and for a known zero generator (public bounds `λ_H = λ_D = 0`, so `A = 0`) it
is `x₀ + T b` (`zero_target`).  The native protocol is the released four-attempt protocol
`GateNative.nprotocol` with the same public bound `g`, around the direct source assembly
`zprepC (srcRot T r₀ r_b) srcC` on a native ODE register `ZNW …` with the released pool
(`native_ode_solver_zero`):

* the trials consist of valid elementary gates and primitive calls;
* one preparation has `|srcC 0| + |srcC 1| + 2` elementary gates and, for every kind `q` of
  primitive oracles, exactly the calls of the source circuits; in every history the protocol
  makes at most `40 g` times these calls, so no call of a kind that the source circuits do not
  call (in particular no matrix-oracle call if they make none), and uses at most
  `40 g (|srcC 0| + |srcC 1| + 2) + 20 g (4 n + 3)` gates, `n` the tested wires;
* for every instance with unitary primitive oracles, unitary source interfaces approximated by
  the source circuits within `ζs`, `2 ζs ≤ ν = ε / (10000 g)`, the public norms
  `‖x₀‖ = r₀`, `‖b‖ = r_b`, the released source promises, `x₀ + T b ≠ 0` and
  `r₀ + T r_b ≤ g ‖x₀ + T b‖`, the protocol has the guarantees `GateNative.NOutcome` against
  `x₀ + T b`.

No private Cayley operation, no `U_J`, no arithmetic and no matrix data enter the circuit or
the hypotheses.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Label Oracles wiring)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The register -/

/-- The pool of the native zero tests, as in the released solver: one wire for every wire of
the released register, of the private work register, of the source scratch and of the
system. -/
abbrev zPool (a m r K k l f : ℕ) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z]
    (bT bP A : ℕ) : ℕ :=
  Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
    Fintype.card S

/-- The native ODE register with the released pool; for the released parameters `p` it is the
register `GateNative.NW p` of the released solver. -/
abbrev ZNW (a m r K k l f : ℕ) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z]
    (bT bP A : ℕ) :=
  HWO a m r K k l f S Zs (zPool a m r K k l f S Zs Z bT bP A) Z bT bP A

section Card

variable {S Zs Z : Type*} [Fintype S] [Fintype Zs] [Fintype Z]

/-- The qubits of the native register. -/
theorem card_ZNW (a m r K k l f bT bP A : ℕ) :
    Fintype.card (ZNW a m r K k l f S Zs Z bT bP A) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K k l f) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Zs) + Fintype.card S + 1 := by
  rw [card_HW]
  simp only [OX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, zPool, XW, AWr]
  ring

/-- The register of the released solver is the register `ZNW` of its parameters. -/
theorem nw_eq_znw (p : GateODE.Params) (bT bP A : ℕ) :
    NW p S Zs Z bT bP A = ZNW p.a p.m p.r p.K p.k p.l p.f S Zs Z bT bP A := rfl

end Card

/-! ### The target -/

section Target

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The zero-case target**: the solution `x(T)` of `x' = -(L + iH) x + b`, `x(0) = x₀`, is
`x₀ + T b` at `T = 0` (where it is `x₀`) and for a zero generator `H = L = 0`. -/
theorem zero_target (H L : P →L[ℂ] P) (x0 b : P) (T : ℝ) (h : T = 0 ∨ (H = 0 ∧ L = 0)) :
    ODEConstantForcing.solution (GateODE.gen H L) x0 b T = x0 + T • b := by
  rcases h with rfl | ⟨rfl, rfl⟩
  · rw [ODEConstantForcing.solution_zero, zero_smul, add_zero]
  · have e : GateODE.gen (0 : P →L[ℂ] P) 0 = 0 := by
      simp [GateODE.gen]
    rw [e, ODEZeroEnergy.solution_zero_generator]

omit [CompleteSpace P] in
/-- A known zero generator: zero public bounds force `H = L = 0`. -/
theorem generator_zero (H L : P →L[ℂ] P) (lamH lamD : ℝ) (hH : ‖H‖ ≤ lamH) (hL : ‖L‖ ≤ lamD)
    (hH0 : lamH = 0) (hL0 : lamD = 0) : H = 0 ∧ L = 0 := by
  subst hH0 hL0
  exact ⟨norm_le_zero_iff.mp hH, norm_le_zero_iff.mp hL⟩

/-- **The decoded vector of the released zero-case preparation is `(x₀ + T b) / B`**: with the
rotation `srcRot T r₀ r_b`, the public norms and the released source promises,
`B · goodF† (run zrelC seed) = x₀ + T b`, `B = r₀ + T r_b`. -/
theorem srcRot_decoded {a m r K k l f : ℕ} (T r₀ rb : ℝ) (hT : 0 ≤ T) (hr₀ : 0 ≤ r₀)
    (hrb : 0 ≤ rb) (hB : 0 < r₀ + T * rb) (v : P) (σ : Oracles a (Label k l) P) (x0 b : P)
    (h₀ : ‖x0‖ = r₀) (hb : ‖b‖ = rb)
    (hJ0 : x0 ≠ 0 → σ.J false v = unitDirection x0)
    (hJb : b ≠ 0 → σ.J true v = unitDirection b) :
    (r₀ + T * rb) • (goodF†) (GateODE.run (wiring (a := a) (m := m) (r := r) (K := K) (k := k)
      (l := l) (f := f) v) σ (zrelC (srcRot T r₀ rb)) (GateODE.seedState v)) = x0 + T • b := by
  rw [srcRot, zrelC_decoded]
  have hc : Real.sqrt (r₀ / (r₀ + T * rb)) ^ 2 = r₀ / (r₀ + T * rb) :=
    Real.sq_sqrt (div_nonneg hr₀ hB.le)
  have hs : Real.sqrt (T * rb / (r₀ + T * rb)) ^ 2 = T * rb / (r₀ + T * rb) :=
    Real.sq_sqrt (div_nonneg (mul_nonneg hT hrb) hB.le)
  rw [hc, hs, Complex.coe_smul, Complex.coe_smul, smul_add, smul_smul, smul_smul]
  have e1 : (r₀ + T * rb) * (r₀ / (r₀ + T * rb)) = r₀ := by field_simp
  have e2 : (r₀ + T * rb) * (T * rb / (r₀ + T * rb)) = T * rb := by field_simp
  rw [e1, e2]
  have hx : r₀ • σ.J false v = x0 := by
    by_cases hx0 : x0 = 0
    · have : r₀ = 0 := by rw [← h₀, hx0, norm_zero]
      rw [this, zero_smul, hx0]
    · rw [hJ0 hx0, unitDirection, smul_smul, ← h₀,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
  have hbb : (T * rb) • σ.J true v = T • b := by
    by_cases hb0 : b = 0
    · have : rb = 0 := by rw [← hb, hb0, norm_zero]
      rw [this, mul_zero, zero_smul, hb0, smul_zero]
    · rw [hJb hb0, unitDirection, smul_smul, ← hb, mul_assoc,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hb0), mul_one]
  rw [hx, hbb]

end Target

/-! ### The solver -/

section Main

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The guarantees for one instance of the zero case.** -/
theorem native_zero_outcome (a m r K k l f bT bP A : ℕ) (T g ε r₀ rb : ℝ) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hr₀ : 0 ≤ r₀) (hrb : 0 ≤ rb)
    (hB : 0 < r₀ + T * rb) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ) (ζs : ℝ)
    (hprim : ∀ j, IsUnitary (prim j)) (hJ : ∀ c, IsUnitary (Jsrc c)) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbudget : 2 * ζs ≤ ImprovedODEQueryBudget.precision g ε)
    (h₀ : ‖x0‖ = r₀) (hb : ‖b‖ = rb)
    (hJ0 : x0 ≠ 0 → Jsrc false seedV = unitDirection x0)
    (hJb : b ≠ 0 → Jsrc true seedV = unitDirection b)
    (hne : x0 + T • b ≠ 0) (hbud : r₀ + T * rb ≤ g * ‖x0 + T • b‖) :
    NOutcome (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g ε hg prim (x0 + T • b) := by
  have hu := srcRot_unitary T r₀ rb hT hr₀ hrb hB
  have hprepV := zprepC_valid (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    (srcRot T r₀ rb) hu srcC hsrcV
  let σ : Oracles a (Label k l) (Reg S ℂ) := ⟨1, fun _ => 1, Jsrc⟩
  have hA := zprepC_approx (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A) prim hprim
    (srcRot T r₀ rb) hu srcC hsrcV seedV σ hJ hζs hsrc
  have hrel := srcRot_decoded (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    T r₀ rb hT hr₀ hrb hB seedV σ x0 b h₀ hb hJ0 hJb
  have hν : 0 < ImprovedODEQueryBudget.precision g ε :=
    ImprovedODEQueryBudget.precision_pos g ε hg hε
  generalize GateODE.run (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    seedV) σ (zrelC (srcRot T r₀ rb)) = Urel at hA hrel
  exact noutcome_of_released (Nat.le_succ _) _ prim hprim hprepV (zprepC_pres _ srcC prim) Urel hA
    (x0 + T • b) (r₀ + T * rb) g ε hne hg hε hεHalf hB hbud hrel (by linarith)

/-- **Zero time or a known zero generator, native gates, constant coefficients** (remark of
Theorem `ode:thm:gates`: direct source assembly, no matrix calls).

On every native ODE register `ZNW a m r K k l f S Zs Z bT bP A` (the released kinds of wires,
with the released pool), the native protocol `nprotocol (zprepC (srcRot T r₀ r_b) srcC) g`
depends only on the public data `T, g, r₀, r_b` and the source circuits.  Its trial circuits
consist of valid elementary gates and primitive calls.  One preparation uses
`|srcC 0| + |srcC 1| + 2` elementary gates and, for every kind `q` of primitive oracles,
exactly `calls_q(srcC 0) + calls_q(srcC 1)` calls; in every history (including four failures)
the protocol uses at most `40 g` times these per preparation, plus `20 g (4 n + 3)` gates for
the zero tests, `n` the wires other than the native flag and pool, and it makes no call of a
kind that the source circuits do not call.  For every instance with unitary primitive oracles,
unitary source interfaces `J c` approximated by the source circuits within `ζs`,
`2 ζs ≤ ν = ε / (10000 g)`, `‖x₀‖ = r₀`, `‖b‖ = r_b`, the released promises
`J₀ v = x₀ / ‖x₀‖` and `J_b v = b / ‖b‖` for the all-zero seed `v` (when nonzero),
`x₀ + T b ≠ 0` and `r₀ + T r_b ≤ g ‖x₀ + T b‖`, the protocol has the guarantees `NOutcome`
against `x₀ + T b` (which is `x(T)` at `T = 0` and for a zero generator, `zero_target`): unitary
trials, mean success at least `1/4`, every successful trial within `ε / 500` of
`(x₀ + T b) / ‖x₀ + T b‖` up to a global phase, success probability at least
`175/256 > 2/3`, and a conditional output density within trace distance `ε`. -/
theorem native_ode_solver_zero (a m r K k l f bT bP A : ℕ) (T g ε r₀ rb : ℝ) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hr₀ : 0 ≤ r₀) (hrb : 0 ≤ rb)
    (hB : 0 < r₀ + T * rb) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) j, i.Valid) ∧
    nGatesN (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) =
      nGatesN (srcC false) + nGatesN (srcC true) + 2 ∧
    (∀ q : J → Bool, nCallsN q (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) =
      nCallsN q (srcC false) + nCallsN q (srcC true)) ∧
    ((nprotocol (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost wGateN : ℝ) ≤
      40 * g * (nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool, ((nprotocol (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost (wCallN q) : ℝ) ≤
      40 * g * (nCallsN q (srcC false) + nCallsN q (srcC true) : ℕ)) ∧
    (∀ q : J → Bool, nCallsN q (srcC false) = 0 → nCallsN q (srcC true) = 0 →
      (nprotocol (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost (wCallN q) = 0) ∧
    Fintype.card (ZNW a m r K k l f S Zs Z bT bP A) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K k l f) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Zs) + Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ)
      (x0 b : Reg S ℂ) (ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      2 * ζs ≤ ImprovedODEQueryBudget.precision g ε →
      ‖x0‖ = r₀ → ‖b‖ = rb →
      (x0 ≠ 0 → Jsrc false seedV = unitDirection x0) →
      (b ≠ 0 → Jsrc true seedV = unitDirection b) →
      x0 + T • b ≠ 0 →
      r₀ + T * rb ≤ g * ‖x0 + T • b‖ →
      NOutcome (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g ε hg prim (x0 + T • b) := by
  have hu := srcRot_unitary T r₀ rb hT hr₀ hrb hB
  have hprepV := zprepC_valid (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    (srcRot T r₀ rb) hu srcC hsrcV
  have hcount := fun q => zprepC_counts (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    (srcRot T r₀ rb) srcC q
  have hworst := fun q => nprotocol_worst (zprepC (srcRot T r₀ rb) srcC :
    List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg q
  refine ⟨fun j => trialN_valid _ hprepV j, (hcount (fun _ => true)).1, fun q => (hcount q).2,
    ?_, ?_, ?_, card_ZNW a m r K k l f bT bP A, ?_⟩
  · have h := (hworst (fun _ => true)).1
    rw [(hcount (fun _ => true)).1] at h
    exact h
  · intro q
    have h := (hworst q).2
    rw [(hcount q).2] at h
    exact h
  · intro q h0 h1
    have h := (hworst q).2
    rw [(hcount q).2, h0, h1] at h
    have h' : ((nprotocol (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost (wCallN q) : ℝ) ≤
        0 := by simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  · intro prim Jsrc x0 b ζs hprim hJ hζs hsrc hbudget h₀ hb hJ0 hJb hne hbud
    exact native_zero_outcome a m r K k l f bT bP A T g ε r₀ rb hT hg hε hεHalf hr₀ hrb hB srcC
      hsrcV prim Jsrc x0 b ζs hprim hJ hζs hsrc hbudget h₀ hb hJ0 hJb hne hbud

end Main

end

end SparseHamiltonian.ZeroTimeGateODE
