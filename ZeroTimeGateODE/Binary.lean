import ZeroTimeGateODE.Combined
import GateEfficientBinaryODE.Solver
import SparseHamiltonian.NativeZeroSimulation

/-!
# Zero time or a known zero generator from binary sparse data, constant coefficients

The released solver from binary sparse data `GateBinaryODE.binary_ode_solver` takes the public
data `GateBinaryODE.Pub` with `Pub.OK`, which requires `T > 0` and `η_H + η_D > 0`.  For every
`T ≥ 0` and all energy bounds `η_H, η_D ≥ 0` (`BPublicOK0`), one circuit per public parameter
choice on the released binary register:

`bprepC q srcC = if T = 0 ∨ η_H + η_D = 0 then zprepC (srcRot T r₀ r_b) srcC else q.prep srcC`

(`BZeroCase`).  In the zero case the matrix data are not used: the direct source assembly makes
no call of the binary sparse oracles (`Query.rowLocation`, `Query.columnLocation`,
`Query.value`) besides those of the source circuits (`binary_zero_no_matrix_calls`), and the
target `x(T)` of `x' = -M̂ x + b` is `x₀ + T b`, because zero energy bounds force the matrix to
vanish (`binary_target_zero`).  `binary_ode_solver_nonneg` states the released solver for every
`T ≥ 0` with the released hypotheses on the input and the sources, the counts
`if BZeroCase q then <direct source assembly> else <released>`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open GateBinaryODE (Pub mLift)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### Public data for every `T ≥ 0` -/

/-- The public conditions for every `T ≥ 0`: the released `GateBinaryODE.Pub.OK` with `0 ≤ T`
in place of `0 < T` and without `0 < η_H + η_D`. -/
structure BPublicOK0 (q : Pub) : Prop where
  b_pos : 0 < q.b
  c0_pos : 0 < q.c0
  etaH_nonneg : 0 ≤ q.etaH
  etaD_nonneg : 0 ≤ q.etaD
  γ_pos : 0 < q.γ
  γ_le : q.γ ≤ 1
  T_nonneg : 0 ≤ q.T
  g_ge : 1 ≤ q.g
  ε_pos : 0 < q.ε
  ε_half : q.ε ≤ 1 / 2
  r₀_nonneg : 0 ≤ q.r₀
  rb_nonneg : 0 ≤ q.rb
  B_pos : 0 < q.r₀ + q.T * q.rb
  ζ_pos : 0 < q.ζ
  ζ_le : q.ζ ≤ 1

/-- **The zero case** of the binary data: zero time or zero energy bounds. -/
abbrev BZeroCase (q : Pub) : Prop := q.T = 0 ∨ q.etaH + q.etaD = 0

/-- The released public conditions give those for every `T ≥ 0`. -/
theorem bpublicOK0_of {q : Pub} (hq : q.OK) : BPublicOK0 q :=
  ⟨hq.b_pos, hq.c0_pos, hq.etaH_nonneg, hq.etaD_nonneg, hq.γ_pos, hq.γ_le, hq.T_pos.le, hq.g_ge,
    hq.ε_pos, hq.ε_half, hq.r₀_nonneg, hq.rb_nonneg, hq.B_pos, hq.ζ_pos, hq.ζ_le⟩

/-- Outside the zero case the conditions for every `T ≥ 0` are the released ones. -/
theorem bpublicOK_of {q : Pub} (hq : BPublicOK0 q) (hz : ¬ BZeroCase q) : q.OK := by
  have hT : q.T ≠ 0 := fun h => hz (Or.inl h)
  have hE : q.etaH + q.etaD ≠ 0 := fun h => hz (Or.inr h)
  exact ⟨hq.b_pos, hq.c0_pos, hq.etaH_nonneg, hq.etaD_nonneg,
    lt_of_le_of_ne (add_nonneg hq.etaH_nonneg hq.etaD_nonneg) (Ne.symm hE), hq.γ_pos, hq.γ_le,
    lt_of_le_of_ne hq.T_nonneg (Ne.symm hT), hq.g_ge, hq.ε_pos, hq.ε_half, hq.r₀_nonneg,
    hq.rb_nonneg, hq.B_pos, hq.ζ_pos, hq.ζ_le⟩

/-! ### The zero-case target -/

section Target

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The zero-case target from binary data**: at `T = 0`, or with zero energy bounds (the row
energy promises then force the matrix to vanish), the solution of `x' = -M̂ x + b` is
`x₀ + T b`. -/
theorem binary_target_zero (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (x0 v : Reg (Fin q.kx) ℂ) :
    ODEConstantForcing.solution (-mLift D en x) x0 v q.T = x0 + q.T • v := by
  rcases hz with hT | hE
  · rw [hT, ODEConstantForcing.solution_zero, zero_smul, add_zero]
  · have hM : D.matrix x = 0 := ODEZeroEnergy.matrix_zero_of_effective_energy (D.matrix x)
      q.etaH q.etaD 1 hq.etaH_nonneg hq.etaD_nonneg one_pos (by rw [one_mul]; exact hE) hrH hrD
    have hL : mLift D en x = 0 := by
      rw [mLift, hM, NativeZeroSimulation.matrixOperator_zero]
      exact map_zero (qliftHom (R := ℂ) en)
    rw [hL, neg_zero, ODEZeroEnergy.solution_zero_generator]

end Target

/-! ### The circuit and the solver -/

section Main

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The preparation from binary data for every `T ≥ 0`**: the direct source assembly in the
zero case, the released preparation from binary data otherwise, on the released register. -/
def bprepC (q : Pub) (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    List (NInstr (NW q.params (Fin q.kx) Zs (GateBinaryODE.SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
      (PY q.kx q.b) Query) :=
  if BZeroCase q then zprepC (srcRot q.T q.r₀ q.rb) srcC else q.prep srcC

/-- **No matrix call in the zero case**: if the source circuits make no call of the oracle kinds
`c` (for example the three binary sparse oracles), the protocol makes none in any history. -/
theorem binary_zero_no_matrix_calls (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (c : Query → Bool)
    (h0 : nCallsN c (srcC false) = 0) (h1 : nCallsN c (srcC true) = 0) :
    (nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) = 0 := by
  obtain ⟨-, -, -, -, -, hno, -, -⟩ := native_ode_solver_zero (Z := GateBinaryODE.SZ4 q.kx q.b)
    (Y := PY q.kx q.b) (J := Query) q.params.a q.params.m q.params.r q.params.K q.params.k
    q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos
    hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos srcC hsrcV
  rw [bprepC, if_pos hz]
  exact hno c h0 h1

/-- **Dissipative ODE from binary sparse data for every `T ≥ 0`, constant coefficients**
(Theorem `ode:thm:gates` with its remark on zero time and a known zero generator).

For binary public data with `BPublicOK0 q`, the protocol `nprotocol (bprepC q srcC) g` on the
released binary register has valid trials; one preparation uses at most
`if BZeroCase q then |srcC 0| + |srcC 1| + 2 else <the released binary count>` gates and at most
`if BZeroCase q then calls(srcC 0) + calls(srcC 1) else 12 d (2 [row] + 2 [col] + 2 [value]) +
calls(srcC 0) + calls(srcC 1)` calls of every kind; every history uses at most `40 g` times these
per preparation plus `20 g (4 n + 3)` gates; the register has the released qubit count.  For every
input with the released energy and accretivity promises and the released source hypotheses
(unitary interfaces, source circuits within `ζs`, `24 d ζ + 2 ζs ≤ ν`, public norms, preparation
promises, `x(T) ≠ 0`, `r₀ + T r_b ≤ g ‖x(T)‖`), the protocol has the guarantees `NOutcome` against
the solution `x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_solver_nonneg (q : Pub) (hq : BPublicOK0 q) {X n : Type*} [Fintype n]
    [DecidableEq n] (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, ∀ i ∈ trialN (bprepC q srcC) j, i.Valid) ∧
    nGatesN (bprepC q srcC) ≤
      (if BZeroCase q then nGatesN (srcC false) + nGatesN (srcC true) + 2
      else q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
        6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
          (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN (srcC false) + nGatesN (srcC true)) ∧
    (∀ c : Query → Bool, nCallsN c (bprepC q srcC) ≤
      (if BZeroCase q then nCallsN c (srcC false) + nCallsN c (srcC true)
      else 12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c (srcC false) + nCallsN c (srcC true))) ∧
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      40 * q.g * nGatesN (bprepC q srcC) +
        20 * q.g * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (GateBinaryODE.SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card Zs + q.kx) + 3) ∧
    (∀ c : Query → Bool, ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
      40 * q.g * nCallsN c (bprepC q srcC)) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (GateBinaryODE.SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      24 * (q.params.d : ℝ) * q.ζ + 2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (bprepC q srcC) q.g q.ε hq.g_ge (prims (R := ℂ) D en x)
        (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  by_cases hz : BZeroCase q
  · obtain ⟨hV, hG, hC, hWG, hWC, -, hcardZ, hout⟩ := native_ode_solver_zero
      (Z := GateBinaryODE.SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query) q.params.a q.params.m
      q.params.r q.params.K q.params.k q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A q.T q.g q.ε
      q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg hq.B_pos srcC
      hsrcV
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [bprepC, if_pos hz]
      exact hV
    · rw [bprepC, if_pos hz, if_pos hz]
      exact hG.le
    · intro c
      rw [bprepC, if_pos hz, if_pos hz]
      exact (hC c).le
    · rw [bprepC, if_pos hz, hG]
      rw [Fintype.card_fin] at hWG
      exact hWG
    · intro c
      rw [bprepC, if_pos hz, hC c]
      exact hWC c
    · rw [GateBinaryODE.card_SZ4, Fintype.card_fin] at hcardZ
      exact hcardZ
    · intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
      have ht := binary_target_zero q hq hz D en x hrH hrD x0 v
      rw [ht] at hne hB ⊢
      have hd : 0 ≤ 24 * (q.params.d : ℝ) * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hq.ζ_pos.le
      have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
      rw [hnu] at hbud
      rw [bprepC, if_pos hz]
      exact hout (prims (R := ℂ) D en x) Jsrc x0 v ζs (prims_isUnitary D en x) hJ hζs hsrc
        (by linarith) hx0 hv hpx hpv hne hB
  · have hP := bpublicOK_of hq hz
    obtain ⟨hV, hG, hC, hWG, hWC, hcard, hout⟩ :=
      GateBinaryODE.binary_ode_solver q hP D en hrange hdec srcC hsrcV
    refine ⟨?_, ?_, ?_, ?_, ?_, hcard, ?_⟩
    · rw [bprepC, if_neg hz]
      exact hV
    · rw [bprepC, if_neg hz, if_neg hz]
      exact hG
    · intro c
      rw [bprepC, if_neg hz, if_neg hz]
      exact hC c
    · rw [bprepC, if_neg hz]
      exact hWG
    · intro c
      rw [bprepC, if_neg hz]
      exact hWC c
    · intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
      rw [bprepC, if_neg hz]
      exact hout x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB

end Main

end

end SparseHamiltonian.ZeroTimeGateODE
