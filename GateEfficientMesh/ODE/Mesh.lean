import GateEfficientMesh.ODE.Native
import GateEfficientMesh.ODE.MeshTarget

/-!
# The gate-level time-dependent ODE solver on a nonuniform mesh

Theorem `ode:thm:gates` (manuscript v15, lines 4335-4377) requires a certificate "for the same
uniform meshes"; its scope paragraph (lines 4573-4587) notes that "an arbitrary nonuniform mesh
obtained by inserting breakpoints does not automatically supply the equal-angle boundary
circuit used here". Here a mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` with breakpoints carries one represented
generator sample `L_q + i H_q` and one forcing sample `b̃_q` per interval, and the released
protocol runs unchanged on its uniform clock of `2^m` slots: slot `k` uses the samples of the
interval `σ k = slotPiece k` containing `k T / 2^m` (generator and forcing samples per slot
from the containing interval). The supplied unitaries are those of the slot data
`(H_{σ k}, L_{σ k}, b̃_{σ k})`, so the counts are the released counts with this `m`, with no
factor `M`; the mesh enters the error only through `meshCertificate` (module `ODE/MeshTarget`):
the integrated certificates on the mesh, the left-endpoint source quadrature of the mesh (which
does not decrease with `m`) and the cost of the refinement into slots (of order `2^{-m}`).

* `target_congr`: the discretised target depends only on the samples of the `2^m` slots.
* `ode_time_solver_mesh`: exact gates (the released `GateODE.Time.solver` protocol and counts).
* `native_ode_time_solver_mesh`: native gates (the released `GateNative.native_ode_time_solver`
  protocol and counts).

The mesh solution is classical piecewise: one accretive, interval-integrable generator piece and
one interval-integrable, bounded forcing piece per mesh interval, solved on each closed interval.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap MeasureTheory Set OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (Label)
open GateODE.Time (TParams TOracles gens)
open TimeDependentODE (SolvesODE Accretive)
open TimeDependentExtensions (IsMesh slotPiece)
open scoped InnerProduct BigOperators Real

section Exact

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
/-- **The discretised target depends only on the slot samples**: the released
`GateODE.Time.recurrence_congr` for the represented generators `L_r + i H_r`. -/
theorem target_congr (p : TParams) (Hs Ls Hs' Ls' : ℕ → P →L[ℂ] P) (x0 : P) (bs bs' : ℕ → P)
    (hH : ∀ r < p.M, Hs r = Hs' r) (hL : ∀ r < p.M, Ls r = Ls' r)
    (hb : ∀ r < p.M, bs r = bs' r) :
    p.target Hs Ls x0 bs = p.target Hs' Ls' x0 bs' := by
  unfold TParams.target
  refine GateODE.Time.recurrence_congr _ _ _ _ _ _ _ (fun r hr => ?_) hb
  unfold gens
  rw [hH r hr, hL r hr]

/-- **Gate-efficient dissipative ODE solver on a nonuniform mesh, exact gates** (Theorem
`ode:thm:gates`, time-dependent part, extended by uniform refinement to nonuniform meshes with
breakpoints).

The released protocol `TParams.protocol p v` has the released validity, worst-case counts,
qubits and sizes of `GateODE.Time.solver` (the same conjuncts as `ode_time_solver_certified`).
For every mesh `tm` of `Mm ≥ 1` intervals on `[0, T]`, mesh samples `H_q` (self-adjoint,
`‖H_q‖ ≤ λ_H`), `L_q` (positive semidefinite, `‖L_q‖ ≤ λ_D`) and forcing samples `b̃_q`, supplied
unitaries satisfying `CoreOK` for the slot data `(H_{σ k}, L_{σ k}, b̃_{σ k})`
(`σ = slotPiece tm T 2^m Mm`), and every classical piecewise solution `x` with one accretive,
interval-integrable generator piece `G_q` and one interval-integrable forcing piece `b_q`,
`‖b_q‖ ≤ b_max`, per mesh interval, with `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` for the source mass `B` of
the slot data, and `meshCertificate ≤ ε B/(2000 g)`, the protocol satisfies the released
`Outcome`: success probability at least `175/256 > 2/3`, every successful trial within `ε/500` of
`x(T)/‖x(T)‖` up to a phase, conditional output within trace distance `ε`. -/
theorem ode_time_solver_mesh [FiniteDimensional ℂ P] (p : TParams) (hp : p.PublicOK) (v : P)
    (hv : ‖v‖ = 1) :
    (∀ j, ∀ g ∈ p.trialC j, g.Valid Wire.anc) ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wGate : ℝ) ≤
      80 * p.g * p.prepGates + 40 * p.g * p.reflGates ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPriv : ℝ) ≤ 480 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wUJ : ℝ) ≤ 960 * p.g * p.d ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wLoad : ℝ) ≤ 80 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wPrep : ℝ) ≤ 160 * p.g ∧
    ((p.protocol v hv hp.g_ge).worstCost p.wSeed : ℝ) ≤ 40 * p.g ∧
    p.prepGates = 200 * (p.d + 1) * (p.a + p.m + p.r + 1) + 3 * (2 ^ p.l * (2 * p.l + 1)) ∧
    p.reflGates = 6 * (2 * p.a + 4 * p.m + 6 * p.r + 4 + p.l) + 4 ∧
    Fintype.card p.W = 4 * p.a + 8 * p.m + 12 * p.r + 2 * p.l + 8 ∧
    (p.d : ℝ) ≤ 128 * (p.tau * p.qbar + p.Q * (1 + Real.log (3 / p.nu))) ∧
    2 * p.d + 2 ≤ 2 ^ p.r ∧ 2 ^ p.r ≤ 4 * (p.d + 1) ∧
    p.J + 2 ≤ 2 ^ p.l ∧ 2 ^ p.l < 2 * (p.J + 2) ∧
    (p.J : ℝ) ≤ p.R * (p.T * p.lamD + 2 * Real.log (512 / p.nu)) / π + 3 ∧
    ∀ (tm : ℕ → ℝ) (Mm : ℕ), 0 < Mm → IsMesh tm Mm p.T →
    ∀ (σ : TOracles p.a p.m p.l P) (Hm Lm : ℕ → P →L[ℂ] P) (bm : ℕ → P)
      (G : ℕ → ℝ → P →L[ℂ] P) (b : ℕ → ℝ → P) (x : ℝ → P) (bmax : ℝ),
      CoreOK p v σ (fun k => Hm (slotPiece tm p.T p.M Mm k))
        (fun k => Lm (slotPiece tm p.T p.M Mm k)) (x 0)
        (fun k => bm (slotPiece tm p.T p.M Mm k)) →
      (∀ q < Mm, star (Hm q) = Hm q) →
      (∀ q < Mm, ∀ w : P, 0 ≤ (inner ℂ w (Lm q w)).re) →
      (∀ q < Mm, ‖Hm q‖ ≤ p.lamH) → (∀ q < Mm, ‖Lm q‖ ≤ p.lamD) →
      (∀ q < Mm, SolvesODE (G q) (b q) x (tm q) (tm (q + 1))) →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), Accretive (G q u)) →
      (∀ q < Mm, IntervalIntegrable (G q) volume (tm q) (tm (q + 1))) →
      (∀ q < Mm, IntervalIntegrable (b q) volume (tm q) (tm (q + 1))) →
      0 ≤ bmax →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), ‖b q u‖ ≤ bmax) →
      x p.T ≠ 0 →
      p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) ≤ p.g * ‖x p.T‖ →
      meshCertificate p tm Mm Hm Lm bm G b ‖x 0‖ bmax ≤
        p.ε * p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) / (2000 * p.g) →
      p.Outcome v hv hp.g_ge σ (x p.T) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, -⟩ :=
    ode_time_solver_certified p hp v hv
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, ?_⟩
  intro tm Mm hMm hmesh σ Hm Lm bm G b x bmax hC hH hPSD hHn hLn hx hG hGint hbint hbmax hb hne
    hbud hcert
  have herr := mesh_target_error p hp.T_pos (add_nonneg hp.lamH_nonneg hp.lamD_nonneg) tm Mm hMm
    hmesh Hm Lm bm hH hPSD hHn hLn G b x bmax hbmax hx hG hGint hbint hb
  exact outcome_of p hp v hv σ _ _ (x 0) _ (x p.T) hC ⟨hne, hbud, herr.trans hcert⟩

end Exact

section Native

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **Native gate-efficient dissipative ODE solver on a nonuniform mesh** (Theorem
`ode:thm:gates`, time-dependent part, before finite-set synthesis, extended by uniform
refinement to nonuniform meshes with breakpoints).

The native protocol `nprotocol (tnprepC p UJg nd ar loadC wpC) (2g)` has the released validity,
gate, call and qubit counts of `GateNative.native_ode_time_solver` (the same conjuncts as
`native_ode_time_solver_certified`). For every mesh `tm` of `Mm ≥ 1` intervals on `[0, T]` with
mesh samples as in `ode_time_solver_mesh`, every instance whose private operations `D z r` are
given natively by `V` (`NativeOK`), with loading and weight preparation approximated within
`ζs`, `24 d ζ + 3 ζs ≤ ν`, the conditions `CoreOK` for the slot data
`(H_{σ k}, L_{σ k}, b̃_{σ k})`, and every classical piecewise solution with one generator and
forcing piece per mesh interval, `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and
`meshCertificate ≤ ε B/(2000 g)`, the protocol has the released guarantees `NOutcome`. -/
theorem native_ode_time_solver_mesh (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (tnprepC p UJg nd ar loadC wpC) j, i.Valid) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (tnprepC p UJg nd ar loadC wpC) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card Zs + Fintype.card S) + 3) ∧
    (∀ q : J → Bool,
      ((nprotocol (tnprepC p UJg nd ar loadC wpC) p.ratio (p.ratio_ge hp.g_ge)).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    Fintype.card (TNW p S Zs Z ar.bT ar.bP ar.A) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 ∧
    ∀ (tm : ℕ → ℝ) (Mm : ℕ), 0 < Mm → IsMesh tm Mm p.T →
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hm Lm : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (bm : ℕ → Reg S ℂ)
      (G : ℕ → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b : ℕ → ℝ → Reg S ℂ) (x : ℝ → Reg S ℂ)
      (bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      CoreOK p (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        (fun k => Hm (slotPiece tm p.T p.M Mm k)) (fun k => Lm (slotPiece tm p.T p.M Mm k))
        (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) →
      (∀ q < Mm, star (Hm q) = Hm q) →
      (∀ q < Mm, ∀ w : Reg S ℂ, 0 ≤ (inner ℂ w (Lm q w)).re) →
      (∀ q < Mm, ‖Hm q‖ ≤ p.lamH) → (∀ q < Mm, ‖Lm q‖ ≤ p.lamD) →
      (∀ q < Mm, SolvesODE (G q) (b q) x (tm q) (tm (q + 1))) →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), Accretive (G q u)) →
      (∀ q < Mm, IntervalIntegrable (G q) volume (tm q) (tm (q + 1))) →
      (∀ q < Mm, IntervalIntegrable (b q) volume (tm q) (tm (q + 1))) →
      0 ≤ bmax →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), ‖b q u‖ ≤ bmax) →
      x p.T ≠ 0 →
      p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) ≤ p.g * ‖x p.T‖ →
      meshCertificate p tm Mm Hm Lm bm G b ‖x 0‖ bmax ≤
        p.ε * p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) / (2000 * p.g) →
      NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard, -⟩ :=
    native_ode_time_solver_certified p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  refine ⟨hV, hG, hC, hW, hWC, hcard, ?_⟩
  intro tm Mm hMm hmesh prim D Jl Wp Hm Lm bm G b x bmax ζs hprim hN hζs hload hwp hbudget hCore
    hH hPSD hHn hLn hx hGa hGint hbint hbmax hb hne hbud hcert
  have herr := mesh_target_error p hp.T_pos (add_nonneg hp.lamH_nonneg hp.lamD_nonneg) tm Mm hMm
    hmesh Hm Lm bm hH hPSD hHn hLn G b x bmax hbmax hx hGa hGint hbint hb
  exact native_outcome_of p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ rfl hN ζs hζs hload hwp hbudget _ _ (x 0) _ (x p.T) hCore
    ⟨hne, hbud, herr.trans hcert⟩

end Native

end

end SparseHamiltonian.GateMesh.ODE
