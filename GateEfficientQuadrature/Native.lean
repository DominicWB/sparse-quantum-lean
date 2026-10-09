import GateEfficientQuadrature.Solver
import GateEfficientSelect.ODE.Native

/-!
# The native solver with the left-endpoint quadrature

The native time-dependent solver on branch-dependent meshes
(`GateSelect.ODE.native_time_outcomeB`, `GateSelect.ODE.native_ode_time_solverB`) keeps the
released native circuits, counts and wires; its instance clause assumes `BInstanceOK` for the
ideal oracles and the released error budget `24 d ζ + 3 ζs ≤ p.nu` (the released precision unit,
not the paper's `ν`). With the left-endpoint quadrature of the proof of Theorem `ode:thm:gates`
the instance clause holds under `LInstanceOK` (`native_time_outcomeL`, through
`LInstanceOK.toB`); the counts are those of `GateSelect.ODE.native_ode_time_solverB`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000

namespace SparseHamiltonian.GateQuad

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE.Time (TParams TOracles)
open scoped InnerProduct BigOperators

variable {S Zs Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- **The guarantees for one instance of the native solver with the left-endpoint quadrature.**
Under the hypotheses of `GateSelect.ODE.native_time_outcomeB` with `LInstanceOK` for the ideal
oracles in place of `BInstanceOK`, the native protocol satisfies the released `NOutcome`. -/
theorem native_time_outcomeL (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (σ : TOracles p.a p.m p.l (Reg S ℂ)) (hUJ : σ.UJ = UJop (R := ℂ) UJg)
    (hN : NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) σ.D false)))
    (ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu)
    (n : ℕ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δG Λ L bs δb : ℝ)
    (hI : LInstanceOK p n (seedV (S := S)) σ fv Hb Lb G b x ys βG δG Λ L bs δb) :
    NOutcome (tnprepC p UJg nd ar loadC wpC) p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) :=
  GateSelect.ODE.native_time_outcomeB p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
    prim hprim σ hUJ hN ζs hζs hload hwp hbudget (vQ p n) (wQ p n) fv Hb Lb G b x ys βG δG _
    (hI.toB hp)

end

end SparseHamiltonian.GateQuad
