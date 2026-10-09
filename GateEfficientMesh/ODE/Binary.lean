import GateEfficientMesh.ODE.Native
import GateEfficientBinaryODETime.Solver

/-!
# The time-dependent ODE solver from binary sparse data under integrated certificates

The released `GateBinaryODETime.binary_ode_time_solver` (Theorem `ode:thm:gates`, time-dependent
part, from time-indexed binary sparse oracles, before finite-set synthesis) constructs every
implementation of the native solver from the public data `q : PubT` and derives the selection
conditions of the instance from row and column energy bounds and accretivity of every sample
(`PubT.selectHyp`, `PubT.nativeOK`); the source, path and target conditions (`PubT.Rest`,
with a Lipschitz path) remain hypotheses. Here the path conditions are replaced by the
integrated certificate on the uniform slots:

* `binary_coreOK`: the oracles constructed from the binary data satisfy `CoreOK` for the lifted
  samples (the released `PubT.selectHyp`), given the source conditions `SourceOK`;
* `binary_ode_time_solver_certified`: the released counts, and the native guarantees for every
  classical piecewise solution on the slots under the budget `slotCertificate ≤ ε B/(2000 g)`
  with the represented slot generators `L_r + i H_r = M̂_r` (the released `gensT_eq`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime
open NativeSparseBlockEncoding (Data Query)
open MeasureTheory Set
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The conditions on the supplied unitaries from binary data**: for row and column energies
of the Hamiltonian and dissipative parts of every sample at most `η_H²` and `η_D²`, accretive
dissipative parts and source unitaries satisfying `SourceOK`, the oracles constructed from the
binary data (`U_J` of the released `PubT.UJg`, the private operations `privFamT`) satisfy
`CoreOK` for the lifted samples `HsT`, `LsT` (the released `PubT.selectHyp`, `LsT_of_lt` and
`re_inner_qlift_nonneg`). -/
theorem binary_coreOK (q : PubT) (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (x0 : Reg (Fin q.kx) ℂ)
    (bs : ℕ → Reg (Fin q.kx) ℂ) (hS : SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp x0 bs) :
    CoreOK q.params (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩ :
        GateODE.Time.TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (GateBinaryODETime.HsT D en x) (GateBinaryODETime.LsT D en x) x0 bs :=
  ⟨q.selectHyp hq D en hrange x hrH hcH hrD hcD Jl Wp, fun r hr w => by
    rw [LsT_of_lt D en x r hr]
    exact re_inner_qlift_nonneg en _ (hPSD _) w, hS⟩

/-- **Native gate-efficient dissipative ODE solver from time-indexed binary sparse data under the
integrated certificate on the uniform slots** (Theorem `ode:thm:gates`, time-dependent part,
before finite-set synthesis: "more generally, a certificate for the same uniform meshes
suffices").

For public data `q` satisfying the public conditions and time-indexed native sparse data `D` in
the released binary format, the native preparation `q.prep loadC wpC` and the protocol have the
released validity, gate, call and qubit counts of `GateBinaryODETime.binary_ode_time_solver`.
For every input `x` whose samples have Hamiltonian and dissipative parts with row and column
energies at most `η_H²` and `η_D²` and accretive dissipative parts, every loading `Jl` and
weight preparation `Wp` approximated within `ζs` by the two circuits with `24 d ζ + 3 ζs ≤ ν`
and satisfying the source conditions `SourceOK`, and every classical piecewise solution `xs` on
the uniform slots with accretive, interval-integrable generator pieces `G_k` and
interval-integrable forcing pieces `b_k` bounded by `b_max ≥ 0`, with `xs(T) ≠ 0`,
`B ≤ g ‖xs(T)‖` and the certified budget `slotCertificate ≤ ε B/(2000 g)` against the lifted
samples `M̂_r = L_r + i H_r`, the protocol succeeds with probability at least `2/3`, every
successful trial is within `ε/500` of `xs(T)/‖xs(T)‖` up to a phase, and the conditional output
is within trace distance `ε` of `xs(T)/‖xs(T)‖`. -/
theorem binary_ode_time_solver_certified (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, ∀ i ∈ trialN (q.prep loadC wpC) j, i.Valid) ∧
    nGatesN (q.prep loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (q.prep loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (q.prep loadC wpC) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
          3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (q.prep loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0) bs →
      (∀ k < q.params.M, SolvesODE (G k) (bf k) xs (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        Accretive (G k u)) →
      (∀ k < q.params.M, IntervalIntegrable (G k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, IntervalIntegrable (bf k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      0 ≤ bmax →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        ‖bf k u‖ ≤ bmax) →
      xs q.T ≠ 0 → q.params.mass (xs 0) bs ≤ q.g * ‖xs q.T‖ →
      slotCertificate q.params (GateBinaryODETime.HsT D en x) (GateBinaryODETime.LsT D en x) bs G
        bf ‖xs 0‖ bmax ≤
        q.ε * q.params.mass (xs 0) bs / (2000 * q.g) →
      NOutcome (q.prep loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard⟩ := binary_ode_time_counts q hq loadC hloadV wpC hwpV
  obtain ⟨-, -, -, -, -, -, hout⟩ :=
    native_ode_time_solver_certified q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd
      q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV
  refine ⟨hV, hG, hC, hW, hWC, hcard, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs bmax ζs hζs hload hwp hbud hS hx hGa hGint hbint
    hbmax hb hne hB hcert
  have hCore := binary_coreOK q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp (xs 0) bs hS
  exact hout (primsT (R := ℂ) D en x) (privFamT q.params D en x q.rho q.γ) Jl Wp
    (GateBinaryODETime.HsT D en x) (GateBinaryODETime.LsT D en x) G bf xs bs bmax ζs
    (primsT_isUnitary D en x) (q.nativeOK hq D en hrange hdec x) hζs hload hwp hbud hCore hx hGa
    hGint hbint hbmax hb hne hB hcert

end Main

end

end SparseHamiltonian.GateMesh.ODE
