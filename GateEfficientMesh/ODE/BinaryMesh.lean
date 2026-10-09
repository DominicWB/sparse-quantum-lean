import GateEfficientMesh.ODE.Binary
import GateEfficientMesh.ODE.Mesh
import GateEfficientMesh.BinaryMesh

/-!
# The time-dependent ODE solver from binary sparse data on a nonuniform mesh

Theorem `ode:thm:gates`, time-dependent part, from time-indexed binary sparse oracles, extended
by uniform refinement to nonuniform meshes with breakpoints. A mesh `0 = t_0 ≤ ⋯ ≤ t_M = T`
carries one sample `M_q = D_m.matrix (x, q)` per interval, given by native sparse data
`D_m : Data (X × Fin M)` in the released binary format, and one forcing sample `b̃_q` per
interval. The released binary solver runs on the uniform clock of `2^m` slots
with the re-indexed data `clockData D_m` (`(x, k) ↦ D_m (x, σ k)`, the released `stageData` along
the slot-to-sample map `σ = slotPiece`; module `BinaryMesh`), whose time-indexed primitive
oracles are the coherent sampled-time oracles of the mesh data (`primsT_clockData`).

* `meshH`, `meshL`: the lifted Hamiltonian and dissipative parts `H_q`, `L_q` of the mesh
  samples; `meshGens_eq`: the represented mesh generators `L_q + i H_q` are the lifted mesh
  samples `M̂_q`; `HsT_clockData`, `LsT_clockData`: the slot samples of the clock data are the
  mesh samples of the containing intervals.
* `mesh_promises`: the mesh samples satisfy the sample promises of the released selection
  hypotheses (self-adjoint, `‖H_q‖ ≤ λ_H`, `‖L_q‖ ≤ λ_D`), from the released `PubT.selectHyp`
  on the clock data that read one mesh interval at every slot.
* `binary_mesh_targetOK`: the conditions on the final state (`TargetOK`) for the discretised
  target of the clock data, from the mesh certificate (`mesh_target_error`, `target_congr`).
* `binary_ode_time_solver_mesh`: the released binary protocol and counts (the mesh enters only
  through `m`), correct under the mesh certificate `meshCertificate ≤ ε B/(2000 g)` for classical
  piecewise solutions with one generator and forcing piece per mesh interval.
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
open TimeDependentExtensions (IsMesh slotPiece slotPiece_lt)
open scoped InnerProduct

section Samples

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s k M : ℕ}

/-- The lifted Hamiltonian part `H_q` of the sample of mesh interval `q` (zero beyond the last
interval). -/
def meshH (D : Data (X × Fin M) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (q : ℕ) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : q < M then hLift D en (x, ⟨q, h⟩) else 0

/-- The lifted dissipative part `L_q` of the sample of mesh interval `q` (zero beyond the last
interval). -/
def meshL (D : Data (X × Fin M) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (q : ℕ) :
    Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ :=
  if h : q < M then lLift D en (x, ⟨q, h⟩) else 0

/-- The represented mesh generators are the lifted mesh samples `M̂_q` (the mesh analogue of the
released `GateBinaryODETime.gensT_eq`). -/
theorem meshGens_eq (D : Data (X × Fin M) n Z s) (en : Cfg (Fin k) ≃ n) (x : X) (q : ℕ)
    (hq : q < M) :
    GateODE.Time.gens (meshH D en x) (meshL D en x) q = mLift D en (x, ⟨q, hq⟩) := by
  rw [GateODE.Time.gens, meshH, meshL, dif_pos hq, dif_pos hq]
  have h := gen_lift D en (x, ⟨q, hq⟩)
  unfold GateODE.gen at h
  rw [← neg_neg (mLift D en (x, ⟨q, hq⟩)), ← h, neg_neg]

/-- The Hamiltonian slot samples of the clock data are the mesh samples of the containing
intervals. -/
theorem HsT_clockData (D : Data (X × Fin M) n Z s) (hM : 0 < M) (tm : ℕ → ℝ) (T : ℝ) (m : ℕ)
    (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ) (hr : r < 2 ^ m) :
    GateBinaryODETime.HsT (clockData D hM tm T m) en x r =
      meshH D en x (slotPiece tm T (2 ^ m) M r) := by
  rw [HsT_of_lt _ en x r hr, meshH, dif_pos (slotPiece_lt hM r)]
  rfl

/-- The dissipative slot samples of the clock data are the mesh samples of the containing
intervals. -/
theorem LsT_clockData (D : Data (X × Fin M) n Z s) (hM : 0 < M) (tm : ℕ → ℝ) (T : ℝ) (m : ℕ)
    (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ) (hr : r < 2 ^ m) :
    GateBinaryODETime.LsT (clockData D hM tm T m) en x r =
      meshL D en x (slotPiece tm T (2 ^ m) M r) := by
  rw [LsT_of_lt _ en x r hr, meshL, dif_pos (slotPiece_lt hM r)]
  rfl

end Samples

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The sample promises on the mesh**: for row and column energies of the Hamiltonian and
dissipative parts at most `η_H²` and `η_D²`, every mesh sample has `H_q` self-adjoint,
`‖H_q‖ ≤ λ_H` and `‖L_q‖ ≤ λ_D` (the released `PubT.selectHyp` on the clock data
`stageData D_m (fun _ => q)` that read interval `q` at every slot). -/
theorem mesh_promises (q : PubT) (hq : q.OK) {Mm : ℕ}
    (D : Data (X × Fin Mm) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (r : ℕ) (hr : r < Mm) :
    star (meshH D en x r) = meshH D en x r ∧ ‖meshH D en x r‖ ≤ q.params.lamH ∧
      ‖meshL D en x r‖ ≤ q.params.lamD := by
  set Dr : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s :=
    ODELowerBoundExtensions.Release.stageData D (fun _ : Fin (2 ^ q.m) => (⟨r, hr⟩ : Fin Mm))
    with hDr
  have hS := q.selectHyp hq Dr en hrange x (fun _ => hrH _) (fun _ => hcH _) (fun _ => hrD _)
    (fun _ => hcD _) (fun _ => 1) 0
  have h0 : 0 < 2 ^ q.m := Nat.two_pow_pos _
  have eH : GateBinaryODETime.HsT Dr en x 0 = meshH D en x r := by
    rw [HsT_of_lt _ en x 0 h0, meshH, dif_pos hr]
    rfl
  have eL : GateBinaryODETime.LsT Dr en x 0 = meshL D en x r := by
    rw [LsT_of_lt _ en x 0 h0, meshL, dif_pos hr]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← eH]
    exact hS.selfH 0 h0
  · rw [← eH]
    exact hS.normH 0 h0
  · rw [← eL]
    exact hS.normL 0 h0

/-- **The conditions on the final state from the mesh certificate**: for mesh samples given by
binary data with row and column energies at most `η_H²`, `η_D²` and accretive dissipative parts,
and a classical piecewise solution `xs` with one accretive, interval-integrable generator piece
and one interval-integrable, bounded forcing piece per mesh interval, `xs(T) ≠ 0`,
`B ≤ g ‖xs(T)‖` and `meshCertificate ≤ ε B/(2000 g)`, the discretised target of the clock data
(slot samples `HsT`, `LsT` of `clockData D_m`, slot forcing `b̃_{σ k}`) satisfies `TargetOK`
(`mesh_target_error`, `target_congr`, `HsT_clockData`, `LsT_clockData`). -/
theorem binary_mesh_targetOK (q : PubT) (hq : q.OK) {Mm : ℕ} (hMm : 0 < Mm) (tm : ℕ → ℝ)
    (hmesh : IsMesh tm Mm q.T) (D : Data (X × Fin Mm) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re)
    (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (bm : ℕ → Reg (Fin q.kx) ℂ) (bmax : ℝ)
    (hx : ∀ r < Mm, SolvesODE (G r) (bf r) xs (tm r) (tm (r + 1)))
    (hGa : ∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), Accretive (G r u))
    (hGint : ∀ r < Mm, IntervalIntegrable (G r) volume (tm r) (tm (r + 1)))
    (hbint : ∀ r < Mm, IntervalIntegrable (bf r) volume (tm r) (tm (r + 1)))
    (hbmax : 0 ≤ bmax) (hb : ∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), ‖bf r u‖ ≤ bmax)
    (hne : xs q.T ≠ 0)
    (hB : q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) ≤
      q.g * ‖xs q.T‖)
    (hcert : meshCertificate q.params tm Mm (meshH D en x) (meshL D en x) bm G bf ‖xs 0‖ bmax ≤
      q.ε * q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) /
        (2000 * q.g)) :
    TargetOK q.params (GateBinaryODETime.HsT (clockData D hMm tm q.T q.m) en x)
      (GateBinaryODETime.LsT (clockData D hMm tm q.T q.m) en x) (xs 0)
      (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) (xs q.T) := by
  have hp := q.params_ok hq
  have hprom := fun r (hr : r < Mm) => mesh_promises q hq D en hrange x hrH hcH hrD hcD r hr
  have hPSDm : ∀ r < Mm, ∀ w : Reg (Fin q.kx) ℂ, 0 ≤ (inner ℂ w (meshL D en x r w)).re := by
    intro r hr w
    rw [meshL, dif_pos hr]
    exact re_inner_qlift_nonneg en _ (hPSD _) w
  have herr := mesh_target_error q.params hp.T_pos (add_nonneg hp.lamH_nonneg hp.lamD_nonneg)
    tm Mm hMm hmesh (meshH D en x) (meshL D en x) bm (fun r hr => (hprom r hr).1) hPSDm
    (fun r hr => (hprom r hr).2.1) (fun r hr => (hprom r hr).2.2) G bf xs bmax hbmax hx hGa
    hGint hbint hb
  have htarget : q.params.target (GateBinaryODETime.HsT (clockData D hMm tm q.T q.m) en x)
      (GateBinaryODETime.LsT (clockData D hMm tm q.T q.m) en x) (xs 0)
      (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) =
      q.params.target (fun k => meshH D en x (slotPiece tm q.params.T q.params.M Mm k))
        (fun k => meshL D en x (slotPiece tm q.params.T q.params.M Mm k)) (xs 0)
        (fun k => bm (slotPiece tm q.params.T q.params.M Mm k)) :=
    target_congr _ _ _ _ _ _ _ _ (fun r hr => HsT_clockData D hMm tm q.T q.m en x r hr)
      (fun r hr => LsT_clockData D hMm tm q.T q.m en x r hr) (fun _ _ => rfl)
  refine ⟨hne, hB, ?_⟩
  rw [htarget]
  exact herr.trans hcert

/-- **Native gate-efficient dissipative ODE solver from binary sparse data on a nonuniform
mesh** (Theorem `ode:thm:gates`, time-dependent part, before finite-set synthesis, extended by
uniform refinement to nonuniform meshes with breakpoints).

Let `0 = t_0 ≤ ⋯ ≤ t_M = T` be a mesh (`M ≥ 1`) whose samples `M_q` are given by native sparse
data `D_m : Data (X × Fin M)` in the released binary format. The native preparation
`q.prep loadC wpC` and the protocol have the released validity, gate, call and qubit counts of
`GateBinaryODETime.binary_ode_time_solver` (the same conjuncts as
`binary_ode_time_solver_certified`; the mesh enters only through `m`). They run on the clock
data `clockData D_m` (slot `k` reads the sample of the interval containing `k T / 2^m`, through
the oracles of `primsT_clockData`). For every input `x` whose mesh samples have Hamiltonian and
dissipative parts with row and column energies at most `η_H²` and `η_D²` and accretive
dissipative parts, every loading `Jl` and weight preparation `Wp` approximated within `ζs` with
`24 d ζ + 3 ζs ≤ ν` and satisfying `SourceOK` for the slot forcing samples `b̃_{σ k}`, and every
classical piecewise solution `xs` with one accretive, interval-integrable generator piece `G_q`
and one interval-integrable forcing piece `b_q`, `‖b_q‖ ≤ b_max`, per mesh interval, with
`xs(T) ≠ 0`, `B ≤ g ‖xs(T)‖` and `meshCertificate ≤ ε B/(2000 g)` against the lifted mesh
samples `L_q + i H_q = M̂_q`, the protocol has the released guarantees `NOutcome`: success
probability at least `2/3`, every successful trial within `ε/500` of `xs(T)/‖xs(T)‖` up to a
phase, conditional output within trace distance `ε`. -/
theorem binary_ode_time_solver_mesh (q : PubT) (hq : q.OK) {Mm : ℕ} (hMm : 0 < Mm)
    (tm : ℕ → ℝ) (hmesh : IsMesh tm Mm q.T)
    (D : Data (X × Fin Mm) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
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
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bm : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) wpC)
        (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0)
        (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) →
      (∀ r < Mm, SolvesODE (G r) (bf r) xs (tm r) (tm (r + 1))) →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), Accretive (G r u)) →
      (∀ r < Mm, IntervalIntegrable (G r) volume (tm r) (tm (r + 1))) →
      (∀ r < Mm, IntervalIntegrable (bf r) volume (tm r) (tm (r + 1))) →
      0 ≤ bmax →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), ‖bf r u‖ ≤ bmax) →
      xs q.T ≠ 0 →
      q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) ≤ q.g * ‖xs q.T‖ →
      meshCertificate q.params tm Mm (meshH D en x) (meshL D en x) bm G bf ‖xs 0‖ bmax ≤
        q.ε * q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) /
          (2000 * q.g) →
      NOutcome (q.prep loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) (xs q.T) := by
  obtain ⟨hV, hG, hC, hW, hWC, hcard⟩ := binary_ode_time_counts q hq loadC hloadV wpC hwpV
  refine ⟨hV, hG, hC, hW, hWC, hcard, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bm bmax ζs hζs hload hwp hbud hS hx hGa hGint hbint
    hbmax hb hne hB hcert
  have hp := q.params_ok hq
  set Dc : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s := clockData D hMm tm q.T q.m with hDc
  have hrangeC : ∀ j : n, (∃ m, Dc.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u) :=
    hrange
  have hdecC : ∀ e z, Dc.decode e z = (q.c0 : ℂ) * gauss z := hdec
  have hCore := binary_coreOK q hq Dc en hrangeC x (fun _ => hrH _) (fun _ => hcH _)
    (fun _ => hrD _) (fun _ => hcD _) (fun _ => hPSD _) Jl Wp (xs 0)
    (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) hS
  have hTarget := binary_mesh_targetOK q hq hMm tm hmesh D en hrange x hrH hcH hrD hcD hPSD G bf
    xs bm bmax hx hGa hGint hbint hbmax hb hne hB hcert
  exact native_outcome_of q.params hp q.UJg (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public q.ar q.ζ
    hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV (primsT (R := ℂ) Dc en x)
    (primsT_isUnitary Dc en x) ⟨UJop (R := ℂ) q.UJg, privFamT q.params Dc en x q.rho q.γ, Jl, Wp⟩
    rfl (q.nativeOK hq Dc en hrangeC hdecC x) ζs hζs hload hwp hbud
    (GateBinaryODETime.HsT Dc en x) (GateBinaryODETime.LsT Dc en x)
    (xs 0) _ (xs q.T) hCore hTarget

end Main

end

end SparseHamiltonian.GateMesh.ODE
