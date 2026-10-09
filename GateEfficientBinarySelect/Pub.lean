import GateEfficientBinarySelect.Clock
import GateEfficientBinaryODETime.Pub

/-!
# The native data and the instance conditions on branch-dependent meshes

The public data are those of the time-dependent solver from binary data
(`GateBinaryODETime.PubT`: system qubits `k`, slot bits `σ`, stored bits `b`, decoder scale `c₀`,
energy bounds `η_H`, `η_D`, Cayley rescaling `γ`, time `T`, amplification bound `g`, accuracy
`ε`, mesh bits `m`, arithmetic accuracy `ζ`), with the released parameters `PubT.params` and
conditions `PubT.OK`. The time-indexed binary data are sampled on the grid of `2^(2m)` points
`g T / 2^(2m)`, which contains every sample address of the branch-dependent meshes.

* `layQ`, `kapQ`, `ndQ`, `arQ`, `prepQ`: the integer layout (`m` node bits for the duration word),
  the decoder scale, the native private operation `odeOpB` with its address program, the
  arithmetic and one native preparation of the released protocol.
* `layQ_ok`, `ndQ_public`, `arQ_ok`, `nativeOKQ`: the layout is admissible, the operation is
  public, the arithmetic hypothesis holds at accuracy `ζ`, and the native identity holds for the
  family `privFamB`.
* `ndQ_nGates`, `ndQ_nCalls`, `arQ_counts`, `card_ZA`: counts of the compute circuit (the address
  program and `28 k + 2` gates), of the arithmetic and of the address registers.
* `RestB`, `instanceB`: the conditions of `GateSelect.ODE.BInstanceOK` other than the selection
  conditions (the source quadrature on the left-endpoint nodes with arbitrary weights, the
  loading, the weight preparation, the generator path with its sample errors at the branch
  addresses, the branch solutions and the certificate), and the instance from them, the energy
  bounds and the accretivity of every grid sample.
* `RestL`, `instanceL`: the same for the left-endpoint quadrature of `GateEfficientQuadrature`
  (`GateQuad.LInstanceOK` with `2^m` nodes).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open CayleyClockInterface
open SparseHamiltonian.GateBinaryODETime (PubT gridP rhoLT_close hRoundT_ne)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GateSelect.ODE (startB BInstanceOK bsW)
open SparseHamiltonian.GateQuad (vQ wQ LInstanceOK quadMass)
open SparseHamiltonian.GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The native data -/

section Data

variable (q : PubT)

/-- The integer layout of the arithmetic of the branch operation (`m` node bits). -/
abbrev layQ : Lay := layB q.params q.b q.F

/-- The decoder scale `κ = γ √(4s) c₀ / (2^(m + F + 10) ρ)`. -/
def kapQ : ℝ := kapB q.s q.c0 q.rho q.γ q.F q.m

/-- **The native private operation on branch-dependent meshes**: the address program, the
compute circuit `computeV4` with every call reading the address bits, the orientation wire and
the decoder with scale `kapQ` and step factor `ρ_L`. -/
def ndQ : NativeOp (TSel q.params.m q.params.l q.params.m) (Fin q.params.a ⊕ Fin q.kx)
    (ZA q.m ⊕ SZ4 q.kx q.b) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query :=
  odeOpB q.kx (layQ q) q.m (kapQ q) (rhoL (gridP q.params) q.F)

/-- **The arithmetic** of the native private operation, with CORDIC accuracy `ζ/2`. -/
def arQ : Arith (NB (TSel q.params.m q.params.l q.params.m) (Fin q.params.a ⊕ Fin q.kx)
    (ZA q.m ⊕ SZ4 q.kx q.b)) :=
  odeArB q.kx (layQ q) q.m (kapQ q) (q.ζ / 2)

/-- **One native preparation** of the released protocol with the branch operation, for the
loading circuit `loadC` and the weight-preparation circuit `wpC`. -/
def prepQ {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query)) :
    List (NInstr (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
      (arQ q).A) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query) :=
  tnprepC q.params q.UJg (ndQ q) (arQ q) loadC wpC

theorem layQ_ok (hq : q.OK) : (layQ q).OK :=
  layB_ok q.params q.b q.F hq.b_pos hq.g_ge hq.ε_pos (q.ε_le_one hq) (q.TD_nonneg hq)

theorem kapQ_pos (hq : q.OK) : 0 < kapQ q :=
  kapB_pos q.s q.c0 q.rho q.γ q.F q.m (Nat.two_pow_pos _) hq.c0_pos (q.rho_pos hq) hq.γ_pos

/-- The native private operation is public. -/
theorem ndQ_public : (ndQ q).Public := odeOpB_public _ _ _ _ _

/-- **The arithmetic hypothesis** with accuracy `ζ`. -/
theorem arQ_ok (hq : q.OK) : ArithOK (arQ q) (Sum.inl (Sum.inr (ndQ q).o)) (ndQ q).dec q.ζ := by
  have hr : |rhoL (gridP q.params) q.F - 1| ≤ q.ζ / 4 :=
    rhoLT_close q.params q.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos (q.ε_le_one hq) (q.TD_nonneg hq)
  have h1 := hq.ζ_pos
  have h2 := hq.ζ_le
  exact odeArB_ok q.kx (layQ q) q.m (layQ_ok q hq) (kapQ q) (rhoL (gridP q.params) q.F)
    (q.ζ / 2) q.ζ (kapQ_pos q hq) (by linarith) (by linarith) (by linarith) (by linarith)

/-- **The gates of the compute circuit**: the address program and `28 k + 2` gates. -/
theorem ndQ_nGates :
    nGatesN (ndQ q).V = (apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2) :=
  odeOpB_nGates _ _ _ _ _

/-- The compute circuit makes two calls of each oracle. -/
theorem ndQ_nCalls (c : Query → Bool) :
    nCallsN c (ndQ q).V = 2 * (if c Query.rowLocation then 1 else 0) +
      2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0) :=
  odeOpB_nCalls _ _ _ _ _ c

/-- The number of address-register wires. -/
theorem card_ZA (m : ℕ) :
    Fintype.card (ZA m) = 1 + 2 * (2 * m + 14) + (4 * m + 62) * (2 * m + 14) := by
  show Fintype.card (CW (RO (aLay m)) (aLay m).w) = _
  rw [card_CW, card_RO, aLay_w]
  simp only [aLay, Lay.mA, Lay.mS]
  ring

/-- **The counts of the arithmetic**: those of the released `GateBinaryODE.odeArith_counts` for
the layout `layQ` (width `b + m + F + l + 14`), the decoder scale `kapQ` and the CORDIC accuracy
`ζ/2`. -/
theorem arQ_counts :
    (arQ q).circ.length ≤
      26 * (layQ q).w * (31 + ((layQ q).F + 2) + 3 + ((layQ q).mA + 1) + 2 * ((layQ q).mS + 1)) +
        (156 * (Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).w *
            ((Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).n + 1) +
          (Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).bP +
          2 * (Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).bT) ∧
    (arQ q).A =
      (1 + 2 * (layQ q).w + (31 + ((layQ q).F + 2) + 3 + ((layQ q).mA + 1) +
          2 * ((layQ q).mS + 1)) * (layQ q).w) +
        (1 + 2 * (Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).w +
          (6 * ((Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).n + 1) + 1) *
            (Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).w) ∧
    (arQ q).bT = (Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).bT ∧
    (arQ q).bP = (Cordic.params (layQ q).w (kapQ q) (q.ζ / 2)).bP :=
  odeArith_counts (inpBB q.kx (layQ q) q.m) (kapQ q) (q.ζ / 2)

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The native identity** of the private operation on branch-dependent meshes, for the
time-indexed binary data on the grid of `2^(2m)` points. -/
theorem nativeOKQ (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) (x : X) :
    NativeOK (primsT (R := ℂ) (m := 2 * q.m) D en x) (ndQ q)
      (selOp (tlabFam (P := Reg (Fin q.kx) ℂ) (privFamB q.params D en x q.rho q.γ) false)) := by
  obtain ⟨k0, hk0⟩ : ∃ m, D.slot m = zIdx en := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  exact nativeOK_B q.params D en k0 hk0 x q.c0 hq.c0_pos.ne' hdec q.rho q.γ (q.rho_pos hq).ne'
    q.F (hRoundT_ne q.params q.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos (q.ε_le_one hq)
      (q.TD_nonneg hq))

end Data

/-! ### The instance conditions -/

section Instance

variable (q : PubT) {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The selection conditions from binary data**: `U_J` and the private operations are unitary,
the lifted branch samples are self-adjoint with `‖H‖ ≤ λ_H`, `‖L‖ ≤ λ_D` and `L ≥ 0`, and the
clock promises hold at every label and slot. -/
theorem selectB (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re) :
    IsUnitary (UJop (R := ℂ) q.UJg) ∧
    (∀ z : Label q.params.m q.params.l, ∀ r < q.params.M,
      IsUnitary (privFamB q.params D en x q.rho q.γ z r)) ∧
    (∀ z : Label q.params.m q.params.l, ∀ r < q.params.M,
      GateODE.ClockPromise (P := Reg (Fin q.kx) ℂ) (a := q.params.a) (UJop (R := ℂ) q.UJg)
      (privFamB q.params D en x q.rho q.γ z r)
      (GateSelect.ODE.branchHB q.params (vQ q.params q.params.M) (HbB q.params D en x)
        (LbB q.params D en x) z r) q.params.Q q.params.qbar) ∧
    (∀ s, ∀ r < q.params.M, star (HbB q.params D en x s r) = HbB q.params D en x s r) ∧
    (∀ s, ∀ r < q.params.M, star (LbB q.params D en x s r) = LbB q.params D en x s r) ∧
    (∀ s, ∀ r < q.params.M, ‖HbB q.params D en x s r‖ ≤ q.params.lamH) ∧
    (∀ s, ∀ r < q.params.M, ‖LbB q.params D en x s r‖ ≤ q.params.lamD) ∧
    (∀ s, ∀ r < q.params.M, ∀ w : Reg (Fin q.kx) ℂ,
      0 ≤ (inner ℂ w (LbB q.params D en x s r w)).re) := by
  refine ⟨UJop_isUnitary _ (hadUJ4_ok q.σ q.hσ),
    fun z r _ => privFamB_isUnitary _ _ _ _ _ _ z r,
    fun z r hr => clockB q.params D en q.σ q.hσ rfl hrange x q.etaH q.etaD q.rho q.γ
      hq.etaH_nonneg hq.etaD_nonneg rfl (q.rho_pos hq) hq.γ_pos hq.T_pos hq.g_ge hq.ε_pos
      (q.ε_le_one hq) (q.TD_nonneg hq) q.tau_eq hrH hcH hrD hcD z r hr, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun s r _ => HbB_self q.params D en x s r
  · exact fun s r _ => LbB_self q.params D en x s r
  · exact fun s r _ => (HbB_norm_le q.params D en x q.etaH hq.etaH_nonneg hrH hcH s r).trans
      (q.sqrt_le_lam hq q.etaH hq.etaH_nonneg)
  · exact fun s r _ => (LbB_norm_le q.params D en x q.etaD hq.etaD_nonneg hrD hcD s r).trans
      (q.sqrt_le_lam hq q.etaD hq.etaD_nonneg)
  · exact fun s r _ w => LbB_psd q.params D en x hPSD s r w

/-- **The remaining instance conditions on branch-dependent meshes**: those of
`GateSelect.ODE.BInstanceOK` other than the selection conditions, for the `2^m` left-endpoint
nodes `u T / 2^m` and arbitrary nonnegative weights `w_u` of a positive source quadrature. The
loading `Jl` is unitary and places the normalised initial state and forcing vectors, the weight
preparation `Wp` is unitary with the amplitudes `√(‖z_s‖/B)` in its zero column; `xs` solves
`x' = -G(u) x + b(u)` on `[0, T]` for an accretive `βG`-Lipschitz path `G` within `δG` of the
lifted samples at the branch addresses only: `G(addrN s r · T / 2^(2m))` against the lifted
sample `M̂` at the grid point `addrN s r`, the address `v_s + r (T - v_s)/2^m` of slot `r` of the
branch of the source label `s` (`addrB_vQ`); the branch solutions `ys` of the homogeneous
equation from the branch starts with the source vectors `w_u f_u` give the source certificate
`κ`; `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and the budget of `BInstanceOK` holds. -/
structure RestB (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δG κ : ℝ) : Prop where
  weights : ∀ u < q.params.M, 0 ≤ wq u
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) =
      ((q.params.srcAmp (xs 0) (bsW q.params wq fv) (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : xs 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (xs 0)
  forcing_load : ∀ w : Fin q.m → Bool, wq (wordValue w) ≠ 0 → fv (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (fv (wordValue w))
  solves : TimeDependentODE.SolvesODE G bf xs 0 q.T
  accretive : ∀ u ∈ Set.Icc 0 q.T, TimeDependentODE.Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleG : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
    ‖G (addrN s r * q.T / 2 ^ (2 * q.m)) - mLift D en (x, addrF s r hr)‖ ≤ δG
  branch_sol : ∀ s, TimeDependentODE.SolvesODE G (fun _ => 0) (ys s)
    (startB q.params (vQ q.params q.params.M) s) q.T
  branch_init : ∀ s, ys s (startB q.params (vQ q.params q.params.M) s) =
    q.params.zsrc (xs 0) (bsW q.params wq fv) s
  quad : ‖xs q.T - ∑ s, ys s q.T‖ ≤ κ
  target_ne : xs q.T ≠ 0
  budget : q.params.mass (xs 0) (bsW q.params wq fv) ≤ q.g * ‖xs q.T‖
  disc : κ + q.T * (βG * (q.T / q.params.M) + δG) * q.params.mass (xs 0) (bsW q.params wq fv) ≤
    q.ε * q.params.mass (xs 0) (bsW q.params wq fv) / (2000 * q.g)

/-- The sample condition at the grid addresses `addrN s r` is the sample condition of
`GateSelect.ODE.BInstanceOK` at the branch addresses `addrB` against the represented slot
generators. -/
theorem sampleG_addr (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (δG : ℝ) (hG : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      ‖G (addrN s r * q.T / 2 ^ (2 * q.m)) - mLift D en (x, addrF s r hr)‖ ≤ δG) :
    ∀ s, ∀ r < q.params.M, ‖G (GateSelect.ODE.addrB q.params (vQ q.params q.params.M) s r) -
      GateODE.Time.gens (HbB q.params D en x s) (LbB q.params D en x s) r‖ ≤ δG := by
  intro s r hr
  rw [gensB_eq q.params D en x s r hr, addrB_vQ]
  exact hG s r hr

/-- **The instance conditions on branch-dependent meshes from binary data**: the selection
conditions from the energy bounds and the accretivity of every grid sample (`selectB`) and the
remaining conditions `RestB`. -/
theorem instanceB (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δG κ : ℝ) (hR : RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ) :
    BInstanceOK q.params (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (vQ q.params q.params.M) wq fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys
      βG δG κ := by
  obtain ⟨huj, hpriv, hclock, hsH, hsL, hnH, hnL, hpsd⟩ :=
    selectB q hq D en hrange x hrH hcH hrD hcD hPSD
  exact
    { uj := huj
      priv := hpriv
      clock := hclock
      selfH := hsH
      selfL := hsL
      normH := hnH
      normL := hnL
      psd := hpsd
      nodes := GateQuad.vQ_mem q.params hq.T_pos.le _
      weights := hR.weights
      load_unitary := hR.load_unitary
      prep_left := hR.prep_left
      prep_right := hR.prep_right
      prep := hR.prep
      init_load := hR.init_load
      forcing_load := hR.forcing_load
      solves := hR.solves
      accretive := hR.accretive
      lipG := hR.lipG
      βG_nonneg := hR.βG_nonneg
      sampleG := sampleG_addr q D en x G δG hR.sampleG
      branch_sol := hR.branch_sol
      branch_init := hR.branch_init
      quad := hR.quad
      target_ne := hR.target_ne
      budget := hR.budget
      disc := hR.disc }

/-- **The remaining instance conditions with the left-endpoint quadrature**: those of
`GateQuad.LInstanceOK` with `n = 2^m` nodes `u T / 2^m` and weights `T / 2^m` (the released
structure allows any `n ≤ 2^m`) other than the selection conditions. Besides the loading, the
weight preparation, the solution and the sample errors at the branch addresses as in `RestB`:
`‖G(u)‖ ≤ Λ`, an `L`-Lipschitz forcing `b` with samples `‖f_u‖ ≤ b_s`,
`‖b(u T / 2^m) - f_u‖ ≤ δb`, the left-endpoint mass `B_m ≤ g ‖x(T)‖` and the budget with the
certificate `(Λ b_s + L) T² / 2^(m+1) + T δb`. -/
structure RestL (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δG Λ L bs δb : ℝ) : Prop where
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) =
      ((q.params.srcAmp (xs 0) (bsW q.params (wQ q.params q.params.M) fv) (w 0, Fin.tail w) :
        ℝ) : ℂ)
  init_load : xs 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (xs 0)
  forcing_load : ∀ w : Fin q.m → Bool, fv (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection (fv (wordValue w))
  solves : TimeDependentODE.SolvesODE G bf xs 0 q.T
  accretive : ∀ u ∈ Set.Icc 0 q.T, TimeDependentODE.Accretive (G u)
  lipG : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleG : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
    ‖G (addrN s r * q.T / 2 ^ (2 * q.m)) - mLift D en (x, addrF s r hr)‖ ≤ δG
  normG : ∀ u ∈ Set.Icc 0 q.T, ‖G u‖ ≤ Λ
  lipb : ∀ u ∈ Set.Icc 0 q.T, ∀ u' ∈ Set.Icc 0 q.T, ‖bf u - bf u'‖ ≤ L * |u - u'|
  L_nonneg : 0 ≤ L
  sample_norm : ∀ u < q.params.M, ‖fv u‖ ≤ bs
  sample_err : ∀ u < q.params.M, ‖bf (u * q.T / q.params.M) - fv u‖ ≤ δb
  branch_sol : ∀ s, TimeDependentODE.SolvesODE G (fun _ => 0) (ys s)
    (startB q.params (vQ q.params q.params.M) s) q.T
  branch_init : ∀ s, ys s (startB q.params (vQ q.params q.params.M) s) =
    q.params.zsrc (xs 0) (bsW q.params (wQ q.params q.params.M) fv) s
  target_ne : xs q.T ≠ 0
  budget : quadMass (xs 0) fv q.T q.params.M ≤ q.g * ‖xs q.T‖
  disc : (Λ * bs + L) * q.T ^ 2 / (2 * q.params.M) + q.T * δb +
      q.T * (βG * (q.T / q.params.M) + δG) * quadMass (xs 0) fv q.T q.params.M ≤
    q.ε * quadMass (xs 0) fv q.T q.params.M / (2000 * q.g)

/-- **The instance conditions with the left-endpoint quadrature from binary data.** -/
theorem instanceL (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δG Λ L bs δb : ℝ) (hR : RestL q D en x Jl Wp fv G bf xs ys βG δG Λ L bs δb) :
    LInstanceOK q.params q.params.M (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δG Λ L bs δb := by
  obtain ⟨huj, hpriv, hclock, hsH, hsL, hnH, hnL, hpsd⟩ :=
    selectB q hq D en hrange x hrH hcH hrD hcD hPSD
  exact
    { n_pos := q.params.M_pos
      n_le := le_rfl
      uj := huj
      priv := hpriv
      clock := hclock
      selfH := hsH
      selfL := hsL
      normH := hnH
      normL := hnL
      psd := hpsd
      load_unitary := hR.load_unitary
      prep_left := hR.prep_left
      prep_right := hR.prep_right
      prep := hR.prep
      init_load := hR.init_load
      forcing_load := fun w _ hf => hR.forcing_load w hf
      solves := hR.solves
      accretive := hR.accretive
      lipG := hR.lipG
      βG_nonneg := hR.βG_nonneg
      sampleG := sampleG_addr q D en x G δG hR.sampleG
      normG := hR.normG
      lipb := hR.lipb
      L_nonneg := hR.L_nonneg
      sample_norm := hR.sample_norm
      sample_err := hR.sample_err
      branch_sol := hR.branch_sol
      branch_init := hR.branch_init
      target_ne := hR.target_ne
      budget := hR.budget
      disc := hR.disc }

end Instance

end

end SparseHamiltonian.GateBinarySelect
