import GateEfficientBinaryNodes.NodeClock

/-!
# The native data and the instance conditions for computed nodes

The public data are those of the time-dependent solver from binary data
(`GateBinaryODETime.PubT`, with the released parameters `PubT.params` and conditions `PubT.OK`;
`m` is the slot exponent and the number of node bits of the source label), together with

* the node precision `μ` (node words of `μ` bits, nodes `word u · T / 2^μ`) and a node program
  `N : NodeProg m μ Zn` satisfying `NodeProg.OK`;
* the data precision `nd ≤ μ + m`: the time-indexed binary data are sampled on the grid of
  `2^nd` points `g T / 2^nd`, and slot `r` of the branch of `s` reads the grid point
  `addrFN s r = ⌊A / 2^(μ+m-nd)⌋` of its exact address `A = addrNN s r` on the grid of
  `2^(μ+m)` points.

* `layQN`, `kapQN`, `ndQN`, `arQN`, `prepQN`: the integer layout (`μ` duration bits), the decoder
  scale, the native private operation `odeOpN` with the node and address programs, the
  arithmetic and one native preparation of the released protocol.
* `layQN_ok`, `ndQN_public`, `arQN_ok`, `nativeOKQN`: the layout is admissible, the operation is
  public, the arithmetic hypothesis holds at accuracy `ζ`, and the native identity holds for the
  family `privFamN`.
* `ndQN_nGates`, `ndQN_nCalls`, `arQN_counts`, `card_ZaN`: counts.
* `selectN`: the selection conditions from the energy bounds of the samples the branches read.
* `sampleErrNQ`, `sampleErrB_NQ`: the integrated represented-sample error of a branch, the error
  of the lifted samples at the rounded grid points against the generator path at the exact
  addresses, weighted by the slot length `(2^μ - ν') T / 2^(μ+m)`.
* `RestN`, `instanceN`: the remaining conditions (positive source quadrature with the computed
  nodes and arbitrary weights, loading, weight preparation, path, integrated certificate, branch
  solutions, source certificate `κ`, budget) and the integrated instance
  `BInstanceOKI` from them.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open CayleyClockInterface
open SparseHamiltonian.GateBinaryODETime (PubT gridP rhoLT_close hRoundT_ne)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GateSelect.ODE (startB bsW)
open SparseHamiltonian.GatePointerEncoding (wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open NativeSparseBlockEncoding (Data Query)
open Set (Icc)
open scoped InnerProduct

/-! ### The native data -/

section Data

variable (q : PubT) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) {Zn : Type} [Fintype Zn] [DecidableEq Zn]
  (N : NodeProg q.m mu Zn)

/-- The integer layout of the arithmetic of the branch operation (`μ` duration bits). -/
abbrev layQN : Lay := layN q.params mu q.b q.F

/-- The decoder scale `κ = γ √(4s) c₀ / (2^(μ + F + 10) ρ)`. -/
def kapQN : ℝ := kapN q.s q.c0 q.rho q.γ q.F mu

/-- **The native private operation for computed nodes**: the node and address programs, the
compute circuit `computeV4` with every call reading the data address, the orientation wire and
the decoder with scale `kapQN` and step factor `ρ_L`. -/
def ndQN : NativeOp (TSel q.params.m q.params.l q.params.m) (Fin q.params.a ⊕ Fin q.kx)
    (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (Fin nd ⊕ PY q.kx q.b) Query :=
  odeOpN q.kx (layQN q mu) q.m mu nd hnd N (kapQN q mu) (rhoL (gridP q.params) q.F)

/-- **The arithmetic** of the native private operation, with CORDIC accuracy `ζ/2`. -/
def arQN (Zn : Type) : Arith (NB (TSel q.params.m q.params.l q.params.m)
    (Fin q.params.a ⊕ Fin q.kx) (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b)) :=
  odeArN q.kx (layQN q mu) q.m mu Zn (kapQN q mu) (q.ζ / 2)

/-- **One native preparation** of the released protocol with the branch operation for computed
nodes, for the loading circuit `loadC` and the weight-preparation circuit `wpC`. -/
def prepQN {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin nd ⊕ PY q.kx q.b) Query)) :
    List (NInstr (TNW q.params (Fin q.kx) Zs (ZaN q.m mu Zn ⊕ SZ4 q.kx q.b) (arQN q mu Zn).bT
      (arQN q mu Zn).bP (arQN q mu Zn).A) (Fin nd ⊕ PY q.kx q.b) Query) :=
  tnprepC q.params q.UJg (ndQN q mu nd hnd N) (arQN q mu Zn) loadC wpC

omit [Fintype Zn] [DecidableEq Zn] in
theorem layQN_ok (hq : q.OK) : (layQN q mu).OK :=
  layN_ok q.params mu q.b q.F hq.b_pos hq.g_ge hq.ε_pos (q.ε_le_one hq) (q.TD_nonneg hq)

theorem kapQN_pos (hq : q.OK) : 0 < kapQN q mu :=
  kapN_pos q.s q.c0 q.rho q.γ q.F mu (Nat.two_pow_pos _) hq.c0_pos (q.rho_pos hq) hq.γ_pos

omit [Fintype Zn] in
/-- The native private operation is public. -/
theorem ndQN_public (hN : N.OK) : (ndQN q mu nd hnd N).Public := odeOpN_public _ _ _ _ _ _ _ hN _ _

omit [Fintype Zn] in
/-- **The arithmetic hypothesis** with accuracy `ζ`. -/
theorem arQN_ok (hq : q.OK) :
    ArithOK (arQN q mu Zn) (Sum.inl (Sum.inr (ndQN q mu nd hnd N).o)) (ndQN q mu nd hnd N).dec
      q.ζ := by
  have hr : |rhoL (gridP q.params) q.F - 1| ≤ q.ζ / 4 :=
    rhoLT_close q.params q.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos (q.ε_le_one hq) (q.TD_nonneg hq)
  have h1 := hq.ζ_pos
  have h2 := hq.ζ_le
  exact odeArN_ok q.kx (layQN q mu) q.m mu nd hnd N (layQN_ok q mu hq) (kapQN q mu)
    (rhoL (gridP q.params) q.F) (q.ζ / 2) q.ζ (kapQN_pos q mu hq) (by linarith) (by linarith)
    (by linarith) (by linarith)

omit [Fintype Zn] [DecidableEq Zn] in
/-- **The gates of the compute circuit**: the node program, the address program and `28 k + 2`
gates. -/
theorem ndQN_nGates :
    nGatesN (ndQN q mu nd hnd N).V =
      N.gates.length + (addrGT q.m q.params.l mu).length + (28 * q.kx + 2) :=
  odeOpN_nGates _ _ _ _ _ _ _ _ _

omit [Fintype Zn] [DecidableEq Zn] in
/-- The compute circuit makes two calls of each oracle. -/
theorem ndQN_nCalls (c : Query → Bool) :
    nCallsN c (ndQN q mu nd hnd N).V = 2 * (if c Query.rowLocation then 1 else 0) +
      2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0) :=
  odeOpN_nCalls _ _ _ _ _ _ _ _ _ c

/-- The number of address-register wires for computed nodes. -/
theorem card_ZAN (m mu : ℕ) :
    Fintype.card (ZAN m mu) = 1 + 2 * (mu + m + 14) + (4 * m + 62) * (mu + m + 14) := by
  show Fintype.card (CW (RO (aLayN m mu)) (aLayN m mu).w) = _
  rw [card_CW, card_RO, aLayN_w]
  simp only [aLayN, Lay.mA, Lay.mS]
  ring

omit [DecidableEq Zn] in
/-- The number of computed scratch wires: the node register, the node scratch and the address
registers. -/
theorem card_ZaN (m mu : ℕ) :
    Fintype.card (ZaN m mu Zn) =
      mu + Fintype.card Zn + (1 + 2 * (mu + m + 14) + (4 * m + 62) * (mu + m + 14)) := by
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, card_ZAN]

omit [Fintype Zn] in
/-- **The counts of the arithmetic**: those of the released `GateBinaryODE.odeArith_counts` for
the layout `layQN` (width `b + μ + F + l + 14`), the decoder scale `kapQN` and the CORDIC
accuracy `ζ/2`. -/
theorem arQN_counts :
    (arQN q mu Zn).circ.length ≤
      26 * (layQN q mu).w * (31 + ((layQN q mu).F + 2) + 3 + ((layQN q mu).mA + 1) +
          2 * ((layQN q mu).mS + 1)) +
        (156 * (Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).w *
            ((Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).n + 1) +
          (Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).bP +
          2 * (Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).bT) ∧
    (arQN q mu Zn).A =
      (1 + 2 * (layQN q mu).w + (31 + ((layQN q mu).F + 2) + 3 + ((layQN q mu).mA + 1) +
          2 * ((layQN q mu).mS + 1)) * (layQN q mu).w) +
        (1 + 2 * (Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).w +
          (6 * ((Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).n + 1) + 1) *
            (Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).w) ∧
    (arQN q mu Zn).bT = (Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).bT ∧
    (arQN q mu Zn).bP = (Cordic.params (layQN q mu).w (kapQN q mu) (q.ζ / 2)).bP :=
  odeArith_counts (inpBBN q.kx (layQN q mu) q.m mu Zn) (kapQN q mu) (q.ζ / 2)

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The native identity** of the private operation for computed nodes, for the time-indexed
binary data on the grid of `2^nd` points. -/
theorem nativeOKQN (hq : q.OK) (hN : N.OK) (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z) (x : X) :
    NativeOK (primsT (R := ℂ) (m := nd) D en x) (ndQN q mu nd hnd N)
      (selOp (tlabFam (P := Reg (Fin q.kx) ℂ)
        (privFamN q.params mu nd hnd N D en x q.rho q.γ) false)) := by
  obtain ⟨k0, hk0⟩ : ∃ m, D.slot m = zIdx en := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  exact nativeOK_N q.params mu nd hnd N hN D en k0 hk0 x q.c0 hq.c0_pos.ne' hdec q.rho q.γ
    (q.rho_pos hq).ne' q.F (hRoundT_ne q.params q.ζ hq.ζ_pos hq.ζ_le hq.g_ge hq.ε_pos
      (q.ε_le_one hq) (q.TD_nonneg hq))

end Data

/-! ### The selection conditions and the integrated certificate -/

section Select

variable (q : PubT) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) {Zn : Type} (N : NodeProg q.m mu Zn)
variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The selection conditions for computed nodes**: `U_J` and the private operations are
unitary, the lifted branch samples are self-adjoint with `‖H‖ ≤ λ_H`, `‖L‖ ≤ λ_D` and `L ≥ 0`,
and the clock promises hold at every label and slot, from the energy bounds and the accretivity
of the samples at the data grid points `addrFN s r` that the branches read. -/
theorem selectN (hq : q.OK) (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrFN nd hnd N s r hr)) :
    IsUnitary (UJop (R := ℂ) q.UJg) ∧
    (∀ z : Label q.params.m q.params.l, ∀ r < q.params.M,
      IsUnitary (privFamN q.params mu nd hnd N D en x q.rho q.γ z r)) ∧
    (∀ z : Label q.params.m q.params.l, ∀ r < q.params.M,
      GateODE.ClockPromise (P := Reg (Fin q.kx) ℂ) (a := q.params.a) (UJop (R := ℂ) q.UJg)
      (privFamN q.params mu nd hnd N D en x q.rho q.γ z r)
      (GateSelect.ODE.branchHB q.params (vN q.params mu N) (HbN q.params mu nd hnd N D en x)
        (LbN q.params mu nd hnd N D en x) z r) q.params.Q q.params.qbar) ∧
    (∀ s, ∀ r < q.params.M, star (HbN q.params mu nd hnd N D en x s r) =
      HbN q.params mu nd hnd N D en x s r) ∧
    (∀ s, ∀ r < q.params.M, star (LbN q.params mu nd hnd N D en x s r) =
      LbN q.params mu nd hnd N D en x s r) ∧
    (∀ s, ∀ r < q.params.M, ‖HbN q.params mu nd hnd N D en x s r‖ ≤ q.params.lamH) ∧
    (∀ s, ∀ r < q.params.M, ‖LbN q.params mu nd hnd N D en x s r‖ ≤ q.params.lamD) ∧
    (∀ s, ∀ r < q.params.M, ∀ w : Reg (Fin q.kx) ℂ,
      0 ≤ (inner ℂ w (LbN q.params mu nd hnd N D en x s r w)).re) := by
  refine ⟨UJop_isUnitary _ (hadUJ4_ok q.σ q.hσ),
    fun z r _ => privFamN_isUnitary _ _ _ _ _ _ _ _ _ _ z r,
    fun z r hr => clockN q.params mu nd hnd N D en q.σ q.hσ rfl hrange x q.etaH q.etaD q.rho q.γ
      hq.etaH_nonneg hq.etaD_nonneg rfl (q.rho_pos hq) hq.γ_pos hq.T_pos hq.g_ge hq.ε_pos
      (q.ε_le_one hq) (q.TD_nonneg hq) q.tau_eq z r hr (hS z.1 r hr), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun s r _ => HbN_self q.params mu nd hnd N D en x s r
  · exact fun s r _ => LbN_self q.params mu nd hnd N D en x s r
  · intro s r hr
    rw [HbN_of_lt q.params mu nd hnd N D en x s r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, addrFN nd hnd N s r hr) _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) q.etaH
      hq.etaH_nonneg (hS s r hr).rowH (hS s r hr).colH).trans
      (q.sqrt_le_lam hq q.etaH hq.etaH_nonneg))
  · intro s r hr
    rw [LbN_of_lt q.params mu nd hnd N D en x s r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, addrFN nd hnd N s r hr) _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) q.etaD
      hq.etaD_nonneg (hS s r hr).rowD (hS s r hr).colD).trans
      (q.sqrt_le_lam hq q.etaD hq.etaD_nonneg))
  · intro s r hr w
    rw [LbN_of_lt q.params mu nd hnd N D en x s r hr]
    exact re_inner_qlift_nonneg en _ (hS s r hr).psd w

/-- **The integrated represented-sample error of a branch for computed nodes**: the errors of
the lifted samples `M̂(addrFN s r)` at the rounded data grid points against the generator path
at the exact branch addresses `addrNN s r · T/2^(μ+m)`, weighted by the slot length
`(2^μ - ν'_s) T/2^(μ+m)`. The time-address rounding to the data grid is part of this error. -/
def sampleErrNQ (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (x : X) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (s : Bool × (Fin q.m → Bool)) :
    ℝ :=
  ((2 ^ mu - startWN N s : ℕ) : ℝ) * q.T / 2 ^ (mu + q.m) *
    ∑ r : Fin (2 ^ q.m), ‖G (addrNN N s r * q.T / 2 ^ (mu + q.m)) -
      mLift D en (x, addrFN nd hnd N s r r.isLt)‖

/-- The integrated error at the grid points is the integrated error `sampleErrB` of the branch. -/
theorem sampleErrB_NQ (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (s : Bool × (Fin q.m → Bool)) :
    sampleErrB q.params (vN q.params mu N) (HbN q.params mu nd hnd N D en x)
      (LbN q.params mu nd hnd N D en x) G s = sampleErrNQ q mu nd hnd N D en x G s := by
  unfold sampleErrB sampleErrNQ
  have hsum : ∑ r ∈ Finset.range q.params.M,
      ‖G (GateSelect.ODE.addrB q.params (vN q.params mu N) s r) -
        GateODE.Time.gens (HbN q.params mu nd hnd N D en x s)
          (LbN q.params mu nd hnd N D en x s) r‖ =
      ∑ r : Fin (2 ^ q.m), ‖G (addrNN N s r * q.T / 2 ^ (mu + q.m)) -
        mLift D en (x, addrFN nd hnd N s r r.isLt)‖ := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    rw [addrB_vN, gensN_eq q.params mu nd hnd N D en x s r r.isLt]
    rfl
  rw [hsum, durB_vN]
  congr 1
  have hM : ((q.params.M : ℕ) : ℝ) = 2 ^ q.m := by push_cast; rfl
  rw [hM, pow_add]
  have h2 : (2 : ℝ) ^ q.m ≠ 0 := by positivity
  have h3 : (2 : ℝ) ^ mu ≠ 0 := by positivity
  field_simp
  rfl

end Select

/-! ### The instance conditions -/

section Instance

variable (q : PubT) (mu nd : ℕ) (hnd : nd ≤ mu + q.m) {Zn : Type} (N : NodeProg q.m mu Zn)
variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The remaining instance conditions for computed nodes**: a positive source quadrature with
the computed nodes `vN` and weights `w_u ≥ 0`, forcing vectors `f_u`; the loading `Jl` is unitary
and places the normalised initial state and forcing vectors, the weight preparation `Wp` is
unitary with the amplitudes `√(‖z_s‖/B)` in its zero column; `xs` solves `x' = -G(u) x + b(u)`
on `[0, T]` for an accretive `βG`-Lipschitz path `G` whose represented samples satisfy the
integrated certificate `sampleErrNQ s ≤ δI` of every branch; the branch solutions `ys` of the
homogeneous equation from the computed starts with the source vectors `w_u f_u` give the source
certificate `κ`; `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and `κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`. -/
structure RestN (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (x : X) (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ : ℝ) : Prop where
  weights : ∀ u < q.params.M, 0 ≤ wq u
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) =
      ((q.params.srcAmp (xs 0) (bsW q.params wq fv) (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : xs 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.kx)) = unitDirection (xs 0)
  forcing_load : ∀ w : Fin q.m → Bool, wq (wordValue w) ≠ 0 → fv (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.kx)) = unitDirection (fv (wordValue w))
  solves : SolvesODE G bf xs 0 q.T
  accretive : ∀ u ∈ Icc 0 q.T, Accretive (G u)
  lipG : ∀ u ∈ Icc 0 q.T, ∀ u' ∈ Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleI : ∀ s, sampleErrNQ q mu nd hnd N D en x G s ≤ δI
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s) (startB q.params (vN q.params mu N) s) q.T
  branch_init : ∀ s, ys s (startB q.params (vN q.params mu N) s) =
    q.params.zsrc (xs 0) (bsW q.params wq fv) s
  quad : ‖xs q.T - ∑ s, ys s q.T‖ ≤ κ
  target_ne : xs q.T ≠ 0
  budget : q.params.mass (xs 0) (bsW q.params wq fv) ≤ q.g * ‖xs q.T‖
  disc : κ + (βG * q.T ^ 2 / q.params.M + δI) * q.params.mass (xs 0) (bsW q.params wq fv) ≤
    q.ε * q.params.mass (xs 0) (bsW q.params wq fv) / (2000 * q.g)

/-- **The integrated instance conditions for computed nodes from binary data**: the selection
conditions from the samples the branches read (`selectN`) and `RestN`. -/
theorem instanceN (hq : q.OK) (D : Data (X × Fin (2 ^ nd)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrFN nd hnd N s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ : ℝ) (hR : RestN q mu nd hnd N D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    BInstanceOKI q.params (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamN q.params mu nd hnd N D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (vN q.params mu N) wq fv (HbN q.params mu nd hnd N D en x)
      (LbN q.params mu nd hnd N D en x) G bf xs ys βG δI κ := by
  obtain ⟨huj, hpriv, hclock, hsH, hsL, hnH, hnL, hpsd⟩ :=
    selectN q mu nd hnd N hq D en hrange x hS
  exact
    { uj := huj
      priv := hpriv
      clock := hclock
      selfH := hsH
      selfL := hsL
      normH := hnH
      normL := hnL
      psd := hpsd
      nodes := vN_mem q.params hq.T_pos.le mu N
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
      sampleI := fun s => (sampleErrB_NQ q mu nd hnd N D en x G s).symm ▸ hR.sampleI s
      branch_sol := hR.branch_sol
      branch_init := hR.branch_init
      quad := hR.quad
      target_ne := hR.target_ne
      budget := hR.budget
      disc := hR.disc }

end Instance

end

end SparseHamiltonian.GateBinaryNodes
