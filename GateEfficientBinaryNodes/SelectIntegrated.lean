import GateEfficientBinaryNodes.Integrated

/-!
# The binary-data solvers on branch-dependent meshes with the integrated certificate

The released binary-data solvers on branch-dependent meshes
(`GateBinarySelect.binary_select_solver`, `binary_select_solverL` and their finite-gate-set forms)
require the row and column energy
bounds and the accretivity of every sample on the grid of `2^(2m)` points, and a uniform bound
`δG` on the error of every represented sample at the branch addresses. Here the same protocol
`GateBinarySelect.prepQ q loadC wpC` (so the same validity and counts) is shown to have the
guarantees `NOutcome` under weaker conditions on the data:

* the energy bounds and the accretivity only at the samples the branches read, the grid points
  `addrF s r` (`SampleOK`, `selectBA`);
* the integrated sample-error certificate of every branch,
  `sampleErrQ s = ((2^m - u'_s) T/2^(2m)) ∑_{r < 2^m} ‖G(addrN s r · T/2^(2m)) - M̂(addrF s r)‖`
  `≤ δI`
  (the represented-sample error integrated over `[v_s, T]`, `sampleErrB_Q`), with the budget
  `κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)` (`RestBI`, `RestLI`).

* `binary_select_solverI` (positive quadrature on the `2^m` left-endpoint nodes, `RestBI`) and
  `binary_select_solverLI` (left-endpoint weights, `RestLI`): natively;
* `binary_select_solverI_synth`, `binary_select_solverLI_synth`: over a finite gate set
  (`GateSynth.sprotocol`, guarantee `SOutcome`);
* `binary_select_solverI_trials`, `binary_select_solverLI_trials`: with the synthesised
  preparation (`GateSynthTrials.synthPrep`, guarantees `NOutcome`, including the per-trial
  claim).

The protocols, their validity, gate-set membership and counts are those of the released
theorems `binary_select_counts`, `binary_select_solver_synth` and `binary_select_solver_trials`,
which do not depend on the instance. A uniform bound `δG` gives the integrated certificate with
`δI = T δG` and the released budget (`sampleErrQ_le_of_uniform`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open CayleyClockInterface
open SparseHamiltonian.GateBinaryODETime (PubT clock_at)
open SparseHamiltonian.GateBinarySelect (addrF addrN startW startW_lt privFamB
  privFamB_isUnitary HbB LbB HbB_of_lt LbB_of_lt HbB_self LbB_self gensB_eq startB_vQ durB_vQ
  addrB_vQ M_cast prepQ ndQ arQ ndQ_public arQ_ok nativeOKQ binary_select_counts)
open SparseHamiltonian.GateODE (Label ClockPromise)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GateSelect.ODE (startB durB addrB branchHB bsW)
open SparseHamiltonian.GateQuad (vQ wQ quadMass)
open SparseHamiltonian.GateSynthTrials (synthPrep)
open SparseHamiltonian.GatePointerEncoding (wordEquivFin wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open NativeSparseBlockEncoding (Data Query)
open Set (Icc)
open scoped InnerProduct BigOperators

/-! ### The conditions on one sample -/

section Sample

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s N : ℕ}

/-- **The conditions on one sample** of the time-indexed data: the Hamiltonian and dissipative
parts of `D.matrix (x, g)` have row and column energies at most `η_H²` and `η_D²`, and the
dissipative part is accretive. -/
structure SampleOK (D : Data (X × Fin N) n Z s) (x : X) (ηH ηD : ℝ) (g : Fin N) : Prop where
  rowH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηH ^ 2
  colH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηH ^ 2
  rowD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηD ^ 2
  colD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηD ^ 2
  psd : ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
    (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re

/-- The conditions of the released solvers on every sample give the conditions on each one. -/
theorem sampleOK_of_all (D : Data (X × Fin N) n Z s) (x : X) (ηH ηD : ℝ)
    (hrH : ∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηH ^ 2)
    (hcH : ∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηH ^ 2)
    (hrD : ∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηD ^ 2)
    (hcD : ∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ ηD ^ 2)
    (hPSD : ∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re) (g : Fin N) :
    SampleOK D x ηH ηD g :=
  ⟨hrH g, hcH g, hrD g, hcD g, hPSD g⟩

end Sample

/-! ### The selection conditions from the samples at the branch addresses -/

section Select

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

/-- **The clock promise at one label and slot** from the energy bounds of the sample at its
branch address only (the proof of `GateBinarySelect.clockB`). -/
theorem clockBA (p : TParams) (D : Data (X × Fin (2 ^ (2 * p.m))) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (ηH ηD ρ γ : ℝ) (hηH : 0 ≤ ηH) (hηD : 0 ≤ ηD) (hρ : ρ = ηH + p.R * ηD)
    (hρpos : 0 < ρ) (hγ : 0 < γ) (hT : 0 < p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hε1 : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (hτ : p.tau = p.T * (Real.sqrt (4 * (s : ℝ)) * ρ) / γ)
    (z : Label p.m p.l) (r : ℕ) (hr : r < 2 ^ p.m)
    (hS : SampleOK D x ηH ηD (addrF z.1 r hr)) :
    ClockPromise (P := Reg (Fin k) ℂ) (a := k + 3) (UJop (R := ℂ) (hadUJ4 k σ hσ))
      (privFamB p D en x ρ γ z r)
      (branchHB p (vQ p p.M) (HbB p D en x) (LbB p D en x) z r)
      (width (4 * (s : ℝ)) γ) (moment γ) := by
  have hu := startW_lt z.1
  set γ' := γ * (((2 ^ p.m - startW z.1 : ℕ) : ℝ) / 2 ^ p.m) with hγ'
  have hfr0 : 0 ≤ ((2 ^ p.m - startW z.1 : ℕ) : ℝ) / 2 ^ p.m := by positivity
  have hfr1 : ((2 ^ p.m - startW z.1 : ℕ) : ℝ) / 2 ^ p.m ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (2 ^ p.m - startW z.1 : ℕ) ≤ 2 ^ p.m := Nat.sub_le _ _
    exact_mod_cast this
  have h0 : 0 ≤ γ' := mul_nonneg hγ.le hfr0
  have h1 : γ' ≤ γ := mul_le_of_le_one_right hγ.le hfr1
  have hsq : 0 < Real.sqrt (4 * (s : ℝ)) := by
    rw [hs]
    exact Real.sqrt_pos.mpr (by positivity)
  have hsc : durB p (vQ p p.M) z.1 / p.tau = γ' / (ρ * Real.sqrt (4 * (s : ℝ))) := by
    rw [durB_vQ, hτ, hγ', M_cast]
    have h2 : (2 : ℝ) ^ p.m ≠ 0 := by positivity
    field_simp
  have h := clock_at D en σ hσ hs hrange (x, addrF z.1 r hr) (p.nodeW z.2) ηH ηD ρ p.R γ γ'
    hηH hηD hρ hρpos (p.nodeW_abs_le hg hε hε1 hTD z.2) h0 h1 hS.rowH hS.colH hS.rowD hS.colD
  rw [GateBinarySelect.privFamB, dif_pos hr, branchHB, hsc, HbB_of_lt p D en x z.1 r hr,
    LbB_of_lt p D en x z.1 r hr]
  exact h

/-- **The selection conditions from the samples at the branch addresses**: those of
`GateBinarySelect.selectB`, with the energy bounds and the accretivity required only of the
samples `addrF s r` that the branches read. -/
theorem selectBA (q : PubT) (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr)) :
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
    fun z r hr => clockBA q.params D en q.σ q.hσ rfl hrange x q.etaH q.etaD q.rho q.γ
      hq.etaH_nonneg hq.etaD_nonneg rfl (q.rho_pos hq) hq.γ_pos hq.T_pos hq.g_ge hq.ε_pos
      (q.ε_le_one hq) (q.TD_nonneg hq) q.tau_eq z r hr (hS z.1 r hr), ?_, ?_, ?_, ?_, ?_⟩
  · exact fun s r _ => HbB_self q.params D en x s r
  · exact fun s r _ => LbB_self q.params D en x s r
  · intro s r hr
    rw [HbB_of_lt q.params D en x s r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, addrF s r hr) _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) q.etaH
      hq.etaH_nonneg (hS s r hr).rowH (hS s r hr).colH).trans
      (q.sqrt_le_lam hq q.etaH hq.etaH_nonneg))
  · intro s r hr
    rw [LbB_of_lt q.params D en x s r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, addrF s r hr) _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) q.etaD
      hq.etaD_nonneg (hS s r hr).rowD (hS s r hr).colD).trans
      (q.sqrt_le_lam hq q.etaD hq.etaD_nonneg))
  · intro s r hr w
    rw [LbB_of_lt q.params D en x s r hr]
    exact re_inner_qlift_nonneg en _ (hS s r hr).psd w

end Select

/-! ### The integrated certificate at the grid addresses -/

section Cert

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The integrated sample error of a branch at the grid addresses**: the errors of the lifted
grid samples `M̂(addrF s r)` against the generator path at the branch addresses
`addrN s r · T/2^(2m)`, weighted by the slot length `(2^m - u'_s) T/2^(2m)` of the branch. -/
def sampleErrQ (q : PubT) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (s : Bool × (Fin q.m → Bool)) : ℝ :=
  ((2 ^ q.m - startW s : ℕ) : ℝ) * q.T / 2 ^ (2 * q.m) *
    ∑ r : Fin (2 ^ q.m), ‖G (addrN s r * q.T / 2 ^ (2 * q.m)) - mLift D en (x, addrF s r r.isLt)‖

/-- The integrated error at the grid addresses is the integrated error `sampleErrB` of the
branch. -/
theorem sampleErrB_Q (q : PubT) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (s : Bool × (Fin q.m → Bool)) :
    sampleErrB q.params (vQ q.params q.params.M) (HbB q.params D en x) (LbB q.params D en x) G s =
      sampleErrQ q D en x G s := by
  unfold sampleErrB sampleErrQ
  have hsum : ∑ r ∈ Finset.range q.params.M,
      ‖G (addrB q.params (vQ q.params q.params.M) s r) -
        GateODE.Time.gens (HbB q.params D en x s) (LbB q.params D en x s) r‖ =
      ∑ r : Fin (2 ^ q.m), ‖G (addrN s r * q.T / 2 ^ (2 * q.m)) -
        mLift D en (x, addrF s r r.isLt)‖ := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro r _
    rw [addrB_vQ, gensB_eq q.params D en x s r r.isLt]
    rfl
  rw [hsum, durB_vQ]
  congr 1
  have hM : ((q.params.M : ℕ) : ℝ) = 2 ^ q.m := M_cast q.params
  rw [hM, pow_mul']
  have h2 : (2 : ℝ) ^ q.m ≠ 0 := by positivity
  field_simp
  rfl

/-- **The integrated certificate at the grid addresses from a uniform bound**: if every lifted
sample at a branch address is within `δG` of the path, `sampleErrQ s ≤ T δG`. -/
theorem sampleErrQ_le_of_uniform (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (δG : ℝ)
    (h : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      ‖G (addrN s r * q.T / 2 ^ (2 * q.m)) - mLift D en (x, addrF s r hr)‖ ≤ δG)
    (s : Bool × (Fin q.m → Bool)) : sampleErrQ q D en x G s ≤ q.T * δG := by
  rw [← sampleErrB_Q]
  exact sampleErrB_le_of_uniform q.params _ (GateQuad.vQ_mem q.params hq.T_pos.le _)
    hq.T_pos.le _ _ G s δG (GateBinarySelect.sampleG_addr q D en x G δG h s)

end Cert

/-! ### The instance conditions -/

section Instance

variable (q : PubT) {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The remaining instance conditions with the integrated certificate**: those of
`GateBinarySelect.RestB` (positive quadrature with arbitrary weights on the `2^m` left-endpoint
nodes, loading, weight preparation, solution, branch solutions and certificate `κ`), with the
uniform sample bound replaced by the integrated certificate `sampleErrQ s ≤ δI` of every branch
and the budget by `κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`. -/
structure RestBI (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
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
  sampleI : ∀ s, sampleErrQ q D en x G s ≤ δI
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s)
    (startB q.params (vQ q.params q.params.M) s) q.T
  branch_init : ∀ s, ys s (startB q.params (vQ q.params q.params.M) s) =
    q.params.zsrc (xs 0) (bsW q.params wq fv) s
  quad : ‖xs q.T - ∑ s, ys s q.T‖ ≤ κ
  target_ne : xs q.T ≠ 0
  budget : q.params.mass (xs 0) (bsW q.params wq fv) ≤ q.g * ‖xs q.T‖
  disc : κ + (βG * q.T ^ 2 / q.params.M + δI) * q.params.mass (xs 0) (bsW q.params wq fv) ≤
    q.ε * q.params.mass (xs 0) (bsW q.params wq fv) / (2000 * q.g)

/-- **The integrated instance conditions from binary data**: the selection conditions from the
samples at the branch addresses (`selectBA`) and `RestBI`. -/
theorem instanceBI (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ : ℝ) (hR : RestBI q D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    BInstanceOKI q.params (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (vQ q.params q.params.M) wq fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys
      βG δI κ := by
  obtain ⟨huj, hpriv, hclock, hsH, hsL, hnH, hnL, hpsd⟩ := selectBA q hq D en hrange x hS
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
      sampleI := fun s => (sampleErrB_Q q D en x G s).symm ▸ hR.sampleI s
      branch_sol := hR.branch_sol
      branch_init := hR.branch_init
      quad := hR.quad
      target_ne := hR.target_ne
      budget := hR.budget
      disc := hR.disc }

/-- **The remaining instance conditions with the left-endpoint quadrature and the integrated
certificate**: those of `GateBinarySelect.RestL` (the `2^m` nodes `u T/2^m` with the weights
`T/2^m` and the source certificate `(Λ b_s + L) T²/2^(m+1) + T δb` of `GateEfficientQuadrature`),
with the uniform sample bound replaced by `sampleErrQ s ≤ δI` and the budget by
`(Λ b_s + L) T²/2^(m+1) + T δb + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`. -/
structure RestLI (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ L bs δb : ℝ) : Prop where
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) =
      ((q.params.srcAmp (xs 0) (bsW q.params (wQ q.params q.params.M) fv) (w 0, Fin.tail w) :
        ℝ) : ℂ)
  init_load : xs 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.kx)) = unitDirection (xs 0)
  forcing_load : ∀ w : Fin q.m → Bool, fv (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.kx)) = unitDirection (fv (wordValue w))
  solves : SolvesODE G bf xs 0 q.T
  accretive : ∀ u ∈ Icc 0 q.T, Accretive (G u)
  lipG : ∀ u ∈ Icc 0 q.T, ∀ u' ∈ Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleI : ∀ s, sampleErrQ q D en x G s ≤ δI
  normG : ∀ u ∈ Icc 0 q.T, ‖G u‖ ≤ Λ
  lipb : ∀ u ∈ Icc 0 q.T, ∀ u' ∈ Icc 0 q.T, ‖bf u - bf u'‖ ≤ L * |u - u'|
  L_nonneg : 0 ≤ L
  sample_norm : ∀ u < q.params.M, ‖fv u‖ ≤ bs
  sample_err : ∀ u < q.params.M, ‖bf (u * q.T / q.params.M) - fv u‖ ≤ δb
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s)
    (startB q.params (vQ q.params q.params.M) s) q.T
  branch_init : ∀ s, ys s (startB q.params (vQ q.params q.params.M) s) =
    q.params.zsrc (xs 0) (bsW q.params (wQ q.params q.params.M) fv) s
  target_ne : xs q.T ≠ 0
  budget : quadMass (xs 0) fv q.T q.params.M ≤ q.g * ‖xs q.T‖
  disc : (Λ * bs + L) * q.T ^ 2 / (2 * q.params.M) + q.T * δb +
      (βG * q.T ^ 2 / q.params.M + δI) * quadMass (xs 0) fv q.T q.params.M ≤
    q.ε * quadMass (xs 0) fv q.T q.params.M / (2000 * q.g)

/-- **The left-endpoint instance with the integrated certificate from binary data**. -/
theorem instanceLI (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ L bs δb : ℝ) (hR : RestLI q D en x Jl Wp fv G bf xs ys βG δI Λ L bs δb) :
    LInstanceOKI q.params q.params.M (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δI Λ L bs δb := by
  obtain ⟨huj, hpriv, hclock, hsH, hsL, hnH, hnL, hpsd⟩ := selectBA q hq D en hrange x hS
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
      sampleI := fun s => (sampleErrB_Q q D en x G s).symm ▸ hR.sampleI s
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

/-! ### The solvers -/

section Solvers

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **Native gate-efficient dissipative ODE solver from binary data on branch-dependent meshes
with the integrated sample-error certificate** (Theorem `ode:thm:gates`, time-dependent part,
with the integrated represented-sample certificate of Lemma `ode:lem:gate-select`). The protocol
is the released `nprotocol (prepQ q loadC wpC) (2g)` of `GateBinarySelect.binary_select_solver`,
with the validity and counts of `GateBinarySelect.binary_select_counts`. For every input `x`
whose samples at the branch addresses `addrF s r` (only those) satisfy the energy bounds and are
accretive (`SampleOK`), every loading `Jl` and weight preparation `Wp` approximated within `ζs`
by the two circuits with `24 d ζ + 3 ζs ≤ ν`, every positive source quadrature on the `2^m`
left-endpoint nodes and every generator path, forcing, solution, branch solutions and
certificate satisfying `RestBI` (with the integrated sample error `δI`), the protocol has the
guarantees `NOutcome`. -/
theorem binary_select_solverI (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestBI q D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    NOutcome (prepQ q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) :=
  native_time_outcomeBI q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) (ndQ q)
    (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
    (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQ q hq D en hrange hdec x) ζs hζs hload hwp hbud (vQ q.params q.params.M) wq fv
    (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δI κ
    (instanceBI q hq D en hrange x hS Jl Wp wq fv G bf xs ys βG δI κ hR)

/-- **The native solver with the left-endpoint quadrature and the integrated certificate**: the
guarantees of `binary_select_solverI` under `RestLI` (the left-endpoint quadrature with the
weights `T/2^m` and the source certificate of `GateEfficientQuadrature`). -/
theorem binary_select_solverLI (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ L bs δb ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestLI q D en x Jl Wp fv G bf xs ys βG δI Λ L bs δb) :
    NOutcome (prepQ q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
      (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) :=
  native_time_outcomeBI q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) (ndQ q)
    (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
    (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQ q hq D en hrange hdec x) ζs hζs hload hwp hbud (vQ q.params q.params.M)
    (wQ q.params q.params.M) fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δI _
    ((instanceLI q hq D en hrange x hS Jl Wp fv G bf xs ys βG δI Λ L bs δb hR).toBI
      (q.params_ok hq))

/-- **The finite-gate-set solver with the integrated certificate**: the guarantee
`GateSynth.SOutcome` of the synthesised protocol `sprotocol hS (ε/200) (prepQ q loadC wpC) (2g)`
of `GateBinarySelect.binary_select_solver_synth` under the hypotheses of
`binary_select_solverI`. -/
theorem binary_select_solverI_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestBI q D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (prepQ q loadC wpC) q.params.ratio
      (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨hV, -⟩ := binary_select_counts q hq loadC hloadV wpC hwpV
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  exact GateSynth.soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
    (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x)
    (primsT_isUnitary D en x) _ hR.target_ne
    (binary_select_solverI q hq D en hrange hdec loadC hloadV wpC hwpV x hSm Jl Wp wq fv G bf xs
      ys βG δI κ ζs hζs hload hwp hbud hR)

/-- **The finite-gate-set solver with the left-endpoint quadrature and the integrated
certificate**: the guarantee `GateSynth.SOutcome` under the hypotheses of
`binary_select_solverLI`. -/
theorem binary_select_solverLI_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ L bs δb ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestLI q D en x Jl Wp fv G bf xs ys βG δI Λ L bs δb) :
    GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (prepQ q loadC wpC) q.params.ratio
      (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨hV, -⟩ := binary_select_counts q hq loadC hloadV wpC hwpV
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  exact GateSynth.soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
    (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x)
    (primsT_isUnitary D en x) _ hR.target_ne
    (binary_select_solverLI q hq D en hrange hdec loadC hloadV wpC hwpV x hSm Jl Wp fv G bf xs ys
      βG δI Λ L bs δb ζs hζs hload hwp hbud hR)

/-- **The solver with the synthesised preparation and the integrated certificate**: the
guarantees `NOutcome` of the protocol `nprotocol (synthPrep hS (ν/3) (prepQ q loadC wpC)) (2g)`
of `GateBinarySelect.binary_select_solver_trials` (every successful trial within `ε/500` of
`x(T)/‖x(T)‖` up to a global phase, success probability at least `2/3`, trace distance at most
`ε`) under the hypotheses of `binary_select_solverI`. -/
theorem binary_select_solverI_trials (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI κ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestBI q D en x Jl Wp wq fv G bf xs ys βG δI κ) :
    NOutcome (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio q.ε
      (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) :=
  native_time_trials_outcomeBI hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) (ndQ q)
    (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
    (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQ q hq D en hrange hdec x) ζs hζs hload hwp hbud (vQ q.params q.params.M) wq fv
    (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δI κ
    (instanceBI q hq D en hrange x hSm Jl Wp wq fv G bf xs ys βG δI κ hR)

/-- **The solver with the synthesised preparation, the left-endpoint quadrature and the
integrated certificate**: the guarantees `NOutcome` of `binary_select_solverI_trials` under the
hypotheses of `binary_select_solverLI`. -/
theorem binary_select_solverLI_trials (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ L bs δb ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestLI q D en x Jl Wp fv G bf xs ys βG δI Λ L bs δb) :
    NOutcome (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio q.ε
      (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) :=
  native_time_trials_outcomeBI hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) (ndQ q)
    (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
    (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQ q hq D en hrange hdec x) ζs hζs hload hwp hbud (vQ q.params q.params.M)
    (wQ q.params q.params.M) fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δI _
    ((instanceLI q hq D en hrange x hSm Jl Wp fv G bf xs ys βG δI Λ L bs δb hR).toBI
      (q.params_ok hq))

end Solvers

end

end SparseHamiltonian.GateBinaryNodes
