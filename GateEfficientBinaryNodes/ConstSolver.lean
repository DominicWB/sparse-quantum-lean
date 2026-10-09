import GateEfficientBinaryNodes.Const
import GateEfficientBinaryODETime.Solver

/-!
# The binary-data solvers with constant forcing

Equation `ode:eq:gate-constant-source`, for the time-dependent solvers from binary data: the
weight preparation `wpConst` (one rotation and `m` controlled Hadamard gates) and the loading
`loadConst srcC` (the two supplied controlled loading circuits, the same on every forcing
label) of `Const` are the source circuits of

* the released common-mesh solver `GateBinaryODETime.binary_ode_time_solver`
  (`binary_ode_time_const_counts`, `binary_ode_time_solver_const`, and over a finite gate set
  `binary_ode_time_solver_const_synth`), and
* the solver on branch-dependent meshes with the left-endpoint quadrature and the integrated
  sample-error certificate (`SelectIntegrated.binary_select_solverLI`):
  `binary_select_const_counts`, `binary_select_solverLI_const`, and over a finite gate set
  `binary_select_solverLI_const_synth`, `binary_select_solverLI_const_trials`,

for constant forcing `b(u) = b`, an initial state with `‖x₀‖ = r₀`, `‖b‖ = r_b` and
`B = r₀ + T r_b > 0`. The source gates are `G_src = |srcC false| + |srcC true| + 2 (m + 1)`
(`m + 1` the gates of the weight preparation, counted twice as in the released count
`|loadC| + 2 |wpC|`), and the supplied circuits enter with their accuracies `ζ₀`, `ζ₁` through
`ζs = ζ₀ + ζ₁` in the released budget `24 d ζ + 3 ζs ≤ ν`. With `2^m` nodes the left-endpoint
source certificate is `Λ r_b T²/2^(m+1)` (the forcing is constant, so `L = 0` and `δb = 0`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT binary_ode_time_counts binary_ode_time_solver
  binary_ode_time_gate_count)
open SparseHamiltonian.GateBinarySelect (addrF prepQ ndQ arQ apG binary_select_counts
  binary_select_gate_count ZA)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams TOracles)
open SparseHamiltonian.GateSelect.ODE (startB bsW)
open SparseHamiltonian.GateQuad (vQ wQ quadMass)
open SparseHamiltonian.GateSynthTrials (synthPrep)
open SparseHamiltonian.GatePointerEncoding (wordValue)
open TimeDependentODE (SolvesODE Accretive)
open ODEStateNormalization (unitDirection)
open NativeSparseBlockEncoding (Data Query)
open Set (Icc)
open scoped InnerProduct BigOperators

/-! ### The common-mesh solver -/

section Common

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **The remaining conditions with constant forcing on the common mesh**: the initial state has
norm `r₀`, the forcing vector `b` norm `r_b`, `B = r₀ + T r_b > 0`; the supplied loadings are
unitary and place the directions of `x(0)` and `b`; `x` solves `x' = -G(u) x + b` on `[0, T]` for
an accretive `βG`-Lipschitz path `G` within `δG` of the lifted samples at the slot times (as in
`GateBinaryODETime.PubT.Rest`), `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and the released discretisation
budget with `βb = δb = 0` and `b_max = r_b` holds. -/
structure RestConst (q : PubT) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X) (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bv : Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (βG δG r0 rb : ℝ) : Prop where
  norm_init : ‖xs 0‖ = r0
  norm_forcing : ‖bv‖ = rb
  load_unitary : ∀ c, IsUnitary (Jsrc c)
  init_load : xs 0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection (xs 0)
  forcing_load : bv ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection bv
  solves : SolvesODE G (fun _ => bv) xs 0 q.T
  accretive : ∀ u ∈ Icc 0 q.T, Accretive (G u)
  lipG : ∀ u ∈ Icc 0 q.T, ∀ u' ∈ Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  sampleG : ∀ (r : ℕ) (hr : r < 2 ^ q.m),
    ‖G (r * q.T / ((2 ^ q.m : ℕ) : ℝ)) - mLift D en (x, ⟨r, hr⟩)‖ ≤ δG
  βG_nonneg : 0 ≤ βG
  target_ne : xs q.T ≠ 0
  budget : srcB r0 rb q.T ≤ q.g * ‖xs q.T‖
  disc : q.params.discretisation βG δG 0 0 rb r0 ≤ q.ε * srcB r0 rb q.T / (2000 * q.g)

/-- **The counts of the common-mesh solver with constant forcing** (equation
`ode:eq:gate-constant-source` in the count of the released solver): for the supplied valid
controlled loading circuits `srcC` and the public norms `r₀, r_b ≥ 0` with `B > 0`, the native
preparation `q.prep (loadConst srcC) wpConst` has valid trials, at most
`prepGates + 84 d (σ+3) + 6 d G_C + (|srcC false| + |srcC true| + 2 (m+1))` elementary gates,
at most `24 d` calls of each coherent sampled-time oracle besides the calls of the two supplied
circuits, and in every history the protocol uses at most
`18000 g [(d+1)(a + m + r + 1 + C_J + G_C) + (J+2)(l+1) + G_src + A]` elementary gates with
`G_src = |srcC false| + |srcC true| + 2 (m+1)` (the other terms as in
`GateBinaryODETime.binary_ode_time_gate_count`). -/
theorem binary_ode_time_const_counts (q : PubT) (hq : q.OK)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (r0 rb : ℝ) (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb)
    (hB : 0 < srcB r0 rb q.T) :
    (∀ j, ∀ i ∈ trialN (q.prep (loadConst q.params.m srcC)
      (wpConst q.params.m Zs (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T)) j, i.Valid) ∧
    nGatesN (q.prep (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T)) ≤
      q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
        6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
          (2 * q.ar.bP + q.ar.bT + 1)) +
        (nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (q.prep (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T)) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        (nCallsN c (srcC false) + nCallsN c (srcC true))) ∧
    ((nprotocol (q.prep (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      18000 * q.g * (((q.params.d : ℝ) + 1) * (((q.kx + 3 : ℕ) : ℝ) + q.params.m +
          q.params.r + 1 + ((q.σ + 3 : ℕ) : ℝ) + ((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
            (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ)) +
        ((q.params.J : ℝ) + 2) * ((q.params.l : ℝ) + 1) +
        ((nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1) : ℕ) : ℝ) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) := by
  have hloadV := loadConst_valid q.params.m srcC hsrcV
  have hwpV := wpConst_valid (Zs := Zs) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) q.params.m r0 rb
    q.T hr0 (mul_nonneg hq.T_pos.le hrb) hB
  obtain ⟨hV, hG, hC, -, -, -⟩ := binary_ode_time_counts q hq _ hloadV _ hwpV
  have hW := binary_ode_time_gate_count q hq _ hloadV _ hwpV
  have hsum := fun c => const_source_counts (Zs := Zs) q.params.m srcC r0 rb q.T c
  have hs : nGatesN (loadConst q.params.m srcC) + 2 * nGatesN (wpConst q.params.m Zs
      (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T) =
      nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1) := (hsum (fun _ => true)).1
  refine ⟨hV, ?_, ?_, ?_⟩
  · omega
  · intro c
    have h := (hsum c).2
    have := hC c
    omega
  · have h' : ((nGatesN (loadConst q.params.m srcC) : ℝ) + 2 * nGatesN (wpConst q.params.m Zs
        (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T)) =
        ((nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1) : ℕ) : ℝ) := by
      rw [← hs]
      push_cast
      ring
    rw [h'] at hW
    exact hW

/-- **The common-mesh solver from binary data with constant forcing** (Theorem `ode:thm:gates`,
time-dependent generator, with the source preparation of equation
`ode:eq:gate-constant-source`). For the public data `q`, the time-indexed binary data of
`GateBinaryODETime.binary_ode_time_solver` and the supplied valid controlled loading circuits
`srcC`, the protocol `nprotocol (q.prep (loadConst srcC) wpConst) (2g)` (counts in
`binary_ode_time_const_counts`) has the guarantees `NOutcome` for every input `x` whose samples
satisfy the energy bounds and are accretive, every pair of loadings `J₀`, `J₁` approximated by
`srcC false`, `srcC true` within `ζ₀`, `ζ₁` (controlled by the sector, `GateNative.srcIdeal`)
with `24 d ζ + 3 (ζ₀ + ζ₁) ≤ ν`, and every generator path, constant forcing `b` and solution
satisfying `RestConst`. -/
theorem binary_ode_time_solver_const (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (r0 rb : ℝ) (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb)
    (hB : 0 < srcB r0 rb q.T) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re)
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bv : Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (βG δG ζ₀ ζ₁ : ℝ) (hζ₀ : 0 ≤ ζ₀) (hζ₁ : 0 ≤ ζ₁)
    (h₀ : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) (srcC false))
      (liftB (X := Zs) (srcIdeal false (Jsrc false))) ζ₀)
    (h₁ : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) (srcC true))
      (liftB (X := Zs) (srcIdeal true (Jsrc true))) ζ₁)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * (ζ₀ + ζ₁) ≤ q.params.nu)
    (hR : RestConst q D en x Jsrc G bv xs βG δG r0 rb) :
    NOutcome (q.prep (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T)) q.params.ratio q.ε
      (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  have hT := hq.T_pos
  have hloadV := loadConst_valid q.params.m srcC hsrcV
  have hwpV := wpConst_valid (Zs := Zs) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) q.params.m r0 rb
    q.T hr0 (mul_nonneg hT.le hrb) hB
  obtain ⟨-, -, -, -, -, -, hout⟩ :=
    binary_ode_time_solver q hq D en hrange hdec _ hloadV _ hwpV
  have hζs : 0 ≤ ζ₀ + ζ₁ := add_nonneg hζ₀ hζ₁
  have hload := loadConst_approx q.params.m (primsT (R := ℂ) D en x) (primsT_isUnitary D en x)
    srcC hsrcV Jsrc hR.load_unitary ζ₀ ζ₁ hζ₀ hζ₁ h₀ h₁
  have hwp := wpConst_approx (Zs := Zs) q.params.m r0 rb q.T (primsT (R := ℂ) D en x) hζs
  have hbs : ∀ r < q.params.M, (fun _ : ℕ => bv) r = bv := fun _ _ => rfl
  have hmass : q.params.mass (xs 0) (fun _ => bv) = srcB r0 rb q.T := by
    rw [mass_const q.params hT.le (xs 0) (fun _ => bv) bv hbs, hR.norm_init, hR.norm_forcing]
    rfl
  have hWu := WpConst_unitary q.params.m r0 rb q.T hr0 (mul_nonneg hT.le hrb) hB
  refine hout x hrH hcH hrD hcD hPSD (JlC q.params.m Jsrc) (WpConst q.params.m r0 rb q.T) G
    (fun _ => bv) xs (fun _ => bv) βG δG 0 0 rb (ζ₀ + ζ₁) hζs hload hwp hbud ?_
  exact
    { load_unitary := fun c => hR.load_unitary c.1
      prep_left := hWu.1
      prep_right := hWu.2
      prep := fun w => by
        rw [← hR.norm_init, ← hR.norm_forcing]
        exact WpConst_srcAmp q.params hT.le (xs 0) (fun _ => bv) bv hbs w
      init_load := hR.init_load
      forcing_load := fun _ hb => hR.forcing_load hb
      solves := hR.solves
      accretive := hR.accretive
      lipG := hR.lipG
      sampleG := hR.sampleG
      lipb := fun _ _ _ _ => by simp
      sampleb := fun _ _ => by simp
      boundb := fun _ _ => le_of_eq hR.norm_forcing
      βG_nonneg := hR.βG_nonneg
      βb_nonneg := le_rfl
      target_ne := hR.target_ne
      budget := by
        rw [hmass]
        exact hR.budget
      disc := by
        rw [hmass, hR.norm_init]
        exact hR.disc }

/-- **The common-mesh solver with constant forcing over a finite gate set**: the guarantee
`GateSynth.SOutcome` of the synthesised protocol
`sprotocol hS (ε/200) (q.prep (loadConst srcC) wpConst) (2g)` of
`GateBinaryODETime.binary_ode_time_solver_synth` under the hypotheses of
`binary_ode_time_solver_const`; its validity, gate-set membership and counts are those of
`binary_ode_time_solver_synth` for these source circuits. -/
theorem binary_ode_time_solver_const_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (r0 rb : ℝ) (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb)
    (hB : 0 < srcB r0 rb q.T) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hPSD : ∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re)
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bv : Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (βG δG ζ₀ ζ₁ : ℝ) (hζ₀ : 0 ≤ ζ₀) (hζ₁ : 0 ≤ ζ₁)
    (h₀ : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) (srcC false))
      (liftB (X := Zs) (srcIdeal false (Jsrc false))) ζ₀)
    (h₁ : ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) (srcC true))
      (liftB (X := Zs) (srcIdeal true (Jsrc true))) ζ₁)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * (ζ₀ + ζ₁) ≤ q.params.nu)
    (hR : RestConst q D en x Jsrc G bv xs βG δG r0 rb) :
    GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (q.prep (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin q.m ⊕ PY q.kx q.b) Query r0 rb q.T)) q.params.ratio
      (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, -⟩ := binary_ode_time_const_counts q hq srcC hsrcV r0 rb hr0 hrb hB
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  exact GateSynth.soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
    (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (primsT_isUnitary D en x) _ hR.target_ne
    (binary_ode_time_solver_const q hq D en hrange hdec srcC hsrcV r0 rb hr0 hrb hB x hrH hcH hrD
      hcD hPSD Jsrc G bv xs βG δG ζ₀ ζ₁ hζ₀ hζ₁ h₀ h₁ hbud hR)

end Common

/-! ### The solver on branch-dependent meshes -/

section Select

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- The forcing samples with the left-endpoint weights are the forcing vector on every node. -/
theorem bsW_wQ_const (p : TParams) (hT : 0 < p.T) {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] (bv : P) : ∀ q < p.M, bsW p (wQ p p.M) (fun _ => bv) q = bv := by
  intro q hq
  unfold bsW wQ
  rw [if_pos hq]
  have hM : ((p.M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
  have e : (p.M : ℝ) / p.T * (p.T / p.M) = 1 := by field_simp
  rw [e, Complex.ofReal_one, one_smul]

/-- **The remaining conditions with constant forcing on branch-dependent meshes** (left-endpoint
quadrature, integrated certificate): the norms `r₀`, `r_b`, `B = r₀ + T r_b > 0`, the supplied
loadings, the solution of `x' = -G(u) x + b` with an accretive `βG`-Lipschitz path `G` with
`‖G(u)‖ ≤ Λ`, the integrated sample errors `sampleErrQ s ≤ δI` of every branch, the branch
solutions from the source vectors of constant forcing, `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and the budget
`Λ r_b T²/2^(m+1) + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`. -/
structure RestLIConst (q : PubT) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X) (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bv : Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ r0 rb : ℝ) : Prop where
  norm_init : ‖xs 0‖ = r0
  norm_forcing : ‖bv‖ = rb
  load_unitary : ∀ c, IsUnitary (Jsrc c)
  init_load : xs 0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection (xs 0)
  forcing_load : bv ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection bv
  solves : SolvesODE G (fun _ => bv) xs 0 q.T
  accretive : ∀ u ∈ Icc 0 q.T, Accretive (G u)
  lipG : ∀ u ∈ Icc 0 q.T, ∀ u' ∈ Icc 0 q.T, ‖G u - G u'‖ ≤ βG * |u - u'|
  βG_nonneg : 0 ≤ βG
  sampleI : ∀ s, sampleErrQ q D en x G s ≤ δI
  normG : ∀ u ∈ Icc 0 q.T, ‖G u‖ ≤ Λ
  branch_sol : ∀ s, SolvesODE G (fun _ => 0) (ys s)
    (startB q.params (vQ q.params q.params.M) s) q.T
  branch_init : ∀ s, ys s (startB q.params (vQ q.params q.params.M) s) =
    q.params.zsrc (xs 0) (fun _ => bv) s
  target_ne : xs q.T ≠ 0
  budget : srcB r0 rb q.T ≤ q.g * ‖xs q.T‖
  disc : Λ * rb * q.T ^ 2 / (2 * q.params.M) +
      (βG * q.T ^ 2 / q.params.M + δI) * srcB r0 rb q.T ≤ q.ε * srcB r0 rb q.T / (2000 * q.g)

/-- **The counts of the solver on branch-dependent meshes with constant forcing**: those of
`GateBinarySelect.binary_select_counts` and `binary_select_gate_count` for the source circuits
`loadConst srcC` and `wpConst`, with `G_src = |srcC false| + |srcC true| + 2 (m+1)` elementary
gates and the calls of the two supplied circuits. -/
theorem binary_select_const_counts (q : PubT) (hq : q.OK)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (r0 rb : ℝ) (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb)
    (hB : 0 < srcB r0 rb q.T) :
    (∀ j, ∀ i ∈ trialN (prepQ q (loadConst q.params.m srcC)
      (wpConst q.params.m Zs (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T)) j, i.Valid) ∧
    nGatesN (prepQ q (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T)) ≤
      q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
        6 * q.params.d * (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
          2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) +
        (nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (prepQ q (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T)) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        (nCallsN c (srcC false) + nCallsN c (srcC true))) ∧
    ((nprotocol (prepQ q (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      18000 * q.g * (((q.params.d : ℝ) + 1) * (((q.kx + 3 : ℕ) : ℝ) + q.params.m +
          q.params.r + 1 + ((q.σ + 3 : ℕ) : ℝ) +
          ((2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
            2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1) : ℕ) : ℝ)) +
        ((q.params.J : ℝ) + 2) * ((q.params.l : ℝ) + 1) +
        ((nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1) : ℕ) : ℝ) +
        ((q.kx : ℝ) + Fintype.card Zs +
          (((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) +
            (6 * q.kx + 4 * q.b) : ℕ) : ℝ) + (arQ q).bT + (arQ q).bP + (arQ q).A)) := by
  have hloadV := loadConst_valid q.params.m srcC hsrcV
  have hwpV := wpConst_valid (Zs := Zs) (Y := Fin (2 * q.m) ⊕ PY q.kx q.b) (J := Query) q.params.m
    r0 rb q.T hr0 (mul_nonneg hq.T_pos.le hrb) hB
  obtain ⟨hV, hG, hC, -, -, -⟩ := binary_select_counts q hq _ hloadV _ hwpV
  have hW := binary_select_gate_count q hq _ hloadV _ hwpV
  have hsum := fun c => const_source_counts (Zs := Zs) q.params.m srcC r0 rb q.T c
  have hs : nGatesN (loadConst q.params.m srcC) + 2 * nGatesN (wpConst q.params.m Zs
      (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T) =
      nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1) := (hsum (fun _ => true)).1
  refine ⟨hV, ?_, ?_, ?_⟩
  · omega
  · intro c
    have h := (hsum c).2
    have := hC c
    omega
  · have h' : ((nGatesN (loadConst q.params.m srcC) : ℝ) + 2 * nGatesN (wpConst q.params.m Zs
        (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T)) =
        ((nGatesN (srcC false) + nGatesN (srcC true) + 2 * (q.m + 1) : ℕ) : ℝ) := by
      rw [← hs]
      push_cast
      ring
    rw [h'] at hW
    exact hW

/-- The constant-forcing conditions give the left-endpoint conditions with the integrated
certificate. -/
theorem RestLIConst.toLI (q : PubT) (hq : q.OK)
    {D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s} {en : Cfg (Fin q.kx) ≃ n} {x : X}
    {Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ}
    {G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ} {bv : Reg (Fin q.kx) ℂ}
    {xs : ℝ → Reg (Fin q.kx) ℂ} {ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ}
    {βG δI Λ r0 rb : ℝ} (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb) (hB : 0 < srcB r0 rb q.T)
    (hR : RestLIConst q D en x Jsrc G bv xs ys βG δI Λ r0 rb) :
    RestLI q D en x (JlC q.params.m Jsrc) (WpConst q.params.m r0 rb q.T) (fun _ => bv) G
      (fun _ => bv) xs ys βG δI Λ 0 rb 0 := by
  have hT := hq.T_pos
  have hbs := bsW_wQ_const q.params hT bv
  have hWu := WpConst_unitary q.params.m r0 rb q.T hr0 (mul_nonneg hT.le hrb) hB
  have hzsrc : q.params.zsrc (xs 0) (bsW q.params (wQ q.params q.params.M) (fun _ => bv)) =
      q.params.zsrc (xs 0) (fun _ => bv) := by
    funext s
    rw [zsrc_const q.params (xs 0) _ bv hbs s, zsrc_const q.params (xs 0) _ bv (fun _ _ => rfl) s]
  have hqm : quadMass (xs 0) (fun _ => bv) q.T q.params.M = srcB r0 rb q.T := by
    change quadMass (xs 0) (fun _ => bv) q.params.T q.params.M = srcB r0 rb q.params.T
    rw [← GateQuad.mass_wQ q.params hT le_rfl, mass_const q.params hT.le (xs 0) _ bv hbs,
      hR.norm_init, hR.norm_forcing]
  exact
    { load_unitary := fun c => hR.load_unitary c.1
      prep_left := hWu.1
      prep_right := hWu.2
      prep := fun w => by
        rw [← hR.norm_init, ← hR.norm_forcing]
        exact WpConst_srcAmp q.params hT.le (xs 0) _ bv hbs w
      init_load := hR.init_load
      forcing_load := fun _ hb => hR.forcing_load hb
      solves := hR.solves
      accretive := hR.accretive
      lipG := hR.lipG
      βG_nonneg := hR.βG_nonneg
      sampleI := hR.sampleI
      normG := hR.normG
      lipb := fun _ _ _ _ => by simp
      L_nonneg := le_rfl
      sample_norm := fun _ _ => le_of_eq hR.norm_forcing
      sample_err := fun _ _ => by simp
      branch_sol := hR.branch_sol
      branch_init := fun s => by
        rw [hzsrc]
        exact hR.branch_init s
      target_ne := hR.target_ne
      budget := by
        rw [hqm]
        exact hR.budget
      disc := by
        rw [hqm]
        have e : (Λ * rb + 0) * q.T ^ 2 / (2 * q.params.M) + q.T * 0 =
            Λ * rb * q.T ^ 2 / (2 * q.params.M) := by ring
        rw [e]
        exact hR.disc }

/-- **The solver on branch-dependent meshes from binary data with constant forcing** (Theorem
`ode:thm:gates`, time-dependent generator, branch-dependent meshes of Lemma `ode:lem:gate-select`
with the integrated certificate, left-endpoint quadrature with `2^m` nodes, and the source
preparation of equation `ode:eq:gate-constant-source`). The protocol
`nprotocol (prepQ q (loadConst srcC) wpConst) (2g)` (counts in `binary_select_const_counts`) has
the guarantees `NOutcome` for every input `x` whose samples at the branch addresses satisfy
`SampleOK`, every pair of loadings approximated within `ζ₀`, `ζ₁` with
`24 d ζ + 3 (ζ₀ + ζ₁) ≤ ν`, and every generator path, constant forcing `b`, solution and branch
solutions satisfying `RestLIConst`. -/
theorem binary_select_solverLI_const (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (r0 rb : ℝ) (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb)
    (hB : 0 < srcB r0 rb q.T) (x : X)
    (hS : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bv : Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ ζ₀ ζ₁ : ℝ) (hζ₀ : 0 ≤ ζ₀) (hζ₁ : 0 ≤ ζ₁)
    (h₀ : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) (srcC false))
      (liftB (X := Zs) (srcIdeal false (Jsrc false))) ζ₀)
    (h₁ : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) (srcC true))
      (liftB (X := Zs) (srcIdeal true (Jsrc true))) ζ₁)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * (ζ₀ + ζ₁) ≤ q.params.nu)
    (hR : RestLIConst q D en x Jsrc G bv xs ys βG δI Λ r0 rb) :
    NOutcome (prepQ q (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T)) q.params.ratio q.ε
      (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  have hloadV := loadConst_valid q.params.m srcC hsrcV
  have hwpV := wpConst_valid (Zs := Zs) (Y := Fin (2 * q.m) ⊕ PY q.kx q.b) (J := Query) q.params.m
    r0 rb q.T hr0 (mul_nonneg hq.T_pos.le hrb) hB
  have hζs : 0 ≤ ζ₀ + ζ₁ := add_nonneg hζ₀ hζ₁
  have hload := loadConst_approx q.params.m (primsT (R := ℂ) (m := 2 * q.m) D en x)
    (primsT_isUnitary D en x) srcC hsrcV Jsrc hR.load_unitary ζ₀ ζ₁ hζ₀ hζ₁ h₀ h₁
  have hwp := wpConst_approx (Zs := Zs) q.params.m r0 rb q.T
    (primsT (R := ℂ) (m := 2 * q.m) D en x) hζs
  exact binary_select_solverLI q hq D en hrange hdec _ hloadV _ hwpV x hS (JlC q.params.m Jsrc)
    (WpConst q.params.m r0 rb q.T) (fun _ => bv) G (fun _ => bv) xs ys βG δI Λ 0 rb 0 (ζ₀ + ζ₁)
    hζs hload hwp hbud (hR.toLI q hq hr0 hrb hB)

/-- **The solver on branch-dependent meshes with constant forcing over a finite gate set**: the
guarantee `GateSynth.SOutcome` of the synthesised protocol
`sprotocol hS (ε/200) (prepQ q (loadConst srcC) wpConst) (2g)` under the hypotheses of
`binary_select_solverLI_const`. -/
theorem binary_select_solverLI_const_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (r0 rb : ℝ) (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb)
    (hB : 0 < srcB r0 rb q.T) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bv : Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ ζ₀ ζ₁ : ℝ) (hζ₀ : 0 ≤ ζ₀) (hζ₁ : 0 ≤ ζ₁)
    (h₀ : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) (srcC false))
      (liftB (X := Zs) (srcIdeal false (Jsrc false))) ζ₀)
    (h₁ : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) (srcC true))
      (liftB (X := Zs) (srcIdeal true (Jsrc true))) ζ₁)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * (ζ₀ + ζ₁) ≤ q.params.nu)
    (hR : RestLIConst q D en x Jsrc G bv xs ys βG δI Λ r0 rb) :
    GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (prepQ q (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T)) q.params.ratio
      (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨hV, -⟩ := binary_select_const_counts q hq srcC hsrcV r0 rb hr0 hrb hB
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  exact GateSynth.soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
    (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x)
    (primsT_isUnitary D en x) _ hR.target_ne
    (binary_select_solverLI_const q hq D en hrange hdec srcC hsrcV r0 rb hr0 hrb hB x hSm Jsrc G
      bv xs ys βG δI Λ ζ₀ ζ₁ hζ₀ hζ₁ h₀ h₁ hbud hR)

/-- **The solver on branch-dependent meshes with constant forcing and the synthesised
preparation**: the guarantees `NOutcome` of the protocol
`nprotocol (synthPrep hS (ν/3) (prepQ q (loadConst srcC) wpConst)) (2g)` under the hypotheses of
`binary_select_solverLI_const` (every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a
global phase). -/
theorem binary_select_solverLI_const_trials (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (r0 rb : ℝ) (hr0 : 0 ≤ r0) (hrb : 0 ≤ rb)
    (hB : 0 < srcB r0 rb q.T) (x : X)
    (hSm : ∀ (s : Bool × (Fin q.m → Bool)) (r : ℕ) (hr : r < 2 ^ q.m),
      SampleOK D x q.etaH q.etaD (addrF s r hr))
    (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bv : Reg (Fin q.kx) ℂ)
    (xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
    (βG δI Λ ζ₀ ζ₁ : ℝ) (hζ₀ : 0 ≤ ζ₀) (hζ₁ : 0 ≤ ζ₁)
    (h₀ : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) (srcC false))
      (liftB (X := Zs) (srcIdeal false (Jsrc false))) ζ₀)
    (h₁ : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) (srcC true))
      (liftB (X := Zs) (srcIdeal true (Jsrc true))) ζ₁)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * (ζ₀ + ζ₁) ≤ q.params.nu)
    (hR : RestLIConst q D en x Jsrc G bv xs ys βG δI Λ r0 rb) :
    NOutcome (synthPrep hS (q.params.nu / 3) (prepQ q (loadConst q.params.m srcC)
        (wpConst q.params.m Zs (Fin (2 * q.m) ⊕ PY q.kx q.b) Query r0 rb q.T))) q.params.ratio
      q.ε (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  have hloadV := loadConst_valid q.params.m srcC hsrcV
  have hwpV := wpConst_valid (Zs := Zs) (Y := Fin (2 * q.m) ⊕ PY q.kx q.b) (J := Query) q.params.m
    r0 rb q.T hr0 (mul_nonneg hq.T_pos.le hrb) hB
  have hζs : 0 ≤ ζ₀ + ζ₁ := add_nonneg hζ₀ hζ₁
  have hload := loadConst_approx q.params.m (primsT (R := ℂ) (m := 2 * q.m) D en x)
    (primsT_isUnitary D en x) srcC hsrcV Jsrc hR.load_unitary ζ₀ ζ₁ hζ₀ hζ₁ h₀ h₁
  have hwp := wpConst_approx (Zs := Zs) q.params.m r0 rb q.T
    (primsT (R := ℂ) (m := 2 * q.m) D en x) hζs
  exact binary_select_solverLI_trials hS q hq D en hrange hdec _ hloadV _ hwpV x hSm
    (JlC q.params.m Jsrc) (WpConst q.params.m r0 rb q.T) (fun _ => bv) G (fun _ => bv) xs ys βG
    δI Λ 0 rb 0 (ζ₀ + ζ₁) hζs hload hwp hbud (hR.toLI q hq hr0 hrb hB)

end Select

end

end SparseHamiltonian.GateBinaryNodes
