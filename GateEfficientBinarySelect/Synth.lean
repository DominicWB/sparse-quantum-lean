import GateEfficientBinarySelect.Solver
import GateEfficientSynthesis.ODESolver
import GateEfficientSynthesisTrials.Solver

/-!
# Theorem `ode:thm:gates` from binary data on branch-dependent meshes over a finite gate set

The native solver from time-indexed binary sparse data on the branch-dependent meshes
(`binary_select_solver`, `binary_select_solverL`) with every trial, or the preparation,
synthesised over a finite gate set. Two forms, as for the released common-mesh solvers:

* **synthesis of every trial** (`binary_select_solver_synth`): the protocol
  `GateSynth.sprotocol hS (ε/200) prepQ (2g)` of `GateEfficientSynthesis` under the synthesis
  hypothesis `GateSynth.Synthesis 𝒢 Xa len`, its validity, gate-set membership and counts;
  success probability at least `2/3` and conditional output within trace distance `ε` of
  `x(T)/‖x(T)‖` (`GateSynth.SOutcome`); `binary_select_solverL_synth` states this guarantee for
  the left-endpoint quadrature (`RestL`; the protocol and its counts do not depend on the
  instance);
* **synthesis of the preparation with exact reflections** (`binary_select_solver_trials`): the
  protocol `nprotocol (GateSynthTrials.synthPrep hS (ν/3) prepQ) (2g)` of
  `GateEfficientSynthesisTrials`; with an adjoint-closed gate set containing the kinds of the
  exact zero tests its trials consist of gates of the set, with the counts; it has the guarantees
  `NOutcome`, in particular every successful trial is within `ε/500` of `x(T)/‖x(T)‖` up to a
  global phase (the last claim of Theorem `ode:thm:gates`); `binary_select_solverL_trials`
  states `NOutcome` for the left-endpoint quadrature (`RestL`).

The per-trial outcome on branch-dependent meshes for any native data
(`native_time_trials_outcomeB`) combines the certificate of the exact target on branch-dependent
meshes (`GateSelect.ODE.prep_certificateB`) with the synthesis error of the preparation
(`GateSynthTrials.synthPrep_approx`) and the trial bounds of `GateEfficientSynthesisTrials`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinarySelect

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.GateODE (Label)
open SparseHamiltonian.GateODE.Time (TParams TOracles teval trun)
open SparseHamiltonian.GateSelect.ODE (BInstanceOK bsW targetB prep_certificateB target_factsB
  targetB_norm_le)
open SparseHamiltonian.GateQuad (vQ wQ)
open SparseHamiltonian.GateSynthTrials (synthPrep STW SX)
open ODEStateNormalization (unitDirection)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The per-trial outcome on branch-dependent meshes -/

section Generic

variable {S Zs Z Y J Xa : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]
variable {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **The guarantees of the synthesised preparation on branch-dependent meshes.** Under the
hypotheses of `GateSelect.ODE.native_time_outcomeB` (the native identity of the label- and
slot-selected private family, the loading and weight preparation within `ζs`, the error budget
`24 d ζ + 3 ζs ≤ ν` and `BInstanceOK` for the ideal oracles), the released native protocol on
the synthesised preparation `synthPrep hS (ν/3) (tnprepC …)` has the guarantees `NOutcome`:
every successful trial is within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, the success
probability is at least `175/256 ≥ 2/3` and the conditional output is within trace distance
`ε`. -/
theorem native_time_trials_outcomeB (hS : GateSynth.Synthesis 𝒢 Xa len) (p : TParams)
    (hp : p.PublicOK) (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
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
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δG κ : ℝ)
    (hI : BInstanceOK p (seedV (S := S)) σ v wq fv Hb Lb G b x ys βG δG κ) :
    NOutcome (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
      (p.ratio_ge hp.g_ge) prim (x p.T) := by
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hν := hp.nu_pos
  have hη : 0 < p.nu / 3 := by positivity
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hU := hI.unitary
  have hDu : ∀ w, IsUnitary (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w) := fun w =>
    hU.priv _ _ (GatePointerEncoding.wordEquivFin p.m (fun i => w (Sum.inr i))).isLt
  have hDadj : ∀ w, tlabFam (m := p.m) (P := Reg S ℂ) σ.D true w =
      (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w)† := fun _ => rfl
  have hA := oprep_approx prim hprim tlabSel UJg hUJg nd hnd ar hζ har
    (tlabFam (P := Reg S ℂ) σ.D) hDu hDadj hN (teval (seedV (S := S)) σ) (fun _ => rfl)
    (fun adj => tode_eval_uj (seedV (S := S)) σ UJg hUJ tlabSel (tlabFam (P := Reg S ℂ) σ.D) adj)
    (fun adj => tode_eval_priv (seedV (S := S)) σ UJg adj)
    (tsrcMacro p loadC wpC) hζs
    (fun c adj => tsrcMacro_approx p prim hprim loadC hloadV wpC hwpV (seedV (S := S)) σ hU hζs
      hload hwp c adj)
    (tsrcMacro_valid p loadC hloadV wpC hwpV) p.prepC (osec_tprepC p) (noseed_tprepC p hp) hvalid
    (fun i hi => GateODE.Time.teval_isUnitary (seedV (S := S)) σ hU norm_seedV i (hvalid i hi))
  rw [prodOps_teval, nSrcAny_eq, cP, cSF, cST] at hA
  have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 2 : ℕ) : ℝ) * ζs ≤ p.nu := by
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 2 : ℕ) : ℝ) = 3 := by norm_num
    rw [e2, e3]
    linarith only [hbudget]
  have hA' := hA.mono hδ
  -- the certificate of the exact target on branch-dependent meshes
  have hC := prep_certificateB p hp (seedV (S := S)) norm_seedV σ v wq fv Hb Lb G b x ys βG δG κ
    hI
  obtain ⟨hy, hbud, hdirY⟩ := target_factsB hp hI
  have hNorm := targetB_norm_le p hp.T_pos.le v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd (x 0) wq
    fv
  have hB : 0 < p.mass (x 0) (bsW p wq fv) := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (x 0) (bsW p wq fv) hB hI.prep
  have h := hC.vector_error
  have hm : p.mass (x 0) (bsW p wq fv) = ODESourceBranches.mass (p.zsrc (x 0) (bsW p wq fv)) :=
    rfl
  rw [← hdec, ← hm] at h
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    simp only [TParams.acc]
    linarith
  have hUS : IsUnitary (nrun prim (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC))) :=
    nrun_isUnitary prim hprim _ (GateSynthTrials.synthPrep_valid hS hη _ hprepV)
  have hne := hI.target_ne
  have hηδ : p.nu / 3 + p.nu ≤ 4 / 3 * ImprovedODEQueryBudget.precision p.ratio p.acc := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
    linarith only [e]
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize targetB p v Hb Lb (x 0) wq fv = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (x 0) (bsW p wq fv) ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (x p.T)‖ ≤ p.ε / 1000 := hdirY
  have hAT := GateSynthTrials.synthPrep_approx hS hη (tnprepC p UJg nd ar loadC wpC) hprepV prim
    hprim Urel hν.le hA'
  obtain ⟨-, -, hmean, hdir⟩ := GateSynthTrials.native_trial_bounds10 prim
    GateSynthTrials.hnP_SWO (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) hUS
    (GateSynthTrials.synthPrep_pres hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC) prim) Urel hAT y
    (p.mass (x 0) (bsW p wq fv)) p.ratio p.acc hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc
    hNorm hbud' h hηδ
  refine noutcome_of_bounds (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) prim hprim
    (GateSynthTrials.synthPrep_valid hS hη _ hprepV) (x p.T) hne p.ratio p.ε
    (p.ratio_ge hp.g_ge) hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

end Generic

/-! ### The binary-data solvers over a finite gate set -/

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **Gate-efficient dissipative ODE solver from time-indexed binary sparse data on
branch-dependent meshes over a finite gate set** (Theorem `ode:thm:gates`, time-dependent part,
with the branch-dependent meshes of Lemma `ode:lem:gate-select` and finite-set synthesis as a
hypothesis).

For the public data `q`, the binary data `D` and the source circuits `loadC`, `wpC` of
`binary_select_solver`, the synthesised protocol `sprotocol hS (ε/200) (prepQ q loadC wpC) (2g)`
depends only on the public data. Its trials consist of valid gates of `𝒢` and primitive calls;
in every history it makes at most `80 g` times the primitive calls of one native preparation
(bounded in `binary_select_counts`) and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(80 g N + 40 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)` elementary gates (`N` the gates of
one native preparation, `n = |W| + |XW| + |Zs| + k` and `G = 20 g N + 10 g (4 n + 3)`); its
register has the native wires and the `|Xa|` synthesis ancillas. For every input and instance
satisfying the hypotheses of `binary_select_solver` (a positive source quadrature on the `2^m`
left-endpoint nodes with `RestB`) it succeeds with probability at least `2/3`, and its
conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem binary_select_solver_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ GateSynth.synthBudget hS (q.ε / 200) (trialN (prepQ q loadC wpC) j),
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ GateSynth.synthBudget hS (q.ε / 200) (trialN (prepQ q loadC wpC) j) →
        GateSynth.GateOf 𝒢 g) ∧
    (∀ c : Query → Bool,
      ((GateSynth.sprotocol hS (q.ε / 200) (prepQ q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (prepQ q loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((GateSynth.sprotocol hS (q.ε / 200) (prepQ q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        (40 * q.params.ratio * nGatesN (prepQ q loadC wpC) +
          20 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) +
            Fintype.card Zs + q.kx) + 3)) *
        (c₁ * Real.log ((10 * q.params.ratio * nGatesN (prepQ q loadC wpC) +
          5 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) +
            Fintype.card Zs + q.kx) + 3) + 1) / (q.ε / 200)) + c₀)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A ⊕ Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
          (arQ q).bT + (arQ q).bP + (arQ q).A + 3) + Fintype.card Zs) + q.kx + 1 +
        Fintype.card Xa ∧
    ∀ x : X,
      (∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
        (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
        (βG δG κ ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC) (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ →
      GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (prepQ q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨hV, -, -, -, -, hcard, hout⟩ :=
    binary_select_solver q hq D en hrange hdec loadC hloadV wpC hwpV
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  refine ⟨fun j => GateSynth.sprotocol_valid hS hη _ hV j,
    fun c => (GateSynth.sprotocol_worst hS hη _ hV q.params.ratio
      (q.params.ratio_ge hq.g_ge) c).2, fun c₀ c₁ hc₀ hc₁ hlen => ?_, ?_, ?_⟩
  · have h := GateSynth.sprotocol_worst_log hS hη (by linarith) _ hV q.params.ratio
      (q.params.ratio_ge hq.g_ge) hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [Fintype.card_sum, hcard]
  · intro x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp hbud hR
    exact GateSynth.soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
      (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x)
      (primsT_isUnitary D en x) _
      (instanceB q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ
        hR).target_ne
      (hout x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp hbud hR)

/-- **The finite-gate-set solver with the left-endpoint quadrature**: the guarantee
`GateSynth.SOutcome` of `binary_select_solver_synth` under `RestL` (the left-endpoint quadrature
with the weights `T/2^m` and the source certificate of `GateEfficientQuadrature`); the protocol,
its validity, gate-set membership and counts are those of `binary_select_solver_synth`, which do
not depend on the instance. -/
theorem binary_select_solverL_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
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
    (βG δG Λ L bs δb ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestL q D en x Jl Wp fv G bf xs ys βG δG Λ L bs δb) :
    GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (prepQ q loadC wpC) q.params.ratio
      (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨hV, -⟩ := binary_select_counts q hq loadC hloadV wpC hwpV
  have hp := q.params_ok hq
  have hε : 0 < q.ε := hp.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hp.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  have hI := instanceL q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp fv G bf xs ys βG δG Λ L bs δb
    hR
  exact GateSynth.soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
    (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x)
    (primsT_isUnitary D en x) _ (hI.toB hp).target_ne
    (binary_select_solverL q hq D en hrange hdec loadC hloadV wpC hwpV x hrH hcH hrD hcD hPSD Jl
      Wp fv G bf xs ys βG δG Λ L bs δb ζs hζs hload hwp hbud hR)

/-- **Gate-efficient dissipative ODE solver from time-indexed binary sparse data on
branch-dependent meshes over a finite gate set with exact reflections** (Theorem
`ode:thm:gates`, time-dependent part, with the branch-dependent meshes of Lemma
`ode:lem:gate-select` and finite-set synthesis as a hypothesis, including the per-trial claim).

For the public data `q`, the binary data `D` and the source circuits `loadC`, `wpC` of
`binary_select_solver`, the synthesised protocol
`nprotocol (synthPrep hS (ν/3) (prepQ q loadC wpC)) (2g)` depends only on the public data.
Under `Synthesis 𝒢 Xa len`, `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢` its trials consist of valid
gates of `𝒢` and primitive calls; one native preparation has the counts of
`binary_select_counts`, the synthesised preparation at most `N len(ν/3/(N+1))` gates and exactly
the native calls; in every history the protocol makes at most `80 g` times the native calls and
uses at most `80 g N_S + 40 g (4 n + 3)` gates (`n = |W| + |XW| + |SX| + k`), at most
`80 g N (c₁ log((N+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` if `len ζ ≤ c₁ log(1/ζ) + c₀`. For every
input and instance satisfying the hypotheses of `binary_select_solver` (`RestB`) it has the
guarantees `NOutcome`: every successful trial is within `ε/500` of `x(T)/‖x(T)‖` up to a global
phase, the success probability is at least `2/3`, and the conditional output is within trace
distance `ε`. -/
theorem binary_select_solver_trials (hS : GateSynth.Synthesis 𝒢 Xa len)
    (hadj : GateSynthTrials.AdjClosed 𝒢) (hzt : GateSynthTrials.zeroTestKinds ⊆ 𝒢) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) j →
        GateSynth.GateOf 𝒢 g) ∧
    nGatesN (prepQ q loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * ((apG q.kx q.b q.m q.params.l).length + (28 * q.kx + 2)) +
        2 * (arQ q).circ.length + (2 * (arQ q).bP + (arQ q).bT + 1)) + nGatesN loadC +
      2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (prepQ q loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) ≤
      nGatesN (prepQ q loadC wpC) * len (q.params.nu / 3 / (nGatesN (prepQ q loadC wpC) + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) =
      nCallsN c (prepQ q loadC wpC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (prepQ q loadC wpC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
            (arQ q).bP (arQ q).A) Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio
          (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        40 * q.params.ratio * (nGatesN (prepQ q loadC wpC) *
          (c₁ * Real.log ((nGatesN (prepQ q loadC wpC) + 1) / (q.params.nu / 3)) + c₀)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP (arQ q).A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
            (arQ q).bP (arQ q).A) Xa) + q.kx) + 3)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT (arQ q).bP
        (arQ q).A Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        ((1 + 2 * (2 * q.m + 14) + (4 * q.m + 62) * (2 * q.m + 14)) + (6 * q.kx + 4 * q.b) +
          (arQ q).bT + (arQ q).bP + (arQ q).A + 3) +
        (Fintype.card Zs + 1 + tnPool q.params (Fin q.kx) Zs (ZA q.m ⊕ SZ4 q.kx q.b) (arQ q).bT
          (arQ q).bP (arQ q).A + Fintype.card Xa)) + q.kx + 1 ∧
    ∀ x : X,
      (∀ g i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ g j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ g i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ g j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, g)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ g, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, g))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ) (wq : ℕ → ℝ)
        (fv : ℕ → Reg (Fin q.kx) ℂ) (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf xs : ℝ → Reg (Fin q.kx) ℂ) (ys : Bool × (Fin q.m → Bool) → ℝ → Reg (Fin q.kx) ℂ)
        (βG δG κ ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC) (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      RestB q D en x Jl Wp wq fv G bf xs ys βG δG κ →
      NOutcome (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) := by
  obtain ⟨-, hG, hC, -, -, -⟩ := binary_select_counts q hq loadC hloadV wpC hwpV
  obtain ⟨hV, -, -, hSG, hSC, hWC, hWG, hWL, hcard, -⟩ :=
    GateSynthTrials.native_ode_time_solver_trials hS hadj hzt q.params (q.params_ok hq) q.UJg
      (hadUJ4_ok q.σ q.hσ) (ndQ q) (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC
      hloadV wpC hwpV
  refine ⟨hV, hG, hC, hSG, hSC, hWC, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin] at hWG
    exact hWG
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWL c₀ c₁ hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [hcard, card_ZB, Fintype.card_fin]
  · intro x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ ζs hζs hload hwp hbud hR
    exact native_time_trials_outcomeB hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
      (ndQ q) (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
      (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x)
      ⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ rfl
      (nativeOKQ q hq D en hrange hdec x) ζs hζs hload hwp hbud (vQ q.params q.params.M) wq fv
      (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δG κ
      (instanceB q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp wq fv G bf xs ys βG δG κ hR)

/-- **The per-trial solver with the left-endpoint quadrature**: the guarantees `NOutcome` of
`binary_select_solver_trials` under `RestL` (no hypothesis on the gate set is needed for them);
the protocol, its gate-set membership and counts are those of `binary_select_solver_trials`. -/
theorem binary_select_solverL_trials (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ (2 * q.m))) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin (2 * q.m) ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
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
    (βG δG Λ L bs δb ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) loadC)
      (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsT (R := ℂ) (m := 2 * q.m) D en x) wpC)
      (liftB (matOp Wp)) ζs)
    (hbud : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu)
    (hR : RestL q D en x Jl Wp fv G bf xs ys βG δG Λ L bs δb) :
    NOutcome (synthPrep hS (q.params.nu / 3) (prepQ q loadC wpC)) q.params.ratio q.ε
      (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) (m := 2 * q.m) D en x) (xs q.T) :=
  native_time_trials_outcomeB hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) (ndQ q)
    (ndQ_public q) (arQ q) q.ζ hq.ζ_pos.le (arQ_ok q hq) loadC hloadV wpC hwpV
    (primsT (R := ℂ) (m := 2 * q.m) D en x) (primsT_isUnitary D en x)
    ⟨UJop (R := ℂ) q.UJg, privFamB q.params D en x q.rho q.γ, Jl, Wp⟩ rfl
    (nativeOKQ q hq D en hrange hdec x) ζs hζs hload hwp hbud (vQ q.params q.params.M)
    (wQ q.params q.params.M) fv (HbB q.params D en x) (LbB q.params D en x) G bf xs ys βG δG _
    ((instanceL q hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp fv G bf xs ys βG δG Λ L bs δb
      hR).toB (q.params_ok hq))

end Binary

end

end SparseHamiltonian.GateBinarySelect
