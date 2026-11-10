import MeshCertificateODE.Binary
import GateEfficientSelective.ODEBudget

/-!
# The certificate-form time-dependent solver over a finite gate set

The finite-gate-set solvers of `GateEfficientSelective` (the native preparation compiled
selectively, `GateSelective.selPrep`: the gates of the finite gate set `𝒢` kept, the other gates
synthesised, every call and every supplied source circuit kept) were proved correct under the
released instance conditions, which require positive semidefinite represented dissipative samples
(`GateODE.Time.TParams.InstanceOK`). The native solver under the manuscript's certificates
(`cert_native_time_outcome`) allows represented samples of either sign, but over the native gate
model. This module combines the two for the uniform mesh with the slot-time sources (the on-mesh
source layout) and exact binary data:

* `cert_time_outcome_of`: for every compiled preparation `P` on the released trial register that is
  valid, never touches the fresh flag and pool of the exact zero tests, and is within `ν/3 + δ` on
  clean inputs of every lifted operator `liftB (conj U)` that the native preparation is within `δ`
  of, the released four-attempt protocol `nprotocol P (2g)` (the actual preparation `P`, the exact
  zero tests, the literal reverse-adjoint of `P` as its inverse) has the guarantees
  `GateNative.NOutcome` against `x(T)` under the certificate-form instance conditions
  `CertInstanceOK` (represented samples of either sign): every successful trial within `ε/500` of
  the normalised solution up to a global phase, success probability at least `2/3`, conditional
  output within trace distance `ε`. The selected-vector error, the amplitude lower bound and the
  direction bound are derived from the certificate of the actual preparation for the repaired target
  (`cert_prep_certificate`, `cert_target_facts'`); the solver's guarantee is not a hypothesis.
* `cert_time_prep_bounds`: these intermediate bounds stated for the actual preparation `P`: the
  repaired target `y` is nonzero with `‖y‖ ≤ B_m ≤ g ‖y‖` and direction within `ε/1000` of that of
  `x(T)`, and the selected vector `d = good† (P s)` has the error `‖3 B_m d - y‖ ≤ 10 ν B_m` and the
  amplitude `‖d‖ ≥ 1/(3g) - 10ν/3`.
* `cert_time_sel_outcome`: the same for the selective preparation
  `selPrep hS (ν/3) (tnprepC …)` (`GateSelective.selPrep_valid`, `selPrep_pres`, `selPrep_approx`):
  the local synthesis error is charged on the actual preparation, which is amplified with its
  literal adjoint; `cert_time_sel_prep_bounds`: its selected-vector error and amplitude.
* `binary_ode_time_cert_sel`: the time-indexed binary-data form of
  `GateSelective.binary_ode_time_budget_sel` (gates, calls and qubits in `𝔟` with the supplied
  loading and weight-preparation circuits charged linearly and outside the synthesis logarithm),
  with the guarantees under `CertRest` (the certificate-form conditions on the lifted samples:
  accretive true generator pieces, integrable, their propagator, the source certificate at the
  slot times and the sample certificate; no positivity of the represented samples).

The exact zero tests are the released ones: the gate kinds of the exact computational-basis zero
tests are assumed in the gate set (`zeroTestKinds ⊆ 𝒢`, an explicit hypothesis), and their gates
are counted in the gate bounds (the term `40 g (4 n + 3)`). The gate set is closed under adjoints
(`AdjClosed 𝒢`, for the literal inverses). The protocol is that of the released finite-set
solvers; only the instance conditions change.

Scope: the uniform mesh `M = 2^m` with the sources at the slot times and exact binary entries
(`hdec`), the case `T > 0`, `η_H + η_D > 0` (`GateBinaryODETime.PubT.OK`); no general sizes, no
approximate decoding, no off-mesh source nodes. The source executions of the protocol are counted
in `ManuscriptConformance.GateODETimeCertFinite`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory OracleCircuit GateCircuit GateNative GateSynth
  GateSynthTrials GateSelective
open GateODE (OInstr OWire AW goodF Label)
open GateODE.Time (TParams TOracles teval trun)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The correctness argument under the certificates -/

section Generic

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]

set_option maxHeartbeats 1600000 in
/-- **The certificate-form correctness argument for any compiled preparation.** For public data
with `PublicOK`, the released native data, loading and weight-preparation circuits within `ζ_s`
with `24 d ζ + 3 ζ_s ≤ ν`, the certificate-form instance conditions `CertInstanceOK`
(represented samples of either sign) and every preparation `P` on the trial register that is
valid, never touches the fresh flag and pool, and is within `ν/3 + δ` on clean inputs of every
lifted operator `liftB (conj U)` that the native preparation is within `δ` of: the protocol
`nprotocol P (2g)` has the guarantees `NOutcome` against `x(T)`. -/
theorem cert_time_outcome_of (p : TParams) (hp : p.PublicOK)
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
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : Fin p.M → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (bf : Fin p.M → ℝ → Reg S ℂ) (sol : ℝ → Reg S ℂ) (U : ℝ → Reg S ℂ → ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (gb cq ζc : ℝ)
    (hI : CertInstanceOK p (seedV (S := S)) σ Hs Ls G bf sol U bs gb cq ζc)
    (P : List (NInstr (STW p S Zs Z ar.bT ar.bP ar.A X) Y J)) (hPV : ∀ i ∈ P, i.Valid)
    (hPpres : Pres2 (ZeroOn reflWire) (nrun prim P))
    (hPA : ∀ (Urel : Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ) →L[ℂ]
        Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ)) (δ : ℝ), 0 ≤ δ →
      ApproxOn CleanX (nrun prim (tnprepC p UJg nd ar loadC wpC)) (liftB (conj Urel)) δ →
      ApproxOn CleanX (nrun prim P) (liftB (conj Urel)) (p.nu / 3 + δ)) :
    NOutcome P p.ratio p.ε (p.ratio_ge hp.g_ge) prim (sol p.T) := by
  have hν := hp.nu_pos
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
  -- the certificate of the actual preparation for the repaired target
  have hC := cert_prep_certificate hp (seedV (S := S)) norm_seedV σ Hs Ls G bf sol U bs gb cq ζc
    hI
  obtain ⟨hy, hbud, hdirY⟩ := cert_target_facts' hp hI
  obtain ⟨-, hpsd', -, -⟩ := hI.repaired hp.T_pos.le
  have hNorm := p.target_norm_le hp.T_pos.le Hs (repLs Ls (pathκ p.T G Hs Ls)) hI.select.selfH
    hpsd' (sol 0) bs
  have hB : 0 < p.mass (sol 0) bs := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (sol 0) bs hB hI.prep
  have h := hC.vector_error
  have hm : p.mass (sol 0) bs = ODESourceBranches.mass (p.zsrc (sol 0) bs) := rfl
  rw [← hdec, ← hm] at h
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    simp only [TParams.acc]
    linarith
  have hUS : IsUnitary (nrun prim P) := nrun_isUnitary prim hprim _ hPV
  have hne := hI.target_ne
  have hηδ : p.nu / 3 + p.nu ≤ 4 / 3 * ImprovedODEQueryBudget.precision p.ratio p.acc := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
    linarith only [e]
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (sol 0) bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (sol p.T)‖ ≤ p.ε / 1000 := hdirY
  have hAT := hPA Urel p.nu hν.le hA'
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds10 prim hnP_SWO P hUS hPpres Urel hAT y
    (p.mass (sol 0) bs) p.ratio p.acc hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm
    hbud' h hηδ
  refine noutcome_of_bounds P prim hprim hPV (sol p.T) hne p.ratio p.ε (p.ratio_ge hp.g_ge)
    hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

set_option maxHeartbeats 1600000 in
/-- **The preparation certificate of the actual compiled preparation.** Under the hypotheses of
`cert_time_outcome_of` (the validity of `P` and its preservation of the zero-test wires are not
needed): the repaired discretised target `y` of the solver is nonzero, `‖y‖ ≤ B_m ≤ g ‖y‖` with
`B_m` the coefficient mass and `g = p.ratio`, its direction is within `ε/1000` of that of `x(T)`,
and the selected vector of the actual preparation, the good-subspace component
`d = good† (P s)` of its output on the seed, has the selected-vector error
`‖3 B_m d - y‖ ≤ 10 ν B_m` and the amplitude `‖d‖ ≥ 1/(3g) - 10ν/3`. The solver's guarantee is
not a hypothesis. -/
theorem cert_time_prep_bounds (p : TParams) (hp : p.PublicOK)
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
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : Fin p.M → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (bf : Fin p.M → ℝ → Reg S ℂ) (sol : ℝ → Reg S ℂ) (U : ℝ → Reg S ℂ → ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (gb cq ζc : ℝ)
    (hI : CertInstanceOK p (seedV (S := S)) σ Hs Ls G bf sol U bs gb cq ζc)
    (P : List (NInstr (STW p S Zs Z ar.bT ar.bP ar.A X) Y J))
    (hPA : ∀ (Urel : Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ) →L[ℂ]
        Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ)) (δ : ℝ), 0 ≤ δ →
      ApproxOn CleanX (nrun prim (tnprepC p UJg nd ar loadC wpC)) (liftB (conj Urel)) δ →
      ApproxOn CleanX (nrun prim P) (liftB (conj Urel)) (p.nu / 3 + δ)) :
    p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs ≠ 0 ∧
    ‖p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs‖ ≤ p.mass (sol 0) bs ∧
    p.mass (sol 0) bs ≤ p.ratio * ‖p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs‖ ∧
    ‖unitDirection (p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs) - unitDirection (sol
        p.T)‖ ≤
      p.ε / 1000 ∧
    ‖(3 * p.mass (sol 0) bs) • (goodN†) (nrun prim P sN) - p.target Hs (repLs Ls (pathκ p.T G Hs
        Ls)) (sol 0) bs‖ ≤
      10 * p.nu * p.mass (sol 0) bs ∧
    1 / (3 * p.ratio) - 10 / 3 * p.nu ≤ ‖(goodN†) (nrun prim P sN)‖ := by
  have hν := hp.nu_pos
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
  -- the certificate of the actual preparation for the repaired target
  have hC := cert_prep_certificate hp (seedV (S := S)) norm_seedV σ Hs Ls G bf sol U bs gb cq ζc
    hI
  obtain ⟨hy, hbud, hdirY⟩ := cert_target_facts' hp hI
  obtain ⟨-, hpsd', -, -⟩ := hI.repaired hp.T_pos.le
  have hNorm := p.target_norm_le hp.T_pos.le Hs (repLs Ls (pathκ p.T G Hs Ls)) hI.select.selfH
    hpsd' (sol 0) bs
  have hB : 0 < p.mass (sol 0) bs := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (sol 0) bs hB hI.prep
  have h := hC.vector_error
  have hm : p.mass (sol 0) bs = ODESourceBranches.mass (p.zsrc (sol 0) bs) := rfl
  rw [← hdec, ← hm] at h
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  have hηδ : p.nu / 3 + p.nu ≤ 4 / 3 * p.nu := le_of_eq (by ring)
  generalize p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs = y at h hy hbud hdirY hNorm ⊢
  have hbud' : p.mass (sol 0) bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (sol p.T)‖ ≤ p.ε / 1000 := hdirY
  have hAT := hPA Urel p.nu hν.le hA'
  have hvec : ‖(3 * p.mass (sol 0) bs) • (goodN†) (nrun prim P sN) - y‖ ≤ 10 * p.nu * p.mass (sol
      0) bs :=
    vector_error10 (nrun prim P) Urel hAT y (p.mass (sol 0) bs) p.nu hB.le h hηδ
  refine ⟨hy, hNorm, hbud', hdirY', hvec, ?_⟩
  have hg0 : 0 < p.ratio := lt_of_lt_of_le one_pos (p.ratio_ge hp.g_ge)
  have hg0' : p.ratio ≠ 0 := hg0.ne'
  have h3B : (0 : ℝ) < 3 * p.mass (sol 0) bs := mul_pos (by norm_num) hB
  have h1 := norm_sub_norm_le y ((3 * p.mass (sol 0) bs) • (goodN†) (nrun prim P sN))
  rw [norm_sub_rev y, norm_smul, Real.norm_eq_abs, abs_of_pos h3B] at h1
  have h2 : p.mass (sol 0) bs / p.ratio ≤ ‖y‖ := by
    rw [div_le_iff₀ hg0]
    linarith [hbud']
  have h4 : 3 * p.mass (sol 0) bs * (1 / (3 * p.ratio) - 10 / 3 * p.nu) ≤
      3 * p.mass (sol 0) bs * ‖(goodN†) (nrun prim P sN)‖ := by
    have e : 3 * p.mass (sol 0) bs * (1 / (3 * p.ratio) - 10 / 3 * p.nu) =
        p.mass (sol 0) bs / p.ratio - 10 * p.nu * p.mass (sol 0) bs := by
      field_simp
      try ring
    rw [e]
    linarith [h1, h2, hvec]
  exact le_of_mul_le_mul_left h4 h3B

variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The selective preparation under the certificates**: the native preparation `tnprepC`
compiled selectively with the budget `ν/3` and placed on the trial register has the guarantees
`NOutcome` against `x(T)` for every instance satisfying `CertInstanceOK`. -/
theorem cert_time_sel_outcome (hS : Synthesis 𝒢 X len) (p : TParams) (hp : p.PublicOK)
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
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : Fin p.M → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (bf : Fin p.M → ℝ → Reg S ℂ) (sol : ℝ → Reg S ℂ) (U : ℝ → Reg S ℂ → ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (gb cq ζc : ℝ)
    (hI : CertInstanceOK p (seedV (S := S)) σ Hs Ls G bf sol U bs gb cq ζc) :
    NOutcome (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
      (p.ratio_ge hp.g_ge) prim (sol p.T) := by
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hη : 0 < p.nu / 3 := by have := hp.nu_pos; positivity
  exact cert_time_outcome_of p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim σ
    hUJ hN ζs hζs hload hwp hbudget Hs Ls G bf sol U bs gb cq ζc hI _
    (selPrep_valid hS hη _ hprepV) (selPrep_pres hS (p.nu / 3) _ prim)
    (fun Urel δ hδ hA => selPrep_approx hS hη _ hprepV prim hprim Urel hδ hA)

/-- **The preparation certificate of the selective preparation**: `cert_time_prep_bounds` for the
native preparation `tnprepC` compiled selectively with the budget `ν/3` and placed on the trial
register (`GateSelective.selPrep_approx`): the selected-vector error `‖3 B_m d - y‖ ≤ 10 ν B_m`
and the amplitude `‖d‖ ≥ 1/(3g) - 10ν/3` of the actual compiled preparation. -/
theorem cert_time_sel_prep_bounds (hS : Synthesis 𝒢 X len) (p : TParams) (hp : p.PublicOK)
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
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : Fin p.M → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (bf : Fin p.M → ℝ → Reg S ℂ) (sol : ℝ → Reg S ℂ) (U : ℝ → Reg S ℂ → ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (gb cq ζc : ℝ)
    (hI : CertInstanceOK p (seedV (S := S)) σ Hs Ls G bf sol U bs gb cq ζc) :
    p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs ≠ 0 ∧
    ‖p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs‖ ≤ p.mass (sol 0) bs ∧
    p.mass (sol 0) bs ≤ p.ratio * ‖p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs‖ ∧
    ‖unitDirection (p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs) - unitDirection (sol
        p.T)‖ ≤
      p.ε / 1000 ∧
    ‖(3 * p.mass (sol 0) bs) •
        (goodN†) (nrun prim (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) sN) -
      p.target Hs (repLs Ls (pathκ p.T G Hs Ls)) (sol 0) bs‖ ≤ 10 * p.nu * p.mass (sol 0) bs ∧
    1 / (3 * p.ratio) - 10 / 3 * p.nu ≤
      ‖(goodN†) (nrun prim (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) sN)‖ := by
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hη : 0 < p.nu / 3 := by have := hp.nu_pos; positivity
  exact cert_time_prep_bounds p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim σ
    hUJ hN ζs hζs hload hwp hbudget Hs Ls G bf sol U bs gb cq ζc hI _
    (fun Urel δ hδ hA => selPrep_approx hS hη _ hprepV prim hprim Urel hδ hA)

end Generic

/-! ### The time-indexed binary-data solver over a finite gate set under the certificates -/

section Binary

open GateBinary GateBinaryODE GateBinaryODETime
open GateODEBudget (gammaOf qOf prepBoundT binary_ode_time_sizes)
open GateBitBudget (bitB HasBits)
open NativeSparseBlockEncoding (Data Query)

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

set_option maxHeartbeats 1600000 in
/-- **The time-dependent Theorem `ode:thm:gates` over a finite gate set under the manuscript's
certificates, time-indexed binary data** (uniform mesh, slot-time sources, exact binary entries).
The protocol and all its counts are those of `GateSelective.binary_ode_time_budget_sel`: valid
trials over `𝒢`; at most `R = prepBoundT q ∅ ∅ ≤ 2·10¹⁸ q* (𝔟+1)³` synthesised gate occurrences per
preparation; in every history at most `80 g (G_src + K (64 c₁ (𝔟+1) + c₀ + 1)) + 40 g (4 n + 3)`
gates with `K = 2·10¹⁸ q* (𝔟+1)³` and `n = 3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|`,
`G_src = |loadC| + 2 |wpC|` charged linearly and outside the synthesis logarithm; at most
`7864320 g q*` calls of each coherent sampled-time oracle besides `80 g` times the calls of `loadC`
and twice those of `wpC`; at most `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits. The guarantees
`NOutcome` (every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, success
probability at least `2/3`, conditional output within trace distance `ε`) hold for every input with
the energy bounds of every sample, loading and weight-preparation circuits within `ζ_s` with
`98304 q* ζ + 3 ζs ≤ ν`, and the certificate-form conditions `CertRest` (represented samples of
either sign). -/
theorem binary_ode_time_cert_sel (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid) (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    (∀ j, (∀ i ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nSynN 𝒢 (q.prep loadC wpC) : ℝ) ≤ prepBoundT (Zs := Zs) q [] [] ∧
    prepBoundT (Zs := Zs) q [] [] ≤
      2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 ∧
    ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 *
          (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1)) + c₀ + 1)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ) (sol : ℝ → Reg (Fin q.kx) ℂ)
        (U : ℝ → Reg (Fin q.kx) ℂ → ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ)
        (gb cq ζc ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      CertRest q D en x Jl Wp G bf sol U bs gb cq ζc →
      NOutcome (selPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (sol q.T) := by
  obtain ⟨hV, hsyn, hBp, hW, hC, hQ, -⟩ := binary_ode_time_budget_sel hS hadj hzt hc₀ hc₁ hlen bd
    q hq hγ hζ hb hc0 hT hH hD D en hrange hdec loadC hloadV hloadG wpC hwpV hwpG
  refine ⟨hV, hsyn, hBp, hW, hC, hQ, ?_⟩
  intro x hrH hcH hrD hcD Jl Wp G bf sol U bs gb cq ζc ζs hζs hload hwp hbud hR
  obtain ⟨-, hd, -, -, -, -⟩ := binary_ode_time_sizes q hq hγ
  have hbud' : 24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu := by
    have hζ0 := hq.ζ_pos.le
    have := mul_le_mul_of_nonneg_right hd hζ0
    linarith
  exact cert_time_sel_outcome hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ) q.nd
    q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC hwpV (primsT (R := ℂ) D en x)
    (primsT_isUnitary D en x)
    (⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩ :
      TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ)) rfl
    (q.nativeOK hq D en hrange hdec x) ζs hζs hload hwp hbud' (HsT D en x) (LsT D en x) G bf sol
    U bs gb cq ζc (cert_instanceOK q hq D en hrange x hrH hcH hrD hcD Jl Wp G bf sol U bs gb cq ζc
      hR)

end Binary

end

end SparseHamiltonian.MeshCertificateODE
