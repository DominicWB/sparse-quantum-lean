import GateEfficientSelective.Sources
import GateEfficientSynthesisTrials.Solver
import GateEfficientBinaryNodes.Integrated

/-!
# Theorem `ode:thm:gates` with retained source circuits: the native solvers

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

**The released correctness argument for any compiled preparation.** The instance arguments of
the released finite-gate-set solvers (`GateSynthTrials.native_ode_solver_trials`,
`GateSynthTrials.native_ode_time_solver_trials`, `GateBinaryNodes.native_time_trials_outcomeC`)
use three properties of the compiled preparation `P` on the trial register: its instructions are
valid, it never touches the fresh flag and pool of the zero tests, and it is within `ν/3 + δ` of
the lifted released preparation on clean work wires whenever the native preparation is within
`δ`. Here these arguments are stated for every compiled preparation `P` with the three
properties (`const_outcome_of`, `time_outcome_of`, `timeC_outcome_of`): the released randomised
amplification of the actual preparation `P` with its actual inverse and the exact zero tests
gives `GateNative.NOutcome` (every successful trial within `ε/500` of the normalised solution up
to a global phase, success probability at least `2/3`, conditional output within trace distance
`ε`).

**The selective preparation.** `selPrep hS (ν/3) prepN` has the three properties
(`selPrep_valid`, `selPrep_pres`, `selPrep_approx`), so the native solvers keep their guarantees
with the source circuits retained over the gate set:

* `native_ode_solver_sel` (constant coefficients) and `native_ode_time_solver_sel`
  (time-dependent coefficients, common mesh; the same preparation `tnprepC` serves the solvers on
  branch-dependent meshes, `native_time_sel_outcomeBI`): every trial consists of valid gates of
  `𝒢` and primitive calls; the native counts; the synthesised gate occurrences are at most
  `K = prepGates + 84 d C_J + 6 d G_C`, independently of the source circuits (supplied over
  `𝒢`); and in every history the protocol uses at most
  `40 g (G_src + K (c₁ log((K+1)/(ν/3)) + c₀ + 1)) + 20 g (4 n + 3)` gates (with `2g` in place of
  `g` for time-dependent coefficients), `G_src = |srcC 0| + |srcC 1|` (respectively
  `|loadC| + 2 |wpC|`) the gates of the supplied source circuits, charged once each and outside
  the synthesis logarithm, and `n` the tested wires (linear in the source workspace `|Zs|`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open GateODE (OInstr Params Label Oracles goodF)
open GateODE.Time (TParams TOracles teval trun)
open GateSelect.ODE (bsW targetB targetB_norm_le)
open GateBinaryNodes (BCore TFacts prep_certificateC BInstanceOKI target_factsBI)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

section Generic

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]

/-- **Constant coefficients: the released correctness argument for any compiled preparation.**
Under the instance hypotheses of `GateNative.native_ode_solver` (unchanged), every preparation
`P` on the trial register that is valid, never touches the fresh flag and pool, and is within
`ν/3 + δ` of the lifted released preparation whenever the native preparation is within `δ`,
gives the guarantees `NOutcome` to the released protocol `nprotocol P g`. -/
theorem const_outcome_of (p : Params) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (D : Label p.k p.l → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
    (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (H L : Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ)
    (ζs : ℝ) (hprim : ∀ j, IsUnitary (prim j))
    (hN : NativeOK prim nd (selOp (labFam D false))) (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 2 * ζs ≤ p.nu)
    (hI : p.InstanceOK (seedV (S := S))
      (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b)
    (P : List (NInstr (SNW p S Zs Z ar.bT ar.bP ar.A X) Y J)) (hPV : ∀ i ∈ P, i.Valid)
    (hPpres : Pres2 (ZeroOn reflWire) (nrun prim P))
    (hPA : ∀ (Urel : Reg (GateODE.AW p.a p.m p.r p.K p.k p.l p.f) (Reg S ℂ) →L[ℂ]
        Reg (GateODE.AW p.a p.m p.r p.K p.k p.l p.f) (Reg S ℂ)) (δ : ℝ), 0 ≤ δ →
      ApproxOn CleanX (nrun prim (nprepC p UJg nd ar srcC)) (liftB (conj Urel)) δ →
      ApproxOn CleanX (nrun prim P) (liftB (conj Urel)) (p.nu / 3 + δ)) :
    NOutcome P p.g p.ε hp.g_ge prim (p.target H L x0 b) := by
  have hν := hp.nu_pos
  have hτ := hp.tau_pos.le
  obtain ⟨cP, -, cS, -, -⟩ := p.prepC_counts hτ hν
  have hvalid := p.prepC_valid hτ hν hp.r₀_nonneg hp.rb_nonneg hp.T_pos.le hp.B_pos
  let σ : Oracles p.a (Label p.k p.l) (Reg S ℂ) := ⟨UJop (R := ℂ) UJg, D, Jsrc⟩
  have hU := p.unitaries_of (norm_seedV (S := S)) hI
  have hJ : ∀ c, IsUnitary (Jsrc c) := hU.src
  have hDu : ∀ w, IsUnitary (labFam D false w) := fun w => hU.priv _
  have hDadj : ∀ w, labFam D true w = (labFam D false w)† := fun _ => rfl
  have hA := oprep_approx prim hprim labSel UJg hUJg nd hnd ar hζ har (labFam D) hDu hDadj hN
    (OInstr.eval (GateODE.wiring (seedV (S := S))) σ) (fun _ => rfl)
    (fun adj => ode_eval_uj (seedV (S := S)) σ UJg rfl labSel (labFam D) adj)
    (fun adj => ode_eval_priv (seedV (S := S)) σ UJg adj)
    (srcMacro p srcC) hζs
    (fun c adj => srcMacro_approx p prim hprim srcC hsrcV Jsrc hJ hζs hsrc (seedV (S := S)) D
      (UJop (R := ℂ) UJg) c adj)
    (srcMacro_valid p srcC hsrcV) p.prepC (osec_prepC p) (noseed_prepC p hτ hν) hvalid
    (fun i hi => OInstr.eval_isUnitary (GateODE.wiring (seedV (S := S))) σ hU.uj hU.priv hU.src
      hU.seed i (hvalid i hi))
  rw [prodOps_oeval, nSrcAny_eq, cP, cS false, cS true] at hA
  have hT := hp.T_pos.le
  have hSel := hI.select
  have hCert := p.prep_certificate hp (seedV (S := S)) norm_seedV σ H L x0 b hI
  have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 b hI.init_norm hI.forcing_norm
  have hmass := p.mass_zsrc x0 b hT hI.init_norm hI.forcing_norm
  have hNorm : ‖p.target H L x0 b‖ ≤ p.B := by
    rw [← hmass]
    exact p.solution_le_mass hT H L hSel.selfH hSel.selfL hI.psd x0 b hI.init_norm
      hI.forcing_norm
  have h := hCert.vector_error
  rw [hmass, ← hdec] at h
  have hδ0 : 0 ≤ ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 1 : ℕ) : ℝ) * ζs :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hζs)
  have hηδ : p.nu / 3 + (((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 1 : ℕ) : ℝ) * ζs) ≤
      4 / 3 * ImprovedODEQueryBudget.precision p.g p.ε := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.g p.ε := rfl
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2, e3]
    linarith only [hbudget, e]
  have hne := hI.target_ne
  have hbud := hI.budget
  generalize GateODE.run (GateODE.wiring (seedV (S := S))) σ p.prepC = Urel at h hA
  generalize p.target H L x0 b = x at h hNorm hne hbud ⊢
  exact noutcome10 prim hnP_SWO P hprim hPV hPpres Urel (hPA Urel _ hδ0 hA) x p.B p.g p.ε hne
    hp.g_ge hp.ε_pos hp.ε_half hNorm hbud h hηδ

/-- **Time-dependent coefficients, common mesh: the released correctness argument for any
compiled preparation.** Under the instance hypotheses of `GateNative.native_ode_time_solver`
(unchanged), every preparation `P` on the trial register with the three properties of
`const_outcome_of` gives the guarantees `NOutcome` to `nprotocol P (2g)` against `x(T)`. -/
theorem time_outcome_of (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
    (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
    (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
    (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ) (hprim : ∀ j, IsUnitary (prim j))
    (hN : NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false))) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs)
    (hbudget : 24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu)
    (hI : p.InstanceOK (seedV (S := S))
      (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
      Hs Ls G b x bs βG δG βb δb bmax)
    (P : List (NInstr (STW p S Zs Z ar.bT ar.bP ar.A X) Y J)) (hPV : ∀ i ∈ P, i.Valid)
    (hPpres : Pres2 (ZeroOn reflWire) (nrun prim P))
    (hPA : ∀ (Urel : Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ) →L[ℂ]
        Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ)) (δ : ℝ), 0 ≤ δ →
      ApproxOn CleanX (nrun prim (tnprepC p UJg nd ar loadC wpC)) (liftB (conj Urel)) δ →
      ApproxOn CleanX (nrun prim P) (liftB (conj Urel)) (p.nu / 3 + δ)) :
    NOutcome P p.ratio p.ε (p.ratio_ge hp.g_ge) prim (x p.T) := by
  have hν := hp.nu_pos
  let σ : TOracles p.a p.m p.l (Reg S ℂ) := ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hU := p.unitary_of hI
  have hDu : ∀ w, IsUnitary (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w) := fun w =>
    hU.priv _ _ (GatePointerEncoding.wordEquivFin p.m (fun i => w (Sum.inr i))).isLt
  have hDadj : ∀ w, tlabFam (m := p.m) (P := Reg S ℂ) σ.D true w =
      (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w)† := fun _ => rfl
  have hA := oprep_approx prim hprim tlabSel UJg hUJg nd hnd ar hζ har
    (tlabFam (P := Reg S ℂ) σ.D) hDu hDadj hN (teval (seedV (S := S)) σ) (fun _ => rfl)
    (fun adj => tode_eval_uj (seedV (S := S)) σ UJg rfl tlabSel (tlabFam (P := Reg S ℂ) σ.D) adj)
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
  have hCert := p.prep_certificate hp (seedV (S := S)) norm_seedV σ Hs Ls G b x bs βG δG βb δb
    bmax hI
  obtain ⟨hy, hbud, hdirY⟩ := p.target_facts hp hI
  have hNorm := p.target_norm_le hp.T_pos.le Hs Ls hI.select.selfH hI.psd (x 0) bs
  have hB : 0 < p.mass (x 0) bs := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (x 0) bs hB hI.prep
  have h := hCert.vector_error
  have hm : p.mass (x 0) bs = ODESourceBranches.mass (p.zsrc (x 0) bs) := rfl
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
  generalize p.target Hs Ls (x 0) bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (x p.T)‖ ≤ p.ε / 1000 := hdirY
  have hAT := hPA Urel p.nu hν.le hA'
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds10 prim hnP_SWO P hUS hPpres Urel hAT y
    (p.mass (x 0) bs) p.ratio p.acc hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud'
    h hηδ
  refine noutcome_of_bounds P prim hprim hPV (x p.T) hne p.ratio p.ε (p.ratio_ge hp.g_ge)
    hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

/-- **Time-dependent coefficients on branch-dependent meshes: the released correctness argument
for any compiled preparation.** Under the hypotheses of `GateBinaryNodes.native_time_outcomeC`
(the released chain on branch-dependent meshes with the three target facts), every preparation
`P` on the trial register with the three properties of `const_outcome_of` gives the guarantees
`NOutcome` to `nprotocol P (2g)` against `xT`. -/
theorem timeC_outcome_of (p : TParams) (hp : p.PublicOK)
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
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (x0 xT : Reg S ℂ)
    (hI : BCore p (seedV (S := S)) σ v wq fv Hb Lb x0)
    (hF : TFacts p v Hb Lb x0 wq fv xT) (hne : xT ≠ 0)
    (P : List (NInstr (STW p S Zs Z ar.bT ar.bP ar.A X) Y J)) (hPV : ∀ i ∈ P, i.Valid)
    (hPpres : Pres2 (ZeroOn reflWire) (nrun prim P))
    (hPA : ∀ (Urel : Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ) →L[ℂ]
        Reg (GateODE.AW p.a p.m p.r p.K p.m p.l p.f) (Reg S ℂ)) (δ : ℝ), 0 ≤ δ →
      ApproxOn CleanX (nrun prim (tnprepC p UJg nd ar loadC wpC)) (liftB (conj Urel)) δ →
      ApproxOn CleanX (nrun prim P) (liftB (conj Urel)) (p.nu / 3 + δ)) :
    NOutcome P p.ratio p.ε (p.ratio_ge hp.g_ge) prim xT := by
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
  obtain ⟨hy, hbud, hdirY⟩ := hF
  have hC := prep_certificateC p hp (seedV (S := S)) norm_seedV σ v wq fv Hb Lb x0 hI hy hbud
  have hNorm := targetB_norm_le p hp.T_pos.le v hI.nodes Hb Lb hI.selfH hI.selfL hI.psd x0 wq fv
  have hB : 0 < p.mass x0 (bsW p wq fv) := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 (bsW p wq fv) hB hI.prep
  have h := hC.vector_error
  have hm : p.mass x0 (bsW p wq fv) = ODESourceBranches.mass (p.zsrc x0 (bsW p wq fv)) := rfl
  rw [← hdec, ← hm] at h
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    simp only [TParams.acc]
    linarith
  have hUS : IsUnitary (nrun prim P) := nrun_isUnitary prim hprim _ hPV
  have hηδ : p.nu / 3 + p.nu ≤ 4 / 3 * ImprovedODEQueryBudget.precision p.ratio p.acc := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
    linarith only [e]
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize targetB p v Hb Lb x0 wq fv = y at h hy hbud hdirY hNorm
  have hbud' : p.mass x0 (bsW p wq fv) ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection xT‖ ≤ p.ε / 1000 := hdirY
  have hAT := hPA Urel p.nu hν.le hA'
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds10 prim hnP_SWO P hUS hPpres Urel hAT y
    (p.mass x0 (bsW p wq fv)) p.ratio p.acc hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc
    hNorm hbud' h hηδ
  refine noutcome_of_bounds P prim hprim hPV xT hne p.ratio p.ε (p.ratio_ge hp.g_ge) hp.ε_pos
    hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

end Generic

section Solvers

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- The separated closed form: `40 g (N_keep + K (c₁ λ + c₀))` with `N_keep ≤ G + K` is at most
`40 g (G + K (c₁ λ + c₀ + 1))`. -/
theorem sep_arith {c g Nk G K lam c₀ c₁ T : ℝ} (hc : 0 ≤ c) (hg : 0 ≤ g) (hNk : Nk ≤ G + K)
    (hW : T ≤ c * g * (Nk + K * (c₁ * lam + c₀))) :
    T ≤ c * g * (G + K * (c₁ * lam + c₀ + 1)) := by
  have h1 : Nk + K * (c₁ * lam + c₀) ≤ G + K * (c₁ * lam + c₀ + 1) := by nlinarith
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc hg)
  linarith

/-- **Gate-efficient dissipative ODE solver over a finite gate set with retained source circuits,
constant coefficients** (partial formalisation, under this package's format hypotheses, of the
finite-set statement of Theorem `ode:thm:gates`, constant coefficients, with
equation `ode:eq:gate-main` in the separated form of the paper).

The supplied source circuits `srcC` are circuits over the gate set `𝒢` (their gates are gates
of `𝒢`); the native preparation `nprepC p UJg nd ar srcC` is compiled selectively with the
budget `ν/3`: the source circuits are retained verbatim, the other gates not in `𝒢` are
synthesised, every primitive call is kept. Under `Synthesis 𝒢 X len`, `AdjClosed 𝒢` and
`zeroTestKinds ⊆ 𝒢`: (1) every trial consists of valid gates of `𝒢` and primitive calls;
(2) one native preparation has the native counts; (3) at most
`K = prepGates + 84 d C_J + 6 d G_C` of its gate occurrences are synthesised, independently of the
source circuits; (4) the selective preparation has at most `nKeepN + nSynN len(ν/3/(nSynN+1))`
gates and exactly the native calls; (5) in every history the protocol makes at most `40 g` times
the native calls and (6) uses at most `40 g N_S + 20 g (4 n + 3)` gates, and, with
`len ζ ≤ c₁ log(1/ζ) + c₀`, at most
`40 g (G_src + K (c₁ log((K+1)/(ν/3)) + c₀ + 1)) + 20 g (4 n + 3)` gates,
`G_src = |srcC 0| + |srcC 1|`, `n = |W| + |XW| + |SX| + |S|`; (7) the register `SNW` has
`|S| + 2 (|W| + (|Z| + bT + bP + A + 3) + (|Zs| + 1 + n_P + |X|)) + |S| + 1` qubits; (8) for
every instance satisfying the hypotheses of `GateNative.native_ode_solver` (unchanged) the
protocol has the guarantees `NOutcome`. -/
theorem native_ode_solver_sel (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : Params) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid)
    (hsrcG : ∀ c, ∀ g, NInstr.gate g ∈ srcC c → GateOf 𝒢 g) :
    (∀ j, (∀ i ∈ trialN (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (nprepC p UJg nd ar srcC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN (srcC false) + nGatesN (srcC true) ∧
    (∀ q : J → Bool, nCallsN q (nprepC p UJg nd ar srcC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q (srcC false) + nCallsN q (srcC true)) ∧
    nSynN 𝒢 (nprepC p UJg nd ar srcC) ≤
      p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar ∧
    nGatesN (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) ≤
      nKeepN 𝒢 (nprepC p UJg nd ar srcC) + nSynN 𝒢 (nprepC p UJg nd ar srcC) *
        len (p.nu / 3 / (nSynN 𝒢 (nprepC p UJg nd ar srcC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) =
      nCallsN q (nprepC p UJg nd ar srcC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.g * nCallsN q (nprepC p UJg nd ar srcC)) ∧
    ((nprotocol (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * p.g * nGatesN (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) +
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (nPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
          wGateN : ℝ) ≤
        40 * p.g * (((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
          ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar : ℕ) : ℝ) *
            (c₁ * Real.log ((((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar :
              ℕ) : ℝ) + 1) / (p.nu / 3)) + c₀ + 1)) +
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (nPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (SNW p S Zs Z ar.bT ar.bP ar.A X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        (Fintype.card Zs + 1 + nPool p S Zs Z ar.bT ar.bP ar.A + Fintype.card X)) +
        Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.k p.l → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (H L : Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ)
      (ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (labFam D false)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      24 * (p.d : ℝ) * ζ + 2 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b →
      NOutcome (selPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g p.ε hp.g_ge prim
        (p.target H L x0 b) := by
  obtain ⟨hV, hG, hC, -, -, -, -⟩ :=
    native_ode_solver p hp UJg hUJg nd hnd ar ζ hζ har srcC hsrcV
  obtain ⟨-, hG0, -, -, -, -, -⟩ :=
    native_ode_solver p hp UJg hUJg nd hnd ar ζ hζ har (Zs := Zs) (fun _ => [])
      (fun _ i hi => by simp at hi)
  have hprepV : ∀ i ∈ nprepC p UJg nd ar srcC, i.Valid :=
    fun i hi => hV 0 i (List.mem_append_left _ hi)
  have hν := hp.nu_pos
  have hν1 : p.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.g p.ε hp.g_ge hp.eps_le_one
  have hη : 0 < p.nu / 3 := by positivity
  have hη1 : p.nu / 3 ≤ 1 := by linarith
  have hsyn : nSynN 𝒢 (nprepC p UJg nd ar srcC) ≤
      p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar := by
    have h1 := nSynN_nprepC_le 𝒢 hadj p UJg nd ar srcC hsrcG
    have h0 : nGatesN ([] : List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) = 0 := rfl
    rw [h0] at hG0
    omega
  obtain ⟨hSG, hSC⟩ := selPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := sel_protocol_worst hS hη _ hprepV p.g hp.g_ge
  refine ⟨fun j => ⟨trialSel_valid hS hη _ hprepV j, trialSel_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hsyn, hSG, hSC, hWC, hWG, fun c₀ c₁ hc₀ hc₁ hlen => ?_, card_SWO, ?_⟩
  · have hK : (nSynN 𝒢 (nprepC p UJg nd ar srcC) : ℝ) ≤
        ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar : ℕ) : ℝ) := by
      exact_mod_cast hsyn
    have hW := sel_protocol_worst_log hS hη hη1 _ hprepV p.g hp.g_ge hc₀ hc₁ hlen _ hK
    have hNk : (nKeepN 𝒢 (nprepC p UJg nd ar srcC) : ℝ) ≤
        ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) +
          ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar : ℕ) : ℝ) := by
      have h1 := nKeepN_le 𝒢 (nprepC p UJg nd ar srcC)
      have h2 : ((nKeepN 𝒢 (nprepC p UJg nd ar srcC) : ℕ) : ℝ) ≤
          ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar +
            nGatesN (srcC false) + nGatesN (srcC true) : ℕ) : ℝ) := by
        exact_mod_cast h1.trans hG
      push_cast at h2 ⊢
      linarith
    have hg0 : 0 ≤ p.g := le_trans zero_le_one hp.g_ge
    have := sep_arith (c := 40) (c₀ := c₀) (c₁ := c₁)
      (lam := Real.log ((((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar :
        ℕ) : ℝ) + 1) / (p.nu / 3))) (by norm_num) hg0 hNk (T := ((nprotocol (selPrep hS (p.nu / 3)
      (nprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost wGateN : ℝ) -
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (nPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3))
      (by linarith)
    linarith
  · intro prim D Jsrc H L x0 b ζs hprim hN hζs hsrc hbudget hI
    exact const_outcome_of p hp UJg hUJg nd hnd ar ζ hζ har srcC hsrcV prim D Jsrc H L x0 b ζs
      hprim hN hζs hsrc hbudget hI _ (selPrep_valid hS hη _ hprepV)
      (selPrep_pres hS (p.nu / 3) _ prim)
      (fun Urel δ hδ hA => selPrep_approx hS hη _ hprepV prim hprim Urel hδ hA)

/-- **Gate-efficient dissipative ODE solver over a finite gate set with retained source circuits,
time-dependent coefficients** (partial formalisation, under this package's format hypotheses, of
the finite-set statement of Theorem `ode:thm:gates`, time-dependent part,
with equation `ode:eq:gate-main` in the separated form of the paper). The supplied loading and
weight-preparation circuits are circuits over `𝒢`; the native preparation is compiled
selectively with the budget `ν/3`. The conclusions of `native_ode_solver_sel`, with the ratio
`2g` (so `80 g`, `40 g`), `G_src = |loadC| + 2 |wpC|`, the budget `24 d ζ + 3 ζs ≤ ν` and the
target `x(T)`; the guarantees hold on every instance satisfying the hypotheses of
`GateNative.native_ode_time_solver` (common mesh). -/
theorem native_ode_time_solver_sel (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (hloadG : ∀ g, NInstr.gate g ∈ loadC → GateOf 𝒢 g)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hwpG : ∀ g, NInstr.gate g ∈ wpC → GateOf 𝒢 g) :
    (∀ j, (∀ i ∈ trialN (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    nSynN 𝒢 (tnprepC p UJg nd ar loadC wpC) ≤
      p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar ∧
    nGatesN (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) ≤
      nKeepN 𝒢 (tnprepC p UJg nd ar loadC wpC) + nSynN 𝒢 (tnprepC p UJg nd ar loadC wpC) *
        len (p.nu / 3 / (nSynN 𝒢 (tnprepC p UJg nd ar loadC wpC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) =
      nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost (wCallN q) : ℝ) ≤
        40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    ((nprotocol (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
          (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
        40 * p.ratio * (((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
          ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar : ℕ) : ℝ) *
            (c₁ * Real.log ((((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar :
              ℕ) : ℝ) + 1) / (p.nu / 3)) + c₀ + 1)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (STW p S Zs Z ar.bT ar.bP ar.A X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        (Fintype.card Zs + 1 + tnPool p S Zs Z ar.bT ar.bP ar.A + Fintype.card X)) +
        Fintype.card S + 1 ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        Hs Ls G b x bs βG δG βb δb bmax →
      NOutcome (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
        (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨-, hG, hC, -, -, -, -⟩ :=
    native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  obtain ⟨-, hG0, -, -, -, -, -⟩ :=
    native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har (Zs := Zs) [] (by simp) []
      (by simp)
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hν := hp.nu_pos
  have hν1 : p.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.ratio p.acc
      (p.ratio_ge hp.g_ge) (by have := hp.ε_half; simp only [TParams.acc]; linarith)
  have hη : 0 < p.nu / 3 := by positivity
  have hη1 : p.nu / 3 ≤ 1 := by linarith
  have hsyn : nSynN 𝒢 (tnprepC p UJg nd ar loadC wpC) ≤
      p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar := by
    have h1 := nSynN_tnprepC_le 𝒢 hadj p UJg nd ar loadC hloadG wpC hwpG
    have h0 : nGatesN ([] : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) = 0 := rfl
    have h0' : nGatesN ([] : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) = 0 := rfl
    rw [h0, h0'] at hG0
    omega
  obtain ⟨hSG, hSC⟩ := selPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := sel_protocol_worst hS hη _ hprepV p.ratio (p.ratio_ge hp.g_ge)
  refine ⟨fun j => ⟨trialSel_valid hS hη _ hprepV j, trialSel_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hsyn, hSG, hSC, hWC, hWG, fun c₀ c₁ hc₀ hc₁ hlen => ?_, card_SWO, ?_⟩
  · have hK : (nSynN 𝒢 (tnprepC p UJg nd ar loadC wpC) : ℝ) ≤
        ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar : ℕ) : ℝ) := by
      exact_mod_cast hsyn
    have hW := sel_protocol_worst_log hS hη hη1 _ hprepV p.ratio (p.ratio_ge hp.g_ge) hc₀ hc₁
      hlen _ hK
    have hNk : (nKeepN 𝒢 (tnprepC p UJg nd ar loadC wpC) : ℝ) ≤
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
          ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar : ℕ) : ℝ) := by
      have h1 := nKeepN_le 𝒢 (tnprepC p UJg nd ar loadC wpC)
      have h2 : ((nKeepN 𝒢 (tnprepC p UJg nd ar loadC wpC) : ℕ) : ℝ) ≤
          ((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar +
            nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) := by
        exact_mod_cast h1.trans hG
      push_cast at h2 ⊢
      linarith
    have hg0 : 0 ≤ p.ratio := le_trans zero_le_one (p.ratio_ge hp.g_ge)
    have := sep_arith (c := 40) (c₀ := c₀) (c₁ := c₁)
      (lam := Real.log ((((p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar :
        ℕ) : ℝ) + 1) / (p.nu / 3))) (by norm_num) hg0 hNk (T := ((nprotocol (selPrep hS (p.nu / 3)
      (tnprepC p UJg nd ar loadC wpC)) p.ratio (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) -
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3))
      (by linarith)
    linarith
  · intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbudget hI
    exact time_outcome_of p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim D Jl Wp Hs
      Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbudget hI _
      (selPrep_valid hS hη _ hprepV) (selPrep_pres hS (p.nu / 3) _ prim)
      (fun Urel δ hδ hA => selPrep_approx hS hη _ hprepV prim hprim Urel hδ hA)

/-- **The selective preparation on branch-dependent meshes with the integrated certificate**: the
guarantees `NOutcome` of `nprotocol (selPrep hS (ν/3) (tnprepC …)) (2g)` for every instance of
`GateBinaryNodes.native_time_outcomeBI` (`BInstanceOKI`: branch-dependent meshes, positive
source quadrature, integrated sample-error certificate). -/
theorem native_time_sel_outcomeBI (hS : Synthesis 𝒢 X len) (p : TParams) (hp : p.PublicOK)
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
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δI κ : ℝ)
    (hI : BInstanceOKI p (seedV (S := S)) σ v wq fv Hb Lb G b x ys βG δI κ) :
    NOutcome (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
      (p.ratio_ge hp.g_ge) prim (x p.T) := by
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hη : 0 < p.nu / 3 := by have := hp.nu_pos; positivity
  exact timeC_outcome_of p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim σ hUJ
    hN ζs hζs hload hwp hbudget v wq fv Hb Lb (x 0) (x p.T) hI.core (target_factsBI hp hI)
    hI.target_ne _ (selPrep_valid hS hη _ hprepV) (selPrep_pres hS (p.nu / 3) _ prim)
    (fun Urel δ hδ hA => selPrep_approx hS hη _ hprepV prim hprim Urel hδ hA)

/-- **The selective preparation with the source certificate of `GateEfficientSelect`**
(partial formalisation, under this package's format hypotheses, of the finite-set statement of
Theorem `ode:thm:gates`, time-dependent part on branch-dependent meshes with a
positive source quadrature and the certificate of equation `ode:eq:gate-source-certificates`): every
instance satisfying `GateSelect.ODE.BInstanceOK` (uniform sample errors `δG`) has the guarantees
`NOutcome` for `nprotocol (selPrep hS (ν/3) (tnprepC …)) (2g)`, through the integrated certificate
with `δI = T δG` (`GateBinaryNodes.BInstanceOK.toI`). -/
theorem native_time_sel_outcomeB (hS : Synthesis 𝒢 X len) (p : TParams) (hp : p.PublicOK)
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
    (v wq : ℕ → ℝ) (fv : ℕ → Reg S ℂ)
    (Hb Lb : Bool × (Fin p.m → Bool) → ℕ → Reg S ℂ →L[ℂ] Reg S ℂ)
    (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
    (ys : Bool × (Fin p.m → Bool) → ℝ → Reg S ℂ) (βG δG κ : ℝ)
    (hI : GateSelect.ODE.BInstanceOK p (seedV (S := S)) σ v wq fv Hb Lb G b x ys βG δG κ) :
    NOutcome (selPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
      (p.ratio_ge hp.g_ge) prim (x p.T) :=
  native_time_sel_outcomeBI hS p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV prim hprim
    σ hUJ hN ζs hζs hload hwp hbudget v wq fv Hb Lb G b x ys βG (p.T * δG) κ
    (GateBinaryNodes.BInstanceOK.toI hp hI)

end Solvers

end

end SparseHamiltonian.GateSelective
