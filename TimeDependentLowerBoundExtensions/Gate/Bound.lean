import TimeDependentLowerBoundExtensions.Gate.Program
import TimeDependentLowerBoundExtensions.Core.Cost

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for gate-level time-dependent circuits

Theorem `hsl:thm:main` counts sparse queries, with all known gates free (the manuscript), and
applies to the time-dependent class with time-independent hard instances (the paragraphs after the
proof of Theorem `hs:thm:time`). The manuscript's gate-level theorem (`hs:thm:gates`) is stated for
time-independent Hamiltonians only; the gate-level time-dependent circuits used here are the
package's slot-selected circuits
(`SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation`). The statements below are
corollaries of Theorem `hsl:thm:main` for those circuits, an extension of the remark after the proof
of Theorem `hs:thm:time`.

In these circuits the instance enters only through the supplied private operation `D_k`
(slot-selected, counted once per call, `nPriv`); `U_J` and the elementary gates are public. A
sparse-query lower bound in this setting therefore concerns private operations realised by sparse
queries: `NativeRealization D D_x q` says that, on one fixed isometric encoding, `D_x` is
implemented by a program over all call forms (plain, inverse, controlled, controlled inverse;
`AdaptiveODELowerBound.Access.callFamily`) of the native sparse queries of `D`, with an untouched
spectator register, using at most `q` value calls (location calls free). It is a hypothesis built
from the package's program model (`MultiOracleCircuit.Program`) and value-call weight
(`AdaptiveHamiltonianLowerBound.Access.valueWeight`). The realisation is exact
(`p.eval x ∘ e = e ∘ D_x`), as in the exact-gate model of the package's slot-selected circuits; the
manuscript's gate model (Section `hs:sec:gates`) allows each controlled private operation an error
`ξ` at a fixed primitive-oracle cost, and that approximate form (which would add `nPriv · ξ` to the
endpoint error) is not stated here. The hard paths are constant in time, so `D_k = D_x` at every
slot. All bounds below are conditional on `NativeRealization`.

* `nonempty_privAccess`: every private call, with any literal controls and forward or inverse,
  then costs at most `2q` Boolean queries (masked calls, `Core.implementsOn_masked`);
* `main_max_gate`: for gate-level circuits on the time, mixed and precision families with
  natively realised private operations (at most `q` value calls each) and endpoint error `ε`
  against `exp(-iτH_x)`, `c₀ (√s τ + √(sτr) + r) ≤ q · max(nPriv_T, nPriv_M, nPriv_P)`;
* `main_max_gate_uniform`: the same under the uniform-mesh criterion on the constant path
  (`TimeDependentHamiltonianLowerBound.UniformGuarantee`: error at most `ε` against every
  propagator of the path from the identity), the form of the error bound of
  `gate_efficient_time_simulation`; the link between that theorem's conclusion and
  `UniformGuarantee` is not stated in this library.

**Satisfiability.** The hypothesis holds with `q = 1` for every call form of one native sparse
query (`Gate.nativeRealization_call`, in `Gate.NonVacuity`). Not stated in this library: the
private operation `D_x = i·beOp D x` of the
Hermitian block encodings of `BlockEncoding.Hard` (padded by the fixed phase `-1` outside its
register) has the inverse `R₁ = (1 + i·beOp D x)/2` of `1 - D_x` (padded by `1/2`), with
`‖R₁‖ ≤ 1` and `beJ† R₁ beJ = (1 + i H_x/α)/2` for `α = beAlpha D` (eq. `hs:eq:blockspecial`),
which are the clock hypotheses of `gate_efficient_time_simulation` with boundary `beJ`; and it is
realised by the fixed swap and two controlled runs of the six-query program, at most `8` value
calls. Stating this needs a padded qubit layout of the native sparse space, which the package
does not provide. Likewise the package's native gate-level model `SparseHamiltonian.GateNative`
(`NativeOK`, `nCallsN`, `native_time_simulation`), whose primitives act on qubit registers, is
not covered.
-/

namespace TimeDependentLowerBoundExtensions.Gate

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
  SparseHamiltonian.GateCircuit.SlotSim
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open TimeDependentHamiltonianLowerBound (constPath UniformGuarantee)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily)
open scoped InnerProduct InnerProductSpace

/-- **Native realisation of a private operation**: on one fixed isometric encoding `e` into a
control qubit, a spectator register and the native space, `D_x` is implemented, uniformly in
`x`, by one program over all call forms of the native sparse queries of `D` with at most `q`
value calls (location calls free). -/
def NativeRealization {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    {s : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (D : Data X N Z s) (Dp : X → V →L[ℂ] V) (q : ℕ) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω)
    (e : V →L[ℂ] Joint Bool (Joint Ω (SparseFlagEmbedding.Space (N × N) Z)))
    (p : MultiOracleCircuit.Program (callFamily (specOracles Ω D))),
    e† ∘L e = 1 ∧ (∀ x, p.eval x ∘L e = e ∘L Dp x) ∧ p.cost (fun c => valueWeight c.1) ≤ q

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **Every private call costs at most `2q` Boolean queries**: from a native realisation of the
private operation with at most `q` value calls and a certificate of the native primitives with
weight `hardCost`, every label of `privFamily D` (any literal controls) has a certificate of
weight `2q`. -/
theorem nonempty_privAccess {I : Type*} [Fintype I] {X N Z : Type} [Fintype N] [DecidableEq N]
    [Fintype Z] [AddCommGroup Z] {s : ℕ} {y : X → I → Bool} (D : Data X N Z s)
    (A : PhaseAccess I y (oracles D) hardCost) (Dp : X → Vsp a P →L[ℂ] Vsp a P)
    {q : ℕ} (hR : NativeRealization D Dp q) :
    Nonempty (PhaseAccess I y (privFamily (m := m) (r := r) (K := K) Dp) (fun _ => 2 * q)) := by
  classical
  obtain ⟨Ω, _, e, p, he, hp, hq⟩ := hR
  let A₁ : PhaseAccess I y (specOracles Ω D) hardCost := (A.spectate Ω).congr fun _ _ => rfl
  let A₂ := Core.callAccess A₁ (SparseLowerBounds.specOracles_unitary Ω D)
  have hc := EncodedMultiOracle.implements_compile A₂.enc A₂.enc_isometry
    (fun x => A₂.fam.isUnitary_phase (y x))
    (AdaptiveODELowerBound.Access.callFamily_unitary (SparseLowerBounds.specOracles_unitary Ω D))
    p (fun c => hardCost c.1) A₂.impl
  have hcost : p.cost (fun c => hardCost c.1) ≤ 2 * q := by
    rw [Core.cost_hardCost_fst]
    omega
  have hD : EncodedOracle.ImplementsOn (fun x => A₂.fam.phase (y x)) Dp (A₂.enc ∘L e)
      (2 * q) := by
    obtain ⟨r', hr, hrc⟩ := hc
    refine ⟨r', fun x => ?_, hrc.trans hcost⟩
    rw [← ContinuousLinearMap.comp_assoc, hr x, ContinuousLinearMap.comp_assoc, hp x,
      ContinuousLinearMap.comp_assoc]
  have hDe : (A₂.enc ∘L e)† ∘L (A₂.enc ∘L e) = 1 := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc _ A₂.enc, A₂.enc_isometry, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp, he]
  obtain ⟨ι, _, L, hL⟩ := slotOracle_const_eq (a := a) (m := m) (r := r) (K := K) (P := P)
  choose msk hmsk using hL
  let B : PhaseAccess I y (fun cs x => MaskedProgram.masked (msk cs) (Dp x)) (fun _ => 2 * q) :=
    PhaseAccess.ofImplementsOn (Core.maskedBoolean ι A₂.fam) (Core.maskedEncoding ι (A₂.enc ∘L e))
      (Core.maskedEncoding_isometry ι _ hDe)
      (fun cs => Core.implementsOn_masked ι (msk cs) A₂.fam y hD)
  exact ⟨(B.conj L.symm).congr fun cs x => (hmsk cs (Dp x)).symm⟩

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for gate-level time-dependent circuits, endpoint form** (eq.
`hsl:eq:main`, max form): for gate-level circuits (valid instruction lists in the slot-selected
semantics `runT`, public unitaries `U_J`, any numbers of ancilla, slot and reuse wires) on the
time, mixed and precision families whose private operations are constant in time, unitary and
natively realised with at most `q` value calls, each with endpoint error `ε` against
`exp(-iτH_x)` on an isometric encoding,
`c₀ (√s τ + √(sτr) + r) ≤ q · max(nPriv_T, nPriv_M, nPriv_P)`. -/
theorem main_max_gate (h : HSRange τ s ε) (q : ℕ)
    (aT mT rT KT aM mM rM KM aP mP rP KP : ℕ)
    {PT PM PP : Type*} [NormedAddCommGroup PT] [InnerProductSpace ℂ PT] [CompleteSpace PT]
    [NormedAddCommGroup PM] [InnerProductSpace ℂ PM] [CompleteSpace PM]
    [NormedAddCommGroup PP] [InnerProductSpace ℂ PP] [CompleteSpace PP]
    (UJT : Vsp aT PT →L[ℂ] Vsp aT PT) (hUJT : IsUnitary UJT)
    (DT : (Fin (timeN τ) → Fin (2 ^ hsMu s)) → Vsp aT PT →L[ℂ] Vsp aT PT)
    (hDT : ∀ x, IsUnitary (DT x)) (hRT : NativeRealization (timeData τ s h.s_ge) DT q)
    (gsT : List (Instr (Wire aT mT rT KT))) (hgsT : ∀ g ∈ gsT, g.Valid Wire.anc)
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] Reg (Wire aT mT rT KT) PT)
    (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖runT UJT (fun _ => DT j) gsT ∘L ιT - ιT ∘L NormedSpace.exp
      ((-Complex.I * (τ : ℂ)) •
        SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε)
    (UJM : Vsp aM PM →L[ℂ] Vsp aM PM) (hUJM : IsUnitary UJM)
    (DM : (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → Vsp aM PM →L[ℂ] Vsp aM PM)
    (hDM : ∀ x, IsUnitary (DM x)) (hRM : NativeRealization (mixedMainData τ ε s h.s_ge) DM q)
    (gsM : List (Instr (Wire aM mM rM KM))) (hgsM : ∀ g ∈ gsM, g.Valid Wire.anc)
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] Reg (Wire aM mM rM KM) PM)
    (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖runT UJM (fun _ => DM j) gsM ∘L ιM - ιM ∘L NormedSpace.exp
      ((-Complex.I * (τ : ℂ)) •
        SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε)
    (UJP : Vsp aP PP →L[ℂ] Vsp aP PP) (hUJP : IsUnitary UJP)
    (DP : (Fin (precN τ ε) → Bool) → Vsp aP PP →L[ℂ] Vsp aP PP)
    (hDP : ∀ x, IsUnitary (DP x)) (hRP : NativeRealization (precisionMainData τ ε s h.s_ge) DP q)
    (gsP : List (Instr (Wire aP mP rP KP))) (hgsP : ∀ g ∈ gsP, g.Valid Wire.anc)
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] Reg (Wire aP mP rP KP) PP)
    (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖runT UJP (fun _ => DP x) gsP ∘L ιP - ιP ∘L NormedSpace.exp
      ((-Complex.I * (τ : ℂ)) •
        SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      q * max (nPriv gsT : ℝ) (max (nPriv gsM : ℝ) (nPriv gsP)) := by
  obtain ⟨pT, hpT, hcT⟩ := exists_program UJT hUJT DT gsT hgsT
  obtain ⟨pM, hpM, hcM⟩ := exists_program UJM hUJM DM gsM hgsM
  obtain ⟨pP, hpP, hcP⟩ := exists_program UJP hUJP DP gsP hgsP
  have key := Core.main_max_uniform_weight h (2 * q)
    (privFamily (m := mT) (r := rT) (K := KT) DT)
    (fun cs x => slotOracle_isUnitary cs _ fun _ _ => hDT x)
    (nonempty_privAccess (timeData τ s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) DT hRT)
    pT ιT hιT (fun j => by rw [hpT j]; exact hsimT j)
    (privFamily (m := mM) (r := rM) (K := KM) DM)
    (fun cs x => slotOracle_isUnitary cs _ fun _ _ => hDM x)
    (nonempty_privAccess (mixedMainData τ ε s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) DM hRM)
    pM ιM hιM (fun j => by rw [hpM j]; exact hsimM j)
    (privFamily (m := mP) (r := rP) (K := KP) DP)
    (fun cs x => slotOracle_isUnitary cs _ fun _ _ => hDP x)
    (nonempty_privAccess (precisionMainData τ ε s h.s_ge)
      (scalarAccess (by have := h.s_ge; omega)) DP hRP)
    pP ιP hιP (fun x => by rw [hpP x]; exact hsimP x)
  rw [hcT, hcM, hcP] at key
  push_cast at key
  linarith

/-- **Theorem `hsl:thm:main` for gate-level time-dependent circuits** (eq. `hsl:eq:main`, max
form): as `main_max_gate`, for circuits meeting the uniform-mesh criterion on the constant path
(`UniformGuarantee`: for every propagator `U` of the path from the identity, error at most `ε`
against `U(τ)` on an isometric encoding; the form of the error bound of
`SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation`),
`c₀ (√s τ + √(sτr) + r) ≤ q · max(nPriv_T, nPriv_M, nPriv_P)`. -/
theorem main_max_gate_uniform (h : HSRange τ s ε) (q : ℕ)
    (aT mT rT KT aM mM rM KM aP mP rP KP : ℕ)
    {PT PM PP : Type*} [NormedAddCommGroup PT] [InnerProductSpace ℂ PT] [CompleteSpace PT]
    [NormedAddCommGroup PM] [InnerProductSpace ℂ PM] [CompleteSpace PM]
    [NormedAddCommGroup PP] [InnerProductSpace ℂ PP] [CompleteSpace PP]
    (UJT : Vsp aT PT →L[ℂ] Vsp aT PT) (hUJT : IsUnitary UJT)
    (DT : (Fin (timeN τ) → Fin (2 ^ hsMu s)) → Vsp aT PT →L[ℂ] Vsp aT PT)
    (hDT : ∀ x, IsUnitary (DT x)) (hRT : NativeRealization (timeData τ s h.s_ge) DT q)
    (gsT : List (Instr (Wire aT mT rT KT))) (hgsT : ∀ g ∈ gsT, g.Valid Wire.anc)
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] Reg (Wire aT mT rT KT) PT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : UniformGuarantee (fun j => runT UJT (fun _ => DT j) gsT) ιT
      (constPath (timeData τ s h.s_ge)) τ ε)
    (UJM : Vsp aM PM →L[ℂ] Vsp aM PM) (hUJM : IsUnitary UJM)
    (DM : (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → Vsp aM PM →L[ℂ] Vsp aM PM)
    (hDM : ∀ x, IsUnitary (DM x)) (hRM : NativeRealization (mixedMainData τ ε s h.s_ge) DM q)
    (gsM : List (Instr (Wire aM mM rM KM))) (hgsM : ∀ g ∈ gsM, g.Valid Wire.anc)
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] Reg (Wire aM mM rM KM) PM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : UniformGuarantee (fun j => runT UJM (fun _ => DM j) gsM) ιM
      (constPath (mixedMainData τ ε s h.s_ge)) τ ε)
    (UJP : Vsp aP PP →L[ℂ] Vsp aP PP) (hUJP : IsUnitary UJP)
    (DP : (Fin (precN τ ε) → Bool) → Vsp aP PP →L[ℂ] Vsp aP PP)
    (hDP : ∀ x, IsUnitary (DP x)) (hRP : NativeRealization (precisionMainData τ ε s h.s_ge) DP q)
    (gsP : List (Instr (Wire aP mP rP KP))) (hgsP : ∀ g ∈ gsP, g.Valid Wire.anc)
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] Reg (Wire aP mP rP KP) PP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : UniformGuarantee (fun x => runT UJP (fun _ => DP x) gsP) ιP
      (constPath (precisionMainData τ ε s h.s_ge)) τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      q * max (nPriv gsT : ℝ) (max (nPriv gsM : ℝ) (nPriv gsP)) := by
  have hτ : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  exact main_max_gate h q aT mT rT KT aM mM rM KM aP mP rP KP UJT hUJT DT hDT hRT gsT hgsT ιT hιT
    ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ _ ιT hτ).1 hT)
    UJM hUJM DM hDM hRM gsM hgsM ιM hιM
    ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ _ ιM hτ).1 hM)
    UJP hUJP DP hDP hRP gsP hgsP ιP hιP
    ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ _ ιP hτ).1 hP)

end

end TimeDependentLowerBoundExtensions.Gate
