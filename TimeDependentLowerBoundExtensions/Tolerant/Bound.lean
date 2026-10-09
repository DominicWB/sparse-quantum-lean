import TimeDependentLowerBoundExtensions.Tolerant.Program
import TimeDependentLowerBoundExtensions.Gate.Bound

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for gate-level circuits with private operations realised within `ξ`

Theorem `hsl:thm:main` (the manuscript, line 2102, eq. `hsl:eq:main`) applies to the
time-dependent classes with time-independent hard instances (lines 1513-1516). The manuscript's
gate model (lines 1805-1812) realises each controlled private operation with error at most `ξ`
in the ancilla convention (lines 511-533), at a primitive-oracle cost independent of `ξ`. The
manuscript states this gate model for time-independent Hamiltonians (line 1849); its use for the
package's slot-selected time-dependent circuits (`SparseHamiltonian.GateCircuit.SlotSim.runT`),
as in `Gate.Bound`, extends lines 1513-1516, and the hard paths are constant in time. For these
circuits this module states Theorem `hsl:thm:main` under that model (`ApproxRealization`).

The error hypothesis is placed on the ideal circuit, the one running the exact private
operations, with endpoint error `ε₀`. The circuit actually executed runs the realised
operations; by `exists_approxProgram` its endpoint error is at most `ε₀ + nPriv · ξ`, and the
bound holds whenever this is at most an error `ε` in the range of Theorem `hsl:thm:main`. This is
how the manuscript adds up its errors in Theorem `hs:thm:gates` (lines 1814-1851, accounting
at lines 1823-1835: `ξ = ε/(24d)` for at most `6d` private operations, full output error at most
`ε`). A form whose hypothesis bounds the endpoint error of the executed circuit directly is not
stated here. Each of the three families has its own `ε₀` and `ξ`; only `q` and `ε` are shared.

* `main_max_gate_tolerant`: for gate-level circuits on the time, mixed and precision families
  whose private operations are realised within `ξ_F` by at most `q` value calls, each with
  endpoint error `ε₀_F` of the ideal circuit against `exp(-iτH_x)` and
  `ε₀_F + nPriv_F · ξ_F ≤ ε`, `c₀ (√s τ + √(sτr) + r) ≤ q · max(nPriv_T, nPriv_M, nPriv_P)` with
  `r = r(τ, ε)`;
* `main_max_gate_uniform_tolerant`: the same under the uniform-mesh criterion on the constant
  path for the ideal circuit (`TimeDependentHamiltonianLowerBound.UniformGuarantee` at `ε₀_F`);
* `main_max_gate_of_tolerant`, `main_max_gate_uniform_of_tolerant`: containment checks; the
  exact forms `Gate.main_max_gate` and `Gate.main_max_gate_uniform` are the case `ξ_F = 0`,
  `ε₀_F = ε` (through `approxRealization_zero_iff`).

The bounds are conditional on `ApproxRealization`; it holds for the bare call forms of the native
queries (`approxRealization_call`) and for every operation within `ξ` of an exactly realised one
(`approxRealization_of_near`). That the private operation of the released time-dependent
simulator is realised in this sense is not stated here.
-/

namespace TimeDependentLowerBoundExtensions.Tolerant

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
  SparseHamiltonian.GateCircuit.SlotSim
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open TimeDependentHamiltonianLowerBound (constPath UniformGuarantee)
open TimeDependentLowerBoundExtensions.Gate (NativeRealization)
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for gate-level circuits with private operations realised within
`ξ`** (eq. `hsl:eq:main`, max form): for gate-level circuits (valid instruction lists in the
slot-selected semantics `runT`, public unitaries `U_J`, any numbers of ancilla, slot and reuse
wires) on the time, mixed and precision families whose private operations are constant in time,
unitary and realised within `ξ_F` with at most `q` value calls each (`ApproxRealization`), each
ideal circuit (exact private operations) with endpoint error `ε₀_F` against `exp(-iτH_x)` on an
isometric encoding, and `ε₀_F + nPriv_F · ξ_F ≤ ε` for each of the three circuits,
`c₀ (√s τ + √(sτr) + r) ≤ q · max(nPriv_T, nPriv_M, nPriv_P)`. The executed circuit then has
endpoint error at most `ε₀_F + nPriv_F · ξ_F` (`exists_approxProgram`), the accounting of
Theorem `hs:thm:gates`; a hypothesis on the executed circuit's error directly is not used. -/
theorem main_max_gate_tolerant (h : HSRange τ s ε) (q : ℕ) (ε₀T ε₀M ε₀P ξT ξM ξP : ℝ)
    (aT mT rT KT aM mM rM KM aP mP rP KP : ℕ)
    {PT PM PP : Type*} [NormedAddCommGroup PT] [InnerProductSpace ℂ PT] [CompleteSpace PT]
    [NormedAddCommGroup PM] [InnerProductSpace ℂ PM] [CompleteSpace PM]
    [NormedAddCommGroup PP] [InnerProductSpace ℂ PP] [CompleteSpace PP]
    (UJT : Vsp aT PT →L[ℂ] Vsp aT PT) (hUJT : IsUnitary UJT)
    (DT : (Fin (timeN τ) → Fin (2 ^ hsMu s)) → Vsp aT PT →L[ℂ] Vsp aT PT)
    (hDT : ∀ x, IsUnitary (DT x)) (hRT : ApproxRealization (timeData τ s h.s_ge) DT q ξT)
    (gsT : List (Instr (Wire aT mT rT KT))) (hgsT : ∀ g ∈ gsT, g.Valid Wire.anc)
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] Reg (Wire aT mT rT KT) PT)
    (hιT : ιT† ∘L ιT = 1)
    (hsimT : ∀ j, ‖runT UJT (fun _ => DT j) gsT ∘L ιT - ιT ∘L NormedSpace.exp
      ((-Complex.I * (τ : ℂ)) •
        SparseStateOverlap.matrixOperator ((timeData τ s h.s_ge).matrix j))‖ ≤ ε₀T)
    (hbudT : ε₀T + nPriv gsT * ξT ≤ ε)
    (UJM : Vsp aM PM →L[ℂ] Vsp aM PM) (hUJM : IsUnitary UJM)
    (DM : (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → Vsp aM PM →L[ℂ] Vsp aM PM)
    (hDM : ∀ x, IsUnitary (DM x)) (hRM : ApproxRealization (mixedMainData τ ε s h.s_ge) DM q ξM)
    (gsM : List (Instr (Wire aM mM rM KM))) (hgsM : ∀ g ∈ gsM, g.Valid Wire.anc)
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] Reg (Wire aM mM rM KM) PM)
    (hιM : ιM† ∘L ιM = 1)
    (hsimM : ∀ j, ‖runT UJM (fun _ => DM j) gsM ∘L ιM - ιM ∘L NormedSpace.exp
      ((-Complex.I * (τ : ℂ)) •
        SparseStateOverlap.matrixOperator ((mixedMainData τ ε s h.s_ge).matrix j))‖ ≤ ε₀M)
    (hbudM : ε₀M + nPriv gsM * ξM ≤ ε)
    (UJP : Vsp aP PP →L[ℂ] Vsp aP PP) (hUJP : IsUnitary UJP)
    (DP : (Fin (precN τ ε) → Bool) → Vsp aP PP →L[ℂ] Vsp aP PP)
    (hDP : ∀ x, IsUnitary (DP x))
    (hRP : ApproxRealization (precisionMainData τ ε s h.s_ge) DP q ξP)
    (gsP : List (Instr (Wire aP mP rP KP))) (hgsP : ∀ g ∈ gsP, g.Valid Wire.anc)
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] Reg (Wire aP mP rP KP) PP)
    (hιP : ιP† ∘L ιP = 1)
    (hsimP : ∀ x, ‖runT UJP (fun _ => DP x) gsP ∘L ιP - ιP ∘L NormedSpace.exp
      ((-Complex.I * (τ : ℂ)) •
        SparseStateOverlap.matrixOperator ((precisionMainData τ ε s h.s_ge).matrix x))‖ ≤ ε₀P)
    (hbudP : ε₀P + nPriv gsP * ξP ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      q * max (nPriv gsT : ℝ) (max (nPriv gsM : ℝ) (nPriv gsP)) := by
  obtain ⟨ΩT, _, eT, prT, heT, hprT, hqT⟩ := hRT
  obtain ⟨ιT', _, LT, hLT⟩ := Gate.slotOracle_const_eq (a := aT) (m := mT) (r := rT)
    (K := KT) (P := PT)
  choose mskT hmskT using hLT
  have hRT' : ∀ x, IsUnitary (prT.eval x) := prT.eval_unitary
    (AdaptiveODELowerBound.Access.callFamily_unitary (SparseLowerBounds.specOracles_unitary ΩT _))
  obtain ⟨pT, herrT, hcT⟩ := exists_approxProgram UJT hUJT DT hDT prT.eval hRT' eT
    heT hprT ιT' LT mskT hmskT gsT hgsT
  obtain ⟨ΩM, _, eM, prM, heM, hprM, hqM⟩ := hRM
  obtain ⟨ιM', _, LM, hLM⟩ := Gate.slotOracle_const_eq (a := aM) (m := mM) (r := rM)
    (K := KM) (P := PM)
  choose mskM hmskM using hLM
  have hRM' : ∀ x, IsUnitary (prM.eval x) := prM.eval_unitary
    (AdaptiveODELowerBound.Access.callFamily_unitary (SparseLowerBounds.specOracles_unitary ΩM _))
  obtain ⟨pM, herrM, hcM⟩ := exists_approxProgram UJM hUJM DM hDM prM.eval hRM' eM
    heM hprM ιM' LM mskM hmskM gsM hgsM
  obtain ⟨ΩP, _, eP, prP, heP, hprP, hqP⟩ := hRP
  obtain ⟨ιP', _, LP, hLP⟩ := Gate.slotOracle_const_eq (a := aP) (m := mP) (r := rP)
    (K := KP) (P := PP)
  choose mskP hmskP using hLP
  have hRP' : ∀ x, IsUnitary (prP.eval x) := prP.eval_unitary
    (AdaptiveODELowerBound.Access.callFamily_unitary (SparseLowerBounds.specOracles_unitary ΩP _))
  obtain ⟨pP, herrP, hcP⟩ := exists_approxProgram UJP hUJP DP hDP prP.eval hRP' eP
    heP hprP ιP' LP mskP hmskP gsP hgsP
  have key := Core.main_max_uniform_weight h (2 * q)
    (realFamily ιT' mskT prT.eval) (realFamily_unitary ιT' mskT hRT')
    (nonempty_realAccess (timeData τ s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) ΩT prT hqT ιT' mskT)
    pT (realEncoding ιT' eT LT ∘L ιT)
      (NativeSparseAttenuation.isometry_comp ιT (realEncoding ιT' eT LT) hιT
        (realEncoding_isometry ιT' heT LT))
    (fun j => (approx_comp_encoding _ _ (realEncoding_isometry ιT' heT LT) _ ιT hιT _
      (herrT j) (hsimT j)).trans (by linarith))
    (realFamily ιM' mskM prM.eval) (realFamily_unitary ιM' mskM hRM')
    (nonempty_realAccess (mixedMainData τ ε s h.s_ge)
      (searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)) ΩM prM hqM ιM' mskM)
    pM (realEncoding ιM' eM LM ∘L ιM)
      (NativeSparseAttenuation.isometry_comp ιM (realEncoding ιM' eM LM) hιM
        (realEncoding_isometry ιM' heM LM))
    (fun j => (approx_comp_encoding _ _ (realEncoding_isometry ιM' heM LM) _ ιM hιM _
      (herrM j) (hsimM j)).trans (by linarith))
    (realFamily ιP' mskP prP.eval) (realFamily_unitary ιP' mskP hRP')
    (nonempty_realAccess (precisionMainData τ ε s h.s_ge)
      (scalarAccess (by have := h.s_ge; omega)) ΩP prP hqP ιP' mskP)
    pP (realEncoding ιP' eP LP ∘L ιP)
      (NativeSparseAttenuation.isometry_comp ιP (realEncoding ιP' eP LP) hιP
        (realEncoding_isometry ιP' heP LP))
    (fun x => (approx_comp_encoding _ _ (realEncoding_isometry ιP' heP LP) _ ιP hιP _
      (herrP x) (hsimP x)).trans (by linarith))
  rw [hcT, hcM, hcP] at key
  push_cast at key
  linarith

/-- **Theorem `hsl:thm:main` for gate-level circuits with private operations realised within
`ξ`, uniform-mesh criterion** (eq. `hsl:eq:main`, max form): as `main_max_gate_tolerant`, for
ideal circuits meeting the uniform-mesh criterion on the constant path at error `ε₀_F`
(`UniformGuarantee`: for every propagator `U` of the path from the identity, error at most `ε₀_F`
against `U(τ)` on an isometric encoding), with `ε₀_F + nPriv_F · ξ_F ≤ ε`,
`c₀ (√s τ + √(sτr) + r) ≤ q · max(nPriv_T, nPriv_M, nPriv_P)`. -/
theorem main_max_gate_uniform_tolerant (h : HSRange τ s ε) (q : ℕ) (ε₀T ε₀M ε₀P ξT ξM ξP : ℝ)
    (aT mT rT KT aM mM rM KM aP mP rP KP : ℕ)
    {PT PM PP : Type*} [NormedAddCommGroup PT] [InnerProductSpace ℂ PT] [CompleteSpace PT]
    [NormedAddCommGroup PM] [InnerProductSpace ℂ PM] [CompleteSpace PM]
    [NormedAddCommGroup PP] [InnerProductSpace ℂ PP] [CompleteSpace PP]
    (UJT : Vsp aT PT →L[ℂ] Vsp aT PT) (hUJT : IsUnitary UJT)
    (DT : (Fin (timeN τ) → Fin (2 ^ hsMu s)) → Vsp aT PT →L[ℂ] Vsp aT PT)
    (hDT : ∀ x, IsUnitary (DT x)) (hRT : ApproxRealization (timeData τ s h.s_ge) DT q ξT)
    (gsT : List (Instr (Wire aT mT rT KT))) (hgsT : ∀ g ∈ gsT, g.Valid Wire.anc)
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ] Reg (Wire aT mT rT KT) PT)
    (hιT : ιT† ∘L ιT = 1)
    (hT : UniformGuarantee (fun j => runT UJT (fun _ => DT j) gsT) ιT
      (constPath (timeData τ s h.s_ge)) τ ε₀T)
    (hbudT : ε₀T + nPriv gsT * ξT ≤ ε)
    (UJM : Vsp aM PM →L[ℂ] Vsp aM PM) (hUJM : IsUnitary UJM)
    (DM : (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → Vsp aM PM →L[ℂ] Vsp aM PM)
    (hDM : ∀ x, IsUnitary (DM x)) (hRM : ApproxRealization (mixedMainData τ ε s h.s_ge) DM q ξM)
    (gsM : List (Instr (Wire aM mM rM KM))) (hgsM : ∀ g ∈ gsM, g.Valid Wire.anc)
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ] Reg (Wire aM mM rM KM) PM)
    (hιM : ιM† ∘L ιM = 1)
    (hM : UniformGuarantee (fun j => runT UJM (fun _ => DM j) gsM) ιM
      (constPath (mixedMainData τ ε s h.s_ge)) τ ε₀M)
    (hbudM : ε₀M + nPriv gsM * ξM ≤ ε)
    (UJP : Vsp aP PP →L[ℂ] Vsp aP PP) (hUJP : IsUnitary UJP)
    (DP : (Fin (precN τ ε) → Bool) → Vsp aP PP →L[ℂ] Vsp aP PP)
    (hDP : ∀ x, IsUnitary (DP x))
    (hRP : ApproxRealization (precisionMainData τ ε s h.s_ge) DP q ξP)
    (gsP : List (Instr (Wire aP mP rP KP))) (hgsP : ∀ g ∈ gsP, g.Valid Wire.anc)
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ] Reg (Wire aP mP rP KP) PP)
    (hιP : ιP† ∘L ιP = 1)
    (hP : UniformGuarantee (fun x => runT UJP (fun _ => DP x) gsP) ιP
      (constPath (precisionMainData τ ε s h.s_ge)) τ ε₀P)
    (hbudP : ε₀P + nPriv gsP * ξP ≤ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      q * max (nPriv gsT : ℝ) (max (nPriv gsM : ℝ) (nPriv gsP)) := by
  have hτ : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  exact main_max_gate_tolerant h q ε₀T ε₀M ε₀P ξT ξM ξP aT mT rT KT aM mM rM KM aP mP rP KP
    UJT hUJT DT hDT hRT gsT hgsT ιT hιT
    ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ _ ιT hτ).1 hT) hbudT
    UJM hUJM DM hDM hRM gsM hgsM ιM hιM
    ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ _ ιM hτ).1 hM) hbudM
    UJP hUJP DP hDP hRP gsP hgsP ιP hιP
    ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ _ ιP hτ).1 hP) hbudP

/-- **The exact form is the case `ξ = 0`** (containment check): the statement of
`Gate.main_max_gate` (natively realised private operations, endpoint error `ε`), derived from
`main_max_gate_tolerant` with `ξ_F = 0` and `ε₀_F = ε` through `approxRealization_zero_iff`. -/
theorem main_max_gate_of_tolerant (h : HSRange τ s ε) (q : ℕ)
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
  exact main_max_gate_tolerant h q ε ε ε 0 0 0 aT mT rT KT aM mM rM KM aP mP rP KP
    UJT hUJT DT hDT ((approxRealization_zero_iff _ _ _).2 hRT) gsT hgsT ιT hιT hsimT (by simp)
    UJM hUJM DM hDM ((approxRealization_zero_iff _ _ _).2 hRM) gsM hgsM ιM hιM hsimM (by simp)
    UJP hUJP DP hDP ((approxRealization_zero_iff _ _ _).2 hRP) gsP hgsP ιP hιP hsimP (by simp)

/-- **The exact uniform-mesh form is the case `ξ = 0`** (containment check): the statement of
`Gate.main_max_gate_uniform` (natively realised private operations, uniform-mesh criterion at
error `ε`), derived from `main_max_gate_uniform_tolerant` with `ξ_F = 0` and `ε₀_F = ε` through
`approxRealization_zero_iff`. -/
theorem main_max_gate_uniform_of_tolerant (h : HSRange τ s ε) (q : ℕ)
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
  exact main_max_gate_uniform_tolerant h q ε ε ε 0 0 0 aT mT rT KT aM mM rM KM aP mP rP KP
    UJT hUJT DT hDT ((approxRealization_zero_iff _ _ _).2 hRT) gsT hgsT ιT hιT hT (by simp)
    UJM hUJM DM hDM ((approxRealization_zero_iff _ _ _).2 hRM) gsM hgsM ιM hιM hM (by simp)
    UJP hUJP DP hDP ((approxRealization_zero_iff _ _ _).2 hRP) gsP hgsP ιP hιP hP (by simp)

end

end TimeDependentLowerBoundExtensions.Tolerant
