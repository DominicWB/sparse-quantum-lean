import ManuscriptConformance.WriterDecoderCert
import ManuscriptConformance.WriterODECert
import ManuscriptConformance.BranchCertificates

/-!
# Conformance: the branch-certificate forms of the time-dependent `ode:thm:gates` with a writer

The branch-certificate forms `ode_thm_gates_time_cert_branch`,
`ode_thm_gates_time_decoder_cert_branch`, `ode_thm_gates_time_cert_valid_branch` and
`ode_thm_gates_time_decoder_cert_valid_branch` (`BranchCertificates`) derive the certificate
endpoints' sample budgets from budgets on the integrated branch errors
(`gate_budgets_of_branch`). Their writer forms (handover item B4) apply the same derivation to the
writer forms `ode_thm_gates_time_cert_writer`, `ode_thm_gates_time_decoder_cert_writer`,
`ode_thm_gates_time_cert_valid_writer` and `ode_thm_gates_time_decoder_cert_valid_writer`: the
same protocols, bounds and guarantees, for every writer of the stored words of every sample
specified on the clean inputs of the valid index pairs only.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section

universe u v w

/-! ### The time-dependent Theorem `ode:thm:gates` from branch certificates with a writer -/

section Gates

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb padLift primsTG primsTGW validEmb validLift
  norm_validEmb accretive_validLift)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTDW)
open SparseHamiltonian.GateBinaryODETime (PubT)
open SparseHamiltonian.ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open SparseHamiltonian.MeshCertificateODE (umesh quadSum quadAmp quadMass sampleErr dissErr liftV)
open SparseHamiltonian.GeneralSourceExtensions (Mesh.meshScale)
open GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:gates` (time-dependent, manuscript certificates) from branch certificates
with a writer** (handover item B4): the protocol and bounds of `ode_thm_gates_time_cert_writer`
(fixed before the writer and the instance), with the sample budgets on the branch errors as in
`ode_thm_gates_time_cert_branch`, for the coherent sampled-time primitives `primsTGW Wr x` of
every writer `Wr` of the stored words of every sample on valid clean inputs. -/
theorem ode_thm_gates_time_cert_branch_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b),
        odeMeshG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → formal_binaryDecoder D c0 → comp_bits b bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N
            (fun _ => false) loadC wpC) j, i.Valid) ∧
          ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N
              (fun _ => false) loadC wpC) (2 * (2 * gbar))
              (one_le_two_mul (one_le_two_mul hg))).worstCost wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTG (odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m) Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs ∧
          (∀ c : Query → Bool,
            ((nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N
              (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg))).worstCost (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (bf : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ) (sol : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (ζ ζs kb : ℝ),
            0 < kb → 0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            (∀ c, OracleCircuit.IsUnitary (Jl c)) → Wp.conjTranspose * Wp = 1 →
            Wp * Wp.conjTranspose = 1 →
            (∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
              ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)) →
            (sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (sol 0)) →
            (∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (bs (wordValue w))) →
            (∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
              TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G →
            RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U →
            formal_classicalPropagator G (umesh T (2 ^ m)) T U →
            sol T ≠ 0 →
            Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖ →
            quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤ ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ζ + 2 * ((1 + 3 / kb) *
                branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / 2) ≤
              ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (2 * gbar) ε *
                (branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / (2 * kb)) ≤
              TimeDependentODE.precision (2 * gbar) ε →
            HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε
                m).prepW N (fun _ => false) loadC wpC) (2 * (2 * gbar))
                (one_le_two_mul (one_le_two_mul hg)))
              (primsTGW Wr x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
                (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N
                  (fun _ => false) loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTGW Wr x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T
                      (2 * gbar) ε m).prepW N (fun _ => false) loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))‖ ≤ ε := by
  obtain ⟨C, hC, h⟩ := ode_thm_gates_time_cert_writer.{u}
  refine ⟨C, hC, ?_⟩
  intro X N s k b bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg Zs _ _ loadC wpC hloadV hwpV hH
    hD hT hε hε2
  obtain ⟨h1, h2, h3, h4, h5⟩ := h bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg loadC wpC hloadV
      hwpV hH hD hT
    hε hε2
  refine ⟨h1, h2, h3, h4, fun Wr x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs kb hkb hζs hload hwp
      hacc hJl hWl hWr hWp
    hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc hbB hbrB => ?_⟩
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G (fun r => padLift D (x, r)) hreg
    hg hε hε2 hkb hbB hbrB
  exact h5 Wr x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs hload hwp hacc hJl hWl hWr hWp hinit
    hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:gates` (time-dependent, binary entry decoder, manuscript certificates) from
branch certificates with a writer**: the protocol and bounds of
`ode_thm_gates_time_decoder_cert_writer`, with the sample budgets on the branch errors as in
`ode_thm_gates_time_cert_branch`, for every writer of the stored words of every sample on valid
clean inputs. -/
theorem ode_thm_gates_time_decoder_cert_branch_writer :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {N s k b b' A : ℕ} (bd : ℕ) (c0 etaH etaD T gbar ε : ℝ) (m : ℕ)
        (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b) (dc : BinDecode b b' A),
        odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m →
        2 ^ k < 2 * N → BinaryEntryDecoding D dc c0 → comp_bits b' bd [c0, T, etaH, etaD] →
        ∀ (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
          (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
          (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query)),
          (∀ i ∈ loadC, i.Valid) → (∀ i ∈ wpC, i.Valid) →
          0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
          (∀ j, ∀ i ∈ trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N
            dc loadC wpC) j, i.Valid) ∧
          ((nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                wGateN : ℝ) ≤
            C * gbar * (odeShape s T etaH etaD gbar ε *
                ((bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
                  dc.cost) +
              ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
          (odeQubitsTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) dc Zs : ℝ) ≤
            C * (bitB bd N (2 ^ m) (2 ^ m) (odeShape s T etaH etaD gbar ε) gbar ε + 1) ^ 3 +
              C * Fintype.card Zs + C * dc.wires ∧
          (∀ c : Query → Bool,
            ((nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
              loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg))).worstCost
                (wCallN c) : ℝ) ≤
            (if T = 0 ∨ etaH + etaD = 0 then 0 else
              C * gbar * odeShape s T etaH etaD gbar ε *
                ((if c Query.rowLocation then 1 else 0) +
                  (if c Query.columnLocation then 1 else 0) + (if c Query.value then 1 else 0))) +
            C * gbar * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
          ∀ (Wr : GeneralSparseAccess.QData.Writer D) (x : X),
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaH ^ 2) →
            (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤
              etaD ^ 2) →
            ∀ (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
              (G : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
              (bf : Fin (2 ^ m) → ℝ → Reg (Fin k) ℂ) (sol : ℝ → Reg (Fin k) ℂ)
              (bs : ℕ → Reg (Fin k) ℂ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (ζ ζs kb : ℝ),
            0 < kb → 0 ≤ ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs →
            ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs →
            ζs ≤ ImprovedODEQueryBudget.precision gbar ε →
            (∀ c, OracleCircuit.IsUnitary (Jl c)) → Wp.conjTranspose * Wp = 1 →
            Wp * Wp.conjTranspose = 1 →
            (∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
              ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)) →
            (sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (sol 0)) →
            (∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
              ODEStateNormalization.unitDirection (bs (wordValue w))) →
            (∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
              TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G →
            RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U →
            formal_classicalPropagator G (umesh T (2 ^ m)) T U →
            sol T ≠ 0 →
            Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖ →
            quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤ ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)) →
            ζ + 2 * ((1 + 3 / kb) *
                branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / 2) ≤
              ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (2 * gbar) ε *
                (branchSum (umesh T (2 ^ m)) G (fun r => padLift D (x, r)) kb / (2 * kb)) ≤
              TimeDependentODE.precision (2 * gbar) ε →
            HeraldedOutput (nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
                ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
              (primsTGW Wr x) (ODEStateNormalization.unitDirection
                (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))) ε ∧
            ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
                (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
                  loadC wpC) j) sN) ≠ 0 →
              ∃ ω : ℂ, ‖ω‖ = 1 ∧
                ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
                    (nrun (primsTGW Wr x) (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD
                      T                       (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
                  ODEStateNormalization.unitDirection
                    (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (sol T))‖ ≤ ε := by
  obtain ⟨C, hC, h⟩ := ode_thm_gates_time_decoder_cert_writer.{u}
  refine ⟨C, hC, ?_⟩
  intro X N s k b b' A bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg Zs _ _ loadC wpC hloadV
    hwpV hH hD hT hε hε2
  obtain ⟨h1, h2, h3, h4, h5⟩ := h bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg loadC wpC
      hloadV hwpV hH hD hT
    hε hε2
  refine ⟨h1, h2, h3, h4, fun Wr x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs kb hkb hζs hload hwp
      hacc hJl hWl hWr hWp
    hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc hbB hbrB => ?_⟩
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G (fun r => padLift D (x, r)) hreg
    hg hε hε2 hkb hbB hbrB
  exact h5 Wr x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs hload hwp hacc hJl hWl hWr hWp hinit
    hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

set_option maxHeartbeats 16000000 in
/-- **`ode_thm_gates_time_cert_valid_writer` from branch certificates** (problems on `ℂ^N`, a
writer): the protocol and conclusions of `ode_thm_gates_time_cert_valid_writer`, with the sample
budgets on the branch errors as in `ode_thm_gates_time_cert_valid_branch`. -/
theorem ode_thm_gates_time_cert_valid_branch_writer {X : Type u} {N s k b : ℕ} (bd : ℕ)
    (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b)
    (hm : odeMeshG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε ≤ m) (hk : 2 ^ k < 2 * N)
    (hF : formal_binaryDecoder D c0) (hbits : comp_bits b bd [c0, T, etaH, etaD])
    (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (Wr : GeneralSparseAccess.QData.Writer D) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
    (G : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (bf : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N)) (sol : ℝ → EuclideanSpace ℂ (Fin N))
    (bs : ℕ → EuclideanSpace ℂ (Fin N))
    (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)) (ζ ζs : ℝ) (hζs0 : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs)
    (hacc : ζs ≤ ImprovedODEQueryBudget.precision gbar ε)
    (hJl : ∀ c, OracleCircuit.IsUnitary (Jl c)) (hWl : Wp.conjTranspose * Wp = 1)
    (hWr : Wp * Wp.conjTranspose = 1)
    (hWp : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ))
    (hinit : sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)))
    (hforce : ∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))))
    (hacc' : ∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
      TimeDependentODE.Accretive (G r u))
    (hreg : RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G)
    (hmild : RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U)
    (hprop : formal_classicalPropagator G (umesh T (2 ^ m)) T U) (hne : sol T ≠ 0)
    (hscale : Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖)
    (hmass : quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (hsrc : ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤
      ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (kb : ℝ) (hkb : 0 < kb)
    (hbudB : ζ + 2 * ((1 + 3 / kb) * branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / 2) ≤
      ε / (2000 * gbar))
    (hbranchB : 6 * TimeDependentODE.radius (2 * gbar) ε * (branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / (2 * kb)) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW
        N (fun _ => false) loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
      (primsTGW Wr x) (ODEStateNormalization.unitDirection
        (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))) ε ∧
    ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
        (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prepW N
          (fun _ => false) loadC wpC) j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
            (nrun (primsTGW Wr x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T
              (2 * gbar) ε m).prepW N (fun _ => false) loadC wpC) j) sN)) -
          ODEStateNormalization.unitDirection
            (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))‖ ≤ ε := by
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G
    (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) hreg hg hε hε2 hkb hbudB hbranchB
  exact ode_thm_gates_time_cert_valid_writer bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg loadC
    wpC hloadV hwpV hH hD hT hε hε2 Wr x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs0 hload hwp
    hacc hJl
    hWl hWr hWp hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

set_option maxHeartbeats 16000000 in
/-- **`ode_thm_gates_time_decoder_cert_valid_writer` from branch certificates** (problems on
`ℂ^N`, binary entry decoder, a writer). -/
theorem ode_thm_gates_time_decoder_cert_valid_branch_writer {X : Type u} {N s k b b' A : ℕ} (bd : ℕ)
    (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b)
    (dc : BinDecode b b' A) (hm : odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m)
    (hk : 2 ^ k < 2 * N) (hF : BinaryEntryDecoding D dc c0)
    (hbits : comp_bits b' bd [c0, T, etaH, etaD]) (hg : formal_gbarOne gbar) {Zs : Type}
    [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (Wr : GeneralSparseAccess.QData.Writer D) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ etaD ^ 2)
    (Jl : Bool × (Fin m → Bool) → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (Wp : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ)
    (G : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (bf : Fin (2 ^ m) → ℝ → EuclideanSpace ℂ (Fin N)) (sol : ℝ → EuclideanSpace ℂ (Fin N))
    (bs : ℕ → EuclideanSpace ℂ (Fin N))
    (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)) (ζ ζs : ℝ) (hζs0 : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTGW Wr x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTGW Wr x) wpC) (liftB (matOp Wp)) ζs)
    (hacc : ζs ≤ ImprovedODEQueryBudget.precision gbar ε)
    (hJl : ∀ c, OracleCircuit.IsUnitary (Jl c)) (hWl : Wp.conjTranspose * Wp = 1)
    (hWr : Wp * Wp.conjTranspose = 1)
    (hWp : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ))
    (hinit : sol 0 ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)))
    (hforce : ∀ w : Fin m → Bool, bs (wordValue w) ≠ 0 → Jl (true, w) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))))
    (hacc' : ∀ r : Fin (2 ^ m), ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
      TimeDependentODE.Accretive (G r u))
    (hreg : RepresentedSampleODE.RegularPieces (umesh T (2 ^ m)) G)
    (hmild : RepresentedSampleODE.MildSolution (umesh T (2 ^ m)) T bf sol U)
    (hprop : formal_classicalPropagator G (umesh T (2 ^ m)) T U) (hne : sol T ≠ 0)
    (hscale : Mesh.meshScale sol bf (umesh T (2 ^ m)) ≤ gbar * ‖sol T‖)
    (hmass : quadMass T m (sol 0) bs ≤ 2 * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (hsrc : ‖sol T - quadSum T (2 ^ m) U (sol 0) bs‖ ≤
      ζ * Mesh.meshScale sol bf (umesh T (2 ^ m)))
    (kb : ℝ) (hkb : 0 < kb)
    (hbudB : ζ + 2 * ((1 + 3 / kb) * branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / 2) ≤
      ε / (2000 * gbar))
    (hbranchB : 6 * TimeDependentODE.radius (2 * gbar) ε * (branchSum (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) kb / (2 * kb)) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    HeraldedOutput (nprotocol (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
        ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
      (primsTGW Wr x) (ODEStateNormalization.unitDirection
        (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))) ε ∧
    ∀ j : ℕ, ((goodN)†) (nrun (primsTGW Wr x)
        (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
          loadC wpC) j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
            (nrun (primsTGW Wr x) (trialN (prepTDW (odePubTG k s D.s_le_pow b' c0 etaH etaD T
              (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
          ODEStateNormalization.unitDirection
            (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))‖ ≤ ε := by
  obtain ⟨c1, c2⟩ := gate_budgets_of_branch
    (MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)) G
    (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) hreg hg hε hε2 hkb hbudB hbranchB
  exact ode_thm_gates_time_decoder_cert_valid_writer bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits
    hg loadC wpC hloadV hwpV hH hD hT hε hε2 Wr x hrH hcH hrD hcD Jl Wp G bf sol bs U ζ ζs hζs0
    hload hwp hacc hJl hWl hWr hWp hinit hforce hacc' hreg hmild hprop hne hscale hmass hsrc c1 c2

end Gates

end

end ManuscriptConformance
