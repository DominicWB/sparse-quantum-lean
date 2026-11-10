import ManuscriptConformance.GateODETimeCert
import MeshCertificateODE.Valid

/-!
# Conformance: the time-dependent `ode:thm:gates` with the manuscript's certificates on `ℂ^N`

`ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert` (`GateODETimeCert`) are stated on
the `k`-qubit index register, for the matrix extended by zero to the index words `≥ N`. This module
states their guarantees for a problem on `ℂ^N` itself: generator pieces `G_r(u)` on `ℂ^N` with
their propagator `U`, forcing pieces, the mild solution `x` and the source vectors on `ℂ^N`, with
the certificate conditions on `ℂ^N` and the sample errors against the samples
`matrixOperator (D.matrix (x, r))` of the sparse access, and the loading circuits preparing the
embedded directions `validEmb (x₀ / ‖x₀‖)` and `validEmb (b_r / ‖b_r‖)` on the index register. The
output is the embedding of the normalised solution, `validEmb (x(T)/‖x(T)‖)`, on the index register
with the marker clean.

The protocols and their resource bounds are those of `ode_thm_gates_time_cert`, resp.
`ode_thm_gates_time_decoder_cert` (the same expressions); the proofs apply those theorems to the
lifted problem (`MeshCertificateODE.Valid`: the lifted pieces `validLift ∘ G_r`, the embedded
forcing, solution and source vectors and the lifted propagator `liftV N k U`), whose
certificate-form conditions follow from those on `ℂ^N`: the source scale, the coefficient mass, the
amplitudes and the source error are unchanged, and the integrated sample errors against the lifted
samples are at most those on `ℂ^N`. Formal restrictions as in `GateODETimeCert`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb padLift primsTG validEmb validLift
  norm_validEmb accretive_validLift)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTD)
open SparseHamiltonian.MeshCertificateODE (umesh quadSum quadAmp quadMass sampleErr dissErr liftV)
open SparseHamiltonian.GeneralSourceExtensions (Mesh.meshScale)
open GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

universe u

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates`, time-dependent, with the manuscript's certificates, for a problem on
`ℂ^N`**: the guarantees of `ode_thm_gates_time_cert` (same protocol, whose resource bounds that
theorem gives) for generator pieces, forcing, mild solution, propagator and source vectors on
`ℂ^N`, with the certificates on `ℂ^N` (sample errors against the samples of the sparse access) and
the loading preparing the embedded directions, against the embedding of the solution. -/
theorem ode_thm_gates_time_cert_valid {X : Type u} {N s k b : ℕ} (bd : ℕ)
    (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b)
    (hm : odeMeshG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε ≤ m) (hk : 2 ^ k < 2 * N)
    (hF : formal_binaryDecoder D c0) (hbits : comp_bits b bd [c0, T, etaH, etaD])
    (hg : formal_gbarOne gbar) {Zs : Type} [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (x : X)
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
    (hload : ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs)
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
    (hbud : ζ + 2 * (sampleErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) +
      2 * dissErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r)))) ≤ ε / (2000 * gbar))
    (hbranch : 6 * TimeDependentODE.radius (2 * gbar) ε * dissErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    HeraldedOutput (nprotocol ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep
        N (fun _ => false) loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
      (primsTG D x) (ODEStateNormalization.unitDirection
        (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))) ε ∧
    ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
        (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T (2 * gbar) ε m).prep N
          (fun _ => false) loadC wpC) j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
            (nrun (primsTG D x) (trialN ((odePubTG k s D.s_le_pow b c0 etaH etaD T
              (2 * gbar) ε m).prep N (fun _ => false) loadC wpC) j) sN)) -
          ODEStateNormalization.unitDirection
            (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))‖ ≤ ε := by
  obtain ⟨C, -, h⟩ := ode_thm_gates_time_cert.{u}
  have hN : N ≤ 2 ^ k := D.hN
  have hg1 : 1 ≤ gbar := hg
  have hε1 : ε ≤ 1 := by linarith
  have hmesh := MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)
  have hS := MeshCertificateODE.sampleErr_padLift_le D x hmesh G hreg
  have hDS := MeshCertificateODE.dissErr_padLift_le D x hmesh G hreg
  have hR0 : 0 ≤ TimeDependentODE.radius (2 * gbar) ε :=
    ImprovedODEQueryBudget.radius_nonneg (2 * (2 * gbar)) (ε / 2) (by linarith) (by linarith)
      (by linarith)
  have hWp' : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (validEmb N k (sol 0)) (fun r => validEmb N k (bs r)) (w 0, Fin.tail w) :
        ℝ) : ℂ) := fun w => by
    rw [MeshCertificateODE.quadAmp_validEmb hN]
    exact hWp w
  have hinit' : validEmb N k (sol 0) ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)) :=
    fun h0 => hinit fun h1 => h0 (by rw [h1, map_zero])
  have hforce' : ∀ w : Fin m → Bool, validEmb N k (bs (wordValue w)) ≠ 0 →
      Jl (true, w) (seedV (S := Fin k)) =
        ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))) :=
    fun w hw => hforce w fun h1 => hw (by rw [h1, map_zero])
  have hacc'' : ∀ r : Fin (2 ^ m),
      ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
        TimeDependentODE.Accretive (validLift N k (G r u)) :=
    fun r u hu => accretive_validLift hN (hacc' r u hu)
  have hscale' : Mesh.meshScale (fun u => validEmb N k (sol u)) (fun r u => validEmb N k (bf r u))
      (umesh T (2 ^ m)) ≤ gbar * ‖validEmb N k (sol T)‖ := by
    rw [MeshCertificateODE.meshScale_validEmb hN, norm_validEmb hN]
    exact hscale
  have hmass' : quadMass T m (validEmb N k (sol 0)) (fun r => validEmb N k (bs r)) ≤
      2 * Mesh.meshScale (fun u => validEmb N k (sol u)) (fun r u => validEmb N k (bf r u))
        (umesh T (2 ^ m)) := by
    rw [MeshCertificateODE.quadMass_validEmb hN, MeshCertificateODE.meshScale_validEmb hN]
    exact hmass
  have hsrc' : ‖validEmb N k (sol T) - quadSum T (2 ^ m) (liftV N k U) (validEmb N k (sol 0))
      (fun r => validEmb N k (bs r))‖ ≤ ζ * Mesh.meshScale (fun u => validEmb N k (sol u))
        (fun r u => validEmb N k (bf r u)) (umesh T (2 ^ m)) := by
    rw [MeshCertificateODE.quadSum_liftV hN, ← map_sub, norm_validEmb hN,
      MeshCertificateODE.meshScale_validEmb hN]
    exact hsrc
  have hbud' : ζ + 2 * (sampleErr (umesh T (2 ^ m)) (fun r u => validLift N k (G r u))
      (fun r => padLift D (x, r)) + 2 * dissErr (umesh T (2 ^ m))
        (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r))) ≤ ε / (2000 * gbar) := by
    linarith
  have hbranch' : 6 * TimeDependentODE.radius (2 * gbar) ε * dissErr (umesh T (2 ^ m))
      (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r)) ≤
        TimeDependentODE.precision (2 * gbar) ε := by
    have := mul_le_mul_of_nonneg_left hDS
      (by linarith : (0 : ℝ) ≤ 6 * TimeDependentODE.radius (2 * gbar) ε)
    linarith
  exact (h bd c0 etaH etaD T gbar ε m D hm hk hF hbits hg loadC wpC hloadV hwpV hH hD hT hε
    hε2).2.2.2.2 x hrH hcH hrD hcD Jl Wp (fun r u => validLift N k (G r u))
    (fun r u => validEmb N k (bf r u)) (fun u => validEmb N k (sol u))
    (fun r => validEmb N k (bs r)) (liftV N k U) ζ ζs hζs0 hload hwp hacc hJl hWl hWr hWp' hinit'
    hforce' hacc'' (MeshCertificateODE.regular_validLift hreg)
    (MeshCertificateODE.mild_liftV hN hmild) (MeshCertificateODE.isMeshPropagator_liftV hN hprop)
    (MeshCertificateODE.validEmb_ne_zero hN hne) hscale' hmass' hsrc' hbud' hbranch'

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:gates` for sparse access of general size with binary entry decoding,
time-dependent, with the manuscript's certificates, for a problem on `ℂ^N`**: the guarantees of
`ode_thm_gates_time_decoder_cert` (same protocol, whose resource bounds that theorem gives) for a
problem on `ℂ^N`, as in `ode_thm_gates_time_cert_valid`. -/
theorem ode_thm_gates_time_decoder_cert_valid {X : Type u} {N s k b b' A : ℕ} (bd : ℕ)
    (c0 etaH etaD T gbar ε : ℝ) (m : ℕ) (D : GeneralSparseAccess.QData (X × Fin (2 ^ m)) N s k b)
    (dc : BinDecode b b' A) (hm : odeMeshG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε ≤ m)
    (hk : 2 ^ k < 2 * N) (hF : BinaryEntryDecoding D dc c0)
    (hbits : comp_bits b' bd [c0, T, etaH, etaD]) (hg : formal_gbarOne gbar) {Zs : Type}
    [Fintype Zs] [DecidableEq Zs]
    (loadC : List (NInstr ((Fin (m + 1) ⊕ Fin k) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (wpC : List (NInstr (Fin (m + 1) ⊕ Zs) (Fin m ⊕ PY k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid) (hwpV : ∀ i ∈ wpC, i.Valid)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (x : X)
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
    (hload : ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs)
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
    (hbud : ζ + 2 * (sampleErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) +
      2 * dissErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r)))) ≤ ε / (2000 * gbar))
    (hbranch : 6 * TimeDependentODE.radius (2 * gbar) ε * dissErr (umesh T (2 ^ m)) G
        (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) ≤
      TimeDependentODE.precision (2 * gbar) ε) :
    HeraldedOutput (nprotocol (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar)
        ε m) N dc loadC wpC) (2 * (2 * gbar)) (one_le_two_mul (one_le_two_mul hg)))
      (primsTG D x) (ODEStateNormalization.unitDirection
        (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))) ε ∧
    ∀ j : ℕ, ((goodN)†) (nrun (primsTG D x)
        (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T (2 * gbar) ε m) N dc
          loadC wpC) j) sN) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection (((goodN)†)
            (nrun (primsTG D x) (trialN (prepTD (odePubTG k s D.s_le_pow b' c0 etaH etaD T
              (2 * gbar) ε m) N dc loadC wpC) j) sN)) -
          ODEStateNormalization.unitDirection
            (cleanAlong (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) (validEmb N k (sol T)))‖ ≤ ε := by
  obtain ⟨C, -, h⟩ := ode_thm_gates_time_decoder_cert.{u}
  have hN : N ≤ 2 ^ k := D.hN
  have hg1 : 1 ≤ gbar := hg
  have hε1 : ε ≤ 1 := by linarith
  have hmesh := MeshCertificateODE.isMesh_umesh hT (Nat.two_pow_pos m)
  have hS := MeshCertificateODE.sampleErr_padLift_le D x hmesh G hreg
  have hDS := MeshCertificateODE.dissErr_padLift_le D x hmesh G hreg
  have hR0 : 0 ≤ TimeDependentODE.radius (2 * gbar) ε :=
    ImprovedODEQueryBudget.radius_nonneg (2 * (2 * gbar)) (ε / 2) (by linarith) (by linarith)
      (by linarith)
  have hWp' : ∀ w : Cfg (Fin (m + 1)), Wp w (fun _ => false) =
      ((quadAmp T m (validEmb N k (sol 0)) (fun r => validEmb N k (bs r)) (w 0, Fin.tail w) :
        ℝ) : ℂ) := fun w => by
    rw [MeshCertificateODE.quadAmp_validEmb hN]
    exact hWp w
  have hinit' : validEmb N k (sol 0) ≠ 0 → Jl (false, fun _ => false) (seedV (S := Fin k)) =
      ODEStateNormalization.unitDirection (validEmb N k (sol 0)) :=
    fun h0 => hinit fun h1 => h0 (by rw [h1, map_zero])
  have hforce' : ∀ w : Fin m → Bool, validEmb N k (bs (wordValue w)) ≠ 0 →
      Jl (true, w) (seedV (S := Fin k)) =
        ODEStateNormalization.unitDirection (validEmb N k (bs (wordValue w))) :=
    fun w hw => hforce w fun h1 => hw (by rw [h1, map_zero])
  have hacc'' : ∀ r : Fin (2 ^ m),
      ∀ u ∈ Set.Icc (umesh T (2 ^ m) r) (umesh T (2 ^ m) ((r : ℕ) + 1)),
        TimeDependentODE.Accretive (validLift N k (G r u)) :=
    fun r u hu => accretive_validLift hN (hacc' r u hu)
  have hscale' : Mesh.meshScale (fun u => validEmb N k (sol u)) (fun r u => validEmb N k (bf r u))
      (umesh T (2 ^ m)) ≤ gbar * ‖validEmb N k (sol T)‖ := by
    rw [MeshCertificateODE.meshScale_validEmb hN, norm_validEmb hN]
    exact hscale
  have hmass' : quadMass T m (validEmb N k (sol 0)) (fun r => validEmb N k (bs r)) ≤
      2 * Mesh.meshScale (fun u => validEmb N k (sol u)) (fun r u => validEmb N k (bf r u))
        (umesh T (2 ^ m)) := by
    rw [MeshCertificateODE.quadMass_validEmb hN, MeshCertificateODE.meshScale_validEmb hN]
    exact hmass
  have hsrc' : ‖validEmb N k (sol T) - quadSum T (2 ^ m) (liftV N k U) (validEmb N k (sol 0))
      (fun r => validEmb N k (bs r))‖ ≤ ζ * Mesh.meshScale (fun u => validEmb N k (sol u))
        (fun r u => validEmb N k (bf r u)) (umesh T (2 ^ m)) := by
    rw [MeshCertificateODE.quadSum_liftV hN, ← map_sub, norm_validEmb hN,
      MeshCertificateODE.meshScale_validEmb hN]
    exact hsrc
  have hbud' : ζ + 2 * (sampleErr (umesh T (2 ^ m)) (fun r u => validLift N k (G r u))
      (fun r => padLift D (x, r)) + 2 * dissErr (umesh T (2 ^ m))
        (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r))) ≤ ε / (2000 * gbar) := by
    linarith
  have hbranch' : 6 * TimeDependentODE.radius (2 * gbar) ε * dissErr (umesh T (2 ^ m))
      (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r)) ≤
        TimeDependentODE.precision (2 * gbar) ε := by
    have := mul_le_mul_of_nonneg_left hDS
      (by linarith : (0 : ℝ) ≤ 6 * TimeDependentODE.radius (2 * gbar) ε)
    linarith
  exact (h bd c0 etaH etaD T gbar ε m D dc hm hk hF hbits hg loadC wpC hloadV hwpV hH hD hT hε
    hε2).2.2.2.2 x hrH hcH hrD hcD Jl Wp (fun r u => validLift N k (G r u))
    (fun r u => validEmb N k (bf r u)) (fun u => validEmb N k (sol u))
    (fun r => validEmb N k (bs r)) (liftV N k U) ζ ζs hζs0 hload hwp hacc hJl hWl hWr hWp' hinit'
    hforce' hacc'' (MeshCertificateODE.regular_validLift hreg)
    (MeshCertificateODE.mild_liftV hN hmild) (MeshCertificateODE.isMeshPropagator_liftV hN hprop)
    (MeshCertificateODE.validEmb_ne_zero hN hne) hscale' hmass' hsrc' hbud' hbranch'

end

end ManuscriptConformance
