import MeshCertificateODE.Native
import RepresentedSampleODE.Gate.Binary

/-!
# The certificate-form instance conditions for time-indexed binary data

For the time-dependent gate solver from time-indexed binary sparse data
(`GateBinaryODETime.PubT`), the samples of the generator are the lifted samples
`M̂_r = mLift D en (x, r)` on the system register. `CertRest` collects the certificate-form
conditions that do not concern the selection (the conditions of `CertInstanceOK` with the sample
certificates stated against `M̂_r`):

* `cert_instanceOK`: with the released row and column energy bounds of every sample, they give
  `CertInstanceOK` for the released oracles (`PubT.selectHyp`);
* `cert_tzInstanceOK`: they give the zero-case conditions `CertTZInstanceOK`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory OracleCircuit GateCircuit GateNative GateBinary
  GateBinaryODE
open GateBinaryODETime (PubT HsT LsT HsT_of_lt LsT_of_lt gensT_eq privFamT)
open ZeroTimeGateODE (BTPublicOK0)
open GateODE.Time (TParams TOracles gens)
open GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open SparseHamiltonian.TimeDependentODE (Accretive)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (IsMeshPropagator meshScale)
open scoped InnerProduct BigOperators

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The certificate-form remaining instance conditions** for time-indexed binary data: those of
`CertInstanceOK` that do not concern the selection, with the sample certificates stated against
the lifted samples `M̂_r = mLift D en (x, r)` of the slots. -/
structure CertRest (q : PubT) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ) (sol : ℝ → Reg (Fin q.kx) ℂ)
    (U : ℝ → Reg (Fin q.kx) ℂ → ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ)
    (gb cq ζ : ℝ) : Prop where
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) = ((q.params.srcAmp (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : sol 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.kx)) = unitDirection (sol 0)
  forcing_load : ∀ w : Fin q.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.kx)) = unitDirection (bs (wordValue w))
  accretive : ∀ r : Fin (2 ^ q.m),
    ∀ u ∈ Icc (umesh q.T (2 ^ q.m) r) (umesh q.T (2 ^ q.m) ((r : ℕ) + 1)), Accretive (G r u)
  regular : RepresentedSampleODE.RegularPieces (umesh q.T (2 ^ q.m)) G
  propagator : IsMeshPropagator G (umesh q.T (2 ^ q.m)) q.T U
  target_ne : sol q.T ≠ 0
  gb_pos : 0 < gb
  cq_nonneg : 0 ≤ cq
  scale : meshScale sol bf (umesh q.T (2 ^ q.m)) ≤ gb * ‖sol q.T‖
  mass : q.params.mass (sol 0) bs ≤ cq * meshScale sol bf (umesh q.T (2 ^ q.m))
  ratio : cq * gb ≤ q.g
  source : ‖sol q.T - quadSum q.T (2 ^ q.m) U (sol 0) bs‖ ≤
    ζ * meshScale sol bf (umesh q.T (2 ^ q.m))
  budget : ζ + cq * (sampleErr (umesh q.T (2 ^ q.m)) G (fun r => mLift D en (x, r)) +
    2 * dissErr (umesh q.T (2 ^ q.m)) G (fun r => mLift D en (x, r))) ≤ q.ε / (2000 * gb)
  branch : 6 * q.params.R * dissErr (umesh q.T (2 ^ q.m)) G (fun r => mLift D en (x, r)) ≤
    q.params.nu

/-- The slot generators of the released oracles are the lifted samples. -/
theorem gens_HsT_LsT (q : PubT) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n) (x : X) :
    (fun r : Fin (2 ^ q.m) => gens (HsT D en x) (LsT D en x) r) =
      fun r => mLift D en (x, r) := by
  funext r
  exact gensT_eq D en x r r.isLt

/-- **The certificate-form instance conditions** of the released time-dependent solver from the
energy bounds of every sample and `CertRest` (no accretivity of the samples). -/
theorem cert_instanceOK (q : PubT) (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ) (sol : ℝ → Reg (Fin q.kx) ℂ)
    (U : ℝ → Reg (Fin q.kx) ℂ → ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ)
    (gb cq ζ : ℝ) (hR : CertRest q D en x Jl Wp G bf sol U bs gb cq ζ) :
    CertInstanceOK q.params (seedV (S := Fin q.kx))
      (⟨UJop (R := ℂ) q.UJg, privFamT q.params D en x q.rho q.γ, Jl, Wp⟩ :
        TOracles q.params.a q.params.m q.params.l (Reg (Fin q.kx) ℂ))
      (HsT D en x) (LsT D en x) G bf sol U bs gb cq ζ where
  select := q.selectHyp hq D en hrange x hrH hcH hrD hcD Jl Wp
  load_unitary := hR.load_unitary
  prep_left := hR.prep_left
  prep_right := hR.prep_right
  prep := hR.prep
  init_load := hR.init_load
  forcing_load := hR.forcing_load
  accretive := hR.accretive
  regular := hR.regular
  propagator := hR.propagator
  target_ne := hR.target_ne
  gb_pos := hR.gb_pos
  cq_nonneg := hR.cq_nonneg
  scale := hR.scale
  mass := hR.mass
  ratio := hR.ratio
  source := hR.source
  budget := by
    have e : (fun r : Fin q.params.M => gens (HsT D en x) (LsT D en x) r) =
        fun r => mLift D en (x, r) := gens_HsT_LsT q D en x
    rw [e]
    exact hR.budget
  branch := by
    have e : (fun r : Fin q.params.M => gens (HsT D en x) (LsT D en x) r) =
        fun r => mLift D en (x, r) := gens_HsT_LsT q D en x
    rw [e]
    exact hR.branch

/-- **The zero-case certificate-form instance conditions** from the energy bounds of every sample
and `CertRest`. -/
theorem cert_tzInstanceOK (q : PubT) (hq : BTPublicOK0 q)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
    (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.kx) ℂ) (sol : ℝ → Reg (Fin q.kx) ℂ)
    (U : ℝ → Reg (Fin q.kx) ℂ → ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ)
    (gb cq ζ : ℝ) (hR : CertRest q D en x Jl Wp G bf sol U bs gb cq ζ) :
    CertTZInstanceOK q.params (seedV (S := Fin q.kx)) Jl Wp (HsT D en x) (LsT D en x) G bf sol U
      bs gb cq ζ := by
  have hselfH : ∀ r < q.params.M, star (HsT D en x r) = HsT D en x r := by
    intro r hr
    rw [HsT_of_lt D en x r hr]
    unfold hLift
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)]
  have hnormH : ∀ r < q.params.M, ‖HsT D en x r‖ ≤ q.params.lamH := by
    intro r hr
    rw [HsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.hamiltonianPart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.hamiltonianPart_apply, hij, hji]) q.etaH
      hq.etaH_nonneg (hrH _) (hcH _)).trans
        (ZeroTimeGateODE.sqrt_le_lam0 q hq.γ_pos hq.γ_le q.etaH hq.etaH_nonneg))
  have hnormL : ∀ r < q.params.M, ‖LsT D en x r‖ ≤ q.params.lamD := by
    intro r hr
    rw [LsT_of_lt D en x r hr]
    exact (norm_qlift_le _ _).trans ((norm_matrixOperator_le D (x, ⟨r, hr⟩) _
      (ODEMatrixEnergy.dissipativePart_isHermitian _)
      (fun i j hij hji => by simp [ODEMatrixEnergy.dissipativePart_apply, hij, hji]) q.etaD
      hq.etaD_nonneg (hrD _) (hcD _)).trans
        (ZeroTimeGateODE.sqrt_le_lam0 q hq.γ_pos hq.γ_le q.etaD hq.etaD_nonneg))
  refine ⟨hselfH, hnormH, hnormL, hR.load_unitary, hR.prep_left, hR.prep_right, hR.prep,
    hR.init_load, hR.forcing_load, hR.accretive, hR.regular, hR.propagator, hR.target_ne,
    hR.gb_pos, hR.cq_nonneg, hR.scale, hR.mass, hR.ratio, hR.source, ?_⟩
  have e : (fun r : Fin q.params.M => gens (HsT D en x) (LsT D en x) r) =
      fun r => mLift D en (x, r) := gens_HsT_LsT q D en x
  rw [e]
  exact hR.budget

end

end SparseHamiltonian.MeshCertificateODE
