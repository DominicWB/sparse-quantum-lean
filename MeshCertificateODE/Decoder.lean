import MeshCertificateODE.General
import GeneralDecoderODE.Decoder

/-!
# The time-dependent decoder solver under the manuscript's certificates

For sparse access of general size with a decoder `val` that has an exact binary entry decoding
`dc` (`GeneralDecoderODE`), the time-dependent solver runs on the decoded data, which has the
matrix of the access, and calls the supplied oracles through the decoding circuit
(`GeneralDecoderODE.prepTD`). The certificate-form conditions `CertRestG` depend on the access only
through the lifts of its matrix:

* `certRestG_decData`: they carry over to the decoded data;
* `decoder_time_cert_outcome`: the guarantees of `nprotocol (prepTD q N dc loadC wpC) (2g)` for the
  coherent sampled-time supplied oracles `primsTG D x`, against the marker embedding of `x(T)`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (GPubT markEmb primsTG)
open SparseHamiltonian.GeneralDecoderODE (BinDecode DW prepTD implDP implOK_implDP)
open SparseHamiltonian.OracleCircuit
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase)
open SourceAccuracyODE (WOutcome)
open GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Query)

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The certificate-form conditions for the decoded data**: they depend on the sparse access
only through the lifts of its matrix, which the decoded data share. -/
theorem certRestG_decData {q : GPubT} {b A : ℕ} {D : QData (X × Fin (2 ^ q.m)) N q.s q.k b}
    {x : X} {Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ}
    {Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ}
    {G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ}
    {bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ} {sol : ℝ → Reg (Fin q.k) ℂ}
    {U : ℝ → Reg (Fin q.k) ℂ → ℝ → Reg (Fin q.k) ℂ} {bs : ℕ → Reg (Fin q.k) ℂ} {gb cq ζ : ℝ}
    (dc : BinDecode b q.b A) (c₀ : ℝ) (hc₀ : 0 < c₀) (hdc : dc.Exact D.val c₀)
    (hR : CertRestG q D x Jl Wp G bf sol U bs gb cq ζ) :
    CertRestG q (D.decData dc c₀ hc₀ hdc) x Jl Wp G bf sol U bs gb cq ζ :=
  ⟨hR.load_unitary, hR.prep_left, hR.prep_right, hR.prep, hR.init_load, hR.forcing_load,
    hR.accretive, hR.regular, hR.mild, hR.propagator, hR.target_ne, hR.gb_pos, hR.cq_nonneg,
    hR.scale, hR.mass, hR.ratio, hR.source, hR.budget, hR.branch⟩

set_option maxHeartbeats 1600000 in
/-- **The outcome of the time-dependent decoder solver under the manuscript's certificates** (every
`T ≥ 0`, represented samples of any sign): for public data with `BTPublicOK0 q.pub` and the public
rescaling outside the zero case, time-indexed sparse access `D` of general size with a decoder that
has an exact binary entry decoding `dc` of its stored words into `q.b`-bit components
(`c₀ = q.c0`), every input whose samples have the released energy bounds, loading and
weight-preparation circuits calling the coherent sampled-time supplied oracles within `ζ_s` with
the source budget `98304 q* ζ + 3 ζ_s ≤ 25 ν'`, and the conditions `CertRestG`, the protocol
`nprotocol (prepTD q N dc loadC wpC) (2g)` has the guarantees `WOutcome … (ε / 100)` for
`primsTG D x`, against the marker embedding of `x(T)`. -/
theorem decoder_time_cert_outcome (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    {b A : ℕ} (D : QData (X × Fin (2 ^ q.m)) N q.s q.k b) (dc : BinDecode b q.b A)
    (hdc : dc.Exact D.val q.c0)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) (x : X)
    (hrH : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hcH : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2)
    (hrD : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (hcD : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ) (sol : ℝ → Reg (Fin q.k) ℂ)
    (U : ℝ → Reg (Fin q.k) ℂ → ℝ → Reg (Fin q.k) ℂ) (bs : ℕ → Reg (Fin q.k) ℂ)
    (gb cq ζ ζs : ℝ) (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun (primsTG D x) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (primsTG D x) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 25 * q.pub.params.nu)
    (hR : CertRestG q D x Jl Wp G bf sol U bs gb cq ζ) :
    WOutcome (prepTD q N dc loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (primsTG D x) (markEmb q.k (sol q.T)) := by
  have hc₀ : 0 < q.c0 := hq.c0_pos
  exact general_time_cert_outcomeI q hq hγ (D.decData dc q.c0 hc₀ hdc) (fun _ => false)
    (QData.decData_val_zero D dc q.c0 hc₀ hdc) (fun z => rfl) x
    (fun w => D.prims (R := ℂ) (x, wordEquivFin q.m w))
    (fun w j => D.prims_isUnitary (x, wordEquivFin q.m w) j)
    (implDP (k := q.k) N q.s (fun _ => false) dc)
    (fun w => implOK_implDP D dc q.c0 hc₀ hdc (fun _ => false)
      (QData.decData_val_zero D dc q.c0 hc₀ hdc) (x, wordEquivFin q.m w))
    loadC hloadV wpC hwpV hrH hcH hrD hcD Jl Wp G bf sol U bs gb cq ζ ζs hζs hload hwp hbud
    (certRestG_decData dc q.c0 hc₀ hdc hR)

end

end SparseHamiltonian.MeshCertificateODE
