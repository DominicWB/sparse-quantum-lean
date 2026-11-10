import MeshCertificateODE.Binary
import GeneralDecoderODE.SolverTime
import GeneralSparseODE.Valid

/-!
# The certificate-form conditions for sparse access of general size

For the time-dependent gate solver for sparse access of general size (`GeneralSparseODE`; through
any implementation of the padded oracles, `GeneralDecoderODE.prepTI`), the problem lives on the
`k`-qubit index register: the generator pieces `G_r`, the forcing pieces, the solution and its
propagator `U` are on `Reg (Fin k) ℂ`, and the samples are the lifts `padLift D (x, r)` of the
matrices extended by zero to the `2^k` index words. `CertRestG` collects the certificate-form
conditions there; they transfer to the padded problem on `k + 1` qubits along the marker
embedding:

* `zextL`: the zero extension as a continuous linear map of operators; `zext_adjoint`,
  `dissipativePart_zext`; the integrated sample errors of the zero-extended pieces are at most
  those on the index register (`sampleErr_zext_le`, `dissErr_zext_le`);
* `liftU U`: the propagator of the zero-extended pieces (the marker embedding of the propagated
  low part, the marked part constant; `isMeshPropagator_liftU`), and `quadSum_liftU`;
* `CertRestG.padded`: the conditions `CertRest` of the padded problem;
* `general_time_cert_outcomeI`: the guarantees of the protocol through any implementation;
* `general_time_cert_outcome`: the guarantees of the protocol `GeneralSparseODE.GPubT.prep` of
  the general-size solver.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory SparseHamiltonian.GateCircuit
  SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open TimeDependentExtensions
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE
open SparseHamiltonian.GeneralDecoderODE (prepTI ndTI arTI ndTI_public arTI_ok nativeOKTI)
open SparseHamiltonian.OracleCircuit
open GateBinaryODE (SZ4 mLift hadUJ4_ok)
open GateBinaryODETime (PubT privFamT HsT LsT)
open ZeroTimeGateODE (BTPublicOK0 BTZeroCase tzprepC btpublicOK_of btparams_ok0
  btzeroCase_params)
open SourceAccuracyODE (WOutcome)
open GateODE.Time (gens)
open GatePointerEncoding (wordValue wordEquivFin)
open NativeSparseBlockEncoding (Query)
open ODEStateNormalization (unitDirection)
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (IsMeshPropagator meshScale)
open scoped InnerProduct BigOperators

/-! ### The zero extension of operators -/

section Zext

variable {k : ℕ}

/-- **The zero extension as a continuous linear map** of operators. -/
def zextL (k : ℕ) : (Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) →L[ℂ]
    (Reg (Fin (k + 1)) ℂ →L[ℂ] Reg (Fin (k + 1)) ℂ) :=
  (ContinuousLinearMap.compL ℂ (Reg (Fin (k + 1)) ℂ) (Reg (Fin k) ℂ) (Reg (Fin (k + 1)) ℂ)
    (markEmb k)) ∘L
    (ContinuousLinearMap.compL ℂ (Reg (Fin (k + 1)) ℂ) (Reg (Fin k) ℂ) (Reg (Fin k) ℂ)).flip
      (lowPart k)

theorem zextL_apply (A : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) : zextL k A = zext A := rfl

/-- The adjoint of a zero extension is the zero extension of the adjoint. -/
theorem zext_adjoint (A : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) : (zext A)† = zext (A†) := by
  have hlow : (lowPart k : Reg (Fin (k + 1)) ℂ →L[ℂ] Reg (Fin k) ℂ)† = markEmb k := by
    rw [← markEmb_adjoint, ContinuousLinearMap.adjoint_adjoint]
  unfold zext
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, markEmb_adjoint, hlow,
    ContinuousLinearMap.comp_assoc]

/-- The Hermitian part of a zero extension is the zero extension of the Hermitian part. -/
theorem dissipativePart_zext (A : Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) :
    ODEHermitianReduction.dissipativePart (zext A) =
      zext (ODEHermitianReduction.dissipativePart A) := by
  simp only [ODEHermitianReduction.dissipativePart, HermitianDilation.hermitianPart]
  rw [zext_adjoint, ← zextL_apply, ← zextL_apply, ← zextL_apply, map_smul, map_add]

/-- Zero-extended pieces are integrable. -/
theorem regular_zext {M : ℕ} {t : ℕ → ℝ} {G : Fin M → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ}
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    RepresentedSampleODE.RegularPieces t (fun r u => zext (G r u)) :=
  fun r => ⟨(zextL k).integrable_comp (hGi r).1, (zextL k).integrable_comp (hGi r).2⟩

/-- **The integrated sample error of zero-extended pieces and samples** is at most that on the
index register. -/
theorem sampleErr_zext_le {M : ℕ} {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (Gt : Fin M → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    sampleErr t (fun r u => zext (G r u)) (fun r => zext (Gt r)) ≤ sampleErr t G Gt := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hab := hmesh.mono (Nat.le_succ r)
  have h1 : IntervalIntegrable (fun u => ‖zext (G r u) - zext (Gt r)‖) volume (t r)
      (t ((r : ℕ) + 1)) := ((regular_zext hGi r).sub intervalIntegrable_const).norm
  have h2 : IntervalIntegrable (fun u => ‖G r u - Gt r‖) volume (t r) (t ((r : ℕ) + 1)) :=
    ((hGi r).sub intervalIntegrable_const).norm
  refine intervalIntegral.integral_mono_on hab h1 h2 fun u _ => ?_
  rw [zext_sub]
  exact norm_zext_le _

/-- **The dissipative sample error of zero-extended pieces and samples** is at most that on the
index register. -/
theorem dissErr_zext_le {M : ℕ} {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (Gt : Fin M → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ)
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    dissErr t (fun r u => zext (G r u)) (fun r => zext (Gt r)) ≤ dissErr t G Gt := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hab := hmesh.mono (Nat.le_succ r)
  have h1 := dissipativePart_intervalIntegrable (regular_zext hGi r) (zext (Gt r))
  have h2 := dissipativePart_intervalIntegrable (hGi r) (Gt r)
  refine intervalIntegral.integral_mono_on hab h1 h2 fun u _ => ?_
  rw [zext_sub, dissipativePart_zext]
  exact norm_zext_le _

/-- The source scale is the same for the marker embeddings of the solution and the forcing. -/
theorem meshScale_markEmb {M : ℕ} (sol : ℝ → Reg (Fin k) ℂ) (bf : Fin M → ℝ → Reg (Fin k) ℂ)
    (t : ℕ → ℝ) :
    meshScale (fun u => markEmb k (sol u)) (fun r u => markEmb k (bf r u)) t =
      meshScale sol bf t := by
  unfold meshScale
  simp only [norm_markEmb]

end Zext

/-! ### The propagator of the zero-extended pieces -/

section Propagator

variable {k : ℕ}

/-- **The lift of a propagator** of pieces on the index register: the marker embedding of the
propagated low part, the marked part kept. -/
def liftU (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) :
    ℝ → Reg (Fin (k + 1)) ℂ → ℝ → Reg (Fin (k + 1)) ℂ :=
  fun t₀ w u => markEmb k (U t₀ (lowPart k w) u) + (w - markEmb k (lowPart k w))

theorem lowPart_markEmb_apply (y : Reg (Fin k) ℂ) : lowPart k (markEmb k y) = y := by
  rw [← comp_apply (lowPart k) (markEmb k), lowPart_markEmb]
  rfl

theorem liftU_markEmb (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ) (t₀ u : ℝ)
    (y : Reg (Fin k) ℂ) : liftU U t₀ (markEmb k y) u = markEmb k (U t₀ y u) := by
  unfold liftU
  rw [lowPart_markEmb_apply, sub_self, add_zero]

/-- A homogeneous solution plus a vector in the kernel of the generator path is a homogeneous
solution. -/
theorem solves_add_const {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] {G : ℝ → V →L[ℂ] V} {y : ℝ → V} {c : V} {a b : ℝ}
    (h : SolvesODE G 0 y a b) (hc : ∀ u, G u c = 0) :
    SolvesODE G 0 (fun u => y u + c) a b := by
  intro u hu
  have h1 := (h u hu).add_const c
  have e : -(G u (y u + c)) + (0 : ℝ → V) u = -(G u (y u)) + (0 : ℝ → V) u := by
    rw [map_add, hc u, add_zero]
  rw [e]
  exact h1

/-- **The propagator of the zero-extended pieces.** -/
theorem isMeshPropagator_liftU {M : ℕ} {G : Fin M → ℝ → Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ}
    {t : ℕ → ℝ} {T : ℝ} {U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ}
    (hU : IsMeshPropagator G t T U) :
    IsMeshPropagator (fun r u => zext (G r u)) t T (liftU U) := by
  intro t₀ ht₀ w
  obtain ⟨h0, hsol⟩ := hU t₀ ht₀ (lowPart k w)
  refine ⟨?_, fun r hst => ?_⟩
  · show markEmb k (U t₀ (lowPart k w) t₀) + (w - markEmb k (lowPart k w)) = w
    rw [h0]
    abel
  · have h1 := solves_comp (markEmb k) (fun u => zext_markEmb (G r u)) (hsol r hst)
    have hz : (fun u => markEmb k ((0 : ℝ → Reg (Fin k) ℂ) u)) = 0 := by
      funext u
      simp
    rw [hz] at h1
    have hc : ∀ u, zext (G r u) (w - markEmb k (lowPart k w)) = 0 := by
      intro u
      show markEmb k (G r u (lowPart k (w - markEmb k (lowPart k w)))) = 0
      rw [map_sub, lowPart_markEmb_apply, sub_self, map_zero, map_zero]
    exact solves_add_const h1 hc

/-- The propagated quadrature sum of the marker embeddings is the marker embedding of the
propagated quadrature sum. -/
theorem quadSum_liftU (T : ℝ) (M : ℕ) (U : ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ)
    (x0 : Reg (Fin k) ℂ) (bs : ℕ → Reg (Fin k) ℂ) :
    quadSum T M (liftU U) (markEmb k x0) (fun r => markEmb k (bs r)) =
      markEmb k (quadSum T M U x0 bs) := by
  unfold quadSum
  simp only [liftU_markEmb, map_add, map_sum, map_smul_of_tower]

end Propagator

/-! ### The conditions on the index register -/

section Rest

variable {X : Type*} {N : ℕ}

/-- **The certificate-form instance conditions on the index register**: the loading `Jl` and the
weight preparation `Wp` with their promises, the generator pieces `G_r` on the uniform mesh of the
`2^m` slots (accretive, integrable) with their propagator `U`, the forcing pieces `b_r` and the
mild solution `x` (`x(T) = U(T, 0) x₀ + ∑_r ∫ U(T, v) b_r(v) dv`), `x(T) ≠ 0`,
`B ≤ ḡ ‖x(T)‖` for `B = ‖x₀‖ + ∑_r ∫ ‖b_r‖`, the source certificate
`‖x(T) - U(T, 0) x₀ - ∑_r (T/M) U(T, t_r) b̃_r‖ ≤ ζ B` of the slot nodes with the mass condition
`B_m ≤ c_q B`, `c_q ḡ ≤ g`, and the sample certificates of the lifts `padLift D (x, r)` of the
samples: `ζ + c_q (ΔG + 2 ΔD) ≤ ε / (2000 ḡ)` and `6 R ΔD ≤ ν'`, for the released public
parameters `q.pub.params` of the padded problem. The conditions depend on the sparse access `D`
only through the lifts of its matrix. The mild solution is the definition of `x`; the analysis uses
the source certificate. -/
structure CertRestG (q : GPubT) {b : ℕ} (D : QData (X × Fin (2 ^ q.m)) N q.s q.k b) (x : X)
    (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
    (G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ)
    (bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ) (sol : ℝ → Reg (Fin q.k) ℂ)
    (U : ℝ → Reg (Fin q.k) ℂ → ℝ → Reg (Fin q.k) ℂ) (bs : ℕ → Reg (Fin q.k) ℂ)
    (gb cq ζ : ℝ) : Prop where
  load_unitary : ∀ c, IsUnitary (Jl c)
  prep_left : Wp.conjTranspose * Wp = 1
  prep_right : Wp * Wp.conjTranspose = 1
  prep : ∀ w : Cfg (Fin (q.m + 1)),
    Wp w (fun _ => false) = ((q.pub.params.srcAmp (sol 0) bs (w 0, Fin.tail w) : ℝ) : ℂ)
  init_load : sol 0 ≠ 0 →
    Jl (false, fun _ => false) (seedV (S := Fin q.k)) = unitDirection (sol 0)
  forcing_load : ∀ w : Fin q.m → Bool, bs (wordValue w) ≠ 0 →
    Jl (true, w) (seedV (S := Fin q.k)) = unitDirection (bs (wordValue w))
  accretive : ∀ r : Fin (2 ^ q.m),
    ∀ u ∈ Icc (umesh q.T (2 ^ q.m) r) (umesh q.T (2 ^ q.m) ((r : ℕ) + 1)), Accretive (G r u)
  regular : RepresentedSampleODE.RegularPieces (umesh q.T (2 ^ q.m)) G
  mild : RepresentedSampleODE.MildSolution (umesh q.T (2 ^ q.m)) q.T bf sol U
  propagator : IsMeshPropagator G (umesh q.T (2 ^ q.m)) q.T U
  target_ne : sol q.T ≠ 0
  gb_pos : 0 < gb
  cq_nonneg : 0 ≤ cq
  scale : meshScale sol bf (umesh q.T (2 ^ q.m)) ≤ gb * ‖sol q.T‖
  mass : q.pub.params.mass (sol 0) bs ≤ cq * meshScale sol bf (umesh q.T (2 ^ q.m))
  ratio : cq * gb ≤ q.g
  source : ‖sol q.T - quadSum q.T (2 ^ q.m) U (sol 0) bs‖ ≤
    ζ * meshScale sol bf (umesh q.T (2 ^ q.m))
  budget : ζ + cq * (sampleErr (umesh q.T (2 ^ q.m)) G (fun r => padLift D (x, r)) +
    2 * dissErr (umesh q.T (2 ^ q.m)) G (fun r => padLift D (x, r))) ≤ q.ε / (2000 * gb)
  branch : 6 * q.pub.params.R * dissErr (umesh q.T (2 ^ q.m)) G (fun r => padLift D (x, r)) ≤
    q.pub.params.nu

/-- **The instance conditions of the padded problem**: the conditions on the index register give
those of `CertRest` for the padded data along the marker embedding (the loading on the low wires,
the zero extensions of the generator pieces and the lifted propagator, the marker embeddings of
the forcing, the solution and the source vectors). -/
theorem CertRestG.padded {q : GPubT} {D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b} {x : X}
    {Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ}
    {Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ}
    {G : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ →L[ℂ] Reg (Fin q.k) ℂ}
    {bf : Fin (2 ^ q.m) → ℝ → Reg (Fin q.k) ℂ} {sol : ℝ → Reg (Fin q.k) ℂ}
    {U : ℝ → Reg (Fin q.k) ℂ → ℝ → Reg (Fin q.k) ℂ} {bs : ℕ → Reg (Fin q.k) ℂ} {gb cq ζ : ℝ}
    (hT : 0 ≤ q.T) (hR0 : 0 ≤ q.pub.params.R) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hR : CertRestG q D x Jl Wp G bf sol U bs gb cq ζ) :
    CertRest q.pub (D.padData z₀ hz₀) (Equiv.refl _) x (fun c => lowOp (Jl c)) Wp
      (fun r u => zext (G r u)) (fun r u => markEmb q.k (bf r u)) (fun u => markEmb q.k (sol u))
      (liftU U) (fun r => markEmb q.k (bs r)) gb cq ζ := by
  have hmesh := isMesh_umesh hT (Nat.two_pow_pos q.m)
  have hseed : ∀ c, lowOp (Jl c) (seedV (S := Fin (q.k + 1))) =
      markEmb q.k (Jl c (seedV (S := Fin q.k))) := by
    intro c
    rw [seedV_markEmb, ← comp_apply, lowOp_markEmb, comp_apply]
  have hne0 : ∀ y : Reg (Fin q.k) ℂ, markEmb q.k y ≠ 0 → y ≠ 0 := by
    intro y hy h0
    apply hy
    rw [h0, map_zero]
  have hlift : (fun r : Fin (2 ^ q.m) => mLift (D.padData z₀ hz₀) (Equiv.refl _) (x, r)) =
      fun r => zext (padLift D (x, r)) := by
    funext r
    exact mLift_padData D z₀ hz₀ (x, r)
  have hS := sampleErr_zext_le hmesh G (fun r => padLift D (x, r)) hR.regular
  have hD := dissErr_zext_le hmesh G (fun r => padLift D (x, r)) hR.regular
  refine ⟨fun c => lowOp_isUnitary (hR.load_unitary c), hR.prep_left, hR.prep_right, ?_, ?_, ?_,
    fun r u hu => accretive_zext (hR.accretive r u hu), regular_zext hR.regular,
    isMeshPropagator_liftU hR.propagator, ?_, hR.gb_pos, hR.cq_nonneg, ?_, ?_, hR.ratio, ?_, ?_,
    ?_⟩
  · intro w
    have h := hR.prep w
    rw [← srcAmp_markEmb] at h
    exact h
  · intro hx
    show lowOp (Jl (false, fun _ => false)) (seedV (S := Fin (q.k + 1))) =
      unitDirection (markEmb q.k (sol 0))
    rw [unitDirection_markEmb, ← hR.init_load (hne0 _ hx)]
    exact hseed _
  · intro w hw
    have hw' : bs (wordValue (r := q.m) w) ≠ 0 := hne0 _ hw
    have e : lowOp (Jl (true, w)) (seedV (S := Fin (q.k + 1))) =
        markEmb q.k (unitDirection (bs (wordValue (r := q.m) w))) := by
      rw [← hR.forcing_load w hw']
      exact hseed _
    rw [← unitDirection_markEmb] at e
    exact e
  · intro h0
    apply hR.target_ne
    have h1 : markEmb q.k (sol q.T) = 0 := h0
    have := congrArg (lowPart q.k) h1
    rwa [lowPart_markEmb_apply, map_zero] at this
  · have h := hR.scale
    rw [← meshScale_markEmb, ← norm_markEmb (k := q.k)] at h
    exact h
  · have h := hR.mass
    rw [← mass_markEmb, ← meshScale_markEmb] at h
    exact h
  · have h := hR.source
    rw [← meshScale_markEmb, ← norm_markEmb (k := q.k), map_sub, ← quadSum_liftU] at h
    exact h
  · show ζ + cq * (sampleErr (umesh q.T (2 ^ q.m)) (fun r u => zext (G r u))
        (fun r => mLift (D.padData z₀ hz₀) (Equiv.refl _) (x, r)) +
      2 * dissErr (umesh q.T (2 ^ q.m)) (fun r u => zext (G r u))
        (fun r => mLift (D.padData z₀ hz₀) (Equiv.refl _) (x, r))) ≤ q.ε / (2000 * gb)
    rw [hlift]
    have h := mul_le_mul_of_nonneg_left (add_le_add hS (mul_le_mul_of_nonneg_left hD
      (by norm_num : (0 : ℝ) ≤ 2))) hR.cq_nonneg
    linarith [hR.budget]
  · show 6 * q.pub.params.R * dissErr (umesh q.T (2 ^ q.m)) (fun r u => zext (G r u))
        (fun r => mLift (D.padData z₀ hz₀) (Equiv.refl _) (x, r)) ≤ q.pub.params.nu
    rw [hlift]
    have h := mul_le_mul_of_nonneg_left hD (by positivity : (0 : ℝ) ≤ 6 * q.pub.params.R)
    linarith [hR.branch]

end Rest

/-! ### The outcome -/

section Outcome

variable {X : Type*} {N : ℕ} {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Y Xa : Type*} [Fintype Y] [DecidableEq Y] [Fintype Xa] [DecidableEq Xa]

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general time-dependent solver through any implementation under the
manuscript's certificates** (every `T ≥ 0`, represented samples of any sign): for public data
with `BTPublicOK0 q.pub` and the public rescaling outside the zero case, time-indexed sparse access
of general size with the decoder `c₀(X + iY)`, a public word `z₀` decoded as `0`, unitary
primitives `Pw w` at every slot word, an implementation `impl` of the padded oracles of the samples
from them on clean ancillas, every input whose samples have the released energy bounds, loading
and weight-preparation circuits calling `slotPrim Pw` within `ζ_s` with the source budget
`98304 q* ζ + 3 ζ_s ≤ 25 ν'` (`ν'` the precision of the private simulation), and the conditions
`CertRestG`, the protocol `nprotocol (prepTI q impl loadC wpC) (2g)` has the guarantees
`WOutcome … (ε / 100)` for `slotPrim Pw`, against the marker embedding of `x(T)`. -/
theorem general_time_cert_outcomeI (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z) (x : X)
    (Pw : Cfg (Fin q.m) → Query → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hPw : ∀ w j, IsUnitary (Pw w j))
    (impl : Query → List (NInstr (PY (q.k + 1) q.b ⊕ Xa) Y Query))
    (himpl : ∀ w, ImplOK (Pw w)
      (prims (R := ℂ) (D.padData z₀ hz₀) (Equiv.refl _) (x, wordEquivFin q.m w)) impl)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ Y) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid)
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
    (hload : ApproxOn CleanX (nrun (slotPrim Pw) loadC) (liftB (loadIdeal Jl)) ζs)
    (hwp : ApproxOn CleanX (nrun (slotPrim Pw) wpC) (liftB (matOp Wp)) ζs)
    (hbud : 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ +
      3 * ζs ≤ 25 * q.pub.params.nu)
    (hR : CertRestG q D x Jl Wp G bf sol U bs gb cq ζ) :
    WOutcome (prepTI q impl loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (slotPrim Pw) (markEmb q.k (sol q.T)) := by
  have hPs : ∀ j, IsUnitary (slotPrim Pw j) := fun j => slotPrim_isUnitary _ hPw j
  -- the padded data and the padded instance
  have hrange := padData_range D z₀ hz₀
  have hrH' : ∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro r i
    rw [padData_zpad, hamiltonianPart_zpad]
    exact zpad_row_le D.hN _ (hrH r) i
  have hcH' : ∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaH ^ 2 := by
    intro r j
    rw [padData_zpad, hamiltonianPart_zpad]
    exact zpad_col_le D.hN _ (hcH r) j
  have hrD' : ∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaD ^ 2 := by
    intro r i
    rw [padData_zpad, dissipativePart_zpad]
    exact zpad_row_le D.hN _ (hrD r) i
  have hcD' : ∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart ((D.padData z₀ hz₀).matrix (x, r)) i
      j‖ ^ 2 ≤ q.pub.etaD ^ 2 := by
    intro r j
    rw [padData_zpad, dissipativePart_zpad]
    exact zpad_col_le D.hN _ (hcD r) j
  have hε0 : (0 : ℝ) < q.ε := hq.ε_pos
  have hεh : q.ε ≤ 1 / 2 := hq.ε_half
  have hg1 : (1 : ℝ) ≤ q.g := hq.g_ge
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith
  have hR0 : 0 ≤ q.pub.params.R := ImprovedODEQueryBudget.radius_nonneg _ _
    (q.pub.params.ratio_ge hq.g_ge) (q.pub.params.acc_pos hq.ε_pos)
    (q.pub.params.acc_le_one (show q.ε ≤ 1 by linarith))
  have hR' := hR.padded hq.T_nonneg hR0 z₀ hz₀
  have hloadV' : ∀ i ∈ liftC loadC, i.Valid := valid_liftC _ hloadV
  have hload' : ApproxOn CleanX (nrun (slotPrim Pw) (liftC loadC))
      (liftB (loadIdeal (fun c => lowOp (Jl c)))) ζs :=
    approxOn_liftLoad (slotPrim Pw) loadC Jl hζs hload
  have hQ1 : 1 ≤ GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    GateRemarks.ODE.one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg
      (by linarith) hε2 (by linarith)
  by_cases hz : BTZeroCase q.pub
  · -- the direct source assembly
    have hp := btparams_ok0 hq
    have hpr : prepTI q impl loadC wpC = tzprepC (liftC loadC) wpC := by
      rw [prepTI, if_pos hz]
      rfl
    have h0 : 0 ≤ 98304 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        q.ζ := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
    have hI := cert_tzInstanceOK q.pub hq (D.padData z₀ hz₀) (Equiv.refl _) x hrH' hcH' hrD'
      hcD' (fun c => lowOp (Jl c)) Wp (fun r u => zext (G r u)) (fun r u => markEmb q.k (bf r u))
      (fun u => markEmb q.k (sol u)) (liftU U) (fun r => markEmb q.k (bs r)) gb cq ζ hR'
    rw [hpr]
    exact cert_native_time_zero_outcome (S := Fin (q.k + 1)) (Zs := Zs)
      (Z := SZ4 (q.k + 1) q.b ⊕ Xa) (Y := Fin q.m ⊕ Y) (J := Query) q.pub.params
      q.pub.params.a q.pub.params.m q.pub.params.r q.pub.params.K q.pub.params.l q.pub.params.f
      (arTI q Xa).bT (arTI q Xa).bP (arTI q Xa).A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half
      hp.lamH_nonneg hp.lamD_nonneg (btzeroCase_params hq hz) (liftC loadC) hloadV' wpC hwpV
      (slotPrim Pw) (fun c => lowOp (Jl c)) Wp (HsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (LsT (D.padData z₀ hz₀) (Equiv.refl _) x) (fun r u => zext (G r u))
      (fun r u => markEmb q.k (bf r u)) (fun u => markEmb q.k (sol u)) (liftU U)
      (fun r => markEmb q.k (bs r)) gb cq ζ ζs hPs hζs hload' hwp (by linarith) hI
  · -- the native preparation
    have hP := btpublicOK_of hq hz
    obtain ⟨-, hd, -, -, -, -⟩ := GateODEBudget.binary_ode_time_sizes q.pub hP (hγ hz)
    have hd' : (q.pub.params.d : ℝ) ≤
        4096 * GateODEBudget.qOf q.pub.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) := hd
    have hpr : prepTI q impl loadC wpC =
        tnprepC q.pub.params q.pub.UJg (ndTI q impl) (arTI q Xa) (liftC loadC) wpC := by
      rw [prepTI, if_neg hz]
    have hbud' : 24 * (q.pub.params.d : ℝ) * q.ζ + 3 * ζs ≤ 25 * q.pub.params.nu := by
      have hζ0 : (0 : ℝ) ≤ q.ζ := hP.ζ_pos.le
      have := mul_le_mul_of_nonneg_right hd' hζ0
      linarith
    rw [hpr]
    exact cert_native_time_outcome q.pub.params (q.pub.params_ok hP) q.pub.UJg
      (hadUJ4_ok q.pub.σ q.pub.hσ) (ndTI q impl) (ndTI_public q (himpl (fun _ => false)).valid)
      (arTI q Xa) q.ζ hP.ζ_pos.le
      (arTI_ok q hP impl) (liftC loadC) hloadV' wpC hwpV (slotPrim Pw) hPs
      ⟨UJop (R := ℂ) q.pub.UJg,
        privFamT q.pub.params (D.padData z₀ hz₀) (Equiv.refl _) x q.pub.rho q.pub.γ,
        fun c => lowOp (Jl c), Wp⟩
      rfl (nativeOKTI q hP D z₀ hz₀ hdec x Pw hPw impl himpl) ζs hζs hload' hwp hbud'
      (HsT (D.padData z₀ hz₀) (Equiv.refl _) x) (LsT (D.padData z₀ hz₀) (Equiv.refl _) x)
      (fun r u => zext (G r u)) (fun r u => markEmb q.k (bf r u))
      (fun u => markEmb q.k (sol u)) (liftU U) (fun r => markEmb q.k (bs r)) gb cq ζ
      (cert_instanceOK q.pub hP (D.padData z₀ hz₀) (Equiv.refl _) hrange x hrH' hcH' hrD' hcD'
        (fun c => lowOp (Jl c)) Wp (fun r u => zext (G r u)) (fun r u => markEmb q.k (bf r u))
        (fun u => markEmb q.k (sol u)) (liftU U) (fun r => markEmb q.k (bs r)) gb cq ζ hR')

set_option maxHeartbeats 1600000 in
/-- **The outcome of the general time-dependent solver under the manuscript's certificates**
(every `T ≥ 0`, represented samples of any sign): the guarantees of
`general_time_cert_outcomeI` for the protocol `nprotocol (q.prep N z₀ loadC wpC) (2g)` of the
general-size solver (the implementation `implP` of the padded oracles from the coherent
sampled-time supplied oracles `primsTG D x`). -/
theorem general_time_cert_outcome (q : GPubT) (hq : BTPublicOK0 q.pub)
    (hγ : ¬ BTZeroCase q.pub →
      q.γ = GateODEBudget.gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (D : QData (X × Fin (2 ^ q.m)) N q.s q.k q.b) (z₀ : Cfg (VW q.b)) (hz₀ : D.val z₀ = 0)
    (hdec : ∀ z, D.val z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.m + 1) ⊕ Fin q.k) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
    (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.k q.b) Query))
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
    WOutcome (q.prep N z₀ loadC wpC) q.pub.params.ratio (q.ε / 100)
      (q.pub.params.ratio_ge hq.g_ge) (primsTG D x) (markEmb q.k (sol q.T)) :=
  general_time_cert_outcomeI q hq hγ D z₀ hz₀ hdec x
    (fun w => D.prims (R := ℂ) (x, wordEquivFin q.m w))
    (fun w j => D.prims_isUnitary (x, wordEquivFin q.m w) j) (implP N q.s z₀)
    (fun w => GeneralSparseAccess.implOK D z₀ hz₀ (x, wordEquivFin q.m w)) loadC hloadV wpC hwpV
    hrH hcH hrD hcD Jl Wp G bf sol U bs gb cq ζ ζs hζs hload hwp hbud hR

end Outcome

end

end SparseHamiltonian.MeshCertificateODE
