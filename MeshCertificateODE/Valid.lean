import MeshCertificateODE.General
import MeshCertificateODE.Quadrature

/-!
# The certificate-form conditions for a problem on `ℂ^N`

The certificate-form conditions `CertRestG` are stated on the `k`-qubit index register, for the
matrix extended by zero to the index words `≥ N`: the samples are
`padLift D (x, r) = validLift (matrixOperator (D.matrix (x, r)))` (`GeneralSparseODE.padLift_eq`).
This module carries a problem on `ℂ^N` into them along the isometric embedding `validEmb` of
`GeneralSparseODE.Valid` (the basis vector of `i` to that of the index word `binW k i`): the
generator pieces lift to `validLift ∘ G_r`, the forcing pieces, the solution and the source
vectors embed, and the propagator lifts to `liftV N k U` (the embedding of the propagated valid
part, the invalid part kept, on which the lifted pieces vanish).

* The path: `regular_validLift`, `GeneralSparseODE.accretive_validLift`, `isMeshPropagator_liftV`,
  `mild_liftV`.
* The source: `meshScale_validEmb`, `quadMass_validEmb`, `quadAmp_validEmb` and `quadSum_liftV`
  (the source scale, the coefficient mass, the weight-preparation amplitudes and the propagated
  quadrature sum are those on `ℂ^N`), `validEmb_ne_zero`.
* The samples: `validLiftL` (the lift as a continuous linear map of operators), `validLift_adjoint`,
  `dissipativePart_validLift`; `sampleErr_padLift_le`, `dissErr_padLift_le`: the integrated sample
  errors of the lifted pieces against the lifted samples are at most those on `ℂ^N` against the
  samples.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set MeasureTheory SparseHamiltonian.GateCircuit
open TimeDependentExtensions
open SparseHamiltonian.GeneralSparseAccess
open SparseHamiltonian.GeneralSparseODE (validEmb validRes validLift padLift padLift_eq
  validRes_validEmb inner_validEmb norm_validEmb validLift_comp_validEmb validLift_sub
  norm_validLift_le solves_comp)
open SparseHamiltonian.TimeDependentODE (SolvesODE)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (IsMeshPropagator meshScale)
open scoped InnerProduct

variable {N k : ℕ}

/-! ### The lift of operators -/

/-- **The lift of operators on `ℂ^N`** to the index register as a continuous linear map. -/
def validLiftL (N k : ℕ) : (EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) →L[ℂ]
    (Reg (Fin k) ℂ →L[ℂ] Reg (Fin k) ℂ) :=
  (ContinuousLinearMap.compL ℂ (Reg (Fin k) ℂ) (EuclideanSpace ℂ (Fin N)) (Reg (Fin k) ℂ)
    (validEmb N k)) ∘L
    (ContinuousLinearMap.compL ℂ (Reg (Fin k) ℂ) (EuclideanSpace ℂ (Fin N))
      (EuclideanSpace ℂ (Fin N))).flip (validRes N k)

theorem validLiftL_apply (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    validLiftL N k A = validLift N k A := rfl

/-- `validRes` is the adjoint of `validEmb`. -/
theorem validEmb_adjoint (hN : N ≤ 2 ^ k) : (validEmb N k)† = validRes N k := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro w u
  exact (inner_validEmb hN w u).symm

theorem validRes_adjoint (hN : N ≤ 2 ^ k) : (validRes N k)† = validEmb N k := by
  rw [← validEmb_adjoint hN, ContinuousLinearMap.adjoint_adjoint]

/-- The adjoint of a lift is the lift of the adjoint. -/
theorem validLift_adjoint (hN : N ≤ 2 ^ k)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    (validLift N k A)† = validLift N k (A†) := by
  unfold validLift
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp, validEmb_adjoint hN,
    validRes_adjoint hN, ContinuousLinearMap.comp_assoc]

/-- The Hermitian part of a lift is the lift of the Hermitian part. -/
theorem dissipativePart_validLift (hN : N ≤ 2 ^ k)
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)) :
    ODEHermitianReduction.dissipativePart (validLift N k A) =
      validLift N k (ODEHermitianReduction.dissipativePart A) := by
  simp only [ODEHermitianReduction.dissipativePart, HermitianDilation.hermitianPart]
  rw [validLift_adjoint hN, ← validLiftL_apply, ← validLiftL_apply, ← validLiftL_apply, map_smul,
    map_add]

/-- The lifted pieces are integrable. -/
theorem regular_validLift {M : ℕ} {t : ℕ → ℝ}
    {G : Fin M → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)}
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    RepresentedSampleODE.RegularPieces t (fun r u => validLift N k (G r u)) :=
  fun r => ⟨(validLiftL N k).integrable_comp (hGi r).1,
    (validLiftL N k).integrable_comp (hGi r).2⟩

/-- **The integrated sample error of lifted pieces and samples** is at most that on `ℂ^N`. -/
theorem sampleErr_validLift_le (hN : N ≤ 2 ^ k) {M : ℕ} {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (Gt : Fin M → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    sampleErr t (fun r u => validLift N k (G r u)) (fun r => validLift N k (Gt r)) ≤
      sampleErr t G Gt := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hab := hmesh.mono (Nat.le_succ r)
  have h1 : IntervalIntegrable (fun u => ‖validLift N k (G r u) - validLift N k (Gt r)‖) volume
      (t r) (t ((r : ℕ) + 1)) :=
    ((regular_validLift (k := k) hGi r).sub intervalIntegrable_const).norm
  have h2 : IntervalIntegrable (fun u => ‖G r u - Gt r‖) volume (t r) (t ((r : ℕ) + 1)) :=
    ((hGi r).sub intervalIntegrable_const).norm
  refine intervalIntegral.integral_mono_on hab h1 h2 fun u _ => ?_
  rw [← validLift_sub]
  exact norm_validLift_le hN _

/-- **The dissipative sample error of lifted pieces and samples** is at most that on `ℂ^N`. -/
theorem dissErr_validLift_le (hN : N ≤ 2 ^ k) {M : ℕ} {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (Gt : Fin M → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    dissErr t (fun r u => validLift N k (G r u)) (fun r => validLift N k (Gt r)) ≤
      dissErr t G Gt := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hab := hmesh.mono (Nat.le_succ r)
  have h1 := dissipativePart_intervalIntegrable (regular_validLift (k := k) hGi r)
    (validLift N k (Gt r))
  have h2 := dissipativePart_intervalIntegrable (hGi r) (Gt r)
  refine intervalIntegral.integral_mono_on hab h1 h2 fun u _ => ?_
  rw [← validLift_sub, dissipativePart_validLift hN]
  exact norm_validLift_le hN _

/-- **The integrated sample error against the lifted samples** of sparse access is at most that on
`ℂ^N` against the samples. -/
theorem sampleErr_padLift_le {X : Type*} {M s b : ℕ} (D : QData (X × Fin M) N s k b) (x : X)
    {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    sampleErr t (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r)) ≤
      sampleErr t G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) := by
  have e : (fun r => padLift D (x, r)) =
      fun r => validLift N k (SparseStateOverlap.matrixOperator (D.matrix (x, r))) :=
    funext fun r => padLift_eq D (x, r)
  rw [e]
  exact sampleErr_validLift_le D.hN hmesh G _ hGi

/-- **The dissipative sample error against the lifted samples** of sparse access is at most that on
`ℂ^N` against the samples. -/
theorem dissErr_padLift_le {X : Type*} {M s b : ℕ} (D : QData (X × Fin M) N s k b) (x : X)
    {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (hGi : RepresentedSampleODE.RegularPieces t G) :
    dissErr t (fun r u => validLift N k (G r u)) (fun r => padLift D (x, r)) ≤
      dissErr t G (fun r => SparseStateOverlap.matrixOperator (D.matrix (x, r))) := by
  have e : (fun r => padLift D (x, r)) =
      fun r => validLift N k (SparseStateOverlap.matrixOperator (D.matrix (x, r))) :=
    funext fun r => padLift_eq D (x, r)
  rw [e]
  exact dissErr_validLift_le D.hN hmesh G _ hGi

/-! ### The source -/

/-- The embedding of a nonzero vector is nonzero. -/
theorem validEmb_ne_zero (hN : N ≤ 2 ^ k) {v : EuclideanSpace ℂ (Fin N)} (hv : v ≠ 0) :
    validEmb N k v ≠ 0 := by
  intro h
  apply hv
  rw [← norm_eq_zero, ← norm_validEmb hN, h, norm_zero]

/-- The source scale is the same for the embeddings of the solution and the forcing. -/
theorem meshScale_validEmb (hN : N ≤ 2 ^ k) {M : ℕ} (sol : ℝ → EuclideanSpace ℂ (Fin N))
    (bf : Fin M → ℝ → EuclideanSpace ℂ (Fin N)) (t : ℕ → ℝ) :
    meshScale (fun u => validEmb N k (sol u)) (fun r u => validEmb N k (bf r u)) t =
      meshScale sol bf t := by
  unfold meshScale
  simp only [norm_validEmb hN]

/-- The coefficient mass of the embedded source vectors is that on `ℂ^N`. -/
theorem quadMass_validEmb (hN : N ≤ 2 ^ k) (T : ℝ) (m : ℕ) (x0 : EuclideanSpace ℂ (Fin N))
    (bs : ℕ → EuclideanSpace ℂ (Fin N)) :
    quadMass T m (validEmb N k x0) (fun r => validEmb N k (bs r)) = quadMass T m x0 bs := by
  unfold quadMass
  simp only [norm_validEmb hN]

/-- The weight-preparation amplitudes of the embedded source vectors are those on `ℂ^N`. -/
theorem quadAmp_validEmb (hN : N ≤ 2 ^ k) (T : ℝ) (m : ℕ) (x0 : EuclideanSpace ℂ (Fin N))
    (bs : ℕ → EuclideanSpace ℂ (Fin N)) (s : Bool × (Fin m → Bool)) :
    quadAmp T m (validEmb N k x0) (fun r => validEmb N k (bs r)) s = quadAmp T m x0 bs s := by
  unfold quadAmp quadNorm quadMass
  simp only [norm_validEmb hN]

/-! ### The propagator -/

/-- **The lift of a propagator** on `ℂ^N`: the embedding of the propagated valid part, the invalid
part kept. -/
def liftV (N k : ℕ) (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)) :
    ℝ → Reg (Fin k) ℂ → ℝ → Reg (Fin k) ℂ :=
  fun t₀ w u => validEmb N k (U t₀ (validRes N k w) u) + (w - validEmb N k (validRes N k w))

theorem liftV_validEmb (hN : N ≤ 2 ^ k)
    (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)) (t₀ u : ℝ)
    (y : EuclideanSpace ℂ (Fin N)) :
    liftV N k U t₀ (validEmb N k y) u = validEmb N k (U t₀ y u) := by
  unfold liftV
  rw [validRes_validEmb hN, sub_self, add_zero]

/-- **The propagator of the lifted pieces.** -/
theorem isMeshPropagator_liftV (hN : N ≤ 2 ^ k) {M : ℕ}
    {G : Fin M → ℝ → EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N)} {t : ℕ → ℝ} {T : ℝ}
    {U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)}
    (hU : IsMeshPropagator G t T U) :
    IsMeshPropagator (fun r u => validLift N k (G r u)) t T (liftV N k U) := by
  intro t₀ ht₀ w
  obtain ⟨h0, hsol⟩ := hU t₀ ht₀ (validRes N k w)
  refine ⟨?_, fun r hst => ?_⟩
  · show validEmb N k (U t₀ (validRes N k w) t₀) + (w - validEmb N k (validRes N k w)) = w
    rw [h0]
    abel
  · have h1 := solves_comp (validEmb N k) (fun u => validLift_comp_validEmb hN (G r u))
      (hsol r hst)
    have hz : (fun u => validEmb N k ((0 : ℝ → EuclideanSpace ℂ (Fin N)) u)) = 0 := by
      funext u
      simp
    rw [hz] at h1
    have hc : ∀ u, validLift N k (G r u) (w - validEmb N k (validRes N k w)) = 0 := by
      intro u
      show validEmb N k (G r u (validRes N k (w - validEmb N k (validRes N k w)))) = 0
      rw [map_sub, validRes_validEmb hN, sub_self, map_zero, map_zero]
    exact solves_add_const h1 hc

/-- The propagated quadrature sum of the embeddings is the embedding of the propagated quadrature
sum. -/
theorem quadSum_liftV (hN : N ≤ 2 ^ k) (T : ℝ) (M : ℕ)
    (U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N))
    (x0 : EuclideanSpace ℂ (Fin N)) (bs : ℕ → EuclideanSpace ℂ (Fin N)) :
    quadSum T M (liftV N k U) (validEmb N k x0) (fun r => validEmb N k (bs r)) =
      validEmb N k (quadSum T M U x0 bs) := by
  unfold quadSum
  simp only [liftV_validEmb hN, map_add, map_sum, map_smul_of_tower]

/-- **The mild solution embeds**: the embedding of a mild solution on `ℂ^N` is the mild solution of
the lifted problem with the lifted propagator. -/
theorem mild_liftV (hN : N ≤ 2 ^ k) {M : ℕ} {t : ℕ → ℝ} {T : ℝ}
    {bf : Fin M → ℝ → EuclideanSpace ℂ (Fin N)} {sol : ℝ → EuclideanSpace ℂ (Fin N)}
    {U : ℝ → EuclideanSpace ℂ (Fin N) → ℝ → EuclideanSpace ℂ (Fin N)}
    (h : RepresentedSampleODE.MildSolution t T bf sol U) :
    RepresentedSampleODE.MildSolution t T (fun r u => validEmb N k (bf r u))
      (fun u => validEmb N k (sol u)) (liftV N k U) := by
  obtain ⟨hint, hsol⟩ := h
  have e : ∀ r : Fin M, (fun v => liftV N k U v (validEmb N k (bf r v)) T) =
      fun v => validEmb N k (U v (bf r v) T) :=
    fun r => funext fun v => liftV_validEmb hN U v T (bf r v)
  refine ⟨fun r => ?_, ?_⟩
  · rw [e r]
    exact ⟨(validEmb N k).integrable_comp (hint r).1, (validEmb N k).integrable_comp (hint r).2⟩
  · show validEmb N k (sol T) = liftV N k U 0 (validEmb N k (sol 0)) T +
      ∑ r : Fin M, ∫ v in t r..t ((r : ℕ) + 1), liftV N k U v (validEmb N k (bf r v)) T
    simp only [liftV_validEmb hN]
    rw [hsol, map_add, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    exact ((validEmb N k).intervalIntegral_comp_comm (hint r)).symm

end

end SparseHamiltonian.MeshCertificateODE
