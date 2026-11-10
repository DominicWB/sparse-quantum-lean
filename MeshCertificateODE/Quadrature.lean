import MeshCertificateODE.Target

/-!
# The positive quadrature of the slot nodes and the Lipschitz bounds

The time-dependent gate solver assembles the source from the initial state and the source vectors
`b_r` of its slot nodes `t_r = r T / M`, `r < M = 2^m`, with weight `T / M`
(`GateODE.Time.TParams.zsrc`): the branch of slot `r` is `(T/M) b_r`. A positive quadrature of the
manuscript with nodes at the slot times and weights `w_r ≥ 0` (eq.
`ode:eq:gate-source-certificates`) is the case `(T/M) b_r = w_r b(t_r)`,
that is `b_r = (M w_r / T) b(t_r)` for `T > 0`; the loaded direction of `b_r` is that of `b(t_r)`.
The node `T` is not a slot time.

* `quadMass T m x₀ b = ‖x₀‖ + (T/M) ∑_r ‖b_r‖`: the coefficient mass `B_m`
  (`mass_eq_quadMass`);
* `quadAmp T m x₀ b`: the amplitudes `√(‖x₀‖ / B_m)`, `√((T/M) ‖b_r‖ / B_m)` of the weight
  preparation (`srcAmp_eq_quadAmp`);
* `sampleErr_umesh_le_of_lipschitz`: the integrated sample error from Lipschitz bounds as in Lemma
  `ode:lem:gate-select`: `β`-Lipschitz pieces with left-endpoint sample errors `δ_r` have
  `ΔG ≤ β T² / (2M) + (T/M) ∑_r δ_r` (the freezing error and the integrated represented-sample
  error);
* `dissErr_umesh_le_of_lipschitz`: the same for the dissipative parts: pieces whose Hermitian parts
  are `β_D`-Lipschitz, with left-endpoint dissipative sample errors `δ^D_r`, have
  `ΔD ≤ β_D T² / (2M) + (T/M) ∑_r δ^D_r` (`dissErr_eq_sampleErr`: `ΔD` is the integrated sample
  error of the Hermitian parts).
-/

set_option autoImplicit false

namespace SparseHamiltonian.MeshCertificateODE

noncomputable section
open ContinuousLinearMap Set
open TimeDependentExtensions
open SparseHamiltonian.GateODE.Time (TParams)
open GatePointerEncoding (wordValue)
open scoped BigOperators InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-! ### The quadrature mass and the weight-preparation amplitudes -/

/-- **The coefficient mass** `B_m = ‖x₀‖ + (T/M) ∑_{r < M} ‖b_r‖` of the slot quadrature,
`M = 2^m`. -/
def quadMass (T : ℝ) (m : ℕ) (x0 : V) (bs : ℕ → V) : ℝ :=
  ‖x0‖ + T / ((2 ^ m : ℕ) : ℝ) * ∑ r ∈ Finset.range (2 ^ m), ‖bs r‖

/-- **The norm of a source branch**: `‖x₀‖` on the initial label, `(T/M) ‖b_r‖` on the forcing
label of slot `r`, zero on the other labels. -/
def quadNorm (T : ℝ) (m : ℕ) (x0 : V) (bs : ℕ → V) (s : Bool × (Fin m → Bool)) : ℝ :=
  if s.1 then T / ((2 ^ m : ℕ) : ℝ) * ‖bs (wordValue s.2)‖
  else if s.2 = (fun _ => false) then ‖x0‖ else 0

/-- **The amplitudes of the weight preparation**: `√(‖x₀‖ / B_m)` on the initial label,
`√((T/M) ‖b_r‖ / B_m)` on the forcing label of slot `r`, zero on the other labels. -/
def quadAmp (T : ℝ) (m : ℕ) (x0 : V) (bs : ℕ → V) (s : Bool × (Fin m → Bool)) : ℝ :=
  Real.sqrt (quadNorm T m x0 bs s / quadMass T m x0 bs)

/-- The source mass of the solver is the quadrature mass. -/
theorem mass_eq_quadMass (p : TParams) (hT : 0 ≤ p.T) (x0 : V) (bs : ℕ → V) :
    p.mass x0 bs = quadMass p.T p.m x0 bs :=
  p.mass_eq hT x0 bs

/-- The norms of the source vectors of the solver are the branch norms of the quadrature. -/
theorem norm_zsrc (p : TParams) (hT : 0 ≤ p.T) (x0 : V) (bs : ℕ → V)
    (s : Bool × (Fin p.m → Bool)) : ‖p.zsrc x0 bs s‖ = quadNorm p.T p.m x0 bs s := by
  unfold TParams.zsrc quadNorm
  split_ifs
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hT (Nat.cast_nonneg _))]
  · rfl
  · exact norm_zero

/-- **The amplitudes of the solver's weight preparation are those of the quadrature.** -/
theorem srcAmp_eq_quadAmp (p : TParams) (hT : 0 ≤ p.T) (x0 : V) (bs : ℕ → V)
    (s : Bool × (Fin p.m → Bool)) : p.srcAmp x0 bs s = quadAmp p.T p.m x0 bs s := by
  unfold TParams.srcAmp quadAmp
  rw [norm_zsrc p hT, mass_eq_quadMass p hT]

/-! ### The Lipschitz bounds of the selection lemma -/

/-- **The integrated sample error from Lipschitz bounds** (as in Lemma `ode:lem:gate-select`):
`β`-Lipschitz pieces on the uniform mesh of `M` slots with left-endpoint sample errors `δ_r` have
`ΔG ≤ β T² / (2M) + (T/M) ∑_r δ_r`. With `M ≥ 8 β T² / δ` the freezing part is at most `δ/16`,
the manuscript's mesh condition for the Lipschitz bound. -/
theorem sampleErr_umesh_le_of_lipschitz {T : ℝ} (hT : 0 ≤ T) {M : ℕ} (hM : 0 < M)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (β : ℝ) (δ : Fin M → ℝ)
    (hLip : ∀ r : Fin M, ∀ u ∈ Icc (umesh T M r) (umesh T M ((r : ℕ) + 1)),
      ∀ w ∈ Icc (umesh T M r) (umesh T M ((r : ℕ) + 1)), ‖G r u - G r w‖ ≤ β * |u - w|)
    (hδ : ∀ r : Fin M, ‖G r (umesh T M r) - Gt r‖ ≤ δ r) :
    sampleErr (umesh T M) G Gt ≤ β * T ^ 2 / (2 * M) + T / M * ∑ r, δ r := by
  have h := sampleErr_le_of_lipschitz (isMesh_umesh hT hM) G Gt (fun _ => β) δ hLip hδ
  refine h.trans (le_of_eq ?_)
  simp only [umesh_succ_sub]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.sum_mul]
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

/-- The dissipative part is additive. -/
theorem dissipativePart_sub [CompleteSpace V] (A B : V →L[ℂ] V) :
    ODEHermitianReduction.dissipativePart (A - B) =
      ODEHermitianReduction.dissipativePart A - ODEHermitianReduction.dissipativePart B := by
  simp only [ODEHermitianReduction.dissipativePart, HermitianDilation.hermitianPart, map_sub]
  module

/-- **The dissipative sample error is the sample error of the Hermitian parts.** -/
theorem dissErr_eq_sampleErr [CompleteSpace V] {M : ℕ} (t : ℕ → ℝ)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) :
    dissErr t G Gt = sampleErr t (fun r u => ODEHermitianReduction.dissipativePart (G r u))
      (fun r => ODEHermitianReduction.dissipativePart (Gt r)) := by
  unfold dissErr sampleErr
  simp only [dissipativePart_sub]

/-- **The dissipative sample error from Lipschitz bounds of the dissipative parts**: pieces on the
uniform mesh of `M` slots whose Hermitian parts are `β`-Lipschitz, with left-endpoint dissipative
sample errors `δ_r`, have `ΔD ≤ β T² / (2M) + (T/M) ∑_r δ_r`. For the branches `H + kD`,
`|k| ≤ R`, of Lemma `ode:lem:gate-select` (`L_* ≥ Lip(H) + R Lip(D)`), `Lip(D) ≤ L_*/R`, and the
dissipative sample errors are at most the average of the branch errors at `k = ±R` over `R`. -/
theorem dissErr_umesh_le_of_lipschitz [CompleteSpace V] {T : ℝ} (hT : 0 ≤ T) {M : ℕ} (hM : 0 < M)
    (G : Fin M → ℝ → V →L[ℂ] V) (Gt : Fin M → V →L[ℂ] V) (β : ℝ) (δ : Fin M → ℝ)
    (hLip : ∀ r : Fin M, ∀ u ∈ Icc (umesh T M r) (umesh T M ((r : ℕ) + 1)),
      ∀ w ∈ Icc (umesh T M r) (umesh T M ((r : ℕ) + 1)),
        ‖ODEHermitianReduction.dissipativePart (G r u) -
          ODEHermitianReduction.dissipativePart (G r w)‖ ≤ β * |u - w|)
    (hδ : ∀ r : Fin M, ‖ODEHermitianReduction.dissipativePart (G r (umesh T M r) - Gt r)‖ ≤ δ r) :
    dissErr (umesh T M) G Gt ≤ β * T ^ 2 / (2 * M) + T / M * ∑ r, δ r := by
  rw [dissErr_eq_sampleErr]
  refine sampleErr_umesh_le_of_lipschitz hT hM _ _ β δ hLip fun r => ?_
  have h := hδ r
  rw [dissipativePart_sub] at h
  exact h

end

end SparseHamiltonian.MeshCertificateODE
