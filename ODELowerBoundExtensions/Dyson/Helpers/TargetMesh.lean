import ODELowerBoundExtensions.Dyson.Compile
import TimeDependentExtensions.ODE.Target

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Helper for the Dyson LCU target: the certified mesh comparison

The exponential left-endpoint scheme on the mesh, with the selected samples
`A_{σ r}` as cell generators and the forcing samples `b̃_r`, is within the release's certified
discretisation bound of every solution of the piecewise problem (proof of Lemma
`odel:lem:dyson`: contractive Duhamel comparison with integrated sample errors and the source
quadrature). This is `TimeDependentExtensions.ODEMesh.mesh_error`, rewritten from cells
`r : ℕ` to cells `r : Fin M` (as in `TimeDependentExtensions.MeshSampling.target_error`), with
the energy bound `‖x(u)‖ ≤ ‖x(0)‖ + b_max T` (`piecewise_norm_le`) and the public bound
`‖A_{σ r}‖ ≤ s Λ`.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE)
open TimeDependentExtensions.ODEMesh (meshRecurrence mesh_error piecewise_norm_le)
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s Ks : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Certified mesh comparison for the selected samples** (proof of Lemma `odel:lem:dyson`): the
scheme with generators `A_{σ r}` and forcing samples `b̃_r` is within
`(r₀ + b_max T) ∑_r ∫ ‖G_r - A_{σ r}‖ + ∑_r ∫ ‖b_r - b̃_r‖ + s Λ ∑_q Δ_q² rb_q / 2` of `x(T)`. -/
theorem mesh_selected_error {M : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T) (x : X)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bs : Fin M → EuclideanSpace ℂ n) (bmax r₀ : ℝ) (rb : Fin M → ℝ)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hAcc : ∀ r : Fin M,
      Accretive (SparseStateOverlap.matrixOperator (D.matrix (x, σ r))))
    (hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (hbint : ∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1)))
    (hbmax : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax)
    (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1)))
    (h₀ : ‖sol 0‖ = r₀) (hbs : ∀ r, ‖bs r‖ = rb r) :
    ‖sol T - meshRecurrence
        (fun r => SparseStateOverlap.matrixOperator
          (D.matrix (x, σ (TimeDependent.Sampled.sampleIndex hM r))))
        (fun r => bs (TimeDependent.Sampled.sampleIndex hM r)) (fun r => t (r + 1) - t r)
        (sol 0) M‖ ≤
      (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, σ r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
        (s : ℝ) * D.scale * (∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 := by
  classical
  set idx : ℕ → Fin M := TimeDependent.Sampled.sampleIndex hM with hidx
  have hidxv : ∀ r : Fin M, idx r = r := fun r => MeshSampling.sampleIndex_of_lt hM r.isLt
  have hidxlt : ∀ r (hr : r < M), idx r = ⟨r, hr⟩ :=
    fun r hr => MeshSampling.sampleIndex_of_lt hM hr
  set Gs : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
    SparseStateOverlap.matrixOperator (D.matrix (x, σ (idx r))) with hGsdef
  set bsq : ℕ → EuclideanSpace ℂ n := fun r => bs (idx r) with hbsqdef
  let Gq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r => G (idx r)
  let bq : ℕ → ℝ → EuclideanSpace ℂ n := fun r => b (idx r)
  set Λ : ℝ := (s : ℝ) * D.scale with hΛdef
  have hGs : ∀ r, Accretive (Gs r) := fun r => hAcc (idx r)
  have hGsn : ∀ r, ‖Gs r‖ ≤ Λ := fun r =>
    MeshSampling.generator_norm_le D (fun _ => σ (idx r)) x 0
  have hbmax0 : 0 ≤ bmax :=
    (norm_nonneg _).trans (hbmax ⟨0, hM⟩ (t 0) ⟨le_rfl, hmesh.mono (Nat.zero_le 1)⟩)
  have hsolq : ∀ r < M, SolvesODE (Gq r) (bq r) sol (t r) (t (r + 1)) := by
    intro r hr
    change SolvesODE (G (idx r)) (b (idx r)) sol (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hsol ⟨r, hr⟩
  have hGq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), Accretive (Gq r u) := by
    intro r hr u hu
    change Accretive (G (idx r) u)
    rw [hidxlt r hr]
    exact hG ⟨r, hr⟩ u hu
  have hbq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), ‖bq r u‖ ≤ bmax := by
    intro r hr u hu
    change ‖b (idx r) u‖ ≤ bmax
    rw [hidxlt r hr]
    exact hbmax ⟨r, hr⟩ u hu
  have hGqint : ∀ r < M, IntervalIntegrable (Gq r) volume (t r) (t (r + 1)) := by
    intro r hr
    change IntervalIntegrable (G (idx r)) volume (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hGint ⟨r, hr⟩
  have hbqint : ∀ r < M, IntervalIntegrable (bq r) volume (t r) (t (r + 1)) := by
    intro r hr
    change IntervalIntegrable (b (idx r)) volume (t r) (t (r + 1))
    rw [hidxlt r hr]
    exact hbint ⟨r, hr⟩
  have hX := piecewise_norm_le hmesh hsolq hGq bmax hbmax0 hbq
  have hMesh := mesh_error hmesh hsolq hGqint hbqint Gs hGs bsq (‖sol 0‖ + bmax * T) hX
  rw [h₀] at hMesh
  refine hMesh.trans ?_
  rw [← Fin.sum_univ_eq_sum_range (fun r => ((r₀ + bmax * T) *
      (∫ u in t r..t (r + 1), ‖Gq r u - Gs r‖) + (∫ u in t r..t (r + 1), ‖bq r u - bsq r‖) +
        (t (r + 1) - t r) ^ 2 / 2 * (‖Gs r‖ * ‖bsq r‖))) M]
  have hterm : ∀ r : Fin M, (t ((r : ℕ) + 1) - t r) ^ 2 / 2 * (‖Gs r‖ * ‖bsq r‖) ≤
      Λ * ((t ((r : ℕ) + 1) - t r) ^ 2 * rb r) / 2 := by
    intro r
    have h1 : ‖bsq r‖ = rb r := by simp only [bsq, hidxv, hbs]
    rw [h1]
    have h2 : 0 ≤ rb r := hbs r ▸ norm_nonneg _
    have h3 : 0 ≤ (t ((r : ℕ) + 1) - t r) ^ 2 / 2 := by positivity
    calc (t ((r : ℕ) + 1) - t r) ^ 2 / 2 * (‖Gs r‖ * rb r) ≤
          (t ((r : ℕ) + 1) - t r) ^ 2 / 2 * (Λ * rb r) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hGsn r) h2) h3
      _ = Λ * ((t ((r : ℕ) + 1) - t r) ^ 2 * rb r) / 2 := by ring
  calc _ ≤ ∑ r : Fin M, ((r₀ + bmax * T) * (∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, σ r))‖) +
        (∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
          Λ * ((t ((r : ℕ) + 1) - t r) ^ 2 * rb r) / 2) := by
        refine Finset.sum_le_sum fun r _ => ?_
        have hG' : Gq r = G r := by simp only [Gq, hidxv]
        have hb' : bq r = b r := by simp only [bq, hidxv]
        have hGs' : Gs r = SparseStateOverlap.matrixOperator (D.matrix (x, σ r)) := by
          simp only [Gs, hidxv]
        have hbs' : bsq r = bs r := by simp only [bsq, hidxv]
        have h := hterm r
        rw [hG', hb', hGs', hbs'] at *
        linarith
    _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
          ← Finset.mul_sum]

end

end ODELowerBoundExtensions.Dyson
