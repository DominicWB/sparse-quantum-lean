import TimeDependentExtensions.ODE.Theorem
import TimeDependentODE.Continuous.Existence
import TimeDependentExtensions.Mesh.Duhamel

set_option autoImplicit false

/-!
# Consequences of the general-mesh ODE solver

* `exists_piecewise_solution`: continuous pieces with breakpoints at the mesh points have a
  solution from every initial state, so the solver hypotheses are satisfiable for them.
  Solutions are classical (`SolvesODE`), so every discontinuity must be a mesh point.
* `LipschitzOutcome`, `solver_lipschitz`: piecewise Lipschitz generators and forcing with
  breakpoints at the mesh points and one-sided samples; the certified error is
  `(r₀ + b_max T) ∑_r (β_{G,r} Δ_r²/2 + δ_{G,r} Δ_r) + ∑_r (β_{b,r} Δ_r²/2 + δ_{b,r} Δ_r)`
  plus the public quadrature and refinement terms. For every such instance a solution exists.
* `publicError_le`: on a mesh of step at most `h`, the public quadrature and refinement error
  is at most `s Λ (h / 2 + M T / N) B`.
-/

namespace TimeDependentExtensions

namespace ODE

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory
open SparseHamiltonian.TimeDependentODE (ratio accuracy radius precision Index SolvesODE
  Accretive)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 3000000

/-! ### Existence across breakpoints -/

section Existence

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Existence on `[a, c]` from any initial state at `a`, for continuous coefficients. -/
theorem exists_solvesODE_from (G : ℝ → V →L[ℂ] V) (b : ℝ → V) {a c : ℝ} (hac : a ≤ c)
    (hGc : ContinuousOn G (Icc a c)) (hbc : ContinuousOn b (Icc a c)) (xa : V) :
    ∃ x : ℝ → V, x a = xa ∧ SolvesODE G b x a c := by
  have hmaps : MapsTo (fun v : ℝ => v + a) (Icc 0 (c - a)) (Icc a c) := by
    intro w hw
    exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨y, hy0, hy⟩ := TimeDependentODE.exists_solvesODE (fun u => G (u + a))
    (fun u => b (u + a)) (sub_nonneg.mpr hac)
    (hGc.comp (continuous_add_const a).continuousOn hmaps)
    (hbc.comp (continuous_add_const a).continuousOn hmaps) xa
  refine ⟨fun u => y (u - a), by simp [hy0], ?_⟩
  intro u hu
  have hmaps' : MapsTo (fun v : ℝ => v - a) (Icc a c) (Icc 0 (c - a)) := by
    intro v hv
    exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hg : HasDerivWithinAt (fun v : ℝ => v - a) 1 (Icc a c) u :=
    ((hasDerivAt_id' u).sub_const a).hasDerivWithinAt
  have h := (hy (u - a) (hmaps' hu)).scomp u hg hmaps'
  simpa only [one_smul, sub_add_cancel, Function.comp_def] using h

/-- **Existence**: continuous pieces with breakpoints at the mesh points have a solution from
every initial state. -/
theorem exists_piecewise_solution (G : ℕ → ℝ → V →L[ℂ] V) (b : ℕ → ℝ → V) {t : ℕ → ℝ}
    (ht0 : t 0 = 0) (hmono : Monotone t) (M : ℕ)
    (hGc : ∀ r < M, ContinuousOn (G r) (Icc (t r) (t (r + 1))))
    (hbc : ∀ r < M, ContinuousOn (b r) (Icc (t r) (t (r + 1)))) (x0 : V) :
    ∃ x : ℝ → V, x 0 = x0 ∧ ∀ r < M, SolvesODE (G r) (b r) x (t r) (t (r + 1)) := by
  induction M with
  | zero => exact ⟨fun _ => x0, rfl, fun r hr => absurd hr (Nat.not_lt_zero r)⟩
  | succ M ih =>
    obtain ⟨x, hx0, hx⟩ := ih (fun r hr => hGc r (by omega)) (fun r hr => hbc r (by omega))
    have hle : t M ≤ t (M + 1) := hmono (Nat.le_succ M)
    obtain ⟨y, hy0, hy⟩ := exists_solvesODE_from (G M) (b M) hle
      (hGc M (Nat.lt_succ_self M)) (hbc M (Nat.lt_succ_self M)) (x (t M))
    let w : ℝ → V := fun u => if u ≤ t M then x u else y u
    have hw0 : w 0 = x0 := by
      have h0 : (0 : ℝ) ≤ t M := by rw [← ht0]; exact hmono (Nat.zero_le M)
      simp only [w, if_pos h0, hx0]
    refine ⟨w, hw0, fun r hr => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hrM | hrM
    · have hsub : ∀ u ∈ Icc (t r) (t (r + 1)), w u = x u := by
        intro u hu
        have hu' : u ≤ t M := hu.2.trans (hmono (by omega))
        simp only [w, if_pos hu']
      intro u hu
      have h1 := (hx r hrM u hu).congr_of_mem hsub hu
      rw [hsub u hu]
      exact h1
    · subst hrM
      have hsub : ∀ u ∈ Icc (t r) (t (r + 1)), w u = y u := by
        intro u hu
        by_cases hle' : u ≤ t r
        · have hu' : u = t r := le_antisymm hle' hu.1
          rw [hu']
          simp [w, hy0]
        · simp only [w, if_neg hle']
      intro u hu
      have h1 := (hy u hu).congr_of_mem hsub hu
      rw [hsub u hu]
      exact h1

end Existence

/-! ### Piecewise Lipschitz instances -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The released complete certificate for piecewise Lipschitz instances with breakpoints at
the mesh points and one-sided samples, for one public circuit family. -/
def LipschitzOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ)
    (E : TimeDependentODE.NativeSource.SourceSpace (Index D T g ε) n M →L[ℂ]
      MeshSource.MatrixSpace (Index D T g ε) n Z M N d)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshSource.physicalOracle (ι := Index D T g ε) D N d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (bs : Fin M → EuclideanSpace ℂ n)
      (βG δG βb δb : Fin M → ℝ) (bmax : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ v ∈ Icc (t r) (t ((r : ℕ) + 1)),
        ‖G r u - G r v‖ ≤ βG r * |u - v|) →
      (∀ r : Fin M, ‖G r (t r) - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤
        δG r) →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ∀ v ∈ Icc (t r) (t ((r : ℕ) + 1)),
        ‖b r u - b r v‖ ≤ βb r * |u - v|) →
      (∀ r : Fin M, ‖b r (t r) - bs r‖ ≤ δb r) →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖b r u‖ ≤ bmax) →
      (r₀ + bmax * T) * (∑ r : Fin M, (βG r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 +
          δG r * (t ((r : ℕ) + 1) - t r))) +
        (∑ r : Fin M, (βb r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 +
          δb r * (t ((r : ℕ) + 1) - t r))) +
          publicError D t T N r₀ rb ≤ ε * MeshSampling.mass r₀ t rb / (2000 * g) →
      (∀ x0 : EuclideanSpace ℂ n, ∃ sol : ℝ → EuclideanSpace ℂ n, sol 0 = x0 ∧
        ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) ∧
      ∀ sol : ℝ → EuclideanSpace ℂ n,
        (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
        ‖sol 0‖ = r₀ → (∀ r, ‖bs r‖ = rb r) →
        (sol 0 ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection (sol 0)) →
        (∀ r, bs r ≠ 0 → Jb x r seed = ODEStateNormalization.unitDirection (bs r)) →
        sol T ≠ 0 →
        MeshSampling.mass r₀ t rb ≤ g * ‖sol T‖ →
        ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations (ratio g))
          (MeshSource.input D hM (Sum.inr false) N d
            (ODECompiledSource.seed E (coefficients D t T g ε r₀ rb) seed))
          (MeshSource.input D hM (Sum.inr false) N d ∘L
            ODECompiledSource.output E (coefficients D t T g ε r₀ rb))
          x (sol T) (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) ε

set_option maxRecDepth 8192 in
/-- **Piecewise Lipschitz generators and forcing with breakpoints.** The public trial family
of `solver` satisfies the released complete certificate for every instance with
`β_{G,r}`-Lipschitz accretive generator pieces and `β_{b,r}`-Lipschitz forcing pieces whose
one-sided samples at the left mesh points are within `δ_{G,r}`, `δ_{b,r}` of the represented
ones, under the public relative budget; a solution exists from every initial state. -/
theorem solver_lipschitz (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T g ε r₀ : ℝ) (rb : Fin M → ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius g ε * etaD)
    (hClock : 8 * s * ((etaH + radius g ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * ((etaH + radius g ε * etaD) * T)) ^ 3 ≤
      precision g ε * (N : ℝ) ^ 2)
    (h₀ : 0 ≤ r₀) (hb : ∀ r, 0 ≤ rb r) (hB : 0 < MeshSampling.mass r₀ t rb)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (J₀ : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (Jb : X → Fin M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x r, IsUnitary (Jb x r))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    LipschitzOutcome D hM t N etaH etaD T g ε r₀ rb J₀ Jb seed := by
  obtain ⟨d, E, q, hq, hAll⟩ := solver D hM t hN etaH etaD T g ε r₀ rb hH hDiss hT hg hε
    hεOne hmesh hρ hClock hCayley h₀ hb hB hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed
  refine ⟨d, E, q, hq, ?_⟩
  intro x G b bs βG δG βb δb bmax hG hGLip hGs hbLip hbs hbB hDisc
  have hle : ∀ r : Fin M, t r ≤ t ((r : ℕ) + 1) := fun r => hmesh.mono (Nat.le_succ _)
  have hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1))) := fun r =>
    continuousOn_of_lipschitz _ (hGLip r)
  have hbc : ∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1))) := fun r =>
    continuousOn_of_lipschitz _ (hbLip r)
  refine ⟨fun x0 => ?_, fun sol hsol h0 hbn hInitial hForcing hTarget hBudget => ?_⟩
  · let Gq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      G (TimeDependent.Sampled.sampleIndex hM r)
    let bq : ℕ → ℝ → EuclideanSpace ℂ n := fun r => b (TimeDependent.Sampled.sampleIndex hM r)
    obtain ⟨sol, hsol0, hsol⟩ := exists_piecewise_solution Gq bq hmesh.zero hmesh.mono M
      (fun r hr => by
        simp only [Gq, MeshSampling.sampleIndex_of_lt hM hr]
        exact hGc ⟨r, hr⟩)
      (fun r hr => by
        simp only [bq, MeshSampling.sampleIndex_of_lt hM hr]
        exact hbc ⟨r, hr⟩) x0
    refine ⟨sol, hsol0, fun r => ?_⟩
    have h := hsol r r.isLt
    simp only [Gq, bq, MeshSampling.sampleIndex_of_lt hM r.isLt] at h
    exact h
  · have hbmax : 0 ≤ bmax :=
      (norm_nonneg _).trans (hbB ⟨0, hM⟩ (t 0) ⟨le_rfl, hmesh.mono (Nat.zero_le 1)⟩)
    have hX : 0 ≤ r₀ + bmax * T := by positivity
    have hGint : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)) :=
      fun r => (hGc r).intervalIntegrable_of_Icc (hle r)
    have hbint : ∀ r : Fin M, IntervalIntegrable (b r) volume (t r) (t ((r : ℕ) + 1)) :=
      fun r => (hbc r).intervalIntegrable_of_Icc (hle r)
    have hCG : ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
        ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤
          ∑ r : Fin M, (βG r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 +
            δG r * (t ((r : ℕ) + 1) - t r)) :=
      Finset.sum_le_sum fun r _ => integral_le_of_lipschitz' _ _ (hle r) (hGLip r) (hGs r)
    have hCb : ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖ ≤
          ∑ r : Fin M, (βb r * (t ((r : ℕ) + 1) - t r) ^ 2 / 2 +
            δb r * (t ((r : ℕ) + 1) - t r)) :=
      Finset.sum_le_sum fun r _ => integral_le_of_lipschitz' _ _ (hle r) (hbLip r) (hbs r)
    have hDisc' : (r₀ + bmax * T) * (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
          ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖) +
        (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖b r u - bs r‖) +
          publicError D t T N r₀ rb ≤ ε * MeshSampling.mass r₀ t rb / (2000 * g) := by
      have h1 := mul_le_mul_of_nonneg_left hCG hX
      linarith
    exact hAll x G b sol bs bmax hG hGint hbint hbB hsol h0 hbn hInitial hForcing hTarget
      hBudget hDisc'

/-! ### The public part of the budget -/

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Public error on a mesh of step at most `h`.** If every mesh interval has length at most
`h`, then `publicError ≤ s Λ (h / 2 + M T / N) B` with `B` the public source mass; for example
`s Λ (h / 2 + M T / N) ≤ ε / (4000 g)` leaves half of the budget `ε B / (2000 g)` for the
integrated certificates. -/
theorem publicError_le (D : Data (X × Fin M) n Z s) {t : ℕ → ℝ} (T : ℝ) (N : ℕ) {r₀ : ℝ}
    {rb : Fin M → ℝ} {h : ℝ} (hmono : Monotone t)
    (hstep : ∀ q : Fin M, t ((q : ℕ) + 1) - t q ≤ h) (hh : 0 ≤ h) (h₀ : 0 ≤ r₀)
    (hb : ∀ q, 0 ≤ rb q) :
    publicError D t T N r₀ rb ≤
      (s : ℝ) * D.scale * (h / 2 + M * (T / N)) * MeshSampling.mass r₀ t rb := by
  have hΔ : ∀ q : Fin M, 0 ≤ t ((q : ℕ) + 1) - t q := fun q =>
    sub_nonneg.mpr (hmono (Nat.le_succ _))
  have hsum : ∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q ≤
      h * ∑ q : Fin M, (t ((q : ℕ) + 1) - t q) * rb q := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    have h1 := mul_le_mul_of_nonneg_right (hstep q) (mul_nonneg (hΔ q) (hb q))
    calc (t ((q : ℕ) + 1) - t q) ^ 2 * rb q =
          (t ((q : ℕ) + 1) - t q) * ((t ((q : ℕ) + 1) - t q) * rb q) := by ring
      _ ≤ h * ((t ((q : ℕ) + 1) - t q) * rb q) := h1
  have hsrc : ∑ q : Fin M, (t ((q : ℕ) + 1) - t q) * rb q ≤ MeshSampling.mass r₀ t rb := by
    unfold MeshSampling.mass
    linarith
  have hmass := hsum.trans (mul_le_mul_of_nonneg_left hsrc hh)
  have hsΛ : 0 ≤ (s : ℝ) * D.scale := mul_nonneg (Nat.cast_nonneg _) D.scale_pos.le
  unfold publicError
  calc (s : ℝ) * D.scale * ((∑ q : Fin M, (t ((q : ℕ) + 1) - t q) ^ 2 * rb q) / 2 +
        M * (T / N) * MeshSampling.mass r₀ t rb) ≤
      (s : ℝ) * D.scale * (h * MeshSampling.mass r₀ t rb / 2 +
        M * (T / N) * MeshSampling.mass r₀ t rb) := by
        apply mul_le_mul_of_nonneg_left _ hsΛ
        linarith
    _ = (s : ℝ) * D.scale * (h / 2 + M * (T / N)) * MeshSampling.mass r₀ t rb := by ring

end

end ODE

end TimeDependentExtensions
