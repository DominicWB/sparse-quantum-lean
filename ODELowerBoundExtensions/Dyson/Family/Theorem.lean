import ODELowerBoundExtensions.Dyson.Family.Transport
import ODELowerBoundExtensions.Dyson.Family.Rescale
import ODELowerBoundExtensions.Dyson.Family.Mesh
import ODELowerBoundExtensions.Dyson.Family.Sources
import ODELowerBoundExtensions.Release.Refine
import ODELowerBoundExtensions.Release.Instances
import SparseLowerBounds.ODE.Uniqueness

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The Dyson solver on the ODE lower-bound class (Certificate layer)

Manuscript: eq. `odel:eq:fixed` and its consequence, "Consequently a uniform worst-case lower bound
proportional to `ḡ √s τ log(ḡ/ε)` is false under these access assumptions: fixing any admissible
positive `s, τ, ḡ` makes this comparison upper bound sublinear in `log(1/ε)`. A constant-coefficient
upper bound alone would not exclude such a worst-case assertion for the larger time-dependent class;
Lemma `odel:lem:dyson` is included precisely to cover that class."

The class is that of Theorem `odel:thm:combined` (`SparseLowerBounds.ODE.Family`,
`Family.InClass η ḡ`): piecewise-constant generators with known breakpoints,
row/column norms at most `η`, public sources, `B ≤ ḡ ‖x(T)‖`, and the sampled-time access
`Family.access ι`.

* `family_dyson`: every family in the class with `T > 0` has a release-style four-trial
  protocol that satisfies the released complete certificate `ODECompleteTrial.Certificate` for
  every instance, with worst-case matrix queries at most `dysonBound (s η T) ḡ ε` (eq.
  `odel:eq:dyson` at `z = s η T`). The certificate is stated for programs over
  `ODESourceQueryBudget.oracle (F.access ι) (fun _ _ => 1)`: the released certificate needs the
  label type `Query ⊕ Bool` (matrix and source counters), and the source vocabulary is idle
  (identity, never called).
  Proof: `dyson` on `NativeBandEncoding.tail F.data η` (`tail_matrix_of_le`, `Λ = η`), the stage
  breakpoints refined into `P` equal cells per stage with the public stage map `σ` (exact
  samples, quadrature term `s η ∑_k len_k² ‖b_k‖/(2P)`, `P` public and large), public source
  interfaces (`Release.prepUnitary`), then the transport `Family/Transport.lean` with public
  sources (`exists_sourceFree`, `Family/Sources.lean`); the class facts (`B > 0`, entry bound,
  choice of `P`) are in `Family/Mesh.lean`. No positivity of `B` is assumed: a
  family without inputs has a vacuous certificate, and a family of the class with an input has
  `B > 0` (zero data force `x(T) = 0`, `Family.solves_endpoint_unique`, against `x(T) ≠ 0`).

`Family/Retry.lean` removes the idle source vocabulary (`Release/Strip.lean`) and states the
consequence in the vocabulary of the retry-protocol lower bound
(`ODELowerBoundExtensions.Release.RetrySolver`, `RetryWitnesses`).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators

set_option maxHeartbeats 4000000 in
/-- **The Dyson solver on every family of the ODE lower-bound class** (Lemma `odel:lem:dyson`,
applied to the class of `odel:thm:combined`): a public four-trial protocol over the lower-bound
access (idle source vocabulary) satisfying the released complete certificate for every instance,
with worst-case matrix queries at most `dysonBound (s η T) ḡ ε`. -/
theorem family_dyson {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {K s : ℕ} (F : SparseLowerBounds.ODE.Family X N Z K s) (η gbar ε : ℝ)
    (hF : F.InClass η gbar) (hη : 0 < η) (hT : 0 < F.T) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι)
      (q : ℕ → MultiOracleCircuit.Program
        (ODESourceQueryBudget.oracle (F.access ι) (fun _ _ => 1)))
      (M : ℕ) (ψ : SparseLowerBounds.ODE.Workspace ι N Z K)
      (out : EuclideanSpace ℂ N →L[ℂ] SparseLowerBounds.ODE.Workspace ι N Z K) (g' ell : ℝ),
      1274019840 * g' * ImprovedODEQueryBudget.queryShape (s : ℝ) 0 ell ≤
          dysonBound ((s : ℝ) * η * F.T) gbar ε ∧
        ∀ x sol, F.Solves x sol →
          ODECompleteTrial.Certificate q M ψ out x (sol F.T) (s : ℝ) 0 ell g' ε := by
  classical
  have hz : 0 ≤ (s : ℝ) * η * F.T := by positivity
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · -- No input: the certificate clause is vacuous.
    refine ⟨PUnit, inferInstance, fun _ => MultiOracleCircuit.Program.identity, 0, 0, 0, 0, 0,
      ?_, fun x => isEmptyElim x⟩
    simpa using dysonBound_nonneg hz hg hε hε1
  -- An input exists: `B > 0`, `K > 0`, `N` is inhabited.
  have hB := mass_pos_of_inClass F hF x₀
  obtain ⟨sol₀, -, hne₀, -⟩ := hF.solution x₀
  obtain ⟨i₀, -⟩ : ∃ i, sol₀ F.T i ≠ 0 := by
    by_contra h
    exact hne₀ (by ext i; simpa using not_exists.mp h i)
  have hK : 0 < K := Nat.pos_of_ne_zero fun h => by
    subst h; simp [SparseLowerBounds.ODE.Family.T_eq_sum] at hT
  obtain ⟨P, hP, hquad⟩ := exists_refinement F hη hg hε hB
  have hDmat := tail_matrix_of_le F.data η hη (entry_le_of_inClass F hF hη)
  -- The Dyson solver on the refined mesh with the public stage map and public sources.
  obtain ⟨hbound, q, ψ, Fo, -, hcert⟩ := dyson (NativeBandEncoding.tail F.data η hη)
    (Nat.mul_pos hK hP) (Release.stageOf K P) (Release.refineFamily F P).start F.T gbar ε
    ‖F.init‖ (fun r => ‖(Release.refineFamily F P).src r‖) (Release.refine_isMesh F P hP) hT
    hg hε hε1 (norm_nonneg _) (fun _ => norm_nonneg _)
    (by rw [Release.refine_meshMass F P hP]; exact hB)
    (fun _ => Release.prepUnitary i₀ F.init)
    (fun _ r => Release.prepUnitary i₀ ((Release.refineFamily F P).src r))
    (fun _ => Release.prepUnitary_unitary _ _) (fun _ _ => Release.prepUnitary_unitary _ _)
    (Release.seedVec i₀) (Release.norm_seedVec i₀)
  obtain ⟨q', ψ', out', htr⟩ := exists_sourceFree F (NativeBandEncoding.tail F.data η hη)
    (NativeBandEncoding.tail_oracles F.data η hη)
    (dysonDegree (NativeBandEncoding.tail F.data η hη) F.T gbar ε) (K * P)
    (Release.prepUnitary i₀ F.init)
    (fun r => Release.prepUnitary i₀ ((Release.refineFamily F P).src r))
    (Release.prepUnitary_unitary _ _) (fun _ => Release.prepUnitary_unitary _ _) q ψ Fo
  refine ⟨Spectator K N Z (dysonDegree (NativeBandEncoding.tail F.data η hη) F.T gbar ε) (K * P),
    inferInstance, q',
    ODEGroverAverage.chosenIterations (ampFactor (NativeBandEncoding.tail F.data η hη)
      (Release.refineFamily F P).start F.T gbar ε ‖F.init‖
      (fun r => ‖(Release.refineFamily F P).src r‖)),
    ψ', out',
    ampFactor (NativeBandEncoding.tail F.data η hη) (Release.refineFamily F P).start F.T gbar ε
      ‖F.init‖ (fun r => ‖(Release.refineFamily F P).src r‖),
    shapeLength (NativeBandEncoding.tail F.data η hη) F.T gbar ε, hbound, ?_⟩
  intro x sol hs
  obtain ⟨sol', hsol', hne', hmass'⟩ := hF.solution x
  have hend := F.solves_endpoint_unique hs hsol'
  have hscale : (NativeBandEncoding.tail F.data η hη).scale = η := rfl
  have hc := hcert x (fun r _ => (Release.refineFamily F P).gen x r)
    (fun r _ => (Release.refineFamily F P).src r) sol (fun r => (Release.refineFamily F P).src r)
    (∑ k, ‖F.src k‖) (fun r _ _ => hF.accretive x (Release.stageOf K P r))
    (fun r => by rw [hDmat]; exact hF.accretive x _)
    (fun _ => intervalIntegrable_const) (fun _ => intervalIntegrable_const)
    (fun r _ _ => Finset.single_le_sum (f := fun k => ‖F.src k‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _))
    (fun r => Release.refine_solves F P hs r) (by rw [hs.1]) (fun _ => rfl)
    (fun h => by rw [hs.1] at h ⊢; exact Release.prepUnitary_seed i₀ h)
    (fun r h => Release.prepUnitary_seed i₀ h)
    (by rw [Release.refine_meshMass F P hP, hend]; exact hmass') (by
      beta_reduce
      simp only [Release.refineFamily_gen]
      simp only [hDmat, hscale, Release.refine_meshMass F P hP, Release.refine_quadrature F P,
        SparseLowerBounds.ODE.Family.gen, sub_self, norm_zero, intervalIntegral.integral_zero,
        Finset.sum_const_zero, mul_zero, zero_add]
      exact hquad)
  have hsolT : sol F.T ≠ 0 := by rw [hend]; exact hne'
  exact htr _ x (sol F.T) hsolT _ _ _ _ ε hε.le hc

end

end ODELowerBoundExtensions.Dyson
