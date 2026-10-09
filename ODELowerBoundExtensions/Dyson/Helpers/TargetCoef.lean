import ODELowerBoundExtensions.Dyson.Compile
import TimeDependentExtensions.ODE.Sampling

set_option autoImplicit false

/-!
# Helpers for the Dyson LCU target: rescaled weights and prepared sources

Auxiliary identities for `Dyson/Target.lean` (Lemma `odel:lem:dyson`, manuscript lines
4198-4214 and 4234-4245):

* `coef_mul_const`: rescaling every cell duration by `κ` multiplies the Dyson weight of a
  configuration by `κ ^ degree`;
* `truncated_eq_of_smul`: when every cell generator is `-κ` times a sample (on the cells
  `r < M` that a configuration reads), the truncated Dyson series is the signed, rescaled
  combination of the time-ordered sample products (the LCU form of lines 4208-4214);
* `norms_smul_eq_sources`: a public weight times the prepared unit source is the source vector
  of the mesh (a zero source has zero weight).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian
open TimeDependentExtensions
open scoped Nat BigOperators

/-- Rescaling every duration by `κ` multiplies the Dyson weight by `κ ^ degree`. -/
theorem coef_mul_const {K M : ℕ} (κ : ℝ) (a : ℕ → ℝ) (c : Cfg K M) :
    coef (fun r => κ * a r) c = κ ^ c.degree * coef a c := by
  unfold coef Cfg.degree
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [mul_pow]
  ring

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- **The truncated Dyson series in LCU form**: if `Y r = (-κ) • S r` on the cells `r < M`,
then `truncated a Y K M = ∑_c (coef (κ a) c (-1)^{deg c}) • cfgProduct S c`. -/
theorem truncated_eq_of_smul (a : ℕ → ℝ) (κ : ℝ) (Y S : ℕ → V →L[ℂ] V) (K M : ℕ)
    (hY : ∀ r < M, Y r = (-κ) • S r) :
    truncated a Y K M =
      ∑ c : Cfg K M, (coef (fun r => κ * a r) c * (-1) ^ c.degree) • cfgProduct S c := by
  unfold truncated
  refine Finset.sum_congr rfl fun c _ => ?_
  have h1 : cfgProduct Y c = cfgProduct (fun r => (-κ) • S r) c := by
    unfold cfgProduct
    exact evolution_congr' _ _ M (fun r hr => by
      show Y r ^ c.count r = ((-κ) • S r) ^ c.count r
      rw [hY r hr])
  rw [h1, cfgProduct_smul, smul_smul, coef_mul_const, neg_pow]
  congr 1
  ring

omit [CompleteSpace V] in
/-- A public weight times the prepared unit source is the mesh source vector: `‖y‖ •
unitDirection y = y`, and a zero source carries zero weight. -/
theorem norms_smul_eq_sources {M : ℕ} (t : ℕ → ℝ) (y0 : V) (bs : Fin M → V) (r₀ : ℝ)
    (rb : Fin M → ℝ) (h₀ : ‖y0‖ = r₀) (hbs : ∀ r, ‖bs r‖ = rb r) (w : Option (Fin M) → V)
    (hw₀ : y0 ≠ 0 → w none = ODEStateNormalization.unitDirection y0)
    (hwb : ∀ r, bs r ≠ 0 → w (some r) = ODEStateNormalization.unitDirection (bs r))
    (q : Option (Fin M)) :
    MeshSampling.norms r₀ t rb q • w q = MeshSampling.sources y0 t bs q := by
  cases q with
  | none =>
      show r₀ • w none = y0
      by_cases hy : y0 = 0
      · have hr : r₀ = 0 := by rw [← h₀, hy, norm_zero]
        rw [hr, zero_smul, hy]
      · rw [hw₀ hy, ODEStateNormalization.unitDirection, smul_smul, ← h₀,
          mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]
  | some r =>
      show ((t ((r : ℕ) + 1) - t r) * rb r) • w (some r) = (t ((r : ℕ) + 1) - t r) • bs r
      by_cases hy : bs r = 0
      · have hr : rb r = 0 := by rw [← hbs r, hy, norm_zero]
        rw [hr, mul_zero, zero_smul, hy, smul_zero]
      · rw [hwb r hy, ODEStateNormalization.unitDirection, smul_smul, ← hbs r, mul_assoc,
          mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), mul_one]

end

end ODELowerBoundExtensions.Dyson
