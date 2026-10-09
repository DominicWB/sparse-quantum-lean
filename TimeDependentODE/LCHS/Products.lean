import TimeDependentODE.LCHS.GaussianFull
import TimeDependentHamiltonian.Chronology.Products

/-!
# Ordered products of complex-frequency slot evolutions

For slot data `Hs r`, `Ds r` and durations `τ r`, the family

  `productFamily Hs Ds τ M z = U (M-1) z ⋯ U 0 z`,
  `U r z = ODEComplexFrequency.evolution (Ds r) (Hs r) (τ r) z
         = exp (τ r • (-I • (Hs r + z • Ds r)))`,

is the time-ordered product of the complex-frequency continuations of the
LCHS slot propagators. This file proves that it satisfies every hypothesis
of the generic Gaussian LCHS theorem `truncated_error` and of the public
table construction:

* it is entire (`productFamily_analyticAt`);
* it is a contraction on the closed lower half-plane when every slot has a
  self-adjoint pair `Hs r`, `Ds r` with `Ds r` positive and a nonnegative
  duration (`productFamily_norm_le_one`);
* at the pole `-I` it is the ordered product of the dissipative slot
  propagators `exp (τ r • (-(Ds r + I • Hs r)))` (`productFamily_neg_I`);
* on the real frequency axis it is the ordered product of the real LCHS
  branches (`productFamily_ofReal`), and it is Lipschitz there with constant
  `∑ r < M, τ r * ‖Ds r‖`, independent of the Hamiltonian parts
  (`productFamily_lipschitz`).
-/

namespace SparseHamiltonian.TimeDependentODE.GaussianLCHS

noncomputable section
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- The ordered product of complex-frequency slot evolutions with nonnegative durations `τ r`. -/
def productFamily (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (M : ℕ) (z : ℂ) : V →L[ℂ] V :=
  TimeDependent.evolution (fun r => ODEComplexFrequency.evolution (Ds r) (Hs r) (τ r) z) M

omit [CompleteSpace V] in
/-- The empty ordered product is the identity. -/
@[simp] theorem productFamily_zero (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (z : ℂ) :
    productFamily Hs Ds τ 0 z = 1 :=
  TimeDependent.evolution_zero _

omit [CompleteSpace V] in
/-- Each new slot acts after all earlier ones. -/
theorem productFamily_succ (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (M : ℕ) (z : ℂ) :
    productFamily Hs Ds τ (M + 1) z =
      ODEComplexFrequency.evolution (Ds M) (Hs M) (τ M) z * productFamily Hs Ds τ M z :=
  TimeDependent.evolution_succ _ M

/-- The ordered product is entire: each factor is entire and the product of
two analytic operator-valued functions is analytic. -/
theorem productFamily_analyticAt (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (M : ℕ) (z : ℂ) :
    AnalyticAt ℂ (productFamily Hs Ds τ M) z := by
  induction M with
  | zero =>
      have hZero : productFamily Hs Ds τ 0 = fun _ => (1 : V →L[ℂ] V) :=
        funext fun ζ => productFamily_zero Hs Ds τ ζ
      rw [hZero]
      exact analyticAt_const
  | succ M ih =>
      have hSucc : productFamily Hs Ds τ (M + 1) =
          ODEComplexFrequency.evolution (Ds M) (Hs M) (τ M) * productFamily Hs Ds τ M :=
        funext fun ζ => productFamily_succ Hs Ds τ M ζ
      rw [hSucc]
      exact (ODEComplexFrequency.evolution_analyticAt (Ds M) (Hs M) (τ M) z).mul ih

/-- Below the real axis every slot factor is a contraction, hence so is the
ordered product. -/
theorem productFamily_norm_le_one (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (M : ℕ)
    (hH : ∀ r, star (Hs r) = Hs r) (hD : ∀ r, star (Ds r) = Ds r)
    (hPSD : ∀ r (v : V), 0 ≤ (inner ℂ v (Ds r v)).re) (hτ : ∀ r, 0 ≤ τ r)
    (z : ℂ) (hz : z.im ≤ 0) : ‖productFamily Hs Ds τ M z‖ ≤ 1 :=
  TimeDependent.evolution_norm_le_one _
    (fun r => ODEComplexFrequency.evolution_norm_le_one (Ds r) (Hs r) (hD r) (hH r)
      (hPSD r) (τ r) (hτ r) z hz) M

omit [CompleteSpace V] in
/-- At the pole `-I` the product is the ordered product of the dissipative
slot propagators. -/
theorem productFamily_neg_I (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (M : ℕ) :
    productFamily Hs Ds τ M (-Complex.I) =
      TimeDependent.evolution
        (fun r => NormedSpace.exp (τ r • (-(Ds r + Complex.I • Hs r)))) M := by
  unfold productFamily
  congr 1
  funext r
  exact ODEComplexFrequency.evolution_neg_I (Ds r) (Hs r) (τ r)

omit [CompleteSpace V] in
/-- On the real frequency axis the product is the ordered product of the real
LCHS branches. -/
theorem productFamily_ofReal (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (M : ℕ) (k : ℝ) :
    productFamily Hs Ds τ M (k : ℂ) =
      TimeDependent.evolution
        (fun r => ODEWeightedLCHS.evolution (Ds r) (Hs r) (τ r) k) M := by
  unfold productFamily
  congr 1
  funext r
  exact ODEComplexFrequency.evolution_ofReal (Ds r) (Hs r) (τ r) k

/-- Real-axis Lipschitz bound: the factors there are contractions, so the
product differences telescope, and each slot costs only `τ r * ‖Ds r‖`. -/
theorem productFamily_lipschitz (Hs Ds : ℕ → V →L[ℂ] V) (τ : ℕ → ℝ) (M : ℕ)
    (hH : ∀ r, star (Hs r) = Hs r) (hD : ∀ r, star (Ds r) = Ds r)
    (hτ : ∀ r, 0 ≤ τ r) (k l : ℝ) :
    ‖productFamily Hs Ds τ M (k : ℂ) - productFamily Hs Ds τ M (l : ℂ)‖ ≤
      (∑ r ∈ Finset.range M, τ r * ‖Ds r‖) * |k - l| := by
  rw [productFamily_ofReal, productFamily_ofReal]
  calc
    _ ≤ ∑ r ∈ Finset.range M, ‖ODEWeightedLCHS.evolution (Ds r) (Hs r) (τ r) k -
          ODEWeightedLCHS.evolution (Ds r) (Hs r) (τ r) l‖ :=
      TimeDependent.evolution_sub_norm_le _ _
        (fun r => ODEWeightedLCHS.evolution_norm_le_one (Ds r) (Hs r) (hD r) (hH r) (τ r) k)
        (fun r => ODEWeightedLCHS.evolution_norm_le_one (Ds r) (Hs r) (hD r) (hH r) (τ r) l) M
    _ ≤ ∑ r ∈ Finset.range M, τ r * ‖Ds r‖ * |k - l| := by
      apply Finset.sum_le_sum
      intro r _
      have h := ODEWeightedLCHS.frequency_error (Ds r) (Hs r) (hD r) (hH r) (τ r) k l
      rwa [abs_of_nonneg (hτ r)] at h
    _ = (∑ r ∈ Finset.range M, τ r * ‖Ds r‖) * |k - l| := by
      rw [Finset.sum_mul]

end
end SparseHamiltonian.TimeDependentODE.GaussianLCHS
