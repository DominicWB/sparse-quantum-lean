import GateEfficientODE.Time.Agree
import GateEfficientODE.Analysis.Words

/-!
# The padded LCHS table of the time-dependent solver

The analytic Gaussian table with ratio `2 g` and accuracy `ε / 2` occupies the
words of value `0, …, J + 1` of the `l` LCHS wires.  As in the
constant-coefficient solver, the padded coefficients have mass exactly three
(`coeffW_mass`), the label amplitudes are normalised (`lchAmp_sq_sum`), every
node lies in `[-R, R]` (`nodeW_abs_le`), and coefficient-weighted sums over
words are the table sums (`coeffW_sum`).
-/

namespace SparseHamiltonian.GateODE.Time

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GatePointerEncoding (wordValue wordValue_lt_pow wordEquivFin wordFin)
open scoped InnerProduct BigOperators

namespace TParams

variable (p : TParams)

theorem ratio_ge (hg : 1 ≤ p.g) : 1 ≤ p.ratio := by
  unfold ratio; linarith

theorem acc_pos (hε : 0 < p.ε) : 0 < p.acc := by
  unfold acc; linarith

theorem acc_le_one (hεOne : p.ε ≤ 1) : p.acc ≤ 1 := by
  unfold acc; linarith

/-- The analytic Gaussian table has mass at most three. -/
theorem table_mass_le (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) :
    ODECoherentLCU.coefficientMass
      (AnalyticLCHS.coefficients (p.T * p.lamD) p.ratio p.acc) ≤ 3 :=
  AnalyticLCHS.mass_le hTD (p.ratio_ge hg) (p.acc_pos hε) (p.acc_le_one hεOne)

theorem coeffW_sum_eq {M : Type*} [AddCommMonoid M] (g : Fin p.J ⊕ Bool → M) :
    ∑ w : Fin p.l → Bool, (padIdx p.J (wordValue w)).elim 0 g = ∑ i, g i :=
  sum_padIdx p.J p.l p.J_add_two_le g

/-- The padded coefficients on words have mass exactly three. -/
theorem coeffW_mass (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) :
    ODECoherentLCU.coefficientMass p.coeffW = 3 := by
  unfold ODECoherentLCU.coefficientMass coeffW
  simp only [norm_elim]
  rw [p.coeffW_sum_eq]
  exact ODECoefficientPadding.coefficientMass_eq _ 3 (p.table_mass_le hg hε hεOne hTD)

theorem lchAmp_nonneg (w : Fin p.l → Bool) : 0 ≤ p.lchAmp w := Real.sqrt_nonneg _

theorem lchAmp_sq (w : Fin p.l → Bool) : p.lchAmp w ^ 2 = ‖p.coeffW w‖ / 3 :=
  Real.sq_sqrt (by positivity)

/-- The LCHS label amplitudes are normalised. -/
theorem lchAmp_sq_sum (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) : ∑ w, p.lchAmp w ^ 2 = 1 := by
  simp only [p.lchAmp_sq]
  rw [← Finset.sum_div]
  have h := p.coeffW_mass hg hε hεOne hTD
  unfold ODECoherentLCU.coefficientMass at h
  rw [h]
  norm_num

/-- Every node lies in the public frequency interval. -/
theorem nodeW_abs_le (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD)
    (w : Fin p.l → Bool) : |p.nodeW w| ≤ p.R := by
  have hR : 0 ≤ p.R := ImprovedODEQueryBudget.radius_nonneg p.ratio p.acc (p.ratio_ge hg)
    (p.acc_pos hε) (p.acc_le_one hεOne)
  unfold nodeW
  cases hw : padIdx p.J (wordValue w) with
  | none => simpa using hR
  | some i =>
      cases i with
      | inl i =>
          exact AnalyticLCHS.nodes_abs_le hTD (p.ratio_ge hg) (p.acc_pos hε)
            (p.acc_le_one hεOne) i
      | inr b => simpa [ODECoefficientPadding.paddedNodes] using hR

/-- The coefficient-weighted sum of a family over the words is the Gaussian
table sum. -/
theorem coeffW_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (F : ℝ → V) :
    ∑ w, p.coeffW w • F (p.nodeW w) =
      ∑ i, AnalyticLCHS.coefficients (p.T * p.lamD) p.ratio p.acc i •
        F (AnalyticLCHS.nodes (p.T * p.lamD) p.ratio p.acc i) := by
  have e : ∀ w, p.coeffW w • F (p.nodeW w) = (padIdx p.J (wordValue w)).elim 0
      (fun i => ODECoefficientPadding.paddedCoefficient
        (AnalyticLCHS.coefficients (p.T * p.lamD) p.ratio p.acc) 3 i •
        F (ODECoefficientPadding.paddedNodes
          (AnalyticLCHS.nodes (p.T * p.lamD) p.ratio p.acc) i)) := by
    intro w
    unfold coeffW nodeW
    cases padIdx p.J (wordValue w) <;> simp
  simp only [e]
  rw [p.coeffW_sum_eq]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, ODECoefficientPadding.paddedCoefficient,
    ODECoefficientPadding.paddedNodes, neg_smul, neg_add_cancel, add_zero]

end TParams

end

end SparseHamiltonian.GateODE.Time
