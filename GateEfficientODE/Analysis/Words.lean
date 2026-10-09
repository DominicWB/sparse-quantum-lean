import GateEfficientODE.Circuit.Agree

/-!
# The padded LCHS table on label words

The `J` analytic-grid labels and the two padding labels occupy the words of value
`0, …, J + 1` of the `l` LCHS wires; all other words carry coefficient zero.
Sums over words therefore reduce to sums over the padded labels
(`sum_padIdx`).  The padded coefficients have mass exactly three
(`coeffW_mass`), so the amplitudes `sqrt(|c_w| / 3)` of the LCHS label
register are normalised (`lchAmp_sq_sum`), every node lies in `[-R, R]`
(`nodeW_abs_le`), and the weighted sum of any family over words is the
analytic table sum (`coeffW_sum`).
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GatePointerEncoding (wordValue wordValue_lt_pow wordEquivFin wordFin)
open scoped InnerProduct BigOperators

/-- Sums over the words reduce to sums over the padded labels. -/
theorem sum_padIdx {M : Type*} [AddCommMonoid M] (J l : ℕ) (hJ : J + 2 ≤ 2 ^ l)
    (g : Fin J ⊕ Bool → M) :
    ∑ w : Fin l → Bool, (padIdx J (wordValue w)).elim 0 g = ∑ i, g i := by
  have h1 : ∑ w : Fin l → Bool, (padIdx J (wordValue w)).elim 0 g =
      ∑ n : Fin (2 ^ l), (padIdx J n).elim 0 g :=
    Fintype.sum_equiv (wordEquivFin l) _ _ (fun w => rfl)
  rw [h1, Fin.sum_univ_eq_sum_range (fun n => (padIdx J n).elim 0 g) (2 ^ l)]
  have h3 : ∑ n ∈ Finset.range (2 ^ l), (padIdx J n).elim 0 g =
      ∑ n ∈ Finset.range (J + 2), (padIdx J n).elim 0 g := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr hJ) ?_).symm
    intro n hn hn'
    simp only [Finset.mem_range, not_lt] at hn hn'
    unfold padIdx
    rw [dif_neg (by omega), if_neg (by omega), if_neg (by omega)]
    rfl
  rw [h3, Finset.sum_range_succ, Finset.sum_range_succ,
    ← Fin.sum_univ_eq_sum_range (fun n => (padIdx J n).elim 0 g) J,
    Fintype.sum_sum_type, Fintype.sum_bool]
  have hl : ∀ i : Fin J, (padIdx J i).elim 0 g = g (Sum.inl i) := by
    intro i
    unfold padIdx
    rw [dif_pos i.isLt]
    rfl
  have hJ0 : (padIdx J J).elim 0 g = g (Sum.inr false) := by
    unfold padIdx
    rw [dif_neg (lt_irrefl J), if_pos rfl]
    rfl
  have hJ1 : (padIdx J (J + 1)).elim 0 g = g (Sum.inr true) := by
    unfold padIdx
    rw [dif_neg (by omega), if_neg (by omega), if_pos rfl]
    rfl
  simp only [hl, hJ0, hJ1]
  abel

theorem norm_elim {M : Type*} [SeminormedAddCommGroup M] {ι : Type*} (o : Option ι)
    (g : ι → M) : ‖o.elim 0 g‖ = o.elim 0 (fun i => ‖g i‖) := by
  cases o <;> simp

theorem smul_elim {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V] (o : Option ι)
    (c : ι → ℂ) (x : ι → V) : o.elim (0 : ℂ) c • o.elim (0 : V) x =
      o.elim 0 (fun i => c i • x i) := by
  cases o <;> simp

namespace Params

variable (p : Params)

/-- The analytic Gaussian table has mass at most three. -/
theorem table_mass_le (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1) (hTD : 0 ≤ p.T * p.lamD) :
    ODECoherentLCU.coefficientMass
      (AnalyticLCHS.coefficients (p.T * p.lamD) p.g p.ε) ≤ 3 :=
  AnalyticLCHS.mass_le hTD hg hε hεOne

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
  have hR : 0 ≤ p.R := ImprovedODEQueryBudget.radius_nonneg p.g p.ε hg hε hεOne
  unfold nodeW
  cases hw : padIdx p.J (wordValue w) with
  | none => simpa using hR
  | some i =>
      cases i with
      | inl i => exact AnalyticLCHS.nodes_abs_le hTD hg hε hεOne i
      | inr b => simpa [ODECoefficientPadding.paddedNodes] using hR

/-- The coefficient-weighted sum of a family over the words is the Gaussian
table sum. -/
theorem coeffW_sum {V : Type*} [AddCommGroup V] [Module ℂ V] (F : ℝ → V) :
    ∑ w, p.coeffW w • F (p.nodeW w) =
      ∑ i, AnalyticLCHS.coefficients (p.T * p.lamD) p.g p.ε i •
        F (AnalyticLCHS.nodes (p.T * p.lamD) p.g p.ε i) := by
  have e : ∀ w, p.coeffW w • F (p.nodeW w) = (padIdx p.J (wordValue w)).elim 0
      (fun i => ODECoefficientPadding.paddedCoefficient
        (AnalyticLCHS.coefficients (p.T * p.lamD) p.g p.ε) 3 i •
        F (ODECoefficientPadding.paddedNodes
          (AnalyticLCHS.nodes (p.T * p.lamD) p.g p.ε) i)) := by
    intro w
    unfold coeffW nodeW
    cases padIdx p.J (wordValue w) <;> simp
  simp only [e]
  rw [p.coeffW_sum_eq]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, ODECoefficientPadding.paddedCoefficient,
    ODECoefficientPadding.paddedNodes, neg_smul, neg_add_cancel, add_zero]

end Params

end

end SparseHamiltonian.GateODE
