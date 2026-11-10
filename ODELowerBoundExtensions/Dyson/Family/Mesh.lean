import ODELowerBoundExtensions.Dyson.Degree
import SparseLowerBounds.ODE.Uniqueness
import SparseODE.ODESourceQueryBudget

set_option autoImplicit false

/-!
# Class facts used to run the Dyson solver on the ODE lower-bound class

Manuscript: Section `odel:sec:main` (the class of Theorem `odel:thm:combined`) and Lemma
`odel:lem:dyson`. The Dyson solver (`ODELowerBoundExtensions.Dyson.dyson`) needs a
positive source mass `B`, entries bounded by the public `η`, and a public mesh fine enough that
the left-endpoint source quadrature is below the certificate budget. In the class these hold:

* `mass_pos_of_inClass`: a family of the class with at least one input has `B > 0`. If
  `B = ‖x₀‖ + Σ_k len_k ‖b_k‖ = 0` then `x₀ = 0` and every stage has zero length or zero
  source, so the zero function solves every instance (`zero_solves`), and uniqueness of the
  endpoint (`Family.solves_endpoint_unique`) contradicts `x(T) ≠ 0`.
* `entry_le_of_inClass`: every entry is bounded by the row-norm bound `η` (proof of Lemma
  `odel:lem:dyson`: "Every true entry lies in the disk" `|w| ≤ η`).
* `exists_refinement`: a number `P > 0` of equal cells per stage with
  `s η (Σ_k len_k² ‖b_k‖ / P) / 2 ≤ ε B / (2000 ḡ)` (the released quadrature term,
  `Release.refine_quadrature`).
* `dysonBound_nonneg`, `dysonBound_pos`, `sourceWeight_le_total`: small bookkeeping facts.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian Set
open scoped BigOperators

section Class

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {K s : ℕ}

/-- A function has every derivative within a one-point interval `[a, a]`. -/
theorem hasDerivWithinAt_Icc_self {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℝ → V) (f' : V) (a : ℝ) : HasDerivWithinAt f f' (Icc a a) a := by
  rw [Icc_self, hasDerivWithinAt_iff_hasFDerivWithinAt]
  refine HasFDerivWithinAt.of_not_accPt ?_
  rw [accPt_iff_clusterPt, Filter.inf_principal]
  simp [ClusterPt]

/-- **Zero data force the zero solution**: if `x₀ = 0` and every stage has zero length or zero
source, the zero function solves every instance. -/
theorem zero_solves (F : SparseLowerBounds.ODE.Family X N Z K s) (h₀ : F.init = 0)
    (hk : ∀ k, F.len k = 0 ∨ F.src k = 0) (x : X) : F.Solves x (fun _ => 0) := by
  refine ⟨h₀.symm, fun k u hu => ?_⟩
  rcases hk k with hl | hb
  · have he : F.start ((k : ℕ) + 1) = F.start k := by rw [F.start_succ_fin, hl, add_zero]
    rw [he] at hu ⊢
    have hu' : u = F.start k := le_antisymm hu.2 hu.1
    subst hu'
    exact hasDerivWithinAt_Icc_self _ _ _
  · simp only [map_zero, neg_zero, zero_add, hb]
    exact hasDerivWithinAt_const _ _ _

/-- The source mass `B` is nonnegative. -/
theorem mass_nonneg (F : SparseLowerBounds.ODE.Family X N Z K s) : 0 ≤ F.mass :=
  add_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun k _ => mul_nonneg (F.len_nonneg k) (norm_nonneg _))

/-- **A family of the class with an input has positive source mass** `B > 0`. -/
theorem mass_pos_of_inClass (F : SparseLowerBounds.ODE.Family X N Z K s) {η gbar : ℝ}
    (hF : F.InClass η gbar) (x₀ : X) : 0 < F.mass := by
  rcases (mass_nonneg F).lt_or_eq with h | h
  · exact h
  exfalso
  have hsum : 0 ≤ ∑ k, F.len k * ‖F.src k‖ :=
    Finset.sum_nonneg fun k _ => mul_nonneg (F.len_nonneg k) (norm_nonneg _)
  have hinit : ‖F.init‖ = 0 := by
    have := norm_nonneg F.init; unfold SparseLowerBounds.ODE.Family.mass at h; linarith
  have hzero : ∑ k, F.len k * ‖F.src k‖ = 0 := by
    have := norm_nonneg F.init; unfold SparseLowerBounds.ODE.Family.mass at h; linarith
  have hk : ∀ k, F.len k = 0 ∨ F.src k = 0 := fun k => by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
      mul_nonneg (F.len_nonneg k) (norm_nonneg (F.src k))).mp hzero k (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (norm_eq_zero.mp h1)
  obtain ⟨sol, hsol, hne, -⟩ := hF.solution x₀
  have h0 := F.solves_endpoint_unique (zero_solves F (norm_eq_zero.mp hinit) hk x₀) hsol
  exact hne h0.symm

/-- **Entries are bounded by the row-norm bound** `η` of the class. -/
theorem entry_le_of_inClass (F : SparseLowerBounds.ODE.Family X N Z K s) {η gbar : ℝ}
    (hF : F.InClass η gbar) (hη : 0 < η) :
    ∀ y i j, ‖F.data.matrix y i j‖ ≤ η := by
  rintro ⟨x, k⟩ i j
  have h1 : ‖F.data.matrix (x, k) i j‖ ^ 2 ≤ ∑ j', ‖F.data.matrix (x, k) i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖F.data.matrix (x, k) i j'‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 := (h1.trans (hF.row_norm x k i))
  nlinarith [norm_nonneg (F.data.matrix (x, k) i j)]

/-- **A fine enough uniform refinement**: some `P > 0` cells per stage make the released source
quadrature term at most `ε B / (2000 ḡ)`. -/
theorem exists_refinement (F : SparseLowerBounds.ODE.Family X N Z K s) {η gbar ε : ℝ}
    (hη : 0 < η) (hg : 1 ≤ gbar) (hε : 0 < ε) (hB : 0 < F.mass) :
    ∃ P : ℕ, 0 < P ∧ (s : ℝ) * η * ((∑ k, F.len k ^ 2 * ‖F.src k‖) / P) / 2 ≤
      ε * F.mass / (2000 * gbar) := by
  set S := ∑ k, F.len k ^ 2 * ‖F.src k‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have hεB : 0 < ε * F.mass := mul_pos hε hB
  have hg0 : 0 < gbar := by linarith
  refine ⟨⌈2000 * gbar * s * η * S / (ε * F.mass)⌉₊ + 1, Nat.succ_pos _, ?_⟩
  set P : ℕ := ⌈2000 * gbar * s * η * S / (ε * F.mass)⌉₊ + 1 with hPdef
  have hP : (0 : ℝ) < P := by rw [hPdef]; positivity
  have hc : 2000 * gbar * s * η * S / (ε * F.mass) ≤ P := by
    rw [hPdef]; push_cast; linarith [Nat.le_ceil (2000 * gbar * s * η * S / (ε * F.mass))]
  have hc' : 2000 * gbar * s * η * S ≤ P * (ε * F.mass) := by rwa [div_le_iff₀ hεB] at hc
  have hsη : 0 ≤ (s : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) hη.le
  have hmain : (s : ℝ) * η * (S / P) ≤ ε * F.mass / (2000 * gbar) := by
    rw [mul_div_assoc', div_le_div_iff₀ hP (by positivity)]
    nlinarith
  have hnn : 0 ≤ (s : ℝ) * η * (S / P) := mul_nonneg hsη (div_nonneg hS0 hP.le)
  linarith

end Class

/-- The paper-form bound `dysonBound z g ε` is nonnegative for `z ≥ 0`, `g ≥ 1`,
`0 < ε ≤ 1`. -/
theorem dysonBound_nonneg {z g ε : ℝ} (hz : 0 ≤ z) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ dysonBound z g ε := by
  have hL := (dysonLog_pos g ε hg hε hε1).le
  have he : 1 ≤ Real.exp 1 + dysonLog g ε / z := by
    have := Real.add_one_le_exp (1 : ℝ)
    have := div_nonneg hL hz
    linarith
  have hlog : 0 ≤ Real.log (Real.exp 1 + dysonLog g ε / z) := Real.log_nonneg he
  unfold dysonBound
  have : 0 ≤ 1 + z + dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z) := by
    have := div_nonneg hL hlog
    linarith
  have hg0 : 0 ≤ 16000 * g * Real.exp z := by positivity
  exact mul_nonneg hg0 this

/-- The Dyson bound is positive for `z > 0`, `ḡ ≥ 1` and `0 < ε ≤ 1` (`dysonLog_pos`). -/
theorem dysonBound_pos {z g ε : ℝ} (hz : 0 < z) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < dysonBound z g ε := by
  have hL := dysonLog_pos g ε hg hε hε1
  have hlog : 0 < Real.log (Real.exp 1 + dysonLog g ε / z) := by
    apply Real.log_pos
    have h1 : 0 < dysonLog g ε / z := div_pos hL hz
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hq : 0 < dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z) := div_pos hL hlog
  unfold dysonBound
  exact mul_pos (mul_pos (mul_pos (by norm_num) (by linarith)) (Real.exp_pos z)) (by linarith)

/-- One source counter is at most the total source counter. -/
theorem sourceWeight_le_total {L : Type*} (b : Bool) :
    ∀ l : L ⊕ Bool, ODESourceQueryBudget.sourceWeight b l ≤
      ODESourceQueryBudget.sourceTotalWeight l := by
  rintro (l | c)
  · simp [ODESourceQueryBudget.sourceWeight, ODESourceQueryBudget.sourceTotalWeight]
  · simp only [ODESourceQueryBudget.sourceWeight, ODESourceQueryBudget.sourceTotalWeight,
      Sum.elim_inr]
    split_ifs <;> omega

end

end ODELowerBoundExtensions.Dyson
