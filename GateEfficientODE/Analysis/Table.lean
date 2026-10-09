import GateEfficientODE.Analysis.Select

/-!
# LCHS and source quadrature for the gate-level solver

For the equation `x' = A x + b` with `A = -(L + iH)`, `L ≥ 0`:

* `lchs_error`: for every source label `s`, the padded word table applied to
  the branch evolutions of duration `dur s` is within `2ν` of the dissipative
  propagator `exp(dur s · A)`.  This is the analytic grid of
  `AnalyticLCHS.table_certificate` for the contractive entire family
  `z ↦ exp(-i dur s (H + z L))`, which grows at most like `exp (T λD Im z)`
  above the real axis (`AnalyticLCHS.evolution_norm_le_exp`).
* `quadrature_error`: the propagated source vectors sum to the released
  left-endpoint quadrature of the Duhamel integral with `2^k` nodes, within
  `ν B` of the solution, because `2^k ≥ T (λH + λD) / ν`.
* `solution_le_mass`: the solution norm is at most the source mass `B`.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire)
open GatePointerEncoding (wordValue wordValue_lt_pow wordEquivFin)
open scoped InnerProduct BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The ODE generator `A = -(L + iH)`. -/
def gen (H L : P →L[ℂ] P) : P →L[ℂ] P := -(L + Complex.I • H)

theorem gen_dissipative (H L : P →L[ℂ] P) (hH : star H = H) (hL : star L = L)
    (hPSD : ∀ w : P, 0 ≤ (inner ℂ w (L w)).re) : ODEDissipative.Dissipative (gen H L) := by
  have h := ODEComplexFrequency.generator_dissipative L H hL hH hPSD (-Complex.I) (by simp)
  rwa [ODEComplexFrequency.generator_neg_I] at h

namespace Params

variable (p : Params)

/-- The dissipative propagator of a source label. -/
def propS (H L : P →L[ℂ] P) (s : Bool × (Fin p.k → Bool)) : P →L[ℂ] P :=
  NormedSpace.exp (p.dur s • gen H L)

/-- **Finite LCHS on the padded word table.** -/
theorem lchs_error (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεOne : p.ε ≤ 1)
    (hTD : 0 ≤ p.T * p.lamD) (H L : P →L[ℂ] P) (hH : star H = H) (hL : star L = L)
    (hLn : ‖L‖ ≤ p.lamD) (hPSD : ∀ w : P, 0 ≤ (inner ℂ w (L w)).re)
    (s : Bool × (Fin p.k → Bool)) :
    ‖(∑ w, p.coeffW w • p.branchU H L s w) - p.propS H L s‖ ≤ 2 * p.nu := by
  have hlam : 0 ≤ p.lamD := (norm_nonneg L).trans hLn
  have hcert := AnalyticLCHS.table_certificate
    (fun (y : Bool × (Fin p.k → Bool)) (z : ℂ) => ODEComplexFrequency.evolution L H (p.dur y) z)
    (fun y z => ODEComplexFrequency.evolution_analyticAt L H (p.dur y) z)
    (fun y z hz => ODEComplexFrequency.evolution_norm_le_one L H hL hH hPSD (p.dur y)
      (p.dur_nonneg hT y) z hz)
    (p.T * p.lamD) hTD
    (fun y z hz => by
      refine (AnalyticLCHS.evolution_norm_le_exp L H hL hH p.lamD hLn (p.dur y)
        (p.dur_nonneg hT y) z hz).trans (Real.exp_le_exp.mpr ?_)
      have h1 := p.dur_le hT y
      have h2 : 0 ≤ p.lamD * z.im := mul_nonneg hlam hz
      have h3 := mul_le_mul_of_nonneg_right h1 h2
      linarith)
    p.g p.ε hg hε hεOne
  have hsum : ∑ w, p.coeffW w • p.branchU H L s w =
      ∑ i, AnalyticLCHS.coefficients (p.T * p.lamD) p.g p.ε i •
        ODEComplexFrequency.evolution L H (p.dur s)
          (AnalyticLCHS.nodes (p.T * p.lamD) p.g p.ε i : ℂ) := by
    have h := p.coeffW_sum (fun κ : ℝ => ODEWeightedLCHS.evolution L H (p.dur s) κ)
    simp only [branchU]
    rw [h]
    apply Finset.sum_congr rfl
    intro i _
    rw [ODEComplexFrequency.evolution_ofReal]
  have hS : p.propS H L s = ODEComplexFrequency.evolution L H (p.dur s) (-Complex.I) := by
    rw [ODEComplexFrequency.evolution_neg_I]
    rfl
  rw [hsum, hS]
  exact hcert.2.2.2 s

/-! ### The source quadrature -/

theorem two_pow_k (hν : 0 < p.nu) : p.T * (p.lamH + p.lamD) ≤ p.nu * 2 ^ p.k := by
  have h1 : p.T * (p.lamH + p.lamD) / p.nu ≤ ⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ :=
    Nat.le_ceil _
  have h2 : ⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ ≤ 2 ^ p.k := Nat.le_pow_clog (by norm_num) _
  have h3 : (⌈p.T * (p.lamH + p.lamD) / p.nu⌉₊ : ℝ) ≤ 2 ^ p.k := by exact_mod_cast h2
  have h4 := h1.trans h3
  rw [div_le_iff₀ hν] at h4
  linarith

theorem sum_words_eq {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ s : Fin p.k → Bool, F (wordValue s) = ∑ i : Fin (2 ^ p.k), F i :=
  Fintype.sum_equiv (wordEquivFin p.k) _ _ (fun _ => rfl)

omit [CompleteSpace P] in
theorem smul_ofReal (r : ℝ) (v : P) : ((r : ℝ) : ℂ) • v = r • v := (Complex.coe_smul r v)

omit [CompleteSpace P] in
/-- The propagated source vectors sum to the released left-endpoint quadrature. -/
theorem source_sum_eq (H L : P →L[ℂ] P) (x0 b : P) :
    ∑ s, p.propS H L s (p.zsrc x0 b s) =
      ODESourceQuadrature.approximation (gen H L) x0 b p.T (2 ^ p.k) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [propS, zsrc, dur, if_true, Bool.false_eq_true, if_false]
  unfold ODESourceQuadrature.approximation ODESourceQuadrature.forcingSum
  rw [add_comm]
  congr 1
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, ← map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    unfold ODEDissipative.trajectory
    have h2 : ((2 ^ p.k : ℕ) : ℂ) * ((1 / 2 ^ p.k : ℝ) : ℂ) = 1 := by
      push_cast
      field_simp
    rw [h2, one_smul]
  · rw [p.sum_words_eq (fun n => NormedSpace.exp (((n : ℝ) * (p.T / 2 ^ p.k)) • gen H L)
      (((p.T / 2 ^ p.k : ℝ) : ℂ) • b))]
    apply Finset.sum_congr rfl
    intro i _
    unfold ODESourceQuadrature.weight ODESourceQuadrature.time ODEDissipative.trajectory
    rw [map_smul, smul_ofReal]
    push_cast
    rfl

/-- **The certified source quadrature.** -/
theorem quadrature_error (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε) (H L : P →L[ℂ] P)
    (hH : star H = H) (hL : star L = L) (hHn : ‖H‖ ≤ p.lamH) (hLn : ‖L‖ ≤ p.lamD)
    (hPSD : ∀ w : P, 0 ≤ (inner ℂ w (L w)).re) (x0 b : P) (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb) :
    ‖(∑ s, p.propS H L s (p.zsrc x0 b s)) -
        ODEConstantForcing.solution (gen H L) x0 b p.T‖ ≤
      p.nu * ODESourceBranches.mass (p.zsrc x0 b) := by
  have hν : 0 < p.nu := ImprovedODEQueryBudget.precision_pos p.g p.ε hg hε
  have hA := gen_dissipative H L hH hL hPSD
  have hN : (0 : ℝ) < 2 ^ p.k := by positivity
  rw [p.source_sum_eq H L x0 b, p.mass_zsrc x0 b hT h₀ hb]
  refine (ODESourceQuadrature.approximation_error _ hA x0 b p.T hT (2 ^ p.k)
    (by positivity)).trans ?_
  have hAn : ‖gen H L‖ ≤ p.lamH + p.lamD := by
    unfold gen
    rw [norm_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Complex.norm_I, one_mul]
    linarith
  have hr₀ : 0 ≤ p.r₀ := h₀ ▸ norm_nonneg _
  have hrb : 0 ≤ p.rb := hb ▸ norm_nonneg _
  have hk := p.two_pow_k hν
  push_cast
  rw [hb, div_le_iff₀ hN]
  calc p.T ^ 2 * ‖gen H L‖ * p.rb ≤ (p.T * p.rb) * (p.T * (p.lamH + p.lamD)) := by
        have := mul_le_mul_of_nonneg_left hAn (mul_nonneg (sq_nonneg p.T) hrb)
        nlinarith
    _ ≤ (p.T * p.rb) * (p.nu * 2 ^ p.k) := mul_le_mul_of_nonneg_left hk (mul_nonneg hT hrb)
    _ ≤ p.nu * (p.r₀ + p.T * p.rb) * 2 ^ p.k := by nlinarith [mul_nonneg hν.le hr₀]

/-- The solution norm is at most the source mass. -/
theorem solution_le_mass (hT : 0 ≤ p.T) (H L : P →L[ℂ] P) (hH : star H = H) (hL : star L = L)
    (hPSD : ∀ w : P, 0 ≤ (inner ℂ w (L w)).re) (x0 b : P) (h₀ : ‖x0‖ = p.r₀) (hb : ‖b‖ = p.rb) :
    ‖ODEConstantForcing.solution (gen H L) x0 b p.T‖ ≤ ODESourceBranches.mass (p.zsrc x0 b) := by
  rw [p.mass_zsrc x0 b hT h₀ hb]
  have h := ODEConstantForcing.solution_norm_le _ (gen_dissipative H L hH hL hPSD) x0 b p.T hT
  rw [h₀, hb] at h
  exact h

end Params

end

end SparseHamiltonian.GateODE
