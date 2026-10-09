import LinearSystemLowerBound.Weight.PartialTrace

/-!
# From heralded accuracy to an exponentially small parity bias

A solver output within trace distance `ε` of the target state gives a decoder correlation
close to that of the target (`abs_corr_sub_le`, trace-distance contractivity for an
observable of norm at most one).  If the solver heralds success with probability at least
`2/3` and the target has signed decoder correlation `p ≥ 2ε`, the unconditional signed
correlation (failure contributing nothing, i.e. a random bit) is at least `(2/3)(p - 2ε)`
(`tree_bias_of_close`; paper, equation `qlsl:eq:bias`).  This holds for a clean output
(`tree_bias`) and for an output register entangled with a garbage register, whose state is
the partial trace and which is decoded by `M ⊗ I_G` (`tree_bias_reduced`).  Together with the
XOR bound for adaptive protocols a signed correlation `b` on every input gives
`b ≤ 2^{-|ι|} C^{worstCost}` (`xor_lower_bound_of_bias`), in particular
`(2/3)(p - 2ε) ≤ 2^{-|ι|} C^{worstCost}` (`xor_lower_bound`).
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem corr_sub (M A B : E →L[ℂ] E) : corr M (A - B) = corr M A - corr M B := by
  simp only [corr, comp_sub, ContinuousLinearMap.toLinearMap_sub, map_sub, Complex.sub_re]

omit [CompleteSpace E] in
/-- **Trace-distance contractivity** for an observable of norm at most one:
`|Re tr(M A) - Re tr(M B)| ≤ 2 · trdist(A, B)`. -/
theorem abs_corr_sub_le (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (A B : E →L[ℂ] E)
    (h : (A - B).toLinearMap.IsSymmetric) :
    |corr M A - corr M B| ≤ 2 * ODEMixedOutput.hermitianTraceDistance A B h := by
  rw [← corr_sub, ODEMixedOutput.hermitianTraceDistance]
  set b := h.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  set ev := h.eigenvalues (n := Module.finrank ℂ E) rfl
  have htr : corr M (A - B) = (∑ i, (ev i : ℂ) * ⟪b i, M (b i)⟫_ℂ).re := by
    rw [corr, LinearMap.trace_eq_sum_inner _ b]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hev : (A - B).toLinearMap (b i) = (ev i : ℂ) • b i := h.apply_eigenvectorBasis rfl i
    change ⟪b i, M ((A - B) (b i))⟫_ℂ = _
    rw [show (A - B) (b i) = (A - B).toLinearMap (b i) from rfl, hev, map_smul,
      inner_smul_right]
  rw [htr]
  have hb : ∀ i, ‖⟪b i, M (b i)⟫_ℂ‖ ≤ 1 := by
    intro i
    calc ‖⟪b i, M (b i)⟫_ℂ‖ ≤ ‖b i‖ * ‖M (b i)‖ := norm_inner_le_norm _ _
      _ ≤ ‖b i‖ * ‖b i‖ := mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
      _ = 1 := by rw [b.norm_eq_one]; ring
  calc |(∑ i, (ev i : ℂ) * ⟪b i, M (b i)⟫_ℂ).re|
      ≤ ‖∑ i, (ev i : ℂ) * ⟪b i, M (b i)⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i, ‖(ev i : ℂ) * ⟪b i, M (b i)⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i, |ev i| := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb i)
    _ = 2 * ((∑ i, |ev i|) / 2) := by ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {K F L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → (ι → Fin m) → K →L[ℂ] K}

omit [Fintype ι] [DecidableEq ι] [FiniteDimensional ℂ E] in
/-- **Heralded success turns a conditional correlation into an unconditional one**: if the
conditional output has signed correlation at least `p - 2ε ≥ 0` and success has probability
at least `2/3`, the unconditional signed correlation is at least `(2/3)(p - 2ε)`. -/
theorem tree_bias_of_close (T : Tree O F E) (x : ι → Fin m) (M : E →L[ℂ] E) (σ p ε : ℝ)
    (hpε : 2 * ε ≤ p) (hsucc : 2 / 3 ≤ T.successMass x)
    (hclose : p - 2 * ε ≤ σ * corr M (T.conditionalDensity x)) :
    2 / 3 * (p - 2 * ε) ≤ σ * corr M (T.successDensity x) := by
  set s := T.successMass x
  have hs0 : 0 < s := by linarith
  have hsd : T.successDensity x = ((s : ℝ) : ℂ) • T.conditionalDensity x := by
    rw [Tree.conditionalDensity, smul_smul]
    have : ((s : ℝ) : ℂ) * ((s : ℂ))⁻¹ = 1 := by
      have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      field_simp
    rw [this, one_smul]
  rw [hsd, corr_smul_real]
  have hpe : 0 ≤ p - 2 * ε := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hclose hs0.le]

omit [Fintype ι] [DecidableEq ι] in
/-- **Heralded accuracy gives a signed correlation** at least `(2/3)(p - 2ε)`. -/
theorem tree_bias (T : Tree O F E) (x : ι → Fin m) (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (u : E) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (p ε : ℝ) (hp : σ * (⟪u, M u⟫_ℂ).re = p)
    (hpε : 2 * ε ≤ p) (hsucc : 2 / 3 ≤ T.successMass x)
    (hdist : ∃ h : (T.conditionalDensity x - ODEMixedOutput.pureOperator u).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (T.conditionalDensity x)
        (ODEMixedOutput.pureOperator u) h ≤ ε) :
    2 / 3 * (p - 2 * ε) ≤ σ * corr M (T.successDensity x) := by
  obtain ⟨h, hd⟩ := hdist
  apply tree_bias_of_close T x M σ p ε hpε hsucc
  have hc := abs_corr_sub_le M hM _ _ h
  rw [corr_pure] at hc
  rcases hσ with hσ | hσ <;> rw [hσ] at hp ⊢ <;> rw [abs_le] at hc <;> nlinarith [hc.1, hc.2]

omit [Fintype ι] [DecidableEq ι] in
/-- **Heralded accuracy with a garbage register**: the output space is identified with an
output register `J` and a garbage register `G` by a fixed isometry `V`; the hypothesis is on
the reduced output state `Tr_G`, and the decoder `M` acts as `M ⊗ I_G`. -/
theorem tree_bias_reduced {J G : Type*} [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (J × G)) (T : Tree O F E) (x : ι → Fin m)
    (M : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (u : EuclideanSpace ℂ J) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (p ε : ℝ)
    (hp : σ * (⟪u, M u⟫_ℂ).re = p) (hpε : 2 * ε ≤ p) (hsucc : 2 / 3 ≤ T.successMass x)
    (hdist : ∃ h : (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)) -
        ODEMixedOutput.pureOperator u).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)))
        (ODEMixedOutput.pureOperator u) h ≤ ε) :
    2 / 3 * (p - 2 * ε) ≤
      σ * corr (V.conjStarAlgEquiv.symm (ampl (G := G) M)) (T.successDensity x) := by
  obtain ⟨h, hd⟩ := hdist
  apply tree_bias_of_close T x _ σ p ε hpε hsucc
  have hc := abs_corr_sub_le M hM _ _ h
  rw [corr_pure, corr_ptrace, corr_conjStarAlgEquiv] at hc
  rcases hσ with hσ | hσ <;> rw [hσ] at hp ⊢ <;> rw [abs_le] at hc <;> nlinarith [hc.1, hc.2]

theorem parSign_pm (j : ι → Fin m) : parSign j = 1 ∨ parSign j = -1 := by
  unfold parSign
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | insert c t hc ih =>
      rw [Finset.prod_insert hc]
      rcases ih with h | h <;> rcases sgn_eq (m := m) (j c) with hs | hs <;> simp [h, hs]

/-- **A uniform parity bias is exponentially small.**  If an adaptive protocol over an
oracle family with weight growth `C ^ w` has signed decoder correlation at least `b` on every
input, then `b ≤ 2^{-|ι|} C^{worstCost}`. -/
theorem xor_lower_bound_of_bias (hm : Even m) (hm0 : m ≠ 0)
    (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, Growth (O l) (C ^ w l))
    (hO' : ∀ l, Growth (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (T : Tree O F E) (b : ℝ)
    (hlow : ∀ x, b ≤ parSign x * corr M (T.successDensity x)) :
    b ≤ (1 / 2) ^ Fintype.card ι * C ^ T.worstCost w := by
  have hxor := tree_xor hm hm0 hU w C hC hO hO' M hM T
  have hsum : (Fintype.card (ι → Fin m) : ℝ) * b ≤
      ∑ x, parSign x * corr M (T.successDensity x) := by
    have := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hlow x)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hcard : (Fintype.card (ι → Fin m) : ℝ) = (m : ℝ) ^ Fintype.card ι := by
    simp [Fintype.card_pi, Fintype.card_fin]
  rw [hcard] at hsum
  have hmpos : 0 < (m : ℝ) ^ Fintype.card ι := by
    have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    positivity
  have h2 := hsum.trans ((le_abs_self _).trans hxor)
  have h3 : (m : ℝ) ^ Fintype.card ι * b ≤
      (m : ℝ) ^ Fintype.card ι * ((1 / 2) ^ Fintype.card ι * C ^ T.worstCost w) := by
    linarith
  exact le_of_mul_le_mul_left h3 hmpos

/-- **The lower-bound inequality.**  If an adaptive protocol over an oracle family with
weight growth `C ^ w` heralds, on every input `x`, an output within trace distance `ε` of a
target `u x` whose signed decoder correlation is `p ≥ 2ε`, with success probability at
least `2/3`, then `(2/3)(p - 2ε) ≤ 2^{-|ι|} C^{worstCost}`. -/
theorem xor_lower_bound (hm : Even m) (hm0 : m ≠ 0) (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, Growth (O l) (C ^ w l))
    (hO' : ∀ l, Growth (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (T : Tree O F E) (u : (ι → Fin m) → E)
    (p ε : ℝ) (hp : ∀ x, parSign x * (⟪u x, M (u x)⟫_ℂ).re = p) (hpε : 2 * ε ≤ p)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (T.conditionalDensity x - ODEMixedOutput.pureOperator (u x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (T.conditionalDensity x)
          (ODEMixedOutput.pureOperator (u x)) h ≤ ε) :
    2 / 3 * (p - 2 * ε) ≤ (1 / 2) ^ Fintype.card ι * C ^ T.worstCost w :=
  xor_lower_bound_of_bias hm hm0 hU w C hC hO hO' M hM T _ fun x =>
    tree_bias T x M hM (u x) (parSign x) (parSign_pm x) p ε (hp x) hpε (hT x).1 (hT x).2

end

end LinearSystemLowerBound
