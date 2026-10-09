import SparseODE.ODEGroverActual

/-!
# Randomized amplification for every successful amplitude up to one

The released randomized amplification theorem `ODEGroverActual.randomized_certificate` assumes
a successful amplitude `a ≤ 1/2`, the range of the preparations of Theorem `ode:thm:gates`,
whose coefficient register divides the amplitude by three.  The direct source assembly of the
zero-time remark of `ode:thm:gates` has no coefficient register: its successful amplitude is
`‖x(T)‖ / B ∈ [1/g, 1]`.  This module proves the same conclusions, with the same public cutoff
`ODEGroverAverage.chosenIterations g` (uniform trial counts `j < ⌈4g⌉ ≤ 5g`), for every
amplitude in `[1/(4g), 1]`.

* `meanSuccess_high`: for an angle `θ ∈ [π/6, π/2)` and `M ≥ 2` trial counts the average of
  `sin² ((2j+1) θ)` is at least `1/4`.  With the released telescoping identity
  `ODEGroverAverage.sum_identity` this reduces to `sin (4Mθ) ≤ M sin 2θ`; for `θ ≤ π/4` the
  right side is at least `4/3`, and otherwise `x = π - 2θ ∈ (0, π/2]` and the inequality is
  `M sin x + sin (2Mx) ≥ 0`, which holds for `2Mx ≤ π` by signs and otherwise by Jordan's
  inequality `sin x ≥ 2x/π > 1/M`.
* `promised_amplitude_full`: the released cutoff serves every amplitude in `[1/(4g), 1)`.
* For an amplitude below one the invariant-plane formula of the released analysis holds
  (`trial_projected_lt_one`, `trial_probability_lt_one`, `decoded_multiple_lt_one`).
* At amplitude one the prepared state lies in the successful subspace
  (`prepared_good_of_amplitude_one`), every Grover step multiplies it by `-1`
  (`trial_of_amplitude_one`), and every trial succeeds.
* `randomized_certificate_full`: mean success at least `1/4` and, for every nonzero decoded
  trial, the direction error of the prepared decoded vector up to a global phase.
-/

set_option autoImplicit false

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct BigOperators

/-! ### The scalar average -/

section Scalar

/-- `sin (4Mθ) = -sin (2M (π - 2θ))`. -/
theorem sin_four_mul_eq (M : ℕ) (θ : ℝ) :
    Real.sin (4 * (M : ℝ) * θ) = -Real.sin (2 * (M : ℝ) * (Real.pi - 2 * θ)) := by
  have e : 4 * (M : ℝ) * θ = -(2 * (M : ℝ) * (Real.pi - 2 * θ)) + (M : ℝ) * (2 * Real.pi) := by
    ring
  rw [e, Real.sin_add_nat_mul_two_pi, Real.sin_neg]

/-- The key inequality `sin (4Mθ) ≤ M sin 2θ` for `θ ∈ [π/4, π/2)`. -/
theorem sin_four_mul_le (θ : ℝ) (M : ℕ) (hθ1 : Real.pi / 4 ≤ θ) (hθ2 : θ < Real.pi / 2) :
    Real.sin (4 * (M : ℝ) * θ) ≤ (M : ℝ) * Real.sin (2 * θ) := by
  have hpi := Real.pi_pos
  set x := Real.pi - 2 * θ with hx
  have hx0 : 0 < x := by linarith
  have hx1 : x ≤ Real.pi / 2 := by linarith
  have hsx : Real.sin (2 * θ) = Real.sin x := by
    rw [hx, Real.sin_pi_sub]
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hsin0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_nonneg_of_le_pi hx0.le (by linarith)
  rw [sin_four_mul_eq, hsx]
  by_cases h2 : 2 * (M : ℝ) * x ≤ Real.pi
  · have h3 := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity : 0 ≤ 2 * (M : ℝ) * x) h2
    nlinarith
  · replace h2 : Real.pi < 2 * (M : ℝ) * x := not_le.mp h2
    have hj := Real.mul_le_sin hx0.le hx1
    have hlt : 1 < 2 * (M : ℝ) * x / Real.pi := (one_lt_div hpi).mpr h2
    have e : 2 * (M : ℝ) * x / Real.pi = (M : ℝ) * (2 / Real.pi * x) := by
      field_simp
    have h1 : 1 < (M : ℝ) * Real.sin x := by
      rw [e] at hlt
      calc (1 : ℝ) < (M : ℝ) * (2 / Real.pi * x) := hlt
        _ ≤ (M : ℝ) * Real.sin x := mul_le_mul_of_nonneg_left hj hM0
    have h4 := Real.neg_one_le_sin (2 * (M : ℝ) * x)
    linarith

/-- **Average success at large angles**: for `θ ∈ [π/6, π/2)` and at least two trial counts,
the uniform average of `sin² ((2j+1) θ)`, `j < M`, is at least `1/4`. -/
theorem meanSuccess_high (θ : ℝ) (M : ℕ) (hM : 2 ≤ M) (hθ1 : Real.pi / 6 ≤ θ)
    (hθ2 : θ < Real.pi / 2) : (1 : ℝ) / 4 ≤ ODEGroverAverage.meanSuccess θ M := by
  have hpi := Real.pi_pos
  have hMpos : 0 < M := by omega
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hs : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  by_cases hθ : θ ≤ Real.pi / 4
  · have hj := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith)
    have h23 : (2 : ℝ) / 3 ≤ Real.sin (2 * θ) := by
      have e : (2 : ℝ) / 3 = 2 / Real.pi * (Real.pi / 3) := by
        field_simp
      rw [e]
      refine le_trans ?_ hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    apply ODEGroverAverage.meanSuccess_lower θ M hMpos hs
    nlinarith
  · replace hθ : Real.pi / 4 < θ := not_le.mp hθ
    have hkey := sin_four_mul_le θ M hθ.le hθ2
    have hsum := ODEGroverAverage.sum_identity θ M
    have hMr0 : (0 : ℝ) < M := by exact_mod_cast hMpos
    unfold ODEGroverAverage.meanSuccess
    rw [le_div_iff₀ hMr0]
    have h1 : (M : ℝ) * Real.sin (2 * θ) ≤
        4 * Real.sin (2 * θ) * (∑ j ∈ Finset.range M, ODEGroverAverage.successProbability θ j) := by
      linarith
    by_contra hneg
    replace hneg := not_le.mp hneg
    have h2 : 4 * Real.sin (2 * θ) *
        (∑ j ∈ Finset.range M, ODEGroverAverage.successProbability θ j) <
        (M : ℝ) * Real.sin (2 * θ) := by
      nlinarith
    linarith

/-- **The public cutoff serves every amplitude below one**: for `1/(4g) ≤ a < 1` the uniform
average over `j < chosenIterations g` is at least `1/4` (the released
`ODEGroverAverage.promised_amplitude` for `a ≤ 1/2`, `meanSuccess_high` above). -/
theorem promised_amplitude_full (g a : ℝ) (hg : 1 ≤ g) (ha0 : 1 / (4 * g) ≤ a) (ha1 : a < 1) :
    (1 : ℝ) / 4 ≤
      ODEGroverAverage.meanSuccess (Real.arcsin a) (ODEGroverAverage.chosenIterations g) := by
  by_cases ha : a ≤ 1 / 2
  · exact (ODEGroverAverage.promised_amplitude g a hg ha0 ha).2.2
  · replace ha : 1 / 2 < a := not_le.mp ha
    obtain ⟨-, hlo, -⟩ := ODEGroverAverage.chosenIterations_bounds g hg
    have hM2 : 2 ≤ ODEGroverAverage.chosenIterations g := by
      have h : (2 : ℝ) ≤ (ODEGroverAverage.chosenIterations g : ℝ) := by linarith
      exact_mod_cast h
    have hpi := Real.pi_pos
    apply meanSuccess_high _ _ hM2
    · rw [Real.le_arcsin_iff_sin_le ⟨by linarith, by linarith⟩ ⟨by linarith, ha1.le⟩,
        Real.sin_pi_div_six]
      exact ha.le
    · exact Real.arcsin_lt_pi_div_two.mpr ha1

end Scalar

/-! ### The actual Grover trials -/

section Operator

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An isometric decoding has an adjoint of norm at most one. -/
theorem norm_adjoint_apply_le (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (v : K) : ‖(F†) v‖ ≤ ‖v‖ := by
  have hn : ‖F‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by
      rw [F.norm_map_iff_adjoint_comp_self.mpr hF w, one_mul])
  have hadj : ‖F†‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact hn
  calc ‖(F†) v‖ ≤ ‖F†‖ * ‖v‖ := le_opNorm _ _
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hadj (norm_nonneg _)
    _ = ‖v‖ := one_mul _

/-- The successful amplitude of a unitary preparation of a unit seed is at most one. -/
theorem amplitude_le_one (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (W : K →L[ℂ] K) (hW : IsUnitary W)
    (ψ : K) (hψ : ‖ψ‖ = 1) : ODEGroverActual.amplitude F W ψ ≤ 1 := by
  have hu : ‖W ψ‖ = 1 := by
    rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hψ]
  rw [ODEGroverActual.amplitude, ← ODEHeraldedSuccess.successfulComponent,
    ODEHeraldedSuccess.successfulComponent_norm _ hF]
  exact (norm_adjoint_apply_le F hF (W ψ)).trans hu.le

/-- Below amplitude one the angle has a positive cosine. -/
theorem angle_geometry_lt_one (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Real.sin (Real.arcsin a) = a ∧ 0 < Real.cos (Real.arcsin a) := by
  refine ⟨Real.sin_arcsin (by linarith) ha1.le, ?_⟩
  rw [Real.cos_arcsin]
  apply Real.sqrt_pos.mpr
  nlinarith

/-- The exact successful component of every trial, for an amplitude below one (the released
`ODEGroverActual.trial_projected` without the bound `a ≤ 1/2`). -/
theorem trial_projected_lt_one (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < ODEGroverActual.amplitude F W ψ) (ha1 : ODEGroverActual.amplitude F W ψ < 1)
    (j : ℕ) :
    ODEHeraldedSuccess.successProjector F (ODEGroverActual.trial F W ψ j) =
      ((Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (ODEGroverActual.amplitude F W ψ)) /
        ODEGroverActual.amplitude F W ψ : ℝ) : ℂ) •
          ODEHeraldedSuccess.successProjector F (W ψ) := by
  have hUnit : ‖W ψ‖ = 1 := by
    rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hψ]
  have hQ := ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF
  obtain ⟨hs, hc⟩ := angle_geometry_lt_one (ODEGroverActual.amplitude F W ψ) ha0.le ha1
  have hs0 : Real.sin (Real.arcsin (ODEGroverActual.amplitude F W ψ)) ≠ 0 := by
    rw [hs]
    exact ha0.ne'
  have hCompression :
      ODEGroverRay.projector (W ψ) (ODEHeraldedSuccess.successProjector F (W ψ)) =
        (Real.sin (Real.arcsin (ODEGroverActual.amplitude F W ψ)) : ℂ) ^ 2 • W ψ := by
    rw [hs]
    exact ODEGroverRay.projector_good (W ψ)
      (ODEHeraldedSuccess.successProjector F) hQ
  simpa only [ODEGroverActual.trial, ODEGroverActual.actualG, hs] using
    ODEGroverPlane.projected_power (ODEGroverRay.projector (W ψ))
      (ODEHeraldedSuccess.successProjector F) hQ (W ψ)
      (Real.arcsin (ODEGroverActual.amplitude F W ψ)) hs0 hc.ne'
      (ODEGroverRay.projector_self (W ψ) hUnit) hCompression j

/-- The herald probability of every trial is the odd-angle sine squared, for an amplitude
below one. -/
theorem trial_probability_lt_one (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < ODEGroverActual.amplitude F W ψ) (ha1 : ODEGroverActual.amplitude F W ψ < 1)
    (j : ℕ) :
    ODEGroverActual.probability F W ψ j =
      ODEGroverAverage.successProbability (Real.arcsin (ODEGroverActual.amplitude F W ψ)) j := by
  have hNorm : ‖ODEHeraldedSuccess.successProjector F (ODEGroverActual.trial F W ψ j)‖ =
      |Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (ODEGroverActual.amplitude F W ψ))| := by
    rw [trial_projected_lt_one F hF W hW ψ hψ ha0 ha1 j,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos ha0]
    change |Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (ODEGroverActual.amplitude F W ψ))| /
      ODEGroverActual.amplitude F W ψ * ODEGroverActual.amplitude F W ψ = _
    exact div_mul_cancel₀ _ ha0.ne'
  unfold ODEGroverActual.probability ODEGroverAverage.successProbability
  rw [hNorm, sq_abs]

/-- Every decoded trial is a real multiple of the decoded prepared vector, for an amplitude
below one. -/
theorem decoded_multiple_lt_one (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha0 : 0 < ODEGroverActual.amplitude F W ψ) (ha1 : ODEGroverActual.amplitude F W ψ < 1)
    (j : ℕ) :
    ODEGroverActual.decoded F W ψ j =
      ((Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (ODEGroverActual.amplitude F W ψ)) /
        ODEGroverActual.amplitude F W ψ : ℝ) : ℂ) • (F†) (W ψ) :=
  ODEGroverDirection.decode_real_multiple F hF (W ψ) (ODEGroverActual.trial F W ψ j)
    (Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (ODEGroverActual.amplitude F W ψ)) /
      ODEGroverActual.amplitude F W ψ) (trial_projected_lt_one F hF W hW ψ hψ ha0 ha1 j)

/-- **At amplitude one the prepared state is successful**: its projection on the successful
subspace is itself. -/
theorem prepared_good_of_amplitude_one (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha : ODEGroverActual.amplitude F W ψ = 1) :
    ODEHeraldedSuccess.successProjector F (W ψ) = W ψ := by
  have hu : ‖W ψ‖ = 1 := by
    rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hψ]
  have hQ := ODEHeraldedSuccess.successProjector_isOrthogonalProjection F hF
  have hQu : ‖ODEHeraldedSuccess.successProjector F (W ψ)‖ = 1 := ha
  have hinner : inner ℂ (W ψ) (ODEHeraldedSuccess.successProjector F (W ψ)) = 1 := by
    have h := ODEGroverRay.ray_adjoint_good (W ψ) (ODEHeraldedSuccess.successProjector F) hQ
    rw [ODEGroverRay.ray_adjoint_apply, hQu] at h
    rw [h]
    norm_num
  have h := norm_sub_sq (𝕜 := ℂ) (W ψ) (ODEHeraldedSuccess.successProjector F (W ψ))
  rw [hu, hQu, hinner] at h
  have h0 : ‖W ψ - ODEHeraldedSuccess.successProjector F (W ψ)‖ ^ 2 = 0 := by
    rw [h]
    norm_num
  have h1 : W ψ - ODEHeraldedSuccess.successProjector F (W ψ) = 0 :=
    norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
  exact (sub_eq_zero.mp h1).symm

omit [CompleteSpace K] in
/-- A Grover step is `-1` on a vector fixed by both projections. -/
theorem grover_apply_fixed (Pr Q : K →L[ℂ] K) (u : K) (hP : Pr u = u) (hQ : Q u = u) :
    ODEGroverPlane.grover Pr Q u = -u := by
  simp only [ODEGroverPlane.grover, mul_apply_eq_comp, sub_apply, smul_apply, one_def, id_apply,
    map_sub, map_smul, hP, hQ]
  module

/-- **At amplitude one every trial is the prepared state up to the sign `(-1)^j`.** -/
theorem trial_of_amplitude_one (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (ha : ODEGroverActual.amplitude F W ψ = 1) (j : ℕ) :
    ODEGroverActual.trial F W ψ j = ((-1 : ℂ) ^ j) • W ψ := by
  have hu : ‖W ψ‖ = 1 := by
    rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hψ]
  have hG : ODEGroverActual.actualG F W ψ (W ψ) = -W ψ :=
    grover_apply_fixed _ _ _ (ODEGroverRay.projector_self (W ψ) hu)
      (prepared_good_of_amplitude_one F hF W hW ψ hψ ha)
  induction j with
  | zero => simp [ODEGroverActual.trial]
  | succ j ih =>
      unfold ODEGroverActual.trial at ih ⊢
      rw [pow_succ', mul_apply_eq_comp, ih, map_smul, hG, pow_succ]
      module

/-- **Randomized amplification for every amplitude in `[1/(4g), 1]`.**  With the released
public cutoff `chosenIterations g ≤ 5g`, the mean herald probability over the uniformly chosen
trial counts is at least `1/4`, and every nonzero decoded trial has the direction error of the
decoded prepared vector, up to one global phase.  This is the released
`ODEGroverActual.randomized_certificate` without the upper bound `a ≤ 1/2` (the amplitude of a
unitary preparation of a unit seed is at most one, `amplitude_le_one`). -/
theorem randomized_certificate_full (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (g : ℝ) (hg : 1 ≤ g) (haLower : 1 / (4 * g) ≤ ODEGroverActual.amplitude F W ψ)
    (target : P) (η : ℝ)
    (hError : ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ ≤ η) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ ODEGroverActual.meanProbability F W ψ (ODEGroverAverage.chosenIterations g) ∧
    ∀ j : ℕ, ODEGroverActual.decoded F W ψ j ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection (ODEGroverActual.decoded F W ψ j) - unitDirection target‖ ≤ η := by
  obtain ⟨hM, -, hM5⟩ := ODEGroverAverage.chosenIterations_bounds g hg
  have hden : 0 < 4 * g := by linarith
  have ha0 : 0 < ODEGroverActual.amplitude F W ψ :=
    lt_of_lt_of_le (one_div_pos.mpr hden) haLower
  refine ⟨hM, hM5, ?_⟩
  rcases lt_or_eq_of_le (amplitude_le_one F hF W hW ψ hψ) with ha1 | ha1
  · -- amplitude below one: the invariant-plane formula
    refine ⟨?_, ?_⟩
    · have hMean : ODEGroverActual.meanProbability F W ψ (ODEGroverAverage.chosenIterations g) =
          ODEGroverAverage.meanSuccess (Real.arcsin (ODEGroverActual.amplitude F W ψ))
            (ODEGroverAverage.chosenIterations g) := by
        unfold ODEGroverActual.meanProbability ODEGroverAverage.meanSuccess
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact trial_probability_lt_one F hF W hW ψ hψ ha0 ha1 j
      rw [hMean]
      exact promised_amplitude_full g _ hg haLower ha1
    · intro j hj
      exact ODEGroverDirection.direction_error_of_real_multiple
        ((F†) (W ψ)) (ODEGroverActual.decoded F W ψ j) target
        (Real.sin ((2 * (j : ℝ) + 1) * Real.arcsin (ODEGroverActual.amplitude F W ψ)) /
          ODEGroverActual.amplitude F W ψ) η
        (decoded_multiple_lt_one F hF W hW ψ hψ ha0 ha1 j) hj hError
  · -- amplitude one: every trial is the prepared state up to a sign
    have hu : ‖W ψ‖ = 1 := by
      rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hψ]
    have hgood := prepared_good_of_amplitude_one F hF W hW ψ hψ ha1
    have hsign : ∀ j : ℕ, ((-1 : ℂ) ^ j) = (((-1 : ℝ) ^ j : ℝ) : ℂ) := by
      intro j
      push_cast
      rfl
    have hnorm : ∀ j : ℕ, ‖((-1 : ℂ) ^ j)‖ = 1 := by
      intro j
      rw [norm_pow, norm_neg, norm_one, one_pow]
    refine ⟨?_, ?_⟩
    · have hprob : ∀ j : ℕ, ODEGroverActual.probability F W ψ j = 1 := by
        intro j
        rw [ODEGroverActual.probability, trial_of_amplitude_one F hF W hW ψ hψ ha1 j,
          map_smul, hgood, norm_smul, hnorm, hu]
        norm_num
      have hMr : (0 : ℝ) < ODEGroverAverage.chosenIterations g := by exact_mod_cast hM
      unfold ODEGroverActual.meanProbability
      rw [Finset.sum_congr rfl (fun j _ => hprob j), Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, div_self hMr.ne']
      norm_num
    · intro j hj
      have hdec : ODEGroverActual.decoded F W ψ j = (((-1 : ℝ) ^ j : ℝ) : ℂ) • (F†) (W ψ) := by
        rw [ODEGroverActual.decoded, trial_of_amplitude_one F hF W hW ψ hψ ha1 j, map_smul,
          hsign]
      exact ODEGroverDirection.direction_error_of_real_multiple
        ((F†) (W ψ)) (ODEGroverActual.decoded F W ψ j) target ((-1 : ℝ) ^ j) η hdec hj hError

end Operator

end

end SparseHamiltonian.ZeroTimeGateODE
