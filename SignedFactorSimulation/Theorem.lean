import SignedFactorSimulation.Attenuation
import SignedFactorSimulation.Parameters

/-!
# Theorem `opt:thm:signed`

For the factor interface `opt:eq:factor` (`H = λ C`, `C = B† Z B`, `D = B† B ⪯ δ I`,
`λ > 0`, `0 < δ ≤ 1`), put `T = λ|t|`, `b = T δ`, `L = log(1/ε)` and `r_b = L/log(e + L/b)`.
For `0 < ε ≤ 1/64` there is a simulation with full-output error at most `ε` using at most

  `4·10¹⁰ (√(Tb) + √(T r_b) + r_b)`

factor queries, including adjoints, controls and cleanup; if `b ≤ ε` (in particular if `t = 0`)
the identity suffices (`signed_factor_simulation`).

The query model: the workspace is `ℂ^ι ⊗ W` for a finite label type `ι` (a Hilbert sum of
copies of `W`), and the only oracle is the factor query `I_ι ⊗ U` with its adjoint; every other
gate is a known unitary, and the input embedding `P → ℂ^ι ⊗ W` is a known isometry.

* `norm_evolution_sub_one_le`: `‖e^{-itH} - I‖ ≤ |t| ‖H‖` (the identity case);
* `positive_time`: the case `t > 0` with `b > ε`, by `core` with `q = √(T/M)` when `T ≥ M` and by
  the attenuated factor (`Known.atten`, `κ = T/M`, `q = 1`) when `T < M`;
* negative time uses the adjoint program (`LabeledAdjointSimulation.adjoint_error_eq`);
* `signed_factor_simulation_uniform`: the same with the instances all admissible factor
  unitaries, so that the input and the program are chosen before `U_B`.
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Complex ContinuousLinearMap OptimalPrecision SparseHamiltonian SparseHamiltonian.OracleCircuit
open scoped InnerProduct InnerProductSpace ComplexOrder

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### The identity case -/

/-- `‖e^{-itH} - I‖ ≤ |t| ‖H‖` for self-adjoint `H`. -/
theorem norm_evolution_sub_one_le (H : P →L[ℂ] P) (hH : star H = H) (t : ℝ) :
    ‖NormedSpace.exp ((-I * (t : ℂ)) • H) - 1‖ ≤ |t| * ‖H‖ := by
  set A : P →L[ℂ] P := (-I * (t : ℂ)) • H with hA
  have hderiv : ∀ u : ℝ, HasDerivAt (fun y : ℝ => NormedSpace.exp ((y : ℂ) • A))
      (NormedSpace.exp ((u : ℂ) • A) * A) u :=
    fun u => by
      have hg := hasDerivAt_exp_smul_const (𝕂 := ℂ) A (u : ℂ)
      have hh : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := by
        simpa using (hasDerivAt_id u).ofReal_comp
      have h := hg.scomp u hh
      rw [one_smul] at h
      exact h
  have hbound : ∀ u : ℝ, ‖NormedSpace.exp ((u : ℂ) • A) * A‖ ≤ ‖A‖ := by
    intro u
    have hu : IsUnitary (NormedSpace.exp ((u : ℂ) • A)) := by
      have h : (u : ℂ) • A = (-I * ((u * t : ℝ) : ℂ)) • H := by
        rw [hA, smul_smul]; push_cast; ring_nf
      rw [h]
      exact LabeledAdjointSimulation.evolution_unitary H hH (u * t)
    calc ‖NormedSpace.exp ((u : ℂ) • A) * A‖ ≤ ‖NormedSpace.exp ((u : ℂ) • A)‖ * ‖A‖ :=
          norm_mul_le _ _
      _ ≤ 1 * ‖A‖ := mul_le_mul_of_nonneg_right (norm_le_one_of_isometry hu.1) (norm_nonneg _)
      _ = ‖A‖ := one_mul _
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := fun y : ℝ => NormedSpace.exp ((y : ℂ) • A))
    (fun x _ => (hderiv x).hasDerivWithinAt) (fun x _ => hbound x)
  simp only [Complex.ofReal_one, one_smul, Complex.ofReal_zero, zero_smul,
    NormedSpace.exp_zero] at h
  calc ‖NormedSpace.exp A - 1‖ ≤ ‖A‖ := h
    _ = |t| * ‖H‖ := by
        rw [hA, norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_eq_abs]

/-- The represented Hamiltonian `H = λ C`. -/
def Known.ham (K : Known P W) (lam : ℝ) (U : W →L[ℂ] W) : P →L[ℂ] P := (lam : ℂ) • K.Cop U

theorem Known.ham_star (K : Known P W) (lam : ℝ) (U : W →L[ℂ] W) :
    star (K.ham lam U) = K.ham lam U := by
  rw [Known.ham, star_smul, K.Cop_star, Complex.star_def, Complex.conj_ofReal]

/-- `‖H‖ ≤ λ δ`. -/
theorem Known.norm_ham_le (K : Known P W) {lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (U : W →L[ℂ] W) (hD : K.Dop U ≤ (δ : ℂ) • (1 : P →L[ℂ] P)) : ‖K.ham lam U‖ ≤ lam * δ := by
  rw [Known.ham, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
  exact mul_le_mul_of_nonneg_left (Tail.norm_le_of_sandwich hδ (K.Dop_nonneg U) hD
    (K.neg_Dop_le_Cop U) (K.Cop_le_Dop U)) hlam

theorem diagonal_unitary_const (ι : Type*) [Fintype ι] {U : W →L[ℂ] W} (hU : IsUnitary U) :
    IsUnitary (WeightedClock.diagonal (fun _ : ι => U)) := by
  have h1 : U† ∘L U = 1 := hU.1
  have h2 : U ∘L U† = 1 := hU.2
  constructor
  · change (WeightedClock.diagonal (fun _ : ι => U))† ∘L WeightedClock.diagonal (fun _ => U) = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [h1]
    exact WeightedClock.diagonal_one
  · change WeightedClock.diagonal (fun _ : ι => U) ∘L (WeightedClock.diagonal (fun _ => U))† = 1
    rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [h2]
    exact WeightedClock.diagonal_one

/-! ### Positive time -/

omit [CompleteSpace P] in
/-- `D' = κ D ⪯ κ δ I`. -/
theorem smul_le_smul_one {D : P →L[ℂ] P} {δ κ : ℝ} (hκ : 0 ≤ κ)
    (hD : D ≤ (δ : ℂ) • (1 : P →L[ℂ] P)) :
    (κ : ℂ) • D ≤ ((κ * δ : ℝ) : ℂ) • (1 : P →L[ℂ] P) := by
  rw [ContinuousLinearMap.le_def] at hD ⊢
  have h : ((κ * δ : ℝ) : ℂ) • (1 : P →L[ℂ] P) - (κ : ℂ) • D =
      (κ : ℂ) • ((δ : ℂ) • (1 : P →L[ℂ] P) - D) := by
    rw [smul_sub, smul_smul]; push_cast; ring_nf
  rw [h]
  exact hD.smul_of_nonneg (by exact_mod_cast hκ)

/-- **Positive time**: for `T > 0` and `b = Tδ > ε` there is a program for `e^{-iTC}`. -/
theorem positive_time [FiniteDimensional ℂ P] [FiniteDimensional ℂ W] (K : Known P W)
    {X : Type*} (U : X → W →L[ℂ] W) (hU : ∀ x, IsUnitary (U x)) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hD : ∀ x, K.Dop (U x) ≤ (δ : ℂ) • (1 : P →L[ℂ] P)) {T : ℝ} (hT : 0 < T)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hb : ε < T * δ) :
    ∃ (ι : Type) (_ : Fintype ι) (inp : P →L[ℂ] PiLp 2 (fun _ : ι => W))
      (p : Program (fun x => WeightedClock.diagonal (fun _ : ι => U x))),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ 4 * 10 ^ 10 * (Real.sqrt (T * (T * δ)) + Real.sqrt (T * rb (T * δ) ε) +
        rb (T * δ) ε) ∧
      ∀ x, ‖p.eval x ∘L inp - inp ∘L NormedSpace.exp ((-I * (T : ℂ)) • K.Cop (U x))‖ ≤ ε := by
  set b := T * δ with hb_def
  have hb0 : 0 < b := hε.trans hb
  have hbT : b ≤ T := by rw [hb_def]; nlinarith
  have hε2 : ε ≤ 1 / 2 := by linarith
  have hr := rb_pos hε hε1 hb0
  set M := order b ε with hM_def
  have hM1 : 1 ≤ M := one_le_order hε hε1 hb0
  have hMge := order_ge b ε
  have hMle := order_le hε hε1 hb
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have htail := tail_bound hε hε1 hb0 hMge
  have hMb : 2 * 27 ^ 2 * b ≤ M := by nlinarith
  by_cases hTM : (M : ℝ) ≤ T
  · -- `q = √(T/M) ≥ 1`
    set q := Real.sqrt (T / M) with hq_def
    have hTM' : 0 ≤ T / M := by positivity
    have hq1 : 1 ≤ q := by
      rw [hq_def, Real.le_sqrt (by norm_num) hTM', one_pow, le_div_iff₀ hM0, one_mul]
      exact hTM
    have hq2 : q ^ 2 * M = T := by
      rw [hq_def, Real.sq_sqrt hTM']; field_simp
    have hqb : q ^ 2 * M * δ = b := by rw [hq2]
    obtain ⟨ι, hι, inp, p, hinp, hcount, herr⟩ := core K U hU hq1 hM1 hδ.le hD
      (by rw [hqb]; exact hMb) hε hε2 (by rw [hqb]; exact htail)
    refine ⟨ι, hι, inp, p, hinp, ?_, fun x => ?_⟩
    · have hqM : q * M = Real.sqrt (T * M) := by
        rw [show T * M = (T / M) * (M : ℝ) ^ 2 by field_simp, Real.sqrt_mul hTM',
          Real.sqrt_sq hM0.le]
      rw [hqM] at hcount
      exact hcount.trans (count_le_of_large hT.le hb0.le hr.le hMle)
    · have h := herr x
      rw [show (-(I * ((q ^ 2 * M : ℝ) : ℂ))) = -I * (T : ℂ) by rw [hq2]; ring] at h
      exact h
  · -- attenuation by `κ = T/M`
    push Not at hTM
    set κ := T / M with hκ_def
    have hκ0 : 0 ≤ κ := by positivity
    have hκ1 : κ ≤ 1 := by rw [hκ_def, div_le_one hM0]; exact hTM.le
    have hMκ : (M : ℝ) * κ = T := by rw [hκ_def]; field_simp
    have hbκ : (1 : ℝ) ^ 2 * M * (κ * δ) = b := by rw [hb_def, ← hMκ]; ring
    have hU' : ∀ x, IsUnitary (dbl (U x)) := fun x => dbl_unitary (hU x)
    have hD' : ∀ x, (K.atten hκ0 hκ1).Dop (dbl (U x)) ≤ ((κ * δ : ℝ) : ℂ) • (1 : P →L[ℂ] P) := by
      intro x
      rw [K.atten_Dop hκ0 hκ1]
      exact smul_le_smul_one hκ0 (hD x)
    obtain ⟨ι, hι, inp, p, hinp, hcount, herr⟩ := core (K.atten hκ0 hκ1) (fun x => dbl (U x))
      hU' le_rfl hM1 (by positivity) hD' (by rw [hbκ]; exact hMb) hε hε2
      (by rw [hbκ]; exact htail)
    have hImp : Implements (fun x => WeightedClock.diagonal (fun _ : ι => dbl (U x)))
        (fun x => p.eval x) p.count := ⟨p, fun _ => rfl, le_rfl⟩
    obtain ⟨p', hp'eval, hp'count⟩ := Implements.of_oracle_eq
      (fun x => flat2_dbl ι (U x)) (hImp.transport (flat2 W ι))
    refine ⟨Σ _ : ι, Bool, inferInstance, embed (flat2 W ι) inp, p', embed_isometry _ hinp, ?_,
      fun x => ?_⟩
    · have hc : (p'.count : ℝ) ≤ p.count := by exact_mod_cast hp'count
      have h1 : (p.count : ℝ) ≤ 2 * 3 ^ 8 * 27 * M := by simpa using hcount
      exact hc.trans (h1.trans (count_le_of_small hb0.le hbT hr.le hMle))
    · have h := herr x
      rw [K.atten_Cop hκ0 hκ1, smul_smul,
        show (-(I * (((1 : ℝ) ^ 2 * M : ℝ) : ℂ))) * (κ : ℂ) = -I * (T : ℂ) by
          rw [← hMκ]; push_cast; ring] at h
      rw [hp'eval x]
      beta_reduce
      rw [embed_error]
      convert h using 4

/-! ### Theorem `opt:thm:signed` -/

/-- **Theorem `opt:thm:signed`.** For the factor interface (`K`, supplied unitaries `U x`) with
`D ⪯ δ I`, `λ > 0`, `0 < δ ≤ 1`, every time `t` and `0 < ε ≤ 1/64`, with `T = λ|t|`,
`b = T δ` and `r_b = log(1/ε)/log(e + log(1/ε)/b)`: there are a finite label type `ι`, a known
isometric input `P → ℂ^ι ⊗ W` and a program whose only oracle is the factor query `I_ι ⊗ U`
(and its adjoint), with no query if `b ≤ ε` and at most
`4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` queries otherwise, whose full output is within `ε` of
`e^{-itH}`, `H = λ C`, for every instance. -/
theorem signed_factor_simulation [FiniteDimensional ℂ P] [FiniteDimensional ℂ W] (K : Known P W)
    {X : Type*} (U : X → W →L[ℂ] W) (hU : ∀ x, IsUnitary (U x)) {lam δ : ℝ} (hlam : 0 < lam)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hD : ∀ x, K.Dop (U x) ≤ (δ : ℂ) • (1 : P →L[ℂ] P)) (t : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    ∃ (ι : Type) (_ : Fintype ι) (inp : P →L[ℂ] PiLp 2 (fun _ : ι => W))
      (p : Program (fun x => WeightedClock.diagonal (fun _ : ι => U x))),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ (if lam * |t| * δ ≤ ε then 0 else
        4 * 10 ^ 10 * (Real.sqrt (lam * |t| * (lam * |t| * δ)) +
          Real.sqrt (lam * |t| * rb (lam * |t| * δ) ε) + rb (lam * |t| * δ) ε)) ∧
      ∀ x, ‖p.eval x ∘L inp - inp ∘L NormedSpace.exp ((-I * (t : ℂ)) • K.ham lam (U x))‖ ≤ ε := by
  by_cases hsmall : lam * |t| * δ ≤ ε
  · -- the identity
    refine ⟨Unit, inferInstance, WeightedClock.boundary (fun _ : Unit => 1) (fun _ => K.E),
      Program.identity, ?_, ?_, fun x => ?_⟩
    · apply WeightedClock.boundary_isometry
      · intro _; norm_num
      · simp
      · intro _; exact K.E_isometry
    · rw [if_pos hsmall, Program.count_identity, Nat.cast_zero]
    · set inp := WeightedClock.boundary (fun _ : Unit => 1) (fun _ => K.E) with hinp_def
      have hinp : inp† ∘L inp = 1 := by
        apply WeightedClock.boundary_isometry
        · intro _; norm_num
        · simp
        · intro _; exact K.E_isometry
      set V := NormedSpace.exp ((-I * (t : ℂ)) • K.ham lam (U x))
      have h1 : (Program.identity : Program (fun x => WeightedClock.diagonal
          (fun _ : Unit => U x))).eval x ∘L inp - inp ∘L V = inp ∘L (1 - V) := by
        rw [Program.eval_identity, comp_sub, comp_one', one_comp']
      rw [h1, EncodedOracle.norm_comp_eq inp hinp, norm_sub_rev]
      calc ‖V - 1‖ ≤ |t| * ‖K.ham lam (U x)‖ :=
            norm_evolution_sub_one_le _ (K.ham_star lam (U x)) t
        _ ≤ |t| * (lam * δ) :=
            mul_le_mul_of_nonneg_left (K.norm_ham_le hlam.le hδ.le (U x) (hD x)) (abs_nonneg t)
        _ = lam * |t| * δ := by ring
        _ ≤ ε := hsmall
  · push Not at hsmall
    have ht : t ≠ 0 := by
      rintro rfl
      simp at hsmall
      linarith
    have hT : 0 < lam * |t| := mul_pos hlam (abs_pos.mpr ht)
    obtain ⟨ι, hι, inp, p, hinp, hcount, herr⟩ :=
      positive_time K U hU hδ hδ1 hD hT hε hε1 hsmall
    have hO : ∀ x, IsUnitary (WeightedClock.diagonal (fun _ : ι => U x)) :=
      fun x => diagonal_unitary_const ι (hU x)
    rcases le_or_gt 0 t with ht0 | ht0
    · refine ⟨ι, hι, inp, p, hinp, by rw [if_neg (not_le.mpr hsmall)]; exact hcount,
        fun x => ?_⟩
      have h := herr x
      rw [abs_of_nonneg ht0] at h
      rw [Known.ham, smul_smul, show (-I * (t : ℂ)) * (lam : ℂ) = -I * ((lam * t : ℝ) : ℂ) by
        push_cast; ring]
      exact h
    · refine ⟨ι, hι, inp, p.adjoint, hinp, ?_, fun x => ?_⟩
      · rw [if_neg (not_le.mpr hsmall), Program.count_adjoint]
        exact hcount
      · have hC := K.Cop_star (U x)
        have hVu := LabeledAdjointSimulation.evolution_unitary (K.Cop (U x)) hC (lam * |t|)
        have hexp : (-I * (t : ℂ)) • K.ham lam (U x) =
            (-I * (((-(lam * |t|)) : ℝ) : ℂ)) • K.Cop (U x) := by
          rw [Known.ham, smul_smul, abs_of_neg ht0]
          congr 1
          push_cast
          ring
        rw [Program.eval_adjoint, hexp,
          ← LabeledAdjointSimulation.evolution_adjoint (K.Cop (U x)) hC (lam * |t|),
          star_eq_adjoint,
          LabeledAdjointSimulation.adjoint_error_eq (p.eval x) _ (p.eval_unitary hO x) hVu inp inp]
        exact herr x

/-- The admissible factor unitaries: unitary `U` with `D(U) ⪯ δ I`. -/
def Admissible (K : Known P W) (δ : ℝ) : Type _ :=
  {U : W →L[ℂ] W // IsUnitary U ∧ K.Dop U ≤ (δ : ℂ) • (1 : P →L[ℂ] P)}

/-- **Theorem `opt:thm:signed`, uniform form.** One input embedding and one program, chosen
before the factor unitary, serve every admissible `U_B` (`Admissible K δ`): the instances are all
unitaries with `D ⪯ δ I` for the known data `K`. -/
theorem signed_factor_simulation_uniform [FiniteDimensional ℂ P] [FiniteDimensional ℂ W]
    (K : Known P W) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    ∃ (ι : Type) (_ : Fintype ι) (inp : P →L[ℂ] PiLp 2 (fun _ : ι => W))
      (p : Program (fun U : Admissible K δ => WeightedClock.diagonal (fun _ : ι => U.1))),
      inp† ∘L inp = 1 ∧
      (p.count : ℝ) ≤ (if lam * |t| * δ ≤ ε then 0 else
        4 * 10 ^ 10 * (Real.sqrt (lam * |t| * (lam * |t| * δ)) +
          Real.sqrt (lam * |t| * rb (lam * |t| * δ) ε) + rb (lam * |t| * δ) ε)) ∧
      ∀ U : Admissible K δ,
        ‖p.eval U ∘L inp - inp ∘L NormedSpace.exp ((-I * (t : ℂ)) • K.ham lam U.1)‖ ≤ ε :=
  signed_factor_simulation K (fun U : Admissible K δ => U.1) (fun U => U.2.1) hlam hδ hδ1
    (fun U => U.2.2) t hε hε1

end

end SignedFactorSimulation
