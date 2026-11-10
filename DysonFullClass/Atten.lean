import GeneralSourceODE.Compiled
import SparseHamiltonian.SubspaceOracle

set_option autoImplicit false

/-!
# The label-controlled attenuation of the Dyson coefficients

Manuscript, proof of Lemma `odel:lem:dyson`: "Use the common coefficient sequence `z^k/k!`
for all branches. For a branch starting at `u`, the coefficient relative to this common sequence
is `((T-u)/T)^k`. It lies in `[0,1]` and is known from the branch and degree labels, so a
controlled rotation can place it in the selected amplitude."

The supplied weight preparation `P_w` acts on the source label only (`P_w ⊗ 1`), so the LCU
coefficient state it produces is a product: source weights times one common table `c` over the
Dyson labels. The label-dependent factor is applied by a public controlled rotation of one fresh
attenuation qubit (`attGate θ`): on branch `(a, l)` it rotates the flag by the angle `θ(a, l)`,
leaving amplitude `cos θ(a, l)` on the selected flag value `false`. The common table is extended by
zero on the flag value `true` (`attTable`), so the selected output reads only the flag `false`.

* `attGate`, `attGate_unitary`: the rotation is a known unitary;
* `atten_compression`: for the product coefficients `π ⊗ attTable c`, any branch-diagonal operator
  `Y` after the rotation selects `(mass c)⁻¹ ∑_{a,l} π_a cos θ(a,l) c_l Y_{(a,l,false)} J_{(a,l,false)}`;
* `lift_comp_self`: the lift of a branch unitary through an isometric encoding (`SubspaceOracle.lift`,
  a fixed gate) intertwines with the encoding;
* `decoded_atten`: the decoded vector of the released joint LCU (`ODEJointSourceLCU.decoded`) for a
  circuit whose compression is `diag Y ∘ attGate θ`.
-/

namespace DysonFullClass

noncomputable section

open SparseHamiltonian ContinuousLinearMap
open scoped BigOperators InnerProduct ComplexConjugate

variable {σ L P : Type*} [Fintype σ] [Fintype L]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The branch space with an attenuation flag: source label, Dyson label and flag. -/
abbrev AttSpace (σ L P : Type*) [Fintype σ] [Fintype L] [NormedAddCommGroup P] :=
  PiLp 2 (fun _ : σ × (L × Bool) => P)

/-- The rotation `[[cos θ, -ε sin θ], [ε sin θ, cos θ]]` (`ε = ±1`) of the flag of every branch. -/
def rotGate (ε : ℝ) (θ : σ × L → ℝ) : AttSpace σ L P →L[ℂ] AttSpace σ L P :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : σ × (L × Bool) => P)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun b : σ × (L × Bool) =>
      if b.2.2 then
        ((ε * Real.sin (θ (b.1, b.2.1)) : ℝ) : ℂ) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ × (L × Bool) => P)
              (b.1, (b.2.1, false)) +
          ((Real.cos (θ (b.1, b.2.1)) : ℝ) : ℂ) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ × (L × Bool) => P)
              (b.1, (b.2.1, true))
      else
        ((Real.cos (θ (b.1, b.2.1)) : ℝ) : ℂ) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ × (L × Bool) => P)
              (b.1, (b.2.1, false)) -
          ((ε * Real.sin (θ (b.1, b.2.1)) : ℝ) : ℂ) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ × (L × Bool) => P)
              (b.1, (b.2.1, true))).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : σ × (L × Bool) => P)).toContinuousLinearMap)

omit [CompleteSpace P] in
@[simp] theorem rotGate_false (ε : ℝ) (θ : σ × L → ℝ) (w : AttSpace σ L P) (a : σ) (l : L) :
    rotGate ε θ w (a, (l, false)) =
      ((Real.cos (θ (a, l)) : ℝ) : ℂ) • w (a, (l, false)) -
        ((ε * Real.sin (θ (a, l)) : ℝ) : ℂ) • w (a, (l, true)) := by
  simp [rotGate]

omit [CompleteSpace P] in
@[simp] theorem rotGate_true (ε : ℝ) (θ : σ × L → ℝ) (w : AttSpace σ L P) (a : σ) (l : L) :
    rotGate ε θ w (a, (l, true)) =
      ((ε * Real.sin (θ (a, l)) : ℝ) : ℂ) • w (a, (l, false)) +
        ((Real.cos (θ (a, l)) : ℝ) : ℂ) • w (a, (l, true)) := by
  simp [rotGate]

/-- **The attenuation gate**: rotation of the flag by `θ(a, l)` on branch `(a, l)`. -/
abbrev attGate (θ : σ × L → ℝ) : AttSpace σ L P →L[ℂ] AttSpace σ L P := rotGate 1 θ

omit [CompleteSpace P] in
/-- The two rotations are inverse to each other. -/
theorem rotGate_mul (θ : σ × L → ℝ) (ε : ℝ) (hε : ε * ε = 1) :
    rotGate (P := P) (-ε) θ * rotGate ε θ = 1 := by
  ext w b
  rcases b with ⟨a, l, f⟩
  have hcs := Real.cos_sq_add_sin_sq (θ (a, l))
  have key : ∀ (c s : ℝ), c ^ 2 + s ^ 2 = 1 → ∀ u v : P,
      (c : ℂ) • ((c : ℂ) • u - ((ε * s : ℝ) : ℂ) • v) -
          ((-ε * s : ℝ) : ℂ) • (((ε * s : ℝ) : ℂ) • u + (c : ℂ) • v) = u ∧
        ((-ε * s : ℝ) : ℂ) • ((c : ℂ) • u - ((ε * s : ℝ) : ℂ) • v) +
          (c : ℂ) • (((ε * s : ℝ) : ℂ) • u + (c : ℂ) • v) = v := by
    intro c s hcs u v
    constructor
    · simp only [smul_sub, smul_add, smul_smul]
      have h1 : (c : ℂ) * c + (-(((-ε * s : ℝ) : ℂ) * ((ε * s : ℝ) : ℂ))) = 1 := by
        push_cast
        have : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
        linear_combination (s : ℂ) ^ 2 * this +
          (by exact_mod_cast hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1)
      have h2 : -((c : ℂ) * ((ε * s : ℝ) : ℂ)) - ((-ε * s : ℝ) : ℂ) * (c : ℂ) = 0 := by
        push_cast; ring
      calc _ = ((c : ℂ) * c + (-(((-ε * s : ℝ) : ℂ) * ((ε * s : ℝ) : ℂ)))) • u +
            (-((c : ℂ) * ((ε * s : ℝ) : ℂ)) - ((-ε * s : ℝ) : ℂ) * (c : ℂ)) • v := by
            simp only [add_smul, sub_smul, neg_smul]; abel
        _ = u := by rw [h1, h2, one_smul, zero_smul, add_zero]
    · simp only [smul_sub, smul_add, smul_smul]
      have h1 : ((-ε * s : ℝ) : ℂ) * (c : ℂ) + (c : ℂ) * ((ε * s : ℝ) : ℂ) = 0 := by
        push_cast; ring
      have h2 : -(((-ε * s : ℝ) : ℂ) * ((ε * s : ℝ) : ℂ)) + (c : ℂ) * c = 1 := by
        push_cast
        have : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
        linear_combination (s : ℂ) ^ 2 * this +
          (by exact_mod_cast hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1)
      calc _ = (((-ε * s : ℝ) : ℂ) * (c : ℂ) + (c : ℂ) * ((ε * s : ℝ) : ℂ)) • u +
            (-(((-ε * s : ℝ) : ℂ) * ((ε * s : ℝ) : ℂ)) + (c : ℂ) * c) • v := by
            simp only [add_smul, neg_smul]; abel
        _ = v := by rw [h1, h2, zero_smul, one_smul, zero_add]
  obtain ⟨k1, k2⟩ := key (Real.cos (θ (a, l))) (Real.sin (θ (a, l))) hcs
    (w (a, (l, false))) (w (a, (l, true)))
  cases f
  · rw [mul_apply_eq_comp, rotGate_false, rotGate_false, rotGate_true]
    simpa only [one_apply_eq_self, neg_mul] using k1
  · rw [mul_apply_eq_comp, rotGate_true, rotGate_false, rotGate_true]
    simpa only [one_apply_eq_self, neg_mul] using k2

/-- The adjoint of a rotation is the opposite rotation. -/
theorem rotGate_adjoint (θ : σ × L → ℝ) (ε : ℝ) :
    (rotGate (P := P) ε θ)† = rotGate (-ε) θ := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u w
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [rotGate_false, rotGate_true, inner_add_left, inner_sub_left, inner_add_right,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  push_cast
  ring

/-- **The attenuation gate is unitary.** -/
theorem attGate_unitary (θ : σ × L → ℝ) : OracleCircuit.IsUnitary (attGate (P := P) θ) := by
  constructor
  · rw [star_eq_adjoint, rotGate_adjoint]
    exact rotGate_mul θ 1 (by norm_num)
  · rw [star_eq_adjoint, rotGate_adjoint]
    have h := rotGate_mul (P := P) θ (-1) (by norm_num)
    rwa [neg_neg] at h

/-- The common table extended by zero on the flag value `true`. -/
def attTable (c : L → ℂ) : L × Bool → ℂ := fun i => if i.2 then 0 else c i.1

omit [Fintype σ] in
theorem attTable_mass (c : L → ℂ) :
    ODECoherentLCU.coefficientMass (attTable c) = ODECoherentLCU.coefficientMass c := by
  unfold ODECoherentLCU.coefficientMass attTable
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_bool]
  simp

set_option maxHeartbeats 1000000 in
/-- **The attenuated compression**: for product coefficients `π ⊗ attTable c` with probability
weights `π`, a branch-diagonal operator `Y` applied after the attenuation gate selects
`(mass c)⁻¹ ∑_{a,l} π_a cos θ(a,l) c_l Y_{(a,l,false)} (J_{(a,l,false)} v)`. -/
theorem atten_compression (π : σ → ℝ) (hπ : ∀ a, 0 ≤ π a) (hπsum : ∑ a, π a = 1)
    (c : L → ℂ) (θ : σ × L → ℝ) (Y : σ × (L × Bool) → P →L[ℂ] P)
    (J : σ × (L × Bool) → P →L[ℂ] P) (v : P) :
    ((ODECoherentLCU.outputEmbedding (ODESourceCoefficients.productCoeff π (attTable c))
        (fun _ => (1 : P →L[ℂ] P)))†)
      (WeightedClock.diagonal Y (attGate θ (ODECoherentLCU.inputEmbedding
        (ODESourceCoefficients.productCoeff π (attTable c)) J v))) =
    ((ODECoherentLCU.coefficientMass c : ℝ) : ℂ)⁻¹ •
      ∑ a, ∑ l, (((π a * Real.cos (θ (a, l)) : ℝ) : ℂ) * c l) •
        Y (a, (l, false)) (J (a, (l, false)) v) := by
  set d := ODESourceCoefficients.productCoeff π (attTable c) with hd
  have hmass : ODECoherentLCU.coefficientMass d = ODECoherentLCU.coefficientMass c := by
    rw [hd, ODESourceCoefficients.coefficientMass_normalized π _ hπ hπsum, attTable_mass]
  have hprob_true : ∀ a l, ODECoherentLCU.coefficientProbability d (a, (l, true)) = 0 := by
    intro a l
    simp [ODECoherentLCU.coefficientProbability, hd, ODESourceCoefficients.productCoeff, attTable]
  have hprob_false : ∀ a l, ODECoherentLCU.coefficientProbability d (a, (l, false)) =
      π a * ‖c l‖ / ODECoherentLCU.coefficientMass c := by
    intro a l
    rw [ODECoherentLCU.coefficientProbability, hmass]
    congr 1
    simp only [hd, ODESourceCoefficients.productCoeff, attTable, Bool.false_eq_true, if_false,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hπ a)]
  have hdv : ∀ a l, d (a, (l, false)) = (π a : ℂ) * c l := by
    intro a l
    simp [hd, ODESourceCoefficients.productCoeff, attTable]
  have hphase : ∀ a l, ((ODECoherentLCU.coefficientProbability d (a, (l, false)) : ℝ) : ℂ) *
      ODECoherentLCU.coefficientPhase (d (a, (l, false))) =
        ((ODECoherentLCU.coefficientMass c : ℝ) : ℂ)⁻¹ * ((π a : ℂ) * c l) := by
    intro a l
    rw [hprob_false, hdv]
    have hn : ‖(π a : ℂ) * c l‖ = π a * ‖c l‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hπ a)]
    calc ((π a * ‖c l‖ / ODECoherentLCU.coefficientMass c : ℝ) : ℂ) *
          ODECoherentLCU.coefficientPhase ((π a : ℂ) * c l)
        = ((ODECoherentLCU.coefficientMass c : ℝ) : ℂ)⁻¹ *
            ((‖(π a : ℂ) * c l‖ : ℂ) * ODECoherentLCU.coefficientPhase ((π a : ℂ) * c l)) := by
          rw [hn]; push_cast; ring
      _ = _ := by rw [ODECoherentLCU.norm_mul_coefficientPhase]
  -- the adjoint of the phased output embedding
  have hout : ∀ w : AttSpace σ L P,
      ((ODECoherentLCU.outputEmbedding d (fun _ => (1 : P →L[ℂ] P)))†) w =
        ∑ b, ((Real.sqrt (ODECoherentLCU.coefficientProbability d b) : ℝ) : ℂ) •
          (ODECoherentLCU.coefficientPhase (d b) • w b) := by
    intro w
    unfold ODECoherentLCU.outputEmbedding
    rw [WeightedClock.boundary_adjoint_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [map_smulₛₗ, starRingEnd_self_apply, smul_apply, one_def,
      adjoint_id, id_apply]
  rw [hout, Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.sum_bool]
  have hsqt : Real.sqrt (ODECoherentLCU.coefficientProbability d (a, (l, true))) = 0 := by
    rw [hprob_true, Real.sqrt_zero]
  have hin_true : ODECoherentLCU.inputEmbedding d J v (a, (l, true)) = 0 := by
    rw [ODECoherentLCU.inputEmbedding, WeightedClock.boundary_apply, hsqt, Complex.ofReal_zero,
      zero_smul]
  have hin_false : ODECoherentLCU.inputEmbedding d J v (a, (l, false)) =
      ((Real.sqrt (ODECoherentLCU.coefficientProbability d (a, (l, false))) : ℝ) : ℂ) •
        J (a, (l, false)) v := rfl
  have hR : attGate θ (ODECoherentLCU.inputEmbedding d J v) (a, (l, false)) =
      ((Real.cos (θ (a, l)) : ℝ) : ℂ) •
        (((Real.sqrt (ODECoherentLCU.coefficientProbability d (a, (l, false))) : ℝ) : ℂ) •
          J (a, (l, false)) v) := by
    rw [rotGate_false, hin_true, hin_false, smul_zero, sub_zero]
  have hp0 := ODECoherentLCU.coefficientProbability_nonneg d (a, (l, false))
  have hsq : ((Real.sqrt (ODECoherentLCU.coefficientProbability d (a, (l, false))) : ℝ) : ℂ) *
      ((Real.sqrt (ODECoherentLCU.coefficientProbability d (a, (l, false))) : ℝ) : ℂ) =
        ((ODECoherentLCU.coefficientProbability d (a, (l, false)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  rw [hsqt, Complex.ofReal_zero, zero_smul, WeightedClock.diagonal_apply, hR, map_smul, map_smul,
    smul_smul, smul_smul, smul_smul, smul_smul, zero_add]
  congr 1
  calc _ = (((Real.sqrt (ODECoherentLCU.coefficientProbability d (a, (l, false))) : ℝ) : ℂ) *
          ((Real.sqrt (ODECoherentLCU.coefficientProbability d (a, (l, false))) : ℝ) : ℂ)) *
          ODECoherentLCU.coefficientPhase (d (a, (l, false))) *
          ((Real.cos (θ (a, l)) : ℝ) : ℂ) := by ring
    _ = ((ODECoherentLCU.coefficientMass c : ℝ) : ℂ)⁻¹ * ((π a : ℂ) * c l) *
          ((Real.cos (θ (a, l)) : ℝ) : ℂ) := by rw [hsq, hphase]
    _ = _ := by push_cast; ring

/-! ### Fixed gates on the encoded branch space -/

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Fintype σ] [Fintype L] [CompleteSpace P] in
/-- The lift of a branch operator through an isometric encoding intertwines with the encoding. -/
theorem lift_comp_self {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
    (E : Q →L[ℂ] K) (hE : E† ∘L E = 1) (U : Q →L[ℂ] Q) :
    SubspaceOracle.lift E U ∘L E = E ∘L U := by
  have hEv : ∀ q, (E†) (E q) = q := fun q => by
    simpa using congrArg (fun A : Q →L[ℂ] Q => A q) hE
  ext q
  simp only [SubspaceOracle.lift, comp_apply, add_apply, one_apply_eq_self, sub_apply, hEv,
    map_sub]
  abel

/-- **The decoded vector with attenuation**: if the compression of `W` is `diag Y ∘ attGate θ`,
the released joint-LCU decoded vector for the product coefficients `π ⊗ attTable c` is
`(mass c)⁻¹ ∑_{a,l} π_a cos θ(a,l) c_l Y_{(a,l,false)} (J_{(a,l,false)} v)`. -/
theorem decoded_atten (E : AttSpace σ L P →L[ℂ] K) (W : K →L[ℂ] K)
    (π : σ → ℝ) (hπ : ∀ a, 0 ≤ π a) (hπsum : ∑ a, π a = 1)
    (c : L → ℂ) (θ : σ × L → ℝ) (Y : σ × (L × Bool) → P →L[ℂ] P)
    (hW : E† ∘L W ∘L E = WeightedClock.diagonal Y ∘L attGate θ)
    (J : σ × (L × Bool) → P →L[ℂ] P) (v : P) :
    ODEJointSourceLCU.decoded E (ODESourceCoefficients.productCoeff π (attTable c)) J W v =
      ((ODECoherentLCU.coefficientMass c : ℝ) : ℂ)⁻¹ •
        ∑ a, ∑ l, (((π a * Real.cos (θ (a, l)) : ℝ) : ℂ) * c l) •
          Y (a, (l, false)) (J (a, (l, false)) v) := by
  rw [← atten_compression π hπ hπsum c θ Y J v]
  have h := congrArg (fun A => A (ODECoherentLCU.inputEmbedding
    (ODESourceCoefficients.productCoeff π (attTable c)) J v)) hW
  simp only [comp_apply] at h
  simp only [ODEJointSourceLCU.decoded, ODEHeraldedSuccess.decoded, ODEJointSourceLCU.input,
    ODEJointLCU.output, ODEJointLCU.coefficientOutput, adjoint_comp, comp_apply, h]

end

end DysonFullClass
