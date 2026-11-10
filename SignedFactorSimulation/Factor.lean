import OptimalPrecision.Tail.Transfer
import SparseHamiltonian.OracleCircuit

/-!
# The factor interface and the three-phase private unitary

The interface `opt:eq:factor` of Theorem `opt:thm:signed`: a known initialised-input
isometry `E : P → W`, a known success projection `Π` and a known Hermitian unitary `Z` on the
success space (here a Hermitian unitary on `W` commuting with `Π`), and a supplied unitary
`U = U_B`. The factor is `B = Π U E`, with

  `C = B† Z B`, `D = B† B`,

so that `-D ⪯ C ⪯ D` (`neg_Dop_le_Cop`, `Cop_le_Dop`) and `0 ⪯ D` (`Dop_nonneg`).

For `q > 0`, the private unitary of `opt:eq:private-unitary` is `P = U† G U`, where `G` is the
Cayley transform of `K = qZ` on success and `0` on failure (`phase`, `phase_cayley`): its
eigenvalues are `ζ_± = (±q + i)/(±q - i)` and `-1`, with spectral projections
`Π_± = Π(1 ± Z)/2` and `I - Π`. Everything is computed in the commutative algebra of
spectral sums `spec a b c = a (I - Π) + b Π_+ + c Π_-` (`spec_mul`).

The main result is `opt:eq:omega`: for `|w| < 1`,

  `E† (I + wP)(I - wP)⁻¹ E = ξ(w) I + R(w)(iqC + q² ξ(w) D) = Tail.Omega q C D w`

(`omega_eq`), where `(I - wP)⁻¹` is the actual inverse (`Ring.inverse`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Complex ContinuousLinearMap OptimalPrecision OptimalPrecision.Tail
open SparseHamiltonian
open scoped InnerProduct ComplexOrder

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The known data of the factor interface `opt:eq:factor`: the initialised-input isometry
`E`, the success projection `proj` (`Π`) and the success reflection `Z`, a Hermitian unitary
commuting with `Π`. -/
structure Known (P W : Type*)
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] where
  /-- The initialised-input isometry. -/
  E : P →L[ℂ] W
  /-- The success projection `Π`. -/
  proj : W →L[ℂ] W
  /-- The success reflection. -/
  Z : W →L[ℂ] W
  E_isometry : E† ∘L E = 1
  proj_adjoint : proj† = proj
  proj_idem : proj * proj = proj
  Z_adjoint : Z† = Z
  Z_sq : Z * Z = 1
  Z_comm : Z * proj = proj * Z

namespace Known

variable (K : Known P W)

/-! ### The factor and its compressions -/

/-- The factor `B = Π U E`. -/
def factor (U : W →L[ℂ] W) : P →L[ℂ] W := K.proj ∘L U ∘L K.E

/-- The signed compression `C = B† Z B`. -/
def Cop (U : W →L[ℂ] W) : P →L[ℂ] P := (K.factor U)† ∘L K.Z ∘L K.factor U

/-- The total successful weight `D = B† B`. -/
def Dop (U : W →L[ℂ] W) : P →L[ℂ] P := (K.factor U)† ∘L K.factor U

theorem Dop_nonneg (U : W →L[ℂ] W) : 0 ≤ K.Dop U := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact isPositive_adjoint_comp_self _

theorem complex_two_inv_nonneg : (0 : ℂ) ≤ 2⁻¹ := by
  rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl]
  exact Complex.zero_le_real.mpr (by norm_num)

/-- `I ± Z` are positive: `I ± Z = (I ± Z)†(I ± Z)/2`. -/
theorem one_add_Z_isPositive : (1 + K.Z).IsPositive := by
  have h : (1 + K.Z) = (2⁻¹ : ℂ) • ((1 + K.Z)† ∘L (1 + K.Z)) := by
    rw [map_add, adjoint_one, K.Z_adjoint]
    change 1 + K.Z = (2⁻¹ : ℂ) • ((1 + K.Z) * (1 + K.Z))
    rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, K.Z_sq]
    rw [show (1 : W →L[ℂ] W) + K.Z + (K.Z + 1) = (2 : ℂ) • (1 + K.Z) by
      rw [two_smul]; abel, smul_smul]
    norm_num
  rw [h]
  exact (isPositive_adjoint_comp_self _).smul_of_nonneg complex_two_inv_nonneg

theorem one_sub_Z_isPositive : (1 - K.Z).IsPositive := by
  have h : (1 - K.Z) = (2⁻¹ : ℂ) • ((1 - K.Z)† ∘L (1 - K.Z)) := by
    rw [map_sub, adjoint_one, K.Z_adjoint]
    change 1 - K.Z = (2⁻¹ : ℂ) • ((1 - K.Z) * (1 - K.Z))
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, K.Z_sq]
    rw [show (1 : W →L[ℂ] W) - K.Z - (K.Z - 1) = (2 : ℂ) • (1 - K.Z) by
      rw [two_smul]; abel, smul_smul]
    norm_num
  rw [h]
  exact (isPositive_adjoint_comp_self _).smul_of_nonneg complex_two_inv_nonneg

theorem Dop_add_Cop (U : W →L[ℂ] W) :
    K.Dop U + K.Cop U = (K.factor U)† ∘L (1 + K.Z) ∘L K.factor U := by
  simp only [Dop, Cop, add_comp, comp_add, one_def, id_comp]

theorem Dop_sub_Cop (U : W →L[ℂ] W) :
    K.Dop U - K.Cop U = (K.factor U)† ∘L (1 - K.Z) ∘L K.factor U := by
  simp only [Dop, Cop, sub_comp, comp_sub, one_def, id_comp]

/-- `-D ⪯ C`. -/
theorem neg_Dop_le_Cop (U : W →L[ℂ] W) : -K.Dop U ≤ K.Cop U := by
  rw [ContinuousLinearMap.le_def, sub_neg_eq_add, add_comm, K.Dop_add_Cop]
  exact K.one_add_Z_isPositive.adjoint_conj _

/-- `C ⪯ D`. -/
theorem Cop_le_Dop (U : W →L[ℂ] W) : K.Cop U ≤ K.Dop U := by
  rw [ContinuousLinearMap.le_def, K.Dop_sub_Cop]
  exact K.one_sub_Z_isPositive.adjoint_conj _

/-! ### Spectral sums -/

/-- The projection `Π_+ = Π(1 + Z)/2`. -/
def plus : W →L[ℂ] W := (2⁻¹ : ℂ) • (K.proj + K.Z * K.proj)

/-- The projection `Π_- = Π(1 - Z)/2`. -/
def minus : W →L[ℂ] W := (2⁻¹ : ℂ) • (K.proj - K.Z * K.proj)

/-- The spectral sum `a (I - Π) + b Π_+ + c Π_-`. -/
def spec (a b c : ℂ) : W →L[ℂ] W := a • (1 - K.proj) + b • K.plus + c • K.minus

theorem proj_Z_proj : K.proj * (K.Z * K.proj) = K.Z * K.proj := by
  rw [← mul_assoc, ← K.Z_comm, mul_assoc, K.proj_idem]

theorem Z_proj_proj : K.Z * K.proj * K.proj = K.Z * K.proj := by
  rw [mul_assoc, K.proj_idem]

theorem Z_proj_Z_proj : K.Z * K.proj * (K.Z * K.proj) = K.proj := by
  rw [mul_assoc, K.proj_Z_proj, ← mul_assoc, K.Z_sq, one_mul]

theorem plus_mul_plus : K.plus * K.plus = K.plus := by
  simp only [plus, smul_mul_smul, add_mul, mul_add, K.proj_idem, K.proj_Z_proj, K.Z_proj_proj,
    K.Z_proj_Z_proj]
  module

theorem minus_mul_minus : K.minus * K.minus = K.minus := by
  simp only [minus, smul_mul_smul, sub_mul, mul_sub, K.proj_idem, K.proj_Z_proj, K.Z_proj_proj,
    K.Z_proj_Z_proj]
  module

theorem plus_mul_minus : K.plus * K.minus = 0 := by
  simp only [plus, minus, smul_mul_smul, add_mul, mul_sub, K.proj_idem, K.proj_Z_proj,
    K.Z_proj_proj, K.Z_proj_Z_proj]
  module

theorem minus_mul_plus : K.minus * K.plus = 0 := by
  simp only [plus, minus, smul_mul_smul, sub_mul, mul_add, K.proj_idem, K.proj_Z_proj,
    K.Z_proj_proj, K.Z_proj_Z_proj]
  module

theorem compl_mul_plus : (1 - K.proj) * K.plus = 0 := by
  simp only [plus, mul_smul_comm, sub_mul, one_mul, mul_add, K.proj_idem, K.proj_Z_proj]
  module

theorem compl_mul_minus : (1 - K.proj) * K.minus = 0 := by
  simp only [minus, mul_smul_comm, sub_mul, one_mul, mul_sub, K.proj_idem, K.proj_Z_proj]
  module

theorem plus_mul_compl : K.plus * (1 - K.proj) = 0 := by
  simp only [plus, smul_mul_assoc, mul_sub, mul_one, add_mul, K.proj_idem, K.Z_proj_proj]
  module

theorem minus_mul_compl : K.minus * (1 - K.proj) = 0 := by
  simp only [minus, smul_mul_assoc, mul_sub, mul_one, sub_mul, K.proj_idem, K.Z_proj_proj]
  module

theorem compl_mul_compl : (1 - K.proj) * (1 - K.proj) = 1 - K.proj := by
  rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, K.proj_idem]
  abel

theorem plus_add_minus : K.plus + K.minus = K.proj := by
  simp only [plus, minus]
  module

theorem spec_one : K.spec 1 1 1 = 1 := by
  simp only [spec, one_smul]
  rw [add_assoc, K.plus_add_minus]
  abel

theorem spec_mul (a b c a' b' c' : ℂ) :
    K.spec a b c * K.spec a' b' c' = K.spec (a * a') (b * b') (c * c') := by
  simp only [spec, add_mul, mul_add, smul_mul_smul, K.compl_mul_compl, K.compl_mul_plus,
    K.compl_mul_minus, K.plus_mul_compl, K.plus_mul_plus, K.plus_mul_minus, K.minus_mul_compl,
    K.minus_mul_plus, K.minus_mul_minus, smul_zero, add_zero, zero_add]

theorem spec_add (a b c a' b' c' : ℂ) :
    K.spec a b c + K.spec a' b' c' = K.spec (a + a') (b + b') (c + c') := by
  simp only [spec, add_smul]
  abel

theorem spec_smul (s a b c : ℂ) : s • K.spec a b c = K.spec (s * a) (s * b) (s * c) := by
  simp only [spec, smul_add, smul_smul]

theorem spec_sub (a b c a' b' c' : ℂ) :
    K.spec a b c - K.spec a' b' c' = K.spec (a - a') (b - b') (c - c') := by
  simp only [spec, sub_smul]
  abel

theorem Zproj_adjoint : (K.Z * K.proj)† = K.Z * K.proj := by
  change (K.Z ∘L K.proj)† = K.Z ∘L K.proj
  rw [adjoint_comp, K.proj_adjoint, K.Z_adjoint]
  exact K.Z_comm.symm

theorem plus_adjoint : K.plus† = K.plus := by
  simp only [plus, map_smulₛₗ, map_add, K.proj_adjoint, K.Zproj_adjoint, map_inv₀, map_ofNat]

theorem minus_adjoint : K.minus† = K.minus := by
  simp only [minus, map_smulₛₗ, map_sub, K.proj_adjoint, K.Zproj_adjoint, map_inv₀, map_ofNat]

theorem spec_adjoint (a b c : ℂ) :
    (K.spec a b c)† = K.spec (starRingEnd ℂ a) (starRingEnd ℂ b) (starRingEnd ℂ c) := by
  simp only [spec, map_add, map_smulₛₗ, map_sub, adjoint_one, K.proj_adjoint, K.plus_adjoint,
    K.minus_adjoint]

/-! ### The phase and its resolvent -/

/-- `ζ_+ = (q + i)/(q - i)`. -/
def zetaP (q : ℝ) : ℂ := ((q : ℂ) + I) / ((q : ℂ) - I)

/-- `ζ_- = (-q + i)/(-q - i)`. -/
def zetaM (q : ℝ) : ℂ := (-(q : ℂ) + I) / (-(q : ℂ) - I)

theorem ofReal_sub_I_ne_zero (q : ℝ) : (q : ℂ) - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem neg_ofReal_sub_I_ne_zero (q : ℝ) : -(q : ℂ) - I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

theorem norm_zetaP (q : ℝ) : ‖zetaP q‖ = 1 := by
  rw [zetaP, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (ofReal_sub_I_ne_zero q)),
    ← Complex.norm_conj]
  congr 1
  apply Complex.ext <;> simp

theorem norm_zetaM (q : ℝ) : ‖zetaM q‖ = 1 := by
  rw [zetaM, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr (neg_ofReal_sub_I_ne_zero q)),
    ← Complex.norm_conj]
  congr 1
  apply Complex.ext <;> simp

theorem conj_mul_self_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : starRingEnd ℂ z * z = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- The known Cayley phase `G`: `-1` on failure and `ζ_±` on the two success eigenspaces. -/
def phase (q : ℝ) : W →L[ℂ] W := K.spec (-1) (zetaP q) (zetaM q)

theorem phase_adjoint_mul (q : ℝ) : (K.phase q)† * K.phase q = 1 := by
  rw [phase, spec_adjoint, spec_mul, ← K.spec_one, conj_mul_self_of_norm_one (norm_zetaP q),
    conj_mul_self_of_norm_one (norm_zetaM q)]
  congr 1
  simp

theorem phase_mul_adjoint (q : ℝ) : K.phase q * (K.phase q)† = 1 := by
  rw [phase, spec_adjoint, spec_mul, ← K.spec_one, mul_comm (zetaP q), mul_comm (zetaM q),
    conj_mul_self_of_norm_one (norm_zetaP q), conj_mul_self_of_norm_one (norm_zetaM q)]
  congr 1
  simp

theorem phase_isUnitary (q : ℝ) : OracleCircuit.IsUnitary (K.phase q) := by
  refine ⟨?_, ?_⟩
  · change (K.phase q)† * K.phase q = 1
    exact K.phase_adjoint_mul q
  · change K.phase q * (K.phase q)† = 1
    exact K.phase_mul_adjoint q

/-- The phase is the Cayley transform of `K = q Z Π`: `(K - i) G = K + i`
(`opt:eq:private-unitary`). -/
theorem phase_cayley (q : ℝ) :
    ((q : ℂ) • (K.Z * K.proj) - I • 1) * K.phase q = (q : ℂ) • (K.Z * K.proj) + I • 1 := by
  have hK : K.Z * K.proj = K.spec 0 1 (-1) := by
    simp only [spec, plus, minus, zero_smul, zero_add, one_smul, neg_smul]
    module
  have hm : (q : ℂ) • (K.Z * K.proj) - I • (1 : W →L[ℂ] W) =
      K.spec (-I) ((q : ℂ) - I) (-(q : ℂ) - I) := by
    rw [hK, ← K.spec_one, K.spec_smul, K.spec_smul, K.spec_sub]
    congr 1 <;> ring
  have hp : (q : ℂ) • (K.Z * K.proj) + I • (1 : W →L[ℂ] W) =
      K.spec I ((q : ℂ) + I) (-(q : ℂ) + I) := by
    rw [hK, ← K.spec_one, K.spec_smul, K.spec_smul, K.spec_add]
    congr 1 <;> ring
  rw [hm, hp, phase, K.spec_mul]
  congr 1
  · ring
  · rw [zetaP, mul_div_cancel₀ _ (ofReal_sub_I_ne_zero q)]
  · rw [zetaM, mul_div_cancel₀ _ (neg_ofReal_sub_I_ne_zero q)]

/-! ### Scalars on the disk -/

theorem one_sub_zeta_mul_ne_zero {ζ : ℂ} (hζ : ‖ζ‖ = 1) {w : ℂ} (hw : ‖w‖ < 1) :
    1 - ζ * w ≠ 0 := by
  intro h
  have h1 : ζ * w = 1 := (sub_eq_zero.mp h).symm
  have := congrArg norm h1
  rw [norm_mul, hζ, one_mul, norm_one] at this
  linarith

/-- `(1 + ζ_+ w)/(1 - ζ_+ w) = μ_+`. -/
theorem muP_eq {q : ℝ} {w : ℂ} (hw : ‖w‖ < 1) :
    (1 + zetaP q * w) / (1 - zetaP q * w) = muP q w := by
  have hd : (1 + w) ≠ 0 := one_add_ne_zero_of_norm_lt hw
  have hs := ofReal_sub_I_ne_zero q
  have hz := one_sub_zeta_mul_ne_zero (norm_zetaP q) hw
  have hz' : ((q : ℂ) - I) - ((q : ℂ) + I) * w ≠ 0 := by
    intro h
    apply hz
    rw [zetaP, div_mul_eq_mul_div, one_sub_div hs, h, zero_div]
  have hden : (q : ℂ) * xi w - I ≠ 0 := by
    rw [xi]
    intro h
    apply hz'
    have : ((q : ℂ) * ((1 - w) / (1 + w)) - I) * (1 + w) = 0 := by rw [h, zero_mul]
    rw [← this]
    field_simp
    ring
  rw [muP, div_eq_div_iff hz hden, zetaP, xi]
  field_simp
  ring

/-- `(1 + ζ_- w)/(1 - ζ_- w) = μ_-`. -/
theorem muM_eq {q : ℝ} {w : ℂ} (hw : ‖w‖ < 1) :
    (1 + zetaM q * w) / (1 - zetaM q * w) = muM q w := by
  have hd : (1 + w) ≠ 0 := one_add_ne_zero_of_norm_lt hw
  have hs := neg_ofReal_sub_I_ne_zero q
  have hz := one_sub_zeta_mul_ne_zero (norm_zetaM q) hw
  have hz' : (-(q : ℂ) - I) - (-(q : ℂ) + I) * w ≠ 0 := by
    intro h
    apply hz
    rw [zetaM, div_mul_eq_mul_div, one_sub_div hs, h, zero_div]
  have hden : (q : ℂ) * xi w + I ≠ 0 := by
    rw [xi]
    intro h
    apply hz'
    have : ((q : ℂ) * ((1 - w) / (1 + w)) + I) * (1 + w) = 0 := by rw [h, zero_mul]
    rw [← neg_eq_zero, ← this]
    field_simp
    ring
  rw [muM, div_eq_div_iff hz hden, zetaM, xi]
  field_simp
  ring

/-- `(1 - w)/(1 + w) = ξ(w)` for the failure eigenvalue `-1`. -/
theorem xi_eq_failure (w : ℂ) : (1 + -1 * w) / (1 - -1 * w) = xi w := by
  rw [xi]
  ring_nf

/-- The resolvent of the phase, `(I - wG)⁻¹`, as a spectral sum. -/
def phaseResolvent (q : ℝ) (w : ℂ) : W →L[ℂ] W :=
  K.spec (1 - -1 * w)⁻¹ (1 - zetaP q * w)⁻¹ (1 - zetaM q * w)⁻¹

theorem one_sub_smul_phase (q : ℝ) (w : ℂ) :
    1 - w • K.phase q = K.spec (1 - -1 * w) (1 - zetaP q * w) (1 - zetaM q * w) := by
  rw [phase, K.spec_smul, ← K.spec_one]
  simp only [spec]
  module

theorem one_add_smul_phase (q : ℝ) (w : ℂ) :
    1 + w • K.phase q = K.spec (1 + -1 * w) (1 + zetaP q * w) (1 + zetaM q * w) := by
  rw [phase, K.spec_smul, ← K.spec_one]
  simp only [spec]
  module

theorem one_sub_smul_phase_mul_resolvent (q : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    (1 - w • K.phase q) * K.phaseResolvent q w = 1 := by
  have h1 : (1 : ℂ) - -1 * w ≠ 0 := by
    rw [neg_one_mul, sub_neg_eq_add]; exact one_add_ne_zero_of_norm_lt hw
  rw [one_sub_smul_phase, phaseResolvent, spec_mul, mul_inv_cancel₀ h1,
    mul_inv_cancel₀ (one_sub_zeta_mul_ne_zero (norm_zetaP q) hw),
    mul_inv_cancel₀ (one_sub_zeta_mul_ne_zero (norm_zetaM q) hw), K.spec_one]

theorem resolvent_mul_one_sub_smul_phase (q : ℝ) {w : ℂ} (hw : ‖w‖ < 1) :
    K.phaseResolvent q w * (1 - w • K.phase q) = 1 := by
  have h1 : (1 : ℂ) - -1 * w ≠ 0 := by
    rw [neg_one_mul, sub_neg_eq_add]; exact one_add_ne_zero_of_norm_lt hw
  rw [one_sub_smul_phase, phaseResolvent, spec_mul, inv_mul_cancel₀ h1,
    inv_mul_cancel₀ (one_sub_zeta_mul_ne_zero (norm_zetaP q) hw),
    inv_mul_cancel₀ (one_sub_zeta_mul_ne_zero (norm_zetaM q) hw), K.spec_one]

/-- `(I + wG)(I - wG)⁻¹ = ξ (I - Π) + μ_+ Π_+ + μ_- Π_-`. -/
theorem one_add_smul_phase_mul_resolvent {q : ℝ} {w : ℂ} (hw : ‖w‖ < 1) :
    (1 + w • K.phase q) * K.phaseResolvent q w = K.spec (xi w) (muP q w) (muM q w) := by
  rw [one_add_smul_phase, phaseResolvent, spec_mul, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ← div_eq_mul_inv, xi_eq_failure, muP_eq hw, muM_eq hw]

/-! ### The private unitary and the generator -/

/-- The private unitary `P = U† G U` of `opt:eq:private-unitary`. -/
def priv (q : ℝ) (U : W →L[ℂ] W) : W →L[ℂ] W := U† * K.phase q * U

theorem priv_isUnitary (q : ℝ) {U : W →L[ℂ] W} (hU : OracleCircuit.IsUnitary U) :
    OracleCircuit.IsUnitary (K.priv q U) := by
  have hU' := hU.adjoint
  exact (hU'.mul (K.phase_isUnitary q)).mul hU

/-- The compression `X ↦ E† U† X U E`. -/
def compress (U X : W →L[ℂ] W) : P →L[ℂ] P := K.E† ∘L (U† * X * U) ∘L K.E

theorem compress_add (U X Y : W →L[ℂ] W) :
    K.compress U (X + Y) = K.compress U X + K.compress U Y := by
  simp only [compress, mul_add, add_mul, add_comp, comp_add]

theorem compress_sub (U X Y : W →L[ℂ] W) :
    K.compress U (X - Y) = K.compress U X - K.compress U Y := by
  simp only [compress, mul_sub, sub_mul, sub_comp, comp_sub]

theorem compress_smul (U X : W →L[ℂ] W) (a : ℂ) :
    K.compress U (a • X) = a • K.compress U X := by
  simp only [compress, mul_smul_comm, smul_mul_assoc, smul_comp, comp_smul]

theorem compress_one (U : W →L[ℂ] W) (hU : U† * U = 1) : K.compress U 1 = 1 := by
  rw [compress, mul_one, hU]
  exact K.E_isometry

theorem compress_proj (U : W →L[ℂ] W) : K.compress U K.proj = K.Dop U := by
  simp only [compress, Dop, factor, adjoint_comp, K.proj_adjoint]
  change K.E† ∘L U† ∘L K.proj ∘L U ∘L K.E = K.E† ∘L U† ∘L K.proj ∘L K.proj ∘L U ∘L K.E
  rw [← comp_assoc K.proj K.proj, show K.proj ∘L K.proj = K.proj from K.proj_idem]

theorem compress_Zproj (U : W →L[ℂ] W) : K.compress U (K.Z * K.proj) = K.Cop U := by
  simp only [compress, Cop, factor, adjoint_comp, K.proj_adjoint]
  change K.E† ∘L U† ∘L (K.Z ∘L K.proj) ∘L U ∘L K.E =
    K.E† ∘L U† ∘L K.proj ∘L K.Z ∘L K.proj ∘L U ∘L K.E
  rw [← comp_assoc K.Z K.proj, ← comp_assoc K.proj (K.Z ∘L K.proj),
    show K.proj ∘L (K.Z ∘L K.proj) = K.Z * K.proj from K.proj_Z_proj]
  rfl

/-- The compression of a spectral sum: `E† U† (a (I - Π) + b Π_+ + c Π_-) U E =
a (I - D) + b (D + C)/2 + c (D - C)/2`. -/
theorem compress_spec (U : W →L[ℂ] W) (hU : U† * U = 1) (a b c : ℂ) :
    K.compress U (K.spec a b c) =
      a • (1 - K.Dop U) + (b / 2) • (K.Dop U + K.Cop U) + (c / 2) • (K.Dop U - K.Cop U) := by
  simp only [spec, plus, minus, K.compress_add, K.compress_sub, K.compress_smul,
    K.compress_one U hU, K.compress_proj, K.compress_Zproj]
  module

/-- **The generator `opt:eq:omega`**: for `|w| < 1`, `E† (I + wP)(I - wP)⁻¹ E = Ω(w)`, with the
actual inverse of `I - wP`. -/
theorem omega_eq {q : ℝ} (hq : 0 < q) {U : W →L[ℂ] W} (hU : OracleCircuit.IsUnitary U)
    {w : ℂ} (hw : ‖w‖ < 1) :
    K.E† ∘L ((1 + w • K.priv q U) * Ring.inverse (1 - w • K.priv q U)) ∘L K.E =
      Omega q (K.Cop U) (K.Dop U) w := by
  have hU1 : U† * U = 1 := hU.1
  have hU2 : U * U† = 1 := hU.2
  -- conjugation by `U`
  have hconj : ∀ X : W →L[ℂ] W, U† * X * U * (U† * K.phaseResolvent q w * U) =
      U† * (X * K.phaseResolvent q w) * U := by
    intro X
    calc U† * X * U * (U† * K.phaseResolvent q w * U) =
        U† * X * (U * U†) * K.phaseResolvent q w * U := by noncomm_ring
      _ = U† * (X * K.phaseResolvent q w) * U := by rw [hU2]; noncomm_ring
  have h1 : 1 - w • K.priv q U = U† * (1 - w • K.phase q) * U := by
    simp only [priv, mul_sub, sub_mul, mul_one, hU1, mul_smul_comm, smul_mul_assoc]
  have h2 : 1 + w • K.priv q U = U† * (1 + w • K.phase q) * U := by
    simp only [priv, mul_add, add_mul, mul_one, hU1, mul_smul_comm, smul_mul_assoc]
  have hinv : Ring.inverse (1 - w • K.priv q U) = U† * K.phaseResolvent q w * U := by
    have hr : (1 - w • K.priv q U) * (U† * K.phaseResolvent q w * U) = 1 := by
      rw [h1, hconj, K.one_sub_smul_phase_mul_resolvent q hw, mul_one, hU1]
    have hl : (U† * K.phaseResolvent q w * U) * (1 - w • K.priv q U) = 1 := by
      rw [h1]
      calc U† * K.phaseResolvent q w * U * (U† * (1 - w • K.phase q) * U) =
          U† * K.phaseResolvent q w * (U * U†) * (1 - w • K.phase q) * U := by noncomm_ring
        _ = U† * (K.phaseResolvent q w * (1 - w • K.phase q)) * U := by
          rw [hU2]; noncomm_ring
        _ = 1 := by rw [K.resolvent_mul_one_sub_smul_phase q hw, mul_one, hU1]
    exact Ring.inverse_unit (⟨1 - w • K.priv q U, U† * K.phaseResolvent q w * U, hr, hl⟩ :
      (W →L[ℂ] W)ˣ)
  rw [hinv, h2, hconj, K.one_add_smul_phase_mul_resolvent hw]
  change K.compress U (K.spec (xi w) (muP q w) (muM q w)) = _
  rw [K.compress_spec U hU1, Omega_eq hq hw]

end Known

end

end SignedFactorSimulation
