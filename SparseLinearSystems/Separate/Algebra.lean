import SparseLinearSystems.WalkGap
import SparseLinearSystems.Spectral.UnitaryFilter

/-!
# The enlarged linear system of Corollary `qls:cor:separate`

Assume the hypotheses `WalkGap.Hyp J K H α μ k₀` of Lemma `qls:lem:walk`: an isometry `J`,
a self-adjoint `K` with `J† K J = H/α`. Put

* `D₀ = (K + i)(K - i)⁻¹` (`h.cayley`) and `R₀ = (I + iK)/2` (`WalkGap.resolvent K`),
* `W = (I - 2JJ†) D₀` (`WalkGap.walk J h.cayley`),
* `B = (I - W)/2` (`enlarged`), the enlarged matrix, and `C = (I - D₀)/2` (`decoder`).

For every `u` (not only kernel vectors of `H`):

* `(I - W) R₀ J u = (i/α) J H u` (`one_sub_walk_resolvent`, eq. `qls:eq:separate-identity`);
* `B ((-2iα) R₀ J u) = J H u` (`enlarged_solution`) and `C ((-2iα) R₀ J u) = -iα J u`
  (`decoder_solution`, eqs. `qls:eq:separate-solution` and `qls:eq:separate-decoder`);
* `‖(-2iα) R₀ J u‖² = α² (‖u‖² + ‖K J u‖²)` (`solution_norm_sq`, eq. `qls:eq:separate-norm`).

If `H` is injective, the walk has no nonzero fixed vector on the whole space
(`walk_fixed_eq_zero`). With the phase gap of Lemma `qls:lem:walk`, which includes the
eigenvalue `-1`, `b ‖v‖ ≤ ‖B v‖` for every `v`, where `b = t*/√(1 + t*²)` (`enlarged_lower`).
The decoder is a contraction (`decoder_norm_le`).
-/

set_option autoImplicit false

namespace SparseLinearSystems.Separate

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P] [CompleteSpace P]
variable {J : P →L[ℂ] V} {K : V →L[ℂ] V} {H : P →L[ℂ] P} {α μ k₀ : ℝ}

/-- The enlarged matrix `B = (I - W)/2` (eq. `qls:eq:separate-system`). -/
def enlarged (h : WalkGap.Hyp J K H α μ k₀) : V →L[ℂ] V :=
  (2 : ℂ)⁻¹ • (1 - WalkGap.walk J h.cayley)

/-- The decoder `C = (I - D₀)/2` (eq. `qls:eq:separate-decoder`). -/
def decoder (h : WalkGap.Hyp J K H α μ k₀) : V →L[ℂ] V :=
  (2 : ℂ)⁻¹ • (1 - h.cayley)

/-- The scalar `-2iα` of the enlarged solution `y = -2iα R₀ J z`. -/
abbrev solScale (α : ℝ) : ℂ := -2 * Complex.I * (α : ℂ)

omit [FiniteDimensional ℂ P] in
theorem enlarged_apply (h : WalkGap.Hyp J K H α μ k₀) (v : V) :
    enlarged h v = (2 : ℂ)⁻¹ • (v - WalkGap.walk J h.cayley v) := by
  simp [enlarged]

omit [FiniteDimensional ℂ P] in
theorem decoder_apply (h : WalkGap.Hyp J K H α μ k₀) (v : V) :
    decoder h v = (2 : ℂ)⁻¹ • (v - h.cayley v) := by
  simp [decoder]

omit [FiniteDimensional ℂ P] in
/-- `D₀ R₀ x = R₀ x - x`, since `(I - D₀) R₀ = I`. -/
theorem cayley_resolvent (h : WalkGap.Hyp J K H α μ k₀) (x : V) :
    h.cayley (WalkGap.resolvent K x) = WalkGap.resolvent K x - x := by
  have e := WalkGap.one_sub_cayley_resolvent h x
  calc h.cayley (WalkGap.resolvent K x)
      = WalkGap.resolvent K x -
          (WalkGap.resolvent K x - h.cayley (WalkGap.resolvent K x)) := by abel
    _ = _ := by rw [e]

omit [FiniteDimensional ℂ P] in
/-- The walk on a lifted vector: `W R₀ J u = R₀ J u - (i/α) J H u`. -/
theorem walk_resolvent (h : WalkGap.Hyp J K H α μ k₀) (u : P) :
    WalkGap.walk J h.cayley (WalkGap.resolvent K (J u)) =
      WalkGap.resolvent K (J u) - (Complex.I * (α : ℂ)⁻¹) • J (H u) := by
  have hJ : (J†) (WalkGap.resolvent K (J u)) =
      (2 : ℂ)⁻¹ • (u + (Complex.I * (α : ℂ)⁻¹) • H u) := by
    rw [WalkGap.resolvent_apply, map_smul, map_add, WalkGap.isometry_apply h.isometry, map_smul,
      h.compression_apply, smul_smul]
  rw [WalkGap.walk, mul_apply_eq_comp, cayley_resolvent h, WalkGap.reflection_apply,
    map_sub, hJ, WalkGap.isometry_apply h.isometry, map_sub, map_smul, map_add, map_smul]
  module

omit [FiniteDimensional ℂ P] in
/-- **The walk identity** `(I - W) R₀ J u = (i/α) J H u` (eq. `qls:eq:separate-identity`), for
every `u`. -/
theorem one_sub_walk_resolvent (h : WalkGap.Hyp J K H α μ k₀) (u : P) :
    WalkGap.resolvent K (J u) - WalkGap.walk J h.cayley (WalkGap.resolvent K (J u)) =
      (Complex.I * (α : ℂ)⁻¹) • J (H u) := by
  rw [walk_resolvent h u]
  abel

omit [FiniteDimensional ℂ P] in
/-- **The enlarged solution**: `B ((-2iα) R₀ J u) = J H u`. -/
theorem enlarged_solution (h : WalkGap.Hyp J K H α μ k₀) (u : P) :
    enlarged h (solScale α • WalkGap.resolvent K (J u)) = J (H u) := by
  have hα : (α : ℂ) ≠ 0 := by exact_mod_cast h.alpha_pos.ne'
  rw [enlarged_apply, map_smul, ← smul_sub, one_sub_walk_resolvent h u, smul_smul, smul_smul]
  have hc : (2 : ℂ)⁻¹ * solScale α * (Complex.I * (α : ℂ)⁻¹) = 1 := by
    simp only [solScale]
    field_simp
    rw [Complex.I_sq]
    ring
  rw [hc, one_smul]

omit [FiniteDimensional ℂ P] in
/-- **The decoded solution**: `C ((-2iα) R₀ J u) = -iα J u`. -/
theorem decoder_solution (h : WalkGap.Hyp J K H α μ k₀) (u : P) :
    decoder h (solScale α • WalkGap.resolvent K (J u)) = (-Complex.I * (α : ℂ)) • J u := by
  rw [decoder_apply, map_smul, ← smul_sub, WalkGap.one_sub_cayley_resolvent h, smul_smul]
  congr 1
  simp only [solScale]
  ring

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
/-- **The enlarged solution norm**: `‖(-2iα) R₀ J u‖² = α² (‖u‖² + ‖K J u‖²)`. -/
theorem solution_norm_sq (h : WalkGap.Hyp J K H α μ k₀) (u : P) :
    ‖solScale α • WalkGap.resolvent K (J u)‖ ^ 2 = α ^ 2 * (‖u‖ ^ 2 + ‖K (J u)‖ ^ 2) := by
  have hnorm : ‖solScale α‖ = 2 * α := by
    simp only [solScale, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos h.alpha_pos]
    norm_num
  rw [norm_smul, mul_pow, h.lift_norm_sq u, hnorm]
  ring

omit [FiniteDimensional ℂ P] in
/-- **No fixed vector.** If `H` is injective, `W v = v` forces `v = 0` on the whole space: the
kernel correspondence gives `H (J† v) = 0` and `R₀ J (2 J† v) = v`. -/
theorem walk_fixed_eq_zero (h : WalkGap.Hyp J K H α μ k₀) (hH : ∀ w : P, H w = 0 → w = 0)
    (v : V) (hv : WalkGap.walk J h.cayley v = v) : v = 0 := by
  obtain ⟨h1, h2⟩ := h.kernel_of_fixed v hv
  rw [← h2, hH _ h1, smul_zero, map_zero, map_zero]

/-- **The inverse bound of the enlarged matrix.** With the phase gap of Lemma `qls:lem:walk`
(nonzero eigenvalues of `H` of modulus at least `Δ`) and an injective `H`, every `v` satisfies
`t*/√(1 + t*²) ‖v‖ ≤ ‖B v‖`. -/
theorem enlarged_lower (h : WalkGap.Hyp J K H α μ k₀) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : ∀ (x : P) (c : ℂ), x ≠ 0 → H x = c • x → c ≠ 0 → Δ ≤ ‖c‖)
    (hH : ∀ w : P, H w = 0 → w = 0) (v : V) :
    WalkGap.tStar α μ k₀ Δ / Real.sqrt (1 + WalkGap.tStar α μ k₀ Δ ^ 2) * ‖v‖ ≤
      ‖enlarged h v‖ := by
  set t := WalkGap.tStar α μ k₀ Δ with ht
  have htpos : 0 < t := WalkGap.tStar_pos α μ k₀ Δ h.alpha_pos h.mu_nonneg h.k0_nonneg hΔ
  have hW : UnitaryFilter.Unitary (WalkGap.walk J h.cayley) :=
    ⟨h.walk_unitary.1, h.walk_unitary.2⟩
  have hb : 0 ≤ t / Real.sqrt (1 + t ^ 2) := by positivity
  have hfix : UnitaryFilter.fixedSpace (WalkGap.walk J h.cayley) = ⊥ := by
    ext w
    rw [UnitaryFilter.mem_fixedSpace, Submodule.mem_bot]
    exact ⟨walk_fixed_eq_zero h hH w, fun hw => by rw [hw, map_zero]⟩
  have hy : v ∈ (UnitaryFilter.fixedSpace (WalkGap.walk J h.cayley))ᗮ := by
    rw [hfix, Submodule.bot_orthogonal_eq_top]
    exact Submodule.mem_top
  have key := hW.lower_bound (t / Real.sqrt (1 + t ^ 2)) hb (fun z w hw hWw hz => by
    have := h.chord_gap Δ hΔ hgap z w hw hWw hz
    rw [mul_div_assoc] at this
    exact this) hy
  have hBv : ‖WalkGap.walk J h.cayley v - v‖ = 2 * ‖enlarged h v‖ := by
    rw [enlarged_apply, norm_smul, norm_sub_rev, norm_inv]
    norm_num
    ring
  linarith

omit [FiniteDimensional ℂ P] in
/-- The decoder is a contraction. -/
theorem decoder_norm_le (h : WalkGap.Hyp J K H α μ k₀) (v : V) : ‖decoder h v‖ ≤ ‖v‖ := by
  rw [decoder_apply, norm_smul, norm_inv]
  have h1 := norm_sub_le v (h.cayley v)
  rw [HilbertCayley.cayley_norm_apply K h.selfAdjoint v] at h1
  norm_num
  linarith

end

end SparseLinearSystems.Separate
