import SparseLinearSystems.Foundations.FourBranchCompression
import SparseLinearSystems.Spectral.Diagonal

/-!
# The kernel walk and its phase gap (Lemma `qls:lem:walk`)

Let `J` be an isometry, `K` self-adjoint, `D = (K + i)(K - i)⁻¹` and
`W = (I - 2JJ†) D`.  Assume `J† K J = H / α`, `J† K² J ≤ μ` and `‖K‖ ≤ k₀`.

* `fixed_lift`, `kernel_of_fixed`, `lift_adjoint`, `lift_norm_sq`: the map
  `u ↦ R₀ J u`, `R₀ = (I + iK)/2`, is a bijection from `ker H` onto the fixed
  space of `W`, with `J† R₀ J u = u/2` and `‖R₀ J u‖² = (‖u‖² + ‖KJu‖²)/4`
  (equation `qls:eq:lift`).
* `tangent_gap`: if every nonzero eigenvalue of `H` has modulus at least `Δ`,
  then every eigenvalue `z ≠ ±1` of `W` satisfies `|tan(θ/2)| ≥ t*`,
  `t* = (Δ/α)/(1 + μ + k₀Δ/α)` (equation `qls:eq:tangap`).  Here
  `tan(θ/2) = tau z = 2 Im z / |z + 1|²`.
* `chord_gap`: every eigenvalue `z ≠ 1` satisfies
  `|z - 1| ≥ 2 t*/√(1 + t*²)`, i.e. `|sin(θ/2)| ≥ t*/√(1 + t*²)`.

The proof follows the manuscript: an eigenvector of `W` gives a kernel vector
of `B(τ) = J†(K + τ)(I - τK)⁻¹J = B(0) + Δ`, where
`Δ = τ J†(I + K²)(I - τK)⁻¹ J`.  The bounds
`J†(I+K²)(I-τK)⁻¹J ≥ (1 + k₀|τ|)⁻¹` and `≤ (1+μ)/(1 - k₀|τ|)` are proved in the
eigenbasis of `K`.  Instead of ordered eigenvalue perturbation bounds, the
inertia lemma `Diagonal.inertia_injective` excludes a kernel of `B(τ)`.
-/

namespace SparseLinearSystems.WalkGap

noncomputable section
open ContinuousLinearMap Diagonal
open scoped InnerProduct ComplexConjugate

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P] [CompleteSpace P]

/-! ### The reflection and the walk -/

/-- Reflection about the orthogonal complement of the range of `J`. -/
def reflection (J : P →L[ℂ] V) : V →L[ℂ] V := 1 - (2 : ℂ) • (J ∘L (J†))

/-- The kernel walk `W = (I - 2JJ†) D`. -/
def walk (J : P →L[ℂ] V) (D : V →L[ℂ] V) : V →L[ℂ] V := reflection J * D

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem reflection_apply (J : P →L[ℂ] V) (v : V) :
    reflection J v = v - (2 : ℂ) • J ((J†) v) := rfl

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem isometry_apply {J : P →L[ℂ] V} (hJ : (J†) ∘L J = 1) (u : P) : (J†) (J u) = u := by
  have h := congrArg (fun A : P →L[ℂ] P => A u) hJ
  simpa only [comp_apply, one_apply_eq_self] using h

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem isometry_norm {J : P →L[ℂ] V} (hJ : (J†) ∘L J = 1) (u : P) : ‖J u‖ = ‖u‖ :=
  (J.norm_map_iff_adjoint_comp_self.mpr hJ) u

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem reflection_reflection (J : P →L[ℂ] V) (hJ : (J†) ∘L J = 1) (v : V) :
    reflection J (reflection J v) = v := by
  rw [reflection_apply, reflection_apply, map_sub, map_smul, isometry_apply hJ, map_sub,
    map_smul]
  module

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem reflection_mul_self (J : P →L[ℂ] V) (hJ : (J†) ∘L J = 1) :
    reflection J * reflection J = 1 := by
  ext v
  rw [mul_apply_eq_comp, reflection_reflection J hJ, one_apply_eq_self]

omit [FiniteDimensional ℂ V] in
theorem adjoint_one' : ((1 : V →L[ℂ] V)†) = 1 := by
  rw [← star_eq_adjoint, star_one]

omit [FiniteDimensional ℂ P] [FiniteDimensional ℂ V] in
theorem reflection_adjoint (J : P →L[ℂ] V) : ((reflection J)†) = reflection J := by
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  rw [reflection, map_sub, map_smulₛₗ, adjoint_comp, adjoint_adjoint, adjoint_one', h2]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem walk_unitary (J : P →L[ℂ] V) (hJ : (J†) ∘L J = 1) (D : V →L[ℂ] V)
    (hD : star D * D = 1 ∧ D * star D = 1) :
    star (walk J D) * walk J D = 1 ∧ walk J D * star (walk J D) = 1 := by
  have hR : star (reflection J) = reflection J := by
    rw [star_eq_adjoint, reflection_adjoint]
  have hRR := reflection_mul_self J hJ
  constructor
  · rw [walk, star_mul, hR, mul_assoc, ← mul_assoc (reflection J), hRR, one_mul, hD.1]
  · rw [walk, star_mul, hR, mul_assoc, ← mul_assoc D, hD.2, one_mul, hRR]

omit [FiniteDimensional ℂ V] in
/-- Eigenvalues of an isometry lie on the unit circle. -/
theorem norm_eigenvalue_eq_one (W : V →L[ℂ] V) (hW : star W * W = 1) (z : ℂ) (v : V)
    (hv : v ≠ 0) (hWv : W v = z • v) : ‖z‖ = 1 := by
  have hW' : (W†) ∘L W = 1 := by rw [← mul_def, ← star_eq_adjoint]; exact hW
  have hn : ‖W v‖ = ‖v‖ := (W.norm_map_iff_adjoint_comp_self.mpr hW') v
  rw [hWv, norm_smul] at hn
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  calc ‖z‖ = ‖z‖ * ‖v‖ / ‖v‖ := by field_simp
    _ = 1 := by rw [hn, div_self hv']

/-! ### Unit-circle parametrisation -/

/-- `tan(θ/2)` for `z = e^{iθ}`, written without trigonometric functions. -/
def tau (z : ℂ) : ℝ := 2 * z.im / ‖z + 1‖ ^ 2

theorem normSq_unit {z : ℂ} (hz : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.sq_norm z
  rw [hz, Complex.normSq_apply] at h
  nlinarith

theorem norm_add_one_sq (z : ℂ) : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
  ring

theorem norm_sub_one_sq (z : ℂ) : ‖z - 1‖ ^ 2 = (z.re - 1) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
  ring

theorem tau_spec (z : ℂ) (hz : ‖z‖ = 1) (hzm1 : z ≠ -1) :
    z - 1 = (Complex.I * (tau z : ℂ)) * (z + 1) := by
  have hn := normSq_unit hz
  have hden : ‖z + 1‖ ^ 2 = 2 * (1 + z.re) := by rw [norm_add_one_sq]; nlinarith
  have hre : 1 + z.re ≠ 0 := by
    intro h0
    have him : z.im = 0 := by nlinarith
    apply hzm1
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.one_re]; linarith
    · simp only [Complex.neg_im, Complex.one_im, neg_zero]; exact him
  have htau : tau z = z.im / (1 + z.re) := by
    rw [tau, hden]; field_simp
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.one_im, Complex.mul_im, zero_mul, one_mul, mul_zero,
      sub_zero, zero_sub, add_zero, htau]
    field_simp
    nlinarith
  · simp only [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.one_re, zero_mul, one_mul, mul_zero, sub_zero, add_zero,
      zero_add, htau]
    field_simp
    ring

theorem tau_ne_zero (z : ℂ) (hz : ‖z‖ = 1) (hzm1 : z ≠ -1) (hz1 : z ≠ 1) : tau z ≠ 0 := by
  intro h0
  have h := tau_spec z hz hzm1
  rw [h0, Complex.ofReal_zero, mul_zero, zero_mul] at h
  exact hz1 (sub_eq_zero.mp h)

/-- `|z - 1|² = 4 τ²/(1 + τ²)`, in multiplied-out form. -/
theorem chord_sq (z : ℂ) (hz : ‖z‖ = 1) (hzm1 : z ≠ -1) :
    ‖z - 1‖ ^ 2 * (1 + tau z ^ 2) = 4 * tau z ^ 2 := by
  have h := tau_spec z hz hzm1
  have h1 : ‖z - 1‖ = |tau z| * ‖z + 1‖ := by
    rw [h, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hpar : ‖z - 1‖ ^ 2 + ‖z + 1‖ ^ 2 = 4 := by
    rw [norm_sub_one_sq, norm_add_one_sq]
    nlinarith [normSq_unit hz]
  have h2 : ‖z - 1‖ ^ 2 = tau z ^ 2 * ‖z + 1‖ ^ 2 := by rw [h1, mul_pow, sq_abs]
  nlinarith

/-! ### Hypotheses of the walk lemma -/

/-- The hypotheses of Lemma `qls:lem:walk`.  The second-moment bound is the
pointwise form of `J† K² J ≤ μ I`. -/
structure Hyp (J : P →L[ℂ] V) (K : V →L[ℂ] V) (H : P →L[ℂ] P) (α μ k₀ : ℝ) : Prop where
  isometry : (J†) ∘L J = 1
  selfAdjoint : (K†) = K
  alpha_pos : 0 < α
  compression : (J†) ∘L K ∘L J = ((α : ℂ)⁻¹) • H
  moment : ∀ u : P, ‖K (J u)‖ ^ 2 ≤ μ * ‖u‖ ^ 2
  mu_nonneg : 0 ≤ μ
  bound : ∀ v : V, ‖K v‖ ≤ k₀ * ‖v‖
  k0_nonneg : 0 ≤ k₀

/-- The threshold `t*` of equation `qls:eq:tangap`. -/
def tStar (α μ k₀ Δ : ℝ) : ℝ := (Δ / α) / (1 + μ + k₀ * (Δ / α))

/-- The resolvent `R₀ = (I + iK)/2` of equation `qls:eq:R0`. -/
abbrev resolvent (K : V →L[ℂ] V) : V →L[ℂ] V := Cayley.resolventAtOne K

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem resolvent_apply (K : V →L[ℂ] V) (x : V) :
    resolvent K x = (2 : ℂ)⁻¹ • (x + Complex.I • K x) := by
  simp only [resolvent, Cayley.resolventAtOne, smul_apply, add_apply, one_apply_eq_self]

variable {J : P →L[ℂ] V} {K : V →L[ℂ] V} {H : P →L[ℂ] P} {α μ k₀ : ℝ}

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem Hyp.compression_apply (h : Hyp J K H α μ k₀) (u : P) :
    (J†) (K (J u)) = ((α : ℂ)⁻¹) • H u := by
  have := congrArg (fun A : P →L[ℂ] P => A u) h.compression
  simpa only [comp_apply, smul_apply] using this

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem Hyp.hamiltonian_eq (h : Hyp J K H α μ k₀) (u : P) :
    H u = (α : ℂ) • (J†) (K (J u)) := by
  rw [h.compression_apply, smul_smul, mul_inv_cancel₀ (by exact_mod_cast h.alpha_pos.ne'),
    one_smul]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem Hyp.hamiltonian_selfAdjoint (h : Hyp J K H α μ k₀) : (H†) = H := by
  have hH : H = (α : ℂ) • ((J†) ∘L K ∘L J) := by
    ext u
    rw [h.hamiltonian_eq u]; rfl
  rw [hH, map_smulₛₗ, adjoint_comp, adjoint_comp, adjoint_adjoint, h.selfAdjoint,
    Complex.conj_ofReal, comp_assoc]

/-- The Cayley transform `D = (K + i)(K - i)⁻¹`. -/
abbrev Hyp.cayley (h : Hyp J K H α μ k₀) : V →L[ℂ] V :=
  HilbertCayley.cayley K h.selfAdjoint

omit [FiniteDimensional ℂ P] in
theorem Hyp.walk_unitary (h : Hyp J K H α μ k₀) :
    star (walk J h.cayley) * walk J h.cayley = 1 ∧
      walk J h.cayley * star (walk J h.cayley) = 1 :=
  WalkGap.walk_unitary J h.isometry _ (HilbertCayley.cayley_unitary K h.selfAdjoint)

/-! ### The kernel bijection -/

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
theorem Hyp.lift_adjoint (h : Hyp J K H α μ k₀) (u : P) (hu : H u = 0) :
    (J†) (resolvent K (J u)) = (2 : ℂ)⁻¹ • u := by
  rw [resolvent_apply, map_smul, map_add, map_smul, isometry_apply h.isometry,
    h.compression_apply, hu, smul_zero, smul_zero, add_zero]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
/-- `W v = v` iff `(I - D) v = 2 J J† v`. -/
theorem walk_fixed_iff (hJ : (J†) ∘L J = 1) (D : V →L[ℂ] V) (v : V) :
    walk J D v = v ↔ v - D v = (2 : ℂ) • J ((J†) v) := by
  constructor
  · intro hv
    have h := congrArg (reflection J) hv
    rw [walk, mul_apply_eq_comp, reflection_reflection J hJ, reflection_apply] at h
    rw [h]; abel
  · intro hv
    have hD : D v = reflection J v := by
      rw [reflection_apply, ← hv]; abel
    rw [walk, mul_apply_eq_comp, hD, reflection_reflection J hJ]

omit [FiniteDimensional ℂ P] in
theorem one_sub_cayley_resolvent (h : Hyp J K H α μ k₀) (x : V) :
    resolvent K x - h.cayley (resolvent K x) = x := by
  have := congrArg (fun A : V →L[ℂ] V => A x)
    (HilbertCayley.one_sub_cayley_mul_resolvent K h.selfAdjoint)
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using this

omit [FiniteDimensional ℂ P] in
theorem resolvent_one_sub_cayley (h : Hyp J K H α μ k₀) (x : V) :
    resolvent K (x - h.cayley x) = x := by
  have := congrArg (fun A : V →L[ℂ] V => A x)
    (HilbertCayley.resolvent_mul_one_sub_cayley K h.selfAdjoint)
  simpa only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] using this

omit [FiniteDimensional ℂ P] in
/-- Every kernel vector lifts to a fixed vector of the walk. -/
theorem Hyp.fixed_lift (h : Hyp J K H α μ k₀) (u : P) (hu : H u = 0) :
    walk J h.cayley (resolvent K (J u)) = resolvent K (J u) := by
  rw [walk_fixed_iff h.isometry, one_sub_cayley_resolvent h, h.lift_adjoint u hu, map_smul,
    smul_smul]
  norm_num

omit [FiniteDimensional ℂ P] in
/-- Every fixed vector comes from a kernel vector. -/
theorem Hyp.kernel_of_fixed (h : Hyp J K H α μ k₀) (v : V)
    (hv : walk J h.cayley v = v) :
    H ((J†) v) = 0 ∧ resolvent K (J ((2 : ℂ) • (J†) v)) = v := by
  have hfix := (walk_fixed_iff h.isometry _ v).mp hv
  have hrec : resolvent K (J ((2 : ℂ) • (J†) v)) = v := by
    rw [map_smul, ← hfix, resolvent_one_sub_cayley h]
  refine ⟨?_, hrec⟩
  set w := (J†) v with hw
  have hc : (J†) (resolvent K (J ((2 : ℂ) • w))) = w := by rw [hrec]
  rw [resolvent_apply, map_smul (J†) (2 : ℂ)⁻¹, map_add, isometry_apply h.isometry,
    map_smul (J†) Complex.I, h.compression_apply, map_smul H (2 : ℂ) w] at hc
  have hα : (α : ℂ) ≠ 0 := by exact_mod_cast h.alpha_pos.ne'
  have key : (Complex.I * (α : ℂ)⁻¹) • H w = 0 := by
    have e : (2 : ℂ)⁻¹ • ((2 : ℂ) • w + Complex.I • ((α : ℂ)⁻¹ • ((2 : ℂ) • H w))) =
        w + (Complex.I * (α : ℂ)⁻¹) • H w := by module
    rw [e] at hc
    have := congrArg (fun y => y - w) hc
    simpa only [add_sub_cancel_left, sub_self] using this
  exact (smul_eq_zero.mp key).resolve_left (mul_ne_zero Complex.I_ne_zero (inv_ne_zero hα))

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
/-- The lift norm, equation `qls:eq:lift`. -/
theorem Hyp.lift_norm_sq (h : Hyp J K H α μ k₀) (u : P) :
    ‖resolvent K (J u)‖ ^ 2 = (‖u‖ ^ 2 + ‖K (J u)‖ ^ 2) / 4 := by
  rw [resolvent, HilbertCayley.resolvent_norm_sq K h.selfAdjoint, isometry_norm h.isometry]

/-! ### The secular equation of an eigenvector -/

omit [FiniteDimensional ℂ P] in
/-- An eigenvector of the walk, in Cayley coordinates `y = (K - i)⁻¹ v`. -/
theorem Hyp.secular (h : Hyp J K H α μ k₀) (z : ℂ) (τ : ℝ) (hzm1 : z ≠ -1)
    (hτ : z - 1 = (Complex.I * (τ : ℂ)) * (z + 1)) (v : V)
    (hWv : walk J h.cayley v = z • v) :
    HilbertCayley.denominatorInverse K h.selfAdjoint v -
        (τ : ℂ) • K (HilbertCayley.denominatorInverse K h.selfAdjoint v) =
        (Complex.I - τ) • J ((J†) v) ∧
      (J†) (K (HilbertCayley.denominatorInverse K h.selfAdjoint v) +
        (τ : ℂ) • HilbertCayley.denominatorInverse K h.selfAdjoint v) = 0 := by
  set y := HilbertCayley.denominatorInverse K h.selfAdjoint v with hy
  have hv_y : v = K y - Complex.I • y := by
    have := congrArg (fun A : V →L[ℂ] V => A v)
      (HilbertCayley.denominator_mul_inverse K h.selfAdjoint)
    simp only [mul_apply_eq_comp, one_apply_eq_self, HilbertCayley.denominator_apply] at this
    rw [hy]; exact this.symm
  have hDv : h.cayley v = K y + Complex.I • y := by
    simp only [Hyp.cayley, HilbertCayley.cayley, Cayley.cayleyAction, mul_apply_eq_comp,
      add_apply, smul_apply, one_apply_eq_self, hy]
  have hD : h.cayley v = z • v - (2 * z) • J ((J†) v) := by
    have hr := congrArg (reflection J) hWv
    rw [walk, mul_apply_eq_comp, reflection_reflection J h.isometry] at hr
    rw [hr, reflection_apply, map_smul, map_smul, smul_smul, mul_comm]
  have hc : Complex.I * (1 + z) ≠ 0 := by
    refine mul_ne_zero Complex.I_ne_zero ?_
    intro h0; apply hzm1; linear_combination h0
  have hcτ : Complex.I * (1 + z) * (τ : ℂ) = z - 1 := by rw [hτ]; ring
  have hcIτ : Complex.I * (1 + z) * (Complex.I - τ) = -2 * z := by
    linear_combination hτ + (1 + z) * Complex.I_mul_I
  have E1 : K y + Complex.I • y = z • (K y - Complex.I • y) - (2 * z) • J ((J†) v) := by
    rw [← hDv, ← hv_y, hD]
  have goal1 : y - (τ : ℂ) • K y = (Complex.I - τ) • J ((J†) v) := by
    apply smul_right_injective V hc
    simp only
    rw [smul_sub, smul_smul, hcτ, smul_smul, hcIτ]
    have e2 : (-2 * z) • J ((J†) v) = (K y + Complex.I • y) - z • (K y - Complex.I • y) := by
      rw [E1]; module
    rw [e2]; module
  refine ⟨goal1, ?_⟩
  have hrel : (J†) y - (τ : ℂ) • (J†) (K y) =
      (Complex.I - τ) • ((J†) (K y) - Complex.I • (J†) y) := by
    have h1 := congrArg (J†) goal1
    rw [map_sub, map_smul, map_smul, isometry_apply h.isometry] at h1
    rw [h1]
    conv_lhs => rw [hv_y]
    rw [map_sub, map_smul]
  have e : (Complex.I - (τ : ℂ)) • ((J†) (K y) - Complex.I • (J†) y) =
      (Complex.I - τ) • (J†) (K y) + (1 + τ * Complex.I) • (J†) y := by
    rw [smul_sub, smul_smul]
    have hs : (Complex.I - (τ : ℂ)) * Complex.I = -(1 + τ * Complex.I) := by
      linear_combination Complex.I_mul_I
    rw [hs, neg_smul, sub_neg_eq_add]
  rw [e] at hrel
  have hI : (-Complex.I) • ((J†) (K y) + (τ : ℂ) • (J†) y) = 0 := by
    have e3 : (-Complex.I) • ((J†) (K y) + (τ : ℂ) • (J†) y) =
        ((J†) y - (τ : ℂ) • (J†) (K y)) -
          ((Complex.I - τ) • (J†) (K y) + (1 + τ * Complex.I) • (J†) y) := by module
    rw [e3, hrel, sub_self]
  rw [map_add, map_smul]
  exact (smul_eq_zero.mp hI).resolve_left (neg_ne_zero.mpr Complex.I_ne_zero)

/-! ### The increment operator -/

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem one_sub_smul_lower (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖)
    (τ : ℝ) (y : V) : (1 - |τ| * k₀) * ‖y‖ ≤ ‖y - (τ : ℂ) • K y‖ := by
  have h1 : ‖(τ : ℂ) • K y‖ ≤ |τ| * k₀ * ‖y‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hk y) (abs_nonneg τ)
  have h2 := norm_sub_norm_le y ((τ : ℂ) • K y)
  nlinarith

/-- The operator `I - τK`. -/
abbrev oneSub (K : V →L[ℂ] V) (τ : ℝ) : V →L[ℂ] V := 1 - (τ : ℂ) • K

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem oneSub_apply (K : V →L[ℂ] V) (τ : ℝ) (y : V) :
    oneSub K τ y = y - (τ : ℂ) • K y := rfl

omit [FiniteDimensional ℂ V] [CompleteSpace V] in
theorem oneSub_injective (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖)
    (τ : ℝ) (hτk : |τ| * k₀ < 1) : Function.Injective (oneSub K τ) := by
  intro a b hab
  have h0 : oneSub K τ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hl := one_sub_smul_lower K k₀ hk τ (a - b)
  rw [← oneSub_apply, h0, norm_zero] at hl
  have hpos : 0 < 1 - |τ| * k₀ := by linarith
  have hn : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hn)

section Increment

/-- The resolvent `G = (I - τK)⁻¹`. -/
def gInv (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ)
    (hτk : |τ| * k₀ < 1) : V →L[ℂ] V :=
  inverseOfInjective (oneSub K τ) (oneSub_injective K k₀ hk τ hτk)

/-- The operator `(I + K²)(I - τK)⁻¹`. -/
def incrementCore (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ)
    (hτk : |τ| * k₀ < 1) : V →L[ℂ] V :=
  (1 + K * K) * gInv K k₀ hk τ hτk

omit [CompleteSpace V] in
theorem gInv_left (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ)
    (hτk : |τ| * k₀ < 1) (y : V) : gInv K k₀ hk τ hτk (y - (τ : ℂ) • K y) = y :=
  inverseOfInjective_apply _ _ y

omit [CompleteSpace V] in
theorem gInv_right (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ)
    (hτk : |τ| * k₀ < 1) (y : V) :
    gInv K k₀ hk τ hτk y - (τ : ℂ) • K (gInv K k₀ hk τ hτk y) = y :=
  apply_inverseOfInjective (oneSub K τ) _ y

theorem abs_tau_eigen_le (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (i : Fin (Module.finrank ℂ V)) :
    |τ * eigenValues K hK i| ≤ |τ| * k₀ := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_eigenValues_le K hK k₀ hk i) (abs_nonneg τ)

/-- `|τ κ| < 1` for every eigenvalue `κ` of `K`. -/
theorem one_sub_eigen_pos (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1)
    (i : Fin (Module.finrank ℂ V)) : 0 < 1 - τ * eigenValues K hK i := by
  have h1 := abs_tau_eigen_le K hK k₀ hk τ i
  have := le_abs_self (τ * eigenValues K hK i)
  linarith

theorem one_sub_eigen_le (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (i : Fin (Module.finrank ℂ V)) :
    1 - τ * eigenValues K hK i ≤ 1 + |τ| * k₀ := by
  have h1 := abs_tau_eigen_le K hK k₀ hk τ i
  have := neg_abs_le (τ * eigenValues K hK i)
  linarith

theorem one_sub_eigen_ge (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (i : Fin (Module.finrank ℂ V)) :
    1 - |τ| * k₀ ≤ 1 - τ * eigenValues K hK i := by
  have h1 := abs_tau_eigen_le K hK k₀ hk τ i
  have := le_abs_self (τ * eigenValues K hK i)
  linarith

theorem gInv_eigen (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1)
    (i : Fin (Module.finrank ℂ V)) :
    gInv K k₀ hk τ hτk (eigenBasis K hK i) =
      (((1 - τ * eigenValues K hK i)⁻¹ : ℝ) : ℂ) • eigenBasis K hK i := by
  have hpos := one_sub_eigen_pos K hK k₀ hk τ hτk i
  have h1 : eigenBasis K hK i - (τ : ℂ) • K (eigenBasis K hK i) =
      ((1 - τ * eigenValues K hK i : ℝ) : ℂ) • eigenBasis K hK i := by
    rw [apply_eigenBasis, smul_smul]; push_cast; module
  have h2 := gInv_left K k₀ hk τ hτk (eigenBasis K hK i)
  rw [h1, map_smul] at h2
  have hc : ((1 - τ * eigenValues K hK i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  calc gInv K k₀ hk τ hτk (eigenBasis K hK i)
      = ((1 - τ * eigenValues K hK i : ℝ) : ℂ)⁻¹ •
          (((1 - τ * eigenValues K hK i : ℝ) : ℂ) • gInv K k₀ hk τ hτk (eigenBasis K hK i)) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = _ := by rw [h2, Complex.ofReal_inv]

omit [CompleteSpace V] in
/-- `K u + τ (I + K²)(I - τK)⁻¹ u = (K + τ)(I - τK)⁻¹ u`. -/
theorem core_identity (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ)
    (hτk : |τ| * k₀ < 1) (u : V) :
    K u + (τ : ℂ) • incrementCore K k₀ hk τ hτk u =
      K (gInv K k₀ hk τ hτk u) + (τ : ℂ) • gInv K k₀ hk τ hτk u := by
  have hu := gInv_right K k₀ hk τ hτk u
  have e : incrementCore K k₀ hk τ hτk u =
      gInv K k₀ hk τ hτk u + K (K (gInv K k₀ hk τ hτk u)) := by
    simp only [incrementCore, mul_apply_eq_comp, add_apply, one_apply_eq_self]
  have hKu : K u = K (gInv K k₀ hk τ hτk u) - (τ : ℂ) • K (K (gInv K k₀ hk τ hτk u)) := by
    conv_lhs => rw [← hu]
    rw [map_sub, map_smul]
  rw [e, hKu]
  module

/-- Diagonal coefficient of `(I + K²)(I - τK)⁻¹`. -/
def coreCoeff (K : V →L[ℂ] V) (hK : (K†) = K) (τ : ℝ) (i : Fin (Module.finrank ℂ V)) : ℝ :=
  (1 + eigenValues K hK i ^ 2) / (1 - τ * eigenValues K hK i)

theorem incrementCore_eigen (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1)
    (i : Fin (Module.finrank ℂ V)) :
    incrementCore K k₀ hk τ hτk (eigenBasis K hK i) =
      (coreCoeff K hK τ i : ℂ) • eigenBasis K hK i := by
  have hKe := apply_eigenBasis K hK i
  rw [incrementCore, mul_apply_eq_comp, gInv_eigen K hK k₀ hk τ hτk i, map_smul,
    add_apply, one_apply_eq_self, mul_apply_eq_comp, hKe, map_smul, hKe, smul_smul,
    coreCoeff]
  push_cast
  module

theorem coreCoeff_pos (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1)
    (i : Fin (Module.finrank ℂ V)) : 0 < coreCoeff K hK τ i :=
  div_pos (by positivity) (one_sub_eigen_pos K hK k₀ hk τ hτk i)

theorem coreCoeff_lower (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1)
    (i : Fin (Module.finrank ℂ V)) :
    1 / (1 + |τ| * k₀) ≤ coreCoeff K hK τ i := by
  have hpos := one_sub_eigen_pos K hK k₀ hk τ hτk i
  have hle := one_sub_eigen_le K hK k₀ hk τ i
  rw [coreCoeff, div_le_div_iff₀ (by linarith) hpos]
  nlinarith [sq_nonneg (eigenValues K hK i)]

theorem coreCoeff_upper (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1)
    (i : Fin (Module.finrank ℂ V)) :
    coreCoeff K hK τ i ≤ (1 + eigenValues K hK i ^ 2) / (1 - |τ| * k₀) := by
  have hge := one_sub_eigen_ge K hK k₀ hk τ i
  have hm : 0 < 1 - |τ| * k₀ := by linarith
  rw [coreCoeff]
  exact div_le_div_of_nonneg_left (by positivity) hm hge

/-- The core is self-adjoint. -/
theorem incrementCore_adjoint (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1) :
    ((incrementCore K k₀ hk τ hτk)†) = incrementCore K k₀ hk τ hτk :=
  adjoint_eq_of_diag_real (eigenBasis K hK) _ (coreCoeff K hK τ)
    (incrementCore_eigen K hK k₀ hk τ hτk)

/-- `‖K w‖² = Σ κᵢ² |wᵢ|²`. -/
theorem norm_sq_K_eq (K : V →L[ℂ] V) (hK : (K†) = K) (w : V) :
    ‖K w‖ ^ 2 = ∑ i, eigenValues K hK i ^ 2 * ‖inner ℂ (eigenBasis K hK i) w‖ ^ 2 := by
  have hdiag : ∀ i, (K * K) (eigenBasis K hK i) =
      ((eigenValues K hK i ^ 2 : ℝ) : ℂ) • eigenBasis K hK i := by
    intro i
    rw [mul_apply_eq_comp, apply_eigenBasis, map_smul, apply_eigenBasis, smul_smul]
    push_cast; ring_nf
  have h := re_inner_self_apply_diag (eigenBasis K hK) (K * K)
    (fun i => eigenValues K hK i ^ 2) hdiag w
  rw [← h, mul_apply_eq_comp]
  have : inner ℂ w (K (K w)) = ((‖K w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← adjoint_inner_left K (K w) w, hK, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  rw [this, Complex.ofReal_re]

/-- Quadratic-form bounds for `(I + K²)(I - τK)⁻¹` (equation
`qls:eq:incrementbounds`). -/
theorem incrementCore_bounds (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1) (w : V) :
    ‖w‖ ^ 2 / (1 + |τ| * k₀) ≤ (inner ℂ w (incrementCore K k₀ hk τ hτk w)).re ∧
      (inner ℂ w (incrementCore K k₀ hk τ hτk w)).re ≤
        (‖w‖ ^ 2 + ‖K w‖ ^ 2) / (1 - |τ| * k₀) := by
  have hq := re_inner_self_apply_diag (eigenBasis K hK) _ (coreCoeff K hK τ)
    (incrementCore_eigen K hK k₀ hk τ hτk) w
  rw [hq]
  constructor
  · rw [norm_sq_eq_sum (eigenBasis K hK) w, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    have hl := coreCoeff_lower K hK k₀ hk τ hτk i
    calc ‖inner ℂ (eigenBasis K hK i) w‖ ^ 2 / (1 + |τ| * k₀) =
        1 / (1 + |τ| * k₀) * ‖inner ℂ (eigenBasis K hK i) w‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hl (sq_nonneg _)
  · rw [norm_sq_eq_sum (eigenBasis K hK) w, norm_sq_K_eq K hK w, ← Finset.sum_add_distrib,
      Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    have hu := coreCoeff_upper K hK k₀ hk τ hτk i
    calc coreCoeff K hK τ i * ‖inner ℂ (eigenBasis K hK i) w‖ ^ 2 ≤
        (1 + eigenValues K hK i ^ 2) / (1 - |τ| * k₀) *
          ‖inner ℂ (eigenBasis K hK i) w‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hu (sq_nonneg _)
      _ = _ := by ring

end Increment

/-! ### The phase gap -/

/-- The increment `Δ = τ J†(I + K²)(I - τK)⁻¹ J`. -/
def increment (J : P →L[ℂ] V) (K : V →L[ℂ] V) (k₀ : ℝ) (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖)
    (τ : ℝ) (hτk : |τ| * k₀ < 1) : P →L[ℂ] P :=
  (τ : ℂ) • ((J†) ∘L incrementCore K k₀ hk τ hτk ∘L J)

omit [FiniteDimensional ℂ P] in
theorem increment_adjoint (J : P →L[ℂ] V) (K : V →L[ℂ] V) (hK : (K†) = K) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1) :
    ((increment J K k₀ hk τ hτk)†) = increment J K k₀ hk τ hτk := by
  rw [increment, map_smulₛₗ, adjoint_comp, adjoint_comp, adjoint_adjoint,
    incrementCore_adjoint K hK k₀ hk τ hτk, Complex.conj_ofReal, comp_assoc]

omit [FiniteDimensional ℂ P] in
theorem increment_re (J : P →L[ℂ] V) (K : V →L[ℂ] V) (k₀ : ℝ)
    (hk : ∀ v, ‖K v‖ ≤ k₀ * ‖v‖) (τ : ℝ) (hτk : |τ| * k₀ < 1) (x : P) :
    (inner ℂ x (increment J K k₀ hk τ hτk x)).re =
      τ * (inner ℂ (J x) (incrementCore K k₀ hk τ hτk (J x))).re := by
  rw [increment, smul_apply, inner_smul_right, comp_apply, comp_apply, adjoint_inner_right,
    Complex.re_ofReal_mul]

/-- **Lemma `qls:lem:walk`, tangent form.**  Every eigenvalue `z ≠ ±1` of the
walk satisfies `t* ≤ |tan(θ/2)|`. -/
theorem Hyp.tangent_gap (h : Hyp J K H α μ k₀) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : ∀ (x : P) (c : ℂ), x ≠ 0 → H x = c • x → c ≠ 0 → Δ ≤ ‖c‖)
    (z : ℂ) (v : V) (hv : v ≠ 0) (hWv : walk J h.cayley v = z • v)
    (hz1 : z ≠ 1) (hzm1 : z ≠ -1) :
    tStar α μ k₀ Δ ≤ |tau z| := by
  by_contra hlt
  push Not at hlt
  have hz := norm_eigenvalue_eq_one _ h.walk_unitary.1 z v hv hWv
  set τ := tau z with hτdef
  have hτ := tau_spec z hz hzm1
  have hτ0 : τ ≠ 0 := tau_ne_zero z hz hzm1 hz1
  set d := Δ / α with hd
  have hdpos : 0 < d := div_pos hΔ h.alpha_pos
  have hden : 0 < 1 + μ + k₀ * d := by nlinarith [h.mu_nonneg, h.k0_nonneg]
  have hlt' : |τ| < d / (1 + μ + k₀ * d) := by
    simpa only [tStar, hd] using hlt
  have hτt : |τ| * (1 + μ + k₀ * d) < d := (lt_div_iff₀ hden).mp hlt'
  have hτk : |τ| * k₀ < 1 := by
    have h1 : |τ| * k₀ * d < d := by
      nlinarith [abs_nonneg τ, h.mu_nonneg, mul_nonneg (abs_nonneg τ) h.mu_nonneg]
    by_contra hc
    push Not at hc
    nlinarith
  -- the secular vector
  obtain ⟨hs1, hs2⟩ := h.secular z τ hzm1 hτ v hWv
  set y := HilbertCayley.denominatorInverse K h.selfAdjoint v with hy
  set w := (J†) v with hw
  have hIτ : (Complex.I - (τ : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
  -- `w ≠ 0`
  have hw0 : w ≠ 0 := by
    intro hw0
    rw [hw0, map_zero, smul_zero] at hs1
    have hy0 : y = 0 := by
      have := oneSub_injective K k₀ h.bound τ hτk
      apply this
      rw [oneSub_apply, hs1, map_zero]
    apply hv
    have hvy : v = K y - Complex.I • y := by
      have := congrArg (fun A : V →L[ℂ] V => A v)
        (HilbertCayley.denominator_mul_inverse K h.selfAdjoint)
      simp only [mul_apply_eq_comp, one_apply_eq_self, HilbertCayley.denominator_apply] at this
      rw [hy]; exact this.symm
    rw [hvy, hy0, map_zero, smul_zero, sub_zero]
  -- `(B₀ + Δ) w = 0`
  set G := gInv K k₀ h.bound τ hτk with hG
  have hGJw : G (J w) = (Complex.I - (τ : ℂ))⁻¹ • y := by
    have e := congrArg G hs1
    rw [gInv_left K k₀ h.bound τ hτk y, map_smul] at e
    rw [e, smul_smul, inv_mul_cancel₀ hIτ, one_smul]
  have hJw : J w = (Complex.I - (τ : ℂ))⁻¹ • (y - (τ : ℂ) • K y) := by
    rw [hs1, smul_smul, inv_mul_cancel₀ hIτ, one_smul]
  set B₀ : P →L[ℂ] P := (J†) ∘L K ∘L J with hB₀
  set Δop := increment J K k₀ h.bound τ hτk with hΔop
  have hkernel : (B₀ + Δop) w = 0 := by
    have e1 : (B₀ + Δop) w =
        (J†) (K (J w) + (τ : ℂ) • incrementCore K k₀ h.bound τ hτk (J w)) := by
      rw [map_add, map_smul]; rfl
    rw [e1, core_identity K k₀ h.bound τ hτk (J w), ← hG, hGJw, map_smul,
      smul_comm (τ : ℂ) (Complex.I - (τ : ℂ))⁻¹ y, ← smul_add, map_smul, hs2, smul_zero]
  -- spectral data of `B₀`
  have hB₀sa : (B₀†) = B₀ := by
    rw [hB₀, adjoint_comp, adjoint_comp, adjoint_adjoint, h.selfAdjoint, comp_assoc]
  have hB₀gap : ∀ (x : P) (c : ℂ), x ≠ 0 → B₀ x = c • x → c ≠ 0 → d ≤ ‖c‖ := by
    intro x c hx hBx hc
    have hHx : H x = ((α : ℂ) * c) • x := by
      rw [h.hamiltonian_eq x, ← smul_smul]
      exact congrArg (fun y => (α : ℂ) • y) hBx
    have hαc : (α : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast h.alpha_pos.ne') hc
    have := hgap x _ hx hHx hαc
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h.alpha_pos] at this
    rw [hd, div_le_iff₀ h.alpha_pos]
    linarith
  -- quadratic bounds for the increment
  set q := |τ| * (1 + μ) / (1 - |τ| * k₀) with hq
  have hm : 0 < 1 - |τ| * k₀ := by linarith
  have hqd : q < d := by
    rw [hq, div_lt_iff₀ hm]
    nlinarith
  have hcore := fun x : P => incrementCore_bounds K h.selfAdjoint k₀ h.bound τ hτk (J x)
  have hJn := isometry_norm h.isometry
  have hupper_core : ∀ x : P,
      (inner ℂ (J x) (incrementCore K k₀ h.bound τ hτk (J x))).re ≤
        (1 + μ) * ‖x‖ ^ 2 / (1 - |τ| * k₀) := by
    intro x
    refine (hcore x).2.trans ?_
    rw [hJn x]
    apply div_le_div_of_nonneg_right _ hm.le
    have := h.moment x
    nlinarith
  have hlower_core : ∀ x : P, x ≠ 0 →
      0 < (inner ℂ (J x) (incrementCore K k₀ h.bound τ hτk (J x))).re := by
    intro x hx
    refine lt_of_lt_of_le ?_ (hcore x).1
    rw [hJn x]
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hp : 0 < 1 + |τ| * k₀ := by nlinarith [abs_nonneg τ, h.k0_nonneg]
    positivity
  have hΔsa := increment_adjoint J K h.selfAdjoint k₀ h.bound τ hτk
  rcases lt_or_gt_of_ne hτ0 with hneg | hpos
  · -- negative branch
    have hw' := inertia_injective_neg B₀ Δop hB₀sa hΔsa d q hB₀gap
      (fun x hx => by
        rw [hΔop, increment_re]
        exact mul_neg_of_neg_of_pos hneg (hlower_core x hx))
      (fun x => by
        rw [hΔop, increment_re, hq]
        set c := (inner ℂ (J x) (incrementCore K k₀ h.bound τ hτk (J x))).re with hc
        set B := (1 + μ) * ‖x‖ ^ 2 / (1 - |τ| * k₀) with hB
        have hup : c ≤ B := hupper_core x
        have e : |τ| * (1 + μ) / (1 - |τ| * k₀) * ‖x‖ ^ 2 = |τ| * B := by rw [hB]; ring
        rw [e]
        have h1 : τ * B ≤ τ * c := mul_le_mul_of_nonpos_left hup hneg.le
        have h2 : |τ| * B = -(τ * B) := by rw [abs_of_neg hneg]; ring
        linarith)
      hqd w hkernel
    exact hw0 hw'
  · -- positive branch
    have hw' := inertia_injective B₀ Δop hB₀sa hΔsa d q hB₀gap
      (fun x hx => by
        rw [hΔop, increment_re]
        exact mul_pos hpos (hlower_core x hx))
      (fun x => by
        rw [hΔop, increment_re, hq]
        set c := (inner ℂ (J x) (incrementCore K k₀ h.bound τ hτk (J x))).re with hc
        set B := (1 + μ) * ‖x‖ ^ 2 / (1 - |τ| * k₀) with hB
        have hup : c ≤ B := hupper_core x
        have e : |τ| * (1 + μ) / (1 - |τ| * k₀) * ‖x‖ ^ 2 = |τ| * B := by rw [hB]; ring
        rw [e]
        have h1 : τ * c ≤ τ * B := mul_le_mul_of_nonneg_left hup hpos.le
        have h2 : |τ| * B = τ * B := by rw [abs_of_pos hpos]
        linarith)
      hqd w hkernel
    exact hw0 hw'

theorem tStar_pos (α μ k₀ Δ : ℝ) (hα : 0 < α) (hμ : 0 ≤ μ) (hk : 0 ≤ k₀) (hΔ : 0 < Δ) :
    0 < tStar α μ k₀ Δ := by
  unfold tStar
  have : 0 < Δ / α := div_pos hΔ hα
  positivity

/-- **Lemma `qls:lem:walk`, chord form.**  Every eigenvalue `z ≠ 1` of the walk,
including `z = -1`, satisfies `|z - 1| ≥ 2 t*/√(1 + t*²)`. -/
theorem Hyp.chord_gap (h : Hyp J K H α μ k₀) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : ∀ (x : P) (c : ℂ), x ≠ 0 → H x = c • x → c ≠ 0 → Δ ≤ ‖c‖)
    (z : ℂ) (v : V) (hv : v ≠ 0) (hWv : walk J h.cayley v = z • v) (hz1 : z ≠ 1) :
    2 * tStar α μ k₀ Δ / Real.sqrt (1 + tStar α μ k₀ Δ ^ 2) ≤ ‖z - 1‖ := by
  have hz := norm_eigenvalue_eq_one _ h.walk_unitary.1 z v hv hWv
  set t := tStar α μ k₀ Δ with ht
  have htpos : 0 < t := tStar_pos α μ k₀ Δ h.alpha_pos h.mu_nonneg h.k0_nonneg hΔ
  have hs : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt (by positivity)
  have hlhs : 0 ≤ 2 * t / Real.sqrt (1 + t ^ 2) := by positivity
  apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
  rw [div_pow, hsq, mul_pow]
  by_cases hzm1 : z = -1
  · subst hzm1
    have : ‖(-1 : ℂ) - 1‖ = 2 := by
      rw [show (-1 : ℂ) - 1 = ((-2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
      norm_num
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith
  · have hτ := h.tangent_gap Δ hΔ hgap z v hv hWv hz1 hzm1
    have hc := chord_sq z hz hzm1
    have ht2 : t ^ 2 ≤ tau z ^ 2 := by
      have := abs_le_abs_of_nonneg htpos.le hτ
      nlinarith [sq_abs (tau z), abs_nonneg (tau z)]
    rw [div_le_iff₀ (by positivity)]
    have ha4 : ‖z - 1‖ ^ 2 ≤ 4 := by
      rw [norm_sub_one_sq]
      have hn := normSq_unit hz
      have hre : -1 ≤ z.re := by nlinarith [sq_nonneg z.im, sq_nonneg (z.re + 1)]
      nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr ht2) (sub_nonneg.mpr ha4)]

end

end SparseLinearSystems.WalkGap
