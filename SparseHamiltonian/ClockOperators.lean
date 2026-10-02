import SparseHamiltonian.ClockCycle

/-!
# Canonical clocks as Hilbert-space bounded operators

This module transports the concrete cyclic clock to the actual `PiLp 2` space.
The clock and boundary injection are isometries, and the inverse boundary
compression and endpoint norm are statements about continuous linear maps.
-/

namespace SparseHamiltonian.ClockOperators

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The finite clock's Hilbert direct sum. -/
abbrev H (q : ℕ) (V : Type*) := PiLp 2 (fun _ : Fin (q + 1) => V)

/-- The algebraic clock transported to the Hilbert direct sum. -/
def clockLinear (O : V →ₗ[ℂ] V) (q : ℕ) : H q V →ₗ[ℂ] H q V :=
  (WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ
    CyclicClock.clockStep O q ∘ₗ (WithLp.linearEquiv 2 ℂ _).toLinearMap

@[simp] theorem clockLinear_apply (O : V →ₗ[ℂ] V) (q : ℕ) (x : H q V) :
    clockLinear O q x = WithLp.toLp 2 (CyclicClock.clockStep O q (WithLp.ofLp x)) := rfl

/-- The canonical clock is an actual Hilbert-space linear isometry. -/
def clockIsometry (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) : H q V →ₗᵢ[ℂ] H q V :=
  (clockLinear O q).isometryOfInner (fun x y => CyclicClock.clockStep_inner O q hO hHerm x y)

/-- Canonical clock in the continuous-operator norm. -/
def clock (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) : H q V →L[ℂ] H q V :=
  (clockIsometry O q hO hHerm).toContinuousLinearMap

@[simp] theorem clock_apply (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (x : H q V) :
    clock O q hO hHerm x = WithLp.toLp 2 (CyclicClock.clockStep O q (WithLp.ofLp x)) := rfl

theorem clock_norm_le (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    ‖clock O q hO hHerm‖ ≤ 1 := (clockIsometry O q hO hHerm).norm_toContinuousLinearMap_le

/-- Powers commute with transport from the algebraic clock. -/
theorem clock_pow_apply (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (n : ℕ) (x : H q V) :
    (clock O q hO hHerm ^ n) x =
      WithLp.toLp 2 ((CyclicClock.clockStep O q ^ n) (WithLp.ofLp x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change clock O q hO hHerm ((clock O q hO hHerm ^ n) x) = _
      rw [ih]
      rfl

/-- Two full traversals of the canonical clock have phase minus one. -/
theorem clock_pow_two_cycles (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    clock O q hO hHerm ^ (2 * (q + 1)) = -1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [clock_pow_apply, CyclicClock.clockStep_pow_two_cycles O q hO]
  rfl

/-- The distinguished slot is an isometric public injection. -/
def boundaryIsometry (q : ℕ) : V →ₗᵢ[ℂ] H q V :=
  ((WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ CyclicClock.boundary q).isometryOfInner
    (fun v w => CyclicClock.boundary_isometry q v w)

/-- Boundary injection as a continuous linear map. -/
def boundary (q : ℕ) : V →L[ℂ] H q V := (boundaryIsometry q).toContinuousLinearMap

@[simp] theorem boundary_apply (q : ℕ) (v : V) :
    boundary q v = WithLp.toLp 2 (CyclicClock.boundary q v) := rfl

section Complete
variable [CompleteSpace V]

theorem clock_adjoint_comp (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    (clock O q hO hHerm)† ∘L clock O q hO hHerm = 1 :=
  (clockIsometry O q hO hHerm).adjoint_comp_self

theorem boundary_adjoint_comp (q : ℕ) :
    (boundary q : V →L[ℂ] H q V)† ∘L boundary q = 1 :=
  (boundaryIsometry (V := V) q).adjoint_comp_self

/-- The actual adjoint boundary operator reads slot zero. -/
theorem boundary_adjoint_apply (q : ℕ) (x : H q V) :
    ((boundary q : V →L[ℂ] H q V)†) x = x 0 := by
  apply ext_inner_left ℂ
  intro v
  rw [adjoint_inner_right]
  exact CyclicClock.boundary_inner q v x

end Complete

section FiniteDimensional
variable [FiniteDimensional ℂ V]

/-- The already constructed genuine inverse transported to the Hilbert direct sum. -/
def resolvent (O : V →ₗ[ℂ] V) (q : ℕ) (hO : ∀ v, O (O v) = v) : H q V →L[ℂ] H q V :=
  ((WithLp.linearEquiv 2 ℂ _).symm.toLinearMap ∘ₗ
    (CyclicClock.resolvent O q hO).toLinearMap ∘ₗ
    (WithLp.linearEquiv 2 ℂ _).toLinearMap).toContinuousLinearMap

@[simp] theorem resolvent_apply (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (x : H q V) :
    resolvent O q hO x = WithLp.toLp 2 (CyclicClock.resolvent O q hO (WithLp.ofLp x)) := rfl

theorem resolvent_right_inverse (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    (1 - clock O q hO hHerm) ∘L resolvent O q hO = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change WithLp.toLp 2 ((LinearMap.id - CyclicClock.clockStep O q : (Fin (q + 1) → V) →ₗ[ℂ] (Fin (q + 1) → V))
    (CyclicClock.resolvent O q hO (WithLp.ofLp x))) = x
  have h := (CyclicClock.resolvent O q hO).symm_apply_apply (WithLp.ofLp x)
  exact congrArg (WithLp.toLp 2) h

theorem resolvent_left_inverse (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    resolvent O q hO ∘L (1 - clock O q hO hHerm) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change WithLp.toLp 2 (CyclicClock.resolvent O q hO
    ((LinearMap.id - CyclicClock.clockStep O q : (Fin (q + 1) → V) →ₗ[ℂ] (Fin (q + 1) → V)) (WithLp.ofLp x))) = x
  have h := (CyclicClock.resolvent O q hO).apply_symm_apply (WithLp.ofLp x)
  exact congrArg (WithLp.toLp 2) h

/-- The genuine inverse agrees with the explicit finite geometric resolvent. -/
theorem resolvent_eq_finiteResolvent (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    resolvent O q hO = OperatorResolvent.finiteResolvent (clock O q hO hHerm) (q + 1) := by
  have hLeft := resolvent_left_inverse O q hO hHerm
  have hRight := OperatorResolvent.finiteResolvent_right_inverse
    (clock O q hO hHerm) (q + 1) (clock_pow_two_cycles O q hO hHerm)
  change resolvent O q hO * (1 - clock O q hO hHerm) = 1 at hLeft
  calc
    resolvent O q hO = resolvent O q hO *
        ((1 - clock O q hO hHerm) * OperatorResolvent.finiteResolvent
          (clock O q hO hHerm) (q + 1)) := by rw [hRight, mul_one]
    _ = OperatorResolvent.finiteResolvent (clock O q hO hHerm) (q + 1) := by
      rw [← mul_assoc, hLeft, one_mul]

/-- The clock-length bound is derived for the actual inverse. -/
theorem resolvent_norm_le (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    ‖resolvent O q hO‖ ≤ ((q + 1 : ℕ) : ℝ) := by
  rcases subsingleton_or_nontrivial (H q V) with hV | hV
  · letI := hV
    have hr : resolvent O q hO = 0 := Subsingleton.elim _ _
    calc
      ‖resolvent O q hO‖ = 0 := (ContinuousLinearMap.opNorm_zero_iff _).mpr hr
      _ ≤ ((q + 1 : ℕ) : ℝ) := Nat.cast_nonneg' _
  · letI := hV
    rw [resolvent_eq_finiteResolvent O q hO hHerm]
    exact OperatorResolvent.norm_finiteResolvent_le _ _ (clock_norm_le O q hO hHerm)

/-- The continuous-operator boundary response is exactly the constant trajectory. -/
theorem resolvent_boundary_apply (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (v : V) :
    (resolvent O q hO ∘L boundary q) v =
      WithLp.toLp 2 (CyclicClock.boundaryResponse O q v) := by
  change WithLp.toLp 2 (CyclicClock.resolvent O q hO (CyclicClock.boundary q v)) = _
  rw [CyclicClock.resolvent_boundary]

/-- Exact squared endpoint norm, in the genuine Hilbert norm. -/
theorem resolvent_boundary_norm_sq (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v : V) :
    ‖(resolvent O q hO ∘L boundary q) v‖ ^ 2 = ((q + 1 : ℕ) : ℝ) / 2 * ‖v‖ ^ 2 := by
  rw [resolvent_boundary_apply]
  exact CyclicClock.boundaryResponse_hilbert_norm_sq O q hO hHerm v

/-- The weighted endpoint bound used in the global chronological resolvent. -/
theorem resolvent_boundary_norm_le (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    ‖resolvent O q hO ∘L boundary q‖ ≤ Real.sqrt (((q + 1 : ℕ) : ℝ) / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have hs : 0 ≤ ((q + 1 : ℕ) : ℝ) / 2 := by positivity
  have he := resolvent_boundary_norm_sq O q hO hHerm v
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hs, he]

/-- The Hermitian involution has operator norm at most one. -/
theorem public_norm_le (O : V →ₗ[ℂ] V)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    ‖O.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hn : ‖O v‖ = ‖v‖ :=
    (O.isometryOfInner (fun x y => by rw [hHerm, hO])).norm_map v
  simpa only [one_mul, LinearMap.coe_toContinuousLinearMap'] using hn.le

variable [CompleteSpace V]

/-- The concrete public operator is self-adjoint in the bounded-operator algebra. -/
theorem public_self_adjoint (O : V →ₗ[ℂ] V)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) :
    star O.toContinuousLinearMap = O.toContinuousLinearMap := by
  exact ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr hHerm).symm

/-- Exact boundary compression in continuous-operator notation. -/
theorem resolvent_boundary_compression (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) :
    (boundary q)† ∘L resolvent O q hO ∘L boundary q =
      (2 : ℂ)⁻¹ • (1 + Complex.I • O.toContinuousLinearMap) := by
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    boundary_adjoint_apply]
  change CyclicClock.resolvent O q hO (CyclicClock.boundary q v) 0 = _
  rw [CyclicClock.resolvent_boundary_compression]
  simp only [one_div, smul_apply, add_apply, LinearMap.coe_toContinuousLinearMap']
  rfl

end FiniteDimensional
end
end SparseHamiltonian.ClockOperators
