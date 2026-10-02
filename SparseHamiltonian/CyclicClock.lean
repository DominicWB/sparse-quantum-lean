import SparseHamiltonian.AmplificationIsometry

/-!
# Actual finite cyclic clocks and their boundary response

The clock has `q+1` valid slots: each ordinary link is the identity and the
return link is `i O`, where `O` is a Hermitian involution. This is a concrete
clock, rather than a hypothesis about an unspecified operator. General
query-distributed clocks are related to this canonical clock by slotwise
unitary changes of coordinates; that implementation step is not claimed here.

The clock inner product and energy below are explicitly finite sums. They are
the Hilbert direct-sum quantities, not the default sup norm on a function type.
-/

namespace SparseHamiltonian.CyclicClock

open scoped BigOperators ComplexConjugate

section AlgebraicClock

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Advance the clock one slot, applying `i O` at the return link. -/
def clockStep (O : V →ₗ[ℂ] V) (q : ℕ) :
    (Fin (q + 1) → V) →ₗ[ℂ] (Fin (q + 1) → V) where
  toFun x := Fin.cases (Complex.I • O (x (Fin.last q))) (fun j => x j.castSucc)
  map_add' x y := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [map_add, smul_add]
  map_smul' c x := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change Complex.I • O (c • x (Fin.last q)) = c • (Complex.I • O (x (Fin.last q)))
      rw [map_smul, smul_comm Complex.I c]
    · rfl

@[simp] theorem clockStep_zero (O : V →ₗ[ℂ] V) (q : ℕ) (x : Fin (q + 1) → V) :
    clockStep O q x 0 = Complex.I • O (x (Fin.last q)) := rfl

@[simp] theorem clockStep_succ (O : V →ₗ[ℂ] V) (q : ℕ)
    (x : Fin (q + 1) → V) (j : Fin q) :
    clockStep O q x j.succ = x j.castSucc := rfl

/-- Embed the public vector at the distinguished boundary slot. -/
def boundary (q : ℕ) : V →ₗ[ℂ] (Fin (q + 1) → V) where
  toFun v := Fin.cases v (fun _ => 0)
  map_add' v w := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp
  map_smul' c v := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp

@[simp] theorem boundary_zero (q : ℕ) (v : V) : boundary q v 0 = v := rfl

@[simp] theorem boundary_succ (q : ℕ) (v : V) (j : Fin q) :
    boundary q v j.succ = 0 := rfl

/-- The exact scalar-time Cayley inverse of `I-iO`. -/
noncomputable def localResponse (O : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  (1 / 2 : ℂ) • (LinearMap.id + Complex.I • O)

@[simp] theorem localResponse_apply (O : V →ₗ[ℂ] V) (v : V) :
    localResponse O v = (1 / 2 : ℂ) • (v + Complex.I • O v) := rfl

theorem localResponse_left_inverse (O : V →ₗ[ℂ] V)
    (hO : ∀ v, O (O v) = v) (v : V) :
    localResponse O (v - Complex.I • O v) = v := by
  simp only [localResponse_apply, map_sub, map_smul, hO]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

theorem localResponse_right_inverse (O : V →ₗ[ℂ] V)
    (hO : ∀ v, O (O v) = v) (v : V) :
    localResponse O v - Complex.I • O (localResponse O v) = v := by
  simp only [localResponse_apply, map_add, map_smul, hO]
  match_scalars <;> ring_nf
  all_goals norm_num [Complex.I_sq]

/-- Every slot of the boundary response is the same vector. -/
noncomputable def boundaryResponse (O : V →ₗ[ℂ] V) (q : ℕ) :
    V →ₗ[ℂ] (Fin (q + 1) → V) where
  toFun v _ := localResponse O v
  map_add' v w := by funext j; exact (localResponse O).map_add v w
  map_smul' c v := by funext j; exact (localResponse O).map_smul c v

@[simp] theorem boundaryResponse_apply (O : V →ₗ[ℂ] V) (q : ℕ)
    (v : V) (j : Fin (q + 1)) :
    boundaryResponse O q v j = localResponse O v := rfl

/-- This is an actual solution of the boundary resolvent equation. -/
theorem boundaryResponse_equation (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (v : V) :
    boundaryResponse O q v - clockStep O q (boundaryResponse O q v) =
      boundary q v := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa using localResponse_right_inverse O hO v
  · simp

/-- Zero resolvent input has only the zero solution. -/
theorem clock_resolvent_kernel (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (x : Fin (q + 1) → V)
    (hx : x - clockStep O q x = 0) : x = 0 := by
  have hstep : ∀ j : Fin q, x j.succ = x j.castSucc := by
    intro j
    have h := congrFun hx j.succ
    simpa only [Pi.sub_apply, clockStep_succ, Pi.zero_apply, sub_eq_zero] using h
  have hconst : ∀ j : Fin (q + 1), x j = x 0 := by
    intro j
    induction j using Fin.induction with
    | zero => rfl
    | succ j ih => exact (hstep j).trans ih
  have hzero : x 0 - Complex.I • O (x 0) = 0 := by
    have h := congrFun hx 0
    simpa only [Pi.sub_apply, clockStep_zero, Pi.zero_apply, hconst] using h
  have hx0 : x 0 = 0 := by
    have h := localResponse_left_inverse O hO (x 0)
    rw [hzero, map_zero] at h
    exact h.symm
  funext j
  exact (hconst j).trans hx0

theorem clock_resolvent_injective (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) :
    Function.Injective (LinearMap.id - clockStep O q :
      (Fin (q + 1) → V) →ₗ[ℂ] (Fin (q + 1) → V)) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  exact clock_resolvent_kernel O q hO x hx

/-- Boundary response is uniquely characterized by the resolvent equation. -/
theorem boundaryResponse_unique (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (v : V) (x : Fin (q + 1) → V)
    (hx : x - clockStep O q x = boundary q v) :
    x = boundaryResponse O q v := by
  apply clock_resolvent_injective O q hO
  exact hx.trans (boundaryResponse_equation O q hO v).symm

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- The genuine inverse of the finite-dimensional clock resolvent denominator. -/
noncomputable def resolvent (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) :
    (Fin (q + 1) → V) ≃ₗ[ℂ] (Fin (q + 1) → V) :=
  (LinearEquiv.ofBijective (LinearMap.id - clockStep O q)
    ⟨clock_resolvent_injective O q hO,
      LinearMap.injective_iff_surjective.mp (clock_resolvent_injective O q hO)⟩).symm

/-- The explicitly constructed trajectory is precisely `(I-D)⁻¹J`. -/
theorem resolvent_boundary (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (v : V) :
    resolvent O q hO (boundary q v) = boundaryResponse O q v := by
  apply boundaryResponse_unique O q hO v
  exact (LinearEquiv.ofBijective (LinearMap.id - clockStep O q)
    ⟨clock_resolvent_injective O q hO,
      LinearMap.injective_iff_surjective.mp (clock_resolvent_injective O q hO)⟩).apply_symm_apply _

/-- Boundary compression of the actual inverse. -/
theorem resolvent_boundary_compression (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) (v : V) :
    resolvent O q hO (boundary q v) 0 = (1 / 2 : ℂ) • (v + Complex.I • O v) := by
  rw [resolvent_boundary]
  rfl

end FiniteDimensional
end AlgebraicClock

section HilbertClock

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Explicit Hilbert direct-sum inner product. -/
def clockInner (q : ℕ) (x y : Fin (q + 1) → V) : ℂ :=
  ∑ j, inner ℂ (x j) (y j)

/-- Explicit squared Hilbert direct-sum norm. -/
def clockEnergy (q : ℕ) (x : Fin (q + 1) → V) : ℝ :=
  ∑ j, ‖x j‖ ^ 2

theorem boundary_inner (q : ℕ) (v : V) (x : Fin (q + 1) → V) :
    clockInner q (boundary q v) x = inner ℂ v (x 0) := by
  simp [clockInner, Fin.sum_univ_succ]

theorem boundary_isometry (q : ℕ) (v w : V) :
    clockInner q (boundary q v) (boundary q w) = inner ℂ v w := by
  rw [boundary_inner, boundary_zero]

theorem return_inner (O : V →ₗ[ℂ] V)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v w : V) :
    inner ℂ (Complex.I • O v) (Complex.I • O w) = inner ℂ v w := by
  simp only [inner_smul_left, inner_smul_right, Complex.conj_I, hHerm, hO]
  ring_nf
  simp [Complex.I_sq]

/-- The explicitly constructed clock preserves the Hilbert direct-sum inner product. -/
theorem clockStep_inner (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (x y : Fin (q + 1) → V) :
    clockInner q (clockStep O q x) (clockStep O q y) = clockInner q x y := by
  unfold clockInner
  rw [Fin.sum_univ_succ]
  simp only [clockStep_zero, clockStep_succ, return_inner O hO hHerm]
  rw [Fin.sum_univ_castSucc]
  exact add_comm _ _

theorem localResponse_inner (O : V →ₗ[ℂ] V)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v w : V) :
    inner ℂ (localResponse O v) (localResponse O w) = (1 / 2 : ℂ) * inner ℂ v w := by
  have hOO : inner ℂ (O v) (O w) = inner ℂ v w := by rw [hHerm, hO]
  simp only [localResponse_apply, inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, hOO, hHerm]
  norm_num [Complex.conj_I]
  ring_nf
  norm_num [Complex.I_sq]
  rw [map_ofNat]
  ring

/-- Endpoint Gram identity of the concrete clock response. -/
theorem boundaryResponse_inner (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v w : V) :
    clockInner q (boundaryResponse O q v) (boundaryResponse O q w) =
      ((q + 1 : ℕ) : ℂ) / 2 * inner ℂ v w := by
  simp only [clockInner, boundaryResponse_apply, localResponse_inner O hO hHerm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  ring

theorem localResponse_energy (O : V →ₗ[ℂ] V)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v : V) :
    ‖localResponse O v‖ ^ 2 = ‖v‖ ^ 2 / 2 := by
  have h := localResponse_inner O hO hHerm v v
  simp only [inner_self_eq_norm_sq_to_K] at h
  have hc : (1 / 2 : ℂ) * (↑‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hreal := congrArg (RCLike.re : ℂ → ℝ) (h.trans hc)
  simp only [RCLike.re_ofReal_pow] at hreal
  exact hreal

/-- Squared Hilbert norm of the actual boundary response. -/
theorem boundaryResponse_energy (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v : V) :
    clockEnergy q (boundaryResponse O q v) =
      ((q + 1 : ℕ) : ℝ) / 2 * ‖v‖ ^ 2 := by
  simp only [clockEnergy, boundaryResponse_apply, localResponse_energy O hO hHerm,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  ring

/-- The endpoint Gram formula now refers to the true inverse `(I-D)⁻¹`. -/
theorem resolvent_boundary_inner [FiniteDimensional ℂ V]
    (O : V →ₗ[ℂ] V) (q : ℕ) (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v w : V) :
    clockInner q (resolvent O q hO (boundary q v))
      (resolvent O q hO (boundary q w)) =
        ((q + 1 : ℕ) : ℂ) / 2 * inner ℂ v w := by
  rw [resolvent_boundary, resolvent_boundary]
  exact boundaryResponse_inner O q hO hHerm v w

theorem resolvent_boundary_energy [FiniteDimensional ℂ V]
    (O : V →ₗ[ℂ] V) (q : ℕ) (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v : V) :
    clockEnergy q (resolvent O q hO (boundary q v)) =
      ((q + 1 : ℕ) : ℝ) / 2 * ‖v‖ ^ 2 := by
  rw [resolvent_boundary]
  exact boundaryResponse_energy O q hO hHerm v

/-- The energy identity also holds for mathlib's actual `PiLp 2` Hilbert norm. -/
theorem boundaryResponse_hilbert_norm_sq (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v : V) :
    ‖(WithLp.toLp 2 (boundaryResponse O q v) : PiLp 2 (fun _ : Fin (q + 1) => V))‖ ^ 2 =
      ((q + 1 : ℕ) : ℝ) / 2 * ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact boundaryResponse_energy O q hO hHerm v

theorem resolvent_boundary_hilbert_norm_sq [FiniteDimensional ℂ V]
    (O : V →ₗ[ℂ] V) (q : ℕ) (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w)) (v : V) :
    ‖(WithLp.toLp 2 (resolvent O q hO (boundary q v)) :
      PiLp 2 (fun _ : Fin (q + 1) => V))‖ ^ 2 =
        ((q + 1 : ℕ) : ℝ) / 2 * ‖v‖ ^ 2 := by
  rw [resolvent_boundary]
  exact boundaryResponse_hilbert_norm_sq O q hO hHerm v

end HilbertClock

end SparseHamiltonian.CyclicClock
