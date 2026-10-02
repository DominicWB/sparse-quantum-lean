import SparseHamiltonian.ActiveRegisterLayout

/-!
# Analytic promises for clocks compiled from oracle programs

For a uniform program implementing a unitary involution, the clock length is
its query count plus two.  The exact endpoint energy gives a square-root
operator-norm bound, supplying every analytic hypothesis of the simulation
certificate.  No nontriviality assumption on the payload space is required.
-/

namespace SparseHamiltonian.ProgramClockBounds

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockStep
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {X : Type*} {O : X → V →L[ℂ] V}

/-- Even a zero-query program has a positive, two-slot clock. -/
theorem slots_ge_two (p : Program O) : 2 ≤ (slots p : ℝ) := by
  simp only [slots, Nat.cast_add, Nat.cast_ofNat]
  exact le_add_of_nonneg_left (Nat.cast_nonneg p.count)

/-- The lower bound needed by the logarithmic filter schedule. -/
theorem slots_ge_one (p : Program O) : 1 ≤ (slots p : ℝ) :=
  (by norm_num : (1 : ℝ) ≤ 2).trans (slots_ge_two p)

/-- The endpoint scalar budget is exact, including on a zero-dimensional space. -/
theorem endpoint_budget_sq (p : Program O) :
    Real.sqrt ((slots p : ℝ) / 2) ^ 2 = (slots p : ℝ) / 2 := by
  exact Real.sq_sqrt (by positivity)

/-- Unitarity gives norm at most one without requiring a nonzero vector. -/
theorem program_norm_le_one (p : Program O) (hO : ∀ x, IsUnitary (O x)) (x : X) :
    ‖p.eval x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have hn := (p.eval x).norm_map_iff_adjoint_comp_self.mpr (p.eval_unitary hO x).1 v
  simpa only [one_mul] using hn.le

/-- The generated Hamiltonian is self-adjoint whenever the program is an involution. -/
theorem program_self_adjoint (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    star (p.eval x) = p.eval x :=
  unitary_involution_selfAdjoint (p.eval x) (p.eval_unitary hO x) (hInv x)

/-- The public clock boundary is a fixed isometry. -/
theorem program_boundary_isometry (p : Program O) :
    (ClockOperators.boundary (p.count + 1) : V →L[ℂ] ClockOperators.H (p.count + 1) V)† ∘L
      ClockOperators.boundary (p.count + 1) = 1 :=
  ClockOperators.boundary_adjoint_comp (p.count + 1)

variable [FiniteDimensional ℂ V]

/-- Pointwise endpoint energy implies the required operator-norm budget. -/
theorem program_endpoint_norm_le (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    ‖programResolvent p hO hInv x ∘L ClockOperators.boundary (p.count + 1)‖ ≤
      Real.sqrt ((slots p : ℝ) / 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro v
  have he := programResolvent_endpoint_energy p hO hInv x v
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, endpoint_budget_sq, he]

/-- All analytic promises, in the order required by the evolution query
certificate.  The maximum and mean clock budgets are both the actual number
of slots; the endpoint budget is their square root divided by `sqrt 2`. -/
theorem programClock_promises (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) :
    let Q : ℝ := slots p
    let b := Real.sqrt (Q / 2)
    let D := programClock p hO hInv
    let R := programResolvent p hO hInv
    let J : V →L[ℂ] ClockOperators.H (p.count + 1) V := ClockOperators.boundary (p.count + 1)
    1 ≤ Q ∧
      (∀ x, (D x)† ∘L D x = 1) ∧ J† ∘L J = 1 ∧
      (∀ x, (1 - D x) ∘L R x = 1) ∧
      (∀ x, R x ∘L (1 - D x) = 1) ∧
      (∀ x, ‖R x‖ ≤ Q) ∧
      (∀ x, J† ∘L R x ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • p.eval x)) ∧
      (∀ x, star (p.eval x) = p.eval x) ∧
      (∀ x, ‖p.eval x‖ ≤ 1) ∧
      (∀ x, ‖R x ∘L J‖ ≤ b) ∧ b ^ 2 ≤ Q / 2 ∧ Q ≤ Q := by
  exact ⟨slots_ge_one p, programClock_isometry p hO hInv,
    program_boundary_isometry p,
    fun x => (programResolvent_inverse p hO hInv x).1,
    fun x => (programResolvent_inverse p hO hInv x).2,
    programResolvent_norm_le p hO hInv, programResolvent_compression p hO hInv,
    program_self_adjoint p hO hInv, program_norm_le_one p hO,
    program_endpoint_norm_le p hO hInv, (endpoint_budget_sq p).le, le_rfl⟩

end

end SparseHamiltonian.ProgramClockBounds
