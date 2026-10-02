import SparseHamiltonian.ClockStepQuery

/-!
# Actual distributed clocks from uniform oracle programs

A program with `q` queries gives `q+1` individual links and `q+2` clock slots.
All link gates and query polarities are extracted from syntax independently of
the unknown input. Implementation of the clock uses one coherent selection of
these oracle letters, followed by fixed gates and a fixed cyclic shift.
-/

namespace SparseHamiltonian.QueryClockStep

noncomputable section
open ContinuousLinearMap OracleCircuit QueryClockLinks ClockStepQuery
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {X : Type*} {O : X → V →L[ℂ] V}

/-- A unitary involution is self-adjoint; this is derived rather than assumed. -/
theorem unitary_involution_selfAdjoint (U : V →L[ℂ] V) (hU : IsUnitary U)
    (hInv : ∀ v, U (U v) = v) : star U = U := by
  have hSquare : U * U = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact hInv v
  calc
    star U = star U * (U * U) := by rw [hSquare, mul_one]
    _ = (star U * U) * U := by rw [mul_assoc]
    _ = U := by rw [hU.1, one_mul]

/-- The inner-product form of self-adjointness for the actual program output. -/
theorem program_hermitian (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) (v w : V) :
    inner ℂ (p.eval x v) w = inner ℂ v (p.eval x w) := by
  have hSelf := unitary_involution_selfAdjoint (p.eval x) (p.eval_unitary hO x) (hInv x)
  rw [← adjoint_inner_right]
  have hAdjoint : (p.eval x)† = p.eval x := hSelf
  rw [hAdjoint]

/-- Number of genuine slots, including the terminal fixed gate and return edge. -/
def slots (p : Program O) : ℕ := p.count + 2

/-- The clock-length overhead is bounded by a uniform constant, also for zero queries. -/
theorem slots_le_twice (p : Program O) : slots p ≤ 2 * (p.count + 1) := by
  exact QueryClockLinks.clock_slots_le_twice p.count

/-- The actual clock derived from the original program. -/
def programClock (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    ClockOperators.H (p.count + 1) V →L[ℂ] ClockOperators.H (p.count + 1) V :=
  ClockGauge.distributedClock (p.eval x).toLinearMap (p.count + 1)
    (hInv x) (program_hermitian p hO hInv x)
    (fun j => ClockGauge.prefixGauge (clockLinkEquiv p hO x) j.val)

/-- The forward/inverse/inactive query SELECT extracted from program syntax. -/
def selectedQueries (p : Program O) (x : X) :
    ClockOperators.H (p.count + 1) V →L[ℂ] ClockOperators.H (p.count + 1) V :=
  paddedSelect (p.count + 1) (fun j => optionalQuery O (clockLinkData p j.val).2 x)

/-- Explicit factorization using the fixed shift and fixed selected link gates. -/
theorem programClock_factor (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    programClock p hO hInv x =
      phasedShift (p.count + 1) ∘L
        (paddedSelect (p.count + 1) (fun j => (clockLinkData p j.val).1.val) ∘L
          selectedQueries p x) := by
  rw [programClock, prefix_distributedClock_factor _ _ _ _ _
    (fun v => (prefixGauge_clockLinkEquiv p hO x v).symm)]
  rw [linkSelect_factor (p.count + 1) (clockLinkEquiv p hO x)
    (fun j => (clockLinkData p j.val).1.val)
    (fun j => optionalQuery O (clockLinkData p j.val).2 x)
    (fun j => clockLinkEquiv_factor p hO x j.val)]
  rfl

/-- A uniform selected-query implementation directly implements the complete
clock. Neither program length nor number of free gates multiplies the cost. -/
theorem programClock_implements (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v)
    (R : X → ClockOperators.H (p.count + 1) V →L[ℂ] ClockOperators.H (p.count + 1) V)
    (c : ℕ) (hSelected : Implements R (selectedQueries p) c) :
    Implements R (programClock p hO hInv) c := by
  apply distributedClock_implements_of_link_factors R
    (fun x => (p.eval x).toLinearMap) (fun x => hInv x)
    (program_hermitian p hO hInv) (clockLinkEquiv p hO)
    (fun x v => (prefixGauge_clockLinkEquiv p hO x v).symm)
    (fun j => (clockLinkData p j.val).1.val) (fun j => (clockLinkData p j.val).1.property)
    (fun x j => optionalQuery O (clockLinkData p j.val).2 x)
    (fun x j => clockLinkEquiv_factor p hO x j.val) c hSelected

/-- Every generated clock step is genuinely isometric independently of its
query implementation. -/
theorem programClock_isometry (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (programClock p hO hInv x)† ∘L programClock p hO hInv x = 1 :=
  ClockGauge.distributedClock_adjoint_comp _ _ _ _ _

variable [FiniteDimensional ℂ V]

/-- The actual inverse of `1-D` for the syntax-derived distributed clock. -/
def programResolvent (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    ClockOperators.H (p.count + 1) V →L[ℂ] ClockOperators.H (p.count + 1) V :=
  ClockGauge.distributedResolvent (p.eval x).toLinearMap (p.count + 1) (hInv x)
    (fun j => ClockGauge.prefixGauge (clockLinkEquiv p hO x) j.val)

/-- Both inverse identities hold for the constructed resolvent. -/
theorem programResolvent_inverse (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (1 - programClock p hO hInv x) ∘L programResolvent p hO hInv x = 1 ∧
      programResolvent p hO hInv x ∘L (1 - programClock p hO hInv x) = 1 :=
  ClockGauge.distributedResolvent_inverse _ _ _ _ _

/-- The resolvent norm is controlled by the original query count plus two. -/
theorem programResolvent_norm_le (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    ‖programResolvent p hO hInv x‖ ≤ (slots p : ℝ) := by
  exact ClockGauge.distributedResolvent_norm_le (p.eval x).toLinearMap (p.count + 1)
    (hInv x) (program_hermitian p hO hInv x) _

/-- Exact boundary energy gives the program-query-length catalyst budget. -/
theorem programResolvent_endpoint_energy (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) (v : V) :
    ‖(programResolvent p hO hInv x ∘L ClockOperators.boundary (p.count + 1)) v‖ ^ 2 =
      (slots p : ℝ) / 2 * ‖v‖ ^ 2 := by
  exact ClockGauge.distributedResolvent_endpoint_energy (p.eval x).toLinearMap
    (p.count + 1) (hInv x) (program_hermitian p hO hInv x) _ rfl v

/-- The boundary generator is exactly the original program output. -/
theorem programResolvent_compression (p : Program O) (hO : ∀ x, IsUnitary (O x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (ClockOperators.boundary (p.count + 1))† ∘L programResolvent p hO hInv x ∘L
      ClockOperators.boundary (p.count + 1) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • p.eval x) := by
  exact ClockGauge.distributedResolvent_compression (p.eval x).toLinearMap
    (p.count + 1) (hInv x) _ rfl

end
end SparseHamiltonian.QueryClockStep
