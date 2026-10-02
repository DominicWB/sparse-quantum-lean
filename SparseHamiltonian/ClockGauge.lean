import SparseHamiltonian.AmplifiedSmoothing

/-!
# Unitary gauges and distributed clock links

A slotwise unitary change of coordinates turns the canonical clock into a
clock with nontrivial internal links.  When it fixes slot zero, the public
boundary map is unchanged.  Both inverse identities, the inverse operator
norm, boundary compression and endpoint energies are preserved exactly.
This establishes the operator equivalence; it does not assign query costs
or construct sparse-oracle implementations of the link unitaries.
-/

namespace SparseHamiltonian.ClockGauge

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

section Conjugation
variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- Change the coordinates of a bounded operator by a unitary equivalence. -/
def conjugate (U : V ≃ₗᵢ[ℂ] V) (A : V →L[ℂ] V) : V →L[ℂ] V :=
  U.conjStarAlgEquiv A

@[simp] theorem conjugate_apply (U : V ≃ₗᵢ[ℂ] V) (A : V →L[ℂ] V) (x : V) :
    conjugate U A x = U (A (U.symm x)) := rfl

/-- The operator norm is invariant, including on a zero-dimensional space. -/
theorem conjugate_norm (U : V ≃ₗᵢ[ℂ] V) (A : V →L[ℂ] V) :
    ‖conjugate U A‖ = ‖A‖ := by
  apply le_antisymm
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [conjugate_apply, U.norm_map, U.symm.norm_map] using A.le_opNorm (U.symm x)
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (conjugate U A).le_opNorm (U x)
    simpa only [conjugate_apply, U.symm_apply_apply, U.norm_map] using h

/-- Conjugation transports a genuine two-sided resolvent inverse. -/
theorem conjugate_resolvent_inverse (U : V ≃ₗᵢ[ℂ] V)
    (D R : V →L[ℂ] V) (z : ℂ)
    (hRight : (z • 1 - D) ∘L R = 1) (hLeft : R ∘L (z • 1 - D) = 1) :
    (z • 1 - conjugate U D) ∘L conjugate U R = 1 ∧
    conjugate U R ∘L (z • 1 - conjugate U D) = 1 := by
  constructor
  · change (z • 1 - U.conjStarAlgEquiv D) * U.conjStarAlgEquiv R = 1
    change (z • 1 - D) * R = 1 at hRight
    have h := congrArg U.conjStarAlgEquiv hRight
    simpa only [map_mul, map_sub, map_smul, map_one] using h
  · change U.conjStarAlgEquiv R * (z • 1 - U.conjStarAlgEquiv D) = 1
    change R * (z • 1 - D) = 1 at hLeft
    have h := congrArg U.conjStarAlgEquiv hLeft
    simpa only [map_mul, map_sub, map_smul, map_one] using h

/-- An isometric private step stays isometric under a unitary gauge. -/
theorem conjugate_adjoint_comp (U : V ≃ₗᵢ[ℂ] V) (D : V →L[ℂ] V)
    (hD : D† ∘L D = 1) :
    (conjugate U D)† ∘L conjugate U D = 1 := by
  change star D * D = 1 at hD
  have h := congrArg U.conjStarAlgEquiv hD
  change star (U.conjStarAlgEquiv D) * U.conjStarAlgEquiv D = 1
  simpa only [← star_eq_adjoint, map_mul,
    map_star, map_one] using h

omit [CompleteSpace V] in
/-- Fixing the public injection also fixes it under the inverse gauge. -/
theorem symm_fixes_boundary (U : V ≃ₗᵢ[ℂ] V) (J : P →L[ℂ] V)
    (hJ : ∀ x, U (J x) = J x) (x : P) : U.symm (J x) = J x := by
  apply U.injective
  rw [U.apply_symm_apply, hJ]

/-- The transformed endpoint is the old endpoint followed by an isometry. -/
theorem conjugate_boundary_apply (U : V ≃ₗᵢ[ℂ] V) (R : V →L[ℂ] V)
    (J : P →L[ℂ] V) (hJ : ∀ x, U (J x) = J x) (x : P) :
    (conjugate U R ∘L J) x = U ((R ∘L J) x) := by
  simp only [comp_apply, conjugate_apply, symm_fixes_boundary U J hJ]

/-- Pointwise boundary energy, and hence the weighted catalyst budget, is unchanged. -/
theorem conjugate_boundary_norm_apply (U : V ≃ₗᵢ[ℂ] V) (R : V →L[ℂ] V)
    (J : P →L[ℂ] V) (hJ : ∀ x, U (J x) = J x) (x : P) :
    ‖(conjugate U R ∘L J) x‖ = ‖(R ∘L J) x‖ := by
  rw [conjugate_boundary_apply U R J hJ, U.norm_map]

/-- The endpoint operator norm is unchanged as well. -/
theorem conjugate_boundary_norm (U : V ≃ₗᵢ[ℂ] V) (R : V →L[ℂ] V)
    (J : P →L[ℂ] V) (hJ : ∀ x, U (J x) = J x) :
    ‖conjugate U R ∘L J‖ = ‖R ∘L J‖ := by
  apply le_antisymm
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [conjugate_boundary_norm_apply U R J hJ]
    exact (R ∘L J).le_opNorm x
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← conjugate_boundary_norm_apply U R J hJ]
    exact (conjugate U R ∘L J).le_opNorm x

variable [CompleteSpace P]

/-- The effective public compression is invariant under a boundary-fixing gauge. -/
theorem conjugate_boundary_compression (U : V ≃ₗᵢ[ℂ] V) (R : V →L[ℂ] V)
    (J : P →L[ℂ] V) (hJ : ∀ x, U (J x) = J x) :
    J† ∘L conjugate U R ∘L J = J† ∘L R ∘L J := by
  ext x
  apply ext_inner_left ℂ
  intro y
  simp only [comp_apply, adjoint_inner_right, conjugate_apply, symm_fixes_boundary U J hJ]
  calc
    inner ℂ (J y) (U (R (J x))) = inner ℂ (U (J y)) (U (R (J x))) := by rw [hJ]
    _ = inner ℂ (J y) (R (J x)) := U.inner_map_map _ _

end Conjugation

section Slots
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The genuine Hilbert-space unitary applying a separate gauge at each slot. -/
def slotGauge (q : ℕ) (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) :
    ClockOperators.H q V ≃ₗᵢ[ℂ] ClockOperators.H q V :=
  LinearIsometryEquiv.piLpCongrRight 2 G

@[simp] theorem slotGauge_apply (q : ℕ) (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (x : ClockOperators.H q V) (j : Fin (q + 1)) :
    slotGauge q G x j = G j (x j) := rfl

@[simp] theorem slotGauge_symm_apply (q : ℕ) (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (x : ClockOperators.H q V) (j : Fin (q + 1)) :
    (slotGauge q G).symm x j = (G j).symm (x j) := rfl

/-- A slot gauge with identity at zero fixes the actual public injection. -/
theorem slotGauge_fixes_boundary (q : ℕ) (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (hG : G 0 = LinearIsometryEquiv.refl ℂ V) (v : V) :
    slotGauge q G (ClockOperators.boundary q v) = ClockOperators.boundary q v := by
  apply PiLp.ext
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · change G 0 v = v
    rw [hG]
    rfl
  · change G k.succ 0 = 0
    exact map_zero _

end Slots

section Distributed
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The canonical clock in slotwise unitary coordinates. -/
def distributedClock (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) : ClockOperators.H q V →L[ℂ] ClockOperators.H q V :=
  conjugate (slotGauge q G) (ClockOperators.clock O q hO hHerm)

/-- An internal link is exactly the ratio of successive slot gauges. -/
theorem distributedClock_succ (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) (x : ClockOperators.H q V) (j : Fin q) :
    distributedClock O q hO hHerm G x j.succ =
      G j.succ ((G j.castSucc).symm (x j.castSucc)) := rfl

/-- The return edge contains precisely the conjugated return operator. -/
theorem distributedClock_zero (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) (x : ClockOperators.H q V) :
    distributedClock O q hO hHerm G x 0 =
      G 0 (Complex.I • O ((G (Fin.last q)).symm (x (Fin.last q)))) := rfl

/-- Cumulative products of explicitly supplied unitary links. -/
def prefixGauge (L : ℕ → V ≃ₗᵢ[ℂ] V) : ℕ → V ≃ₗᵢ[ℂ] V
  | 0 => LinearIsometryEquiv.refl ℂ V
  | n + 1 => (prefixGauge L n).trans (L n)

omit [CompleteSpace V] in
/-- Prefix gauges start with the identity at the public boundary. -/
theorem prefixGauge_zero (L : ℕ → V ≃ₗᵢ[ℂ] V) :
    prefixGauge L 0 = LinearIsometryEquiv.refl ℂ V := rfl

/-- The gauge construction realizes every specified internal unitary link. -/
theorem prefix_distributedClock_succ (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (L : ℕ → V ≃ₗᵢ[ℂ] V) (x : ClockOperators.H q V) (j : Fin q) :
    distributedClock O q hO hHerm (fun j => prefixGauge L j.val) x j.succ =
      L j.val (x j.castSucc) := by
  rw [distributedClock_succ]
  change L j.val (prefixGauge L j.val ((prefixGauge L j.val).symm (x j.castSucc))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]

/-- If the link product implements the involution, the return edge is just phase `i`. -/
theorem prefix_distributedClock_zero (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (L : ℕ → V ≃ₗᵢ[ℂ] V) (hProduct : ∀ v, O v = prefixGauge L q v)
    (x : ClockOperators.H q V) :
    distributedClock O q hO hHerm (fun j => prefixGauge L j.val) x 0 =
      Complex.I • x (Fin.last q) := by
  rw [distributedClock_zero]
  change Complex.I • O ((prefixGauge L q).symm (x (Fin.last q))) = _
  rw [hProduct, LinearIsometryEquiv.apply_symm_apply]

/-- Distributing links preserves the isometry of the private clock step. -/
theorem distributedClock_adjoint_comp (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) :
    (distributedClock O q hO hHerm G)† ∘L distributedClock O q hO hHerm G = 1 :=
  conjugate_adjoint_comp (slotGauge q G) (ClockOperators.clock O q hO hHerm)
    (ClockOperators.clock_adjoint_comp O q hO hHerm)

variable [FiniteDimensional ℂ V]

/-- The genuine inverse for the distributed clock. -/
def distributedResolvent (O : V →ₗ[ℂ] V) (q : ℕ) (hO : ∀ v, O (O v) = v)
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) : ClockOperators.H q V →L[ℂ] ClockOperators.H q V :=
  conjugate (slotGauge q G) (ClockOperators.resolvent O q hO)

/-- The concrete distributed clock satisfies both resolvent inverse identities. -/
theorem distributedResolvent_inverse (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) :
    (1 - distributedClock O q hO hHerm G) ∘L distributedResolvent O q hO G = 1 ∧
    distributedResolvent O q hO G ∘L (1 - distributedClock O q hO hHerm G) = 1 := by
  simpa only [one_smul, distributedClock, distributedResolvent] using conjugate_resolvent_inverse (slotGauge q G)
    (ClockOperators.clock O q hO hHerm) (ClockOperators.resolvent O q hO) 1
    (by simpa only [one_smul] using ClockOperators.resolvent_right_inverse O q hO hHerm)
    (by simpa only [one_smul] using ClockOperators.resolvent_left_inverse O q hO hHerm)

/-- The distributed inverse retains the canonical clock-length norm bound. -/
theorem distributedResolvent_norm_le (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V) :
    ‖distributedResolvent O q hO G‖ ≤ ((q + 1 : ℕ) : ℝ) := by
  rw [distributedResolvent, conjugate_norm]
  exact ClockOperators.resolvent_norm_le O q hO hHerm

/-- The exact endpoint energy does not depend on how the unitary links are distributed. -/
theorem distributedResolvent_endpoint_energy (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (hHerm : ∀ v w, inner ℂ (O v) w = inner ℂ v (O w))
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (hG : G 0 = LinearIsometryEquiv.refl ℂ V) (v : V) :
    ‖(distributedResolvent O q hO G ∘L ClockOperators.boundary q) v‖ ^ 2 =
      ((q + 1 : ℕ) : ℝ) / 2 * ‖v‖ ^ 2 := by
  rw [distributedResolvent, conjugate_boundary_norm_apply (slotGauge q G)
    (ClockOperators.resolvent O q hO) (ClockOperators.boundary q)
    (slotGauge_fixes_boundary q G hG)]
  exact ClockOperators.resolvent_boundary_norm_sq O q hO hHerm v

/-- The public Cayley generator is unchanged by distributing the clock links. -/
theorem distributedResolvent_compression (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v)
    (G : Fin (q + 1) → V ≃ₗᵢ[ℂ] V)
    (hG : G 0 = LinearIsometryEquiv.refl ℂ V) :
    (ClockOperators.boundary q)† ∘L distributedResolvent O q hO G ∘L ClockOperators.boundary q =
      (2 : ℂ)⁻¹ • (1 + Complex.I • O.toContinuousLinearMap) := by
  rw [distributedResolvent, conjugate_boundary_compression (slotGauge q G)
    (ClockOperators.resolvent O q hO) (ClockOperators.boundary q)
    (slotGauge_fixes_boundary q G hG)]
  exact ClockOperators.resolvent_boundary_compression O q hO

end Distributed
end
end SparseHamiltonian.ClockGauge
