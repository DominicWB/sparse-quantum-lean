import SparseODE.ODETaggedMoments

/-!
# Exact Cayley action on the full tagged workspace

A fixed exchange of the orientation and edge registers reduces the Hermitian
dilation of any tagged diagonal to the verified two-dimensional Cayley gate.
The explicit inverse and its two identities hold on every workspace vector,
including unused or unmatched padding.  This is an operator construction;
the native query implementation is a separate obligation.
-/

namespace SparseHamiltonian.ODETaggedCayley

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct ComplexConjugate
set_option maxHeartbeats 1000000

section Generic
variable {ι : Type*} [Fintype ι]

/-- The orientation register precedes the entire edge address. -/
abbrev Doubled (ι : Type*) [Fintype ι] :=
  HermitianDilation.Double (EuclideanSpace ℂ ι)

/-- The address precedes its two-dimensional orientation register. -/
abbrev LocalSpace (ι : Type*) :=
  PiLp 2 (fun _ : ι => ExactEdgeCayley.Qubit)

/-- A full fixed register permutation, with no discarded subspace. -/
def regroup : Doubled ι ≃ₗᵢ[ℂ] LocalSpace ι where
  toLinearEquiv :=
    { toFun := fun v => WithLp.toLp 2 (fun e =>
        WithLp.toLp 2 (fun b : Bool => v b e))
      invFun := fun v => WithLp.toLp 2 (fun b : Bool =>
        WithLp.toLp 2 (fun e => v e b))
      left_inv := by intro v; ext b e; rfl
      right_inv := by intro v; ext e b; rfl
      map_add' := by intro v w; ext e b; rfl
      map_smul' := by intro z v; ext e b; rfl }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_comm

@[simp] theorem regroup_apply (v : Doubled ι) (e : ι) (b : Bool) :
    regroup v e b = v b e := rfl

@[simp] theorem regroup_symm_apply (v : LocalSpace ι) (b : Bool) (e : ι) :
    regroup.symm v b e = v e b := rfl

/-- Assemble the local gates in the orientation-first workspace. -/
def lift (G : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    Doubled ι →L[ℂ] Doubled ι :=
  regroup.symm.conjStarAlgEquiv (WeightedClock.diagonal G)

@[simp] theorem lift_apply
    (G : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (v : Doubled ι) (b : Bool) (e : ι) :
    lift G v b e = G e (regroup v e) b := rfl

@[simp] theorem regroup_lift
    (G : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (v : Doubled ι) :
    regroup (lift G v) = WeightedClock.diagonal G (regroup v) := by
  ext e b
  rfl

@[simp] theorem lift_one :
    lift (fun _ : ι => (1 : ExactEdgeCayley.Qubit →L[ℂ] _)) = 1 := by
  ext v b e
  rfl

theorem lift_add
    (G F : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => G e + F e) = lift G + lift F := by
  ext v b e
  rfl

theorem lift_sub
    (G F : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => G e - F e) = lift G - lift F := by
  ext v b e
  rfl

theorem lift_smul (z : ℂ)
    (G : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => z • G e) = z • lift G := by
  ext v b e
  rfl

theorem lift_mul
    (G F : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => G e * F e) = lift G * lift F := by
  apply ContinuousLinearMap.ext
  intro v
  apply regroup.injective
  apply PiLp.ext
  intro e
  simp only [mul_apply_eq_comp, regroup_lift, WeightedClock.diagonal_apply]

/-- Full-space unitarity follows from the fixed equivalence and local gates. -/
theorem lift_unitary
    (G : ι → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (hG : ∀ e, IsUnitary (G e)) : IsUnitary (lift G) :=
  (CoherentQuerySchedule.diagonal_unitary G hG).transport regroup.symm

/-- The local generator is exactly the Hermitian dilation of a diagonal. -/
theorem lift_generator (d : ι → ℂ) :
    lift (fun e => ExactEdgeCayley.generator (d e)) =
      HermitianDilation.dilation (RelativeAmplitudeError.complexDiagonal d) := by
  ext v b e
  cases b
  · simp only [lift_apply, ExactEdgeCayley.generator_false, regroup_apply,
      HermitianDilation.dilation_apply_false,
      RelativeAmplitudeError.complexDiagonal_apply]
  · simp only [lift_apply, ExactEdgeCayley.generator_true, regroup_apply,
      HermitianDilation.dilation_apply_true,
      RelativeAmplitudeError.complexDiagonal_adjoint,
      RelativeAmplitudeError.complexDiagonal_apply, Complex.star_def]

/-- Real scaling acts on both conjugate off-diagonal entries correctly. -/
theorem scaled_dilation_eq_lift (d : ι → ℂ) (a : ℝ) :
    (a : ℂ) • HermitianDilation.dilation
        (RelativeAmplitudeError.complexDiagonal d) =
      lift (fun e => ExactEdgeCayley.generator ((a : ℂ) * d e)) := by
  rw [lift_generator]
  ext v b e
  cases b <;>
    simp [HermitianDilation.dilation_apply_false,
      HermitianDilation.dilation_apply_true,
      RelativeAmplitudeError.complexDiagonal_adjoint, mul_assoc]

/-- A constructed inverse for the negative-imaginary Cayley denominator. -/
def diagonalInverse (d : ι → ℂ) : Doubled ι →L[ℂ] Doubled ι :=
  lift (fun e => ExactEdgeCayley.inverse (d e))

theorem diagonalInverse_right (d : ι → ℂ) :
    (HermitianDilation.dilation (RelativeAmplitudeError.complexDiagonal d) -
      Complex.I • (1 : Doubled ι →L[ℂ] Doubled ι)) * diagonalInverse d = 1 := by
  rw [← lift_generator, diagonalInverse, ← lift_one (ι := ι), ← lift_smul,
    ← lift_sub, ← lift_mul]
  simp only [ExactEdgeCayley.inverse_right, lift_one]

theorem diagonalInverse_left (d : ι → ℂ) :
    diagonalInverse d *
      (HermitianDilation.dilation (RelativeAmplitudeError.complexDiagonal d) -
        Complex.I • (1 : Doubled ι →L[ℂ] Doubled ι)) = 1 := by
  rw [← lift_generator, diagonalInverse, ← lift_one (ι := ι), ← lift_smul,
    ← lift_sub, ← lift_mul]
  simp only [ExactEdgeCayley.inverse_left, lift_one]

/-- The full diagonal Cayley action is a direct sum of rational qubit gates. -/
def diagonalAction (d : ι → ℂ) : Doubled ι →L[ℂ] Doubled ι :=
  lift (fun e => ExactEdgeCayley.action (d e))

theorem diagonalAction_unitary (d : ι → ℂ) : IsUnitary (diagonalAction d) :=
  lift_unitary _ (fun e => ExactEdgeCayley.action_unitary (d e))

theorem diagonalAction_eq_cayley (d : ι → ℂ) :
    diagonalAction d = ImprovedCayleyMoments.cayleyAction
      (HermitianDilation.dilation (RelativeAmplitudeError.complexDiagonal d))
        (diagonalInverse d) := by
  rw [diagonalAction, ImprovedCayleyMoments.cayleyAction,
    ← lift_generator, diagonalInverse]
  simp only [ExactEdgeCayley.action, ImprovedCayleyMoments.cayleyAction,
    lift_mul, lift_add, lift_smul, lift_one]

/-- An unused tagged address receives phase minus one in both orientations. -/
theorem diagonalAction_zero_apply (d : ι → ℂ) (e : ι) (he : d e = 0)
    (v : Doubled ι) (b : Bool) : diagonalAction d v b e = -(v b e) := by
  simp [diagonalAction, lift_apply, he]

end Generic

section Tagged
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Explicit diagonal entries in the two support-tag sectors. -/
def entries (M K : Matrix n n ℂ) : (n × n) ⊕ (n × n) → ℂ :=
  Sum.elim (fun e => ODETaggedSupport.tagZero M K e.1 e.2)
    (fun e => ODETaggedSupport.tagOne M K e.1 e.2)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem entries_inl (M K : Matrix n n ℂ) (i j : n) :
    entries M K (.inl (i, j)) = ODETaggedSupport.tagZero M K i j := rfl

omit [Fintype n] [DecidableEq n] in
@[simp] theorem entries_inr (M K : Matrix n n ℂ) (i j : n) :
    entries M K (.inr (i, j)) = ODETaggedSupport.tagOne M K i j := rfl

/-- All scale parameters occur only in the local, query-free rational gate. -/
def scaledEntries (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    (n × n) ⊕ (n × n) → ℂ :=
  fun e => ((γ * (Real.sqrt (2 * (s : ℝ)) / ρ) : ℝ) : ℂ) * entries M K e

omit [DecidableEq n] in
/-- The analytic tagged generator has exactly these entrywise qubit blocks. -/
theorem scaled_generator_eq_lift (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    CayleyClockInterface.scaled (ODETaggedMoments.generator M K s ρ) γ =
      lift (fun e => ExactEdgeCayley.generator (scaledEntries M K s ρ γ e)) := by
  unfold CayleyClockInterface.scaled ODETaggedMoments.generator
  rw [smul_smul, ← Complex.ofReal_mul]
  exact scaled_dilation_eq_lift (entries M K) (γ * (Real.sqrt (2 * (s : ℝ)) / ρ))

/-- The explicit tagged denominator inverse includes all padded addresses. -/
def inverse (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  diagonalInverse (scaledEntries M K s ρ γ)

omit [DecidableEq n] in
theorem inverse_right (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    (CayleyClockInterface.scaled (ODETaggedMoments.generator M K s ρ) γ -
      Complex.I • (1 : ODETaggedMoments.PrivateSpace n →L[ℂ] _)) *
        inverse M K s ρ γ = 1 := by
  rw [scaled_generator_eq_lift, lift_generator]
  exact diagonalInverse_right (scaledEntries M K s ρ γ)

omit [DecidableEq n] in
theorem inverse_left (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    inverse M K s ρ γ *
      (CayleyClockInterface.scaled (ODETaggedMoments.generator M K s ρ) γ -
        Complex.I • (1 : ODETaggedMoments.PrivateSpace n →L[ℂ] _)) = 1 := by
  rw [scaled_generator_eq_lift, lift_generator]
  exact diagonalInverse_left (scaledEntries M K s ρ γ)

/-- The actual logical tagged action, before native-oracle compilation. -/
def action (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  diagonalAction (scaledEntries M K s ρ γ)

omit [DecidableEq n] in
@[simp] theorem action_apply (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ)
    (v : ODETaggedMoments.PrivateSpace n) (b : Bool)
    (e : (n × n) ⊕ (n × n)) :
    action M K s ρ γ v b e =
      ExactEdgeCayley.action (scaledEntries M K s ρ γ e) (regroup v e) b := rfl

omit [DecidableEq n] in
/-- This is the address-diagonal action used by a clean paired-value query. -/
theorem regroup_action (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ)
    (v : ODETaggedMoments.PrivateSpace n) :
    regroup (action M K s ρ γ v) =
      WeightedClock.diagonal (fun e =>
        ExactEdgeCayley.action (scaledEntries M K s ρ γ e)) (regroup v) :=
  regroup_lift _ v

omit [DecidableEq n] in
theorem action_unitary (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    IsUnitary (action M K s ρ γ) :=
  diagonalAction_unitary (scaledEntries M K s ρ γ)

omit [DecidableEq n] in
theorem action_eq_cayley (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    action M K s ρ γ = ImprovedCayleyMoments.cayleyAction
      (CayleyClockInterface.scaled (ODETaggedMoments.generator M K s ρ) γ)
        (inverse M K s ρ γ) := by
  rw [scaled_generator_eq_lift, lift_generator]
  exact diagonalAction_eq_cayley (scaledEntries M K s ρ γ)

omit [DecidableEq n] in
/-- Both resolvent identities hold for the constructed full-space action. -/
theorem one_sub_action_mul_resolvent (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    (1 - action M K s ρ γ) * ImprovedCayleyMoments.resolventAtOne
      (CayleyClockInterface.scaled (ODETaggedMoments.generator M K s ρ) γ) = 1 := by
  rw [action_eq_cayley]
  exact ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne _ _
    (inverse_right M K s ρ γ) (inverse_left M K s ρ γ)

omit [DecidableEq n] in
theorem resolvent_mul_one_sub_action (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    ImprovedCayleyMoments.resolventAtOne
      (CayleyClockInterface.scaled (ODETaggedMoments.generator M K s ρ) γ) *
        (1 - action M K s ρ γ) = 1 := by
  rw [action_eq_cayley]
  exact ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction _ _
    (inverse_right M K s ρ γ)

end Tagged
end
end SparseHamiltonian.ODETaggedCayley
