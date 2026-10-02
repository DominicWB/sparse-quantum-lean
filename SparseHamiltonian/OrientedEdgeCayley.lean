import SparseHamiltonian.CayleyClockInterface

/-!
# Exact Cayley inverse on the full oriented sparse edge space

The explicit two-dimensional inverse is assembled on every edge, including
unused and padded edges.  A fixed regrouping isometry identifies the two
orientation copies with the address-and-qubit layout of the value oracle.
Thus the inverse hypotheses in the analytic clock interface are discharged
by actual operators, and the exact edge action inherits the proved two-query
implementation with clean value scratch.
-/

namespace SparseHamiltonian.OrientedEdgeCayley

noncomputable section
open ContinuousLinearMap SparseEdgeMoments
open scoped BigOperators InnerProduct ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Fixed relabelling from two orientation copies to one qubit at each edge. -/
def regroup : OrientedSpace n →ₗᵢ[ℂ] ExactEdgeValueQuery.LogicalSpace n where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun e =>
        WithLp.toLp 2 (fun b : Bool => if b then v (.inr e) else v (.inl e)))
      map_add' := by
        intro v w
        ext e b
        cases b <;> simp
      map_smul' := by
        intro z v
        ext e b
        cases b <;> simp }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type,
      Finset.sum_add_distrib, add_comm]

omit [DecidableEq n] in
@[simp] theorem regroup_false (v : OrientedSpace n) (e : n × n) :
    regroup v e false = v (.inl e) := rfl

omit [DecidableEq n] in
@[simp] theorem regroup_true (v : OrientedSpace n) (e : n × n) :
    regroup v e true = v (.inr e) := rfl

/-- The inverse coordinate permutation is defined on the entire Hilbert space. -/
def unregroup : ExactEdgeValueQuery.LogicalSpace n →L[ℂ] OrientedSpace n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2
        (Sum.elim (fun e => v e false) (fun e => v e true))
      map_add' := by intro v w; ext e; cases e <;> simp
      map_smul' := by intro z v; ext e; cases e <;> simp }

omit [DecidableEq n] in
@[simp] theorem unregroup_inl (v : ExactEdgeValueQuery.LogicalSpace n) (e : n × n) :
    unregroup v (.inl e) = v e false := rfl

omit [DecidableEq n] in
@[simp] theorem unregroup_inr (v : ExactEdgeValueQuery.LogicalSpace n) (e : n × n) :
    unregroup v (.inr e) = v e true := rfl

omit [DecidableEq n] in
@[simp] theorem unregroup_regroup (v : OrientedSpace n) : unregroup (regroup v) = v := by
  ext e
  cases e <;> rfl

omit [DecidableEq n] in
@[simp] theorem regroup_unregroup (v : ExactEdgeValueQuery.LogicalSpace n) :
    regroup (unregroup v) = v := by
  ext e b
  cases b <;> rfl

omit [DecidableEq n] in
/-- The regrouping has no hidden projection or unused subspace. -/
theorem regroup_surjective : Function.Surjective (regroup (n := n)) :=
  fun v => ⟨unregroup v, regroup_unregroup v⟩

/-- Direct sum of exact qubit operators in the sparse oriented-space layout. -/
def lift (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    OrientedSpace n →L[ℂ] OrientedSpace n :=
  unregroup ∘L WeightedClock.diagonal G ∘L regroup.toContinuousLinearMap

omit [DecidableEq n] in
@[simp] theorem lift_inl
    (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (v : OrientedSpace n) (e : n × n) :
    lift G v (.inl e) = G e (regroup v e) false := rfl

omit [DecidableEq n] in
@[simp] theorem lift_inr
    (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (v : OrientedSpace n) (e : n × n) :
    lift G v (.inr e) = G e (regroup v e) true := rfl

omit [DecidableEq n] in
@[simp] theorem regroup_lift
    (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit)
    (v : OrientedSpace n) :
    regroup (lift G v) = WeightedClock.diagonal G (regroup v) := by
  ext e b
  cases b <;> rfl

omit [DecidableEq n] in
@[simp] theorem lift_one :
    lift (fun _ : n × n => (1 : ExactEdgeCayley.Qubit →L[ℂ] _)) = 1 := by
  ext v e
  cases e <;> rfl

omit [DecidableEq n] in
theorem lift_add
    (G F : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => G e + F e) = lift G + lift F := by
  ext v e
  cases e <;> rfl

omit [DecidableEq n] in
theorem lift_sub
    (G F : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => G e - F e) = lift G - lift F := by
  ext v e
  cases e <;> rfl

omit [DecidableEq n] in
theorem lift_smul (z : ℂ)
    (G : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => z • G e) = z • lift G := by
  ext v e
  cases e <;> rfl

omit [DecidableEq n] in
/-- Coordinate lifting preserves multiplication, hence both inverse identities. -/
theorem lift_mul
    (G F : n × n → ExactEdgeCayley.Qubit →L[ℂ] ExactEdgeCayley.Qubit) :
    lift (fun e => G e * F e) = lift G * lift F := by
  apply ContinuousLinearMap.ext
  intro v
  apply regroup.injective
  apply PiLp.ext
  intro e
  simp only [mul_apply_eq_comp, regroup_lift, WeightedClock.diagonal_apply]

omit [DecidableEq n] in
/-- The lifted edge generator is the concrete incidence-space generator. -/
theorem lift_generator (H : Matrix n n ℂ) :
    lift (fun e : n × n => ExactEdgeCayley.generator (H e.1 e.2)) =
      SparseEdgeMoments.entryGenerator H := by
  ext v e
  cases e with
  | inl e => simp only [lift_inl, ExactEdgeCayley.generator_false,
      regroup_true, SparseEdgeMoments.entryGenerator_inl]
  | inr e => simp only [lift_inr, ExactEdgeCayley.generator_true,
      regroup_false, SparseEdgeMoments.entryGenerator_inr, Complex.star_def]

omit [DecidableEq n] in
/-- Real rescaling of the sparse generator is entrywise rescaling of its edges. -/
theorem scaled_eq_lift (H : Matrix n n ℂ) (s : ℕ) (γ : ℝ) :
    CayleyClockInterface.scaled (SparseEdgeMoments.generator H s) γ =
      lift (fun e : n × n => ExactEdgeCayley.generator
        (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H e.1 e.2)) := by
  rw [lift_generator (fun i j => (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H i j))]
  ext v e
  cases e with
  | inl e =>
    simp [CayleyClockInterface.scaled, SparseEdgeMoments.generator,
      SparseEdgeMoments.entryGenerator_inl, Complex.ofReal_mul, mul_assoc]
  | inr e =>
    simp [CayleyClockInterface.scaled, SparseEdgeMoments.generator,
      SparseEdgeMoments.entryGenerator_inr, Complex.ofReal_mul, mul_assoc]

/-- Explicit full inverse; no nonzero-entry or spectral-gap premise is needed. -/
def inverse (H : Matrix n n ℂ) (s : ℕ) (γ : ℝ) :
    OrientedSpace n →L[ℂ] OrientedSpace n :=
  lift (fun e => ExactEdgeCayley.inverse
    (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H e.1 e.2))

omit [DecidableEq n] in
/-- The actual denominator has a right inverse on the entire edge workspace. -/
theorem inverse_right (H : Matrix n n ℂ) (s : ℕ) (γ : ℝ) :
    (CayleyClockInterface.scaled (SparseEdgeMoments.generator H s) γ -
      Complex.I • (1 : OrientedSpace n →L[ℂ] OrientedSpace n)) *
        inverse H s γ = 1 := by
  rw [scaled_eq_lift, inverse, ← lift_one (n := n), ← lift_smul, ← lift_sub,
    ← lift_mul]
  simp only [ExactEdgeCayley.inverse_right, lift_one]

omit [DecidableEq n] in
/-- The same concrete inverse satisfies the left identity. -/
theorem inverse_left (H : Matrix n n ℂ) (s : ℕ) (γ : ℝ) :
    inverse H s γ *
      (CayleyClockInterface.scaled (SparseEdgeMoments.generator H s) γ -
        Complex.I • (1 : OrientedSpace n →L[ℂ] OrientedSpace n)) = 1 := by
  rw [scaled_eq_lift, inverse, ← lift_one (n := n), ← lift_smul, ← lift_sub,
    ← lift_mul]
  simp only [ExactEdgeCayley.inverse_left, lift_one]

/-- The sparse edge Cayley action, assembled from exact local gates. -/
def action (H : Matrix n n ℂ) (s : ℕ) (γ : ℝ) :
    OrientedSpace n →L[ℂ] OrientedSpace n :=
  lift (fun e => ExactEdgeCayley.action
    (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H e.1 e.2))

omit [DecidableEq n] in
/-- This action is exactly the Cayley action required by the analytic theorem. -/
theorem action_eq_cayley (H : Matrix n n ℂ) (s : ℕ) (γ : ℝ) :
    action H s γ = ImprovedCayleyMoments.cayleyAction
      (CayleyClockInterface.scaled (SparseEdgeMoments.generator H s) γ)
        (inverse H s γ) := by
  rw [action, ImprovedCayleyMoments.cayleyAction, scaled_eq_lift, inverse]
  simp only [ExactEdgeCayley.action, ImprovedCayleyMoments.cayleyAction,
    lift_mul, lift_add, lift_smul, lift_one]

section NativeValue

variable {X Z : Type*} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Fixed orientation regrouping followed by zero value-scratch initialization. -/
def clean : OrientedSpace n →ₗᵢ[ℂ] ExactEdgeValueQuery.Space n Z :=
  (ExactEdgeValueQuery.clean (n := n) (Z := Z)).comp regroup

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The logical edge direct sum and oriented Cayley action coincide exactly. -/
theorem logical_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) :
    ExactEdgeValueQuery.logical D (γ * Real.sqrt (s : ℝ)) x ∘L
        regroup.toContinuousLinearMap =
      regroup.toContinuousLinearMap ∘L action (D.matrix x) s γ := by
  ext v e b
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    action, regroup_lift, ExactEdgeValueQuery.logical_apply,
    WeightedClock.diagonal_apply]

/-- Two ordinary value queries implement the full Cayley action and restore scratch. -/
theorem program_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (γ : ℝ) (x : X) :
    (ExactEdgeValueQuery.program D (γ * Real.sqrt (s : ℝ))).eval x ∘L
        (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L action (D.matrix x) s γ := by
  have h := congrArg
    (fun F : ExactEdgeValueQuery.LogicalSpace n →L[ℂ] ExactEdgeValueQuery.Space n Z =>
      F ∘L regroup.toContinuousLinearMap)
    (ExactEdgeValueQuery.program_intertwines D (γ * Real.sqrt (s : ℝ)) x)
  have hclean : (clean (n := n) (Z := Z)).toContinuousLinearMap =
      ExactEdgeValueQuery.clean.toContinuousLinearMap ∘L regroup.toContinuousLinearMap := rfl
  rw [hclean]
  simpa only [comp_assoc, logical_intertwines D γ x] using h

/-- Concrete implementation certificate for the full oriented edge action. -/
theorem implementsOn (D : NativeSparseBlockEncoding.Data X n Z s) (γ : ℝ) :
    EncodedOracle.ImplementsOn (ExactEdgeValueQuery.oracle D)
      (fun x => action (D.matrix x) s γ)
      (clean (n := n) (Z := Z)).toContinuousLinearMap 2 :=
  ⟨ExactEdgeValueQuery.program D (γ * Real.sqrt (s : ℝ)),
    program_intertwines D γ, by rw [ExactEdgeValueQuery.program_count]⟩

end NativeValue
end
end SparseHamiltonian.OrientedEdgeCayley
