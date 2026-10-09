import GateEfficientBinaryODE.Operator

/-!
# The locator without coordinate exchanges

The released locator of the tagged construction (`ODETaggedLocators.locator`) follows the column
locator, in the transposed tag, by a fixed exchange of the two indices. A gate-level circuit
need not perform this exchange: with the fixed tag swap `tagSwap` (the exchange on the transposed
tag of both orientations),

* `swap_locator`: `tagSwap L = locS`, the locator that applies the row locator when the
  orientation and the tag agree and the column locator otherwise;
* `actS_eq`: `tagSwap A tagSwap = actS`, the edgewise Cayley action of `ODETaggedCayley` read in
  swapped coordinates (`actS` uses the tagged value of `swapTag e` on the edge `e`);
* `action_eq_locS`: the private operation of `ODEFixedTaggedMoments` is `locS† actS locS`, and
  `act4_eq_loc4` the same for the four sectors.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding (Data)
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-! ### The tag swap -/

/-- A tagged edge with the two indices of the transposed tag exchanged. -/
def swapTag : (n × n) ⊕ (n × n) → (n × n) ⊕ (n × n)
  | .inl e => .inl e
  | .inr e => .inr (e.2, e.1)

omit [Fintype n] [DecidableEq n] in
@[simp] theorem swapTag_swapTag (e : (n × n) ⊕ (n × n)) : swapTag (swapTag e) = e := by
  rcases e with e | e <;> rfl

/-- The index exchange of the transposed tag on the tagged space. -/
def tagSwapT : ODETaggedSupport.TaggedSpace n →L[ℂ] ODETaggedSupport.TaggedSpace n :=
  FixedLocatorConjugation.block 1 NativeHermitianOracle.coordinateSwap

omit [DecidableEq n] in
theorem tagSwapT_apply (w : ODETaggedSupport.TaggedSpace n) (e : (n × n) ⊕ (n × n)) :
    tagSwapT w e = w (swapTag e) := by
  rcases e with e | e <;> rfl

/-- The tag swap on both orientations. -/
def tagSwap : ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  dg (fun _ => tagSwapT)

omit [DecidableEq n] in
theorem tagSwap_apply (v : ODETaggedMoments.PrivateSpace n) (b : Bool) (e : (n × n) ⊕ (n × n)) :
    tagSwap v b e = v b (swapTag e) :=
  tagSwapT_apply _ e

omit [DecidableEq n] in
theorem tagSwap_mul_self : (tagSwap (n := n)) * tagSwap = 1 := by
  ext v b e
  simp only [mul_apply_eq_comp, tagSwap_apply, swapTag_swapTag]
  rfl

omit [DecidableEq n] in
theorem tagSwap_unitary : IsUnitary (tagSwap (n := n)) :=
  dg_unitary _ (fun _ => FixedLocatorConjugation.block_unitary _ _ isUnitary_one
    NativeHermitianOracle.coordinateSwap_unitary)

omit [DecidableEq n] in
theorem tagSwap_adjoint : (tagSwap (n := n))† = tagSwap := by
  have h1 : (tagSwap (n := n))† * tagSwap = 1 := by
    have := (tagSwap_unitary (n := n)).1
    rwa [star_eq_adjoint] at this
  calc (tagSwap (n := n))†
      = (tagSwap (n := n))† * (tagSwap * tagSwap) := by rw [tagSwap_mul_self, mul_one]
    _ = ((tagSwap (n := n))† * tagSwap) * tagSwap := by rw [mul_assoc]
    _ = tagSwap := by rw [h1, one_mul]

/-! ### The locator -/

/-- **The locator without coordinate exchange**: on orientation `o` and tag `t` it applies the
row locator when `o = t` and the column locator otherwise. -/
def locS (D : Data X n Z s) (x : X) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  dg (fun o => if o then FixedLocatorConjugation.block (D.columnOracle x) (D.rowOracle x)
    else FixedLocatorConjugation.block (D.rowOracle x) (D.columnOracle x))

omit [DecidableEq n] in
theorem coordinateSwap_comp_self :
    (NativeHermitianOracle.coordinateSwap : EuclideanSpace ℂ (n × n) →L[ℂ] _) ∘L
      NativeHermitianOracle.coordinateSwap = 1 := by
  ext v e
  rfl

theorem swap_locator (D : Data X n Z s) (x : X) :
    tagSwap * ODETaggedLocators.locator D x = locS D x := by
  unfold ODETaggedLocators.locator tagSwap locS
  rw [dg_mul]
  congr 1
  funext o
  cases o
  · simp only [Bool.false_eq_true, if_false, ODETaggedLocators.leftLocator, tagSwapT, mul_def,
      FixedLocatorConjugation.block_comp]
    rw [← comp_assoc, coordinateSwap_comp_self, one_def, id_comp, id_comp]
  · simp only [if_true, ODETaggedLocators.rightLocator, tagSwapT, mul_def,
      FixedLocatorConjugation.block_comp]
    rw [← comp_assoc, coordinateSwap_comp_self, one_def, id_comp, id_comp]

theorem locS_unitary (D : Data X n Z s) (x : X) : IsUnitary (locS D x) := by
  rw [← swap_locator]
  exact tagSwap_unitary.mul (ODETaggedLocators.locator_unitary D x)

/-! ### The edgewise action in swapped coordinates -/

/-- **The edgewise Cayley action in swapped coordinates**: on the tagged edge `e` the exact
Cayley gate of the tagged value of `swapTag e`. -/
def actS (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  ODETaggedCayley.lift (fun e =>
    ExactEdgeCayley.action (ODETaggedCayley.scaledEntries M K s ρ γ (swapTag e)))

omit [DecidableEq n] in
theorem actS_eq (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) :
    tagSwap * ODETaggedCayley.action M K s ρ γ * tagSwap = actS M K s ρ γ := by
  ext v b e
  simp only [mul_apply_eq_comp, tagSwap_apply, ODETaggedCayley.action_apply, actS,
    ODETaggedCayley.lift_apply]
  have h : ODETaggedCayley.regroup (tagSwap v) (swapTag e) = ODETaggedCayley.regroup v e := by
    apply PiLp.ext
    intro b'
    simp only [ODETaggedCayley.regroup_apply, tagSwap_apply, swapTag_swapTag]
  rw [h]

omit [DecidableEq n] in
theorem actS_unitary (M K : Matrix n n ℂ) (s : ℕ) (ρ γ : ℝ) : IsUnitary (actS M K s ρ γ) :=
  ODETaggedCayley.lift_unitary _ (fun _ => ExactEdgeCayley.action_unitary _)

theorem action_eq_locS (D : Data X n Z s) (x : X) (K : Matrix n n ℂ) (ρ γ : ℝ) :
    ODEFixedTaggedMoments.action D x K ρ γ =
      (locS D x)† * actS (D.matrix x) K s ρ γ * locS D x := by
  rw [← swap_locator, ← actS_eq, ODEFixedTaggedMoments.action, UnitaryCayleyTransport.conjugate,
    star_eq_adjoint]
  have h1 : (tagSwap * ODETaggedLocators.locator D x)† =
      (ODETaggedLocators.locator D x)† * tagSwap := by
    rw [mul_def, adjoint_comp, tagSwap_adjoint]
    rfl
  rw [h1]
  calc (ODETaggedLocators.locator D x)† * ODETaggedCayley.action (D.matrix x) K s ρ γ *
        ODETaggedLocators.locator D x
      = (ODETaggedLocators.locator D x)† * ((tagSwap * tagSwap) *
          ODETaggedCayley.action (D.matrix x) K s ρ γ * (tagSwap * tagSwap)) *
          ODETaggedLocators.locator D x := by rw [tagSwap_mul_self, one_mul, mul_one]
    _ = (ODETaggedLocators.locator D x)† * tagSwap *
          (tagSwap * ODETaggedCayley.action (D.matrix x) K s ρ γ * tagSwap) *
          (tagSwap * ODETaggedLocators.locator D x) := by simp only [mul_assoc]

/-! ### Four sectors -/

/-- The locator on the four sectors (the same in both parts). -/
def loc4 (D : Data X n Z s) (x : X) : Space4 n →L[ℂ] Space4 n := dg (fun _ => locS D x)

/-- The edgewise action of the four sectors in swapped coordinates. -/
def actS4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) : Space4 n →L[ℂ] Space4 n :=
  dg (fun p => actS (D.matrix x) (partK (D.matrix x) k p) s ρ (Real.sqrt 2 * γ))

theorem loc4_unitary (D : Data X n Z s) (x : X) : IsUnitary (loc4 D x) :=
  dg_unitary _ (fun _ => locS_unitary D x)

theorem actS4_unitary (D : Data X n Z s) (x : X) (k ρ γ : ℝ) : IsUnitary (actS4 D x k ρ γ) :=
  dg_unitary _ (fun _ => actS_unitary _ _ _ _ _)

/-- **The four-sector action is `loc4† actS4 loc4`.** -/
theorem act4_eq_loc4 (D : Data X n Z s) (x : X) (k ρ γ : ℝ) :
    act4 D x k ρ γ = (loc4 D x)† * actS4 D x k ρ γ * loc4 D x := by
  have h : (loc4 D x)† * actS4 D x k ρ γ * loc4 D x = dg (fun p => (locS D x)† *
      actS (D.matrix x) (partK (D.matrix x) k p) s ρ (Real.sqrt 2 * γ) * locS D x) := by
    rw [loc4, actS4, dg_adjoint, dg_mul, dg_mul]
  rw [h, act4]
  exact congrArg dg (funext fun p => action_eq_locS D x _ ρ _)

end

end SparseHamiltonian.GateBinaryODE
