import GateEfficientHamiltonian.GatePrefixCircuit
/-!
# Exact inverse of the clean prefix circuit

The inverse is the reversed elementary gate list. Prefix Boolean gates are
their own inverses, and each single-controlled matrix is replaced by its
conjugate transpose. The two inverse identities are proved on the entire
workspace, not only on clean inputs. Gate counts are unchanged.
-/

namespace SparseHamiltonian.GatePrefixCircuit

noncomputable section
open scoped BigOperators

variable {w : ℕ}

/-- Elementary inverse: no controlled opaque operation is introduced. -/
def Gate.inverse : Gate w → Gate w
  | .prefixBit j => .prefixBit j
  | .rotate j a => .rotate j (Matrix.conjTranspose a)

@[simp] theorem Gate.inverse_inverse (g : Gate w) : g.inverse.inverse = g := by
  cases g with
  | prefixBit j => rfl
  | rotate j a => simp [Gate.inverse, Matrix.conjTranspose_conjTranspose]

theorem Gate.inverse_valid (g : Gate w) (hg : g.Valid) : g.inverse.Valid := by
  cases g with
  | prefixBit j => trivial
  | rotate j a =>
      change a.IsUnitary at hg
      change Coefficients.IsUnitary (Matrix.conjTranspose a)
      constructor
      · simpa only [Matrix.conjTranspose_conjTranspose] using hg.2
      · simpa only [Matrix.conjTranspose_conjTranspose] using hg.1

@[simp] theorem Gate.inverse_positiveCost (g : Gate w) :
    g.inverse.positiveCost = g.positiveCost := by
  cases g <;> rfl

/-- Exact composition of controlled two-by-two matrices. The control flag
is unchanged, so the matrix product is also the product on disabled states. -/
theorem rotate_comp (j : Fin w) (a b : Coefficients) :
    (Gate.eval (.rotate j a)).comp (Gate.eval (.rotate j b)) =
      Gate.eval (.rotate j ((a : Matrix Bool Bool ℂ) * (b : Matrix Bool Bool ℂ))) := by
  classical
  apply Finsupp.lhom_ext
  intro z c
  simp only [LinearMap.comp_apply, Gate.eval,
    Finsupp.linearCombination_single, map_smul]
  congr 1
  cases hz : z.flags j
  · simp [rotateBasis, hz, Finsupp.linearCombination_single]
  · simp only [rotateBasis, hz, if_true, Fintype.sum_bool,
      map_add, map_smul, Finsupp.linearCombination_single, 
      Function.update_self, Function.update_idem, Matrix.mul_apply,
      Fintype.sum_bool, smul_add, add_smul, smul_smul]
    module

theorem rotate_identity (j : Fin w) :
    Gate.eval (.rotate j (1 : Matrix Bool Bool ℂ)) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro z c
  simp only [Gate.eval, Finsupp.linearCombination_single, LinearMap.id_apply]
  have h : rotateBasis j (1 : Matrix Bool Bool ℂ) z = Finsupp.single z 1 := by
    unfold rotateBasis
    split
    · simp [Matrix.one_apply]
    · rfl
  rw [h]
  simp

/-- The Boolean prefix gate is a permutation whose inverse is itself. -/
theorem prefix_comp_self (j : Fin w) :
    (Gate.eval (.prefixBit j)).comp (Gate.eval (.prefixBit j)) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro z c
  simp [Gate.eval, LinearMap.comp_apply, togglePrefix_involutive j z]

theorem Gate.inverse_comp (g : Gate w) (hg : g.Valid) :
    g.inverse.eval.comp g.eval = LinearMap.id := by
  cases g with
  | prefixBit j => exact prefix_comp_self j
  | rotate j a =>
      change a.IsUnitary at hg
      change (Gate.eval (.rotate j (Matrix.conjTranspose a))).comp
        (Gate.eval (.rotate j a)) = LinearMap.id
      rw [rotate_comp, hg.1, rotate_identity]

theorem Gate.comp_inverse (g : Gate w) (hg : g.Valid) :
    g.eval.comp g.inverse.eval = LinearMap.id := by
  cases g with
  | prefixBit j => exact prefix_comp_self j
  | rotate j a =>
      change a.IsUnitary at hg
      change (Gate.eval (.rotate j a)).comp
        (Gate.eval (.rotate j (Matrix.conjTranspose a))) = LinearMap.id
      rw [rotate_comp, hg.2, rotate_identity]

end
end SparseHamiltonian.GatePrefixCircuit

namespace SparseHamiltonian.GatePrefixInverse

noncomputable section
open GatePrefixCircuit
open scoped BigOperators
open scoped BigOperators

variable {w : ℕ}

/-- Reverse the real gate sequence and invert each actual elementary gate. -/
def inverse (gs : List (Gate w)) : List (Gate w) := gs.reverse.map Gate.inverse

@[simp] theorem inverse_nil : inverse ([] : List (Gate w)) = [] := rfl

@[simp] theorem inverse_cons (g : Gate w) (gs : List (Gate w)) :
    inverse (g :: gs) = inverse gs ++ [g.inverse] := by
  simp [inverse]

theorem inverse_valid (gs : List (Gate w))
    (hgs : ∀ g ∈ gs, g.Valid) : ∀ g ∈ inverse gs, g.Valid := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  exact h.inverse_valid (hgs h (List.mem_reverse.mp hh))

@[simp] theorem inverse_length (gs : List (Gate w)) :
    (inverse gs).length = gs.length := by
  simp [inverse]

@[simp] theorem inverse_positiveCost (gs : List (Gate w)) :
    positiveCost (inverse gs) = positiveCost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [inverse_cons, positiveCost_append, ih]
      simp [positiveCost, Gate.inverse_positiveCost]; omega

/-- The implemented inverse undoes the entire circuit on every workspace
state, including states whose ancilla flags are not initially clean. -/
theorem run_inverse_comp (gs : List (Gate w))
    (hgs : ∀ g ∈ gs, g.Valid) :
    (run (inverse gs)).comp (run gs) = LinearMap.id := by
  revert hgs
  induction gs with
  | nil => intro _; rfl
  | cons g gs ih =>
      intro hgs
      have hg := hgs g List.mem_cons_self
      have ht : ∀ h ∈ gs, h.Valid := fun h hh => hgs h (List.mem_cons_of_mem g hh)
      have hi := ih ht
      rw [inverse_cons, run_append]
      apply LinearMap.ext
      intro v
      simp only [run, LinearMap.comp_apply, LinearMap.id_apply]
      have hv := congrArg (fun A : State w →ₗ[ℂ] State w => A (g.eval v)) hi
      change run (inverse gs) (run gs (g.eval v)) = g.eval v at hv
      rw [hv]
      exact congrArg (fun A : State w →ₗ[ℂ] State w => A v) (g.inverse_comp hg)

theorem run_comp_inverse (gs : List (Gate w))
    (hgs : ∀ g ∈ gs, g.Valid) :
    (run gs).comp (run (inverse gs)) = LinearMap.id := by
  revert hgs
  induction gs with
  | nil => intro _; rfl
  | cons g gs ih =>
      intro hgs
      have hg := hgs g List.mem_cons_self
      have ht : ∀ h ∈ gs, h.Valid := fun h hh => hgs h (List.mem_cons_of_mem g hh)
      have hi := ih ht
      rw [inverse_cons, run_append]
      apply LinearMap.ext
      intro v
      simp only [run, LinearMap.comp_apply, LinearMap.id_apply]
      have hv := congrArg (fun A : State w →ₗ[ℂ] State w =>
        A (run (inverse gs) v)) (g.comp_inverse hg)
      change g.eval (g.inverse.eval (run (inverse gs) v)) = run (inverse gs) v at hv
      rw [hv]
      exact congrArg (fun A : State w →ₗ[ℂ] State w => A v) hi

/-- Exact reversal of the clean prefix circuit. This is a concrete gate
list, not a new free inverse-frame primitive. -/
def circuit (a : Fin w → Coefficients) : List (Gate w) :=
  inverse (GatePrefixCircuit.circuit a)

theorem circuit_valid (a : Fin w → Coefficients)
    (ha : ∀ j, (a j).IsUnitary) : ∀ g ∈ circuit a, g.Valid :=
  inverse_valid _ (GatePrefixCircuit.circuit_valid a ha)

theorem circuit_length (a : Fin w → Coefficients) :
    (circuit a).length = 3 * w := by
  rw [circuit, inverse_length, GatePrefixCircuit.circuit_length]

theorem circuit_positiveCost (a : Fin w → Coefficients) :
    positiveCost (circuit a) = 7 * w := by
  rw [circuit, inverse_positiveCost, GatePrefixCircuit.positive_control_gate_bound]

/-- Undo the complete forward circuit, on the full workspace. -/
theorem circuit_comp_forward (a : Fin w → Coefficients)
    (ha : ∀ j, (a j).IsUnitary) :
    (run (circuit a)).comp (run (GatePrefixCircuit.circuit a)) = LinearMap.id :=
  run_inverse_comp _ (GatePrefixCircuit.circuit_valid a ha)

/-- The reverse circuit takes the forward ideal frame on clean inputs back
to the original clean state, returning all prefix flags to zero. -/
theorem circuit_inverse_clean (a : Fin w → Coefficients)
    (ha : ∀ j, (a j).IsUnitary) :
    (run (circuit a)).comp ((embed 0).comp (ideal a w le_rfl)) = embed 0 := by
  rw [← GatePrefixCircuit.circuit_correct a, ← LinearMap.comp_assoc,
    circuit_comp_forward a ha]
  rfl

end
end SparseHamiltonian.GatePrefixInverse
