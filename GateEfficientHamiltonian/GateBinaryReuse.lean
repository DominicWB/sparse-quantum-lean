import GateEfficientHamiltonian.GatePrivateControl
/-!
# Exact reuse with a private binary pointer

The state has a public and private amplitude at each pointer word.  A step
applies the private operation at every word, a single boundary colligation
at the selected word, and a cyclic increment on the private sector only.
The reachable-support invariant is proved from these coordinate-linear
gates.  Consequently the successful public block is the already analysed
coherent-reuse block.  No involution hypothesis is imposed on the private
operation.  `capacity + 1` is the number of pointer words, so taking it to
be a power of two gives the binary-register implementation.

This module compiles with Lean/Mathlib 4.32.1.
-/

namespace SparseHamiltonian.GateBinaryReuse

noncomputable section

open ContinuousLinearMap ChronologicalResolvent FiniteChronologicalInverse
open scoped BigOperators InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Coordinate amplitudes of the public and private sectors.  The final
pointer word is available even after the last occupied public word. -/
abbrev Registers (capacity : ℕ) :=
  (Fin (capacity + 1) → P) × (Fin (capacity + 1) → V)

/-- A private amplitude supported at exactly one pointer word. -/
def point {capacity : ℕ} (j : Fin (capacity + 1)) (v : V) :
    Fin (capacity + 1) → V := fun k => if k = j then v else 0

/-- The given private operation acts coherently at every pointer word. -/
def privateEverywhere (D₀ : V →L[ℂ] V) (capacity : ℕ) :
    Registers (P := P) (V := V) capacity →ₗ[ℂ] Registers (P := P) (V := V) capacity where
  toFun z := (z.1, fun k => D₀ (z.2 k))
  map_add' := by
    intro z w
    apply Prod.ext
    · rfl
    · funext k
      exact map_add D₀ _ _
  map_smul' := by
    intro a z
    apply Prod.ext
    · rfl
    · funext k
      exact map_smul D₀ _ _

/-- The boundary network mixes the sectors only at the selected pointer word. -/
def boundary (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) {capacity : ℕ}
    (j : Fin (capacity + 1)) : Registers (P := P) (V := V) capacity →ₗ[ℂ] Registers (P := P) (V := V) capacity where
  toFun z :=
    (fun k => if k = j then A (z.1 k) + B (z.2 k) else z.1 k,
     fun k => if k = j then C (z.1 k) + D (z.2 k) else z.2 k)
  map_add' := by
    intro z w
    apply Prod.ext <;> funext k <;> by_cases h : k = j <;>
      simp [h, map_add, add_assoc, add_left_comm, add_comm]
  map_smul' := by
    intro a z
    apply Prod.ext <;> funext k <;> by_cases h : k = j <;>
      simp [h, map_smul, smul_add]

/-- Increment the pointer cyclically on the private sector, preserving every
public word.  This is a permutation, including on unreachable words. -/
def increment (capacity : ℕ) :
    Registers (P := P) (V := V) capacity →ₗ[ℂ] Registers (P := P) (V := V) capacity where
  toFun z := (z.1, fun k => z.2 ((finRotate (capacity + 1)).symm k))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- The inverse permutation is included explicitly: the pointer operation
does not erase its old value or assume the support invariant. -/
def decrement (capacity : ℕ) :
    Registers (P := P) (V := V) capacity →ₗ[ℂ] Registers (P := P) (V := V) capacity where
  toFun z := (z.1, fun k => z.2 (finRotate (capacity + 1) k))
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

omit [CompleteSpace P] [CompleteSpace V] in
theorem decrement_increment (capacity : ℕ) (z : Registers (P := P) (V := V) capacity) :
    decrement capacity (increment capacity z) = z := by
  apply Prod.ext
  · rfl
  · funext k
    simp [increment, decrement]

omit [CompleteSpace P] [CompleteSpace V] in
theorem increment_decrement (capacity : ℕ) (z : Registers (P := P) (V := V) capacity) :
    increment capacity (decrement capacity z) = z := by
  apply Prod.ext
  · rfl
  · funext k
    simp [increment, decrement]

/-- One exact circuit step, in the chronological order specified in the paper. -/
def step (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) {capacity : ℕ}
    (j : Fin (capacity + 1)) : Registers (P := P) (V := V) capacity →ₗ[ℂ] Registers (P := P) (V := V) capacity :=
  (increment capacity).comp
    ((boundary A B C D j).comp (privateEverywhere D₀ capacity))

omit [CompleteSpace P] [CompleteSpace V] in
theorem privateEverywhere_point (D₀ : V →L[ℂ] V) {capacity : ℕ}
    (p : Fin (capacity + 1) → P) (j : Fin (capacity + 1)) (v : V) :
    privateEverywhere D₀ capacity (p, point j v) = (p, point j (D₀ v)) := by
  apply Prod.ext
  · rfl
  · funext k
    by_cases h : k = j <;> simp [privateEverywhere, point, h]

omit [CompleteSpace P] [CompleteSpace V] in
theorem boundary_point (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) {capacity : ℕ}
    (p : Fin (capacity + 1) → P) (j : Fin (capacity + 1)) (v : V) :
    boundary A B C D j (p, point j v) =
      (fun k => if k = j then A (p j) + B v else p k,
       point j (C (p j) + D v)) := by
  apply Prod.ext <;> funext k <;> by_cases h : k = j <;>
    simp [boundary, point, h]

omit [CompleteSpace P] [CompleteSpace V] in
theorem increment_point {capacity : ℕ} (p : Fin (capacity + 1) → P)
    (j : Fin (capacity + 1)) (v : V) :
    increment capacity (p, point j v) =
      (p, point (finRotate (capacity + 1) j) v) := by
  apply Prod.ext
  · rfl
  · funext k
    change (if (finRotate (capacity + 1)).symm k = j then v else 0) =
      (if k = finRotate (capacity + 1) j then v else 0)
    have hiff : (finRotate (capacity + 1)).symm k = j ↔
        k = finRotate (capacity + 1) j := by
      constructor
      · intro h
        simpa using congrArg (finRotate (capacity + 1)) h
      · intro h
        rw [h, Equiv.symm_apply_apply]
    simp only [hiff]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The support invariant for one step is a theorem of the actual gates.
The effective reuse blocks are `A`, `B D₀`, `C`, and `D D₀`. -/
theorem step_point (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) {capacity : ℕ}
    (p : Fin (capacity + 1) → P) (j : Fin (capacity + 1)) (v : V) :
    step A B C D D₀ j (p, point j v) =
      (fun k => if k = j then A (p j) + B (D₀ v) else p k,
       point (finRotate (capacity + 1) j) (C (p j) + D (D₀ v))) := by
  change increment capacity
    (boundary A B C D j (privateEverywhere D₀ capacity (p, point j v))) = _
  rw [privateEverywhere_point, boundary_point, increment_point]

/-- The chronological circuit is a product of the explicit coordinate-linear
steps; the guard makes its definition total for every natural step count. -/
def run (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) (capacity : ℕ) :
    ℕ → Registers (P := P) (V := V) capacity →ₗ[ℂ] Registers (P := P) (V := V) capacity
  | 0 => LinearMap.id
  | j + 1 => if h : j < capacity + 1 then
      (step A B C D D₀ ⟨j, h⟩).comp (run A B C D D₀ capacity j)
    else run A B C D D₀ capacity j

/-- Squared Hilbert norm of the coordinate amplitudes. -/
def energy {capacity : ℕ} (z : Registers (P := P) (V := V) capacity) : ℝ :=
  ∑ k, (‖z.1 k‖ ^ 2 + ‖z.2 k‖ ^ 2)

omit [CompleteSpace P] [CompleteSpace V] in
theorem privateEverywhere_energy (D₀ : V →L[ℂ] V)
    (hD₀ : ∀ v, ‖D₀ v‖ = ‖v‖) (capacity : ℕ)
    (z : Registers (P := P) (V := V) capacity) :
    energy (privateEverywhere D₀ capacity z) = energy z := by
  simp [energy, privateEverywhere, hD₀]

omit [CompleteSpace P] [CompleteSpace V] in
theorem boundary_energy (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hS : ∀ p v, ‖A p + B v‖ ^ 2 + ‖C p + D v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    {capacity : ℕ} (j : Fin (capacity + 1)) (z : Registers (P := P) (V := V) capacity) :
    energy (boundary A B C D j z) = energy z := by
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k = j
  · simp only [boundary, LinearMap.coe_mk, AddHom.coe_mk, h, ↓reduceIte]
    exact hS _ _
  · simp [boundary, h]

omit [CompleteSpace P] [CompleteSpace V] in
theorem increment_energy (capacity : ℕ)
    (z : Registers (P := P) (V := V) capacity) :
    energy (increment capacity z) = energy z := by
  change (∑ k, (‖z.1 k‖ ^ 2 +
    ‖z.2 ((finRotate (capacity + 1)).symm k)‖ ^ 2)) = _
  rw [Finset.sum_add_distrib]
  unfold energy
  rw [Finset.sum_add_distrib]
  congr 1
  exact Fintype.sum_equiv (finRotate (capacity + 1)).symm _ _ (fun _ => rfl)

omit [CompleteSpace P] [CompleteSpace V] in
/-- All three operations preserve the physical Hilbert norm, on arbitrary
states and not merely the reachable one-pointer subspace. -/
theorem step_energy (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V)
    (hS : ∀ p v, ‖A p + B v‖ ^ 2 + ‖C p + D v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (hD₀ : ∀ v, ‖D₀ v‖ = ‖v‖) {capacity : ℕ}
    (j : Fin (capacity + 1)) (z : Registers (P := P) (V := V) capacity) :
    energy (step A B C D D₀ j z) = energy z := by
  change energy (increment capacity
    (boundary A B C D j (privateEverywhere D₀ capacity z))) = _
  rw [increment_energy, boundary_energy A B C D hS,
    privateEverywhere_energy D₀ hD₀]

omit [CompleteSpace P] [CompleteSpace V] in
theorem run_energy (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V)
    (hS : ∀ p v, ‖A p + B v‖ ^ 2 + ‖C p + D v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (hD₀ : ∀ v, ‖D₀ v‖ = ‖v‖) (capacity n : ℕ)
    (z : Registers (P := P) (V := V) capacity) :
    energy (run A B C D D₀ capacity n z) = energy z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases hn : n < capacity + 1
      · rw [run, dif_pos hn, LinearMap.comp_apply, step_energy A B C D D₀ hS hD₀, ih]
      · rw [run, dif_neg hn, ih]

/-- The same registers as a genuine Hilbert direct sum. -/
abbrev HilbertRegisters (capacity : ℕ) :=
  WithLp 2 (BlockOperator.H (capacity + 1) P × BlockOperator.H (capacity + 1) V)

def pack {capacity : ℕ} (z : Registers (P := P) (V := V) capacity) :
    HilbertRegisters (P := P) (V := V) capacity :=
  WithLp.toLp 2 (WithLp.toLp 2 z.1, WithLp.toLp 2 z.2)

omit [InnerProductSpace ℂ P] [CompleteSpace P] [InnerProductSpace ℂ V] [CompleteSpace V] in
theorem norm_pack_sq {capacity : ℕ} (z : Registers (P := P) (V := V) capacity) :
    ‖pack z‖ ^ 2 = energy z := by
  simp [pack, WithLp.prod_norm_sq_eq_of_L2, WithLp.fst, WithLp.snd,
    PiLp.norm_sq_eq_of_L2, energy, Finset.sum_add_distrib]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The explicit binary-pointer circuit is norm preserving in the quantum
Hilbert norm whenever its supplied local gates are norm preserving. -/
theorem run_norm (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V)
    (hS : ∀ p v, ‖A p + B v‖ ^ 2 + ‖C p + D v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (hD₀ : ∀ v, ‖D₀ v‖ = ‖v‖) (capacity n : ℕ)
    (z : Registers (P := P) (V := V) capacity) :
    ‖pack (run A B C D D₀ capacity n z)‖ = ‖pack z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_pack_sq, norm_pack_sq, run_energy A B C D D₀ hS hD₀]

/-- Completed public words have their response; future words retain the input. -/
def publicBefore (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) (capacity j : ℕ)
    (y : ℕ → P) : Fin (capacity + 1) → P := fun k =>
  if k.val < j then
    A (y k.val) + B (D₀ (forcedPublicState (D ∘L D₀) C y k.val))
  else y k.val

omit [CompleteSpace P] [CompleteSpace V] in
/-- Full invariant: all private amplitude occupies exactly the next pointer
word, while completed public words remain fixed. -/
theorem run_invariant (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) (capacity : ℕ)
    (y : ℕ → P) (j : ℕ) (hj : j ≤ capacity) :
    run A B C D D₀ capacity j (fun k => y k.val, 0) =
      (publicBefore A B C D D₀ capacity j y,
       point ⟨j, by omega⟩ (forcedPublicState (D ∘L D₀) C y j)) := by
  revert hj
  induction j with
  | zero =>
      intro hj
      apply Prod.ext
      · funext k
        simp [run, publicBefore]
      · funext k
        simp [run, point]
  | succ j ih =>
      intro hj
      have hjc : j < capacity := by omega
      have hjlt : j < capacity + 1 := by omega
      have hjle : j ≤ capacity := by omega
      rw [run, dif_pos hjlt, LinearMap.comp_apply, ih hjle]
      rw [step_point]
      have hcurrent : publicBefore A B C D D₀ capacity j y ⟨j, hjlt⟩ = y j := by
        simp [publicBefore]
      have hrotate : finRotate (capacity + 1) (⟨j, hjlt⟩ : Fin (capacity + 1)) =
          ⟨j + 1, by omega⟩ := finRotate_of_lt hjc
      rw [hcurrent, hrotate]
      apply Prod.ext
      · funext k
        by_cases hk : k.val = j
        · have hkeq : k = (⟨j, hjlt⟩ : Fin (capacity + 1)) := Fin.ext hk
          subst k
          simp [publicBefore]
        · have hkeq : k ≠ (⟨j, hjlt⟩ : Fin (capacity + 1)) := by
            intro h
            exact hk (congrArg Fin.val h)
          have hlt : k.val < j + 1 ↔ k.val < j := by omega
          simp only [hkeq, ↓reduceIte, publicBefore, hlt]
      · have hv : C (y j) + D (D₀ (forcedPublicState (D ∘L D₀) C y j)) =
            forcedPublicState (D ∘L D₀) C y (j + 1) := by
          change C (y j) + D (D₀ (forcedPublicState (D ∘L D₀) C y j)) =
            D (D₀ (forcedPublicState (D ∘L D₀) C y j)) + C (y j)
          exact add_comm (C (y j)) (D (D₀ (forcedPublicState (D ∘L D₀) C y j)))
        exact congrArg
          (fun v : V => point (⟨j + 1, by omega⟩ : Fin (capacity + 1)) v) hv

/-- Run the pointer circuit with zero-padded public input and read its first
`n` public words.  This definition directly uses the gates, not a stipulated
reuse formula. -/
def publicOutput (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) (capacity n : ℕ)
    (hn : n ≤ capacity) (x : BlockOperator.H n P) : BlockOperator.H n P :=
  WithLp.toLp 2 (fun k : Fin n =>
    (run A B C D D₀ capacity n
      (fun j => extendSequence x j.val, 0)).1 ⟨k.val, by omega⟩)

omit [CompleteSpace P] [CompleteSpace V] in
/-- Exact identification with the previously analysed chronological reuse.
There is no approximation and no unproved routing hypothesis. -/
theorem publicOutput_eq (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) (capacity n : ℕ)
    (hn : n ≤ capacity) (x : BlockOperator.H n P) :
    publicOutput A B C D D₀ capacity n hn x =
      CoherentReuse.publicReuse A (B ∘L D₀) C (D ∘L D₀) n x := by
  ext k
  change (run A B C D D₀ capacity n
      (fun j => extendSequence x j.val, 0)).1 ⟨k.val, by omega⟩ = _
  rw [run_invariant A B C D D₀ capacity (extendSequence x) n hn]
  change publicBefore A B C D D₀ capacity n (extendSequence x) ⟨k.val, by omega⟩ =
    chronologicalOperator A (B ∘L D₀) (D ∘L D₀) C n x k
  have hx : WithLp.toLp 2 (fun j : Fin n => extendSequence x j.val) = x :=
    restrict_extend x
  have hchron := chronologicalOperator_apply A (B ∘L D₀) (D ∘L D₀) C
    (extendSequence x) k
  rw [hx] at hchron
  rw [hchron]
  simp [publicBefore, k.isLt, chronologicalPrivateState]

/-- Prepare the uniform public pointer and unprepare it after the explicit
binary-pointer circuit; private amplitudes are excluded by the success test. -/
def successfulOutput (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) (capacity n : ℕ)
    (hn : n ≤ capacity) (p : P) : P :=
  ((CoherentReuse.uniformEmbedding n)†)
    (publicOutput A B C D D₀ capacity n hn (CoherentReuse.uniformEmbedding n p))

omit [CompleteSpace V] in
theorem successfulOutput_eq_block (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D D₀ : V →L[ℂ] V) (capacity n : ℕ)
    (hn : n ≤ capacity) (p : P) :
    successfulOutput A B C D D₀ capacity n hn p =
      CoherentReuse.successfulBlock A (B ∘L D₀) C (D ∘L D₀) n p := by
  rw [successfulOutput, publicOutput_eq]
  rfl

omit [CompleteSpace V] in
/-- The exact successful block asserted by the gate-efficient construction.
Only the local colligation/catalyst identities enter this final algebraic
corollary; pointer reachability has already been derived from the circuit. -/
theorem successfulOutput_eq (A U : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C Γ : P →L[ℂ] V) (D D₀ : V →L[ℂ] V)
    (hPublic : A + (B ∘L D₀) ∘L Γ = U)
    (hPrivate : C + (D ∘L D₀) ∘L Γ = Γ)
    (capacity n : ℕ) (hn : n ≤ capacity) (hn0 : n ≠ 0) (p : P) :
    successfulOutput A B C D D₀ capacity n hn p =
      (U - (B ∘L D₀) ∘L averagedGeometricFilter (D ∘L D₀) n ∘L Γ) p := by
  rw [successfulOutput_eq_block,
    CoherentReuse.successfulBlock_eq A U (B ∘L D₀) C Γ (D ∘L D₀)
      hPublic hPrivate n hn0]

end

end SparseHamiltonian.GateBinaryReuse
