import GateEfficientHamiltonian.GateRangeHilbertTransport
/-!
# Actual rotations for nonnegative coefficient tables

A binary table-preparation node splits the square-root amplitude of its
parent mass into its two child masses.  Zero-mass subtrees use the identity
rotation.  These coefficients will be placed in the mixed-prefix circuit;
no assumption of an arbitrary whole-register state-preparation gate is used.
-/

namespace SparseHamiltonian.GateTableSplit
noncomputable section

/-- Cosine for a table node; the zero-mass convention is the identity. -/
def cosine (left right : ℝ) : ℝ :=
  if left + right = 0 then 1 else Real.sqrt left / Real.sqrt (left + right)

/-- Sine for the same node, including its zero-mass convention. -/
def sine (left right : ℝ) : ℝ :=
  if left + right = 0 then 0 else Real.sqrt right / Real.sqrt (left + right)

theorem unit (left right : ℝ) (hl : 0 ≤ left) (hr : 0 ≤ right) :
    cosine left right ^ 2 + sine left right ^ 2 = 1 := by
  by_cases h : left + right = 0
  · simp [cosine, sine, h]
  · have hp : 0 < left + right := lt_of_le_of_ne (add_nonneg hl hr) (Ne.symm h)
    have hd : Real.sqrt (left + right) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    simp only [cosine, sine, if_neg h]
    field_simp [hd]; nlinarith [Real.sq_sqrt hl, Real.sq_sqrt hr,
      Real.sq_sqrt (add_nonneg hl hr)]

theorem cosine_nonneg (left right : ℝ) : 0 ≤ cosine left right := by
  unfold cosine
  split_ifs <;> positivity

theorem sine_nonneg (left right : ℝ) : 0 ≤ sine left right := by
  unfold sine
  split_ifs <;> positivity

theorem split_left (left right : ℝ) (hl : 0 ≤ left) (hr : 0 ≤ right) :
    Real.sqrt (left + right) * cosine left right = Real.sqrt left := by
  by_cases h : left + right = 0
  · have hl0 : left = 0 := by linarith
    have hr0 : right = 0 := by linarith
    simp [hl0, hr0, cosine]
  · have hp : 0 < left + right := lt_of_le_of_ne (add_nonneg hl hr) (Ne.symm h)
    have hd : Real.sqrt (left + right) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    simp only [cosine, if_neg h]
    field_simp [hd]

theorem split_right (left right : ℝ) (hl : 0 ≤ left) (hr : 0 ≤ right) :
    Real.sqrt (left + right) * sine left right = Real.sqrt right := by
  by_cases h : left + right = 0
  · have hl0 : left = 0 := by linarith
    have hr0 : right = 0 := by linarith
    simp [hl0, hr0, sine]
  · have hp : 0 < left + right := lt_of_le_of_ne (add_nonneg hl hr) (Ne.symm h)
    have hd : Real.sqrt (left + right) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
    simp only [sine, if_neg h]
    field_simp [hd]

/-- A concrete two-by-two matrix for the table node. -/
def coefficients (left right : ℝ) : GatePrefixCircuit.Coefficients :=
  GateDyadicUnitary.rotationCoefficients (cosine left right) (sine left right)

theorem coefficients_unitary (left right : ℝ) (hl : 0 ≤ left) (hr : 0 ≤ right) :
    (coefficients left right).IsUnitary :=
  GateDyadicUnitary.rotationCoefficients_unitary _ _ (unit left right hl hr)

/-- Exact first-column action, including when both masses vanish. -/
theorem coefficients_split (left right : ℝ) (hl : 0 ≤ left) (hr : 0 ≤ right)
    (b : Bool) :
    coefficients left right b false * (Real.sqrt (left + right) : ℂ) =
      if b then (Real.sqrt right : ℂ) else (Real.sqrt left : ℂ) := by
  cases b
  · change (cosine left right : ℂ) * (Real.sqrt (left + right) : ℂ) =
      (Real.sqrt left : ℂ)
    have h := congrArg Complex.ofReal (split_left left right hl hr)
    push_cast at h
    simpa only [mul_comm] using h
  · change (sine left right : ℂ) * (Real.sqrt (left + right) : ℂ) =
      (Real.sqrt right : ℂ)
    have h := congrArg Complex.ofReal (split_right left right hl hr)
    push_cast at h
    simpa only [mul_comm] using h

end
end SparseHamiltonian.GateTableSplit


/-!
This component supplies the mixed-polarity prefix gates and the concrete
depth-first traversal list needed for filter coefficient preparation, with
whole-traversal intertwining. The complete square-root-table preparation theorem and finite Hilbert-space
lift remain open.

The actual target probabilities are
  `CoherentLCU.coefficientProbability (ReuseWeights.weight a d)`;
for the averaging-polynomial coefficients their sum is one by
`ReuseWeights.concrete_absolute_mass` and
`CoherentLCU.coefficientProbability_sum`.
-/

namespace SparseHamiltonian.GateFilterTree

noncomputable section
open scoped BigOperators

abbrev Word (w : ℕ) := GatePrefixCircuit.Word w
abbrev Configuration (w : ℕ) := GatePrefixCircuit.Configuration w
abbrev State (w : ℕ) := GatePrefixCircuit.State w
abbrev Coefficients := GatePrefixCircuit.Coefficients

variable {w : ℕ}

/-- A classical relabelling used only in proofs. It is not charged as an
elementary gate. The actual prefix gate below reads only the preceding bit
and the preceding prefix flag. -/
def twistWord (p x : Word w) : Word w :=
  fun j => if p j then !(x j) else x j

theorem twistWord_twice (p x : Word w) :
    twistWord p (twistWord p x) = x := by
  funext j
  cases hp : p j <;> cases hx : x j <;> simp [twistWord, hp, hx]

theorem twistWord_update (p x : Word w) (j : Fin w) (b : Bool) :
    twistWord p (Function.update x j b) =
      Function.update (twistWord p x) j (if p j then !b else b) := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [twistWord]
  · simp [twistWord, Function.update_of_ne hi]

theorem twistWord_path_update (p x : Word w) (j : Fin w) (b : Bool) :
    twistWord (Function.update p j b) x =
      Function.update (twistWord p x) j (if b then !(x j) else x j) := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [twistWord]
  · simp [twistWord, Function.update_of_ne hi]

def twistConfiguration (p : Word w) (z : Configuration w) : Configuration w where
  slot := twistWord p z.slot
  flags := z.flags

theorem twistConfiguration_twice (p : Word w) (z : Configuration w) :
    twistConfiguration p (twistConfiguration p z) = z := by
  apply GatePrefixCircuit.Configuration.ext
  · exact twistWord_twice p z.slot
  · rfl

/-- Compute the predicate that all preceding bits equal a public path.
For `j = 0` this is a NOT on the root flag; otherwise it is a mixed-polarity
Toffoli on the preceding flag, preceding slot, and current flag. -/
def pathControl (p : Word w) (j : Fin w) (z : Configuration w) : Bool :=
  if hj : j.val = 0 then true
  else z.flags (GatePrefixCircuit.previous j hj) &&
    !(twistWord p z.slot (GatePrefixCircuit.previous j hj))

def togglePath (p : Word w) (j : Fin w) (z : Configuration w) : Configuration w where
  slot := z.slot
  flags := Function.update z.flags j
    (if pathControl p j z then !(z.flags j) else z.flags j)

theorem pathControl_eq (p : Word w) (j : Fin w) (z : Configuration w) :
    pathControl p j z =
      GatePrefixCircuit.prefixControl j (twistConfiguration p z) := rfl

/-- Identification with a conjugated zero-prefix gate is a correctness
proof, not an implementation charging a whole-register relabelling. -/
theorem togglePath_eq (p : Word w) (j : Fin w) (z : Configuration w) :
    togglePath p j z = twistConfiguration p
      (GatePrefixCircuit.togglePrefix j (twistConfiguration p z)) := by
  apply GatePrefixCircuit.Configuration.ext
  · exact (twistWord_twice p z.slot).symm
  · rfl

theorem togglePath_involutive (p : Word w) (j : Fin w) :
    Function.Involutive (togglePath p j) := by
  intro z
  rw [togglePath_eq, togglePath_eq, twistConfiguration_twice,
    GatePrefixCircuit.togglePrefix_involutive j (twistConfiguration p z),
    twistConfiguration_twice]

/-- The path-prefix invariant reuses the proved zero-prefix invariant after
a known Boolean relabelling. The slot register is still literally `x`. -/
def encoded (p : Word w) (n : ℕ) (x : Word w) : Configuration w :=
  twistConfiguration p (GatePrefixCircuit.encoded n (twistWord p x))

@[simp] theorem encoded_slot (p : Word w) (n : ℕ) (x : Word w) :
    (encoded p n x).slot = x := twistWord_twice p x

@[simp] theorem encoded_zero_flags (p : Word w) (x : Word w) :
    (encoded p 0 x).flags = fun _ => false := by
  exact GatePrefixCircuit.encoded_zero (twistWord p x)

theorem togglePath_encoded (p : Word w) (j : Fin w) (x : Word w) :
    togglePath p j (encoded p j.val x) = encoded p (j.val + 1) x := by
  rw [togglePath_eq]
  unfold encoded
  rw [twistConfiguration_twice, GatePrefixCircuit.togglePrefix_encoded]

theorem togglePath_encoded_succ (p : Word w) (j : Fin w) (x : Word w) :
    togglePath p j (encoded p (j.val + 1) x) = encoded p j.val x := by
  rw [← togglePath_encoded p j x]
  exact togglePath_involutive p j (encoded p j.val x)

/-- A node rotation changes only its current slot; all computed earlier
path flags retain their values. -/
theorem encoded_update_slot (p : Word w) (j : Fin w) (x : Word w) (b : Bool) :
    encoded p (j.val + 1) (Function.update x j b) =
      { slot := Function.update x j b,
        flags := (encoded p (j.val + 1) x).flags } := by
  apply GatePrefixCircuit.Configuration.ext
  · exact encoded_slot p (j.val + 1) (Function.update x j b)
  · funext i
    change (if i.val < j.val + 1 then
        GatePrefixCircuit.prefixBit (twistWord p (Function.update x j b)) i.val
      else false) =
      (if i.val < j.val + 1 then
        GatePrefixCircuit.prefixBit (twistWord p x) i.val else false)
    by_cases hi : i.val < j.val + 1
    · rw [if_pos hi, if_pos hi, twistWord_update]
      exact GatePrefixCircuit.prefix_update (twistWord p x) j
        (if p j then !b else b) i.val (by omega)
    · rw [if_neg hi, if_neg hi]

/-- Choosing either child changes a public path bit which none of the
already-computed prefix flags reads. Thus both child traversals share
literally the same physical invariant subspace at their entrance and exit. -/
theorem encoded_path_update (p : Word w) (j : Fin w) (b : Bool)
    (n : ℕ) (hn : n ≤ j.val + 1) (x : Word w) :
    encoded (Function.update p j b) n x = encoded p n x := by
  apply GatePrefixCircuit.Configuration.ext
  · simp only [encoded_slot]
  · funext i
    change (if i.val < n then
        GatePrefixCircuit.prefixBit (twistWord (Function.update p j b) x) i.val
      else false) =
      (if i.val < n then GatePrefixCircuit.prefixBit (twistWord p x) i.val
      else false)
    by_cases hi : i.val < n
    · rw [if_pos hi, if_pos hi, twistWord_path_update]
      exact GatePrefixCircuit.prefix_update (twistWord p x) j
        (if b then !(x j) else x j) i.val (by omega)
    · rw [if_neg hi, if_neg hi]

/-- The new syntax has the same maximum arity as the existing prefix
construction: at most three Boolean wires, or a controlled one-qubit gate. -/
inductive Gate (w : ℕ) where
  | prefix (p : Word w) (j : Fin w)
  | rotate (j : Fin w) (a : Coefficients)

def Gate.eval : Gate w → State w →ₗ[ℂ] State w
  | .prefix p j => Finsupp.linearCombination ℂ
      (fun z => Finsupp.single (togglePath p j z) 1)
  | .rotate j a => GatePrefixCircuit.Gate.eval (.rotate j a)

def embed (p : Word w) (n : ℕ) :
    GatePrefixCircuit.SlotState w →ₗ[ℂ] State w :=
  Finsupp.linearCombination ℂ (fun x => Finsupp.single (encoded p n x) 1)

theorem embed_path_update (p : Word w) (j : Fin w) (b : Bool)
    (n : ℕ) (hn : n ≤ j.val + 1) :
    embed (Function.update p j b) n = embed p n := by
  apply Finsupp.lhom_ext
  intro x c
  simp [embed, encoded_path_update p j b n hn]

theorem prefix_gate_embed (p : Word w) (j : Fin w) :
    (Gate.eval (.prefix p j)).comp (embed p j.val) =
      embed p (j.val + 1) := by
  apply Finsupp.lhom_ext
  intro x c
  simp [Gate.eval, embed, togglePath_encoded]

theorem prefix_gate_unembed (p : Word w) (j : Fin w) :
    (Gate.eval (.prefix p j)).comp (embed p (j.val + 1)) =
      embed p j.val := by
  apply Finsupp.lhom_ext
  intro x c
  simp [Gate.eval, embed, togglePath_encoded_succ]

/-- The many-controlled operator is used only to state the meaning of an
elementary node rotation on its computed-prefix invariant subspace. -/
def idealBasis (p : Word w) (j : Fin w) (a : Coefficients)
    (x : Word w) : GatePrefixCircuit.SlotState w :=
  if GatePrefixCircuit.prefixBit (twistWord p x) j.val then
    ∑ b : Bool, a b (x j) • Finsupp.single (Function.update x j b) 1
  else Finsupp.single x 1

def idealStep (p : Word w) (j : Fin w) (a : Coefficients) :
    GatePrefixCircuit.SlotState w →ₗ[ℂ] GatePrefixCircuit.SlotState w :=
  Finsupp.linearCombination ℂ (idealBasis p j a)

/-- Actual one-control gate correctness for an arbitrary public path. -/
theorem rotation_gate_embed (p : Word w) (j : Fin w) (a : Coefficients) :
    (Gate.eval (.rotate j a)).comp (embed p (j.val + 1)) =
      (embed p (j.val + 1)).comp (idealStep p j a) := by
  apply Finsupp.lhom_ext
  intro x c
  simp only [LinearMap.comp_apply, embed, Gate.eval, idealStep,
    GatePrefixCircuit.Gate.eval, Finsupp.linearCombination_single, map_smul]
  congr 1
  have hf : (encoded p (j.val + 1) x).flags j =
      GatePrefixCircuit.prefixBit (twistWord p x) j.val := by
    simp [encoded, twistConfiguration, GatePrefixCircuit.encoded]
  simp only [GatePrefixCircuit.rotateBasis, idealBasis, hf, encoded_slot]
  cases hp : GatePrefixCircuit.prefixBit (twistWord p x) j.val
  · simp
  · simp only [if_true, map_sum, map_smul,
      Finsupp.linearCombination_single, one_smul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [encoded_update_slot]

/-- A complete binary tree of public local rotation matrices. Assignment of
the matrices from conditional probability masses is a separate obligation. -/
inductive RotationTree : ℕ → Type where
  | leaf : RotationTree 0
  | node {h : ℕ} (a : Coefficients) (left right : RotationTree h) :
      RotationTree (h + 1)

/-- Depth-first traversal computes each path flag once, retains it while
visiting the two child subtrees, then uncomputes it. No gate has a number of
controls proportional to the tree depth. Only `w` reusable prefix flags are
needed. `p` is a compile-time path, not a quantum register. -/
def compile : {h : ℕ} → RotationTree h →
    (offset : ℕ) → offset + h ≤ w → Word w → List (Gate w)
  | 0, .leaf, _, _, _ => []
  | h + 1, .node a left right, offset, hfit, p =>
      let j : Fin w := ⟨offset, by omega⟩
      let hchild : offset + 1 + h ≤ w := by omega
      [.prefix p j, .rotate j a] ++
        compile left (offset + 1) hchild (Function.update p j false) ++
        compile right (offset + 1) hchild (Function.update p j true) ++
        [.prefix p j]

/-- Mathematical action of the tree as path-conditioned rotations. This
operator is only a specification; the actual implementation is `compile`. -/
def idealTraversal : {h : ℕ} → RotationTree h →
    (offset : ℕ) → offset + h ≤ w → Word w →
      GatePrefixCircuit.SlotState w →ₗ[ℂ] GatePrefixCircuit.SlotState w
  | 0, .leaf, _, _, _ => LinearMap.id
  | h + 1, .node a left right, offset, hfit, p =>
      let j : Fin w := ⟨offset, by omega⟩
      let hchild : offset + 1 + h ≤ w := by omega
      (idealTraversal right (offset + 1) hchild (Function.update p j true)).comp
        ((idealTraversal left (offset + 1) hchild (Function.update p j false)).comp
          (idealStep p j a))

/-- Exactly three elementary gates per internal tree node. The count
already includes all prefix preparation and unpreparation. -/
theorem compile_length {h : ℕ} (t : RotationTree h) (offset : ℕ)
    (hfit : offset + h ≤ w) (p : Word w) :
    (compile t offset hfit p).length = 3 * (2 ^ h - 1) := by
  induction t generalizing offset p with
  | leaf => simp [compile]
  | @node h a left right ihL ihR =>
      simp only [compile, List.length_append, List.length_cons, List.length_nil]
      rw [ihL, ihR]
      have hpow : 0 < 2 ^ h := by positivity
      rw [pow_succ]
      omega

/-- Genuine complex-linear semantics of the literal depth-first list. -/
def run : List (Gate w) → State w →ₗ[ℂ] State w
  | [] => LinearMap.id
  | g :: gs => (run gs).comp g.eval

theorem run_append (gs hs : List (Gate w)) :
    run (gs ++ hs) = (run hs).comp (run gs) := by
  induction gs with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, LinearMap.comp_assoc]

/-- A concrete three-gate node computes its path control, performs the
rotation, and uncomputes the flag, on arbitrary superpositions in the
preceding-prefix invariant subspace. -/
theorem node_compute_rotate_uncompute (p : Word w) (j : Fin w)
    (a : Coefficients) :
    (run [.prefix p j, .rotate j a, .prefix p j]).comp (embed p j.val) =
      (embed p j.val).comp (idealStep p j a) := by
  simp only [run, LinearMap.id_comp]
  rw [LinearMap.comp_assoc, prefix_gate_embed]
  rw [LinearMap.comp_assoc, rotation_gate_embed]
  rw [← LinearMap.comp_assoc, prefix_gate_unembed]

/-- The whole depth-first list implements its tree of ideal rotations on
arbitrary superpositions, returns all temporary path flags clean relative
to its input depth, and uses the same workspace for both child subtrees. -/
theorem compile_intertwines {h : ℕ} (t : RotationTree h) (offset : ℕ)
    (hfit : offset + h ≤ w) (p : Word w) :
    (run (compile t offset hfit p)).comp (embed p offset) =
      (embed p offset).comp (idealTraversal t offset hfit p) := by
  induction t generalizing offset p with
  | leaf => simp [compile, run, idealTraversal]
  | @node h a left right ihL ihR =>
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + h ≤ w := by omega
      have hEL : embed (Function.update p j false) (offset + 1) =
          embed p (offset + 1) :=
        embed_path_update p j false (offset + 1) (by simp [j])
      have hER : embed (Function.update p j true) (offset + 1) =
          embed p (offset + 1) :=
        embed_path_update p j true (offset + 1) (by simp [j])
      have hL := ihL (offset := offset + 1) (hfit := hchild)
        (p := Function.update p j false)
      have hR := ihR (offset := offset + 1) (hfit := hchild)
        (p := Function.update p j true)
      rw [hEL] at hL
      rw [hER] at hR
      have hpre (u : GatePrefixCircuit.SlotState w) :
          Gate.eval (.prefix p j) (embed p offset u) =
            embed p (offset + 1) u := by
        exact congrArg (fun F : GatePrefixCircuit.SlotState w →ₗ[ℂ] State w => F u)
          (prefix_gate_embed p j)
      have hrot (u : GatePrefixCircuit.SlotState w) :
          Gate.eval (.rotate j a) (embed p (offset + 1) u) =
            embed p (offset + 1) (idealStep p j a u) := by
        exact congrArg (fun F : GatePrefixCircuit.SlotState w →ₗ[ℂ] State w => F u)
          (rotation_gate_embed p j a)
      have hpost (u : GatePrefixCircuit.SlotState w) :
          Gate.eval (.prefix p j) (embed p (offset + 1) u) =
            embed p offset u := by
        exact congrArg (fun F : GatePrefixCircuit.SlotState w →ₗ[ℂ] State w => F u)
          (prefix_gate_unembed p j)
      have hLapply (u : GatePrefixCircuit.SlotState w) :
          run (compile left (offset + 1) hchild (Function.update p j false))
            (embed p (offset + 1) u) =
          embed p (offset + 1)
            (idealTraversal left (offset + 1) hchild (Function.update p j false) u) :=
        congrArg (fun F : GatePrefixCircuit.SlotState w →ₗ[ℂ] State w => F u) hL
      have hRapply (u : GatePrefixCircuit.SlotState w) :
          run (compile right (offset + 1) hchild (Function.update p j true))
            (embed p (offset + 1) u) =
          embed p (offset + 1)
            (idealTraversal right (offset + 1) hchild (Function.update p j true) u) :=
        congrArg (fun F : GatePrefixCircuit.SlotState w →ₗ[ℂ] State w => F u) hR
      apply LinearMap.ext
      intro v
      simp only [compile, idealTraversal, run_append, run,
        LinearMap.comp_apply, LinearMap.id_apply]
      change Gate.eval (.prefix p j)
          (run (compile right (offset + 1) hchild (Function.update p j true))
            (run (compile left (offset + 1) hchild (Function.update p j false))
              (Gate.eval (.rotate j a) (Gate.eval (.prefix p j) (embed p offset v))))) =
        embed p offset
          (idealTraversal right (offset + 1) hchild (Function.update p j true)
            (idealTraversal left (offset + 1) hchild (Function.update p j false)
              (idealStep p j a v)))
      rw [hpre, hrot, hLapply, hRapply, hpost]

/- Remaining central obligations, deliberately not assumed:
1. Instantiate the tree with the required padded coefficient table; the
   local mass-splitting matrices are provided by GateTableSplit.
2. Show the zero input is sent to the square-root probability table and
   prove the actual adjoint reverses that preparation.
3. Lift the literal bounded-arity list to the finite physical Hilbert space;
   tensor arbitrary payload/reference registers without cost inflation.
4. Choose a power-of-two table size between 2(d+1) and 4(d+1), pad with zero
   probabilities, and prove the concrete ReuseWeights/CoherentLCU identity.
-/

end
end SparseHamiltonian.GateFilterTree


/-! ### Bounded arity and validity of the concrete traversal -/

namespace SparseHamiltonian.GateFilterTree
noncomputable section

variable {w : ℕ}

/-- Prefix gates are either a NOT or a mixed-polarity Toffoli; each rotation
has one flag control and one slot target. -/
def Gate.arity : Gate w → ℕ
  | .prefix _ j => if j.val = 0 then 1 else 3
  | .rotate _ _ => 2

theorem Gate.arity_le_three (g : Gate w) : g.arity ≤ 3 := by
  cases g with
  | «prefix» p j =>
      simp only [Gate.arity]
      split_ifs <;> omega
  | rotate j a => norm_num [Gate.arity]

/-- Arbitrary coefficient arrays still have the algebraic semantics above,
but a quantum circuit requires each two-dimensional coefficient matrix to
be unitary. No such property is inferred merely from the word 'rotation'. -/
def Gate.Valid : Gate w → Prop
  | .prefix _ _ => True
  | .rotate _ a => GatePrefixCircuit.Coefficients.IsUnitary a

/-- Validity of a whole table tree records every actual node matrix. -/
def RotationTree.Valid : {h : ℕ} → RotationTree h → Prop
  | 0, .leaf => True
  | _ + 1, .node a left right =>
      GatePrefixCircuit.Coefficients.IsUnitary a ∧ left.Valid ∧ right.Valid

/-- All elementary instructions in a list satisfy their explicit validity
conditions. This is distinct from their algebraic action on amplitudes. -/
def GatesValid (gs : List (Gate w)) : Prop := ∀ g ∈ gs, g.Valid

theorem gatesValid_append (gs hs : List (Gate w)) :
    GatesValid (gs ++ hs) ↔ GatesValid gs ∧ GatesValid hs := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (List.mem_append.mpr (Or.inl hg))
    · intro g hg
      exact h g (List.mem_append.mpr (Or.inr hg))
  · rintro ⟨hg, hh⟩ g hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hg g hm
    · exact hh g hm

/-- Tree compilation transfers matrix unitarity to every literal instruction,
without adding an implementation hypothesis for the traversal. -/
theorem compile_valid {h : ℕ} (t : RotationTree h) :
    t.Valid → ∀ (offset : ℕ) (hfit : offset + h ≤ w) (p : Word w),
      GatesValid (compile t offset hfit p) := by
  induction t with
  | leaf =>
      intro ht offset hfit p g hg
      simp [compile] at hg
  | @node h a left right ihL ihR =>
      intro ht offset hfit p
      change GatePrefixCircuit.Coefficients.IsUnitary a ∧ left.Valid ∧ right.Valid at ht
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + h ≤ w := by omega
      have hstart : GatesValid [.prefix p j, .rotate j a] := by
        intro g hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl
        · trivial
        · exact ht.1
      have hend : GatesValid [.prefix p j] := by
        intro g hg
        have he : g = Gate.prefix p j := by simpa using hg
        subst g
        trivial
      have hleft := ihL ht.2.1 (offset + 1) hchild (Function.update p j false)
      have hright := ihR ht.2.2 (offset + 1) hchild (Function.update p j true)
      exact (gatesValid_append _ _).mpr ⟨(gatesValid_append _ _).mpr
        ⟨(gatesValid_append _ _).mpr ⟨hstart, hleft⟩, hright⟩, hend⟩

/-- Arity is bounded independently of the tree depth and the chosen path. -/
theorem compile_gate_arity {h : ℕ} (t : RotationTree h) (offset : ℕ)
    (hfit : offset + h ≤ w) (p : Word w) (g : Gate w)
    (_hg : g ∈ compile t offset hfit p) : g.arity ≤ 3 :=
  g.arity_le_three

end
end SparseHamiltonian.GateFilterTree


/-! ### Constructing every tree rotation from nonnegative leaf masses

No unitary-matrix hypothesis is needed for this construction:
each actual matrix is constructed from its two child masses.
-/

namespace SparseHamiltonian.GateFilterTree
noncomputable section
open scoped BigOperators

/-- A finite complete binary table with a proof of nonnegative mass at each
leaf. This is public input data, not a state-preparation certificate. -/
inductive MassTree : ℕ → Type where
  | leaf (a : ℝ) (ha : 0 ≤ a) : MassTree 0
  | node {h : ℕ} (left right : MassTree h) : MassTree (h + 1)

def MassTree.mass : {h : ℕ} → MassTree h → ℝ
  | 0, .leaf a _ => a
  | _ + 1, .node left right => left.mass + right.mass

theorem MassTree.mass_nonneg {h : ℕ} (t : MassTree h) : 0 ≤ t.mass := by
  induction t with
  | leaf a ha => exact ha
  | node left right ihL ihR => exact add_nonneg ihL ihR

/-- The actual public rotation matrix at each branching node. Empty-mass
nodes use the identity convention proved in GateTableSplit. -/
def MassTree.rotations : {h : ℕ} → MassTree h → RotationTree h
  | 0, .leaf _ _ => .leaf
  | _ + 1, .node left right =>
      .node (GateTableSplit.coefficients left.mass right.mass)
        left.rotations right.rotations

theorem MassTree.rotations_valid {h : ℕ} (t : MassTree h) :
    t.rotations.Valid := by
  induction t with
  | leaf a ha => trivial
  | node left right ihL ihR =>
      exact ⟨GateTableSplit.coefficients_unitary left.mass right.mass
        left.mass_nonneg right.mass_nonneg, ihL, ihR⟩

/-- All literal compiled gates are valid, as a consequence of leaf
nonnegativity alone; no state-preparation or rotation-validity assumption
is passed to this theorem. -/
theorem MassTree.compile_valid {h w : ℕ} (t : MassTree h) (offset : ℕ)
    (hfit : offset + h ≤ w) (p : Word w) :
    GatesValid (compile t.rotations offset hfit p) :=
  GateFilterTree.compile_valid t.rotations t.rotations_valid offset hfit p

/-- Recursive lookup of the table's leaf mass. The first bit chooses the
root child, in the same order used by the physical tree traversal. -/
def MassTree.value : {h : ℕ} → MassTree h → Word h → ℝ
  | 0, .leaf a _, _ => a
  | _ + 1, .node left right, x =>
      if x 0 then right.value (fun j => x j.succ)
      else left.value (fun j => x j.succ)

/-- Construct a mass tree from an arbitrary nonnegative Boolean-indexed
table. This recursion performs only classical preprocessing of known data. -/
def MassTree.fromTable : (h : ℕ) → (a : Word h → ℝ) →
    (∀ x, 0 ≤ a x) → MassTree h
  | 0, a, ha => .leaf (a (fun j => Fin.elim0 j)) (ha _)
  | h + 1, a, ha =>
      .node
        (fromTable h (fun x => a (Fin.cons false x)) (fun _ => ha _))
        (fromTable h (fun x => a (Fin.cons true x)) (fun _ => ha _))

/-- Reconstructing the word from its first bit and tail changes no data. -/
theorem word_cons_head_tail {h : ℕ} (x : Word (h + 1)) :
    Fin.cons (x 0) (fun j => x j.succ) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Exact bijection used for finite summation over a table's two children. -/
def wordHeadTail (h : ℕ) : Word (h + 1) ≃ Bool × Word h where
  toFun x := (x 0, fun j => x j.succ)
  invFun q := Fin.cons q.1 q.2
  left_inv := word_cons_head_tail
  right_inv q := by
    rcases q with ⟨b, x⟩
    rfl

theorem sum_words_succ (h : ℕ) (a : Word (h + 1) → ℝ) :
    (∑ x : Word (h + 1), a x) =
      (∑ x : Word h, a (Fin.cons false x)) +
        ∑ x : Word h, a (Fin.cons true x) := by
  calc
    (∑ x : Word (h + 1), a x) =
        ∑ q : Bool × Word h, a (Fin.cons q.1 q.2) :=
      (Fintype.sum_equiv (wordHeadTail h).symm _ _ (fun _ => rfl)).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-- The recursively computed parent masses are exactly the sums of the
original nonnegative leaf masses, so their normalisation has no hidden
state-preparation certificate. -/
theorem MassTree.mass_eq_sum_values {h : ℕ} (t : MassTree h) :
    t.mass = ∑ x : Word h, t.value x := by
  induction t with
  | leaf a ha =>
      simp [MassTree.mass, MassTree.value, Word, GatePrefixCircuit.Word]
  | @node h left right ihL ihR =>
      rw [MassTree.mass, ihL, ihR, sum_words_succ]
      simp [MassTree.value]

/-- The constructed tree contains exactly the supplied table, rather than
a table selected by an existential preparation assumption. -/
theorem MassTree.fromTable_value (h : ℕ) (a : Word h → ℝ)
    (ha : ∀ x, 0 ≤ a x) (x : Word h) :
    (MassTree.fromTable h a ha).value x = a x := by
  induction h with
  | zero =>
      have hx : x = (fun j => Fin.elim0 j) := by
        funext j
        exact Fin.elim0 j
      subst x
      rfl
  | succ h ih =>
      have hx := word_cons_head_tail x
      cases hb : x 0
      · simp only [MassTree.fromTable, MassTree.value, hb, Bool.false_eq_true,
          if_false]
        rw [ih]
        congr 1
        simpa only [hb] using hx
      · simp only [MassTree.fromTable, MassTree.value, hb, 
          if_true]
        rw [ih]
        congr 1
        simpa only [hb] using hx

theorem MassTree.fromTable_mass (h : ℕ) (a : Word h → ℝ)
    (ha : ∀ x, 0 ≤ a x) :
    (MassTree.fromTable h a ha).mass = ∑ x : Word h, a x := by
  rw [MassTree.mass_eq_sum_values]
  apply Finset.sum_congr rfl
  intro x hx
  exact MassTree.fromTable_value h a ha x

/-- The coherent-LCU coefficient probabilities have exactly unit root mass.
For the smoothing weights, the required absolute-mass premise is supplied
by ReuseWeights.concrete_absolute_mass after finite table relabelling. -/
theorem MassTree.coefficientTable_mass (h : ℕ) (a : Word h → ℝ)
    (ha : ∑ x, |a x| = 2) :
    (MassTree.fromTable h (CoherentLCU.coefficientProbability a)
      (CoherentLCU.coefficientProbability_nonneg a)).mass = 1 := by
  rw [MassTree.fromTable_mass]
  exact CoherentLCU.coefficientProbability_sum a ha

/-- Exact first-column split at each actual node, including zero-mass
subtrees. This is the local amplitude identity for the table-preparation
induction still to be connected to idealTraversal. -/
theorem MassTree.node_split {h : ℕ} (left right : MassTree h) (b : Bool) :
    GateTableSplit.coefficients left.mass right.mass b false *
      (Real.sqrt (MassTree.node left right).mass : ℂ) =
      if b then (Real.sqrt right.mass : ℂ) else (Real.sqrt left.mass : ℂ) :=
  GateTableSplit.coefficients_split left.mass right.mass
    left.mass_nonneg right.mass_nonneg b

end
end SparseHamiltonian.GateFilterTree


/-! ### Literal reversal of the filter-tree traversal -/

namespace SparseHamiltonian.GateFilterTree
noncomputable section

variable {w : ℕ}

/-- Reverse each local instruction on exactly the same wires.  Prefix
Boolean gates are involutions; a controlled matrix is conjugate-transposed. -/
def Gate.inverse : Gate w → Gate w
  | .prefix p j => .prefix p j
  | .rotate j a => .rotate j (Matrix.conjTranspose a)

@[simp] theorem Gate.inverse_inverse (g : Gate w) : g.inverse.inverse = g := by
  cases g with
  | «prefix» p j => rfl
  | rotate j a => simp [Gate.inverse, Matrix.conjTranspose_conjTranspose]

@[simp] theorem Gate.inverse_arity (g : Gate w) : g.inverse.arity = g.arity := by
  cases g <;> rfl

theorem Gate.inverse_valid (g : Gate w) (hg : g.Valid) : g.inverse.Valid := by
  cases g with
  | «prefix» p j => trivial
  | rotate j a =>
      exact GatePrefixCircuit.Gate.inverse_valid (.rotate j a) hg

/-- Inverse action on the complete amplitude space, including arbitrary
initial values of the temporary path flags. -/
theorem Gate.inverse_comp (g : Gate w) (hg : g.Valid) :
    g.inverse.eval.comp g.eval = LinearMap.id := by
  cases g with
  | «prefix» p j =>
      apply Finsupp.lhom_ext
      intro z c
      simp [Gate.inverse, Gate.eval, LinearMap.comp_apply, togglePath_involutive p j z]
  | rotate j a =>
      exact GatePrefixCircuit.Gate.inverse_comp (.rotate j a) hg

theorem Gate.comp_inverse (g : Gate w) (hg : g.Valid) :
    g.eval.comp g.inverse.eval = LinearMap.id := by
  have h := g.inverse.inverse_comp (g.inverse_valid hg)
  simpa only [Gate.inverse_inverse] using h

/-- This is the literal reversed elementary list, with local inverses. -/
def inverse (gs : List (Gate w)) : List (Gate w) :=
  gs.reverse.map Gate.inverse

@[simp] theorem inverse_nil : inverse ([] : List (Gate w)) = [] := rfl

@[simp] theorem inverse_cons (g : Gate w) (gs : List (Gate w)) :
    inverse (g :: gs) = inverse gs ++ [g.inverse] := by
  simp [inverse]

@[simp] theorem inverse_length (gs : List (Gate w)) :
    (inverse gs).length = gs.length := by simp [inverse]

theorem inverse_valid (gs : List (Gate w)) (hgs : GatesValid gs) :
    GatesValid (inverse gs) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  exact q.inverse_valid (hgs q (List.mem_reverse.mp hq))

/-- The actual inverse list undoes the full compiled map; no clean-input
or state-preparation assumption appears in this two-sided identity. -/
theorem run_inverse_comp (gs : List (Gate w)) (hgs : GatesValid gs) :
    (run (inverse gs)).comp (run gs) = LinearMap.id := by
  revert hgs
  induction gs with
  | nil => intro _; rfl
  | cons g gs ih =>
      intro hgs
      have hg := hgs g List.mem_cons_self
      have ht : GatesValid gs := fun q hq => hgs q (List.mem_cons_of_mem g hq)
      have hi := ih ht
      rw [inverse_cons, run_append]
      apply LinearMap.ext
      intro v
      simp only [run, LinearMap.comp_apply, LinearMap.id_apply]
      have hv := congrArg (fun A : State w →ₗ[ℂ] State w => A (g.eval v)) hi
      change run (inverse gs) (run gs (g.eval v)) = g.eval v at hv
      rw [hv]
      exact congrArg (fun A : State w →ₗ[ℂ] State w => A v) (g.inverse_comp hg)

theorem run_comp_inverse (gs : List (Gate w)) (hgs : GatesValid gs) :
    (run gs).comp (run (inverse gs)) = LinearMap.id := by
  revert hgs
  induction gs with
  | nil => intro _; rfl
  | cons g gs ih =>
      intro hgs
      have hg := hgs g List.mem_cons_self
      have ht : GatesValid gs := fun q hq => hgs q (List.mem_cons_of_mem g hq)
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

/-- Reversing the actual valid tree traversal undoes its ideal action while
restoring the input prefix workspace. The later Hilbert-space lift must
still identify this full algebraic inverse with its operator adjoint. -/
theorem compile_inverse_intertwines {h : ℕ} (t : RotationTree h)
    (ht : t.Valid) (offset : ℕ) (hfit : offset + h ≤ w) (p : Word w) :
    (run (inverse (compile t offset hfit p))).comp
      ((embed p offset).comp (idealTraversal t offset hfit p)) = embed p offset := by
  rw [← compile_intertwines t offset hfit p, ← LinearMap.comp_assoc,
    run_inverse_comp _ (compile_valid t ht offset hfit p)]
  rfl

/-- The literal inverse retains the exact linear-size gate count. -/
theorem compile_inverse_length {h : ℕ} (t : RotationTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p : Word w) :
    (inverse (compile t offset hfit p)).length = 3 * (2 ^ h - 1) := by
  rw [inverse_length, compile_length]

end
end SparseHamiltonian.GateFilterTree


/-! ### Inactive branches of the actual table traversal -/

namespace SparseHamiltonian.GateFilterTree
noncomputable section

variable {w : ℕ}

/-- Once the word differs from the public path, choosing either child
cannot make the longer path match. -/
theorem child_prefix_inactive (p x : Word w) (j : Fin w) (b : Bool)
    (h : GatePrefixCircuit.prefixBit (twistWord p x) j.val = false) :
    GatePrefixCircuit.prefixBit (twistWord (Function.update p j b) x)
      (j.val + 1) = false := by
  rw [twistWord_path_update, GatePrefixCircuit.prefixBit,
    GatePrefixCircuit.prefix_update _ j _ j.val le_rfl, h]
  rfl

/-- A path-conditioned local rotation fixes an inactive basis amplitude. -/
theorem idealStep_single_inactive (p : Word w) (j : Fin w)
    (a : Coefficients) (x : Word w) (c : ℂ)
    (h : GatePrefixCircuit.prefixBit (twistWord p x) j.val = false) :
    idealStep p j a (Finsupp.single x c) = Finsupp.single x c := by
  simp [idealStep, idealBasis, h]

/-- Every descendant of an inactive tree is inactive. This supplies the
cross-branch identity needed when separately preparing the two children. -/
theorem idealTraversal_single_inactive {h : ℕ} (t : RotationTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p x : Word w) (c : ℂ)
    (hinactive : GatePrefixCircuit.prefixBit (twistWord p x) offset = false) :
    idealTraversal t offset hfit p (Finsupp.single x c) = Finsupp.single x c := by
  induction t generalizing offset p with
  | leaf => rfl
  | @node h a left right ihL ihR =>
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + h ≤ w := by omega
      have hleft : GatePrefixCircuit.prefixBit
          (twistWord (Function.update p j false) x) (offset + 1) = false :=
        child_prefix_inactive p x j false hinactive
      have hright : GatePrefixCircuit.prefixBit
          (twistWord (Function.update p j true) x) (offset + 1) = false :=
        child_prefix_inactive p x j true hinactive
      change idealTraversal right (offset + 1) hchild (Function.update p j true)
        (idealTraversal left (offset + 1) hchild (Function.update p j false)
          (idealStep p j a (Finsupp.single x c))) = _
      rw [idealStep_single_inactive p j a x c hinactive,
        ihL (offset + 1) hchild (Function.update p j false) hleft,
        ihR (offset + 1) hchild (Function.update p j true) hright]

/-- The literal elementary gate list inherits the inactive-branch action,
including restoration of all flags belonging to this traversal. -/
theorem compile_inactive {h : ℕ} (t : RotationTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p x : Word w) (c : ℂ)
    (hinactive : GatePrefixCircuit.prefixBit (twistWord p x) offset = false) :
    run (compile t offset hfit p) (embed p offset (Finsupp.single x c)) =
      embed p offset (Finsupp.single x c) := by
  have he := congrArg
    (fun F : GatePrefixCircuit.SlotState w →ₗ[ℂ] State w => F (Finsupp.single x c))
    (compile_intertwines t offset hfit p)
  change run (compile t offset hfit p) (embed p offset (Finsupp.single x c)) =
    embed p offset (idealTraversal t offset hfit p (Finsupp.single x c)) at he
  rw [idealTraversal_single_inactive t offset hfit p x c hinactive] at he
  exact he

end
end SparseHamiltonian.GateFilterTree


/-! ### Coordinates of the actual mixed-path rotation specification

The operator is the same `idealStep` already
proved to be implemented by the literal compute/rotate/uncompute circuit.
These lemmas supply the row-action formula needed for the table-amplitude
induction; they introduce no new implementation hypotheses.
-/

namespace SparseHamiltonian.GateFilterTree
noncomputable section
open scoped BigOperators

variable {w : ℕ}

theorem pathPrefix_update (p x : Word w) (j : Fin w) (b : Bool)
    (n : ℕ) (hn : n ≤ j.val) :
    GatePrefixCircuit.prefixBit (twistWord p (Function.update x j b)) n =
      GatePrefixCircuit.prefixBit (twistWord p x) n := by
  rw [twistWord_update]
  exact GatePrefixCircuit.prefix_update (twistWord p x) j
    (if p j then !b else b) n hn

private theorem sum_single_update_input (j : Fin w) (x y : Word w)
    (c : ℂ) (t : Bool → ℂ) :
    (∑ b : Bool, t b * (Finsupp.single y c) (Function.update x j b)) =
      t (y j) * (Finsupp.single y c) (Function.update x j (y j)) := by
  classical
  apply Finset.sum_eq_single (y j)
  · intro b hb hne
    have hword : y ≠ Function.update x j b := by
      intro h
      have hh := congrFun h j
      simp only [Function.update_self] at hh
      exact hne hh.symm
    simp [hword]
  · simp

private theorem sum_single_update_output (j : Fin w) (x y : Word w)
    (c : ℂ) (t : Bool → ℂ) :
    (∑ b : Bool, t b * (Finsupp.single (Function.update y j b) c) x) =
      t (x j) * (Finsupp.single (Function.update y j (x j)) c) x := by
  classical
  apply Finset.sum_eq_single (x j)
  · intro b hb hne
    have hword : Function.update y j b ≠ x := by
      intro h
      have hh := congrFun h j
      simp only [Function.update_self] at hh
      exact hne hh
    simp [hword]
  · simp

/-- Complete row-action formula for a mixed-path controlled node. The
predicate is evaluated on the output word; the target-bit update cannot
change it because the predicate reads only strictly earlier bits. -/
theorem idealStep_apply (p : Word w) (j : Fin w) (a : Coefficients)
    (f : GatePrefixCircuit.SlotState w) (x : Word w) :
    (idealStep p j a f) x =
      if GatePrefixCircuit.prefixBit (twistWord p x) j.val then
        ∑ b : Bool, a (x j) b * f (Function.update x j b)
      else f x := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add]
      simp only [Finsupp.add_apply, hf, hg]
      cases hp : GatePrefixCircuit.prefixBit (twistWord p x) j.val <;>
        simp [mul_add, Finset.sum_add_distrib]
  | single y c =>
      simp only [idealStep, Finsupp.linearCombination_single, Finsupp.smul_apply,
        smul_eq_mul, idealBasis]
      by_cases he : Function.update y j (x j) = x
      · have hp : GatePrefixCircuit.prefixBit (twistWord p y) j.val =
            GatePrefixCircuit.prefixBit (twistWord p x) j.val := by
          calc
            GatePrefixCircuit.prefixBit (twistWord p y) j.val =
                GatePrefixCircuit.prefixBit
                  (twistWord p (Function.update y j (x j))) j.val :=
              (pathPrefix_update p y j (x j) j.val le_rfl).symm
            _ = GatePrefixCircuit.prefixBit (twistWord p x) j.val :=
              congrArg (fun z => GatePrefixCircuit.prefixBit (twistWord p z) j.val) he
        have he' := (GatePrefixCircuit.update_exchange j x y).mp he
        cases h : GatePrefixCircuit.prefixBit (twistWord p x) j.val
        · simp [hp, h, Finsupp.single_apply]
        · simp only [hp, h, if_true, Finsupp.finsetSum_apply,
            Finsupp.smul_apply, smul_eq_mul]
          rw [sum_single_update_output, sum_single_update_input]
          simp only [Finsupp.single_apply, if_pos he, if_pos he', mul_one]
          ring
      · have he' : y ≠ Function.update x j (y j) := by
          intro h
          exact he ((GatePrefixCircuit.update_exchange j x y).mpr h)
        have hxy : y ≠ x := by
          intro h
          subst y
          exact he (Function.update_eq_self j x)
        cases hp : GatePrefixCircuit.prefixBit (twistWord p y) j.val <;>
          cases hx : GatePrefixCircuit.prefixBit (twistWord p x) j.val
          <;> simp only [Bool.false_eq_true, if_true, if_false,
            Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
          <;> (try simp only [sum_single_update_output, sum_single_update_input])
          <;> simp only [Finsupp.single_apply, if_neg he, if_neg he', if_neg hxy,
            mul_zero]

/-- A node acts as the identity on every amplitude coordinate outside its
own path prefix; sibling subtrees therefore have disjoint active sectors. -/
theorem idealStep_apply_inactive (p : Word w) (j : Fin w) (a : Coefficients)
    (f : GatePrefixCircuit.SlotState w) (x : Word w)
    (hx : GatePrefixCircuit.prefixBit (twistWord p x) j.val = false) :
    idealStep p j a f x = f x := by
  simp only [idealStep_apply, hx, Bool.false_eq_true, if_false]

end
end SparseHamiltonian.GateFilterTree



/-! ### Exact square-root amplitudes of the compiled filter table

The induction starts with the square root of the actual root mass.  It
therefore also covers empty subtrees without dividing by a zero mass.
-/

namespace SparseHamiltonian.GateFilterTree
noncomputable section
open scoped BigOperators

variable {w : ℕ}

/-- The path control recognises literal agreement with the known path on
the preceding wires. -/
theorem pathPrefix_true_iff (p x : Word w) (n : ℕ) (hn : n ≤ w) :
    GatePrefixCircuit.prefixBit (twistWord p x) n = true ↔
      ∀ j : Fin w, j.val < n → x j = p j := by
  rw [GatePrefixCircuit.prefix_true_iff _ n hn]
  constructor
  · intro h j hj
    have hh := h j hj
    cases hp : p j <;> cases hx : x j <;> simp [twistWord, hp, hx] at hh ⊢
  · intro h j hj
    change (if p j then !(x j) else x j) = false
    rw [h j hj]
    cases hp : p j <;> simp

/-- A disagreement on even one preceding bit makes the path inactive. -/
theorem pathPrefix_false_of_ne (p x : Word w) (n : ℕ) (hn : n ≤ w)
    (j : Fin w) (hj : j.val < n) (hne : x j ≠ p j) :
    GatePrefixCircuit.prefixBit (twistWord p x) n = false := by
  cases hp : GatePrefixCircuit.prefixBit (twistWord p x) n
  · rfl
  · exact False.elim (hne ((pathPrefix_true_iff p x n hn).mp hp j hj))

/-- After choosing one child, both the path and the state word contain the
same chosen bit; all earlier path tests are unchanged. -/
theorem child_prefix_active (p x : Word w) (j : Fin w) (b : Bool)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p x) j.val = true) :
    GatePrefixCircuit.prefixBit
      (twistWord (Function.update p j b) (Function.update x j b))
      (j.val + 1) = true := by
  apply (pathPrefix_true_iff _ _ _ (by omega)).mpr
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp only [Function.update_self]
  · have hlt : k.val < j.val := by
      have hne : k.val ≠ j.val := fun hh => hkj (Fin.ext hh)
      omega
    rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
    exact (pathPrefix_true_iff p x j.val (Nat.le_of_lt j.isLt)).mp hactive k hlt

/-- Recursive square-root leaf table, with the tree's bits written into a
window of a larger register.  The untouched wires retain `seed` exactly. -/
def MassTree.leafState : {h : ℕ} → MassTree h →
    (offset : ℕ) → offset + h ≤ w → Word w → GatePrefixCircuit.SlotState w
  | 0, .leaf a _, _, _, seed => Finsupp.single seed (Real.sqrt a : ℂ)
  | h + 1, .node left right, offset, hfit, seed =>
      let j : Fin w := ⟨offset, by omega⟩
      let hchild : offset + 1 + h ≤ w := by omega
      left.leafState (offset + 1) hchild (Function.update seed j false) +
        right.leafState (offset + 1) hchild (Function.update seed j true)

/-- A linear operator fixing every basis vector with the prescribed
preceding bits also fixes the whole leaf table.  This is only a support
lemma: no preparation or implementation property is assumed. -/
theorem MassTree.leafState_fixed {h : ℕ} (t : MassTree h) (offset : ℕ)
    (hfit : offset + h ≤ w) (seed : Word w)
    (F : GatePrefixCircuit.SlotState w →ₗ[ℂ] GatePrefixCircuit.SlotState w)
    (hF : ∀ x : Word w, (∀ i : Fin w, i.val < offset → x i = seed i) →
      ∀ c : ℂ, F (Finsupp.single x c) = Finsupp.single x c) :
    F (t.leafState offset hfit seed) = t.leafState offset hfit seed := by
  induction t generalizing offset seed with
  | leaf a ha =>
      exact hF seed (fun _ _ => rfl) _
  | @node h left right ihL ihR =>
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + h ≤ w := by omega
      have hchildF (b : Bool) (x : Word w)
          (hx : ∀ i : Fin w, i.val < offset + 1 →
            x i = Function.update seed j b i) (c : ℂ) :
          F (Finsupp.single x c) = Finsupp.single x c := by
        apply hF x
        intro i hi
        have hij : i ≠ j := by
          intro he
          have hv := congrArg Fin.val he
          dsimp [j] at hv
          omega
        rw [hx i (by omega), Function.update_of_ne hij]
      change F (left.leafState (offset + 1) hchild (Function.update seed j false) +
          right.leafState (offset + 1) hchild (Function.update seed j true)) = _
      rw [map_add, ihL (offset + 1) hchild (Function.update seed j false)
        (hchildF false), ihR (offset + 1) hchild (Function.update seed j true)
        (hchildF true)]
      rfl

/-- First-column action of the actual conditional mass rotation.  The
square-root parent amplitude splits into the two square-root child masses
even when either mass, or their sum, is zero. -/
theorem MassTree.idealStep_split {h : ℕ} (left right : MassTree h)
    (p seed : Word w) (j : Fin w)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p seed) j.val = true)
    (hzero : seed j = false) :
    idealStep p j (GateTableSplit.coefficients left.mass right.mass)
        (Finsupp.single seed (Real.sqrt (MassTree.node left right).mass : ℂ)) =
      Finsupp.single (Function.update seed j false) (Real.sqrt left.mass : ℂ) +
        Finsupp.single (Function.update seed j true) (Real.sqrt right.mass : ℂ) := by
  classical
  simp only [idealStep, Finsupp.linearCombination_single, idealBasis,
    hactive, if_true, hzero]
  rw [Finset.smul_sum]
  simp only [smul_smul]
  have hsplit (b : Bool) :
      (Real.sqrt (MassTree.node left right).mass : ℂ) *
          GateTableSplit.coefficients left.mass right.mass b false =
        if b then (Real.sqrt right.mass : ℂ) else (Real.sqrt left.mass : ℂ) := by
    rw [mul_comm]
    exact MassTree.node_split left right b
  simp only [hsplit]
  simp [Finsupp.smul_single, smul_eq_mul, add_comm]

/-- Full table preparation by the path-conditioned tree already proved
equal to the literal bounded-arity circuit.  The only hypotheses on the
input are an active public path and zero bits in the tree's own window. -/
theorem MassTree.idealTraversal_prepares {h : ℕ} (t : MassTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p seed : Word w)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p seed) offset = true)
    (hzero : ∀ i : Fin w, offset ≤ i.val → i.val < offset + h → seed i = false) :
    idealTraversal t.rotations offset hfit p
        (Finsupp.single seed (Real.sqrt t.mass : ℂ)) =
      t.leafState offset hfit seed := by
  induction t generalizing offset p seed with
  | leaf a ha => rfl
  | @node h left right ihL ihR =>
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + h ≤ w := by omega
      let pL := Function.update p j false
      let pR := Function.update p j true
      let seedL := Function.update seed j false
      let seedR := Function.update seed j true
      have hLactive : GatePrefixCircuit.prefixBit (twistWord pL seedL)
          (offset + 1) = true := child_prefix_active p seed j false hactive
      have hRactive : GatePrefixCircuit.prefixBit (twistWord pR seedR)
          (offset + 1) = true := child_prefix_active p seed j true hactive
      have hchildZero (b : Bool) (i : Fin w) (hi : offset + 1 ≤ i.val)
          (hih : i.val < offset + 1 + h) : Function.update seed j b i = false := by
        have hij : i ≠ j := by
          intro he
          have hv := congrArg Fin.val he
          dsimp [j] at hv
          omega
        rw [Function.update_of_ne hij]
        exact hzero i (by omega) (by omega)
      have hcrossL : GatePrefixCircuit.prefixBit (twistWord pL seedR)
          (offset + 1) = false := by
        apply pathPrefix_false_of_ne pL seedR (offset + 1) (by omega) j
          (by simp [j])
        simp [pL, seedR]
      have hcrossR :
          idealTraversal right.rotations (offset + 1) hchild pR
            (left.leafState (offset + 1) hchild seedL) =
          left.leafState (offset + 1) hchild seedL := by
        apply left.leafState_fixed
        intro x hx c
        apply idealTraversal_single_inactive
        apply pathPrefix_false_of_ne pR x (offset + 1) (by omega) j
          (by simp [j])
        have hxj := hx j (by simp [j])
        simp [pR, seedL, hxj]
      change idealTraversal right.rotations (offset + 1) hchild pR
          (idealTraversal left.rotations (offset + 1) hchild pL
            (idealStep p j (GateTableSplit.coefficients left.mass right.mass)
              (Finsupp.single seed
                (Real.sqrt (MassTree.node left right).mass : ℂ)))) = _
      rw [MassTree.idealStep_split left right p seed j hactive
        (hzero j (by simp [j]) (by change offset < offset + (h + 1); omega))]
      rw [map_add, ihL (offset + 1) hchild pL seedL hLactive (hchildZero false),
        idealTraversal_single_inactive left.rotations (offset + 1) hchild
          pL seedR (Real.sqrt right.mass : ℂ) hcrossL,
        map_add, hcrossR,
        ihR (offset + 1) hchild pR seedR hRactive (hchildZero true)]
      rfl

/-- The actual elementary list prepares the complete square-root leaf
table and returns all prefix flags to their entrance values. -/
theorem MassTree.compile_prepares {h : ℕ} (t : MassTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p seed : Word w)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p seed) offset = true)
    (hzero : ∀ i : Fin w, offset ≤ i.val → i.val < offset + h → seed i = false) :
    run (compile t.rotations offset hfit p)
        (embed p offset (Finsupp.single seed (Real.sqrt t.mass : ℂ))) =
      embed p offset (t.leafState offset hfit seed) := by
  have he := congrArg (fun F : GatePrefixCircuit.SlotState w →ₗ[ℂ] State w =>
    F (Finsupp.single seed (Real.sqrt t.mass : ℂ)))
    (compile_intertwines t.rotations offset hfit p)
  change run (compile t.rotations offset hfit p)
      (embed p offset (Finsupp.single seed (Real.sqrt t.mass : ℂ))) =
    embed p offset (idealTraversal t.rotations offset hfit p
      (Finsupp.single seed (Real.sqrt t.mass : ℂ))) at he
  rw [t.idealTraversal_prepares offset hfit p seed hactive hzero] at he
  exact he

/-- Explicit coordinate placement of the table's logical bits. This is a
definition of the output labels, not an uncharged physical permutation. -/
def writeWindow : {h : ℕ} → (offset : ℕ) → offset + h ≤ w →
    Word h → Word w → Word w
  | 0, _, _, _, seed => seed
  | h + 1, offset, hfit, x, seed =>
      let j : Fin w := ⟨offset, by omega⟩
      writeWindow (offset + 1) (by omega) (fun i => x i.succ)
        (Function.update seed j (x 0))

theorem sum_words_succ_add {A : Type*} [AddCommMonoid A]
    (h : ℕ) (a : Word (h + 1) → A) :
    (∑ x : Word (h + 1), a x) =
      (∑ x : Word h, a (Fin.cons false x)) +
        ∑ x : Word h, a (Fin.cons true x) := by
  calc
    (∑ x : Word (h + 1), a x) =
        ∑ q : Bool × Word h, a (Fin.cons q.1 q.2) :=
      (Fintype.sum_equiv (wordHeadTail h).symm _ _ (fun _ => rfl)).symm
    _ = _ := by
      simp only [Fintype.sum_prod_type, Fintype.sum_bool]
      ac_rfl

/-- The recursive output above is exactly the leaf table with square-root
coefficients, rather than merely a recursively specified target state. -/
theorem MassTree.leafState_eq_sum {h : ℕ} (t : MassTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (seed : Word w) :
    t.leafState offset hfit seed =
      ∑ x : Word h, Finsupp.single (writeWindow offset hfit x seed)
        (Real.sqrt (t.value x) : ℂ) := by
  induction t generalizing offset seed with
  | leaf a ha =>
      simp [MassTree.leafState, MassTree.value, writeWindow,
        Word, GatePrefixCircuit.Word]
  | @node h left right ihL ihR =>
      rw [sum_words_succ_add]
      simp only [MassTree.leafState, MassTree.value, writeWindow,
        Fin.cons_zero, Fin.cons_succ, Bool.false_eq_true, 
        if_false, if_true]
      rw [ihL, ihR]

/-- A known unit-mass nonnegative table is prepared from a single clean
word by the actual `3 * (2^h - 1)`-gate list; no abstract state loader occurs
in the statement or proof. -/
theorem MassTree.compile_table {h : ℕ} (a : Word h → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1)
    (offset : ℕ) (hfit : offset + h ≤ w) (p seed : Word w)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p seed) offset = true)
    (hzero : ∀ i : Fin w, offset ≤ i.val → i.val < offset + h → seed i = false) :
    run (compile (MassTree.fromTable h a ha).rotations offset hfit p)
        (embed p offset (Finsupp.single seed 1)) =
      embed p offset (∑ x : Word h,
        Finsupp.single (writeWindow offset hfit x seed) (Real.sqrt (a x) : ℂ)) := by
  have he := (MassTree.fromTable h a ha).compile_prepares
    offset hfit p seed hactive hzero
  rw [MassTree.fromTable_mass, hmass, Real.sqrt_one, Complex.ofReal_one,
    MassTree.leafState_eq_sum] at he
  simpa only [MassTree.fromTable_value] using he

/-- The literal reversed circuit unprepares the same square-root table,
returning the seed and its complete prefix workspace exactly. -/
theorem MassTree.compile_table_inverse {h : ℕ} (a : Word h → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1)
    (offset : ℕ) (hfit : offset + h ≤ w) (p seed : Word w)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p seed) offset = true)
    (hzero : ∀ i : Fin w, offset ≤ i.val → i.val < offset + h → seed i = false) :
    run (inverse (compile (MassTree.fromTable h a ha).rotations offset hfit p))
        (embed p offset (∑ x : Word h,
          Finsupp.single (writeWindow offset hfit x seed) (Real.sqrt (a x) : ℂ))) =
      embed p offset (Finsupp.single seed 1) := by
  rw [← MassTree.compile_table a ha hmass offset hfit p seed hactive hzero]
  exact congrArg (fun F : State w →ₗ[ℂ] State w =>
    F (embed p offset (Finsupp.single seed 1)))
    (run_inverse_comp _ ((MassTree.fromTable h a ha).compile_valid offset hfit p))

/-- The table preparation does not change any wire outside its declared
window; in particular it cannot disturb a previously selected branch. -/
theorem writeWindow_outside {h : ℕ} (offset : ℕ) (hfit : offset + h ≤ w)
    (x : Word h) (seed : Word w) (i : Fin w)
    (hi : i.val < offset ∨ offset + h ≤ i.val) :
    writeWindow offset hfit x seed i = seed i := by
  induction h generalizing offset seed with
  | zero => rfl
  | succ h ih =>
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + h ≤ w := by omega
      have houtside : i.val < offset + 1 ∨ offset + 1 + h ≤ i.val := by omega
      have hij : i ≠ j := by
        intro he
        have hv := congrArg Fin.val he
        dsimp [j] at hv
        omega
      change writeWindow (offset + 1) hchild (fun k => x k.succ)
        (Function.update seed j (x 0)) i = seed i
      rw [ih (offset + 1) hchild (fun k => x k.succ)
        (Function.update seed j (x 0)) houtside, Function.update_of_ne hij]

/-- Reading a wire inside the output window gives precisely its logical
table bit. This fixes the bit order explicitly, independently of a finite
enumeration or a chosen equivalence. -/
theorem writeWindow_inside {h : ℕ} (offset : ℕ) (hfit : offset + h ≤ w)
    (x : Word h) (seed : Word w) (k : Fin h) :
    writeWindow offset hfit x seed ⟨offset + k.val, by omega⟩ = x k := by
  induction h generalizing offset seed with
  | zero => exact Fin.elim0 k
  | succ h ih =>
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + h ≤ w := by omega
      refine Fin.cases ?_ (fun k => ?_) k
      · change writeWindow (offset + 1) hchild (fun l => x l.succ)
          (Function.update seed j (x 0)) j = x 0
        rw [writeWindow_outside (offset + 1) hchild (fun l => x l.succ)
          (Function.update seed j (x 0)) j (Or.inl (by simp [j]))]
        simp only [Function.update_self]
      · change writeWindow (offset + 1) hchild (fun l => x l.succ)
          (Function.update seed j (x 0)) ⟨offset + (k.val + 1), by omega⟩ = x k.succ
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          ih (offset + 1) hchild (fun l => x l.succ)
            (Function.update seed j (x 0)) k

theorem writeWindow_injective {h : ℕ} (offset : ℕ) (hfit : offset + h ≤ w)
    (seed : Word w) : Function.Injective (fun x : Word h =>
      writeWindow offset hfit x seed) := by
  intro x y hxy
  funext k
  have he := congrFun hxy (⟨offset + k.val, by omega⟩ : Fin w)
  simpa only [writeWindow_inside] using he

/-- If the table occupies the entire register, its physical word is
literally its logical word. No final permutation is needed. -/
theorem writeWindow_full (x seed : Word w) :
    writeWindow 0 (show 0 + w ≤ w by omega) x seed = x := by
  funext k
  simpa only [Nat.zero_add] using
    writeWindow_inside 0 (show 0 + w ≤ w by omega) x seed k

/-- Every individual prepared coordinate is the square root of its actual
leaf mass; injectivity rules out accidental amplitude addition. -/
theorem MassTree.leafState_coordinate {h : ℕ} (t : MassTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (seed : Word w) (x : Word h) :
    t.leafState offset hfit seed (writeWindow offset hfit x seed) =
      (Real.sqrt (t.value x) : ℂ) := by
  classical
  rw [t.leafState_eq_sum]
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y hy hne
    have hword : writeWindow offset hfit y seed ≠ writeWindow offset hfit x seed :=
      fun he => hne (writeWindow_injective offset hfit seed he)
    simp [Ne.symm hword]
  · simp

/-- Complete clean-register preparation of an arbitrary known probability
table in its literal Boolean basis. All prefix ancillas start and end zero,
because the embedding depth is zero. -/
theorem MassTree.compile_full_table (a : Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1) :
    run (compile (MassTree.fromTable w a ha).rotations 0 (by omega)
        (fun _ => false))
      (embed (fun _ => false) 0 (Finsupp.single (fun _ => false) 1)) =
    embed (fun _ => false) 0
      (∑ x : Word w, Finsupp.single x (Real.sqrt (a x) : ℂ)) := by
  have he := MassTree.compile_table a ha hmass 0 (show 0 + w ≤ w by omega)
    (fun _ => false) (fun _ => false) rfl (fun _ _ _ => rfl)
  simpa only [writeWindow_full] using he

/-- Exact unpreparation of the same full-register probability table by
the reverse of the very same elementary gate list. -/
theorem MassTree.compile_full_table_inverse (a : Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1) :
    run (inverse (compile (MassTree.fromTable w a ha).rotations 0 (by omega)
        (fun _ => false)))
      (embed (fun _ => false) 0
        (∑ x : Word w, Finsupp.single x (Real.sqrt (a x) : ℂ))) =
    embed (fun _ => false) 0 (Finsupp.single (fun _ => false) 1) := by
  have he := MassTree.compile_table_inverse a ha hmass 0 (show 0 + w ≤ w by omega)
    (fun _ => false) (fun _ => false) rfl (fun _ _ _ => rfl)
  simpa only [writeWindow_full] using he

end
end SparseHamiltonian.GateFilterTree
