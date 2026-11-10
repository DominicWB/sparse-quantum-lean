import SparseLowerBounds.Hamiltonian.DataBuilder

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Native primitives of one-bit data from Boolean queries

Manuscript: the chain construction of Section `part:hsl` (and the QLS analogue, proof of Theorem
`qlsl:thm:main`). For data
built by `bitData` from a one-bit word table `T` and hidden bits `y x`, every
native primitive (`NativeSparseBlockEncoding.oracles`) is implemented exactly,
on the clean-ancilla encoding `v ↦ |0⟩ ⊗ v` (`ancillaEmbed`), by a program over
the Boolean phase oracle `x ↦ (bitBooleanFamily T Z).phase (y x)`:

* the row and column **location** oracles are input-independent permutation
  unitaries, hence fixed gates: **0** Boolean queries
  (`oracles_bitData_rowLocation`, `oracles_bitData_columnLocation`);
* the **value** oracle costs **2** Boolean queries: query the one bit the address depends on into
  the ancilla, add the word selected by that bit (a fixed gate, `bitWordGate`), unquery (the chain
  construction of Section `part:hsl`). Known words make no query. The two branch identities of
  `PhaseCircuit.circuit_intertwines` are `bitValue_branch_zero/one` (and
  `bitValue_spec_branch_zero/one` with a spectator); at a single address the value oracle *is* the
  word gate of the queried bit (`oracles_bitData_value_apply_eq_gate`).

`Π_i` (`bitAddressFamily`) projects onto the addresses whose word depends on
bit `i`; the Boolean family is `|−⟩⟨−| ⊗ Π_i` (`ProjFamily.withAncilla`), so its
phase oracle is the XOR oracle `|a, z⟩ ↦ |a, z ⊕ y_{addr a}⟩` in the Hadamard
basis of the ancilla. For the search families `y j (k, a) = [j k = a]` and the
phase oracle is literally `oneHotOracle`; for the scalar family `y x = x` and it
is `bitOracle` (both by `rfl`, see `Hamiltonian/Native`).

Inverse value queries are covered by `EncodedMultiOracle.compile` (adjoint
circuit, again 2 queries), since the release value oracle is additive. All of
this holds with an untouched spectator register (`specOracles`,
`implementsOn_bitData_spec`). The generic query–gate–unquery circuit is
`Query/PhaseCircuit`.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit

variable {N I : Type*} [Fintype N] [DecidableEq N] [Fintype I] [DecidableEq I]

/-- `Π_i`: the addresses whose word depends on bit `i`. -/
def bitAddressFamily (T : BitTable I (N × N)) (Z : Type*) [Fintype Z] :
    ProjFamily (SparseFlagEmbedding.Space (N × N) Z) I where
  proj i := Joint.fiber fun az => if T.addr az.1 = some i then 1 else 0
  isStarProjection := by
    intro i
    refine ⟨?_, ?_⟩
    · change Joint.fiber _ * Joint.fiber _ = Joint.fiber _
      rw [Joint.fiber_mul]
      congr 1
      funext az
      split_ifs <;> simp
    · change star (Joint.fiber _) = Joint.fiber _
      rw [Joint.star_fiber]
      congr 1
      funext az
      split_ifs <;> simp
  orthogonal := by
    intro i i' hne
    refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun az => ?_
    change (if T.addr az.1 = some i then (1 : SparseFlagEmbedding.Qutrit →L[ℂ] _) else 0)
      ((if T.addr az.1 = some i' then (1 : SparseFlagEmbedding.Qutrit →L[ℂ] _) else 0)
        (Ψ az)) = 0
    split_ifs with h₁ h₂
    · exact absurd (Option.some_injective _ (h₁.symm.trans h₂)) hne
    all_goals simp

/-- The Boolean XOR oracle in phase form on ancilla ⊗ native space. -/
def bitBooleanFamily (T : BitTable I (N × N)) (Z : Type*) [Fintype Z] :
    ProjFamily (Joint (Fin 2) (SparseFlagEmbedding.Space (N × N) Z)) I :=
  (bitAddressFamily T Z).withAncilla

/-- The same with an untouched spectator register `ℂ^Ω`. -/
def bitSpecFamily (Ω : Type*) [Fintype Ω] (T : BitTable I (N × N)) (Z : Type*) [Fintype Z] :
    ProjFamily (Joint (Fin 2) (Joint Ω (SparseFlagEmbedding.Space (N × N) Z))) I :=
  ((bitAddressFamily T Z).spectate Ω).withAncilla

/-! ### The marked part of the native workspace -/

section Marked

variable {Z : Type*} [Fintype Z]

omit [DecidableEq N] [Fintype I] in
theorem bitAddressFamily_proj_apply (T : BitTable I (N × N)) (i : I)
    (v : SparseFlagEmbedding.Space (N × N) Z) (az : (N × N) × Z) :
    (bitAddressFamily T Z).proj i v az = if T.addr az.1 = some i then v az else 0 := by
  change (if T.addr az.1 = some i then (1 : SparseFlagEmbedding.Qutrit →L[ℂ] _) else 0)
    (v az) = _
  split_ifs <;> simp

omit [DecidableEq N] in
/-- The part of the workspace marked by the hidden bits `y`: the addresses whose
queried bit is set. -/
theorem hitProj_bitAddress_apply (T : BitTable I (N × N)) (y : I → Bool)
    (v : SparseFlagEmbedding.Space (N × N) Z) (az : (N × N) × Z) :
    PhaseCircuit.hitProj (bitAddressFamily T Z) y v az =
      if T.bit y az.1 = true then v az else 0 := by
  rw [PhaseCircuit.hitProj_apply, PhaseCircuit.joint_sum_apply]
  simp only [bitAddressFamily_proj_apply]
  unfold BitTable.bit
  cases h : T.addr az.1 with
  | none => simp
  | some i =>
    simp only [Option.some.injEq]
    rw [Finset.sum_ite_eq]
    simp

end Marked

/-! ### The value circuit: fixed word gates selected by the queried bit -/

section ValueCircuit

omit [DecidableEq N] [Fintype I] [DecidableEq I]

/-- The fixed gate adding, at every address `a`, the word `T.word a b` of the
known bit value `b`. -/
def bitWordGate (T : BitTable I (N × N)) (B : ℕ) (b : Bool) :
    SparseFlagEmbedding.Space (N × N) (Word B) →L[ℂ] SparseFlagEmbedding.Space (N × N) (Word B) :=
  LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) (X := Unit)
    (fun _ a => ((T.word a b : ℤ) : Word B)) ()

theorem bitWordGate_apply (T : BitTable I (N × N)) (B : ℕ) (b : Bool)
    (v : SparseFlagEmbedding.Space (N × N) (Word B)) (a : N × N) (z : Word B) :
    bitWordGate T B b v (a, z) = v (a, z - ((T.word a b : ℤ) : Word B)) := rfl

theorem bitWordGate_unitary (T : BitTable I (N × N)) (B : ℕ) (b : Bool) :
    IsUnitary (bitWordGate T B b) :=
  LookupControlledGate.oracle_unitary _ ()

/-- The two branch gates, selected by the ancilla (`0 ↦ false`, `1 ↦ true`). -/
def bitBranchGate (T : BitTable I (N × N)) (B : ℕ) :
    Fin 2 → SparseFlagEmbedding.Space (N × N) (Word B) →L[ℂ]
      SparseFlagEmbedding.Space (N × N) (Word B) :=
  ![bitWordGate T B false, bitWordGate T B true]

theorem bitBranchGate_zero (T : BitTable I (N × N)) (B : ℕ) :
    bitBranchGate T B 0 = bitWordGate T B false := rfl

theorem bitBranchGate_one (T : BitTable I (N × N)) (B : ℕ) :
    bitBranchGate T B 1 = bitWordGate T B true := rfl

theorem bitBranchGate_unitary (T : BitTable I (N × N)) (B : ℕ) (b : Fin 2) :
    IsUnitary (bitBranchGate T B b) := by
  fin_cases b <;> exact bitWordGate_unitary _ _ _

end ValueCircuit

/-! ### The native primitives of `bitData` -/

section Primitives

variable {X : Type*} {s B : ℕ} {hs : 0 < s} {slot : Fin s ↪ N} {loc : N → Fin s ↪ N}
  {T : BitTable I (N × N)} {y : X → I → Bool} {H : X → Matrix N N ℂ}
  {hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B}
  {hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j}
  {hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i)}
  {hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)}

omit [Fintype I] [DecidableEq I] in
/-- The row location primitive is one fixed unitary (the chain construction of Section
`part:hsl`). -/
theorem oracles_bitData_rowLocation (x : X) :
    oracles (bitData s B hs slot loc T y H hbound hdec hrow hcol) .rowLocation x =
      SparseFlagEmbedding.location (Z := Word B) (fun _ : Unit => permCLM (rowEquiv slot loc)) () :=
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The column location primitive is one fixed unitary (the chain construction of Section
`part:hsl`). -/
theorem oracles_bitData_columnLocation (x : X) :
    oracles (bitData s B hs slot loc T y H hbound hdec hrow hcol) .columnLocation x =
      SparseFlagEmbedding.location (Z := Word B) (fun _ : Unit => permCLM (colEquiv slot loc)) () :=
  rfl

omit [Fintype I] [DecidableEq I] in
/-- The value primitive adds the word of the queried bit. -/
theorem oracles_bitData_value_apply (x : X) (v : SparseFlagEmbedding.Space (N × N) (Word B))
    (a : N × N) (z : Word B) :
    oracles (bitData s B hs slot loc T y H hbound hdec hrow hcol) .value x v (a, z) =
      v (a, z - ((T.value (y x) a : ℤ) : Word B)) := rfl

omit [Fintype I] [DecidableEq I] in
/-- **Per address, the value oracle is the word gate of the queried bit.** -/
theorem oracles_bitData_value_apply_eq_gate (x : X)
    (v : SparseFlagEmbedding.Space (N × N) (Word B)) (a : N × N) (z : Word B) :
    oracles (bitData s B hs slot loc T y H hbound hdec hrow hcol) .value x v (a, z) =
      bitWordGate T B (T.bit (y x) a) v (a, z) := rfl

/-- **Branch identity `0`** of `PhaseCircuit.circuit_intertwines` for the value
oracle: unmarked addresses get the `false` word, marked ones the `true` word. -/
theorem bitValue_branch_zero (x : X) (v : SparseFlagEmbedding.Space (N × N) (Word B)) :
    bitBranchGate T B 0 (v - PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x) v) -
        PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x)
          (bitBranchGate T B 0 (v - PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x) v)) +
        PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x)
          (bitBranchGate T B 1 (PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x) v)) =
      oracles (bitData s B hs slot loc T y H hbound hdec hrow hcol) .value x v := by
  refine PiLp.ext fun az => ?_
  obtain ⟨a, z⟩ := az
  simp only [PiLp.add_apply, PiLp.sub_apply, hitProj_bitAddress_apply, bitBranchGate_zero,
    bitBranchGate_one, bitWordGate_apply, oracles_bitData_value_apply, BitTable.value]
  cases T.bit (y x) a <;> simp

omit [DecidableEq N] in
/-- **Branch identity `1`**: the ancilla returns clean. -/
theorem bitValue_branch_one (x : X) (v : SparseFlagEmbedding.Space (N × N) (Word B)) :
    bitBranchGate T B 1 (PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x) v) -
        PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x)
          (bitBranchGate T B 1 (PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x) v)) +
        PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x)
          (bitBranchGate T B 0 (v - PhaseCircuit.hitProj (bitAddressFamily T (Word B)) (y x) v)) =
      0 := by
  refine PiLp.ext fun az => ?_
  obtain ⟨a, z⟩ := az
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply, hitProj_bitAddress_apply,
    bitBranchGate_zero, bitBranchGate_one, bitWordGate_apply]
  cases T.bit (y x) a <;> simp

/-- Branch identity `0` with an untouched spectator register `ℂ^Ω`. -/
theorem bitValue_spec_branch_zero (Ω : Type*) [Fintype Ω] (x : X)
    (v : Joint Ω (SparseFlagEmbedding.Space (N × N) (Word B))) :
    Joint.fiber (fun _ : Ω => bitBranchGate T B 0)
          (v - PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x) v) -
        PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x)
          (Joint.fiber (fun _ : Ω => bitBranchGate T B 0)
            (v - PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x) v)) +
        PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x)
          (Joint.fiber (fun _ : Ω => bitBranchGate T B 1)
            (PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x) v)) =
      specOracles Ω (bitData s B hs slot loc T y H hbound hdec hrow hcol) .value x v := by
  refine PiLp.ext fun ω => ?_
  simp only [PiLp.add_apply, PiLp.sub_apply, PhaseCircuit.hitProj_spectate_apply,
    Joint.fiber_apply]
  exact bitValue_branch_zero x (v ω)

omit [DecidableEq N] in
/-- Branch identity `1` with an untouched spectator register `ℂ^Ω`. -/
theorem bitValue_spec_branch_one (Ω : Type*) [Fintype Ω] (x : X)
    (v : Joint Ω (SparseFlagEmbedding.Space (N × N) (Word B))) :
    Joint.fiber (fun _ : Ω => bitBranchGate T B 1)
          (PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x) v) -
        PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x)
          (Joint.fiber (fun _ : Ω => bitBranchGate T B 1)
            (PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x) v)) +
        PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x)
          (Joint.fiber (fun _ : Ω => bitBranchGate T B 0)
            (v - PhaseCircuit.hitProj ((bitAddressFamily T (Word B)).spectate Ω) (y x) v)) =
      0 := by
  refine PiLp.ext fun ω => ?_
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply,
    PhaseCircuit.hitProj_spectate_apply, Joint.fiber_apply]
  exact bitValue_branch_one x (v ω)

end Primitives

variable {X : Type*} {s B : ℕ}

/-- **Every native primitive of one-bit data is a `hardCost`-query Boolean
program** on the clean-ancilla encoding: `0` for the location oracles, `2` for
the value oracle (the chain construction of Section `part:hsl`). -/
theorem implementsOn_bitData (hs : 0 < s) (slot : Fin s ↪ N) (loc : N → Fin s ↪ N)
    (T : BitTable I (N × N)) (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) (l : Query) :
    EncodedOracle.ImplementsOn (fun x => (bitBooleanFamily T (Word B)).phase (y x))
      (oracles (bitData s B hs slot loc T y H hbound hdec hrow hcol) l)
      (ancillaEmbed (SparseFlagEmbedding.Space (N × N) (Word B))) (hardCost l) := by
  cases l with
  | rowLocation =>
    exact PhaseCircuit.implementsOn_of_eq _
      (SparseFlagEmbedding.location_unitary (Z := Word B)
        (fun _ : Unit => permCLM (rowEquiv slot loc)) (fun _ => isUnitary_permCLM _) ())
      fun x => oracles_bitData_rowLocation x
  | columnLocation =>
    exact PhaseCircuit.implementsOn_of_eq _
      (SparseFlagEmbedding.location_unitary (Z := Word B)
        (fun _ : Unit => permCLM (colEquiv slot loc)) (fun _ => isUnitary_permCLM _) ())
      fun x => oracles_bitData_columnLocation x
  | value =>
    exact PhaseCircuit.implementsOn_circuit (bitAddressFamily T (Word B)) y (bitBranchGate T B)
      (bitBranchGate_unitary T B)
      (oracles (bitData s B hs slot loc T y H hbound hdec hrow hcol) .value)
      (fun x v => bitValue_branch_zero x v) (fun x v => bitValue_branch_one x v)

/-- **Spectator form**: the same costs for the primitives acting on every copy
of an untouched spectator register. -/
theorem implementsOn_bitData_spec (Ω : Type*) [Fintype Ω] (hs : 0 < s) (slot : Fin s ↪ N)
    (loc : N → Fin s ↪ N) (T : BitTable I (N × N)) (y : X → I → Bool) (H : X → Matrix N N ℂ)
    (hbound : ∀ a b, -(2 : ℤ) ^ B < T.word a b ∧ T.word a b ≤ 2 ^ B)
    (hdec : ∀ x i j, ((T.value (y x) (i, j) : ℤ) : ℂ) / 2 ^ B = H x i j)
    (hrow : ∀ x i j, H x i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ x i j, H x i j ≠ 0 → i ∈ Set.range (loc j)) (l : Query) :
    EncodedOracle.ImplementsOn (fun x => (bitSpecFamily Ω T (Word B)).phase (y x))
      (specOracles Ω (bitData s B hs slot loc T y H hbound hdec hrow hcol) l)
      (ancillaEmbed (Joint Ω (SparseFlagEmbedding.Space (N × N) (Word B)))) (hardCost l) := by
  cases l with
  | rowLocation =>
    exact PhaseCircuit.implementsOn_of_eq _
      (PhaseCircuit.isUnitary_fiber _ fun _ : Ω =>
        SparseFlagEmbedding.location_unitary (Z := Word B)
          (fun _ : Unit => permCLM (rowEquiv slot loc)) (fun _ => isUnitary_permCLM _) ())
      fun x => rfl
  | columnLocation =>
    exact PhaseCircuit.implementsOn_of_eq _
      (PhaseCircuit.isUnitary_fiber _ fun _ : Ω =>
        SparseFlagEmbedding.location_unitary (Z := Word B)
          (fun _ : Unit => permCLM (colEquiv slot loc)) (fun _ => isUnitary_permCLM _) ())
      fun x => rfl
  | value =>
    exact PhaseCircuit.implementsOn_circuit ((bitAddressFamily T (Word B)).spectate Ω) y
      (fun b => Joint.fiber fun _ : Ω => bitBranchGate T B b)
      (fun b => PhaseCircuit.isUnitary_fiber _ fun _ => bitBranchGate_unitary T B b)
      (specOracles Ω (bitData s B hs slot loc T y H hbound hdec hrow hcol) .value)
      (fun x v => bitValue_spec_branch_zero Ω x v) (fun x v => bitValue_spec_branch_one Ω x v)

end

end SparseLowerBounds.Hamiltonian
end
