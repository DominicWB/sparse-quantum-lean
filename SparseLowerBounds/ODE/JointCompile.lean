import SparseLowerBounds.ODE.JointInstance

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The sampled-time access of the joint family from membership queries

Manuscript: the construction before Theorem `odel:thm:joint`, "A value query computes one relevant
membership bit, writes the known entry and uncomputes the bit. It therefore uses at most two
membership queries, also for inverse and controlled calls." For the joint family
(`ODE/JointInstance`) every label of the coherent sampled-time oracle (`Family.access ι`, branch
register `ι`, time address `Fin (n + 2)`) is `EncodedOracle.ImplementsOn` the membership phase
oracle `x ↦ (jointBoolean ι …).phase (membership x)` on the clean-ancilla encoding (`ancillaEmbed`)
at cost `hardCost`:

* the row and column **location** labels are input-, stage- and
  branch-independent permutation unitaries (fixed gates): **0** queries;
* the **value** label costs **2** queries: query the bit `(c, k, z)` that the
  address and the time address `k` select (projection
  `P_{(c,k,z)} = Σ_{(i,k')} [k' = k] |i,k'⟩⟨i,k'| ⊗ Π_{(c,z)}`,
  `stageAddressFamily`, with `Π` the `Hamiltonian.bitAddressFamily` of
  `jointTable`), add the word selected by the bit and the time address (a
  fixed gate: `Hamiltonian.bitWordGate` on hidden stages, the identity on the
  idle and source stages), unquery (`PhaseCircuit.implementsOn_circuit`).

Inverse queries are handled by `EncodedMultiOracle.compile` (adjoint circuit).
Controlled calls are covered by the reduction of the **Controlled calls**
paragraph of `ODE/Model` (controlled locator: fixed gate; controlled value
call: one value call between controlled swaps with a uniform dummy `Word μ`
register, spectator `ι × Fin 2 × Word μ`); there is no Lean lemma for it.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- **The time-addressed address family**:
`P_{(c,k,z)} = Σ_{(i,k')} [k' = k] |i,k'⟩⟨i,k'| ⊗ Π_{(c,z)}`. -/
def stageAddressFamily (ι : Type*) [Fintype ι] (M n μ s : ℕ) :
    ProjFamily (Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2))
      (Fin M × Fin n × Fin (2 ^ μ)) where
  proj i := Joint.fiber fun b =>
    if (b.2 : ℕ) = (i.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).proj (i.1, i.2.2)
    else 0
  isStarProjection := by
    intro i
    refine ⟨?_, ?_⟩
    · change Joint.fiber _ * Joint.fiber _ = Joint.fiber _
      rw [Joint.fiber_mul]
      congr 1
      funext b
      split_ifs
      · exact ((Hamiltonian.bitAddressFamily (jointTable M μ s)
          (Hamiltonian.Word μ)).isStarProjection _).isIdempotentElem
      · simp
    · change star (Joint.fiber _) = Joint.fiber _
      rw [Joint.star_fiber]
      congr 1
      funext b
      split_ifs
      · exact ((Hamiltonian.bitAddressFamily (jointTable M μ s)
          (Hamiltonian.Word μ)).isStarProjection _).isSelfAdjoint
      · simp
  orthogonal := by
    intro i i' hne
    refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => ?_
    change (if (b.2 : ℕ) = (i.2.1 : ℕ) then
        (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).proj (i.1, i.2.2)
      else 0)
      ((if (b.2 : ℕ) = (i'.2.1 : ℕ) then
        (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).proj (i'.1, i'.2.2)
      else 0) (Ψ b)) = 0
    split_ifs with h₁ h₂
    · have hk : i.2.1 = i'.2.1 := Fin.ext (h₁.symm.trans h₂)
      have hcz : (i.1, i.2.2) ≠ (i'.1, i'.2.2) := fun h =>
        hne (Prod.ext (Prod.ext_iff.mp h).1 (Prod.ext hk (Prod.ext_iff.mp h).2))
      exact congrArg (fun A : _ →L[ℂ] _ => A (Ψ b))
        ((Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).orthogonal _ _ hcz)
    all_goals simp

/-- **The membership oracle of the joint problem** in phase form on
ancilla ⊗ workspace (the XOR oracle in the Hadamard basis of the ancilla). -/
def jointBoolean (ι : Type*) [Fintype ι] (M n μ s : ℕ) :
    ProjFamily (Joint (Fin 2) (Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2)))
      (Fin M × Fin n × Fin (2 ^ μ)) :=
  (stageAddressFamily ι M n μ s).withAncilla

/-! ### The value circuit, blockwise -/

variable {ι : Type*} [Fintype ι] {M n μ s : ℕ}

/-- The block `b = (branch, stage)` of `P_{(c,k,z)} v`: `Π_{(c,z)} v_b` on stage
`k`, `0` on the other stages. -/
theorem stageAddressFamily_proj_apply (i : Fin M × Fin n × Fin (2 ^ μ))
    (v : Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2)) (b : ι × Fin (n + 2)) :
    (stageAddressFamily ι M n μ s).proj i v b =
      if (b.2 : ℕ) = (i.2.1 : ℕ) then
        (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).proj (i.1, i.2.2)
          (v b)
      else 0 := by
  change (if (b.2 : ℕ) = (i.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).proj (i.1, i.2.2)
    else 0) (v b) = _
  split_ifs <;> simp

/-- **The marked part, blockwise**: on a hidden stage `k < n` the membership
string marks exactly the addresses whose bit `(c, k, z)` is set (the
`Hamiltonian.bitAddressFamily` marking of the stage bits `stageBits x k`); the
idle and source stages are unmarked. -/
theorem hitProj_stage_apply (x : Promised M n (2 ^ μ))
    (v : Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2)) (b : ι × Fin (n + 2)) :
    PhaseCircuit.hitProj (stageAddressFamily ι M n μ s) (membership x) v b =
      if h : (b.2 : ℕ) < n then
        PhaseCircuit.hitProj (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ))
          (stageBits x ⟨b.2, h⟩) (v b)
      else 0 := by
  rw [PhaseCircuit.hitProj_apply, PhaseCircuit.joint_sum_apply]
  simp only [stageAddressFamily_proj_apply]
  split_ifs with h
  · rw [PhaseCircuit.hitProj_apply, Finset.sum_filter, Finset.sum_filter]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_eq_single ⟨b.2, h⟩]
    · show (if membership x (c, ⟨b.2, h⟩, z) = true then
          (if (b.2 : ℕ) = (b.2 : ℕ) then
            (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).proj (c, z)
              (v b)
          else 0) else 0) =
        if membership x (c, ⟨b.2, h⟩, z) = true then
          (Hamiltonian.bitAddressFamily (jointTable M μ s) (Hamiltonian.Word μ)).proj (c, z) (v b)
        else 0
      rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (show ¬((b.2 : ℕ) = (k : ℕ)) from fun he => hk (Fin.ext he.symm)), ite_self]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · exact Finset.sum_eq_zero fun i _ => if_neg fun he => h (by rw [he]; exact i.2.1.isLt)

variable (ι M n μ s) in
/-- **The branch gate** `G_β = Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ (W_β if k < n else 1)`: the
fixed word gate of bit value `β` on the hidden stages, the identity on the idle
and source stages. -/
def stageGate (g : Fin 2) :
    Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2) →L[ℂ]
      Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2) :=
  Joint.fiber fun b =>
    if (b.2 : ℕ) < n then Hamiltonian.bitBranchGate (jointTable M μ s) μ g else 1

omit [Fintype ι] in
/-- The branch gate acts blockwise. -/
theorem stageGate_apply (g : Fin 2)
    (v : Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2)) (b : ι × Fin (n + 2)) :
    stageGate ι M n μ s g v b =
      if (b.2 : ℕ) < n then Hamiltonian.bitBranchGate (jointTable M μ s) μ g (v b) else v b := by
  rw [stageGate, Joint.fiber_apply]
  split_ifs <;> rfl

variable (ι M n μ s) in
/-- The branch gates are unitary. -/
theorem stageGate_unitary (g : Fin 2) : IsUnitary (stageGate ι M n μ s g) :=
  PhaseCircuit.isUnitary_fiber _ fun b => by
    split_ifs
    · exact Hamiltonian.bitBranchGate_unitary _ _ _
    · exact ⟨by simp, by simp⟩

omit [Fintype ι] in
/-- **The value label, entrywise**: on block `(i, k)` it adds the stage-`k` word
of the queried bit on the hidden stages and nothing on the idle and source
stages. -/
theorem access_value_apply (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (T : ℝ)
    (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) (x : Promised M n (2 ^ μ))
    (v : Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2)) (b : ι × Fin (n + 2))
    (a : JointIndex M μ s × JointIndex M μ s) (z : Hamiltonian.Word μ) :
    (jointFamily M n μ s hμ hμs T hT).access ι .value x v b (a, z) =
      v b (a, z - if h : (b.2 : ℕ) < n then
        (((jointTable M μ s).value (stageBits x ⟨b.2, h⟩) a : ℤ) : Hamiltonian.Word μ)
        else 0) :=
  rfl

/-- **Every sampled-time label is a `hardCost`-query membership program** (the construction before
Theorem `odel:thm:joint`): `0` for the locators, `2` for the value oracle. -/
theorem implementsOn_joint (ι : Type*) [Fintype ι] {M n μ s : ℕ} (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) (l : Query) :
    EncodedOracle.ImplementsOn
      (fun x : Promised M n (2 ^ μ) => (jointBoolean ι M n μ s).phase (membership x))
      ((jointFamily M n μ s hμ hμs T hT).access ι l)
      (ancillaEmbed (Workspace ι (JointIndex M μ s) (Hamiltonian.Word μ) (n + 2)))
      (hardCost l) := by
  cases l with
  | rowLocation =>
    exact PhaseCircuit.implementsOn_of_eq
      (Joint.fiber fun _ : ι × Fin (n + 2) =>
        SparseFlagEmbedding.location (Z := Hamiltonian.Word μ)
          (fun _ : Unit => Hamiltonian.permCLM
            (Hamiltonian.rowEquiv (jointSlot M μ s) (jointLoc M μ s))) ())
      (PhaseCircuit.isUnitary_fiber _ fun _ =>
        SparseFlagEmbedding.location_unitary _ (fun _ => Hamiltonian.isUnitary_permCLM _) ())
      fun x => ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => rfl
  | columnLocation =>
    exact PhaseCircuit.implementsOn_of_eq
      (Joint.fiber fun _ : ι × Fin (n + 2) =>
        SparseFlagEmbedding.location (Z := Hamiltonian.Word μ)
          (fun _ : Unit => Hamiltonian.permCLM
            (Hamiltonian.colEquiv (jointSlot M μ s) (jointLoc M μ s))) ())
      (PhaseCircuit.isUnitary_fiber _ fun _ =>
        SparseFlagEmbedding.location_unitary _ (fun _ => Hamiltonian.isUnitary_permCLM _) ())
      fun x => ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => rfl
  | value =>
    refine PhaseCircuit.implementsOn_circuit (stageAddressFamily ι M n μ s) membership
      (stageGate ι M n μ s) (stageGate_unitary ι M n μ s) _ (fun x v => ?_) (fun x v => ?_)
    · -- branch identity `0`: the value oracle, blockwise
      refine PiLp.ext fun b => PiLp.ext fun az => ?_
      obtain ⟨a, z⟩ := az
      rw [access_value_apply]
      simp only [PiLp.add_apply, PiLp.sub_apply, hitProj_stage_apply, stageGate_apply]
      by_cases h : (b.2 : ℕ) < n
      · simp only [dif_pos h, if_pos h, PiLp.sub_apply,
          Hamiltonian.hitProj_bitAddress_apply, Hamiltonian.bitBranchGate_zero,
          Hamiltonian.bitBranchGate_one, Hamiltonian.bitWordGate_apply,
          Hamiltonian.BitTable.value]
        cases (jointTable M μ s).bit (stageBits x ⟨b.2, h⟩) a <;> simp
      · simp only [dif_neg h, if_neg h, PiLp.zero_apply, sub_zero, add_zero]
    · -- branch identity `1`: the ancilla returns clean
      refine PiLp.ext fun b => ?_
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply, hitProj_stage_apply,
        stageGate_apply]
      by_cases h : (b.2 : ℕ) < n
      · simp only [dif_pos h, if_pos h]
        exact Hamiltonian.bitValue_branch_one (X := Unit) (y := fun _ => stageBits x ⟨b.2, h⟩)
          () (v b)
      · simp only [dif_neg h, if_neg h, sub_zero, add_zero]

end

end SparseLowerBounds.ODE
end
