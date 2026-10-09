import ODELowerBoundExtensions.Padding.StageData

/-!
# The sampled-time access of stage-table data from membership queries

Manuscript lines 3852-3858: "A matrix value query is
implemented using at most two Boolean membership queries, by computing the relevant bit, writing
the known entry, and uncomputing the bit"; and lines 3899-3903: the dense padding block "requires
no membership queries". This is `SparseLowerBounds.ODE.implementsOn_joint` for every data built by
`stageData` (`Padding/StageData`), in particular for the dense and the zero-padded joint families.

Every label of the coherent sampled-time oracle `TimeDependentODE.labelOracle (oracles D) sample`
(branch register `ι`, time address `Fin (n + 2)`) is `EncodedOracle.ImplementsOn` the membership
phase oracle `x ↦ (stageBoolean ι M n μ B T).phase (membership x)` on the clean-ancilla encoding
at cost `hardCost`:

* row and column **location** labels: fixed permutation gates, **0** queries;
* **value** label: **2** queries. On a hidden stage `k < n`: query the bit `(c, k, z)` selected by
  the address and the time address (`stageBitFamily`, the `Hamiltonian.bitAddressFamily` of `T`
  on stage `k`), add the word of that bit value (`Hamiltonian.bitBranchGate T B`), unquery. On the
  idle and source stages: add the known words `W₀` by a fixed gate (`idleTable`), with no query.
  Known addresses of `T` (no bit, e.g. the dense padding block) are fixed words on every stage.

**Relation to the released package.** `stageBitFamily`, `stageBoolean`, `stageTableGate` and
`hitProj_stageBit_apply` are table-generic generalisations of
`SparseLowerBounds.ODE.stageAddressFamily`, `jointBoolean`, `stageGate` and `hitProj_stage_apply`,
which are fixed to `jointTable M μ s` and `Word μ` (and to the identity on the idle and source
stages). The generalisations are needed because the padded joint families change the table, the
word length, the index and the idle words, and the released package is not edited. At
`T = jointTable M μ s`, `B = μ`, `W₀ = 0` they are the released declarations: `stageBitFamily_jointTable`,
`stageBoolean_jointTable` and `stageTableGate_jointTable` (the gate of the all-zero idle words is
the identity); rewriting with `stageBitFamily_jointTable` turns `hitProj_stageBit_apply` into the
released `hitProj_stage_apply`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Padding

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.ODE
open SparseLowerBounds.Hamiltonian (BitTable Word)

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- **The time-addressed address family** of a stage bit table:
`P_{(c,k,z)} = Σ_{(i,k')} [k' = k] |i,k'⟩⟨i,k'| ⊗ Π_{(c,z)}`, `Π` the
`Hamiltonian.bitAddressFamily` of `T`. -/
def stageBitFamily (ι : Type*) [Fintype ι] {N : Type*} [Fintype N] [DecidableEq N]
    (M n μ B : ℕ) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)) :
    ProjFamily (Workspace ι N (Word B) (n + 2)) (Fin M × Fin n × Fin (2 ^ μ)) where
  proj i := Joint.fiber fun b =>
    if (b.2 : ℕ) = (i.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily T (Word B)).proj (i.1, i.2.2)
    else 0
  isStarProjection := by
    intro i
    refine ⟨?_, ?_⟩
    · change Joint.fiber _ * Joint.fiber _ = Joint.fiber _
      rw [Joint.fiber_mul]
      congr 1
      funext b
      split_ifs
      · exact ((Hamiltonian.bitAddressFamily T (Word B)).isStarProjection _).isIdempotentElem
      · simp
    · change star (Joint.fiber _) = Joint.fiber _
      rw [Joint.star_fiber]
      congr 1
      funext b
      split_ifs
      · exact ((Hamiltonian.bitAddressFamily T (Word B)).isStarProjection _).isSelfAdjoint
      · simp
  orthogonal := by
    intro i i' hne
    refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => ?_
    change (if (b.2 : ℕ) = (i.2.1 : ℕ) then
        (Hamiltonian.bitAddressFamily T (Word B)).proj (i.1, i.2.2)
      else 0)
      ((if (b.2 : ℕ) = (i'.2.1 : ℕ) then
        (Hamiltonian.bitAddressFamily T (Word B)).proj (i'.1, i'.2.2)
      else 0) (Ψ b)) = 0
    split_ifs with h₁ h₂
    · have hk : i.2.1 = i'.2.1 := Fin.ext (h₁.symm.trans h₂)
      have hcz : (i.1, i.2.2) ≠ (i'.1, i'.2.2) := fun h =>
        hne (Prod.ext (Prod.ext_iff.mp h).1 (Prod.ext hk (Prod.ext_iff.mp h).2))
      exact congrArg (fun A : _ →L[ℂ] _ => A (Ψ b))
        ((Hamiltonian.bitAddressFamily T (Word B)).orthogonal _ _ hcz)
    all_goals simp

/-- **The membership oracle** in phase form on ancilla ⊗ workspace, for the stage bit table
`T` (the analogue of `SparseLowerBounds.ODE.jointBoolean`). -/
def stageBoolean (ι : Type*) [Fintype ι] {N : Type*} [Fintype N] [DecidableEq N]
    (M n μ B : ℕ) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)) :
    ProjFamily (Joint (Fin 2) (Workspace ι N (Word B) (n + 2))) (Fin M × Fin n × Fin (2 ^ μ)) :=
  (stageBitFamily ι M n μ B T).withAncilla

/-- The known words `W₀` as a bit table with no bit (`addr = none`): its word gate adds `W₀`. -/
def idleTable {N : Type*} (M μ : ℕ) (W₀ : N × N → ℤ) : BitTable (Fin M × Fin (2 ^ μ)) (N × N) :=
  ⟨fun _ => none, fun a _ => W₀ a⟩

/-- **The branch gate** `G_β = Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ (W_β(T) if k < n else W(W₀))`: the fixed
word gate of bit value `β` on the hidden stages, the fixed gate of the known words `W₀` on the
idle and source stages. -/
def stageTableGate (ι : Type*) [Fintype ι] {N : Type*} [Fintype N] [DecidableEq N]
    (M n μ B : ℕ) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)) (W₀ : N × N → ℤ) (g : Fin 2) :
    Workspace ι N (Word B) (n + 2) →L[ℂ] Workspace ι N (Word B) (n + 2) :=
  Joint.fiber fun b =>
    if (b.2 : ℕ) < n then Hamiltonian.bitBranchGate T B g
    else Hamiltonian.bitWordGate (idleTable M μ W₀) B false

/-- **The generalisation agrees with the released package**: for the joint table and `B = μ`,
`stageBitFamily` is the released `SparseLowerBounds.ODE.stageAddressFamily`. -/
theorem stageBitFamily_jointTable (ι : Type*) [Fintype ι] (M n μ s : ℕ) :
    stageBitFamily ι M n μ μ (jointTable M μ s) = stageAddressFamily ι M n μ s :=
  rfl

/-- **The generalisation agrees with the released package**: for the joint table and `B = μ`,
`stageBoolean` is the released membership oracle `SparseLowerBounds.ODE.jointBoolean`. -/
theorem stageBoolean_jointTable (ι : Type*) [Fintype ι] (M n μ s : ℕ) :
    stageBoolean ι M n μ μ (jointTable M μ s) = jointBoolean ι M n μ s :=
  congrArg ProjFamily.withAncilla (stageBitFamily_jointTable ι M n μ s)

/-- **The generalised gate agrees with the released package**: for the joint table, `B = μ` and the all-zero
idle words, `stageTableGate` is the released branch gate `SparseLowerBounds.ODE.stageGate` (the word
gate of the zero idle table is the identity). -/
theorem stageTableGate_jointTable (ι : Type*) [Fintype ι] (M n μ s : ℕ) (g : Fin 2) :
    stageTableGate ι M n μ μ (jointTable M μ s) (fun _ => 0) g = stageGate ι M n μ s g := by
  unfold stageTableGate stageGate
  congr 1
  funext b
  split_ifs
  · rfl
  · refine ContinuousLinearMap.ext fun v => PiLp.ext fun az => ?_
    obtain ⟨a, z⟩ := az
    rw [Hamiltonian.bitWordGate_apply]
    simp [idleTable]

variable {ι : Type*} [Fintype ι] {N : Type*} [Fintype N] [DecidableEq N] {M n μ B : ℕ}

/-- The block `b = (branch, stage)` of `P_{(c,k,z)} v`: `Π_{(c,z)} v_b` on stage `k`, `0` on the
other stages (the analogue of `SparseLowerBounds.ODE.stageAddressFamily_proj_apply`). -/
theorem stageBitFamily_proj_apply (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N))
    (i : Fin M × Fin n × Fin (2 ^ μ)) (v : Workspace ι N (Word B) (n + 2))
    (b : ι × Fin (n + 2)) :
    (stageBitFamily ι M n μ B T).proj i v b =
      if (b.2 : ℕ) = (i.2.1 : ℕ) then
        (Hamiltonian.bitAddressFamily T (Word B)).proj (i.1, i.2.2) (v b)
      else 0 := by
  change (if (b.2 : ℕ) = (i.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily T (Word B)).proj (i.1, i.2.2)
    else 0) (v b) = _
  split_ifs <;> simp

/-- The branch gate acts blockwise: the bit-value word gate of `T` on the hidden stages, the
known-word gate of `W₀` on the idle and source stages. -/
theorem stageTableGate_apply (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)) (W₀ : N × N → ℤ)
    (g : Fin 2) (v : Workspace ι N (Word B) (n + 2)) (b : ι × Fin (n + 2)) :
    stageTableGate ι M n μ B T W₀ g v b =
      if (b.2 : ℕ) < n then Hamiltonian.bitBranchGate T B g (v b)
      else Hamiltonian.bitWordGate (idleTable M μ W₀) B false (v b) := by
  rw [stageTableGate, Joint.fiber_apply]
  split_ifs <;> rfl

/-- **The marked part, blockwise**: on a hidden stage `k < n` the membership string marks the
addresses whose bit `(c, k, z)` is set (the `Hamiltonian.bitAddressFamily` marking of
`stageBits x k`); the idle and source stages are unmarked. -/
theorem hitProj_stageBit_apply (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N))
    (x : Promised M n (2 ^ μ)) (v : Workspace ι N (Word B) (n + 2)) (b : ι × Fin (n + 2)) :
    PhaseCircuit.hitProj (stageBitFamily ι M n μ B T) (membership x) v b =
      if h : (b.2 : ℕ) < n then
        PhaseCircuit.hitProj (Hamiltonian.bitAddressFamily T (Word B))
          (stageBits x ⟨b.2, h⟩) (v b)
      else 0 := by
  rw [PhaseCircuit.hitProj_apply, PhaseCircuit.joint_sum_apply]
  simp only [stageBitFamily_proj_apply]
  split_ifs with h
  · rw [PhaseCircuit.hitProj_apply, Finset.sum_filter, Finset.sum_filter]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_eq_single ⟨b.2, h⟩]
    · show (if membership x (c, ⟨b.2, h⟩, z) = true then
          (if (b.2 : ℕ) = (b.2 : ℕ) then
            (Hamiltonian.bitAddressFamily T (Word B)).proj (c, z) (v b)
          else 0) else 0) =
        if membership x (c, ⟨b.2, h⟩, z) = true then
          (Hamiltonian.bitAddressFamily T (Word B)).proj (c, z) (v b)
        else 0
      rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (show ¬((b.2 : ℕ) = (k : ℕ)) from fun he => hk (Fin.ext he.symm)), ite_self]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · exact Finset.sum_eq_zero fun i _ => if_neg fun he => h (by rw [he]; exact i.2.1.isLt)

/-- The branch gates are unitary. -/
theorem stageTableGate_unitary (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N)) (W₀ : N × N → ℤ)
    (g : Fin 2) : IsUnitary (stageTableGate ι M n μ B T W₀ g) :=
  PhaseCircuit.isUnitary_fiber _ fun b => by
    split_ifs
    · exact Hamiltonian.bitBranchGate_unitary _ _ _
    · exact Hamiltonian.bitWordGate_unitary _ _ _

omit [Fintype ι] in
/-- **The value label, entrywise**: on block `b = (branch, stage)` it adds the stage word of the
sampled point `(x, b.2)`. -/
theorem stageData_value_apply {s : ℕ} (hs : 0 < s)
    (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N))
    (W₀ : N × N → ℤ) (H : Promised M n (2 ^ μ) × Fin (n + 2) → Matrix N N ℂ)
    (hbound : ∀ p a, -(2 : ℤ) ^ B < stageWord n T W₀ p a ∧ stageWord n T W₀ p a ≤ 2 ^ B)
    (hdec : ∀ p i j, Complex.I * ((stageWord n T W₀ p (i, j) : ℂ) / 2 ^ B) = H p i j)
    (hrow : ∀ p i j, H p i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ p i j, H p i j ≠ 0 → i ∈ Set.range (loc j)) (x : Promised M n (2 ^ μ))
    (v : Workspace ι N (Word B) (n + 2)) (b : ι × Fin (n + 2)) (a : N × N) (z : Word B) :
    TimeDependentODE.labelOracle
        (oracles (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol))
        (TimeDependentODE.sample (ι := ι) (M := n + 2)) .value x v b (a, z) =
      v b (a, z - ((stageWord n T W₀ (x, b.2) a : ℤ) : Word B)) :=
  rfl

/-- **Every sampled-time label of stage-table data is a `hardCost`-query membership program**
(lines 3852-3858, 3899-3903): `0` for the locators, `2` for the value oracle (the known words of
`T` and the idle words `W₀`, in particular a dense padding block, cost nothing). -/
theorem implementsOn_stageData (ι : Type*) [Fintype ι] {s : ℕ} (hs : 0 < s)
    (slot : Fin s ↪ N) (loc : N → Fin s ↪ N) (T : BitTable (Fin M × Fin (2 ^ μ)) (N × N))
    (W₀ : N × N → ℤ) (H : Promised M n (2 ^ μ) × Fin (n + 2) → Matrix N N ℂ)
    (hbound : ∀ p a, -(2 : ℤ) ^ B < stageWord n T W₀ p a ∧ stageWord n T W₀ p a ≤ 2 ^ B)
    (hdec : ∀ p i j, Complex.I * ((stageWord n T W₀ p (i, j) : ℂ) / 2 ^ B) = H p i j)
    (hrow : ∀ p i j, H p i j ≠ 0 → j ∈ Set.range (loc i))
    (hcol : ∀ p i j, H p i j ≠ 0 → i ∈ Set.range (loc j)) (l : Query) :
    EncodedOracle.ImplementsOn
      (fun x : Promised M n (2 ^ μ) => (stageBoolean ι M n μ B T).phase (membership x))
      (TimeDependentODE.labelOracle
        (oracles (stageData M n μ s B hs slot loc T W₀ H hbound hdec hrow hcol))
        (TimeDependentODE.sample (ι := ι) (M := n + 2)) l)
      (ancillaEmbed (Workspace ι N (Word B) (n + 2))) (hardCost l) := by
  cases l with
  | rowLocation =>
    exact PhaseCircuit.implementsOn_of_eq
      (Joint.fiber fun _ : ι × Fin (n + 2) =>
        SparseFlagEmbedding.location (Z := Word B)
          (fun _ : Unit => Hamiltonian.permCLM (Hamiltonian.rowEquiv slot loc)) ())
      (PhaseCircuit.isUnitary_fiber _ fun _ =>
        SparseFlagEmbedding.location_unitary _ (fun _ => Hamiltonian.isUnitary_permCLM _) ())
      fun x => ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => rfl
  | columnLocation =>
    exact PhaseCircuit.implementsOn_of_eq
      (Joint.fiber fun _ : ι × Fin (n + 2) =>
        SparseFlagEmbedding.location (Z := Word B)
          (fun _ : Unit => Hamiltonian.permCLM (Hamiltonian.colEquiv slot loc)) ())
      (PhaseCircuit.isUnitary_fiber _ fun _ =>
        SparseFlagEmbedding.location_unitary _ (fun _ => Hamiltonian.isUnitary_permCLM _) ())
      fun x => ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => rfl
  | value =>
    refine PhaseCircuit.implementsOn_circuit (stageBitFamily ι M n μ B T) membership
      (stageTableGate ι M n μ B T W₀) (stageTableGate_unitary T W₀) _ (fun x v => ?_)
      (fun x v => ?_)
    · -- branch identity `0`: the value oracle, blockwise
      refine PiLp.ext fun b => PiLp.ext fun az => ?_
      obtain ⟨a, z⟩ := az
      rw [stageData_value_apply]
      simp only [PiLp.add_apply, PiLp.sub_apply, hitProj_stageBit_apply, stageTableGate_apply]
      by_cases h : (b.2 : ℕ) < n
      · simp only [dif_pos h, if_pos h, PiLp.sub_apply, stageWord,
          Hamiltonian.hitProj_bitAddress_apply, Hamiltonian.bitBranchGate_zero,
          Hamiltonian.bitBranchGate_one, Hamiltonian.bitWordGate_apply,
          Hamiltonian.BitTable.value]
        cases T.bit (stageBits x ⟨b.2, h⟩) a <;> simp
      · simp only [dif_neg h, if_neg h, PiLp.zero_apply, sub_zero, add_zero, stageWord,
          Hamiltonian.bitWordGate_apply, idleTable]
    · -- branch identity `1`: the ancilla returns clean
      refine PiLp.ext fun b => ?_
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply, hitProj_stageBit_apply,
        stageTableGate_apply]
      by_cases h : (b.2 : ℕ) < n
      · simp only [dif_pos h, if_pos h]
        exact Hamiltonian.bitValue_branch_one (X := Unit) (y := fun _ => stageBits x ⟨b.2, h⟩)
          () (v b)
      · simp only [dif_neg h, if_neg h, map_zero, sub_zero, add_zero]

end

end ODELowerBoundExtensions.Padding
