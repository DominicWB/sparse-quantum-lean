import ODELowerBoundExtensions.Homogeneous.Data

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Proposition `odel:rem:homogeneous`: the sampled-time access from membership queries

Manuscript: the construction before Theorem `odel:thm:joint` and the proof of Proposition
`odel:rem:homogeneous` ("the same oracle simulation and adversary reduction prove eq.
`odel:eq:joint`"), following `SparseLowerBounds.ODE.JointCompile` with the stage-indexed tables
`homTable`. Every label of the coherent sampled-time oracle of `homFamily` (branch register
`ι`, time address `Fin (n + 4)`) is `EncodedOracle.ImplementsOn` the membership phase oracle
`x ↦ (homBoolean ι …).phase (membership x)` on the clean-ancilla encoding at cost `hardCost`:

* row and column **location** labels: input-independent, stage-dependent permutation unitaries
  `Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ L_k` (fixed gates), **0** queries;
* the **value** label, **2** queries: query the bit `(c, k, z)` selected by the address and the
  time address (`homStageAddressFamily`: `Σ_{(i,k')} [k' = k] |i,k'⟩⟨i,k'| ⊗ Π^{(k)}_{(c,z)}`,
  `Π^{(k)}` the `Hamiltonian.bitAddressFamily` of `homTable k`), add the word selected by the
  bit and the time address (`homStageGate`: `Hamiltonian.bitBranchGate (homTable k)` on block
  `k`; on the known stages no address reads a bit and both branch gates add the known word),
  unquery (`PhaseCircuit.implementsOn_circuit`).

Inverse and controlled calls are covered as in `SparseLowerBounds.ODE.Model`. That module's cost-`0`
argument for a controlled locator call is stated for input- and stage-independent locators; the
homogeneous locators depend on the stage (forced when `s = 2^μ`, see
`ODELowerBoundExtensions.Homogeneous.Data`) but not on the input (`homData_locators_input_indep`),
and the time address is a workspace register, so the locator `Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ L_k` is still a
fixed gate of cost `0` (the construction before Theorem `odel:thm:joint`). The template is the
released `SparseLowerBounds.ODE.JointCompile`; the stage-indexed builder of
`ODELowerBoundExtensions.Padding.StageCompile` is fixed to `n + 2` stages, one table and
stage-independent locators, so it is not reused here.
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian NativeSparseBlockEncoding
open OracleCircuit

variable {ι : Type*} [Fintype ι] {M n μ s : ℕ}

variable (ι M n μ s) in
/-- The time-addressed address projection
`P_{(c,k,z)} = Σ_{(i,k')} [k' = k] |i,k'⟩⟨i,k'| ⊗ Π^{(k')}_{(c,z)}`. -/
def homStageProj (i : Fin M × Fin n × Fin (2 ^ μ)) :
    Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4) →L[ℂ]
      Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4) :=
  Joint.fiber fun b =>
    if (b.2 : ℕ) = (i.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ)).proj
        (i.1, i.2.2)
    else 0

/-- The address projections are star projections. -/
theorem homStageProj_isStarProjection (i : Fin M × Fin n × Fin (2 ^ μ)) :
    IsStarProjection (homStageProj ι M n μ s i) := by
  refine ⟨?_, ?_⟩
  · change Joint.fiber _ * Joint.fiber _ = Joint.fiber _
    rw [Joint.fiber_mul]
    congr 1
    funext b
    split_ifs
    · exact ((Hamiltonian.bitAddressFamily (homTable M n μ s b.2)
        (Hamiltonian.Word μ)).isStarProjection _).isIdempotentElem
    · simp
  · change star (Joint.fiber _) = Joint.fiber _
    rw [Joint.star_fiber]
    congr 1
    funext b
    split_ifs
    · exact ((Hamiltonian.bitAddressFamily (homTable M n μ s b.2)
        (Hamiltonian.Word μ)).isStarProjection _).isSelfAdjoint
    · simp

omit [Fintype ι] in
/-- Distinct address projections are orthogonal. -/
theorem homStageProj_orthogonal (i i' : Fin M × Fin n × Fin (2 ^ μ)) (h : i ≠ i') :
    homStageProj ι M n μ s i * homStageProj ι M n μ s i' = 0 := by
  refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => ?_
  change (if (b.2 : ℕ) = (i.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ)).proj (i.1, i.2.2)
    else 0)
    ((if (b.2 : ℕ) = (i'.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ)).proj (i'.1, i'.2.2)
    else 0) (Ψ b)) = 0
  split_ifs with h₁ h₂
  · have hk : i.2.1 = i'.2.1 := Fin.ext (h₁.symm.trans h₂)
    have hcz : (i.1, i.2.2) ≠ (i'.1, i'.2.2) := fun he =>
      h (Prod.ext (Prod.ext_iff.mp he).1 (Prod.ext hk (Prod.ext_iff.mp he).2))
    exact congrArg (fun A : _ →L[ℂ] _ => A (Ψ b))
      ((Hamiltonian.bitAddressFamily (homTable M n μ s b.2)
        (Hamiltonian.Word μ)).orthogonal _ _ hcz)
  all_goals simp

variable (ι M n μ s) in
/-- **The time-addressed address family** of the homogeneous data. -/
def homStageAddressFamily :
    ProjFamily (Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4))
      (Fin M × Fin n × Fin (2 ^ μ)) where
  proj := homStageProj ι M n μ s
  isStarProjection := homStageProj_isStarProjection
  orthogonal := homStageProj_orthogonal

/-- The block `b = (branch, stage)` of `P_{(c,k,z)} v`: `Π^{(k)}_{(c,z)} v_b` on stage `k`, `0`
on the other stages. -/
theorem homStageAddressFamily_proj_apply (i : Fin M × Fin n × Fin (2 ^ μ))
    (v : Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4)) (b : ι × Fin (n + 4)) :
    (homStageAddressFamily ι M n μ s).proj i v b =
      if (b.2 : ℕ) = (i.2.1 : ℕ) then
        (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ)).proj
          (i.1, i.2.2) (v b)
      else 0 := by
  change (if (b.2 : ℕ) = (i.2.1 : ℕ) then
      (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ)).proj
        (i.1, i.2.2)
    else 0) (v b) = _
  split_ifs <;> simp

/-- **The marked part, blockwise**: on a hidden stage `k < n` the membership string marks
exactly the addresses of the stage table whose bit `(c, k, z)` is set; the known stages are
unmarked. -/
theorem hitProj_homStage_apply (x : Promised M n (2 ^ μ))
    (v : Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4)) (b : ι × Fin (n + 4)) :
    PhaseCircuit.hitProj (homStageAddressFamily ι M n μ s) (membership x) v b =
      if h : (b.2 : ℕ) < n then
        PhaseCircuit.hitProj
          (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ))
          (stageBits x ⟨b.2, h⟩) (v b)
      else 0 := by
  rw [PhaseCircuit.hitProj_apply, PhaseCircuit.joint_sum_apply]
  simp only [homStageAddressFamily_proj_apply]
  split_ifs with h
  · rw [PhaseCircuit.hitProj_apply, Finset.sum_filter, Finset.sum_filter]
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_eq_single ⟨b.2, h⟩]
    · show (if membership x (c, ⟨b.2, h⟩, z) = true then
          (if (b.2 : ℕ) = (b.2 : ℕ) then
            (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ)).proj
              (c, z) (v b)
          else 0) else 0) =
        if membership x (c, ⟨b.2, h⟩, z) = true then
          (Hamiltonian.bitAddressFamily (homTable M n μ s b.2) (Hamiltonian.Word μ)).proj
            (c, z) (v b)
        else 0
      rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (show ¬((b.2 : ℕ) = (k : ℕ)) from fun he => hk (Fin.ext he.symm)), ite_self]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · exact Finset.sum_eq_zero fun i _ => if_neg fun he => h (by rw [he]; exact i.2.1.isLt)

variable (ι M n μ s) in
/-- **The membership oracle** in phase form on ancilla ⊗ workspace. -/
def homBoolean :
    ProjFamily (Joint (Fin 2) (Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4)))
      (Fin M × Fin n × Fin (2 ^ μ)) :=
  (homStageAddressFamily ι M n μ s).withAncilla

variable (ι M n μ s) in
/-- **The branch gate** `G_β = Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ W^{(k)}_β`: the word gate of bit value
`β` of the stage-`k` table (on the known stages both branches add the known word). -/
def homStageGate (g : Fin 2) :
    Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4) →L[ℂ]
      Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4) :=
  Joint.fiber fun b => Hamiltonian.bitBranchGate (homTable M n μ s b.2) μ g

/-- The branch gates are unitary. -/
theorem homStageGate_unitary (g : Fin 2) : IsUnitary (homStageGate ι M n μ s g) := by
  exact PhaseCircuit.isUnitary_fiber _ fun _ => Hamiltonian.bitBranchGate_unitary _ _ _

omit [Fintype ι] in
/-- The branch gate acts blockwise. -/
theorem homStageGate_apply (g : Fin 2)
    (v : Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4)) (b : ι × Fin (n + 4)) :
    homStageGate ι M n μ s g v b =
      Hamiltonian.bitBranchGate (homTable M n μ s b.2) μ g (v b) := by
  rw [homStageGate, Joint.fiber_apply]

omit [Fintype ι] in
/-- **The value label, entrywise**: on block `(i, k)` it adds the stage-`k` word of the
queried bit. -/
theorem access_hom_value_apply (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : homBusy M n ≤ T)
    (x : Promised M n (2 ^ μ)) (v : Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4))
    (b : ι × Fin (n + 4)) (a : HomIndex M μ s × HomIndex M μ s) (z : Hamiltonian.Word μ) :
    (homFamily M n μ s hμ hμs T hT).access ι .value x v b (a, z) =
      v b (a, z - (((homTable M n μ s b.2).value (homBits x b.2) a : ℤ) : Hamiltonian.Word μ)) :=
  rfl

/-- **Every sampled-time label is a `hardCost`-query membership program** (the construction before
Theorem `odel:thm:joint`): `0` for the locators, `2` for the value oracle. -/
theorem implementsOn_hom (ι : Type*) [Fintype ι] {M n μ s : ℕ} (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) (T : ℝ) (hT : homBusy M n ≤ T) (l : Query) :
    EncodedOracle.ImplementsOn
      (fun x : Promised M n (2 ^ μ) => (homBoolean ι M n μ s).phase (membership x))
      ((homFamily M n μ s hμ hμs T hT).access ι l)
      (ancillaEmbed (Workspace ι (HomIndex M μ s) (Hamiltonian.Word μ) (n + 4)))
      (hardCost l) := by
  have hs : 0 < s := lt_of_lt_of_le (Nat.two_pow_pos μ) hμs
  cases l with
  | rowLocation =>
    exact PhaseCircuit.implementsOn_of_eq
      (Joint.fiber fun b : ι × Fin (n + 4) =>
        SparseFlagEmbedding.location (Z := Hamiltonian.Word μ)
          (fun _ : Unit => Hamiltonian.permCLM
            (Hamiltonian.rowEquiv (homSlot M μ s) (homLoc M n μ s hs b.2))) ())
      (PhaseCircuit.isUnitary_fiber _ fun _ =>
        SparseFlagEmbedding.location_unitary _ (fun _ => Hamiltonian.isUnitary_permCLM _) ())
      fun x => ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => rfl
  | columnLocation =>
    exact PhaseCircuit.implementsOn_of_eq
      (Joint.fiber fun b : ι × Fin (n + 4) =>
        SparseFlagEmbedding.location (Z := Hamiltonian.Word μ)
          (fun _ : Unit => Hamiltonian.permCLM
            (Hamiltonian.colEquiv (homSlot M μ s) (homLoc M n μ s hs b.2))) ())
      (PhaseCircuit.isUnitary_fiber _ fun _ =>
        SparseFlagEmbedding.location_unitary _ (fun _ => Hamiltonian.isUnitary_permCLM _) ())
      fun x => ContinuousLinearMap.ext fun Ψ => PiLp.ext fun b => rfl
  | value =>
    refine PhaseCircuit.implementsOn_circuit (homStageAddressFamily ι M n μ s) membership
      (homStageGate ι M n μ s) homStageGate_unitary _ (fun x v => ?_) (fun x v => ?_)
    · -- branch identity `0`: the value oracle, blockwise
      refine PiLp.ext fun b => PiLp.ext fun az => ?_
      obtain ⟨a, z⟩ := az
      rw [access_hom_value_apply]
      simp only [PiLp.add_apply, PiLp.sub_apply, hitProj_homStage_apply, homStageGate_apply]
      by_cases h : (b.2 : ℕ) < n
      · have hb : homBits x b.2 = stageBits x ⟨b.2, h⟩ := dif_pos h
        simp only [dif_pos h, hb, PiLp.sub_apply,
          Hamiltonian.hitProj_bitAddress_apply, Hamiltonian.bitBranchGate_zero,
          Hamiltonian.bitBranchGate_one, Hamiltonian.bitWordGate_apply,
          Hamiltonian.BitTable.value]
        cases (homTable M n μ s b.2).bit (stageBits x ⟨b.2, h⟩) a <;> simp
      · simp only [dif_neg h, PiLp.zero_apply, sub_zero, add_zero,
          Hamiltonian.bitBranchGate_zero, Hamiltonian.bitWordGate_apply,
          homTable_value_known h]
    · -- branch identity `1`: the ancilla returns clean
      refine PiLp.ext fun b => ?_
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.zero_apply, hitProj_homStage_apply,
        homStageGate_apply]
      by_cases h : (b.2 : ℕ) < n
      · simp only [dif_pos h]
        exact Hamiltonian.bitValue_branch_one (X := Unit) (y := fun _ => stageBits x ⟨b.2, h⟩)
          () (v b)
      · simp only [dif_neg h, sub_zero, add_zero, map_zero, sub_self]

end

end ODELowerBoundExtensions.Homogeneous
