import TimeDependentLowerBoundExtensions.Tolerant.Realization
import TimeDependentLowerBoundExtensions.Tolerant.Approx

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Gate-level circuits with approximately realised private operations

In the gate-level circuits of `Gate.Program` (instruction lists `gs`, run by
`SparseHamiltonian.GateCircuit.SlotSim.runT U_J D gs`) a private call with literal controls `cs`
of an operation constant in time is the masked call `L⁻¹ (masked m_cs D_x) L` in one fixed
layout `L` (`Gate.slotOracle_const_eq`). When `D_x` is replaced by an operation `R_x` on a larger
space that implements it within `ξ` on an isometric encoding `e` (`‖R_x ∘ e - e ∘ D_x‖ ≤ ξ`),
the circuit with every private call replaced by the masked call of `R_x` is a program over the
family of these realised calls (`realFamily`), and it implements the ideal circuit within
`nPriv gs · ξ` on the encoding `jointMap e ∘ L` (`realEncoding`): errors of the private calls add
up, the other instructions are lifted exactly. This is the error accounting of the manuscript's
gate model (Section `hs:sec:gates`) and of Theorem `hs:thm:gates`, in which the
errors of the private calls add up to `nPriv · ξ`.

* `realFamily`: the masked calls `masked m_cs R_x`, one label per list of literal controls;
* `nonempty_realAccess`: when `R_x = p(x)` for a program `p` over the call forms of the native
  sparse queries with at most `q` value calls, every realised call costs at most `2q` Boolean
  queries (exactly, no error: the realised calls are what the circuit executes);
* `exists_approxProgram`: the circuit as a program over `realFamily` with `nPriv gs` calls and
  error at most `nPriv gs · ξ` against `runT U_J D gs` on `realEncoding` (from `approx_adjoint`
  and `masked_approx` of `Tolerant.Approx`).
-/

namespace TimeDependentLowerBoundExtensions.Tolerant

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
  SparseHamiltonian.GateCircuit.SlotSim
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open SparseLowerBounds.Adaptive.Access (jointMap)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily)
open scoped InnerProduct InnerProductSpace

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The family of realised private calls**: on the branch register `ι` of a fixed layout, the
label `cs` (literal controls) on input `x` is the masked call `masked (msk cs) (R x)` of the
realised operation `R x`. -/
def realFamily {X : Type*} (ι : Type*) [Fintype ι]
    (msk : List (Wire a m r K × Bool) → ι → Bool) (R : X → W →L[ℂ] W) :
    List (Wire a m r K × Bool) → X → Joint ι W →L[ℂ] Joint ι W :=
  fun cs x => MaskedProgram.masked (msk cs) (R x)

/-- The realised calls of a unitary operation are unitary. -/
theorem realFamily_unitary {X : Type*} (ι : Type*) [Fintype ι]
    (msk : List (Wire a m r K × Bool) → ι → Bool) {R : X → W →L[ℂ] W}
    (hR : ∀ x, IsUnitary (R x)) (cs : List (Wire a m r K × Bool)) (x : X) :
    IsUnitary (realFamily ι msk R cs x) :=
  MaskedProgram.masked_unitary (msk cs) (R x) (hR x)

/-- **The encoding of realised circuits**: the fixed layout `L` of the wires followed by the
encoding `e` of the private register on every branch, `jointMap ι e ∘ L`. -/
def realEncoding (ι : Type*) [Fintype ι] (e : Vsp a P →L[ℂ] W)
    (L : Reg (Wire a m r K) P ≃ₗᵢ[ℂ] Joint ι (Vsp a P)) :
    Reg (Wire a m r K) P →L[ℂ] Joint ι W :=
  jointMap ι e ∘L L.toLinearIsometry.toContinuousLinearMap

/-- The encoding of realised circuits is isometric when `e` is. -/
theorem realEncoding_isometry (ι : Type*) [Fintype ι] {e : Vsp a P →L[ℂ] W}
    (he : e† ∘L e = 1) (L : Reg (Wire a m r K) P ≃ₗᵢ[ℂ] Joint ι (Vsp a P)) :
    (realEncoding ι e L)† ∘L realEncoding ι e L = 1 := by
  rw [realEncoding, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc _ (jointMap ι e),
    SparseLowerBounds.Adaptive.Access.jointMap_isometry ι e he, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]
  exact LinearIsometry.adjoint_comp_self _

/-- **Realised calls cost at most `2q` Boolean queries**: from a certificate of the native
primitives of `D` with weight `hardCost` and a program `p` over all call forms of the native
sparse queries of `D` on a spectator register `Ω` with at most `q` value calls, every label of
`realFamily ι msk p.eval` (any mask) has a certificate of weight `2q`. The construction is that
of `Gate.nonempty_privAccess`, applied to the realised operation `p(x)` itself. -/
theorem nonempty_realAccess {I : Type*} [Fintype I] {X N Z : Type} [Fintype N] [DecidableEq N]
    [Fintype Z] [AddCommGroup Z] {s : ℕ} {y : X → I → Bool} (D : Data X N Z s)
    (A : PhaseAccess I y (oracles D) hardCost) (Ω : Type) [Fintype Ω]
    (p : MultiOracleCircuit.Program (callFamily (specOracles Ω D))) {q : ℕ}
    (hq : p.cost (fun c => valueWeight c.1) ≤ q) (ι : Type) [Fintype ι]
    (msk : List (Wire a m r K × Bool) → ι → Bool) :
    Nonempty (PhaseAccess I y (realFamily ι msk p.eval) (fun _ => 2 * q)) := by
  classical
  let A₁ : PhaseAccess I y (specOracles Ω D) hardCost := (A.spectate Ω).congr fun _ _ => rfl
  let A₂ := Core.callAccess A₁ (SparseLowerBounds.specOracles_unitary Ω D)
  have hc := EncodedMultiOracle.implements_compile A₂.enc A₂.enc_isometry
    (fun x => A₂.fam.isUnitary_phase (y x))
    (AdaptiveODELowerBound.Access.callFamily_unitary (SparseLowerBounds.specOracles_unitary Ω D))
    p (fun c => hardCost c.1) A₂.impl
  have hcost : p.cost (fun c => hardCost c.1) ≤ 2 * q := by
    rw [Core.cost_hardCost_fst]
    omega
  have hD : EncodedOracle.ImplementsOn (fun x => A₂.fam.phase (y x)) p.eval A₂.enc (2 * q) :=
    EncodedOracle.ImplementsOn.mono hc hcost
  exact ⟨PhaseAccess.ofImplementsOn (Core.maskedBoolean ι A₂.fam) (Core.maskedEncoding ι A₂.enc)
    (Core.maskedEncoding_isometry ι _ A₂.enc_isometry)
    (fun cs => Core.implementsOn_masked ι (msk cs) A₂.fam y hD)⟩

omit [CompleteSpace W] in
/-- **Errors of conjugated calls**: on the encoding `jointMap ι e ∘ L`, the error of `A` against
the call `L⁻¹ B L` is at most the error of `A` against `B` on `jointMap ι e`. -/
theorem norm_sub_conj_le (ι : Type*) [Fintype ι] (e : Vsp a P →L[ℂ] W)
    (L : Reg (Wire a m r K) P ≃ₗᵢ[ℂ] Joint ι (Vsp a P)) (A : Joint ι W →L[ℂ] Joint ι W)
    (B : Joint ι (Vsp a P) →L[ℂ] Joint ι (Vsp a P)) :
    ‖A ∘L realEncoding ι e L - realEncoding ι e L ∘L L.symm.conjStarAlgEquiv B‖ ≤
      ‖A ∘L jointMap ι e - jointMap ι e ∘L B‖ := by
  have h : A ∘L realEncoding ι e L - realEncoding ι e L ∘L L.symm.conjStarAlgEquiv B =
      (A ∘L jointMap ι e - jointMap ι e ∘L B) ∘L L.toLinearIsometry.toContinuousLinearMap := by
    ext v
    simp [realEncoding, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [h]
  calc _ ≤ ‖A ∘L jointMap ι e - jointMap ι e ∘L B‖ * ‖L.toLinearIsometry.toContinuousLinearMap‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A ∘L jointMap ι e - jointMap ι e ∘L B‖ * 1 :=
        mul_le_mul_of_nonneg_left (LinearIsometry.norm_toContinuousLinearMap_le _)
          (ContinuousLinearMap.opNorm_nonneg _)
    _ = _ := mul_one _

/-- **Gate-level circuits with realised private operations are programs**: for a public unitary
`U_J`, a unitary private operation `D_x` constant in time, a unitary operation `R_x` with
`‖R_x ∘ e - e ∘ D_x‖ ≤ ξ` on an isometric encoding `e`, a fixed layout `L` of the wires in which
every constant private call is masked (as given by `Gate.slotOracle_const_eq`), and an
instruction list of valid instructions, there is a program over `realFamily ι msk R` with exactly
`nPriv gs` calls whose operator is within `nPriv gs · ξ` of `runT U_J D gs` on the encoding
`realEncoding ι e L`, for every input. -/
theorem exists_approxProgram {X : Type*} (UJ : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ)
    (Dp : X → Vsp a P →L[ℂ] Vsp a P) (hDp : ∀ x, IsUnitary (Dp x)) (R : X → W →L[ℂ] W)
    (hR : ∀ x, IsUnitary (R x)) (e : Vsp a P →L[ℂ] W) (he : e† ∘L e = 1) {ξ : ℝ}
    (hRe : ∀ x, ‖R x ∘L e - e ∘L Dp x‖ ≤ ξ) (ι : Type) [Fintype ι]
    (L : Reg (Wire a m r K) P ≃ₗᵢ[ℂ] Joint ι (Vsp a P))
    (msk : List (Wire a m r K × Bool) → ι → Bool)
    (hmsk : ∀ cs (A : Vsp a P →L[ℂ] Vsp a P),
      slotOracle cs (fun _ => A) = L.symm.conjStarAlgEquiv (MaskedProgram.masked (msk cs) A))
    (gs : List (Instr (Wire a m r K))) (hgs : ∀ g ∈ gs, g.Valid Wire.anc) :
    ∃ p : MultiOracleCircuit.Program (realFamily ι msk R),
      (∀ x, ‖p.eval x ∘L realEncoding ι e L -
        realEncoding ι e L ∘L runT UJ (fun _ => Dp x) gs‖ ≤ nPriv gs * ξ) ∧
      p.count = nPriv gs := by
  have hE := realEncoding_isometry ι he L
  induction gs with
  | nil =>
    refine ⟨.identity, fun _ => ?_, rfl⟩
    simp only [MultiOracleCircuit.Program.eval_identity, runT_nil, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, sub_self,
      ContinuousLinearMap.opNorm_zero]
    simp [nPriv]
  | cons g gs ih =>
    obtain ⟨p, hp, hc⟩ := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    have hg := hgs g List.mem_cons_self
    have key : ∃ pg : MultiOracleCircuit.Program (realFamily ι msk R),
        (∀ x, ‖pg.eval x ∘L realEncoding ι e L -
          realEncoding ι e L ∘L evalT UJ (fun _ => Dp x) g‖ ≤
            ((if g.isPriv then 1 else 0 : ℕ) : ℝ) * ξ) ∧
          pg.count = if g.isPriv then 1 else 0 := by
      cases g with
      | gate g' =>
        have hop : IsUnitary (gateOp g'.cs g'.t g'.u : Reg (Wire a m r K) P →L[ℂ] _) :=
          gateOp_isUnitary g'.cs g'.t g'.u hg.2.2
        refine ⟨.fixed (SubspaceOracle.lift (realEncoding ι e L) _)
          (SubspaceOracle.lift_unitary _ hE _ hop), fun x => ?_, rfl⟩
        change ‖SubspaceOracle.lift (realEncoding ι e L) _ ∘L realEncoding ι e L -
          realEncoding ι e L ∘L gateOp g'.cs g'.t g'.u‖ ≤ _
        rw [EncodedOracle.lift_comp _ hE, sub_self, ContinuousLinearMap.opNorm_zero]
        simp [Instr.isPriv]
      | uj cs adj =>
        have hU : IsUnitary (if adj then UJ† else UJ) := by
          cases adj
          · exact hUJ
          · exact hUJ.adjoint
        have hop := oracleOp_isUnitary Wire.anc anc_injective cs _ hU
        refine ⟨.fixed (SubspaceOracle.lift (realEncoding ι e L) _)
          (SubspaceOracle.lift_unitary _ hE _ hop), fun x => ?_, rfl⟩
        change ‖SubspaceOracle.lift (realEncoding ι e L) _ ∘L realEncoding ι e L -
          realEncoding ι e L ∘L oracleOp Wire.anc anc_injective cs (if adj then UJ† else UJ)‖
            ≤ _
        rw [EncodedOracle.lift_comp _ hE, sub_self, ContinuousLinearMap.opNorm_zero]
        simp [Instr.isPriv]
      | priv cs adj =>
        cases adj
        · refine ⟨.query cs, fun x => ?_, rfl⟩
          change ‖MaskedProgram.masked (msk cs) (R x) ∘L realEncoding ι e L -
            realEncoding ι e L ∘L slotOracle cs (fun _ => Dp x)‖ ≤ _
          rw [hmsk cs (Dp x)]
          refine (norm_sub_conj_le ι e L _ _).trans ?_
          refine (masked_approx ι (msk cs) (R x) (Dp x) e (hRe x)).trans (le_of_eq ?_)
          simp [Instr.isPriv]
        · refine ⟨.queryAdjoint cs, fun x => ?_, rfl⟩
          change ‖star (MaskedProgram.masked (msk cs) (R x)) ∘L realEncoding ι e L -
            realEncoding ι e L ∘L slotOracle cs (fun _ => (Dp x)†)‖ ≤ _
          rw [ContinuousLinearMap.star_eq_adjoint, MaskedProgram.masked_adjoint,
            hmsk cs ((Dp x)†)]
          refine (norm_sub_conj_le ι e L _ _).trans ?_
          refine (masked_approx ι (msk cs) ((R x)†) ((Dp x)†) e
            (approx_adjoint (R x) (Dp x) e (hR x) (hDp x) (hRe x))).trans (le_of_eq ?_)
          simp [Instr.isPriv]
    obtain ⟨pg, hpg, hcg⟩ := key
    refine ⟨.seq p pg, fun x => ?_, ?_⟩
    · rw [MultiOracleCircuit.Program.eval_seq, runT_cons]
      set E := realEncoding ι e L
      set P₀ := p.eval x
      set G := pg.eval x
      set Rn := runT UJ (fun _ => Dp x) gs
      set Ev := evalT UJ (fun _ => Dp x) g
      have hP : ‖P₀‖ ≤ 1 := SparseHamiltonian.OracleCircuit.IsUnitary.norm_le_one
        (MultiOracleCircuit.Program.eval_unitary p (realFamily_unitary ι msk hR) x)
      have hEv : ‖Ev‖ ≤ 1 := SparseHamiltonian.OracleCircuit.IsUnitary.norm_le_one
        (evalT_isUnitary UJ _ hUJ (fun _ _ => hDp x) g hg)
      have hsplit : (P₀ * G) ∘L E - E ∘L (Rn ∘L Ev) =
          P₀ ∘L (G ∘L E - E ∘L Ev) + (P₀ ∘L E - E ∘L Rn) ∘L Ev := by
        ext v
        simp
      have h1 : ‖G ∘L E - E ∘L Ev‖ ≤ ((if g.isPriv then 1 else 0 : ℕ) : ℝ) * ξ := hpg x
      have h2 : ‖P₀ ∘L E - E ∘L Rn‖ ≤ (nPriv gs : ℝ) * ξ := hp x
      have n1 := ContinuousLinearMap.opNorm_nonneg (G ∘L E - E ∘L Ev)
      have n2 := ContinuousLinearMap.opNorm_nonneg (P₀ ∘L E - E ∘L Rn)
      have b1 := ContinuousLinearMap.opNorm_comp_le P₀ (G ∘L E - E ∘L Ev)
      have b2 := ContinuousLinearMap.opNorm_comp_le (P₀ ∘L E - E ∘L Rn) Ev
      have m1 := mul_le_mul_of_nonneg_right hP n1
      have m2 := mul_le_mul_of_nonneg_left hEv n2
      have hn : ((nPriv (g :: gs) : ℕ) : ℝ) =
          (nPriv gs : ℝ) + ((if g.isPriv then 1 else 0 : ℕ) : ℝ) := by
        rw [nPriv, List.countP_cons]
        push_cast
        rfl
      rw [hsplit, hn]
      refine (ContinuousLinearMap.opNorm_add_le _ _).trans ?_
      nlinarith
    · rw [MultiOracleCircuit.Program.count_seq, hc, hcg, nPriv, nPriv, List.countP_cons]

end

end TimeDependentLowerBoundExtensions.Tolerant
