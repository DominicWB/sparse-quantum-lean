import GateEfficientHamiltonian.Circuit.Theorem
import TimeDependentHamiltonian.Chronology.Simulation
import TimeDependentHamiltonian.Chronology.Products

/-!
# The released gate-level simulator with slot-selected private calls

The released circuit of `hs:thm:gates` (`GateCircuit.Sim.ampI`) calls the
private Cayley operation under the sector control, with the same operation on
every time slot.  For time-dependent Hamiltonians the private call is
*slot-selected*: on a configuration whose slot wires carry the word of slot
`k` it applies `D k` to the ancilla slice (`slotOracle`); one call is still
one instruction.  Gates and `U_J` calls keep their released meaning.

`evalT`, `runT` give this semantics to the released instruction lists; lists
without private calls run exactly as in the released semantics
(`runT_eq_run`).  On embedded reuse-model states the slot-selected private
call is the parallel slot action `⊕ₖ D k` of `TimeDependent.slotAction`
(`secOracleT_emb`), so every released identity of the reuse model applies
with this private operation: the reuse step (`STEPT_emb`), the SELECT
circuit (`selectNT_emb`) and its successful block (`select_blockT`).  The
circuit agrees with the ideal operators on clean inputs (`stepT_agrees`,
`selectT_agrees`).
-/

namespace SparseHamiltonian.GateCircuit.SlotSim

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin successorEquiv)
open ChronologicalResolvent GlobalColligation ChronologicalCatalyst
  FiniteChronologicalInverse GlobalResolvent CoherentReuse

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### Slot-selected oracle calls -/

/-- The slot-selected oracle call: on a configuration satisfying the literal
controls `cs` and carrying slot word `k`, apply `D k` to the ancilla slice. -/
def slotOracle (cs : List (Wire a m r K × Bool)) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  localOp Wire.anc anc_injective (fun x => if ctrlOK cs x then D (slotIdx x : ℕ) else 1)

theorem slotOracle_adjoint (cs : List (Wire a m r K × Bool)) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    (slotOracle cs D)† = slotOracle cs (fun k => (D k)†) := by
  unfold slotOracle
  rw [localOp_adjoint]
  congr 1
  funext x
  split_ifs <;> simp

theorem slotOracle_isUnitary (cs : List (Wire a m r K × Bool)) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k)) : IsUnitary (slotOracle cs D) := by
  apply localOp_isUnitary
  intro x
  split_ifs
  · exact hD _ (slotIdx _).isLt
  · exact isUnitary_one

theorem pres2_slotOracle (cs : List (Wire a m r K × Bool)) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    Pres2 Clean (slotOracle cs D) := by
  unfold slotOracle
  exact pres2_localOp _ _ _ _ (fun y b h => clean_overwrite_anc y b h)

/-- Two slot families agreeing on the `2^m` slots give the same call. -/
theorem slotOracle_congr (cs : List (Wire a m r K × Bool)) (D D' : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (h : ∀ k < 2 ^ m, D k = D' k) : slotOracle cs D = slotOracle cs D' := by
  unfold slotOracle
  congr 1
  funext x
  rw [h _ (slotIdx x).isLt]

/-- The sector-controlled slot-selected private call. -/
def secOracleT (D : ℕ → Vsp a P →L[ℂ] Vsp a P) : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  slotOracle [(Wire.sec, true)] D

/-- On embedded states the slot-selected private call is the parallel slot
action on every private slot and pointer word. -/
theorem secOracleT_emb (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (lw : Word r) (z : Model a m r P) :
    secOracleT (K := K) D (emb lw z) =
      emb lw (GateBinaryReuse.privateEverywhere (TimeDependent.slotAction D (2 ^ m)) (cap r) z) := by
  apply PiLp.ext
  intro x
  rw [secOracleT, slotOracle, localOp_apply]
  have hsec : (clearCfg Wire.anc x) .sec = x .sec := sec_overwrite x _
  have hslot : slotIdx (clearCfg Wire.anc x) = slotIdx x := slotIdx_overwrite x _
  by_cases hs : x .sec = true
  · have hc : ctrlOK [(Wire.sec, true)] (clearCfg Wire.anc x) = true := by
      simp [ctrlOK, hsec, hs]
    rw [if_pos hc, slice_emb_private lw z x hs, hslot]
    simp only [emb_apply, embVal, hs, if_true, GateBinaryReuse.privateEverywhere,
      LinearMap.coe_mk, AddHom.coe_mk, TimeDependent.slotAction_apply]
    split_ifs
    · rfl
    · simp
  · have hc : ¬ ctrlOK [(Wire.sec, true)] (clearCfg Wire.anc x) = true := by
      simp [ctrlOK, hsec, hs]
    rw [if_neg hc]
    change (slice Wire.anc (emb lw z) x) (ancOf x) = _
    rw [slice_apply, overwrite_anc_self]
    simp [emb_apply, embVal, hs, GateBinaryReuse.privateEverywhere]

theorem pres2_secOracleT (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    Pres2 Clean (secOracleT (K := K) (m := m) (r := r) D) :=
  pres2_slotOracle _ _

theorem secOracleT_isUnitary (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (hD : ∀ k < 2 ^ m, IsUnitary (D k)) :
    IsUnitary (secOracleT (K := K) (m := m) (r := r) D) :=
  slotOracle_isUnitary _ _ hD

/-! ### Instruction semantics -/

/-- `A` or its adjoint. -/
def adjT (adj : Bool) (A : Vsp a P →L[ℂ] Vsp a P) : Vsp a P →L[ℂ] Vsp a P :=
  if adj then A† else A

/-- One released instruction with the slot-selected private call. -/
def evalT (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    Instr (Wire a m r K) → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | .gate g => gateOp g.cs g.t g.u
  | .uj cs adj => oracleOp Wire.anc anc_injective cs (if adj then UJ† else UJ)
  | .priv cs adj => slotOracle cs (fun k => adjT adj (D k))

/-- Run a released instruction list with slot-selected private calls; the head
instruction acts first. -/
def runT (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    List (Instr (Wire a m r K)) → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | [] => 1
  | g :: gs => runT UJ D gs ∘L evalT UJ D g

section Run

variable (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)

@[simp] theorem runT_nil : runT UJ D ([] : List (Instr (Wire a m r K))) = 1 := rfl

theorem runT_cons (g : Instr (Wire a m r K)) (gs : List (Instr (Wire a m r K))) :
    runT UJ D (g :: gs) = runT UJ D gs ∘L evalT UJ D g := rfl

theorem runT_append (gs hs : List (Instr (Wire a m r K))) :
    runT UJ D (gs ++ hs) = runT UJ D hs ∘L runT UJ D gs := by
  induction gs with
  | nil => ext ψ; rfl
  | cons g gs ih => simp only [List.cons_append, runT_cons, ih, comp_assoc]

theorem runT_singleton (g : Instr (Wire a m r K)) : runT UJ D [g] = evalT UJ D g := by
  ext ψ; rfl

theorem adjT_adjoint (adj : Bool) (A : Vsp a P →L[ℂ] Vsp a P) :
    (adjT adj A)† = adjT (!adj) A := by
  cases adj <;> simp [adjT]

theorem evalT_inv (g : Instr (Wire a m r K)) : evalT UJ D g.inv = (evalT UJ D g)† := by
  cases g with
  | gate g => exact (gateOp_adjoint g.cs g.t g.u).symm
  | uj cs adj =>
      cases adj
      · have e1 : evalT UJ D (Instr.uj cs false).inv =
            oracleOp Wire.anc anc_injective cs (UJ†) := rfl
        have e2 : evalT UJ D (Instr.uj cs false) = oracleOp Wire.anc anc_injective cs UJ := rfl
        rw [e1, e2, oracleOp_adjoint]
      · have e1 : evalT UJ D (Instr.uj cs true).inv = oracleOp Wire.anc anc_injective cs UJ := rfl
        have e2 : evalT UJ D (Instr.uj cs true) =
            oracleOp Wire.anc anc_injective cs (UJ†) := rfl
        rw [e1, e2, oracleOp_adjoint, adjoint_adjoint]
  | priv cs adj =>
      have e1 : evalT UJ D (Instr.priv cs adj).inv =
          slotOracle cs (fun k => adjT (!adj) (D k)) := rfl
      have e2 : evalT UJ D (Instr.priv cs adj) = slotOracle cs (fun k => adjT adj (D k)) := rfl
      rw [e1, e2, slotOracle_adjoint]
      congr 1
      funext k
      rw [adjT_adjoint]

theorem adjT_isUnitary (adj : Bool) (A : Vsp a P →L[ℂ] Vsp a P) (hA : IsUnitary A) :
    IsUnitary (adjT adj A) := by
  cases adj
  · exact hA
  · simpa [adjT, star_eq_adjoint] using hA.adjoint

theorem evalT_isUnitary (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (g : Instr (Wire a m r K)) (hg : g.Valid Wire.anc) : IsUnitary (evalT UJ D g) := by
  cases g with
  | gate g => exact gateOp_isUnitary g.cs g.t g.u hg.2.2
  | uj cs adj =>
      apply oracleOp_isUnitary
      cases adj
      · exact hUJ
      · simpa [star_eq_adjoint] using hUJ.adjoint
  | priv cs adj =>
      show IsUnitary (slotOracle cs (fun k => adjT adj (D k)))
      exact slotOracle_isUnitary _ _ (fun k hk => adjT_isUnitary adj _ (hD k hk))

theorem runT_invList (gs : List (Instr (Wire a m r K))) :
    runT UJ D (invList gs) = (runT UJ D gs)† := by
  induction gs with
  | nil => simp [invList, runT]
  | cons g gs ih =>
      have h1 : invList (g :: gs) = invList gs ++ [g.inv] := by simp [invList]
      rw [h1, runT_append, ih, runT_singleton, evalT_inv, runT_cons, adjoint_comp]

theorem runT_isUnitary (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (gs : List (Instr (Wire a m r K))) (hgs : ∀ g ∈ gs, g.Valid Wire.anc) :
    IsUnitary (runT UJ D gs) := by
  induction gs with
  | nil => exact isUnitary_one
  | cons g gs ih =>
      rw [runT_cons, ← mul_def]
      exact (ih (fun h hh => hgs h (List.mem_cons_of_mem g hh))).mul
        (evalT_isUnitary UJ D hUJ hD g (hgs g List.mem_cons_self))

theorem runT_ofGates (gs : List (Gate (Wire a m r K))) : runT UJ D (ofGates gs) = gRun gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      simp only [ofGates, List.map_cons] at ih ⊢
      rw [runT_cons, ih]
      rfl

/-- Lists without private calls run as in the released semantics. -/
theorem runT_eq_run (D₀ : Vsp a P →L[ℂ] Vsp a P) (gs : List (Instr (Wire a m r K)))
    (hgs : ∀ g ∈ gs, g.isPriv = false) : runT UJ D gs = run (simSem UJ D₀) gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      rw [runT_cons, run_cons, ih (fun h hh => hgs h (List.mem_cons_of_mem g hh))]
      have hg := hgs g List.mem_cons_self
      cases g with
      | gate g => rfl
      | uj cs adj => rfl
      | priv cs adj => simp [Instr.isPriv] at hg

/-- Slot families agreeing on the `2^m` slots give the same instruction. -/
theorem evalT_congr (D' : ℕ → Vsp a P →L[ℂ] Vsp a P) (h : ∀ k < 2 ^ m, D k = D' k)
    (g : Instr (Wire a m r K)) : evalT UJ D g = evalT UJ D' g := by
  cases g with
  | gate g => rfl
  | uj cs adj => rfl
  | priv cs adj =>
      show slotOracle cs (fun k => adjT adj (D k)) = slotOracle cs (fun k => adjT adj (D' k))
      exact slotOracle_congr cs _ _ (fun k hk => by rw [h k hk])

/-- Slot families agreeing on the `2^m` slots run identically. -/
theorem runT_congr (D' : ℕ → Vsp a P →L[ℂ] Vsp a P) (h : ∀ k < 2 ^ m, D k = D' k)
    (gs : List (Instr (Wire a m r K))) : runT UJ D gs = runT UJ D' gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => rw [runT_cons, runT_cons, ih, evalT_congr UJ D D' h g]

theorem runT_privI : runT UJ D [privI (a := a) (m := m) (r := r) (K := K)] = secOracleT D := by
  rw [runT_singleton]
  rfl

theorem bnetI_noPriv (j : Fin (cap r + 1)) (c σ : ℝ) :
    ∀ g ∈ bnetI (a := a) (m := m) (K := K) j c σ, g.isPriv = false := by
  intro g hg
  simp only [bnetI, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, ofGates,
    List.mem_map] at hg
  rcases hg with (rfl | ⟨g', _, rfl⟩) | rfl <;> rfl

end Run

/-! ### Reuse steps and the SELECT circuit -/

/-- One reuse step at pointer word `j` with the slot-selected private call. -/
def STEPT (j : Fin (cap r + 1)) (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : ℕ → Vsp a P →L[ℂ] Vsp a P) : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  INC ∘L BNET j c σ UJ ∘L secOracleT D

theorem STEPT_emb (j : Fin (cap r + 1)) (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (hκ : κ = 1 - c) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hUJ : UJ ∘L UJ† = 1) (lw : Word r) (z : Model a m r P) :
    STEPT (K := K) j c σ UJ D (emb lw z) =
      emb lw (GateBinaryReuse.step (blkA c (2 ^ m)) (netB c σ UJ) (netC c σ UJ)
        (netG c κ σ UJ) (TimeDependent.slotAction D (2 ^ m)) j z) := by
  rw [STEPT, comp_apply, comp_apply, secOracleT_emb, BNET_emb j c κ σ hunit hκ UJ hUJ, INC_emb]
  rfl

/-- The SELECT circuit: `n` reuse steps at pointer words `0, …, n-1`. -/
def selectNT (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    ℕ → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | 0 => 1
  | n + 1 => if h : n < cap r + 1 then STEPT ⟨n, h⟩ c σ UJ D ∘L selectNT c σ UJ D n
      else selectNT c σ UJ D n

theorem selectNT_emb (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (hκ : κ = 1 - c)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1) (n : ℕ)
    (lw : Word r) (z : Model a m r P) :
    selectNT (K := K) c σ UJ D n (emb lw z) =
      emb lw (GateBinaryReuse.run (blkA c (2 ^ m)) (netB c σ UJ) (netC c σ UJ)
        (netG c κ σ UJ) (TimeDependent.slotAction D (2 ^ m)) (cap r) n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases h : n < cap r + 1
      · rw [selectNT, dif_pos h, comp_apply, ih, STEPT_emb _ c κ σ hunit hκ UJ D hUJ,
          GateBinaryReuse.run, dif_pos h]
        rfl
      · rw [selectNT, dif_neg h, ih, GateBinaryReuse.run, dif_neg h]

/-- The SELECT circuit between uniform pointer states of length `n` is the
coherent-reuse successful block of length `n` for the parallel slot action. -/
theorem select_blockT (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (hκ : κ = 1 - c)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (hUJ : UJ ∘L UJ† = 1)
    (lw : Word r) (n N : ℕ) (hnN : n ≤ N) (hN : N ≤ cap r) (ψ ψ' : P) :
    inner ℂ (emb (K := K) (m := m) lw (uIn n ψ'))
        (selectNT (m := m) (K := K) c σ UJ D N (emb lw (uIn n ψ))) =
      inner ℂ ψ' (successfulBlock (V := HV a m P) (blkA c (2 ^ m))
        (netB (m := m) c σ UJ ∘L TimeDependent.slotAction D (2 ^ m)) (netC (m := m) c σ UJ)
        (netG (m := m) c κ σ UJ ∘L TimeDependent.slotAction D (2 ^ m)) n ψ) := by
  set y : ℕ → P := fun k => extendSequence (uniformEmbedding n ψ) k with hy
  set y' : ℕ → P := fun k => extendSequence (uniformEmbedding n ψ') k with hy'
  rw [selectNT_emb c κ σ hunit hκ UJ D hUJ N lw]
  have hrun := GateBinaryReuse.run_invariant (blkA c (2 ^ m)) (netB (m := m) c σ UJ)
    (netC (m := m) c σ UJ) (netG (m := m) c κ σ UJ) (TimeDependent.slotAction D (2 ^ m)) (cap r) y N hN
  rw [show (uIn n ψ : Model a m r P) = ((fun k => y k.val), 0) from rfl, hrun,
    show (uIn n ψ' : Model a m r P) = ((fun k => y' k.val), 0) from rfl, inner_emb_public]
  rw [successfulBlock, comp_apply, comp_apply, adjoint_inner_right, PiLp.inner_apply]
  have hz : ∀ k, n ≤ k → y' k = 0 := by
    intro k hk
    simp only [hy', extendSequence, dif_neg (by omega : ¬ k < n)]
  let f : ℕ → ℂ := fun k => inner ℂ (y' k)
    (if k < N then blkA c (2 ^ m) (y k) + netB (m := m) c σ UJ ((TimeDependent.slotAction D (2 ^ m))
      (forcedPublicState (netG (m := m) c κ σ UJ ∘L (TimeDependent.slotAction D (2 ^ m))) (netC (m := m) c σ UJ) y k)) else y k)
  have hL : ∀ k : Fin (cap r + 1), inner ℂ (y' k.val)
      (GateBinaryReuse.publicBefore (blkA c (2 ^ m)) (netB (m := m) c σ UJ)
        (netC (m := m) c σ UJ) (netG (m := m) c κ σ UJ) (TimeDependent.slotAction D (2 ^ m)) (cap r) N y k) = f k.val :=
    fun k => rfl
  simp only [hL]
  rw [sum_ptr_eq n (by omega) f (fun k hk => by simp only [f, hz k hk, inner_zero_left])]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k : ℕ) < N := lt_of_lt_of_le k.isLt hnN
  have hpr : publicReuse (blkA c (2 ^ m)) (netB (m := m) c σ UJ ∘L (TimeDependent.slotAction D (2 ^ m))) (netC (m := m) c σ UJ)
      (netG (m := m) c κ σ UJ ∘L (TimeDependent.slotAction D (2 ^ m))) n (uniformEmbedding n ψ) k =
        blkA c (2 ^ m) (y k) + (netB (m := m) c σ UJ ∘L (TimeDependent.slotAction D (2 ^ m)))
          (forcedPublicState (netG (m := m) c κ σ UJ ∘L (TimeDependent.slotAction D (2 ^ m))) (netC (m := m) c σ UJ) y k) := by
    have h := chronologicalOperator_apply (blkA c (2 ^ m)) (netB (m := m) c σ UJ ∘L (TimeDependent.slotAction D (2 ^ m)))
      (netG (m := m) c κ σ UJ ∘L (TimeDependent.slotAction D (2 ^ m))) (netC (m := m) c σ UJ) y k
    rw [show (WithLp.toLp 2 (fun k : Fin n => y k) : BlockOperator.H n P) =
      uniformEmbedding n ψ from restrict_extend _] at h
    rw [publicReuse, h]
    rfl
  simp only [f, if_pos hk, hpr, comp_apply]
  congr 1
  simp only [hy', extendSequence_apply]

/-! ### Unitarity and clean invariance -/

theorem pres2_STEPT (j : Fin (cap r + 1)) (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P)
    (D : ℕ → Vsp a P →L[ℂ] Vsp a P) : Pres2 Clean (STEPT (K := K) (m := m) j c σ UJ D) :=
  pres2_INC.comp ((pres2_BNET _ _ _ _).comp (pres2_secOracleT _))

theorem pres2_selectNT (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (n : ℕ) : Pres2 Clean (selectNT (K := K) (m := m) (r := r) c σ UJ D n) := by
  induction n with
  | zero => exact pres2_one _
  | succ n ih =>
      rw [selectNT]
      split_ifs
      · exact (pres2_STEPT _ _ _ _ _).comp ih
      · exact ih

theorem STEPT_isUnitary (j : Fin (cap r + 1)) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k)) : IsUnitary (STEPT (K := K) (m := m) j c σ UJ D) :=
  isUnitary_comp INC_isUnitary
    (isUnitary_comp (BNET_isUnitary _ _ _ hunit _ hUJ) (secOracleT_isUnitary _ hD))

theorem selectNT_isUnitary (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k)) (n : ℕ) :
    IsUnitary (selectNT (K := K) (m := m) (r := r) c σ UJ D n) := by
  induction n with
  | zero => exact isUnitary_one
  | succ n ih =>
      rw [selectNT]
      split_ifs
      · exact isUnitary_comp (STEPT_isUnitary _ _ _ hunit _ _ hUJ hD) ih
      · exact ih

/-! ### Agreement with the ideal operators -/

theorem stepT_agrees (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (j : Fin (cap r + 1)) (c σ : ℝ) (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (runT UJ D (stepI (a := a) (m := m) (K := K) j c σ)) (STEPT j c σ UJ D) := by
  rw [stepI, runT_append, runT_append, runT_privI, runT_ofGates,
    runT_eq_run UJ D 0 _ (bnetI_noPriv j c σ), STEPT]
  exact ((Agrees.refl _ _).comp (pres2_secOracleT _).1 (bnet_agrees UJ 0 j c σ hK)).comp
    ((pres2_BNET _ _ _ _).comp (pres2_secOracleT _)).1 inc_agrees

theorem selectT_agrees (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (c σ : ℝ)
    (hK : a + m + 2 * r ≤ K) (n : ℕ) :
    Agrees Clean (runT UJ D (selectI (a := a) (m := m) (r := r) (K := K) c σ n))
      (selectNT c σ UJ D n) := by
  induction n with
  | zero => exact Agrees.refl _ _
  | succ n ih =>
      rw [selectI, runT_append, selectNT]
      split_ifs with h
      · exact ih.comp (pres2_selectNT _ _ _ _ _).1 (stepT_agrees UJ D _ c σ hK)
      · have h0 : runT (m := m) (r := r) (K := K) UJ D ([] : List (Instr (Wire a m r K))) = 1 :=
          rfl
        rw [h0, one_comp']
        exact ih

end

end SparseHamiltonian.GateCircuit.SlotSim
