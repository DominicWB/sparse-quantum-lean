import GateEfficientHamiltonian.Circuit.Dyadic

/-!
# The wire layout of the gate-level simulator

Logical wires: `a` ancillas of `U_J`, the public/private sector bit, `m` time
slot bits, an `r`-bit reuse pointer and an `r`-bit LCU label.  Work wires:
the network enable flag `hf`, prefix flags `pf`, the label flag `lf`, tight
flags `tf`, carry flags `cf` and a pool `wk` for AND chains.  Every work wire
is clean (zero) between macro operations.

`emb lw z` places a state of the coherent-reuse model `GateBinaryReuse` into
the register with label word `lw`: the public amplitude of pointer word `k`
sits on the public mode (sector zero, slot zero, ancillas zero), and the
private amplitude of slot `σ` on the private sector.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)
open ChronologicalResolvent

/-- The wires of the simulator. -/
inductive Wire (a m r K : ℕ)
  | anc (i : Fin a)
  | sec
  | slot (i : Fin m)
  | ptr (i : Fin r)
  | lab (i : Fin r)
  | hf
  | pf (i : Fin m)
  | lf
  | tf (i : Fin r)
  | cf (i : Fin r)
  | wk (i : Fin K)
  deriving DecidableEq, Fintype

variable {a m r K : ℕ}

theorem anc_injective : Function.Injective (Wire.anc : Fin a → Wire a m r K) :=
  fun _ _ h => by cases h; rfl

/-- The work wires. -/
def isFlag : Wire a m r K → Bool
  | .hf => true
  | .pf _ => true
  | .lf => true
  | .tf _ => true
  | .cf _ => true
  | .wk _ => true
  | _ => false

/-- All work wires are zero. -/
def Clean (x : Cfg (Wire a m r K)) : Prop := ∀ w, isFlag w = true → x w = false

instance (x : Cfg (Wire a m r K)) : Decidable (Clean x) := by
  unfold Clean; infer_instance

abbrev Word (n : ℕ) := Fin n → Bool

def ancOf (x : Cfg (Wire a m r K)) : Cfg (Fin a) := fun i => x (.anc i)
def slotOf (x : Cfg (Wire a m r K)) : Word m := fun i => x (.slot i)
def ptrOf (x : Cfg (Wire a m r K)) : Word r := fun i => x (.ptr i)
def labOf (x : Cfg (Wire a m r K)) : Word r := fun i => x (.lab i)

/-- The zero word. -/
abbrev zw (n : ℕ) : Word n := fun _ => false

/-- Capacity of the reuse pointer: its words are `0, …, 2^r - 1`. -/
abbrev cap (r : ℕ) : ℕ := 2 ^ r - 1

theorem cap_succ (r : ℕ) : cap r + 1 = 2 ^ r := Nat.sub_add_cancel Nat.one_le_two_pow

/-- The pointer word as an index of the reuse model. -/
def ptrIdx (x : Cfg (Wire a m r K)) : Fin (cap r + 1) :=
  Fin.cast (cap_succ r).symm (wordEquivFin r (ptrOf x))

/-- The slot word as a time-slot index. -/
def slotIdx (x : Cfg (Wire a m r K)) : Fin (2 ^ m) := wordEquivFin m (slotOf x)

/-! ### Overwriting the ancilla wires -/

theorem overwrite_anc_anc (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) (i : Fin a) :
    overwrite Wire.anc x b (.anc i) = b i :=
  joinCfg_apply_ι anc_injective _ b i

theorem overwrite_anc_other (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) (w : Wire a m r K)
    (hw : ∀ i, Wire.anc i ≠ w) : overwrite Wire.anc x b w = x w :=
  joinCfg_apply_out Wire.anc (outPart Wire.anc x) b ⟨w, hw⟩

@[simp] theorem ancOf_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    ancOf (overwrite Wire.anc x b) = b := by
  funext i; exact overwrite_anc_anc x b i

@[simp] theorem sec_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    overwrite Wire.anc x b .sec = x .sec :=
  overwrite_anc_other x b _ (fun _ h => by cases h)

@[simp] theorem slotOf_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    slotOf (overwrite Wire.anc x b) = slotOf x := by
  funext i; exact overwrite_anc_other x b _ (fun _ h => by cases h)

@[simp] theorem ptrOf_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    ptrOf (overwrite Wire.anc x b) = ptrOf x := by
  funext i; exact overwrite_anc_other x b _ (fun _ h => by cases h)

@[simp] theorem labOf_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    labOf (overwrite Wire.anc x b) = labOf x := by
  funext i; exact overwrite_anc_other x b _ (fun _ h => by cases h)

@[simp] theorem ptrIdx_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    ptrIdx (overwrite Wire.anc x b) = ptrIdx x := by
  simp [ptrIdx]

@[simp] theorem slotIdx_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    slotIdx (overwrite Wire.anc x b) = slotIdx x := by
  simp [slotIdx]

theorem clean_overwrite (x : Cfg (Wire a m r K)) (b : Cfg (Fin a)) :
    Clean (overwrite Wire.anc x b) ↔ Clean x := by
  unfold Clean
  have h : ∀ w : Wire a m r K, isFlag w = true → overwrite Wire.anc x b w = x w := by
    intro w hw
    apply overwrite_anc_other
    intro i hi
    subst hi
    simp [isFlag] at hw
  constructor
  · intro hc w hw; rw [← h w hw]; exact hc w hw
  · intro hc w hw; rw [h w hw]; exact hc w hw

theorem overwrite_anc_self (x : Cfg (Wire a m r K)) :
    overwrite Wire.anc x (ancOf x) = x :=
  joinCfg_self anc_injective x

/-! ### The embedding of the reuse model -/

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The private space of one time slot: `U_J`-ancillas and the system. -/
abbrev Vsp (a : ℕ) (P : Type*) := Anc a P

/-- All time slots. -/
abbrev HV (a m : ℕ) (P : Type*) := BlockOperator.H (2 ^ m) (Vsp a P)

/-- The coherent-reuse model of `GateBinaryReuse` for this layout. -/
abbrev Model (a m r : ℕ) (P : Type*) [NormedAddCommGroup P] [InnerProductSpace ℂ P] :=
  GateBinaryReuse.Registers (P := P) (V := HV a m P) (cap r)

/-- Value of the embedded state at one configuration. -/
def embVal (lw : Word r) (z : Model a m r P) (x : Cfg (Wire a m r K)) : P :=
  if labOf x = lw ∧ Clean x then
    (if x .sec then z.2 (ptrIdx x) (slotIdx x) (ancOf x)
     else if slotOf x = zw m ∧ ancOf x = zw a then z.1 (ptrIdx x) else 0)
  else 0

/-- Embed a reuse-model state with label word `lw`. -/
def emb (lw : Word r) (z : Model a m r P) : Reg (Wire a m r K) P :=
  WithLp.toLp 2 (embVal lw z)

omit [CompleteSpace P] in
@[simp] theorem emb_apply (lw : Word r) (z : Model a m r P) (x : Cfg (Wire a m r K)) :
    emb (K := K) lw z x = embVal lw z x := rfl

/-- The slots-everywhere private operation. -/
def diagV (O : Vsp a P →L[ℂ] Vsp a P) : HV a m P →L[ℂ] HV a m P :=
  WeightedClock.diagonal (fun _ : Fin (2 ^ m) => O)

omit [CompleteSpace P] in
@[simp] theorem diagV_apply (O : Vsp a P →L[ℂ] Vsp a P) (v : HV a m P) (k : Fin (2 ^ m)) :
    diagV O v k = O (v k) := rfl

/-- The sector-controlled oracle call. -/
def secOracle (O : Vsp a P →L[ℂ] Vsp a P) : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  oracleOp Wire.anc anc_injective [(.sec, true)] O

omit [CompleteSpace P] in
theorem slice_emb_private (lw : Word r) (z : Model a m r P) (x : Cfg (Wire a m r K))
    (hs : x .sec = true) :
    slice Wire.anc (emb lw z) x =
      if labOf x = lw ∧ Clean x then z.2 (ptrIdx x) (slotIdx x) else 0 := by
  apply PiLp.ext
  intro b
  simp only [slice_apply, emb_apply, embVal, labOf_overwrite, clean_overwrite,
    sec_overwrite, hs, if_true, ptrIdx_overwrite, slotIdx_overwrite, ancOf_overwrite]
  split_ifs <;> rfl

/-- The private operation acts on every private slot and pointer word. -/
theorem secOracle_emb (O : Vsp a P →L[ℂ] Vsp a P) (lw : Word r) (z : Model a m r P) :
    secOracle (K := K) O (emb lw z) =
      emb lw (GateBinaryReuse.privateEverywhere (diagV O) (cap r) z) := by
  apply PiLp.ext
  intro x
  rw [secOracle, oracleOp, localOp_apply]
  have hsec : (clearCfg Wire.anc x) .sec = x .sec := sec_overwrite x _
  by_cases hs : x .sec = true
  · have hc : ctrlOK [(Wire.sec, true)] (clearCfg Wire.anc x) = true := by
      simp [ctrlOK, hsec, hs]
    rw [if_pos hc, slice_emb_private lw z x hs]
    simp only [emb_apply, embVal, hs, if_true, GateBinaryReuse.privateEverywhere,
      LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs
    · rfl
    · simp
  · have hc : ¬ ctrlOK [(Wire.sec, true)] (clearCfg Wire.anc x) = true := by
      simp [ctrlOK, hsec, hs]
    rw [if_neg hc]
    change (slice Wire.anc (emb lw z) x) (ancOf x) = _
    rw [slice_apply, overwrite_anc_self]
    simp [emb_apply, embVal, hs, GateBinaryReuse.privateEverywhere]

end

end SparseHamiltonian.GateCircuit.Sim
