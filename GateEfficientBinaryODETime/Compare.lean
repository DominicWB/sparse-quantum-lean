import GateEfficientBinaryODE.ProgramVal

/-!
# The slot comparator

At time slot `r` the branch of the source label `(ini, u)` evolves exactly when its start slot
`start = (ini ? u : 0)` is at most `r` (`TimeDependentODE.mask start r = [start ≤ r]`). The
decoded value of the time-dependent private operation therefore carries the factor
`[start ≤ r] = 1 - [ini ∧ r < u]`.

The comparator is a two-operation register program of `GateEfficientBinary` on the registers of
`GateEfficientBinaryODE.Program`, with the layout `cLay m` (its stored-bits field `m` sets the
register width `m + 14`; without fractional, LCHS or node bits the register set
`GateBinaryODE.RO (cLay m)` has 62 registers, of which the comparator uses two):

* `du := r - u` for the slot word `r` and the node word `u` (unsigned, `m` bits each);
* `de := du ± du`, with `+` exactly when the source sector bit `ini` is set,

so that `de = (ini ? 2 (r - u) : 0)` and its sign bit is `ini ∧ r < u` (`msb_cde`). It is a
single-assignment program (`cmpOK`), and its register values are exact (`v_cdu`, `v_cde`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODETime

open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open GatePointerEncoding (wordValue)

/-- The layout of the comparator registers: width `m + 14` (only the width is used). -/
def cLay (m : ℕ) : Lay := ⟨m, 0, 0, 0, 0, 0, 0⟩

theorem cLay_w (m : ℕ) : (cLay m).w = m + 14 := by
  simp [cLay, Lay.w]

section Ops

variable {B : Type} {m : ℕ}

/-- An unsigned input word as the second operand of a register operation. -/
def uB (r : Fin m → B) : ℕ → BSrc (PW B (cLay m)) := fun i => .lit (uA r i) true

/-- **The comparator program**: `du := r - u` and `de := du ± du`, with `+` exactly when `ini`
is set. -/
def cmpOps (ini : B) (sl u : Fin m → B) : List (ROp B (RO (cLay m)) (cLay m).w) :=
  [⟨.du, uA sl, uB u, .const true⟩, ⟨.de, rA .du, rB .du, .lit (.inl ini) false⟩]

/-- The comparator is a single-assignment program. -/
theorem cmpOK (ini : B) (sl u : Fin m → B) : ProgOK (lvO (cLay m)) (cmpOps ini sl u) := by
  refine ⟨?_, ?_⟩
  · simp only [cmpOps, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, List.Pairwise.nil, IsEmpty.forall_iff, implies_true, and_true, lvO]
    omega
  · intro o ho
    simp only [cmpOps, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · exact ⟨by simp [lvO], fun i _ => readable_uA _ sl i, fun i _ => readable_uA _ u i, trivial⟩
    · exact ⟨by simp [lvO], fun i _ => readable_rA (by simp [lvO]) i,
        fun i _ => on_rB (by simp [lvO]) i, trivial⟩

/-- The comparator registers on the input configuration `x`. -/
def cregs (ini : B) (sl u : Fin m → B) (x : B → Bool) : RO (cLay m) → BitVec (cLay m).w :=
  runOps x (cmpOps ini sl u) 0

theorem cregs_dst (ini : B) (sl u : Fin m → B) (x : B → Bool) :
    ∀ o ∈ cmpOps ini sl u, cregs ini sl u x o.dst = o.val (cfgOf x (cregs ini sl u x)) :=
  runOps_dst (lvO (cLay m)) _ (cmpOK ini sl u) x 0

theorem ofBits_uB (r : Fin m → B) (y : PW B (cLay m) → Bool) :
    ofBits (fun i => (uB r i).val y) (cLay m).w = readBV (uA r) (cLay m).w y := by
  apply ofBits_congr
  intro i _
  simp [uB, BSrc.val]

theorem m_le_w (m : ℕ) : m ≤ (cLay m).w := by
  rw [cLay_w]
  omega

/-- The first comparator register holds `r - u`. -/
theorem v_cdu (ini : B) (sl u : Fin m → B) (x : B → Bool) :
    cregs ini sl u x .du = BitVec.ofInt (cLay m).w
      ((wordValue (fun j => x (sl j)) : ℤ) - wordValue (fun j => x (u j))) := by
  have hd := cregs_dst ini sl u x _ List.mem_cons_self
  change cregs ini sl u x .du = ROp.val ⟨.du, uA sl, uB u, .const true⟩
    (cfgOf x (cregs ini sl u x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_uA x _ sl (m_le_w m))
    (by rw [ofBits_uB, readBV_uA x _ u (m_le_w m)])]
  congr 1

/-- The second comparator register holds `ini ? 2 (r - u) : 0`. -/
theorem v_cde (ini : B) (sl u : Fin m → B) (x : B → Bool) :
    cregs ini sl u x .de = BitVec.ofInt (cLay m).w (if x ini then
      2 * ((wordValue (fun j => x (sl j)) : ℤ) - wordValue (fun j => x (u j))) else 0) := by
  have hd := cregs_dst ini sl u x _ (List.mem_cons_of_mem _ List.mem_cons_self)
  change cregs ini sl u x .de = ROp.val ⟨.de, rA .du, rB .du, .lit (.inl ini) false⟩
    (cfgOf x (cregs ini sl u x)) at hd
  rw [hd, val_mk _ _ _ _ _
    ((wordValue (fun j => x (sl j)) : ℤ) - wordValue (fun j => x (u j)))
    ((wordValue (fun j => x (sl j)) : ℤ) - wordValue (fun j => x (u j)))
    (by rw [readBV_rA, v_cdu]) (by rw [ofBits_rB, v_cdu])]
  congr 1
  rcases Bool.eq_false_or_eq_true (x ini) with h | h <;> simp [BSrc.val, cfg_inl, h]
  ring

/-- **The comparator bit**: the sign bit of the second register is `ini ∧ r < u`. -/
theorem msb_cde (ini : B) (sl u : Fin m → B) (x : B → Bool) :
    (cregs ini sl u x .de).getLsbD ((cLay m).w - 1) =
      (x ini && decide (wordValue (fun j => x (sl j)) < wordValue (fun j => x (u j)))) := by
  have hr := GatePointerEncoding.wordValue_lt_pow (fun j => x (sl j))
  have hu := GatePointerEncoding.wordValue_lt_pow (fun j => x (u j))
  have hw : (cLay m).w - 1 = m + 13 := by
    rw [cLay_w]
    omega
  have hb : |(if x ini then 2 * ((wordValue (fun j => x (sl j)) : ℤ) -
      wordValue (fun j => x (u j))) else 0)| < 2 ^ ((cLay m).w - 1) := by
    have hr' : ((wordValue (fun j => x (sl j)) : ℕ) : ℤ) < 2 ^ m := by exact_mod_cast hr
    have hu' : ((wordValue (fun j => x (u j)) : ℕ) : ℤ) < 2 ^ m := by exact_mod_cast hu
    have hp : (2 : ℤ) * 2 ^ m < 2 ^ ((cLay m).w - 1) := by
      rw [hw, ← pow_succ']
      exact pow_lt_pow_right₀ (by norm_num) (by omega)
    split_ifs
    · rw [abs_lt]
      constructor <;> omega
    · simp only [abs_zero]
      positivity
  rw [v_cde, msb_ofInt _ w_pos hb]
  rcases Bool.eq_false_or_eq_true (x ini) with h | h
  · simp only [h, if_true, Bool.true_and, decide_eq_decide]
    omega
  · simp [h]

end Ops

end SparseHamiltonian.GateBinaryODETime
