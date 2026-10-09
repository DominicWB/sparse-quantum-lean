import GateEfficientBinaryODE.ProgramVal
import GateEfficientHamiltonian.Circuit.Range

/-!
# The address program

On the power-of-two source mesh with `2^m` nodes `v_u = u T / 2^m` and `M = 2^m` slots per
branch, the sample address of slot `r` of the branch of the source label `(ini, u)` is
(Lemma `ode:lem:gate-select`, proof)

`v + r (T - v) / 2^m = T (2^m u' + r (2^m - u')) / 2^(2m)`,   `u' = (ini ? u : 0)`,

where the bit `ini` is the sector bit of the released source labels: it is set on the forcing
labels `(true, u)`, whose branch starts at the node `u T / 2^m`, and clear on the initial
labels, whose branch starts at `0`;

an integer address `g = 2^m u' + r (2^m - u') < 2^(2m)` on a uniform grid of `2^(2m)` points,
"computed by multiplication and addition on `O(log m + log M)` bits". The branch scale
`(T - v)/T` is `dv / 2^m` with the duration word `dv = 2^m - u'`.

The address program is a single-assignment register program of `GateEfficientBinary` on the
registers `GateBinaryODE.RO (aLay m)` of width `2m + 14` (the layout `aLay m` has `m` stored
bits and `m` fractional bits, so that its first chain has `m + 2` registers):

* `ax1 := u ± u` (`+` exactly when `ini` is set): `2 u'`;
* `n1 := 0 - ax1`: `-2 u'`, whose sign bit is `u' > 0` and whose bits `1, …, m` are the word
  `2^m - u'` when `u' > 0` (`n1_msb`, `n1_word`): the duration word read by the angle arithmetic;
* `z1 := ax1 - 2^(m+1)`: `-2 dv`;
* the multiplication chain `GateBinaryODE.chain` (module `GateEfficientBinaryODE.Program`) with
  the slot digits: `2 r (-2 dv)`;
* `md := (ax1 << (m+1)) - chain`: `4 g`, whose bits `2, …, 2m + 1` are the address word
  (`md_word`).

`addrOK`: single assignment; `v_ax1`, `v_n1`, `v_z1`, `v_acc`, `v_md`: the register values;
`length_addrG`: at most `13 (2m + 14) (m + 5)` gates.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinarySelect

open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open GatePointerEncoding (wordValue bitValue)

/-- The layout of the address registers: width `2m + 14`, chain registers `hc 0, …, hc (m+1)`. -/
def aLay (m : ℕ) : Lay := ⟨m, 0, 0, 0, 0, m, 0⟩

theorem aLay_w (m : ℕ) : (aLay m).w = 2 * m + 14 := by
  simp only [aLay, Lay.w]
  ring

theorem aLay_F (m : ℕ) : (aLay m).F = m := rfl

/-! ### Words and bits -/

/-- A word whose bits are those of `N < 2^r` has the value `N`. -/
theorem wordValue_testBit {r : ℕ} (N : ℕ) (hN : N < 2 ^ r) :
    wordValue (fun j : Fin r => N.testBit j) = N := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < r
  · exact GateCircuit.testBit_wordValue (fun j : Fin r => N.testBit j) ⟨i, hi⟩
  · rw [GateCircuit.testBit_wordValue_ge _ i (Nat.le_of_not_lt hi),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hN (Nat.pow_le_pow_right (by norm_num)
        (Nat.le_of_not_lt hi)))]

/-- A word is determined by its bits: equal bits give equal values. -/
theorem wordValue_congr {r : ℕ} (w w' : Fin r → Bool) (h : ∀ j, w j = w' j) :
    wordValue w = wordValue w' := by
  rw [funext h]

section Ops

variable {B : Type} {m : ℕ}

/-- An unsigned input word as the second operand of a register operation. -/
def uBa (r : Fin m → B) : ℕ → BSrc (PW B (aLay m)) := fun i => .lit (uA r i) true

/-- The slot digits of the multiplication chain. -/
def dgA (sl : Fin m → B) : ℕ → BSrc (PW B (aLay m)) :=
  fun j => if h : j < m then .lit (.inl (sl ⟨j, h⟩)) true else .const false

/-- The registers of the multiplication chain. -/
def accA (j : Fin (m + 1)) : RO (aLay m) := .hc ⟨j.val, by rw [aLay_F]; omega⟩

theorem lvO_accA (j : Fin (m + 1)) : lvO (aLay m) (accA j) = 25 + j.val := rfl

/-- The first three operations: `ax1 := u ± u`, `n1 := 0 - ax1`, `z1 := ax1 - 2^(m+1)`. -/
def opsA3 (ini : B) (u : Fin m → B) : List (ROp B (RO (aLay m)) (aLay m).w) :=
  [⟨.ax1, uA u, uBa u, .lit (.inl ini) false⟩,
   ⟨.n1, zA, rB .ax1, .const true⟩,
   ⟨.z1, rA .ax1, cB (2 ^ (m + 1)), .const true⟩]

/-- The chain `2 r z1` with the slot digits. -/
def chainA (sl : Fin m → B) : List (ROp B (RO (aLay m)) (aLay m).w) :=
  chain (m := m) accA .z1 (dgA sl)

/-- The last operation: `md := (ax1 << (m+1)) - acc_m`. -/
def opMd : ROp B (RO (aLay m)) (aLay m).w :=
  ⟨.md, shA .ax1 (m + 1), rB (accA (Fin.last m)), .const true⟩

/-- **The address program.** -/
def addrOps (ini : B) (u sl : Fin m → B) : List (ROp B (RO (aLay m)) (aLay m).w) :=
  opsA3 ini u ++ chainA sl ++ [opMd]

theorem length_addrOps (ini : B) (u sl : Fin m → B) : (addrOps ini u sl).length = m + 5 := by
  simp only [addrOps, opsA3, chainA, chain, opMd, List.length_append, List.length_cons,
    List.length_map, List.length_finRange, List.length_nil]
  ring

end Ops

/-! ### Single assignment -/

section OK

variable {B : Type} {m : ℕ}

theorem opsA3_ok (ini : B) (u : Fin m → B) :
    (opsA3 ini u).Pairwise (fun o o' => lvO (aLay m) o.dst < lvO (aLay m) o'.dst) ∧
      ∀ o ∈ opsA3 ini u, o.OK (fun r => lvO (aLay m) r < lvO (aLay m) o.dst) ∧
        lvO (aLay m) o.dst ≤ 2 := by
  refine ⟨?_, ?_⟩
  · simp only [opsA3, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, IsEmpty.forall_iff, implies_true, and_true,
      lvO]
    omega
  · intro o ho
    simp only [opsA3, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact ⟨⟨by simp [lvO], fun i _ => readable_uA _ u i, fun i _ => readable_uA _ u i,
        trivial⟩, by simp [lvO]⟩
    · exact ⟨⟨by simp [lvO], fun i _ => readable_zA _ i, fun i _ => on_rB (by simp [lvO]) i,
        trivial⟩, by simp [lvO]⟩
    · exact ⟨⟨by simp [lvO], fun i _ => readable_rA (by simp [lvO]) i, fun i _ => on_cB _ _ i,
        trivial⟩, by simp [lvO]⟩

theorem chainA_ok (sl : Fin m → B) :
    (chainA sl).Pairwise (fun o o' => lvO (aLay m) o.dst < lvO (aLay m) o'.dst) ∧
      ∀ o ∈ chainA sl, o.OK (fun r => lvO (aLay m) r < lvO (aLay m) o.dst) ∧
        25 ≤ lvO (aLay m) o.dst ∧ lvO (aLay m) o.dst ≤ 25 + m := by
  refine chain_ok _ _ _ 25 lvO_accA (by simp [lvO]) (fun j hj => ?_)
  simp only [dgA, hj, dif_pos]
  trivial

theorem opMd_ok :
    (opMd : ROp B (RO (aLay m)) (aLay m).w).OK
        (fun r => lvO (aLay m) r < lvO (aLay m) (opMd : ROp B (RO (aLay m)) (aLay m).w).dst) ∧
      lvO (aLay m) (opMd : ROp B (RO (aLay m)) (aLay m).w).dst = m + 27 := by
  refine ⟨⟨by simp [opMd, lvO], fun i _ => readable_shA (by simp [opMd, lvO]) _ i,
    fun i _ => on_rB (by simp only [opMd, lvO_accA, Fin.val_last]; simp only [lvO, aLay_F]; omega)
      i,
    trivial⟩, ?_⟩
  simp [opMd, lvO, aLay_F]

/-- **The address program is a single-assignment program.** -/
theorem addrOK (ini : B) (u sl : Fin m → B) : ProgOK (lvO (aLay m)) (addrOps ini u sl) := by
  obtain ⟨hA1, hA2⟩ := opsA3_ok ini u
  obtain ⟨hC1, hC2⟩ := chainA_ok sl
  obtain ⟨hM1, hM2⟩ := opMd_ok (B := B) (m := m)
  refine ⟨?_, ?_⟩
  · simp only [addrOps, List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
      forall_eq, true_and]
    refine ⟨⟨hA1, hC1, ?_⟩, ?_⟩
    · intro o ho o' ho'
      have := (hA2 o ho).2
      have := (hC2 o' ho').2.1
      omega
    · intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · have := (hA2 o ho).2
        omega
      · have := (hC2 o ho).2.2
        omega
  · intro o ho
    simp only [addrOps, List.mem_append, List.mem_singleton] at ho
    rcases ho with (ho | ho) | rfl
    · exact (hA2 o ho).1
    · exact (hC2 o ho).1
    · exact hM1

end OK

/-! ### Register values -/

section Values

variable {B : Type} {m : ℕ} (ini : B) (u sl : Fin m → B) (x : B → Bool)

/-- The register file of the address program on the input configuration `x`. -/
def regsA : RO (aLay m) → BitVec (aLay m).w := runOps x (addrOps ini u sl) 0

theorem regsA_dst :
    ∀ o ∈ addrOps ini u sl, regsA ini u sl x o.dst = o.val (cfgOf x (regsA ini u sl x)) :=
  runOps_dst (lvO (aLay m)) _ (addrOK ini u sl) x 0

/-- The start word `u' = (ini ? u : 0)`. -/
def uP : ℕ := if x ini then wordValue (fun j => x (u j)) else 0

/-- The slot word `r`. -/
def rS : ℕ := wordValue (fun j => x (sl j))

/-- **The address** `g = 2^m u' + r (2^m - u')`. -/
def gA : ℕ := 2 ^ m * uP ini u x + rS sl x * (2 ^ m - uP ini u x)

theorem uP_lt : uP ini u x < 2 ^ m := by
  unfold uP
  split_ifs
  · exact GatePointerEncoding.wordValue_lt_pow _
  · exact Nat.pos_of_ne_zero (by positivity)

theorem rS_lt : rS sl x < 2 ^ m := GatePointerEncoding.wordValue_lt_pow _

theorem gA_lt : gA ini u sl x < 2 ^ (2 * m) := by
  have hu := uP_lt ini u x
  have hr := rS_lt sl x
  unfold gA
  have hle : rS sl x * (2 ^ m - uP ini u x) ≤ (2 ^ m - 1) * (2 ^ m - uP ini u x) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [h2]
  have h3 : (2 ^ m - 1) * (2 ^ m - uP ini u x) + 2 ^ m * uP ini u x =
      2 ^ m * 2 ^ m - (2 ^ m - uP ini u x) := by
    have e1 : (2 ^ m - 1) * (2 ^ m - uP ini u x) =
        2 ^ m * (2 ^ m - uP ini u x) - (2 ^ m - uP ini u x) := by
      rw [Nat.sub_mul, one_mul]
    have e2 : 2 ^ m * (2 ^ m - uP ini u x) + 2 ^ m * uP ini u x = 2 ^ m * 2 ^ m := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hu.le]
    have e3 : (2 ^ m - uP ini u x) ≤ 2 ^ m * (2 ^ m - uP ini u x) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have h4 : 0 < 2 ^ m - uP ini u x := by omega
  have h5 : 2 ^ m - uP ini u x ≤ 2 ^ m * 2 ^ m :=
    le_trans (Nat.sub_le _ _) (Nat.le_mul_of_pos_right _ (by positivity))
  omega

theorem m_le_wA : m ≤ (aLay m).w := by
  rw [aLay_w]
  omega

theorem ofBits_uBa (r : Fin m → B) (y : PW B (aLay m) → Bool) :
    ofBits (fun i => (uBa r i).val y) (aLay m).w = readBV (uA r) (aLay m).w y := by
  apply ofBits_congr
  intro i _
  simp [uBa, BSrc.val]

theorem v_ax1 : regsA ini u sl x .ax1 = BitVec.ofInt (aLay m).w (2 * (uP ini u x : ℤ)) := by
  have hd := regsA_dst ini u sl x ⟨.ax1, uA u, uBa u, .lit (.inl ini) false⟩
    (by simp [addrOps, opsA3])
  change regsA ini u sl x .ax1 = ROp.val ⟨.ax1, uA u, uBa u, .lit (.inl ini) false⟩
    (cfgOf x (regsA ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_uA x _ u m_le_wA)
    (by rw [ofBits_uBa, readBV_uA x _ u m_le_wA])]
  congr 1
  unfold uP
  rcases Bool.eq_false_or_eq_true (x ini) with h | h <;> simp [BSrc.val, cfg_inl, h]
  ring

theorem v_n1 : regsA ini u sl x .n1 = BitVec.ofInt (aLay m).w (-(2 * (uP ini u x : ℤ))) := by
  have hd := regsA_dst ini u sl x ⟨.n1, zA, rB .ax1, .const true⟩ (by simp [addrOps, opsA3])
  change regsA ini u sl x .n1 = ROp.val ⟨.n1, zA, rB .ax1, .const true⟩
    (cfgOf x (regsA ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (2 * (uP ini u x : ℤ)) (readBV_zA x _)
    (by rw [ofBits_rB, v_ax1])]
  simp [BSrc.val]

theorem v_z1 : regsA ini u sl x .z1 =
    BitVec.ofInt (aLay m).w (2 * (uP ini u x : ℤ) - 2 ^ (m + 1)) := by
  have hd := regsA_dst ini u sl x ⟨.z1, rA .ax1, cB (2 ^ (m + 1)), .const true⟩
    (by simp [addrOps, opsA3])
  change regsA ini u sl x .z1 = ROp.val ⟨.z1, rA .ax1, cB (2 ^ (m + 1)), .const true⟩
    (cfgOf x (regsA ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ (2 * (uP ini u x : ℤ)) ((2 ^ (m + 1) : ℕ) : ℤ)
    (by rw [readBV_rA, v_ax1]) (ofBits_cB x _ _)]
  simp only [BSrc.val, if_true]
  push_cast
  ring_nf

theorem sum_dgA (F : RO (aLay m) → BitVec (aLay m).w) :
    (∑ j ∈ Finset.range m, if (dgA sl j).val (cfgOf x F) then (2 ^ j : ℤ) else 0) =
      (rS sl x : ℤ) := by
  rw [Finset.sum_range]
  unfold rS wordValue
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  simp only [dgA, j.isLt, dif_pos, BSrc.val, cfg_inl, beq_true]
  rcases Bool.eq_false_or_eq_true (x (sl j)) with h | h <;> simp [h, bitValue]

theorem v_acc : regsA ini u sl x (accA (Fin.last m)) =
    BitVec.ofInt (aLay m).w (2 * (rS sl x : ℤ) * (2 * (uP ini u x : ℤ) - 2 ^ (m + 1))) := by
  have h := chain_last x (regsA ini u sl x) accA .z1 (dgA sl)
    (2 * (uP ini u x : ℤ) - 2 ^ (m + 1)) (v_z1 ini u sl x)
    (fun o ho => regsA_dst ini u sl x o (by
      simp only [addrOps, List.mem_append]
      exact Or.inl (Or.inr ho)))
  rw [h, sum_dgA]

theorem v_md : regsA ini u sl x .md = BitVec.ofInt (aLay m).w (4 * (gA ini u sl x : ℤ)) := by
  have hd := regsA_dst ini u sl x opMd (by simp [addrOps])
  change regsA ini u sl x .md = ROp.val ⟨.md, shA .ax1 (m + 1), rB (accA (Fin.last m)),
    .const true⟩ (cfgOf x (regsA ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ (2 * (uP ini u x : ℤ) * 2 ^ (m + 1))
    (2 * (rS sl x : ℤ) * (2 * (uP ini u x : ℤ) - 2 ^ (m + 1)))
    (by rw [readBV_shA, v_ax1, GateBinaryODE.ofInt_mul'])
    (by rw [ofBits_rB, v_acc])]
  simp only [BSrc.val, if_true]
  congr 1
  have hu := uP_lt ini u x
  unfold gA
  push_cast [Nat.cast_sub hu.le]
  ring

end Values

/-! ### The address word and the duration word -/

section Words

variable {B : Type} {m : ℕ} (ini : B) (u sl : Fin m → B) (x : B → Bool)

/-- **The address bits**: bit `j + 2` of `md` is bit `j` of the address. -/
theorem md_bit (j : ℕ) (hj : j < 2 * m) :
    (regsA ini u sl x .md).getLsbD (j + 2) = (gA ini u sl x).testBit j := by
  rw [v_md]
  have hcast : (4 * (gA ini u sl x : ℤ)) = ((4 * gA ini u sl x : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat]
  have hw : j + 2 < (aLay m).w := by rw [aLay_w]; omega
  simp only [hw, decide_true, Bool.true_and]
  rw [show 4 * gA ini u sl x = gA ini u sl x * 2 ^ 2 by ring, Nat.testBit_mul_two_pow]
  simp

/-- **The address word**: the bits `2, …, 2m + 1` of `md` form the address `g`. -/
theorem md_word :
    wordValue (fun j : Fin (2 * m) => (regsA ini u sl x .md).getLsbD (j.val + 2)) =
      gA ini u sl x := by
  rw [← wordValue_testBit (gA ini u sl x) (gA_lt ini u sl x)]
  exact wordValue_congr _ _ (fun j => md_bit ini u sl x j.val j.isLt)

/-- The sign bit of `n1 = -2 u'` is `u' > 0`. -/
theorem n1_msb :
    (regsA ini u sl x .n1).getLsbD ((aLay m).w - 1) = decide (0 < uP ini u x) := by
  have hu := uP_lt ini u x
  have hb : |(-(2 * (uP ini u x : ℤ)))| < 2 ^ ((aLay m).w - 1) := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have h1 : ((uP ini u x : ℕ) : ℤ) < 2 ^ m := by exact_mod_cast hu
    have h2 : (2 : ℤ) * 2 ^ m ≤ 2 ^ ((aLay m).w - 1) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by rw [aLay_w]; omega)
    linarith
  rw [v_n1, GateBinaryODE.msb_ofInt _ (by rw [aLay_w]; omega) hb]
  simp only [decide_eq_decide]
  constructor
  · intro h
    have : (0 : ℤ) < uP ini u x := by linarith
    exact_mod_cast this
  · intro h
    have : (0 : ℤ) < uP ini u x := by exact_mod_cast h
    linarith

/-- The bits `1, …, m` of `n1 = -2 u'` are the bits of `2^m - u'` when `u' > 0`. -/
theorem n1_bit (h0 : 0 < uP ini u x) (j : ℕ) (hj : j < m) :
    (regsA ini u sl x .n1).getLsbD (j + 1) = (2 ^ m - uP ini u x).testBit j := by
  have hu := uP_lt ini u x
  set w := (aLay m).w with hw
  have hwm : m + 14 ≤ w := by rw [hw, aLay_w]; omega
  set U := uP ini u x with hU
  -- the two's complement word of `-2u'` is `2^w - 2u'`
  have h2w : 2 * U < 2 ^ w := by
    have : 2 ^ (m + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this
    omega
  have hnat : (BitVec.ofInt w (-(2 * (U : ℤ)))).toNat = 2 ^ w - 2 * U := by
    rw [BitVec.toNat_ofInt]
    have hmod : (-(2 * (U : ℤ))) % (2 ^ w : ℕ) = ((2 ^ w - 2 * U : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2w.le]
      rw [show (-(2 * (U : ℤ))) = (2 ^ w - 2 * (U : ℤ)) + (-1) * 2 ^ w by ring,
        Int.add_mul_emod_self_right]
      apply Int.emod_eq_of_lt
      · have : (2 * (U : ℤ)) < 2 ^ w := by exact_mod_cast h2w
        linarith
      · have : (0 : ℤ) < 2 * (U : ℤ) := by
          have : (0 : ℤ) < U := by exact_mod_cast h0
          linarith
        linarith
    rw [hmod, Int.toNat_natCast]
  rw [v_n1, ← BitVec.testBit_toNat, hnat, Nat.testBit_succ]
  -- `(2^w - 2u')/2 = 2^(w-1) - u'`, congruent to `2^m - u'` modulo `2^m`
  have hdiv : (2 ^ w - 2 * U) / 2 = 2 ^ (w - 1) - U := by
    have e : 2 ^ w = 2 * 2 ^ (w - 1) := by
      rw [← pow_succ']
      congr 1
    rw [e, ← Nat.mul_sub, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hdiv]
  have hsplit : 2 ^ (w - 1) - U = (2 ^ m - U) + 2 ^ m * (2 ^ (w - 1 - m) - 1) := by
    have e : 2 ^ (w - 1) = 2 ^ m * 2 ^ (w - 1 - m) := by
      rw [← pow_add]
      congr 1
      omega
    have hK : 1 ≤ 2 ^ (w - 1 - m) := Nat.one_le_two_pow
    rw [e, Nat.mul_sub, mul_one]
    have : 2 ^ m ≤ 2 ^ m * 2 ^ (w - 1 - m) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have key : (2 ^ m - U + 2 ^ m * (2 ^ (w - 1 - m) - 1)).testBit j =
      ((2 ^ m - U + 2 ^ m * (2 ^ (w - 1 - m) - 1)) % 2 ^ m).testBit j := by
    rw [Nat.testBit_mod_two_pow]
    simp [hj]
  rw [hsplit, key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **The duration word**: when `u' > 0`, the bits `1, …, m` of `n1` form `2^m - u'`. -/
theorem n1_word (h0 : 0 < uP ini u x) :
    wordValue (fun j : Fin m => (regsA ini u sl x .n1).getLsbD (j.val + 1)) =
      2 ^ m - uP ini u x := by
  rw [← wordValue_testBit (r := m) (2 ^ m - uP ini u x) (by have := uP_lt ini u x; omega)]
  exact wordValue_congr _ _ (fun j => n1_bit ini u sl x h0 j.val j.isLt)

/-- **The duration factor** read from `n1` by the angle arithmetic:
`(msb ? word : 2^m) = 2^m - u'`. -/
theorem n1_dv :
    (if (regsA ini u sl x .n1).getLsbD ((aLay m).w - 1) then
      (wordValue (fun j : Fin m => (regsA ini u sl x .n1).getLsbD (j.val + 1)) : ℤ)
      else 2 ^ m) = 2 ^ m - (uP ini u x : ℤ) := by
  rw [n1_msb]
  by_cases h0 : 0 < uP ini u x
  · simp only [h0, decide_true, if_true]
    rw [n1_word ini u sl x h0]
    have := uP_lt ini u x
    push_cast [Nat.cast_sub this.le]
    ring
  · have : uP ini u x = 0 := by omega
    simp [this]

end Words

/-! ### Counts -/

section Counts

variable {B : Type} [DecidableEq B] {m : ℕ}

/-- The gates of the address program. -/
def addrG (ini : B) (u sl : Fin m → B) : List (CGate (PW B (aLay m))) := progG (addrOps ini u sl)

theorem w_posA : 0 < (aLay m).w := by rw [aLay_w]; omega

omit [DecidableEq B] in
/-- **The address program has at most `13 (2m + 14) (m + 5)` gates.** -/
theorem length_addrG (ini : B) (u sl : Fin m → B) :
    (addrG ini u sl).length ≤ 13 * (2 * m + 14) * (m + 5) := by
  have h := length_progG (addrOps ini u sl) w_posA
  rw [length_addrOps] at h
  calc (addrG ini u sl).length ≤ 13 * (aLay m).w * (m + 5) := h
    _ = 13 * (2 * m + 14) * (m + 5) := by rw [aLay_w]

omit [DecidableEq B] in
theorem addrG_proper (ini : B) (u sl : Fin m → B) : ∀ g ∈ addrG ini u sl, g.Proper := by
  intro g hg
  simp only [addrG, progG, List.mem_flatMap] at hg
  obtain ⟨o, ho, hg⟩ := hg
  exact ROp.proper_gates o _ ((addrOK ini u sl).ok o ho) w_posA g hg

omit [DecidableEq B] in
theorem addrG_cs (ini : B) (u sl : Fin m → B) : ∀ g ∈ addrG ini u sl, g.cs.length ≤ 2 := by
  intro g hg
  simp only [addrG, progG, List.mem_flatMap] at hg
  obtain ⟨o, _, hg⟩ := hg
  exact ROp.cs_gates o g hg

/-- **The address program writes its register file** on clean work wires. -/
theorem crun_addrG (ini : B) (u sl : Fin m → B) (x : B → Bool) :
    crun (addrG ini u sl) (cfgOf x 0) = cfgOf x (regsA ini u sl x) :=
  crun_progG (lvO (aLay m)) _ (addrOK ini u sl) w_posA x 0 (fun _ _ => rfl)

end Counts

end SparseHamiltonian.GateBinarySelect
