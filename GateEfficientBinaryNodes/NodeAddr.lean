import GateEfficientBinarySelect.Address

/-!
# The address program for computed source nodes

For a source node `v = ν T / 2^μ` given by a `μ`-bit node word `ν` (computed coherently from
the node label by a node program, `NodeProg` of module `NodeNative`) and `M = 2^m` slots per
branch, the sample address of slot
`r` of the branch of the source label `(ini, ·)` is

`v' + r (T - v') / 2^m = T (2^m ν' + r (2^μ - ν')) / 2^(μ+m)`,   `ν' = (ini ? ν : 0)`,

an integer address `A = 2^m ν' + r (2^μ - ν') < 2^(μ+m)` on the uniform grid of `2^(μ+m)`
points ("computed by multiplication and addition", Lemma `ode:lem:gate-select`, proof); the
branch scale `(T - v')/T` is `dv / 2^μ` with the duration word `dv = 2^μ - ν'`. This generalises
`GateBinarySelect.addrOps` (the dyadic nodes `u T/2^m`, `μ = m`) to node words of any length.

The program is a single-assignment register program of `GateEfficientBinary` on the registers
`GateBinaryODE.RO (aLayN m μ)` of width `μ + m + 14` (`μ` stored bits, `m` chain digits):

* `ax1 := ν ± ν` (`+` exactly when `ini` is set): `2 ν'`;
* `n1 := 0 - ax1`: `-2 ν'`, whose sign bit is `ν' > 0` and whose bits `1, …, μ` are the word
  `2^μ - ν'` when `ν' > 0` (`n1N_msb`, `n1N_word`): the duration word read by the arithmetic;
* `z1 := ax1 - 2^(μ+1)`: `-2 dv`;
* the multiplication chain with the slot digits: `2 r (-2 dv)`;
* `md := (ax1 << (m+1)) - chain`: `4 A`, whose bits `2, …, μ + m + 1` are the address word
  (`mdN_word`).

`addrOKN`: single assignment; `vN_md`, `n1N_dv`: the register values; `length_addrGN`: at most
`13 (μ + m + 14)(m + 5)` gates.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryNodes

open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinarySelect (wordValue_testBit wordValue_congr)
open GatePointerEncoding (wordValue bitValue)

/-- The layout of the address registers for `μ`-bit node words and `m` slot digits: width
`μ + m + 14`, chain registers `hc 0, …, hc (m+1)`. -/
def aLayN (m mu : ℕ) : Lay := ⟨mu, 0, 0, 0, 0, m, 0⟩

theorem aLayN_w (m mu : ℕ) : (aLayN m mu).w = mu + m + 14 := by
  simp only [aLayN, Lay.w]
  ring

theorem aLayN_F (m mu : ℕ) : (aLayN m mu).F = m := rfl

section Ops

variable {B : Type} {m mu : ℕ}

/-- An unsigned input word as the second operand of a register operation. -/
def uBaN (r : Fin mu → B) : ℕ → BSrc (PW B (aLayN m mu)) := fun i => .lit (uA r i) true

/-- The slot digits of the multiplication chain. -/
def dgN (sl : Fin m → B) : ℕ → BSrc (PW B (aLayN m mu)) :=
  fun j => if h : j < m then .lit (.inl (sl ⟨j, h⟩)) true else .const false

/-- The registers of the multiplication chain. -/
def accN (j : Fin (m + 1)) : RO (aLayN m mu) := .hc ⟨j.val, by rw [aLayN_F]; omega⟩

theorem lvO_accN (j : Fin (m + 1)) : lvO (aLayN m mu) (accN j) = 25 + j.val := rfl

/-- The first three operations: `ax1 := ν ± ν`, `n1 := 0 - ax1`, `z1 := ax1 - 2^(μ+1)`. -/
def opsN3 (ini : B) (u : Fin mu → B) : List (ROp B (RO (aLayN m mu)) (aLayN m mu).w) :=
  [⟨.ax1, uA u, uBaN u, .lit (.inl ini) false⟩,
   ⟨.n1, zA, rB .ax1, .const true⟩,
   ⟨.z1, rA .ax1, cB (2 ^ (mu + 1)), .const true⟩]

/-- The chain `2 r z1` with the slot digits. -/
def chainN (sl : Fin m → B) : List (ROp B (RO (aLayN m mu)) (aLayN m mu).w) :=
  chain (m := m) accN .z1 (dgN sl)

/-- The last operation: `md := (ax1 << (m+1)) - acc_m`. -/
def opMdN : ROp B (RO (aLayN m mu)) (aLayN m mu).w :=
  ⟨.md, shA .ax1 (m + 1), rB (accN (Fin.last m)), .const true⟩

/-- **The address program for computed nodes.** -/
def addrOpsN (ini : B) (u : Fin mu → B) (sl : Fin m → B) :
    List (ROp B (RO (aLayN m mu)) (aLayN m mu).w) :=
  opsN3 ini u ++ chainN sl ++ [opMdN]

theorem length_addrOpsN (ini : B) (u : Fin mu → B) (sl : Fin m → B) :
    (addrOpsN ini u sl).length = m + 5 := by
  simp only [addrOpsN, opsN3, chainN, chain, opMdN, List.length_append, List.length_cons,
    List.length_map, List.length_finRange, List.length_nil]
  ring

end Ops

/-! ### Single assignment -/

section OK

variable {B : Type} {m mu : ℕ}

theorem opsN3_ok (ini : B) (u : Fin mu → B) :
    (opsN3 (m := m) ini u).Pairwise
        (fun o o' => lvO (aLayN m mu) o.dst < lvO (aLayN m mu) o'.dst) ∧
      ∀ o ∈ opsN3 (m := m) ini u, o.OK (fun r => lvO (aLayN m mu) r < lvO (aLayN m mu) o.dst) ∧
        lvO (aLayN m mu) o.dst ≤ 2 := by
  refine ⟨?_, ?_⟩
  · simp only [opsN3, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, IsEmpty.forall_iff, implies_true, and_true,
      lvO]
    omega
  · intro o ho
    simp only [opsN3, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · exact ⟨⟨by simp [lvO], fun i _ => readable_uA _ u i, fun i _ => readable_uA _ u i,
        trivial⟩, by simp [lvO]⟩
    · exact ⟨⟨by simp [lvO], fun i _ => readable_zA _ i, fun i _ => on_rB (by simp [lvO]) i,
        trivial⟩, by simp [lvO]⟩
    · exact ⟨⟨by simp [lvO], fun i _ => readable_rA (by simp [lvO]) i, fun i _ => on_cB _ _ i,
        trivial⟩, by simp [lvO]⟩

theorem chainN_ok (sl : Fin m → B) :
    (chainN (mu := mu) sl).Pairwise
        (fun o o' => lvO (aLayN m mu) o.dst < lvO (aLayN m mu) o'.dst) ∧
      ∀ o ∈ chainN (mu := mu) sl,
        o.OK (fun r => lvO (aLayN m mu) r < lvO (aLayN m mu) o.dst) ∧
          25 ≤ lvO (aLayN m mu) o.dst ∧ lvO (aLayN m mu) o.dst ≤ 25 + m := by
  refine chain_ok _ _ _ 25 lvO_accN (by simp [lvO]) (fun j hj => ?_)
  simp only [dgN, hj, dif_pos]
  trivial

theorem opMdN_ok :
    (opMdN : ROp B (RO (aLayN m mu)) (aLayN m mu).w).OK
        (fun r => lvO (aLayN m mu) r <
          lvO (aLayN m mu) (opMdN : ROp B (RO (aLayN m mu)) (aLayN m mu).w).dst) ∧
      lvO (aLayN m mu) (opMdN : ROp B (RO (aLayN m mu)) (aLayN m mu).w).dst = m + 27 := by
  refine ⟨⟨by simp [opMdN, lvO], fun i _ => readable_shA (by simp [opMdN, lvO]) _ i,
    fun i _ => on_rB (by
      simp only [opMdN, lvO_accN, Fin.val_last]
      simp only [lvO, aLayN_F]
      omega) i,
    trivial⟩, ?_⟩
  simp [opMdN, lvO, aLayN_F]

/-- **The address program for computed nodes is a single-assignment program.** -/
theorem addrOKN (ini : B) (u : Fin mu → B) (sl : Fin m → B) :
    ProgOK (lvO (aLayN m mu)) (addrOpsN ini u sl) := by
  obtain ⟨hA1, hA2⟩ := opsN3_ok (m := m) ini u
  obtain ⟨hC1, hC2⟩ := chainN_ok (mu := mu) sl
  obtain ⟨hM1, hM2⟩ := opMdN_ok (B := B) (m := m) (mu := mu)
  refine ⟨?_, ?_⟩
  · simp only [addrOpsN, List.pairwise_append, List.pairwise_singleton, List.mem_singleton,
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
    simp only [addrOpsN, List.mem_append, List.mem_singleton] at ho
    rcases ho with (ho | ho) | rfl
    · exact (hA2 o ho).1
    · exact (hC2 o ho).1
    · exact hM1

end OK

/-! ### Register values -/

section Values

variable {B : Type} {m mu : ℕ} (ini : B) (u : Fin mu → B) (sl : Fin m → B) (x : B → Bool)

/-- The register file of the address program on the input configuration `x`. -/
def regsN : RO (aLayN m mu) → BitVec (aLayN m mu).w := runOps x (addrOpsN ini u sl) 0

theorem regsN_dst :
    ∀ o ∈ addrOpsN ini u sl, regsN ini u sl x o.dst = o.val (cfgOf x (regsN ini u sl x)) :=
  runOps_dst (lvO (aLayN m mu)) _ (addrOKN ini u sl) x 0

/-- The start word `ν' = (ini ? ν : 0)`. -/
def nuP : ℕ := if x ini then wordValue (fun j => x (u j)) else 0

/-- The slot word `r`. -/
def rSN : ℕ := wordValue (fun j => x (sl j))

/-- **The address** `A = 2^m ν' + r (2^μ - ν')`. -/
def gAN : ℕ := 2 ^ m * nuP ini u x + rSN sl x * (2 ^ mu - nuP ini u x)

theorem nuP_lt : nuP ini u x < 2 ^ mu := by
  unfold nuP
  split_ifs
  · exact GatePointerEncoding.wordValue_lt_pow _
  · exact Nat.pos_of_ne_zero (by positivity)

theorem rSN_lt : rSN sl x < 2 ^ m := GatePointerEncoding.wordValue_lt_pow _

/-- `2^m a + r (2^μ - a) < 2^(μ+m)` for `a < 2^μ`, `r < 2^m`. -/
theorem addr_lt (a r : ℕ) (ha : a < 2 ^ mu) (hr : r < 2 ^ m) :
    2 ^ m * a + r * (2 ^ mu - a) < 2 ^ (mu + m) := by
  have hle : r * (2 ^ mu - a) ≤ (2 ^ m - 1) * (2 ^ mu - a) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : 2 ^ (mu + m) = 2 ^ m * 2 ^ mu := by rw [pow_add, mul_comm]
  rw [h2]
  have e1 : (2 ^ m - 1) * (2 ^ mu - a) = 2 ^ m * (2 ^ mu - a) - (2 ^ mu - a) := by
    rw [Nat.sub_mul, one_mul]
  have e2 : 2 ^ m * (2 ^ mu - a) + 2 ^ m * a = 2 ^ m * 2 ^ mu := by
    rw [← Nat.mul_add, Nat.sub_add_cancel ha.le]
  have e3 : (2 ^ mu - a) ≤ 2 ^ m * (2 ^ mu - a) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have h4 : 0 < 2 ^ mu - a := by omega
  have h5 : 2 ^ mu - a ≤ 2 ^ m * 2 ^ mu :=
    le_trans (Nat.sub_le _ _) (Nat.le_mul_of_pos_left _ (by positivity))
  omega

theorem gAN_lt : gAN ini u sl x < 2 ^ (mu + m) :=
  addr_lt _ _ (nuP_lt ini u x) (rSN_lt sl x)

theorem mu_le_wN : mu ≤ (aLayN m mu).w := by
  rw [aLayN_w]
  omega

theorem ofBits_uBaN (r : Fin mu → B) (y : PW B (aLayN m mu) → Bool) :
    ofBits (fun i => (uBaN (m := m) r i).val y) (aLayN m mu).w =
      readBV (uA r) (aLayN m mu).w y := by
  apply ofBits_congr
  intro i _
  simp [uBaN, BSrc.val]

theorem vN_ax1 : regsN ini u sl x .ax1 = BitVec.ofInt (aLayN m mu).w (2 * (nuP ini u x : ℤ)) := by
  have hd := regsN_dst ini u sl x ⟨.ax1, uA u, uBaN u, .lit (.inl ini) false⟩
    (by simp [addrOpsN, opsN3])
  change regsN ini u sl x .ax1 = ROp.val ⟨.ax1, uA u, uBaN u, .lit (.inl ini) false⟩
    (cfgOf x (regsN ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_uA x _ u mu_le_wN)
    (by rw [ofBits_uBaN, readBV_uA x _ u mu_le_wN])]
  congr 1
  unfold nuP
  rcases Bool.eq_false_or_eq_true (x ini) with h | h <;> simp [BSrc.val, cfg_inl, h]
  ring

theorem vN_n1 : regsN ini u sl x .n1 =
    BitVec.ofInt (aLayN m mu).w (-(2 * (nuP ini u x : ℤ))) := by
  have hd := regsN_dst ini u sl x ⟨.n1, zA, rB .ax1, .const true⟩ (by simp [addrOpsN, opsN3])
  change regsN ini u sl x .n1 = ROp.val ⟨.n1, zA, rB .ax1, .const true⟩
    (cfgOf x (regsN ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (2 * (nuP ini u x : ℤ)) (readBV_zA x _)
    (by rw [ofBits_rB, vN_ax1])]
  simp [BSrc.val]

theorem vN_z1 : regsN ini u sl x .z1 =
    BitVec.ofInt (aLayN m mu).w (2 * (nuP ini u x : ℤ) - 2 ^ (mu + 1)) := by
  have hd := regsN_dst ini u sl x ⟨.z1, rA .ax1, cB (2 ^ (mu + 1)), .const true⟩
    (by simp [addrOpsN, opsN3])
  change regsN ini u sl x .z1 = ROp.val ⟨.z1, rA .ax1, cB (2 ^ (mu + 1)), .const true⟩
    (cfgOf x (regsN ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ (2 * (nuP ini u x : ℤ)) ((2 ^ (mu + 1) : ℕ) : ℤ)
    (by rw [readBV_rA, vN_ax1]) (ofBits_cB x _ _)]
  simp only [BSrc.val, if_true]
  push_cast
  ring_nf

theorem sum_dgN (F : RO (aLayN m mu) → BitVec (aLayN m mu).w) :
    (∑ j ∈ Finset.range m, if (dgN (mu := mu) sl j).val (cfgOf x F) then (2 ^ j : ℤ) else 0) =
      (rSN sl x : ℤ) := by
  rw [Finset.sum_range]
  unfold rSN wordValue
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  simp only [dgN, j.isLt, dif_pos, BSrc.val, cfg_inl, beq_true]
  rcases Bool.eq_false_or_eq_true (x (sl j)) with h | h <;> simp [h, bitValue]

theorem vN_acc : regsN ini u sl x (accN (Fin.last m)) =
    BitVec.ofInt (aLayN m mu).w
      (2 * (rSN sl x : ℤ) * (2 * (nuP ini u x : ℤ) - 2 ^ (mu + 1))) := by
  have h := chain_last x (regsN ini u sl x) accN .z1 (dgN sl)
    (2 * (nuP ini u x : ℤ) - 2 ^ (mu + 1)) (vN_z1 ini u sl x)
    (fun o ho => regsN_dst ini u sl x o (by
      simp only [addrOpsN, List.mem_append]
      exact Or.inl (Or.inr ho)))
  rw [h, sum_dgN]

theorem vN_md : regsN ini u sl x .md =
    BitVec.ofInt (aLayN m mu).w (4 * (gAN ini u sl x : ℤ)) := by
  have hd := regsN_dst ini u sl x opMdN (by simp [addrOpsN])
  change regsN ini u sl x .md = ROp.val ⟨.md, shA .ax1 (m + 1), rB (accN (Fin.last m)),
    .const true⟩ (cfgOf x (regsN ini u sl x)) at hd
  rw [hd, val_mk _ _ _ _ _ (2 * (nuP ini u x : ℤ) * 2 ^ (m + 1))
    (2 * (rSN sl x : ℤ) * (2 * (nuP ini u x : ℤ) - 2 ^ (mu + 1)))
    (by rw [readBV_shA, vN_ax1, GateBinaryODE.ofInt_mul'])
    (by rw [ofBits_rB, vN_acc])]
  simp only [BSrc.val, if_true]
  congr 1
  have hu := nuP_lt ini u x
  unfold gAN
  push_cast [Nat.cast_sub hu.le]
  ring

end Values

/-! ### The address word and the duration word -/

section Words

variable {B : Type} {m mu : ℕ} (ini : B) (u : Fin mu → B) (sl : Fin m → B) (x : B → Bool)

/-- **The address bits**: bit `j + 2` of `md` is bit `j` of the address. -/
theorem mdN_bit (j : ℕ) (hj : j < mu + m) :
    (regsN ini u sl x .md).getLsbD (j + 2) = (gAN ini u sl x).testBit j := by
  rw [vN_md]
  have hcast : (4 * (gAN ini u sl x : ℤ)) = ((4 * gAN ini u sl x : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat]
  have hw : j + 2 < (aLayN m mu).w := by rw [aLayN_w]; omega
  simp only [hw, decide_true, Bool.true_and]
  rw [show 4 * gAN ini u sl x = gAN ini u sl x * 2 ^ 2 by ring, Nat.testBit_mul_two_pow]
  simp

/-- **The address word**: the bits `2, …, μ + m + 1` of `md` form the address `A`. -/
theorem mdN_word :
    wordValue (fun j : Fin (mu + m) => (regsN ini u sl x .md).getLsbD (j.val + 2)) =
      gAN ini u sl x := by
  rw [← wordValue_testBit (gAN ini u sl x) (gAN_lt ini u sl x)]
  exact wordValue_congr _ _ (fun j => mdN_bit ini u sl x j.val j.isLt)

/-- The sign bit of `n1 = -2 ν'` is `ν' > 0`. -/
theorem n1N_msb :
    (regsN ini u sl x .n1).getLsbD ((aLayN m mu).w - 1) = decide (0 < nuP ini u x) := by
  have hu := nuP_lt ini u x
  have hb : |(-(2 * (nuP ini u x : ℤ)))| < 2 ^ ((aLayN m mu).w - 1) := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have h1 : ((nuP ini u x : ℕ) : ℤ) < 2 ^ mu := by exact_mod_cast hu
    have h2 : (2 : ℤ) * 2 ^ mu ≤ 2 ^ ((aLayN m mu).w - 1) := by
      rw [← pow_succ']
      exact pow_le_pow_right₀ (by norm_num) (by rw [aLayN_w]; omega)
    linarith
  rw [vN_n1, GateBinaryODE.msb_ofInt _ (by rw [aLayN_w]; omega) hb]
  simp only [decide_eq_decide]
  constructor
  · intro h
    have : (0 : ℤ) < nuP ini u x := by linarith
    exact_mod_cast this
  · intro h
    have : (0 : ℤ) < nuP ini u x := by exact_mod_cast h
    linarith

/-- The bits `1, …, μ` of `n1 = -2 ν'` are the bits of `2^μ - ν'` when `ν' > 0`. -/
theorem n1N_bit (h0 : 0 < nuP ini u x) (j : ℕ) (hj : j < mu) :
    (regsN ini u sl x .n1).getLsbD (j + 1) = (2 ^ mu - nuP ini u x).testBit j := by
  have hu := nuP_lt ini u x
  set w := (aLayN m mu).w with hw
  have hwm : mu + 14 ≤ w := by rw [hw, aLayN_w]; omega
  set U := nuP ini u x with hU
  have h2w : 2 * U < 2 ^ w := by
    have : 2 ^ (mu + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
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
  rw [vN_n1, ← BitVec.testBit_toNat, hnat, Nat.testBit_succ]
  have hdiv : (2 ^ w - 2 * U) / 2 = 2 ^ (w - 1) - U := by
    have e : 2 ^ w = 2 * 2 ^ (w - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ w)]
    rw [e, ← Nat.mul_sub, Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hdiv]
  have hsplit : 2 ^ (w - 1) - U = (2 ^ mu - U) + 2 ^ mu * (2 ^ (w - 1 - mu) - 1) := by
    have e : 2 ^ (w - 1) = 2 ^ mu * 2 ^ (w - 1 - mu) := by
      rw [← pow_add]
      congr 1
      omega
    have hK : 1 ≤ 2 ^ (w - 1 - mu) := Nat.one_le_two_pow
    rw [e, Nat.mul_sub, mul_one]
    have : 2 ^ mu ≤ 2 ^ mu * 2 ^ (w - 1 - mu) := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have key : (2 ^ mu - U + 2 ^ mu * (2 ^ (w - 1 - mu) - 1)).testBit j =
      ((2 ^ mu - U + 2 ^ mu * (2 ^ (w - 1 - mu) - 1)) % 2 ^ mu).testBit j := by
    rw [Nat.testBit_mod_two_pow]
    simp [hj]
  rw [hsplit, key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **The duration word**: when `ν' > 0`, the bits `1, …, μ` of `n1` form `2^μ - ν'`. -/
theorem n1N_word (h0 : 0 < nuP ini u x) :
    wordValue (fun j : Fin mu => (regsN ini u sl x .n1).getLsbD (j.val + 1)) =
      2 ^ mu - nuP ini u x := by
  rw [← wordValue_testBit (r := mu) (2 ^ mu - nuP ini u x) (by have := nuP_lt ini u x; omega)]
  exact wordValue_congr _ _ (fun j => n1N_bit ini u sl x h0 j.val j.isLt)

/-- **The duration factor** read from `n1` by the angle arithmetic:
`(msb ? word : 2^μ) = 2^μ - ν'`. -/
theorem n1N_dv :
    (if (regsN ini u sl x .n1).getLsbD ((aLayN m mu).w - 1) then
      (wordValue (fun j : Fin mu => (regsN ini u sl x .n1).getLsbD (j.val + 1)) : ℤ)
      else 2 ^ mu) = 2 ^ mu - (nuP ini u x : ℤ) := by
  rw [n1N_msb]
  by_cases h0 : 0 < nuP ini u x
  · simp only [h0, decide_true, if_true]
    rw [n1N_word ini u sl x h0]
    have := nuP_lt ini u x
    push_cast [Nat.cast_sub this.le]
    ring
  · have : nuP ini u x = 0 := by omega
    simp [this]

end Words

/-! ### Counts -/

section Counts

variable {B : Type} [DecidableEq B] {m mu : ℕ}

/-- The gates of the address program. -/
def addrGN (ini : B) (u : Fin mu → B) (sl : Fin m → B) : List (CGate (PW B (aLayN m mu))) :=
  progG (addrOpsN ini u sl)

theorem w_posN : 0 < (aLayN m mu).w := by rw [aLayN_w]; omega

omit [DecidableEq B] in
/-- **The address program has at most `13 (μ + m + 14) (m + 5)` gates.** -/
theorem length_addrGN (ini : B) (u : Fin mu → B) (sl : Fin m → B) :
    (addrGN ini u sl).length ≤ 13 * (mu + m + 14) * (m + 5) := by
  have h := length_progG (addrOpsN ini u sl) w_posN
  rw [length_addrOpsN] at h
  calc (addrGN ini u sl).length ≤ 13 * (aLayN m mu).w * (m + 5) := h
    _ = 13 * (mu + m + 14) * (m + 5) := by rw [aLayN_w]

omit [DecidableEq B] in
theorem addrGN_proper (ini : B) (u : Fin mu → B) (sl : Fin m → B) :
    ∀ g ∈ addrGN ini u sl, g.Proper := by
  intro g hg
  simp only [addrGN, progG, List.mem_flatMap] at hg
  obtain ⟨o, ho, hg⟩ := hg
  exact ROp.proper_gates o _ ((addrOKN ini u sl).ok o ho) w_posN g hg

omit [DecidableEq B] in
theorem addrGN_cs (ini : B) (u : Fin mu → B) (sl : Fin m → B) :
    ∀ g ∈ addrGN ini u sl, g.cs.length ≤ 2 := by
  intro g hg
  simp only [addrGN, progG, List.mem_flatMap] at hg
  obtain ⟨o, _, hg⟩ := hg
  exact ROp.cs_gates o g hg

/-- **The address program writes its register file** on clean work wires. -/
theorem crun_addrGN (ini : B) (u : Fin mu → B) (sl : Fin m → B) (x : B → Bool) :
    crun (addrGN ini u sl) (cfgOf x 0) = cfgOf x (regsN ini u sl x) :=
  crun_progG (lvO (aLayN m mu)) _ (addrOKN ini u sl) w_posN x 0 (fun _ _ => rfl)

end Counts

end SparseHamiltonian.GateBinaryNodes
