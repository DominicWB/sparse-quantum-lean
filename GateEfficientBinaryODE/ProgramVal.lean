import GateEfficientBinaryODE.ProgramSem

/-!
# The registers of the pre-processing program

On every input configuration `x` the final register file `regsO I x` of the program satisfies
the equation of each operation (single assignment). Register by register this gives the integer
held by the register (`v_ax1`, …), and finally (`v_xc`, `v_yc`; `toInt_xc`, `toInt_yc`) the two
output registers hold the integers `zx` and `zy` of `Program` exactly, as two's complement words,
under the layout bounds `Lay.OK`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinaryODE

open SparseHamiltonian.GateBinary
open GatePointerEncoding (wordValue)

/-- The layout bounds: nonempty components, the LCHS grid fits its word, `K < J`, and the rounded
step has at most `F + 1` bits. -/
structure Lay.OK (L : Lay) : Prop where
  b_pos : 0 < L.b
  J_le : L.J ≤ 2 ^ L.lq
  K_lt : L.K < L.J
  Hn_lt : L.Hn < 2 ^ (L.F + 1)

/-! ### Elementary bounds -/

theorem twos_abs_le {B : Type} {b : ℕ} (r : Fin b → B) (x : B → Bool) :
    |twos r x| ≤ 2 ^ (b - 1) := by
  unfold twos
  have h1 := BitVec.toInt_lt (x := ofBits (fun j => if h : j < b then x (r ⟨j, h⟩) else false) b)
  have h2 := BitVec.le_toInt (ofBits (fun j => if h : j < b then x (r ⟨j, h⟩) else false) b)
  rw [abs_le]
  constructor <;> omega

theorem sum_testBit (n m : ℕ) (hn : n < 2 ^ m) :
    (∑ j ∈ Finset.range m, if n.testBit j then (2 ^ j : ℤ) else 0) = n := by
  have h := toNat_eq_sum (BitVec.ofNat m n)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at h
  have h' : (n : ℤ) = ((∑ i ∈ Finset.range m,
      (if (BitVec.ofNat m n).getLsbD i then 2 ^ i else 0) : ℕ) : ℤ) := by
    rw [← h]
  rw [h']
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [BitVec.getLsbD_ofNat]
  simp [hj]

theorem chi_eq (X Y : ℤ) : chi X Y = if X = 0 ∧ Y = 0 then 0 else 1 := rfl

theorem chi_mem (X Y : ℤ) : chi X Y = 0 ∨ chi X Y = 1 := by
  unfold chi
  split_ifs <;> simp

namespace Inp

variable {B : Type} {L : Lay} (I : Inp B L) (x : B → Bool)

theorem ct_nonneg : 0 ≤ I.ct x := by
  unfold ct
  rcases chi_mem (I.X1 x) (I.Y1 x) with h1 | h1 <;>
    rcases chi_mem (I.X2 x) (I.Y2 x) with h2 | h2 <;>
    rw [h1, h2] <;> norm_num

theorem ct_le : I.ct x ≤ 2 := by
  unfold ct
  rcases chi_mem (I.X1 x) (I.Y1 x) with h1 | h1 <;>
    rcases chi_mem (I.X2 x) (I.Y2 x) with h2 | h2 <;>
    rw [h1, h2] <;> norm_num

theorem dv_nonneg : 0 ≤ I.dv x := by
  unfold dv
  split_ifs <;> positivity

theorem dv_le : I.dv x ≤ 2 ^ L.kq := by
  unfold dv
  split_ifs
  · have := GatePointerEncoding.wordValue_lt_pow (fun j => x (I.u j))
    unfold U
    exact_mod_cast this.le
  · exact le_rfl

theorem nv_abs_le (hL : L.OK) : |I.nv x| ≤ 2 ^ L.lq := by
  unfold nv
  split_ifs with h
  · have hJ := hL.J_le
    have hK := hL.K_lt
    rw [abs_le]
    constructor
    · have : (L.K : ℤ) ≤ 2 ^ L.lq := by exact_mod_cast (hK.le.trans hJ)
      omega
    · have : ((I.V x : ℕ) : ℤ) < 2 ^ L.lq := by
        have := GatePointerEncoding.wordValue_lt_pow (fun j => x (I.wd j))
        exact_mod_cast this
      omega
  · simp

theorem mu_abs_le (hL : L.OK) : |I.mu x| ≤ 2 ^ (L.F + L.lq + 1) := by
  unfold mu
  split_ifs
  · rw [abs_mul, Nat.abs_cast]
    have h1 := I.nv_abs_le x hL
    have h2 : (L.Hn : ℤ) ≤ 2 ^ (L.F + 1) := by exact_mod_cast hL.Hn_lt.le
    calc |I.nv x| * (L.Hn : ℤ) ≤ 2 ^ L.lq * 2 ^ (L.F + 1) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 ^ (L.F + L.lq + 1) := by rw [← pow_add]; ring_nf
  · rw [abs_of_pos (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem ax_abs_le (hL : L.OK) : |I.ax x| ≤ 2 ^ L.b := by
  have hb := hL.b_pos
  unfold ax
  have h1 := twos_abs_le I.x1 x
  have h2 := twos_abs_le I.x2 x
  have h3 := twos_abs_le I.y1 x
  have h4 := twos_abs_le I.y2 x
  have hp : (2 : ℤ) ^ (L.b - 1) + 2 ^ (L.b - 1) ≤ 2 ^ L.b := by
    rw [← two_mul, ← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  split_ifs
  · exact (abs_add_le _ _).trans (by unfold X1 X2; linarith)
  · exact (abs_add_le _ _).trans (by unfold Y1 Y2; linarith)

theorem ay_abs_le (hL : L.OK) : |I.ay x| ≤ 2 ^ L.b := by
  have hb := hL.b_pos
  unfold ay
  have h1 := twos_abs_le I.x1 x
  have h2 := twos_abs_le I.x2 x
  have h3 := twos_abs_le I.y1 x
  have h4 := twos_abs_le I.y2 x
  have hp : (2 : ℤ) ^ (L.b - 1) + 2 ^ (L.b - 1) ≤ 2 ^ L.b := by
    rw [← two_mul, ← pow_succ']
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  rw [abs_mul]
  have hs : |(if x I.tg then (-1 : ℤ) else 1)| = 1 := by split_ifs <;> simp
  rw [hs, mul_one]
  split_ifs
  · exact (abs_sub _ _).trans (by unfold Y1 Y2; linarith)
  · exact (abs_sub _ _).trans (by unfold X1 X2; linarith)

/-- The output integers fit the registers. -/
theorem zx_abs_lt (hL : L.OK) : |I.zx x| < 2 ^ (L.w - 1) := by
  unfold zx
  have h1 := I.ct_nonneg x
  have h2 := I.ct_le x
  have h3 := I.dv_nonneg x
  have h4 := I.dv_le x
  have h5 := I.mu_abs_le x hL
  have h6 := I.ax_abs_le x hL
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
  calc |(256 : ℤ)| * (I.ct x * (I.dv x * (|I.mu x| * |I.ax x|)))
      ≤ 256 * (2 * (2 ^ L.kq * (2 ^ (L.F + L.lq + 1) * 2 ^ L.b))) := by
        norm_num
        apply mul_le_mul h2 _ (by positivity) (by norm_num)
        apply mul_le_mul h4 _ (by positivity) (by positivity)
        exact mul_le_mul h5 h6 (abs_nonneg _) (by positivity)
    _ < 2 ^ (L.w - 1) := by
        rw [show L.w - 1 = (L.b + L.kq + L.F + L.lq + 13) by unfold Lay.w; omega]
        have : (256 : ℤ) * (2 * (2 ^ L.kq * (2 ^ (L.F + L.lq + 1) * 2 ^ L.b))) =
            2 ^ (L.b + L.kq + L.F + L.lq + 10) := by
          rw [show L.b + L.kq + L.F + L.lq + 10 = L.kq + (L.F + L.lq + 1) + L.b + 9 by omega]
          simp only [pow_add]
          norm_num
          ring
        rw [this]
        exact pow_lt_pow_right₀ (by norm_num) (by omega)

theorem zy_abs_lt (hL : L.OK) : |I.zy x| < 2 ^ (L.w - 1) := by
  unfold zy
  have h1 := I.ct_nonneg x
  have h2 := I.ct_le x
  have h3 := I.dv_nonneg x
  have h4 := I.dv_le x
  have h5 := I.mu_abs_le x hL
  have h6 := I.ay_abs_le x hL
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
  calc |(256 : ℤ)| * (I.ct x * (I.dv x * (|I.mu x| * |I.ay x|)))
      ≤ 256 * (2 * (2 ^ L.kq * (2 ^ (L.F + L.lq + 1) * 2 ^ L.b))) := by
        norm_num
        apply mul_le_mul h2 _ (by positivity) (by norm_num)
        apply mul_le_mul h4 _ (by positivity) (by positivity)
        exact mul_le_mul h5 h6 (abs_nonneg _) (by positivity)
    _ < 2 ^ (L.w - 1) := by
        rw [show L.w - 1 = (L.b + L.kq + L.F + L.lq + 13) by unfold Lay.w; omega]
        have : (256 : ℤ) * (2 * (2 ^ L.kq * (2 ^ (L.F + L.lq + 1) * 2 ^ L.b))) =
            2 ^ (L.b + L.kq + L.F + L.lq + 10) := by
          rw [show L.b + L.kq + L.F + L.lq + 10 = L.kq + (L.F + L.lq + 1) + L.b + 9 by omega]
          simp only [pow_add]
          norm_num
          ring
        rw [this]
        exact pow_lt_pow_right₀ (by norm_num) (by omega)

end Inp

/-! ### The register file -/

section Regs

variable {B : Type} {L : Lay}

/-- The final register file of the program on the input configuration `x`. -/
def regsO (I : Inp B L) (x : B → Bool) : RO L → BitVec L.w := runOps x (prog I) 0

theorem regsO_dst (I : Inp B L) (x : B → Bool) :
    ∀ o ∈ prog I, regsO I x o.dst = o.val (cfgOf x (regsO I x)) :=
  runOps_dst (lvO L) (prog I) (progOK I) x 0

theorem memA (I : Inp B L) {o : ROp B (RO L) L.w} (h : o ∈ opsA I) : o ∈ prog I := by
  simp only [prog, List.mem_append]
  tauto

theorem memB (I : Inp B L) {o : ROp B (RO L) L.w} (h : o ∈ chainB) : o ∈ prog I := by
  simp only [prog, List.mem_append]
  tauto

theorem memC (I : Inp B L) {o : ROp B (RO L) L.w} (h : o ∈ opsC I) : o ∈ prog I := by
  simp only [prog, List.mem_append]
  tauto

theorem memD (I : Inp B L) {o : ROp B (RO L) L.w} (h : o ∈ chainD) : o ∈ prog I := by
  simp only [prog, List.mem_append]
  tauto

theorem memE (I : Inp B L) {o : ROp B (RO L) L.w} (h : o ∈ chainE) : o ∈ prog I := by
  simp only [prog, List.mem_append]
  tauto

theorem memF (I : Inp B L) {o : ROp B (RO L) L.w} (h : o ∈ chainF) : o ∈ prog I := by
  simp only [prog, List.mem_append]
  tauto

theorem memG (I : Inp B L) {o : ROp B (RO L) L.w} (h : o ∈ chainG) : o ∈ prog I := by
  simp only [prog, List.mem_append]
  tauto

theorem memA_get (I : Inp B L) (k : ℕ) (hk : k < 25) :
    (opsA I)[k]'(by simp [opsA]; omega) ∈ prog I :=
  memA I (List.getElem_mem _)

theorem memC_get (I : Inp B L) (k : ℕ) (hk : k < 6) :
    (opsC I)[k]'(by simp [opsC]; omega) ∈ prog I :=
  memC I (List.getElem_mem _)

end Regs

/-! ### Register values -/

section Values

variable {B : Type} {L : Lay} (I : Inp B L) (x : B → Bool)

theorem w_pos : 0 < L.w := by unfold Lay.w; omega

/-- The value of an explicit register operation on integers. -/
theorem val_mk (d : RO L) (a : ℕ → PW B L) (b : ℕ → BSrc (PW B L)) (s : BSrc (PW B L))
    (y : PW B L → Bool) (α β : ℤ) (ha : readBV a L.w y = BitVec.ofInt L.w α)
    (hb : ofBits (fun i => (b i).val y) L.w = BitVec.ofInt L.w β) :
    ROp.val (⟨d, a, b, s⟩ : ROp B (RO L) L.w) y =
      BitVec.ofInt L.w (α + (if s.val y then -β else β)) :=
  val_ofInt _ y α β ha hb

theorem cfg_inl (F : RO L → BitVec L.w) (u : B) : cfgOf x F (.inl u : PW B L) = x u := rfl

/-! #### Zero tests and the tag split -/

theorem v_ax1 (hL : L.OK) : regsO I x .ax1 = BitVec.ofInt L.w |I.X1 x| := by
  have hd := regsO_dst I x _ (memA_get I 0 (by norm_num))
  change regsO I x .ax1 =
    ROp.val ⟨.ax1, zA, inB I.x1, inMsb I.x1 true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (I.X1 x) (readBV_zA x _) (ofBits_inB x _ I.x1 hL.b_pos)]
  congr 1
  simp only [inMsb_val x _ I.x1 hL.b_pos, beq_true]
  unfold Inp.X1
  by_cases h : twos I.x1 x < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.1 h)]

theorem v_ax2 (hL : L.OK) : regsO I x .ax2 = BitVec.ofInt L.w |I.X2 x| := by
  have hd := regsO_dst I x _ (memA_get I 3 (by norm_num))
  change regsO I x .ax2 =
    ROp.val ⟨.ax2, zA, inB I.x2, inMsb I.x2 true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (I.X2 x) (readBV_zA x _) (ofBits_inB x _ I.x2 hL.b_pos)]
  congr 1
  simp only [inMsb_val x _ I.x2 hL.b_pos, beq_true]
  unfold Inp.X2
  by_cases h : twos I.x2 x < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.1 h)]

theorem v_n1 (hL : L.OK) : regsO I x .n1 = BitVec.ofInt L.w (|I.X1 x| + |I.Y1 x|) := by
  have hd := regsO_dst I x _ (memA_get I 1 (by norm_num))
  change regsO I x .n1 =
    ROp.val ⟨.n1, rA .ax1, inB I.y1, inMsb I.y1 true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ |I.X1 x| (I.Y1 x) (by rw [readBV_rA, v_ax1 I x hL])
      (ofBits_inB x _ I.y1 hL.b_pos)]
  congr 1
  simp only [inMsb_val x _ I.y1 hL.b_pos, beq_true]
  unfold Inp.Y1
  by_cases h : twos I.y1 x < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.1 h)]

theorem v_n2 (hL : L.OK) : regsO I x .n2 = BitVec.ofInt L.w (|I.X2 x| + |I.Y2 x|) := by
  have hd := regsO_dst I x _ (memA_get I 4 (by norm_num))
  change regsO I x .n2 =
    ROp.val ⟨.n2, rA .ax2, inB I.y2, inMsb I.y2 true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ |I.X2 x| (I.Y2 x) (by rw [readBV_rA, v_ax2 I x hL])
      (ofBits_inB x _ I.y2 hL.b_pos)]
  congr 1
  simp only [inMsb_val x _ I.y2 hL.b_pos, beq_true]
  unfold Inp.Y2
  by_cases h : twos I.y2 x < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.1 h)]

theorem v_z1 (hL : L.OK) : regsO I x .z1 = BitVec.ofInt L.w (-(|I.X1 x| + |I.Y1 x|)) := by
  have hd := regsO_dst I x _ (memA_get I 2 (by norm_num))
  change regsO I x .z1 = ROp.val ⟨.z1, zA, rB .n1, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (|I.X1 x| + |I.Y1 x|) (readBV_zA x _)
    (by rw [ofBits_rB, v_n1 I x hL])]
  congr 1
  simp [BSrc.val]

theorem v_z2 (hL : L.OK) : regsO I x .z2 = BitVec.ofInt L.w (-(|I.X2 x| + |I.Y2 x|)) := by
  have hd := regsO_dst I x _ (memA_get I 5 (by norm_num))
  change regsO I x .z2 = ROp.val ⟨.z2, zA, rB .n2, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (|I.X2 x| + |I.Y2 x|) (readBV_zA x _)
    (by rw [ofBits_rB, v_n2 I x hL])]
  congr 1
  simp [BSrc.val]

/-- The sign bit of the zero test is the indicator of a nonzero entry. -/
theorem msb_z (X Y : ℤ) (hX : |X| ≤ 2 ^ (L.b - 1)) (hY : |Y| ≤ 2 ^ (L.b - 1)) (hb : 0 < L.b) :
    (BitVec.ofInt L.w (-(|X| + |Y|))).getLsbD (L.w - 1) = decide (chi X Y = 1) := by
  have hp : (2 : ℤ) ^ (L.b - 1) + 2 ^ (L.b - 1) < 2 ^ (L.w - 1) := by
    rw [← two_mul, ← pow_succ']
    exact pow_lt_pow_right₀ (by norm_num) (by unfold Lay.w; omega)
  rw [msb_ofInt _ w_pos (by rw [abs_neg, abs_of_nonneg (by positivity)]; linarith)]
  unfold chi
  by_cases h : X = 0 ∧ Y = 0
  · rw [if_pos h, h.1, h.2]
    simp
  · rw [if_neg h]
    have : 0 < |X| + |Y| := by
      rcases not_and_or.1 h with h1 | h1
      · have := abs_pos.2 h1
        positivity
      · have := abs_pos.2 h1
        positivity
    simp only [decide_true, decide_eq_true_eq]
    linarith

theorem chi1_bit (hL : L.OK) :
    cfgOf x (regsO I x) (msbO .z1 : PW B L) = decide (chi (I.X1 x) (I.Y1 x) = 1) := by
  rw [msbO, cfgOf_regW x _ _ (by unfold Lay.w; omega), v_z1 I x hL]
  exact msb_z _ _ (twos_abs_le _ _) (twos_abs_le _ _) hL.b_pos

theorem chi2_bit (hL : L.OK) :
    cfgOf x (regsO I x) (msbO .z2 : PW B L) = decide (chi (I.X2 x) (I.Y2 x) = 1) := by
  rw [msbO, cfgOf_regW x _ _ (by unfold Lay.w; omega), v_z2 I x hL]
  exact msb_z _ _ (twos_abs_le _ _) (twos_abs_le _ _) hL.b_pos

theorem ite_chi (X Y : ℤ) : (if decide (chi X Y = 1) = true then (1 : ℤ) else 0) = chi X Y := by
  rcases chi_mem X Y with h | h <;> simp [h]

theorem v_q0 (hL : L.OK) :
    regsO I x .q0 = BitVec.ofInt L.w (chi (I.X1 x) (I.Y1 x) + chi (I.X2 x) (I.Y2 x)) := by
  have hd := regsO_dst I x _ (memA_get I 6 (by norm_num))
  change regsO I x .q0 = ROp.val ⟨.q0, b0A (msbO .z1), b0B (.lit (msbO .z2) true),
    .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (chi (I.X1 x) (I.Y1 x)) (chi (I.X2 x) (I.Y2 x))
      (by rw [readBV_b0A _ _ w_pos rfl, chi1_bit I x hL, ite_chi])
      (by rw [ofBits_b0B _ _ w_pos]; simp only [BSrc.val, chi2_bit I x hL, beq_true, ite_chi])]
  simp [BSrc.val]

theorem v_q1 (hL : L.OK) :
    regsO I x .q1 = BitVec.ofInt L.w (chi (I.X1 x) (I.Y1 x) + (1 - chi (I.X2 x) (I.Y2 x))) := by
  have hd := regsO_dst I x _ (memA_get I 7 (by norm_num))
  change regsO I x .q1 = ROp.val ⟨.q1, b0A (msbO .z1), b0B (.lit (msbO .z2) false),
    .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (chi (I.X1 x) (I.Y1 x))
      (1 - chi (I.X2 x) (I.Y2 x)) (by rw [readBV_b0A _ _ w_pos rfl, chi1_bit I x hL, ite_chi])
      (by
        rw [ofBits_b0B _ _ w_pos]
        simp only [BSrc.val, chi2_bit I x hL]
        rcases chi_mem (I.X2 x) (I.Y2 x) with h | h <;> simp [h])]
  simp [BSrc.val]

/-! #### The duration and the LCHS node -/

theorem v_du : regsO I x .du = BitVec.ofInt L.w ((I.U x : ℤ) - 2 ^ L.kq) := by
  have hd := regsO_dst I x _ (memA_get I 8 (by norm_num))
  change regsO I x .du =
    ROp.val ⟨.du, uA I.u, cB (2 ^ L.kq), .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_uA x _ I.u (by unfold Lay.w; omega)) (ofBits_cB x _ _)]
  congr 1

theorem v_de : regsO I x .de =
    BitVec.ofInt L.w (if x I.ini then 2 * ((I.U x : ℤ) - 2 ^ L.kq) else 0) := by
  have hd := regsO_dst I x _ (memA_get I 9 (by norm_num))
  change regsO I x .de =
    ROp.val ⟨.de, rA .du, rB .du, .lit (.inl I.ini) false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ ((I.U x : ℤ) - 2 ^ L.kq) ((I.U x : ℤ) - 2 ^ L.kq)
    (by rw [readBV_rA, v_du]) (by rw [ofBits_rB, v_du])]
  congr 1
  rcases Bool.eq_false_or_eq_true (x I.ini) with h | h <;> simp [BSrc.val, cfg_inl, h]
  ring

theorem v_dd : regsO I x .dd = BitVec.ofInt L.w (2 * I.dv x) := by
  have hd := regsO_dst I x _ (memA_get I 10 (by norm_num))
  change regsO I x .dd =
    ROp.val ⟨.dd, rA .de, cB (2 ^ (L.kq + 1)), .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (if x I.ini then 2 * ((I.U x : ℤ) - 2 ^ L.kq) else 0)
    ((2 ^ (L.kq + 1) : ℕ) : ℤ) (by rw [readBV_rA, v_de]) (ofBits_cB x _ _)]
  congr 1
  unfold Inp.dv
  simp only [BSrc.val]
  push_cast
  split_ifs <;> ring

theorem v_nw : regsO I x .nw = BitVec.ofInt L.w ((I.V x : ℤ) - L.K) := by
  have hd := regsO_dst I x _ (memA_get I 11 (by norm_num))
  change regsO I x .nw =
    ROp.val ⟨.nw, uA I.wd, cB L.K, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_uA x _ I.wd (by unfold Lay.w; omega)) (ofBits_cB x _ _)]
  congr 1

theorem v_rg : regsO I x .rg = BitVec.ofInt L.w ((I.V x : ℤ) - L.J) := by
  have hd := regsO_dst I x _ (memA_get I 12 (by norm_num))
  change regsO I x .rg =
    ROp.val ⟨.rg, uA I.wd, cB L.J, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_uA x _ I.wd (by unfold Lay.w; omega)) (ofBits_cB x _ _)]
  congr 1

theorem msb_rg (hL : L.OK) :
    (regsO I x .rg).getLsbD (L.w - 1) = decide (I.V x < L.J) := by
  have hV : ((I.V x : ℕ) : ℤ) < 2 ^ L.lq := by
    have := GatePointerEncoding.wordValue_lt_pow (fun j => x (I.wd j))
    exact_mod_cast this
  have hJ : (L.J : ℤ) ≤ 2 ^ L.lq := by exact_mod_cast hL.J_le
  have hp : (2 : ℤ) ^ L.lq < 2 ^ (L.w - 1) :=
    pow_lt_pow_right₀ (by norm_num) (by unfold Lay.w; omega)
  rw [v_rg, msb_ofInt _ w_pos (by rw [abs_lt]; constructor <;> omega)]
  simp only [decide_eq_decide]
  omega

theorem v_nn (hL : L.OK) : regsO I x .nn = BitVec.ofInt L.w (2 * I.nv x) := by
  have hd := regsO_dst I x _ (memA_get I 13 (by norm_num))
  change regsO I x .nn =
    ROp.val ⟨.nn, rA .nw, rB .nw, .lit (msbO .rg) false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ ((I.V x : ℤ) - L.K) ((I.V x : ℤ) - L.K)
    (by rw [readBV_rA, v_nw]) (by rw [ofBits_rB, v_nw]), msbO_val, msb_rg I x hL]
  congr 1
  unfold Inp.nv
  by_cases h : I.V x < L.J
  · simp [h]
    ring
  · simp [h]

/-! #### The combination of the stored entries -/

theorem v_hx (hL : L.OK) : regsO I x .hx = BitVec.ofInt L.w (I.Y1 x + I.Y2 x) := by
  have hd := regsO_dst I x _ (memA_get I 14 (by norm_num))
  change regsO I x .hx =
    ROp.val ⟨.hx, inA I.y1, inB I.y2, .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_inA x _ I.y1 hL.b_pos) (ofBits_inB x _ I.y2 hL.b_pos)]
  rfl

theorem v_hy (hL : L.OK) : regsO I x .hy = BitVec.ofInt L.w (I.X2 x - I.X1 x) := by
  have hd := regsO_dst I x _ (memA_get I 15 (by norm_num))
  change regsO I x .hy =
    ROp.val ⟨.hy, inA I.x2, inB I.x1, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_inA x _ I.x2 hL.b_pos) (ofBits_inB x _ I.x1 hL.b_pos)]
  congr 1

theorem v_lx (hL : L.OK) : regsO I x .lx = BitVec.ofInt L.w (I.X1 x + I.X2 x) := by
  have hd := regsO_dst I x _ (memA_get I 16 (by norm_num))
  change regsO I x .lx =
    ROp.val ⟨.lx, inA I.x1, inB I.x2, .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_inA x _ I.x1 hL.b_pos) (ofBits_inB x _ I.x2 hL.b_pos)]
  rfl

theorem v_ly (hL : L.OK) : regsO I x .ly = BitVec.ofInt L.w (I.Y1 x - I.Y2 x) := by
  have hd := regsO_dst I x _ (memA_get I 17 (by norm_num))
  change regsO I x .ly =
    ROp.val ⟨.ly, inA I.y1, inB I.y2, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ _ _ (readBV_inA x _ I.y1 hL.b_pos) (ofBits_inB x _ I.y2 hL.b_pos)]
  congr 1

theorem v_sx (hL : L.OK) :
    regsO I x .sx = BitVec.ofInt L.w ((I.X1 x + I.X2 x) - (I.Y1 x + I.Y2 x)) := by
  have hd := regsO_dst I x _ (memA_get I 18 (by norm_num))
  change regsO I x .sx =
    ROp.val ⟨.sx, rA .lx, rB .hx, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (I.X1 x + I.X2 x) (I.Y1 x + I.Y2 x)
    (by rw [readBV_rA, v_lx I x hL]) (by rw [ofBits_rB, v_hx I x hL])]
  congr 1

theorem v_ex (hL : L.OK) : regsO I x .ex = BitVec.ofInt L.w
    (if x I.pt then 2 * ((I.X1 x + I.X2 x) - (I.Y1 x + I.Y2 x)) else 0) := by
  have hd := regsO_dst I x _ (memA_get I 19 (by norm_num))
  change regsO I x .ex =
    ROp.val ⟨.ex, rA .sx, rB .sx, .lit (.inl I.pt) false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ ((I.X1 x + I.X2 x) - (I.Y1 x + I.Y2 x))
    ((I.X1 x + I.X2 x) - (I.Y1 x + I.Y2 x))
    (by rw [readBV_rA, v_sx I x hL]) (by rw [ofBits_rB, v_sx I x hL])]
  congr 1
  rcases Bool.eq_false_or_eq_true (x I.pt) with h | h <;> simp [BSrc.val, cfg_inl, h]
  ring

theorem v_ax (hL : L.OK) : regsO I x .ax = BitVec.ofInt L.w (2 * I.ax x) := by
  have hd := regsO_dst I x _ (memA_get I 20 (by norm_num))
  change regsO I x .ax =
    ROp.val ⟨.ax, shA .hx 1, rB .ex, .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ ((I.Y1 x + I.Y2 x) * 2 ^ 1)
    (if x I.pt then 2 * ((I.X1 x + I.X2 x) - (I.Y1 x + I.Y2 x)) else 0)
    (by rw [readBV_shA, v_hx I x hL, ofInt_mul']) (by rw [ofBits_rB, v_ex I x hL])]
  congr 1
  unfold Inp.ax
  rcases Bool.eq_false_or_eq_true (x I.pt) with h | h <;> simp [BSrc.val, h] <;> ring

theorem v_sy (hL : L.OK) :
    regsO I x .sy = BitVec.ofInt L.w ((I.Y1 x - I.Y2 x) - (I.X2 x - I.X1 x)) := by
  have hd := regsO_dst I x _ (memA_get I 21 (by norm_num))
  change regsO I x .sy =
    ROp.val ⟨.sy, rA .ly, rB .hy, .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (I.Y1 x - I.Y2 x) (I.X2 x - I.X1 x)
    (by rw [readBV_rA, v_ly I x hL]) (by rw [ofBits_rB, v_hy I x hL])]
  congr 1

theorem v_ey (hL : L.OK) : regsO I x .ey = BitVec.ofInt L.w
    (if x I.pt then 2 * ((I.Y1 x - I.Y2 x) - (I.X2 x - I.X1 x)) else 0) := by
  have hd := regsO_dst I x _ (memA_get I 22 (by norm_num))
  change regsO I x .ey =
    ROp.val ⟨.ey, rA .sy, rB .sy, .lit (.inl I.pt) false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ ((I.Y1 x - I.Y2 x) - (I.X2 x - I.X1 x))
    ((I.Y1 x - I.Y2 x) - (I.X2 x - I.X1 x))
    (by rw [readBV_rA, v_sy I x hL]) (by rw [ofBits_rB, v_sy I x hL])]
  congr 1
  rcases Bool.eq_false_or_eq_true (x I.pt) with h | h <;> simp [BSrc.val, cfg_inl, h]
  ring

theorem v_ay (hL : L.OK) : regsO I x .ay = BitVec.ofInt L.w
    (2 * (if x I.pt then I.Y1 x - I.Y2 x else I.X2 x - I.X1 x)) := by
  have hd := regsO_dst I x _ (memA_get I 23 (by norm_num))
  change regsO I x .ay =
    ROp.val ⟨.ay, shA .hy 1, rB .ey, .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ ((I.X2 x - I.X1 x) * 2 ^ 1)
    (if x I.pt then 2 * ((I.Y1 x - I.Y2 x) - (I.X2 x - I.X1 x)) else 0)
    (by rw [readBV_shA, v_hy I x hL, ofInt_mul']) (by rw [ofBits_rB, v_ey I x hL])]
  congr 1
  rcases Bool.eq_false_or_eq_true (x I.pt) with h | h <;> simp [BSrc.val, h] <;> ring

theorem v_ayt (hL : L.OK) : regsO I x .ayt = BitVec.ofInt L.w (2 * I.ay x) := by
  have hd := regsO_dst I x _ (memA_get I 24 (by norm_num))
  change regsO I x .ayt =
    ROp.val ⟨.ayt, zA, rB .ay, .lit (.inl I.tg) true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (2 * (if x I.pt then I.Y1 x - I.Y2 x else I.X2 x - I.X1 x))
    (readBV_zA x _) (by rw [ofBits_rB, v_ay I x hL])]
  congr 1
  unfold Inp.ay
  rcases Bool.eq_false_or_eq_true (x I.tg) with h | h <;> simp [BSrc.val, cfg_inl, h]

/-! #### The part multiplier -/

theorem v_hc (hL : L.OK) :
    regsO I x (.hc (Fin.last _)) = BitVec.ofInt L.w (2 * L.Hn * (2 * I.nv x)) := by
  have h := chain_last (m := L.F + 1) x (regsO I x) RO.hc .nn
    (fun j => .const (L.Hn.testBit j)) (2 * I.nv x) (v_nn I x hL)
    (fun o ho => regsO_dst I x o (memB I ho))
  have hs : (∑ j ∈ Finset.range (L.F + 1), if (BSrc.const (L.Hn.testBit j) : BSrc (PW B L)).val
      (cfgOf x (regsO I x)) then (2 ^ j : ℤ) else 0) = L.Hn :=
    sum_testBit _ _ hL.Hn_lt
  rw [h, hs]

theorem v_md (hL : L.OK) :
    regsO I x .md = BitVec.ofInt L.w (2 * L.Hn * (2 * I.nv x) - 2 ^ (L.F + 2)) := by
  have hd := regsO_dst I x _ (memC_get I 0 (by norm_num))
  change regsO I x .md = ROp.val ⟨.md, rA (.hc (Fin.last _)), cB (2 ^ (L.F + 2)),
    .const true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (2 * L.Hn * (2 * I.nv x)) ((2 ^ (L.F + 2) : ℕ) : ℤ)
    (by rw [readBV_rA, v_hc I x hL]) (ofBits_cB x _ _)]
  congr 1

theorem v_me (hL : L.OK) : regsO I x .me = BitVec.ofInt L.w
    (if x I.pt then 2 * (2 * L.Hn * (2 * I.nv x) - 2 ^ (L.F + 2)) else 0) := by
  have hd := regsO_dst I x _ (memC_get I 1 (by norm_num))
  change regsO I x .me =
    ROp.val ⟨.me, rA .md, rB .md, .lit (.inl I.pt) false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (2 * L.Hn * (2 * I.nv x) - 2 ^ (L.F + 2))
    (2 * L.Hn * (2 * I.nv x) - 2 ^ (L.F + 2))
    (by rw [readBV_rA, v_md I x hL]) (by rw [ofBits_rB, v_md I x hL])]
  congr 1
  rcases Bool.eq_false_or_eq_true (x I.pt) with h | h <;> simp [BSrc.val, cfg_inl, h]
  ring

theorem v_mu (hL : L.OK) : regsO I x .mu = BitVec.ofInt L.w (8 * I.mu x) := by
  have hd := regsO_dst I x _ (memC_get I 2 (by norm_num))
  change regsO I x .mu =
    ROp.val ⟨.mu, rA .me, cB (2 ^ (L.F + 3)), .const false⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ (if x I.pt then 2 * (2 * L.Hn * (2 * I.nv x) - 2 ^ (L.F + 2)) else 0)
    ((2 ^ (L.F + 3) : ℕ) : ℤ) (by rw [readBV_rA, v_me I x hL]) (ofBits_cB x _ _)]
  congr 1
  unfold Inp.mu
  simp only [BSrc.val]
  push_cast
  split_ifs <;> ring

theorem abs_mu8_lt (hL : L.OK) : |8 * I.mu x| < 2 ^ L.mA := by
  have h := I.mu_abs_le x hL
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 8)]
  calc 8 * |I.mu x| ≤ 8 * 2 ^ (L.F + L.lq + 1) := by linarith
    _ = 2 ^ (L.F + L.lq + 4) := by ring
    _ < 2 ^ L.mA := pow_lt_pow_right₀ (by norm_num) (by unfold Lay.mA; omega)

theorem msb_mu (hL : L.OK) : (regsO I x .mu).getLsbD (L.w - 1) = decide (I.mu x < 0) := by
  have h := abs_mu8_lt I x hL
  have hp : (2 : ℤ) ^ L.mA < 2 ^ (L.w - 1) :=
    pow_lt_pow_right₀ (by norm_num) (by unfold Lay.mA Lay.w; omega)
  rw [v_mu I x hL, msb_ofInt _ w_pos (h.trans hp)]
  simp only [decide_eq_decide]
  omega

theorem v_am (hL : L.OK) : regsO I x .am = BitVec.ofInt L.w (8 * |I.mu x|) := by
  have hd := regsO_dst I x _ (memC_get I 3 (by norm_num))
  change regsO I x .am =
    ROp.val ⟨.am, zA, rB .mu, .lit (msbO .mu) true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (8 * I.mu x) (readBV_zA x _) (by rw [ofBits_rB, v_mu I x hL]),
    msbO_val, msb_mu I x hL]
  congr 1
  by_cases h : I.mu x < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.1 h)]

theorem v_axs (hL : L.OK) : regsO I x .axs =
    BitVec.ofInt L.w (if I.mu x < 0 then -(2 * I.ax x) else 2 * I.ax x) := by
  have hd := regsO_dst I x _ (memC_get I 4 (by norm_num))
  change regsO I x .axs =
    ROp.val ⟨.axs, zA, rB .ax, .lit (msbO .mu) true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (2 * I.ax x) (readBV_zA x _) (by rw [ofBits_rB, v_ax I x hL]),
    msbO_val, msb_mu I x hL]
  congr 1
  by_cases h : I.mu x < 0 <;> simp [h]

theorem v_ays (hL : L.OK) : regsO I x .ays =
    BitVec.ofInt L.w (if I.mu x < 0 then -(2 * I.ay x) else 2 * I.ay x) := by
  have hd := regsO_dst I x _ (memC_get I 5 (by norm_num))
  change regsO I x .ays =
    ROp.val ⟨.ays, zA, rB .ayt, .lit (msbO .mu) true⟩ (cfgOf x (regsO I x)) at hd
  rw [hd, val_mk _ _ _ _ _ 0 (2 * I.ay x) (readBV_zA x _) (by rw [ofBits_rB, v_ayt I x hL]),
    msbO_val, msb_mu I x hL]
  congr 1
  by_cases h : I.mu x < 0 <;> simp [h]

/-! #### The three chains -/

theorem bit1_small (v : ℤ) (hv : v = 0 ∨ v = 1 ∨ v = 2) :
    (BitVec.ofInt L.w v).getLsbD 1 = decide (v = 2) := by
  have h1 : 1 < L.w := by unfold Lay.w; omega
  rcases hv with rfl | rfl | rfl
  · rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) from rfl, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat]
    simp only [h1, decide_true, Bool.true_and]
    decide
  · rw [show ((1 : ℤ)) = ((1 : ℕ) : ℤ) from rfl, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat]
    simp only [h1, decide_true, Bool.true_and]
    decide
  · rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, BitVec.ofInt_natCast, BitVec.getLsbD_ofNat]
    simp only [h1, decide_true, Bool.true_and]
    decide

theorem q0_bit (hL : L.OK) : (regsO I x .q0).getLsbD 1 =
    decide (chi (I.X1 x) (I.Y1 x) + chi (I.X2 x) (I.Y2 x) = 2) := by
  rw [v_q0 I x hL]
  apply bit1_small
  rcases chi_mem (I.X1 x) (I.Y1 x) with ha | ha <;>
    rcases chi_mem (I.X2 x) (I.Y2 x) with hb | hb <;> norm_num [ha, hb]

theorem q1_bit (hL : L.OK) : (regsO I x .q1).getLsbD 1 =
    decide (chi (I.X1 x) (I.Y1 x) + (1 - chi (I.X2 x) (I.Y2 x)) = 2) := by
  rw [v_q1 I x hL]
  apply bit1_small
  rcases chi_mem (I.X1 x) (I.Y1 x) with ha | ha <;>
    rcases chi_mem (I.X2 x) (I.Y2 x) with hb | hb <;> norm_num [ha, hb]

theorem v_cc (hL : L.OK) :
    regsO I x (.cc (Fin.last 2)) = BitVec.ofInt L.w (2 * I.ct x * (2 * I.dv x)) := by
  have h := chain_last (m := 2) x (regsO I x) RO.cc .dd
    (fun j => if j = 0 then .lit (regW .q0 1) true else .lit (regW .q1 1) true) (2 * I.dv x)
    (v_dd I x) (fun o ho => regsO_dst I x o (memD I ho))
  have hsum : (∑ j ∈ Finset.range 2, if (if j = 0 then BSrc.lit (regW RO.q0 1) true else
      BSrc.lit (regW RO.q1 1) true : BSrc (PW B L)).val (cfgOf x (regsO I x)) then (2 ^ j : ℤ)
      else 0) = I.ct x := by
    have h1 : 1 < L.w := by unfold Lay.w; omega
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.one_ne_zero, reduceIte, BSrc.val, beq_true,
      cfgOf_regW x (regsO I x) RO.q0 h1, cfgOf_regW x (regsO I x) RO.q1 h1, q0_bit I x hL,
      q1_bit I x hL, decide_eq_true_eq]
    unfold Inp.ct
    rcases chi_mem (I.X1 x) (I.Y1 x) with ha | ha <;>
      rcases chi_mem (I.X2 x) (I.Y2 x) with hb | hb <;> norm_num [ha, hb]
  rw [h, hsum]

theorem v_ec (hL : L.OK) : regsO I x (.ec (Fin.last _)) =
    BitVec.ofInt L.w (64 * (I.ct x * (I.dv x * |I.mu x|))) := by
  have h := chain_last (m := L.mA) x (regsO I x) RO.ec (.cc (Fin.last 2))
    (fun j => .lit (regW .am j) true) (2 * I.ct x * (2 * I.dv x)) (v_cc I x hL)
    (fun o ho => regsO_dst I x o (memE I ho))
  have hmA : L.mA < L.w := by unfold Lay.mA Lay.w; omega
  have hlt : 8 * |I.mu x| < 2 ^ L.mA := by
    have := abs_mu8_lt I x hL
    rwa [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 8)] at this
  have hsum : (∑ j ∈ Finset.range L.mA, if (BSrc.lit (regW .am j) true : BSrc (PW B L)).val
      (cfgOf x (regsO I x)) then (2 ^ j : ℤ) else 0) = 8 * |I.mu x| := by
    rw [← digits_ofInt (w := L.w) (8 * |I.mu x|) L.mA hmA (by positivity) hlt]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range] at hj
    simp only [BSrc.val, beq_true]
    rw [cfgOf_regW x _ _ (by omega), v_am I x hL]
  rw [h, hsum]
  congr 1
  ring

theorem ec_lt (hL : L.OK) : 64 * (I.ct x * (I.dv x * |I.mu x|)) < 2 ^ L.mS := by
  have h1 := I.ct_nonneg x
  have h2 := I.ct_le x
  have h3 := I.dv_nonneg x
  have h4 := I.dv_le x
  have h5 := I.mu_abs_le x hL
  calc 64 * (I.ct x * (I.dv x * |I.mu x|))
      ≤ 64 * (2 * (2 ^ L.kq * 2 ^ (L.F + L.lq + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul h2 _ (by positivity) (by norm_num)
        exact mul_le_mul h4 h5 (abs_nonneg _) (by positivity)
    _ = 2 ^ (L.kq + L.F + L.lq + 8) := by
        rw [show L.kq + L.F + L.lq + 8 = L.kq + (L.F + L.lq + 1) + 7 by omega]
        simp only [pow_add]
        ring
    _ < 2 ^ L.mS := pow_lt_pow_right₀ (by norm_num) (by unfold Lay.mS; omega)

theorem sum_ec (hL : L.OK) :
    (∑ j ∈ Finset.range L.mS, if (BSrc.lit (regW (.ec (Fin.last _)) j) true : BSrc (PW B L)).val
      (cfgOf x (regsO I x)) then (2 ^ j : ℤ) else 0) =
      64 * (I.ct x * (I.dv x * |I.mu x|)) := by
  have hmS : L.mS < L.w := by unfold Lay.mS Lay.w; omega
  have h0 : 0 ≤ 64 * (I.ct x * (I.dv x * |I.mu x|)) := by
    have := I.ct_nonneg x
    have := I.dv_nonneg x
    positivity
  rw [← digits_ofInt (w := L.w) _ L.mS hmS h0 (ec_lt I x hL)]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  simp only [BSrc.val, beq_true]
  rw [cfgOf_regW x _ _ (by omega), v_ec I x hL]

/-- **The real output register holds `zx`.** -/
theorem v_xc (hL : L.OK) : regsO I x (.xc (Fin.last _)) = BitVec.ofInt L.w (I.zx x) := by
  have h := chain_last (m := L.mS) x (regsO I x) RO.xc .axs
    (fun j => .lit (regW (.ec (Fin.last _)) j) true) _ (v_axs I x hL)
    (fun o ho => regsO_dst I x o (memF I ho))
  rw [h, sum_ec I x hL]
  congr 1
  unfold Inp.zx
  by_cases hm : I.mu x < 0
  · rw [if_pos hm, abs_of_neg hm]
    ring
  · rw [if_neg hm, abs_of_nonneg (not_lt.1 hm)]
    ring

/-- **The imaginary output register holds `zy`.** -/
theorem v_yc (hL : L.OK) : regsO I x (.yc (Fin.last _)) = BitVec.ofInt L.w (I.zy x) := by
  have h := chain_last (m := L.mS) x (regsO I x) RO.yc .ays
    (fun j => .lit (regW (.ec (Fin.last _)) j) true) _ (v_ays I x hL)
    (fun o ho => regsO_dst I x o (memG I ho))
  rw [h, sum_ec I x hL]
  congr 1
  unfold Inp.zy
  by_cases hm : I.mu x < 0
  · rw [if_pos hm, abs_of_neg hm]
    ring
  · rw [if_neg hm, abs_of_nonneg (not_lt.1 hm)]
    ring

theorem toInt_xc (hL : L.OK) : (regsO I x (.xc (Fin.last _))).toInt = I.zx x := by
  rw [v_xc I x hL, toInt_ofInt_of _ w_pos (I.zx_abs_lt x hL)]

theorem toInt_yc (hL : L.OK) : (regsO I x (.yc (Fin.last _))).toInt = I.zy x := by
  rw [v_yc I x hL, toInt_ofInt_of _ w_pos (I.zy_abs_lt x hL)]

end Values

end SparseHamiltonian.GateBinaryODE
