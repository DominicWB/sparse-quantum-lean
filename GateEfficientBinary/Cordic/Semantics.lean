import GateEfficientBinary.Cordic.Program

/-!
# What the CORDIC program computes

Under explicit width conditions (`CParams.OK`) no register overflows, so the registers of both
stages hold the integer CORDIC iterates `citer` exactly (`stage1`, `stage2`), the stage-1
angle register holds the accumulated angle modulo `2^w` (`acc1`) and the stage-2 angle
register holds it exactly (`acc2`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary.Cordic

/-- Width and constant conditions under which no register of the program overflows. -/
structure CParams.OK (P : CParams) : Prop where
  n2 : 2 ≤ P.n
  b1 : 0 < P.b
  T : P.n * P.n ≤ P.T
  S2 : P.T ≤ P.S2
  bP1 : 0 < P.bP
  bPw : P.bP < P.w
  U1 : 1 ≤ P.U
  w1 : P.T + P.b + 3 ≤ P.w
  w2 : 2 * (P.U * 2 ^ P.T + 2 ^ (P.T + P.b + 1 + P.S2)) < 2 ^ (P.w - 1)
  c1 : ∀ k, P.c1 k < 2 ^ (P.w - 1)
  c2 : ∀ k, P.c2 k ≤ 2 ^ P.bT
  acc2 : P.n * 2 ^ P.bT + 2 ^ P.bT < 2 ^ (P.w - 1)

variable {P : CParams}

theorem CParams.OK.w0 (hP : P.OK) : 0 < P.w := by
  have := hP.w1
  omega

/-! ### Membership in the program -/

theorem mem_prog_init1 {o : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w} (ho : o ∈ init1 P) :
    o ∈ prog P := by
  simp only [prog, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl ho)))

theorem mem_prog_iter1 {k : ℕ} (hk : k < P.n) {o : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w}
    (ho : o ∈ iterOps P RN.x1 RN.y1 RN.a1 P.c1 k) : o ∈ prog P := by
  simp only [prog, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ho⟩))))

theorem mem_prog_init2 {o : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w} (ho : o ∈ init2 P) :
    o ∈ prog P := by
  simp only [prog, List.mem_append]
  exact Or.inl (Or.inl (Or.inr ho))

theorem mem_prog_iter2 {k : ℕ} (hk : k < P.n) {o : ROp (Fin P.b ⊕ Fin P.b) (RN P.n) P.w}
    (ho : o ∈ iterOps P RN.x2 RN.y2 RN.a2 P.c2 k) : o ∈ prog P := by
  simp only [prog, List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk, ho⟩))

theorem mem_prog_clamp : clampOp P ∈ prog P := by
  simp [prog]

/-! ### Stage 1 -/

/-- The input components as integers. -/
def inX (v : Fin P.b ⊕ Fin P.b → Bool) : ℤ := (inBV P v false).toInt

/-- The input components as integers. -/
def inY (v : Fin P.b ⊕ Fin P.b → Bool) : ℤ := (inBV P v true).toInt

/-- The initial stage-1 point `±(X, Y) 2^T` in the closed right half-plane. -/
def p1 (v : Fin P.b ⊕ Fin P.b → Bool) : ℤ × ℤ :=
  (|inX v| * 2 ^ P.T, (if inX v < 0 then -inY v else inY v) * 2 ^ P.T)

theorem abs_inX_le (v : Fin P.b ⊕ Fin P.b → Bool) : |inX v| ≤ 2 ^ (P.b - 1) :=
  abs_toInt_le _

theorem abs_inY_le (v : Fin P.b ⊕ Fin P.b → Bool) : |inY v| ≤ 2 ^ (P.b - 1) :=
  abs_toInt_le _

theorem dvd_p1 (v : Fin P.b ⊕ Fin P.b → Bool) :
    (2 : ℤ) ^ P.T ∣ (p1 v).1 ∧ (2 : ℤ) ^ P.T ∣ (p1 v).2 :=
  ⟨Dvd.intro_left _ rfl, Dvd.intro_left _ rfl⟩

theorem norm_p1_le (hb : 0 < P.b) (v : Fin P.b ⊕ Fin P.b → Bool) :
    ‖toC (p1 v)‖ ≤ 2 ^ (P.T + P.b) := by
  have hX := abs_inX_le v
  have hY := abs_inY_le v
  have h1 : |(p1 v).1| ≤ 2 ^ (P.b - 1) * 2 ^ P.T := by
    simp only [p1, abs_mul, abs_abs, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ P.T)]
    exact mul_le_mul_of_nonneg_right hX (by positivity)
  have h2 : |(p1 v).2| ≤ 2 ^ (P.b - 1) * 2 ^ P.T := by
    simp only [p1, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 ^ P.T)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    split_ifs
    · rwa [abs_neg]
    · exact hY
  have hsum : |(p1 v).1| + |(p1 v).2| ≤ 2 ^ (P.T + P.b) := by
    have : (2 : ℤ) ^ (P.T + P.b) = 2 * (2 ^ (P.b - 1) * 2 ^ P.T) := by
      rw [show P.T + P.b = (P.b - 1) + 1 + P.T by omega, pow_add, pow_succ]
      ring
    omega
  calc ‖toC (p1 v)‖ ≤ |(toC (p1 v)).re| + |(toC (p1 v)).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = ((|(p1 v).1| + |(p1 v).2| : ℤ) : ℝ) := by
        rw [toC_re, toC_im]
        push_cast
        rfl
    _ ≤ 2 ^ (P.T + P.b) := by exact_mod_cast hsum

/-- Coordinates of the exact iterates stay in the signed range. -/
theorem citer_range (p : ℤ × ℤ) (n T w : ℕ) (hT : n * n ≤ T) (h1 : (2 : ℤ) ^ T ∣ p.1)
    (h2 : (2 : ℤ) ^ T ∣ p.2) (k : ℕ) (hk : k ≤ n) (hb : 2 * ‖toC p‖ < 2 ^ (w - 1)) :
    |(citer p k).1| < 2 ^ (w - 1) ∧ |(citer p k).2| < 2 ^ (w - 1) := by
  obtain ⟨hx, hy⟩ := abs_citer_le p n T hT h1 h2 k hk
  constructor
  · have : (|(citer p k).1| : ℝ) < 2 ^ (w - 1) := lt_of_le_of_lt hx hb
    exact_mod_cast this
  · have : (|(citer p k).2| : ℝ) < 2 ^ (w - 1) := lt_of_le_of_lt hy hb
    exact_mod_cast this

theorem norm_p1_lt (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    2 * ‖toC (p1 v)‖ < 2 ^ (P.w - 1) := by
  have h := norm_p1_le hP.b1 v
  have hw : (2 : ℝ) * 2 ^ (P.T + P.b) < 2 ^ (P.w - 1) := by
    rw [← pow_succ']
    exact pow_lt_pow_right₀ (by norm_num) (by have := hP.w1; omega)
  linarith

/-- **Stage 1.** The stage-1 registers hold the integer CORDIC iterates of `p1`. -/
theorem stage1 (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) (k : ℕ) (hk : k ≤ P.n) :
    ((regs P v (.x1 (ix P k))).toInt, (regs P v (.y1 (ix P k))).toInt) = citer (p1 v) k := by
  have hw := hP.w0
  induction k with
  | zero =>
      have hx := regs_dst v _ (mem_prog_init1 (o := ⟨.x1 (ix P 0), fun _ => zW P,
        inpS P false P.T, signX P⟩) (by simp [init1]))
      have hy := regs_dst v _ (mem_prog_init1 (o := ⟨.y1 (ix P 0), fun _ => zW P,
        inpS P true P.T, signX P⟩) (by simp [init1]))
      simp only at hx hy
      have hbw : P.b + P.T + 1 ≤ P.w := by have := hP.w1; omega
      rw [hx, hy, val_x1_init hw hP.b1 hbw, val_y1_init hw hP.b1 hbw]
      rfl
  | succ k ih =>
      have ih' := ih (by omega)
      have hx := regs_dst v _ (mem_prog_iter1 (by omega : k < P.n)
        (o := ⟨.x1 (ix P (k + 1)), regW (.x1 (ix P k)), shrS P (.y1 (ix P k)) k,
          .lit (msbW P (.y1 (ix P k))) true⟩) (by simp [iterOps]))
      have hy := regs_dst v _ (mem_prog_iter1 (by omega : k < P.n)
        (o := ⟨.y1 (ix P (k + 1)), regW (.y1 (ix P k)), shrS P (.x1 (ix P k)) k,
          .lit (msbW P (.y1 (ix P k))) false⟩) (by simp [iterOps]))
      simp only at hx hy
      rw [hx, hy, val_iter_x hw v _ RN.x1 RN.y1 k, val_iter_y hw v _ RN.x1 RN.y1 k, ih']
      obtain ⟨d1, d2⟩ := dvd_p1 (P := P) v
      obtain ⟨r1, r2⟩ := citer_range (p1 v) P.n P.T P.w hP.T d1 d2 (k + 1) hk (norm_p1_lt hP v)
      rw [citer_succ] at r1 r2 ⊢
      rw [bmod_two_pow_eq_self hw r1, bmod_two_pow_eq_self hw r2]

theorem toInt_bmod_self (x : BitVec P.w) : x.toInt.bmod (2 ^ P.w) = x.toInt := by
  rw [BitVec.toInt_eq_toNat_bmod, Int.bmod_bmod]

/-- The integer angle constants of stage 1. -/
def c1Z (P : CParams) (k : ℕ) : ℤ := P.c1 k

/-- The integer angle constants of stage 2. -/
def c2Z (P : CParams) (k : ℕ) : ℤ := P.c2 k

/-- **The stage-1 angle register** holds its initial value plus the accumulated angle,
modulo `2^w`. -/
theorem acc1 (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) (k : ℕ) (hk : k ≤ P.n) :
    (regs P v (.a1 (ix P k))).toInt =
      ((regs P v (.a1 (ix P 0))).toInt + cacc (p1 v) (c1Z P) k).bmod (2 ^ P.w) := by
  have hw := hP.w0
  induction k with
  | zero =>
      simp only [cacc, Finset.range_zero, Finset.sum_empty, add_zero]
      exact (toInt_bmod_self _).symm
  | succ k ih =>
      have ha := regs_dst v _ (mem_prog_iter1 (by omega : k < P.n)
        (o := ⟨.a1 (ix P (k + 1)), regW (.a1 (ix P k)), cstS P (P.c1 k),
          .lit (msbW P (.y1 (ix P k))) true⟩) (by simp [iterOps]))
      simp only at ha
      rw [ha, val_iter_a hw v _ RN.x1 RN.y1 RN.a1 P.c1 k (hP.c1 k), ih (by omega),
        stage1 hP v k (by omega), Int.bmod_add_bmod, cacc_succ, add_assoc]
      rfl

/-! ### Stage 2 -/

/-- The stage-1 output `x_n`. -/
def xOut (v : Fin P.b ⊕ Fin P.b → Bool) : ℤ := (citer (p1 v) P.n).1

/-- The initial stage-2 point `(U 2^T, x_n 2^S₂)`. -/
def p2 (v : Fin P.b ⊕ Fin P.b → Bool) : ℤ × ℤ := (P.U * 2 ^ P.T, xOut v * 2 ^ P.S2)

theorem xOut_nonneg (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) : 0 ≤ xOut v := by
  obtain ⟨d1, d2⟩ := dvd_p1 (P := P) v
  exact citer_fst_nonneg (p1 v) P.n P.T hP.n2 hP.T d1 d2 (by simp only [p1]; positivity)

theorem xOut_le (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    xOut v ≤ 2 ^ (P.T + P.b + 1) := by
  obtain ⟨d1, d2⟩ := dvd_p1 (P := P) v
  have h := (abs_citer_le (p1 v) P.n P.T hP.T d1 d2 P.n le_rfl).1
  have h2 := norm_p1_le hP.b1 v
  have h3 : ((xOut v : ℤ) : ℝ) ≤ 2 ^ (P.T + P.b + 1) := by
    calc ((xOut v : ℤ) : ℝ) ≤ |((citer (p1 v) P.n).1 : ℝ)| := le_abs_self _
      _ ≤ 2 * ‖toC (p1 v)‖ := h
      _ ≤ 2 * 2 ^ (P.T + P.b) := by linarith
      _ = 2 ^ (P.T + P.b + 1) := by ring
  exact_mod_cast h3

theorem dvd_p2 (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    (2 : ℤ) ^ P.T ∣ (p2 v).1 ∧ (2 : ℤ) ^ P.T ∣ (p2 v).2 := by
  refine ⟨Dvd.intro_left _ rfl, ?_⟩
  simp only [p2]
  exact Dvd.dvd.mul_left (pow_dvd_pow 2 hP.S2) _

theorem norm_p2_lt (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    2 * ‖toC (p2 v)‖ < 2 ^ (P.w - 1) := by
  have hx := xOut_le hP v
  have hx0 := xOut_nonneg hP v
  have h1 : ‖toC (p2 v)‖ ≤ (P.U * 2 ^ P.T + 2 ^ (P.T + P.b + 1 + P.S2) : ℕ) := by
    calc ‖toC (p2 v)‖ ≤ |(toC (p2 v)).re| + |(toC (p2 v)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = ((P.U * 2 ^ P.T : ℕ) : ℝ) + ((xOut v * 2 ^ P.S2 : ℤ) : ℝ) := by
          rw [toC_re, toC_im]
          simp only [p2]
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
          push_cast
          ring
      _ ≤ (P.U * 2 ^ P.T + 2 ^ (P.T + P.b + 1 + P.S2) : ℕ) := by
          have : xOut v * 2 ^ P.S2 ≤ 2 ^ (P.T + P.b + 1 + P.S2) := by
            rw [pow_add (2 : ℤ) (P.T + P.b + 1) P.S2]
            exact mul_le_mul_of_nonneg_right hx (by positivity)
          have : ((xOut v * 2 ^ P.S2 : ℤ) : ℝ) ≤ ((2 ^ (P.T + P.b + 1 + P.S2) : ℤ) : ℝ) := by
            exact_mod_cast this
          push_cast at this ⊢
          linarith
  have h2 : (2 : ℝ) * ((P.U * 2 ^ P.T + 2 ^ (P.T + P.b + 1 + P.S2) : ℕ) : ℝ) < 2 ^ (P.w - 1) :=
    by exact_mod_cast hP.w2
  linarith

/-- **Stage 2.** The stage-2 registers hold the integer CORDIC iterates of `p2`. -/
theorem stage2 (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) (k : ℕ) (hk : k ≤ P.n) :
    ((regs P v (.x2 (ix P k))).toInt, (regs P v (.y2 (ix P k))).toInt) = citer (p2 v) k := by
  have hw := hP.w0
  induction k with
  | zero =>
      have hx := regs_dst v _ (mem_prog_init2 (o := ⟨.x2 (ix P 0), fun _ => zW P,
        cstS P (P.U * 2 ^ P.T), .const false⟩) (by simp [init2]))
      have hy := regs_dst v _ (mem_prog_init2 (o := ⟨.y2 (ix P 0), fun _ => zW P,
        shlS P (.x1 (ix P P.n)) P.S2, .const false⟩) (by simp [init2]))
      simp only at hx hy
      have hxn : (regs P v (.x1 (ix P P.n))).toInt = xOut v := by
        rw [xOut, ← stage1 hP v P.n le_rfl]
      have hU : P.U * 2 ^ P.T < 2 ^ (P.w - 1) := by
        have := hP.w2
        have he : 0 < 2 ^ (P.T + P.b + 1 + P.S2) := by positivity
        omega
      have hX2 : (regs P v (.x1 (ix P P.n))).toInt * 2 ^ P.S2 < 2 ^ (P.w - 1) := by
        rw [hxn]
        have h1 := xOut_le hP v
        have h2 : xOut v * 2 ^ P.S2 ≤ 2 ^ (P.T + P.b + 1 + P.S2) := by
          rw [pow_add (2 : ℤ) (P.T + P.b + 1) P.S2]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)
        have h3 : ((2 ^ (P.T + P.b + 1 + P.S2) : ℕ) : ℤ) < ((2 ^ (P.w - 1) : ℕ) : ℤ) := by
          have := hP.w2
          have he : 0 ≤ P.U * 2 ^ P.T := by positivity
          exact_mod_cast (show 2 ^ (P.T + P.b + 1 + P.S2) < 2 ^ (P.w - 1) by omega)
        push_cast at h3
        linarith
      rw [hx, hy, val_x2_init hU, val_y2_init v _ (by rw [hxn]; exact xOut_nonneg hP v) hX2,
        hxn]
      rfl
  | succ k ih =>
      have ih' := ih (by omega)
      have hx := regs_dst v _ (mem_prog_iter2 (by omega : k < P.n)
        (o := ⟨.x2 (ix P (k + 1)), regW (.x2 (ix P k)), shrS P (.y2 (ix P k)) k,
          .lit (msbW P (.y2 (ix P k))) true⟩) (by simp [iterOps]))
      have hy := regs_dst v _ (mem_prog_iter2 (by omega : k < P.n)
        (o := ⟨.y2 (ix P (k + 1)), regW (.y2 (ix P k)), shrS P (.x2 (ix P k)) k,
          .lit (msbW P (.y2 (ix P k))) false⟩) (by simp [iterOps]))
      simp only at hx hy
      rw [hx, hy, val_iter_x hw v _ RN.x2 RN.y2 k, val_iter_y hw v _ RN.x2 RN.y2 k, ih']
      obtain ⟨d1, d2⟩ := dvd_p2 hP v
      obtain ⟨r1, r2⟩ := citer_range (p2 v) P.n P.T P.w hP.T d1 d2 (k + 1) hk (norm_p2_lt hP v)
      rw [citer_succ] at r1 r2 ⊢
      rw [bmod_two_pow_eq_self hw r1, bmod_two_pow_eq_self hw r2]

/-- The stage-2 angle register before the first step is never written. -/
theorem regs_a2_zero (v : Fin P.b ⊕ Fin P.b → Bool) : regs P v (.a2 (ix P 0)) = 0 := by
  apply runOps_of_forall_ne
  intro o ho
  simp only [prog, List.mem_append, List.mem_singleton] at ho
  rcases ho with (((ho | ho) | ho) | ho) | rfl
  · simp only [init1, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl <;> simp
  · simp only [List.mem_flatMap, List.mem_range, iterOps, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    obtain ⟨k, _, ho⟩ := ho
    rcases ho with rfl | rfl | rfl <;> simp
  · simp only [init2, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl <;> simp
  · simp only [List.mem_flatMap, List.mem_range, iterOps, List.mem_cons, List.not_mem_nil,
      or_false] at ho
    obtain ⟨k, hk, ho⟩ := ho
    rcases ho with rfl | rfl | rfl
    · simp
    · simp
    · intro h
      have h' := congrArg Fin.val (RN.a2.inj h)
      rw [ix_val (by omega), ix_val (by omega)] at h'
      omega
  · simp [clampOp]

theorem abs_cacc_le (p : ℤ × ℤ) (c : ℕ → ℤ) (B : ℤ) (hc : ∀ k, |c k| ≤ B) (m : ℕ) :
    |cacc p c m| ≤ m * B := by
  induction m with
  | zero => simp [cacc]
  | succ m ih =>
      rw [cacc_succ]
      have h1 : |isgn (citer p m) * c m| ≤ B := by
        rw [abs_mul]
        have : |isgn (citer p m)| = 1 := by
          unfold isgn
          split_ifs <;> simp
        rw [this, one_mul]
        exact hc m
      calc |cacc p c m + isgn (citer p m) * c m| ≤ |cacc p c m| + |isgn (citer p m) * c m| :=
            abs_add_le _ _
        _ ≤ m * B + B := add_le_add ih h1
        _ = ((m + 1 : ℕ) : ℤ) * B := by push_cast; ring

theorem abs_c2Z_le (hP : P.OK) (k : ℕ) : |c2Z P k| ≤ 2 ^ P.bT := by
  rw [c2Z, abs_of_nonneg (by positivity)]
  exact_mod_cast hP.c2 k

theorem abs_cacc2_lt (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) (m : ℕ) (hm : m ≤ P.n) :
    |cacc (p2 v) (c2Z P) m| + 2 ^ P.bT < 2 ^ (P.w - 1) := by
  have h1 := abs_cacc_le (p2 v) (c2Z P) _ (abs_c2Z_le hP) m
  have h2 : (m : ℤ) * 2 ^ P.bT ≤ P.n * 2 ^ P.bT :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hm) (by positivity)
  have h3 : ((P.n * 2 ^ P.bT + 2 ^ P.bT : ℕ) : ℤ) < ((2 ^ (P.w - 1) : ℕ) : ℤ) := by
    exact_mod_cast hP.acc2
  push_cast at h3
  linarith

/-- **The stage-2 angle register** holds the accumulated angle exactly. -/
theorem acc2 (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) (k : ℕ) (hk : k ≤ P.n) :
    (regs P v (.a2 (ix P k))).toInt = cacc (p2 v) (c2Z P) k := by
  have hw := hP.w0
  induction k with
  | zero =>
      rw [regs_a2_zero]
      simp [cacc]
  | succ k ih =>
      have ha := regs_dst v _ (mem_prog_iter2 (by omega : k < P.n)
        (o := ⟨.a2 (ix P (k + 1)), regW (.a2 (ix P k)), cstS P (P.c2 k),
          .lit (msbW P (.y2 (ix P k))) true⟩) (by simp [iterOps]))
      simp only at ha
      have hc : P.c2 k < 2 ^ (P.w - 1) := by
        have := hP.c2 k
        have := hP.acc2
        omega
      rw [ha, val_iter_a hw v _ RN.x2 RN.y2 RN.a2 P.c2 k hc, ih (by omega),
        stage2 hP v k (by omega)]
      have h := abs_cacc2_lt hP v (k + 1) hk
      rw [cacc_succ] at h ⊢
      exact bmod_two_pow_eq_self hw (by
        have : (0 : ℤ) ≤ 2 ^ P.bT := by positivity
        exact lt_of_le_of_lt (le_add_of_nonneg_right this) h)

/-- The stage-2 angle. -/
def ang2 (v : Fin P.b ⊕ Fin P.b → Bool) : ℤ := cacc (p2 v) (c2Z P) P.n

/-- **The clamp register** holds the stage-2 angle minus `2^bT`. -/
theorem regs_dc (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    (regs P v .dc).toInt = ang2 v - 2 ^ P.bT := by
  have hw := hP.w0
  have h := regs_dst v _ (mem_prog_clamp (P := P))
  have hT : 2 ^ P.bT < 2 ^ (P.w - 1) := by
    have := hP.acc2
    omega
  rw [show (clampOp P).dst = RN.dc from rfl] at h
  rw [h, val_dc hT, acc2 hP v P.n le_rfl]
  apply bmod_two_pow_eq_self hw
  have h1 := abs_cacc2_lt hP v P.n le_rfl
  calc |ang2 v - 2 ^ P.bT| ≤ |ang2 v| + |(2 : ℤ) ^ P.bT| := abs_sub _ _
    _ = |ang2 v| + 2 ^ P.bT := by rw [abs_of_pos (by positivity : (0 : ℤ) < 2 ^ P.bT)]
    _ < 2 ^ (P.w - 1) := h1

/-! ### The output words -/

/-- The sum of the low `p` bits of a bit vector is its value modulo `2^p`. -/
theorem sum_low_bits {w : ℕ} (A : BitVec w) (p : ℕ) :
    (∑ i ∈ Finset.range p, if A.getLsbD i then 2 ^ i else 0) = A.toNat % 2 ^ p := by
  rw [← BitVec.toNat_setWidth, toNat_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [BitVec.getLsbD_setWidth, decide_eq_true (Finset.mem_range.1 hi), Bool.true_and]

theorem sum_two_pow (p : ℕ) : (∑ i ∈ Finset.range p, (2 : ℕ) ^ i) = 2 ^ p - 1 := by
  have h := toNat_eq_sum (BitVec.allOnes p)
  rw [BitVec.toNat_allOnes] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  rw [BitVec.getLsbD_allOnes, decide_eq_true (Finset.mem_range.1 hi), if_pos rfl]

/-- The bits of the `φ` word, most significant first: the low `bP` bits of the final stage-1
angle register. -/
def phiBits (v : Fin P.b ⊕ Fin P.b → Bool) (j : Fin P.bP) : Bool :=
  (regs P v (.a1 (ix P P.n))).getLsbD (P.bP - 1 - j)

/-- Bit `i` of the clamped `θ` word, from the sign bits of the stage-2 angle and of the clamp
register. -/
def tBit (v : Fin P.b ⊕ Fin P.b → Bool) (i : ℕ) : Bool :=
  !(regs P v (.a2 (ix P P.n))).getLsbD (P.w - 1) &&
    (!(regs P v .dc).getLsbD (P.w - 1) || (regs P v (.a2 (ix P P.n))).getLsbD i)

/-- The bits of the `θ` word, most significant first. -/
def thetaBits (v : Fin P.b ⊕ Fin P.b → Bool) (j : Fin P.bT) : Bool := tBit v (P.bT - 1 - j)

/-- Clamping an integer to `[0, 2^m)`. -/
def clampN (a : ℤ) (m : ℕ) : ℕ := if a < 0 then 0 else if a < 2 ^ m then a.toNat else 2 ^ m - 1

/-- The initial stage-1 angle: `2^(bP-1)` when `X < 0`. -/
def a0 (v : Fin P.b ⊕ Fin P.b → Bool) : ℤ := if inX v < 0 then 2 ^ (P.bP - 1) else 0

/-- **The `φ` word**: its value is the accumulated stage-1 angle modulo `2^bP`. -/
theorem phi_word (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    (((∑ i ∈ Finset.range P.bP,
      if (regs P v (.a1 (ix P P.n))).getLsbD i then 2 ^ i else 0 : ℕ)) : ℤ) =
      (a0 v + cacc (p1 v) (c1Z P) P.n) % 2 ^ P.bP := by
  rw [sum_low_bits, toNat_mod_eq_toInt_emod _ _ hP.bPw.le, acc1 hP v P.n le_rfl]
  have hdvd : (2 : ℤ) ^ P.bP ∣ 2 ^ P.w := pow_dvd_pow 2 hP.bPw.le
  have h0 : (regs P v (.a1 (ix P 0))).toInt = a0 v := by
    have ha := regs_dst v _ (mem_prog_init1 (o := ⟨.a1 (ix P 0), fun _ => zW P,
      fun i => if i = P.bP - 1 then signX P else .const false, .const false⟩) (by simp [init1]))
    simp only at ha
    have hnat := val_a1_init (v := v) (F := regs P v) hP.b1 hP.bP1 hP.bPw.le
    rw [← ha] at hnat
    have hlt : 2 * (regs P v (.a1 (ix P 0))).toNat < 2 ^ P.w := by
      rw [hnat]
      split_ifs
      · rw [← pow_succ']
        exact Nat.pow_lt_pow_right (by norm_num) (by have := hP.bPw; have := hP.bP1; omega)
      · positivity
    rw [BitVec.toInt_eq_toNat_of_lt hlt, hnat, a0, inX]
    split_ifs <;> simp
  rw [h0]
  have h1 : (2 ^ P.w : ℤ) = ((2 ^ P.w : ℕ) : ℤ) := by push_cast; rfl
  rw [← Int.emod_emod_of_dvd _ hdvd, h1, Int.bmod_emod, ← h1, Int.emod_emod_of_dvd _ hdvd]

/-- The sign bit of the final stage-2 angle register. -/
theorem a2_msb (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    (regs P v (.a2 (ix P P.n))).getLsbD (P.w - 1) = decide (ang2 v < 0) := by
  rw [getLsbD_last_eq _ hP.w0, acc2 hP v P.n le_rfl]
  rfl

/-- The sign bit of the clamp register. -/
theorem dc_msb (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    (regs P v .dc).getLsbD (P.w - 1) = decide (ang2 v - 2 ^ P.bT < 0) := by
  rw [getLsbD_last_eq _ hP.w0, regs_dc hP v]

/-- **The `θ` word**: its value is the stage-2 angle clamped to `[0, 2^bT)`. -/
theorem theta_word (hP : P.OK) (v : Fin P.b ⊕ Fin P.b → Bool) :
    (∑ i ∈ Finset.range P.bT, if tBit v i then 2 ^ i else 0) = clampN (ang2 v) P.bT := by
  have hm := a2_msb hP v
  have hd := dc_msb hP v
  unfold tBit clampN
  rw [hm, hd]
  by_cases h1 : ang2 v < 0
  · simp [h1]
  · by_cases h2 : ang2 v < 2 ^ P.bT
    · have h3 : ang2 v - 2 ^ P.bT < 0 := by linarith
      simp only [h1, h2, h3, decide_true, decide_false, Bool.not_false, Bool.not_true,
        Bool.false_or, Bool.true_and, if_false, if_true]
      rw [sum_low_bits]
      have hA := acc2 hP v P.n le_rfl
      have hnn : 0 ≤ (regs P v (.a2 (ix P P.n))).toInt := by
        rw [hA]
        exact not_lt.1 h1
      have hlt : 2 * (regs P v (.a2 (ix P P.n))).toNat < 2 ^ P.w := by
        by_contra hc
        have := BitVec.toInt_eq_toNat_cond (regs P v (.a2 (ix P P.n)))
        rw [if_neg hc] at this
        have hb := BitVec.isLt (regs P v (.a2 (ix P P.n)))
        have : (regs P v (.a2 (ix P P.n))).toInt < 0 := by
          rw [this]
          have : ((regs P v (.a2 (ix P P.n))).toNat : ℤ) < ((2 ^ P.w : ℕ) : ℤ) := by
            exact_mod_cast hb
          linarith
        linarith
      have hval := BitVec.toInt_eq_toNat_of_lt hlt
      rw [hA] at hval
      have hn : (regs P v (.a2 (ix P P.n))).toNat = (ang2 v).toNat := by
        have : ((regs P v (.a2 (ix P P.n))).toNat : ℤ) = ((ang2 v).toNat : ℤ) := by
          rw [Int.toNat_of_nonneg (not_lt.1 h1), ← hval]
          rfl
        exact_mod_cast this
      rw [hn]
      apply Nat.mod_eq_of_lt
      have : ((ang2 v).toNat : ℤ) < ((2 ^ P.bT : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (not_lt.1 h1)]
        push_cast
        exact h2
      exact_mod_cast this
    · have h3 : ¬ (ang2 v - 2 ^ P.bT < 0) := by linarith
      simp only [h1, h2, h3, decide_false, Bool.not_false, Bool.true_or, Bool.true_and,
        if_true, if_false]
      exact sum_two_pow P.bT

end SparseHamiltonian.GateBinary.Cordic
