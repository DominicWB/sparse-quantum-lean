import GateEfficientHamiltonian.Circuit.Flags

/-!
# The dyadic boundary identity for vector amplitudes

The chronological boundary network on `2^m` slots couples one public mode
with each private slot by the rotation `R(c)` in increasing slot order.  The
amplitudes here are vectors of an arbitrary complex vector space (the system
payload), so the identity applies directly to the simulator registers.

`chron_eq_compressed` is the ordered-rotation factorisation of Chen, Gao, Ji,
Li, Wang and Zhou: an inverse input frame, a single central rotation by
`c^(2^m)`, and an output frame.  The frames are products of one rotation per
slot bit, conditioned on the lower bits being zero (`inFrameInv_eq_ascend`,
`outFrame_eq_descend`).  `chron_closed` gives the explicit sequential form
used to identify the network with the transducer blocks.
-/

namespace SparseHamiltonian.GateCircuit.Dyadic

noncomputable section
open GateDyadicBoundary (snocWord tailWord rootDenominator centralCosine centralSine
  snocWord_last tailWord_snocWord snocWord_tailWord rootDenominator_sq
  rootDenominator_ne_zero central_unit)
open scoped BigOperators

abbrev Word (m : ℕ) := Fin m → Bool

def zeroW (m : ℕ) : Word m := fun _ => false

variable {P : Type*} [AddCommGroup P] [Module ℂ P]

/-! ### Two- and three-mode rotations -/

/-- Rotation of a public and a private amplitude by the real cosine/sine pair. -/
def rot (z v : ℝ) (p a : P) : P × P :=
  ((z : ℂ) • p - (v : ℂ) • a, (v : ℂ) • p + (z : ℂ) • a)

/-- Inverse normalisation of the root frames. -/
abbrev kk (z : ℝ) : ℂ := ((rootDenominator z : ℝ) : ℂ)⁻¹

def inMix (z : ℝ) (a b : P) : P × P :=
  (kk z • ((z : ℂ) • a - b), kk z • (a + (z : ℂ) • b))

def inUnmix (z : ℝ) (a b : P) : P × P :=
  (kk z • ((z : ℂ) • a + b), kk z • (-a + (z : ℂ) • b))

def outMix (z : ℝ) (a b : P) : P × P :=
  (kk z • (a - (z : ℂ) • b), kk z • ((z : ℂ) • a + b))

theorem kk_sq (z : ℝ) : kk z * kk z * (1 + (z : ℂ) ^ 2) = 1 := by
  have hd : ((rootDenominator z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast rootDenominator_ne_zero z
  have h2 : ((rootDenominator z : ℝ) : ℂ) ^ 2 = 1 + (z : ℂ) ^ 2 := by
    exact_mod_cast rootDenominator_sq z
  rw [← h2]
  field_simp

theorem inMix_inUnmix (z : ℝ) (a b : P) :
    inMix z (inUnmix z a b).1 (inUnmix z a b).2 = (a, b) := by
  have h := kk_sq z
  simp only [inMix, inUnmix]
  apply Prod.ext
  · simp only [smul_add, smul_smul, smul_neg]
    have e1 : kk z * ((z : ℂ) * kk z) * (z : ℂ) + kk z * kk z = 1 := by
      linear_combination h
    have e2 : kk z * ((z : ℂ) * kk z) - kk z * (kk z * (z : ℂ)) = 0 := by ring
    calc _ = (kk z * ((z : ℂ) * kk z) * (z : ℂ) + kk z * kk z) • a +
          (kk z * ((z : ℂ) * kk z) - kk z * (kk z * (z : ℂ))) • b := by module
      _ = a := by rw [e1, e2]; simp
  · simp only [smul_add, smul_smul, smul_neg]
    have e1 : kk z * kk z * (z : ℂ) - kk z * ((z : ℂ) * kk z) = 0 := by ring
    have e2 : kk z * kk z + kk z * ((z : ℂ) * kk z) * (z : ℂ) = 1 := by
      linear_combination h
    calc _ = (kk z * kk z * (z : ℂ) - kk z * ((z : ℂ) * kk z)) • a +
          (kk z * kk z + kk z * ((z : ℂ) * kk z) * (z : ℂ)) • b := by module
      _ = b := by rw [e1, e2]; simp

/-- The coefficient form of the three-mode identity. -/
theorem two_halves_abstract (z v k rd : ℂ) (h : k * k * (1 + z ^ 2) = 1)
    (hu : z ^ 2 + v ^ 2 = 1) (hr : rd = k * (1 + z ^ 2)) (p a b : P) :
    let A1 := k • (z • a - b)
    let A2 := k • (a + z • b)
    let pa := (z • p - v • A1, v • p + z • A1)
    let qb := (z • pa.1 - v • A2, v • pa.1 + z • A2)
    let qa := ((z * z) • p - (v * rd) • a, (v * rd) • p + (z * z) • a)
    let ab' := (k • (qa.2 - z • b), k • (z • qa.2 + b))
    (qb.1, pa.2, qb.2) = (qa.1, ab'.1, ab'.2) := by
  intro A1 A2 pa qb qa ab'
  simp only [A1, A2, pa, qb, qa, ab', hr]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · match_scalars <;> ring
  · match_scalars
    · linear_combination (-v) * h
    · ring
    · ring
  · match_scalars
    · linear_combination (-v * z) * h
    · linear_combination (-k * z) * hu
    · linear_combination k * hu

/-- The three-mode identity behind the dyadic recursion, for vector amplitudes. -/
theorem two_halves (z v : ℝ) (hunit : z ^ 2 + v ^ 2 = 1) (p a b : P) :
    let ab := inMix z a b
    let pa := rot z v p ab.1
    let qb := rot z v pa.1 ab.2
    (qb.1, pa.2, qb.2) =
      let qa := rot (z * z) (v * rootDenominator z) p a
      let ab' := outMix z qa.2 b
      (qa.1, ab'.1, ab'.2) := by
  have h := kk_sq z
  have h2 : ((rootDenominator z : ℝ) : ℂ) ^ 2 = 1 + (z : ℂ) ^ 2 := by
    exact_mod_cast rootDenominator_sq z
  have hu : (z : ℂ) ^ 2 + (v : ℂ) ^ 2 = 1 := by exact_mod_cast hunit
  have hr : ((rootDenominator z : ℝ) : ℂ) = kk z * (1 + (z : ℂ) ^ 2) := by
    rw [← h2]; simp only [kk]
    have hd : ((rootDenominator z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast rootDenominator_ne_zero z
    field_simp
  have key := two_halves_abstract (z : ℂ) (v : ℂ) (kk z) ((rootDenominator z : ℝ) : ℂ)
    h hu hr p a b
  simp only [rot, inMix, outMix, Complex.ofReal_mul]
  exact key

/-! ### Words, halves and roots -/

variable {m : ℕ}

def lo (φ : Word (m + 1) → P) : Word m → P := fun w => φ (snocWord false w)
def hi (φ : Word (m + 1) → P) : Word m → P := fun w => φ (snocWord true w)

def joinW (φ0 φ1 : Word m → P) : Word (m + 1) → P :=
  fun w => if w (Fin.last m) then φ1 (tailWord w) else φ0 (tailWord w)

omit [AddCommGroup P] [Module ℂ P] in
@[simp] theorem lo_joinW (φ0 φ1 : Word m → P) : lo (joinW φ0 φ1) = φ0 := by
  funext w; simp [lo, joinW]

omit [AddCommGroup P] [Module ℂ P] in
@[simp] theorem hi_joinW (φ0 φ1 : Word m → P) : hi (joinW φ0 φ1) = φ1 := by
  funext w; simp [hi, joinW]

omit [AddCommGroup P] [Module ℂ P] in
theorem joinW_lo_hi (φ : Word (m + 1) → P) : joinW (lo φ) (hi φ) = φ := by
  funext w
  have hw := snocWord_tailWord w
  unfold joinW lo hi
  cases hb : w (Fin.last m)
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hb] at hw; rw [hw]
  · simp only [↓reduceIte]; rw [hb] at hw; rw [hw]

theorem zeroW_succ : zeroW (m + 1) = snocWord false (zeroW m) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [zeroW]
  | cast j => simp [zeroW, snocWord]

theorem snocWord_true_ne_zero (w : Word m) : snocWord true w ≠ zeroW (m + 1) := by
  intro h
  have := congrFun h (Fin.last m)
  simp [zeroW] at this

theorem snocWord_false_eq_zero_iff (w : Word m) :
    snocWord false w = zeroW (m + 1) ↔ w = zeroW m := by
  rw [zeroW_succ]
  constructor
  · intro h
    have := congrArg tailWord h
    simpa using this
  · intro h; rw [h]

/-- Replace the amplitude of the all-zero (root) slot. -/
def setRoot (φ : Word m → P) (a : P) : Word m → P := Function.update φ (zeroW m) a

omit [AddCommGroup P] [Module ℂ P] in
@[simp] theorem setRoot_zero (φ : Word m → P) (a : P) : setRoot φ a (zeroW m) = a := by
  simp [setRoot]

omit [AddCommGroup P] [Module ℂ P] in
theorem setRoot_ne (φ : Word m → P) (a : P) (w : Word m) (hw : w ≠ zeroW m) :
    setRoot φ a w = φ w := by
  simp [setRoot, Function.update_of_ne hw]

omit [AddCommGroup P] [Module ℂ P] in
@[simp] theorem setRoot_setRoot (φ : Word m → P) (a b : P) :
    setRoot (setRoot φ a) b = setRoot φ b := by
  simp [setRoot]

omit [AddCommGroup P] [Module ℂ P] in
@[simp] theorem setRoot_self (φ : Word m → P) : setRoot φ (φ (zeroW m)) = φ := by
  simp [setRoot]

omit [AddCommGroup P] [Module ℂ P] in
@[simp] theorem lo_setRoot (φ : Word (m + 1) → P) (a : P) :
    lo (setRoot φ a) = setRoot (lo φ) a := by
  funext w
  unfold lo setRoot
  by_cases hw : w = zeroW m
  · subst hw; rw [← zeroW_succ]; simp
  · have : snocWord false w ≠ zeroW (m + 1) :=
      fun h => hw ((snocWord_false_eq_zero_iff w).mp h)
    rw [Function.update_of_ne this, Function.update_of_ne hw]

omit [AddCommGroup P] [Module ℂ P] in
@[simp] theorem hi_setRoot (φ : Word (m + 1) → P) (a : P) :
    hi (setRoot φ a) = hi φ := by
  funext w
  unfold hi setRoot
  rw [Function.update_of_ne (snocWord_true_ne_zero w)]

omit [AddCommGroup P] [Module ℂ P] in
theorem lo_zero (φ : Word (m + 1) → P) : lo φ (zeroW m) = φ (zeroW (m + 1)) := by
  simp [lo, zeroW_succ]

/-! ### The chronological network and its compression -/

/-- Chronological star rotations: the left half (top bit zero) before the right
half, sharing the public amplitude.  In value order this is slot `0, 1, 2, …`. -/
def chron (c σ : ℝ) : (m : ℕ) → P × (Word m → P) → P × (Word m → P)
  | 0, s => let q := rot c σ s.1 (s.2 (zeroW 0)); (q.1, fun _ => q.2)
  | m + 1, s =>
      let L := chron c σ m (s.1, lo s.2)
      let R := chron c σ m (L.1, hi s.2)
      (R.1, joinW L.2 R.2)

def inFrame (c : ℝ) : (m : ℕ) → (Word m → P) → (Word m → P)
  | 0, φ => φ
  | m + 1, φ =>
      let r := inMix (centralCosine c m) (lo φ (zeroW m)) (hi φ (zeroW m))
      joinW (inFrame c m (setRoot (lo φ) r.1)) (inFrame c m (setRoot (hi φ) r.2))

def inFrameInv (c : ℝ) : (m : ℕ) → (Word m → P) → (Word m → P)
  | 0, φ => φ
  | m + 1, φ =>
      let L := inFrameInv c m (lo φ)
      let R := inFrameInv c m (hi φ)
      let r := inUnmix (centralCosine c m) (L (zeroW m)) (R (zeroW m))
      joinW (setRoot L r.1) (setRoot R r.2)

def outFrame (c : ℝ) : (m : ℕ) → (Word m → P) → (Word m → P)
  | 0, φ => φ
  | m + 1, φ =>
      let r := outMix (centralCosine c m) (lo φ (zeroW m)) (hi φ (zeroW m))
      joinW (outFrame c m (setRoot (lo φ) r.1)) (outFrame c m (setRoot (hi φ) r.2))

def central (c σ : ℝ) (m : ℕ) (s : P × (Word m → P)) : P × (Word m → P) :=
  let q := rot (centralCosine c m) (centralSine c σ m) s.1 (s.2 (zeroW m))
  (q.1, setRoot s.2 q.2)

/-- The compressed circuit: inverse input frame, central rotation, output frame. -/
def compressed (c σ : ℝ) (m : ℕ) (s : P × (Word m → P)) : P × (Word m → P) :=
  let q := central c σ m (s.1, inFrameInv c m s.2)
  (q.1, outFrame c m q.2)

theorem inFrame_inFrameInv (c : ℝ) (m : ℕ) (φ : Word m → P) :
    inFrame c m (inFrameInv c m φ) = φ := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp only [inFrameInv, inFrame, lo_joinW, hi_joinW, setRoot_zero]
      rw [inMix_inUnmix]
      simp only [setRoot_setRoot, setRoot_self, ih, joinW_lo_hi]

theorem chron_inFrame (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) (p : P)
    (φ : Word m → P) :
    chron c σ m (p, inFrame c m φ) =
      ((central c σ m (p, φ)).1, outFrame c m (central c σ m (p, φ)).2) := by
  induction m generalizing p with
  | zero =>
      simp only [chron, inFrame, central, outFrame, centralCosine, centralSine]
      congr 1
      funext w
      have : w = zeroW 0 := funext (fun j => Fin.elim0 j)
      subst this
      simp
  | succ m ih =>
      have hcc : centralCosine c (m + 1) = centralCosine c m * centralCosine c m := rfl
      have hcs : centralSine c σ (m + 1) =
          centralSine c σ m * rootDenominator (centralCosine c m) := rfl
      have H := two_halves (centralCosine c m) (centralSine c σ m) (central_unit c σ hunit m)
        p (φ (zeroW (m + 1))) (hi φ (zeroW m))
      simp only [Prod.mk.injEq] at H
      simp only [chron, inFrame, lo_joinW, hi_joinW]
      rw [ih, ih]
      simp only [central, setRoot_setRoot, setRoot_zero, outFrame, lo_setRoot, hi_setRoot,
        hcc, hcs, lo_zero]
      rw [H.1, H.2.1, H.2.2]

theorem chron_eq_compressed (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ)
    (s : P × (Word m → P)) : chron c σ m s = compressed c σ m s := by
  obtain ⟨p, φ⟩ := s
  conv_lhs => rw [← inFrame_inFrameInv c m φ]
  rw [chron_inFrame c σ hunit]
  rfl

/-! ### Frames as products of single-bit rotations -/

/-- All bits below `j` vanish. -/
def lowerZero (j : Fin m) (w : Word m) : Prop := ∀ i : Fin m, i < j → w i = false

instance (j : Fin m) (w : Word m) : Decidable (lowerZero j w) := by
  unfold lowerZero; infer_instance

/-- Rotation of bit `j` by `R` (row: new bit, column: old bit), applied exactly
where all lower bits vanish. -/
def bitRot (j : Fin m) (R : Matrix Bool Bool ℂ) (φ : Word m → P) : Word m → P :=
  fun w => if lowerZero j w then ∑ b : Bool, R (w j) b • φ (Function.update w j b) else φ w

theorem tailWord_update_castSucc (w : Word (m + 1)) (j : Fin m) (b : Bool) :
    tailWord (Function.update w j.castSucc b) = Function.update (tailWord w) j b := by
  funext i
  simp only [tailWord]
  by_cases h : i = j
  · subst h; simp
  · rw [Function.update_of_ne (fun e => h (Fin.castSucc_injective m e)),
      Function.update_of_ne h]
    rfl

theorem snocWord_update (w : Word m) (c : Bool) (j : Fin m) (b : Bool) :
    snocWord c (Function.update w j b) = Function.update (snocWord c w) j.castSucc b := by
  funext i
  induction i using Fin.lastCases with
  | last =>
      rw [Function.update_of_ne (Fin.castSucc_ne_last j).symm]
      simp
  | cast i =>
      by_cases h : i = j
      · subst h; simp [snocWord]
      · rw [Function.update_of_ne (fun e => h (Fin.castSucc_injective m e))]
        simp [snocWord, Function.update_of_ne h]

theorem lowerZero_snocWord (c : Bool) (w : Word m) (j : Fin m) :
    lowerZero j.castSucc (snocWord c w) ↔ lowerZero j w := by
  unfold lowerZero
  constructor
  · intro h i hi
    have := h i.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hi)
    simpa [snocWord] using this
  · intro h i hi
    induction i using Fin.lastCases with
    | last => exact absurd hi (not_lt.mpr (Fin.castSucc_lt_last j).le)
    | cast i =>
        have := h i (Fin.castSucc_lt_castSucc_iff.mp hi)
        simpa [snocWord] using this

@[simp] theorem snocWord_castSucc (c : Bool) (w : Word m) (j : Fin m) :
    snocWord c w j.castSucc = w j := by simp [snocWord]

theorem lo_bitRot (j : Fin m) (R : Matrix Bool Bool ℂ) (φ : Word (m + 1) → P) :
    lo (bitRot j.castSucc R φ) = bitRot j R (lo φ) := by
  funext w
  simp only [lo, bitRot, lowerZero_snocWord, snocWord_castSucc, snocWord_update]

theorem hi_bitRot (j : Fin m) (R : Matrix Bool Bool ℂ) (φ : Word (m + 1) → P) :
    hi (bitRot j.castSucc R φ) = bitRot j R (hi φ) := by
  funext w
  simp only [hi, bitRot, lowerZero_snocWord, snocWord_castSucc, snocWord_update]

/-- Mixing two amplitudes by a one-qubit matrix. -/
def mix2 (R : Matrix Bool Bool ℂ) (a b : P) : P × P :=
  (R false false • a + R false true • b, R true false • a + R true true • b)

theorem lowerZero_last (w : Word (m + 1)) :
    lowerZero (Fin.last m) w ↔ tailWord w = zeroW m := by
  unfold lowerZero
  constructor
  · intro h; funext i; exact h i.castSucc (Fin.castSucc_lt_last i)
  · intro h i hi
    induction i using Fin.lastCases with
    | last => exact absurd hi (lt_irrefl _)
    | cast i => exact congrFun h i

/-- The top-bit rotation conditioned on all lower bits only mixes the two roots. -/
theorem bitRot_last (R : Matrix Bool Bool ℂ) (φ : Word (m + 1) → P) :
    bitRot (Fin.last m) R φ =
      joinW (setRoot (lo φ) (mix2 R (lo φ (zeroW m)) (hi φ (zeroW m))).1)
        (setRoot (hi φ) (mix2 R (lo φ (zeroW m)) (hi φ (zeroW m))).2) := by
  funext w
  have hw := snocWord_tailWord w
  unfold bitRot joinW
  by_cases hz : tailWord w = zeroW m
  · rw [if_pos ((lowerZero_last w).mpr hz)]
    have h0 : ∀ b, Function.update w (Fin.last m) b = snocWord b (zeroW m) := by
      intro b
      rw [← hw, hz]
      funext i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => rw [Function.update_of_ne (Fin.castSucc_ne_last i)]; simp [snocWord]
    simp only [h0, Fintype.sum_bool, hz, setRoot_zero, mix2]
    cases hb : w (Fin.last m)
    · simp [lo, hi, add_comm]
    · simp [lo, hi, add_comm]
  · rw [if_neg (fun h => hz ((lowerZero_last w).mp h))]
    cases hb : w (Fin.last m)
    · simp only [Bool.false_eq_true, ↓reduceIte, setRoot_ne _ _ _ hz, lo]
      rw [hb] at hw; rw [hw]
    · simp only [↓reduceIte, setRoot_ne _ _ _ hz, hi]
      rw [hb] at hw; rw [hw]

/-- Rotations of bits `n-1, …, 0` (bit `n-1` first). -/
def descendR (R : ℕ → Matrix Bool Bool ℂ) {m : ℕ} :
    (n : ℕ) → n ≤ m → (Word m → P) → (Word m → P)
  | 0, _ => id
  | n + 1, h => descendR R n (by omega) ∘ bitRot ⟨n, by omega⟩ (R n)

/-- Rotations of bits `0, …, n-1` (bit `0` first). -/
def ascendR (R : ℕ → Matrix Bool Bool ℂ) {m : ℕ} :
    (n : ℕ) → n ≤ m → (Word m → P) → (Word m → P)
  | 0, _ => id
  | n + 1, h => bitRot ⟨n, by omega⟩ (R n) ∘ ascendR R n (by omega)

theorem lo_descendR (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n ≤ m)
    (φ : Word (m + 1) → P) :
    lo (descendR R n (by omega) φ) = descendR R n hn (lo φ) := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
      simp only [descendR, Function.comp_apply]
      rw [ih (by omega)]
      congr 1
      exact lo_bitRot (P := P) (⟨n, by omega⟩ : Fin m) (R n) φ

theorem hi_descendR (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n ≤ m)
    (φ : Word (m + 1) → P) :
    hi (descendR R n (by omega) φ) = descendR R n hn (hi φ) := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
      simp only [descendR, Function.comp_apply]
      rw [ih (by omega)]
      congr 1
      exact hi_bitRot (P := P) (⟨n, by omega⟩ : Fin m) (R n) φ

theorem lo_ascendR (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n ≤ m)
    (φ : Word (m + 1) → P) :
    lo (ascendR R n (by omega) φ) = ascendR R n hn (lo φ) := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
      simp only [ascendR, Function.comp_apply]
      rw [← ih (by omega)]
      exact lo_bitRot (P := P) (⟨n, by omega⟩ : Fin m) (R n) _

theorem hi_ascendR (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) (hn : n ≤ m)
    (φ : Word (m + 1) → P) :
    hi (ascendR R n (by omega) φ) = ascendR R n hn (hi φ) := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
      simp only [ascendR, Function.comp_apply]
      rw [← ih (by omega)]
      exact hi_bitRot (P := P) (⟨n, by omega⟩ : Fin m) (R n) _

/-- The root-frame matrices (rows: new bit, columns: old bit). -/
def inMat (z : ℝ) : Matrix Bool Bool ℂ := fun r c =>
  match r, c with
  | false, false => kk z * z | false, true => -kk z
  | true, false => kk z | true, true => kk z * z

def unMat (z : ℝ) : Matrix Bool Bool ℂ := fun r c =>
  match r, c with
  | false, false => kk z * z | false, true => kk z
  | true, false => -kk z | true, true => kk z * z

def outMat (z : ℝ) : Matrix Bool Bool ℂ := fun r c =>
  match r, c with
  | false, false => kk z | false, true => -(kk z * z)
  | true, false => kk z * z | true, true => kk z

theorem mix2_inMat (z : ℝ) (a b : P) : mix2 (inMat z) a b = inMix z a b := by
  simp only [mix2, inMat, inMix, Prod.mk.injEq]
  constructor <;> module

theorem mix2_unMat (z : ℝ) (a b : P) : mix2 (unMat z) a b = inUnmix z a b := by
  simp only [mix2, unMat, inUnmix, Prod.mk.injEq]
  constructor <;> module

theorem mix2_outMat (z : ℝ) (a b : P) : mix2 (outMat z) a b = outMix z a b := by
  simp only [mix2, outMat, outMix, Prod.mk.injEq]
  constructor <;> module

theorem joinW_eq_descend (R : ℕ → Matrix Bool Bool ℂ) (ψ : Word (m + 1) → P) :
    joinW (descendR R m le_rfl (lo ψ)) (descendR R m le_rfl (hi ψ)) =
      descendR R m (Nat.le_succ m) ψ := by
  rw [← lo_descendR R m le_rfl ψ, ← hi_descendR R m le_rfl ψ, joinW_lo_hi]

theorem inFrame_eq (c : ℝ) (m : ℕ) :
    inFrame (P := P) c m = descendR (fun j => inMat (centralCosine c j)) m le_rfl := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext φ
      simp only [inFrame, descendR, Function.comp_apply]
      rw [ih]
      have hb := bitRot_last (P := P) (inMat (centralCosine c m)) φ
      rw [mix2_inMat] at hb
      have e := joinW_eq_descend (fun j => inMat (centralCosine c j))
        (bitRot (Fin.last m) (inMat (centralCosine c m)) φ)
      rw [hb, lo_joinW, hi_joinW] at e
      rw [e, ← hb]
      rfl

theorem outFrame_eq (c : ℝ) (m : ℕ) :
    outFrame (P := P) c m = descendR (fun j => outMat (centralCosine c j)) m le_rfl := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext φ
      simp only [outFrame, descendR, Function.comp_apply]
      rw [ih]
      have hb := bitRot_last (P := P) (outMat (centralCosine c m)) φ
      rw [mix2_outMat] at hb
      have e := joinW_eq_descend (fun j => outMat (centralCosine c j))
        (bitRot (Fin.last m) (outMat (centralCosine c m)) φ)
      rw [hb, lo_joinW, hi_joinW] at e
      rw [e, ← hb]
      rfl

theorem inFrameInv_eq (c : ℝ) (m : ℕ) :
    inFrameInv (P := P) c m = ascendR (fun j => unMat (centralCosine c j)) m le_rfl := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext φ
      simp only [inFrameInv, ascendR, Function.comp_apply]
      rw [ih]
      set ψ := ascendR (fun j => unMat (centralCosine c j)) m (Nat.le_succ m) φ with hψ
      have hl : lo ψ = ascendR (fun j => unMat (centralCosine c j)) m le_rfl (lo φ) :=
        lo_ascendR _ m le_rfl φ
      have hh : hi ψ = ascendR (fun j => unMat (centralCosine c j)) m le_rfl (hi φ) :=
        hi_ascendR _ m le_rfl φ
      change _ = bitRot (Fin.last m) (unMat (centralCosine c m)) ψ
      rw [bitRot_last, mix2_unMat, hl, hh]

/-! ### The sequential form of the chronological network -/

open GatePointerEncoding (wordValue bitValue)

/-- Public amplitude after `k` slots, with private inputs `ψ` in slot order. -/
def seqPub (c σ : ℝ) (p : P) (ψ : ℕ → P) : ℕ → P
  | 0 => p
  | k + 1 => (c : ℂ) • seqPub c σ p ψ k - (σ : ℂ) • ψ k

theorem seqPub_add (c σ : ℝ) (p : P) (ψ : ℕ → P) (a b : ℕ) :
    seqPub c σ p ψ (a + b) = seqPub c σ (seqPub c σ p ψ a) (fun k => ψ (a + k)) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 from rfl, seqPub, seqPub, ih]

theorem seqPub_congr (c σ : ℝ) (p : P) (ψ ψ' : ℕ → P) (n : ℕ)
    (h : ∀ k < n, ψ k = ψ' k) : seqPub c σ p ψ n = seqPub c σ p ψ' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [seqPub]
      rw [ih (fun k hk => h k (by omega)), h n (by omega)]

theorem wordValue_snocWord (b : Bool) (w : Word m) :
    wordValue (snocWord b w) = wordValue w + bitValue b * 2 ^ m := by
  unfold wordValue
  rw [Fin.sum_univ_castSucc]
  simp [snocWord]

theorem wordValue_zero (w : Word 0) : wordValue w = 0 := by simp [wordValue]

/-- The chronological network is the sequential slot-by-slot rotation. -/
theorem chron_closed (c σ : ℝ) (m : ℕ) (p : P) (φ : Word m → P) (ψ : ℕ → P)
    (hψ : ∀ w, ψ (wordValue w) = φ w) :
    chron c σ m (p, φ) = (seqPub c σ p ψ (2 ^ m),
      fun w => (σ : ℂ) • seqPub c σ p ψ (wordValue w) + (c : ℂ) • φ w) := by
  induction m generalizing p ψ with
  | zero =>
      have h0 : ψ 0 = φ (zeroW 0) := by
        have := hψ (zeroW 0); rwa [wordValue_zero] at this
      simp only [chron, rot, pow_zero, seqPub, h0]
      refine Prod.ext rfl ?_
      funext w
      have : w = zeroW 0 := funext (fun j => Fin.elim0 j)
      subst this
      simp [wordValue_zero, seqPub]
  | succ m ih =>
      have hlo : ∀ w, ψ (wordValue w) = lo φ w := by
        intro w; rw [lo, ← hψ, wordValue_snocWord]; simp [bitValue]
      have hhi : ∀ w, (fun k => ψ (2 ^ m + k)) (wordValue w) = hi φ w := by
        intro w; simp only [hi, ← hψ, wordValue_snocWord]; simp [bitValue, add_comm]
      simp only [chron]
      rw [ih p (lo φ) ψ hlo, ih _ (hi φ) (fun k => ψ (2 ^ m + k)) hhi]
      have hsplit : ∀ k, seqPub c σ p ψ (2 ^ m + k) =
          seqPub c σ (seqPub c σ p ψ (2 ^ m)) (fun k => ψ (2 ^ m + k)) k :=
        fun k => seqPub_add c σ p ψ (2 ^ m) k
      refine Prod.ext ?_ ?_
      · simp only
        rw [← hsplit, pow_succ, mul_two]
      · funext w
        have hw := snocWord_tailWord w
        simp only [joinW]
        cases hb : w (Fin.last m)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hb] at hw
          conv_rhs => rw [← hw]
          rw [wordValue_snocWord]
          simp [bitValue, lo, hw]
        · simp only [↓reduceIte]
          rw [hb] at hw
          conv_rhs => rw [← hw]
          rw [wordValue_snocWord, ← hsplit]
          simp only [bitValue, if_true, one_mul, hi]
          rw [add_comm (wordValue (tailWord w))]

end

end SparseHamiltonian.GateCircuit.Dyadic
