import GateEfficientBinaryNodes.SelectIntegrated

/-!
# The source preparation for constant forcing

The proof of Theorem `ode:thm:gates` (equation `ode:eq:gate-constant-source`): "For constant
forcing, take `m` to be a power of two … and let `w_i = T/m`. Then `B_m = B`, the label circuit
consists of one rotation between the initial and forcing sectors and `log₂ m` Hadamard gates,
and the forcing state is loaded by the same controlled circuit on every forcing label.
Consequently `G_src(ν) = G_{x₀}(cν) + G_b(cν) + poly(b_data, log(m+1), log(1/ν))`."

The released constant-coefficient solver already prepares its source register this way
(`GateODE.Params.srcPrep`: one rotation and uncontrolled Hadamard gates on `2^k` left-endpoint
nodes; in its source format every label `(false, w)` of the initial sector has duration `T`).
The released time-dependent solvers take the weight preparation `Wp` and the loading `J` of the
source labels `(ini, w)` (`w` an `m`-bit node word, `2^m` nodes; only `(false, 0)` carries the
initial state) as hypotheses, with circuits `wpC`, `loadC` approximating them. For constant
forcing `b` this module constructs both for the time-dependent source format:

* `wpGates m r₀ r_b T`: the rotation `rotC √(r₀/B) √(T r_b/B)` on the sector wire `0`, then
  the Hadamard gate on each node wire `1, …, m`, controlled by the sector wire
  (`B = r₀ + T r_b`, `srcB`); `m + 1` gates (`length_wpGates`), valid (`wpGates_ok`).
  `WpConst` is its matrix: unitary (`WpConst_unitary`), with first column
  `√(T r_b/B) 2^(-m/2)` on the forcing labels, `√(r₀/B)` on the initial label `(false, 0)` and
  `0` on the other labels (`WpConst_col`); for `r₀ = ‖x₀‖`, `r_b = ‖b‖` and forcing samples
  equal to `b` on all `2^m` nodes these are the amplitudes `√(‖z_s‖/mass)` of the released
  weight promise (`WpConst_srcAmp`). The control on the sector wire keeps the labels
  `(false, w)`, `w ≠ 0`, empty, as the released source format requires.
* `wpConst`: the gates on the source-label wires of the weight-preparation register;
  `nrun_wpConst`: it implements `liftB (matOp WpConst)` exactly.
* `loadConst srcC`: the two supplied controlled loading circuits `srcC false` (the initial
  state) and `srcC true` (the forcing state), each controlled by the sector wire as in the
  constant-coefficient native solver (`GateNative.srcIdeal`), placed on the sector wire, the
  system and the scratch; `loadConst_approx`: within `ζ₀ + ζ₁` of the selected loading
  `loadIdeal (JlC J)`, `JlC J (ini, w) = J ini`, the same circuit on every forcing label.
* Counts (`loadConst_counts`, `wpConst_counts`): `|loadC| + 2 |wpC| = G_{x₀} + G_b + 2 (m + 1)`
  elementary gates (the supplied loading circuits are counted by their gates, as `G_{x₀}`,
  `G_b` in the paper), and the calls of the two supplied circuits; the weight preparation makes
  no call.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryNodes

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE.Time (TParams)
open GatePointerEncoding (wordValue)
open scoped InnerProduct BigOperators

/-! ### Trees of controlled gates -/

section Tree

variable {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The gates `⟨cs s, ts s, U s⟩` for `s = k-1, …, 0`, top bit first. -/
def ctrlT (ts : Fin q → W) (cs : Fin q → List (W × Bool)) (U : Fin q → Matrix Bool Bool ℂ) :
    ℕ → List (Gate W)
  | 0 => []
  | k + 1 => (if h : k < q then [⟨cs ⟨k, h⟩, ts ⟨k, h⟩, U ⟨k, h⟩⟩] else []) ++ ctrlT ts cs U k

/-- The controlled tree gates run as the tree operator with the controlled matrices. -/
theorem gRun_ctrlT (ts : Fin q → W) (cs : Fin q → List (W × Bool))
    (U : Fin q → Matrix Bool Bool ℂ) (k : ℕ) (hk : k ≤ q) :
    gRun (Q := Q) (ctrlT ts cs U k) =
      treeFrom ts (fun s x => if ctrlOK (cs s) x then U s else 1) k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ctrlT, dif_pos (show k < q by omega), gRun_append, ih (by omega), treeFrom,
        gRun_singleton]
      rfl

omit [Fintype W] [DecidableEq W] in
theorem length_ctrlT (ts : Fin q → W) (cs : Fin q → List (W × Bool))
    (U : Fin q → Matrix Bool Bool ℂ) (k : ℕ) (hk : k ≤ q) : (ctrlT ts cs U k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [ctrlT, dif_pos (show k < q by omega), List.length_append, ih (by omega)]
      simp only [List.length_singleton]
      omega

omit [Fintype W] [DecidableEq W] in
theorem mem_ctrlT (ts : Fin q → W) (cs : Fin q → List (W × Bool))
    (U : Fin q → Matrix Bool Bool ℂ) (k : ℕ) (g : Gate W) (hg : g ∈ ctrlT ts cs U k) :
    ∃ s : Fin q, g = ⟨cs s, ts s, U s⟩ := by
  induction k with
  | zero => simp [ctrlT] at hg
  | succ k ih =>
      rw [ctrlT, List.mem_append] at hg
      rcases hg with hg | hg
      · split_ifs at hg with h
        · rw [List.mem_singleton] at hg
          exact ⟨⟨k, h⟩, hg⟩
        · simp at hg
      · exact ih hg

end Tree

/-! ### The weight-preparation gates -/

section Weights

/-- The source mass `B = r₀ + T r_b` of constant forcing. -/
def srcB (r0 rb T : ℝ) : ℝ := r0 + T * rb

/-- The tree wires: the sector wire `0` is the top bit (rotated first), the node wire `i + 1` is
bit `i`. -/
abbrev tsW (m : ℕ) : Fin (m + 1) → Fin (m + 1) := finRotate (m + 1)

/-- The controls: none for the rotation, the sector wire for the Hadamard gates. -/
def csW (m : ℕ) : Fin (m + 1) → List (Fin (m + 1) × Bool) :=
  Fin.lastCases [] (fun _ => [((0 : Fin (m + 1)), true)])

/-- The matrices: the sector rotation, then Hadamard gates. -/
def UW (m : ℕ) (c s : ℝ) : Fin (m + 1) → Matrix Bool Bool ℂ :=
  Fin.lastCases (rotC c s) (fun _ => hadC)

/-- **The weight-preparation gates for constant forcing**: the rotation
`rotC √(r₀/B) √(T r_b/B)` on the sector wire `0`, then the Hadamard gates on the node wires
`m, …, 1`, each controlled by the sector wire. -/
def wpGates (m : ℕ) (r0 rb T : ℝ) : List (Gate (Fin (m + 1))) :=
  ctrlT (tsW m) (csW m) (UW m (Real.sqrt (r0 / srcB r0 rb T)) (Real.sqrt (T * rb / srcB r0 rb T)))
    (m + 1)

theorem length_wpGates (m : ℕ) (r0 rb T : ℝ) : (wpGates m r0 rb T).length = m + 1 :=
  length_ctrlT _ _ _ _ le_rfl

theorem tsW_last (m : ℕ) : tsW m (Fin.last m) = 0 := finRotate_last

theorem tsW_castSucc (m : ℕ) (i : Fin m) : tsW m i.castSucc = i.succ := by
  rw [tsW, finRotate_apply, Fin.coeSucc_eq_succ]

theorem tsW_ne_zero (m : ℕ) (i : Fin m) : tsW m i.castSucc ≠ 0 := by
  rw [tsW_castSucc]
  exact Fin.succ_ne_zero i

theorem sq_sqrt_srcB (r0 rb T : ℝ) (h0 : 0 ≤ r0) (hb : 0 ≤ T * rb) (hB : 0 < srcB r0 rb T) :
    Real.sqrt (r0 / srcB r0 rb T) ^ 2 + Real.sqrt (T * rb / srcB r0 rb T) ^ 2 = 1 := by
  rw [Real.sq_sqrt (div_nonneg h0 hB.le), Real.sq_sqrt (div_nonneg hb hB.le), ← add_div]
  exact div_self hB.ne'

/-- **The weight-preparation gates are valid**: at most one control, off the target, and unitary
matrices. -/
theorem wpGates_ok (m : ℕ) (r0 rb T : ℝ) (h0 : 0 ≤ r0) (hb : 0 ≤ T * rb)
    (hB : 0 < srcB r0 rb T) : ∀ g ∈ wpGates m r0 rb T, GateOK 3 g := by
  intro g hg
  obtain ⟨s, rfl⟩ := mem_ctrlT _ _ _ _ g hg
  refine Fin.lastCases ?_ (fun i => ?_) s
  · refine ⟨by simp [csW], by simp [csW], ?_⟩
    simp only [UW, Fin.lastCases_last]
    exact rotC_unitary _ _ (sq_sqrt_srcB r0 rb T h0 hb hB)
  · refine ⟨by simp [csW], ?_, ?_⟩
    · intro c hc
      simp only [csW, Fin.lastCases_castSucc, List.mem_singleton] at hc
      subst hc
      exact (tsW_ne_zero m i).symm
    · simp only [UW, Fin.lastCases_castSucc]
      exact hadC_unitary

end Weights

/-! ### The column of the weight preparation -/

section Column

/-- The tree matrices of the weight preparation. -/
def MxW (m : ℕ) (c s : ℝ) (t : Fin (m + 1)) (x : Cfg (Fin (m + 1))) : Matrix Bool Bool ℂ :=
  if ctrlOK (csW m t) x then UW m c s t else 1

theorem MxW_last (m : ℕ) (c s : ℝ) (x : Cfg (Fin (m + 1))) :
    MxW m c s (Fin.last m) x = rotC c s := by
  simp [MxW, csW, UW, ctrlOK]

theorem MxW_castSucc (m : ℕ) (c s : ℝ) (i : Fin m) (x : Cfg (Fin (m + 1))) :
    MxW m c s i.castSucc x = if x 0 then hadC else 1 := by
  rcases Bool.eq_false_or_eq_true (x 0) with h | h <;>
    simp [MxW, csW, UW, Fin.lastCases_castSucc, ctrlOK, h]

/-- Bit `t` of the tree reads only the sector wire, which is the top bit. -/
theorem MxW_update (m : ℕ) (c s : ℝ) (t : Fin (m + 1)) (y : Cfg (Fin (m + 1))) (t' : Fin (m + 1))
    (ht : t'.val ≤ t.val) (b : Bool) :
    MxW m c s t (Function.update y (tsW m t') b) = MxW m c s t y := by
  induction t using Fin.lastCases with
  | last => rw [MxW_last, MxW_last]
  | cast i =>
    rw [MxW_castSucc, MxW_castSucc]
    have hne : tsW m t' ≠ 0 := by
      have hlt : t'.val < m := lt_of_le_of_lt ht (by simp)
      have e : t' = (⟨t'.val, hlt⟩ : Fin m).castSucc := Fin.ext rfl
      rw [e]
      exact tsW_ne_zero m _
    rw [Function.update_of_ne (Ne.symm hne)]

theorem rotC_col (c s : ℝ) (b : Bool) : rotC c s b false = if b then (s : ℂ) else (c : ℂ) := by
  cases b <;> rfl

theorem hadC_col (b : Bool) : hadC b false = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) := by
  cases b <;> rfl

/-- The tree matrices of a basis configuration, multiplied along the tree bits. -/
theorem prod_MxW (m : ℕ) (c s : ℝ) (y : Cfg (Fin (m + 1))) :
    ∏ t : Fin (m + 1), MxW m c s t y (y (tsW m t)) false =
      if y 0 then (s : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ m
      else if ∀ i : Fin m, y i.succ = false then (c : ℂ) else 0 := by
  rw [Fin.prod_univ_castSucc, MxW_last, tsW_last, rotC_col]
  simp only [MxW_castSucc, tsW_castSucc]
  rcases Bool.eq_false_or_eq_true (y 0) with h0 | h0
  · simp only [h0, if_true, hadC_col, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  · simp only [h0, Bool.false_eq_true, if_false]
    by_cases hall : ∀ i : Fin m, y i.succ = false
    · rw [if_pos hall]
      have : ∏ i : Fin m, (1 : Matrix Bool Bool ℂ) (y i.succ) false = 1 := by
        apply Finset.prod_eq_one
        intro i _
        rw [hall i]
        rfl
      rw [this, one_mul]
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      have hi' : y i.succ = true := by simpa using hi
      have : ∏ i : Fin m, (1 : Matrix Bool Bool ℂ) (y i.succ) false = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        rw [hi']
        rfl
      rw [this, zero_mul]

/-- **The weight preparation on the all-zero configuration**: the amplitude of the label
configuration `y` is `s 2^(-m/2)` on the forcing sector, `c` on the initial label and `0`
elsewhere. -/
theorem gRun_wp_zero (m : ℕ) (c s : ℝ) (y : Cfg (Fin (m + 1))) :
    (gRun (Q := ℂ) (ctrlT (tsW m) (csW m) (UW m c s) (m + 1)) (bas (fun _ => false) 1)) y =
      if y 0 then (s : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) ^ m
      else if ∀ i : Fin m, y i.succ = false then (c : ℂ) else 0 := by
  have hinj : Function.Injective (tsW m) := (finRotate (m + 1)).injective
  have hM : (fun t x => if ctrlOK (csW m t) x then UW m c s t else 1) = MxW m c s := by
    funext t x
    rfl
  rw [gRun_ctrlT (tsW m) (csW m) (UW m c s) (m + 1) le_rfl, hM,
    treeFrom_bas (tsW m) hinj (MxW m c s) (fun t y' t' ht b => MxW_update m c s t
      y' t' ht b) (m + 1) le_rfl (fun _ => false) (fun _ _ => rfl) 1]
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply]
  have hset : ∀ w : Fin (m + 1) → Bool, ∀ t : Fin (m + 1),
      setLow (tsW m) (m + 1) le_rfl (fun _ => false) w (tsW m t) = w t := by
    intro w t
    have h := setLow_apply_low (tsW m) hinj (m + 1) le_rfl (fun _ => false) w t
    exact h
  have hset' : ∀ w : Fin (m + 1) → Bool, setLow (tsW m) (m + 1) le_rfl (fun _ => false) w =
      fun z => w ((finRotate (m + 1)).symm z) := by
    intro w
    funext z
    have h := hset w ((finRotate (m + 1)).symm z)
    rwa [show tsW m ((finRotate (m + 1)).symm z) = z from (finRotate (m + 1)).apply_symm_apply z]
      at h
  rw [Finset.sum_eq_single (fun t => y (tsW m t))]
  · have hy : setLow (tsW m) (m + 1) le_rfl (fun _ => false) (fun t => y (tsW m t)) = y := by
      rw [hset']
      funext z
      simp
    rw [WithLp.ofLp_smul, Pi.smul_apply, hy, bas_apply, if_pos rfl, smul_eq_mul, mul_one]
    rw [← prod_MxW m c s y]
  · intro w _ hw
    rw [WithLp.ofLp_smul, Pi.smul_apply, bas_apply, if_neg, smul_zero]
    intro h
    apply hw
    funext t
    rw [h, hset]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Column

/-! ### The matrix of the weight preparation -/

section Matrix

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- **The matrix of an operator** on a register with scalar payload. -/
def matOf (O : Reg A ℂ →L[ℂ] Reg A ℂ) : Matrix (Cfg A) (Cfg A) ℂ := fun b c => O (bas c 1) b

/-- Every operator on a register with scalar payload is the operator of its matrix. -/
theorem matOp_matOf (O : Reg A ℂ →L[ℂ] Reg A ℂ) : matOp (Q := ℂ) (matOf O) = O := by
  apply ext_bas_clm
  intro c z
  apply PiLp.ext
  intro b
  rw [matOp_apply, Finset.sum_eq_single c]
  · have hz : bas c z = z • bas c (1 : ℂ) := by
      rw [← bas_smul, smul_eq_mul, mul_one]
    rw [bas_apply, if_pos rfl, hz, map_smul, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
    change O (bas c 1) b * z = z * O (bas c 1) b
    ring
  · intro c' _ hc'
    rw [bas_apply, if_neg hc', smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The operator of a matrix determines the matrix. -/
theorem matOp_injective {M N : Matrix (Cfg A) (Cfg A) ℂ}
    (h : matOp (Q := ℂ) M = matOp (Q := ℂ) N) : M = N := by
  funext b c
  have := congrArg (fun O => (O (bas c (1 : ℂ))) b) h
  simp only [matOp_apply, bas_apply] at this
  rw [Finset.sum_eq_single c, Finset.sum_eq_single c] at this
  · simpa using this
  · intro c' _ hc'
    simp [hc']
  · intro h'
    exact absurd (Finset.mem_univ _) h'
  · intro c' _ hc'
    simp [hc']
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-- **The matrix of a unitary operator is unitary.** -/
theorem matOf_unitary (O : Reg A ℂ →L[ℂ] Reg A ℂ) (hO : IsUnitary O) :
    (matOf O).conjTranspose * matOf O = 1 ∧ matOf O * (matOf O).conjTranspose = 1 := by
  have hl : (O†) ∘L O = 1 := by
    have h := hO.1
    rwa [star_eq_adjoint, mul_def] at h
  have hr : O ∘L (O†) = 1 := by
    have h := hO.2
    rwa [star_eq_adjoint, mul_def] at h
  constructor
  · apply matOp_injective
    rw [← matOp_mul, ← matOp_adjoint, matOp_matOf, hl, matOp_one]
  · apply matOp_injective
    rw [← matOp_mul, ← matOp_adjoint, matOp_matOf, hr, matOp_one]

end Matrix

section WpMatrix

/-- **The matrix of the weight preparation** for constant forcing. -/
def WpConst (m : ℕ) (r0 rb T : ℝ) : Matrix (Cfg (Fin (m + 1))) (Cfg (Fin (m + 1))) ℂ :=
  matOf (gRun (Q := ℂ) (wpGates m r0 rb T))

theorem matOp_WpConst (m : ℕ) (r0 rb T : ℝ) :
    matOp (Q := ℂ) (WpConst m r0 rb T) = gRun (Q := ℂ) (wpGates m r0 rb T) :=
  matOp_matOf _

/-- **The weight-preparation matrix is unitary.** -/
theorem WpConst_unitary (m : ℕ) (r0 rb T : ℝ) (h0 : 0 ≤ r0) (hb : 0 ≤ T * rb)
    (hB : 0 < srcB r0 rb T) :
    (WpConst m r0 rb T).conjTranspose * WpConst m r0 rb T = 1 ∧
      WpConst m r0 rb T * (WpConst m r0 rb T).conjTranspose = 1 :=
  matOf_unitary _ (gRun_isUnitary _ (fun g hg => (wpGates_ok m r0 rb T h0 hb hB g hg).2.2))

/-- **The first column of the weight preparation**: `√(T r_b/B) 2^(-m/2)` on every forcing
label, `√(r₀/B)` on the initial label `(false, 0)` and `0` on the labels `(false, w)`,
`w ≠ 0`. -/
theorem WpConst_col (m : ℕ) (r0 rb T : ℝ) (y : Cfg (Fin (m + 1))) :
    WpConst m r0 rb T y (fun _ => false) =
      if y 0 then ((Real.sqrt (T * rb / srcB r0 rb T) * ((Real.sqrt 2)⁻¹) ^ m : ℝ) : ℂ)
      else if Fin.tail y = (fun _ => false) then ((Real.sqrt (r0 / srcB r0 rb T) : ℝ) : ℂ)
      else 0 := by
  unfold WpConst matOf wpGates
  rw [gRun_wp_zero]
  have htail : (∀ i : Fin m, y i.succ = false) ↔ Fin.tail y = (fun _ => false) := by
    constructor
    · intro h
      funext i
      exact h i
    · intro h i
      exact congrFun h i
  split_ifs with h1 h2 h3 h3 <;> push_cast <;> first | rfl | (exfalso; tauto)

end WpMatrix

/-! ### The weight-preparation circuit -/

section WpCircuit

variable {Zs Y J : Type*} [Fintype Zs] [DecidableEq Zs] [Fintype Y] [DecidableEq Y]

/-- **The weight-preparation circuit for constant forcing** on the source-label wires and the
scratch of the weight-preparation register: the gates `wpGates` on the source-label wires. -/
def wpConst (m : ℕ) (Zs Y J : Type*) (r0 rb T : ℝ) : List (NInstr (Fin (m + 1) ⊕ Zs) Y J) :=
  nGatesOf ((wpGates m r0 rb T).map (GateODE.Gate.map (Function.Embedding.inl :
    Fin (m + 1) ↪ Fin (m + 1) ⊕ Zs)))

/-- **The weight-preparation circuit implements `Wp` exactly.** -/
theorem nrun_wpConst (m : ℕ) (r0 rb T : ℝ) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) :
    nrun prim (wpConst m Zs Y J r0 rb T) = liftB (X := Zs) (matOp (WpConst m r0 rb T)) := by
  rw [wpConst, nrun_nGatesOf, gRun_map_gates, matOp_WpConst]
  rfl

/-- The weight-preparation circuit within `ζs ≥ 0` of `Wp` (exactly). -/
theorem wpConst_approx (m : ℕ) (r0 rb T : ℝ) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) {ζs : ℝ}
    (hζs : 0 ≤ ζs) :
    ApproxOn CleanX (nrun prim (wpConst m Zs Y J r0 rb T))
      (liftB (X := Zs) (matOp (WpConst m r0 rb T))) ζs := by
  rw [nrun_wpConst]
  intro ψ _
  rw [sub_self, norm_zero]
  exact mul_nonneg hζs (norm_nonneg _)

omit [Fintype Zs] [DecidableEq Zs] [Fintype Y] [DecidableEq Y] in
/-- The weight-preparation circuit is valid. -/
theorem wpConst_valid (m : ℕ) (r0 rb T : ℝ) (h0 : 0 ≤ r0) (hb : 0 ≤ T * rb)
    (hB : 0 < srcB r0 rb T) : ∀ i ∈ wpConst m Zs Y J r0 rb T, i.Valid := by
  apply valid_nGatesOf
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have h := wpGates_ok m r0 rb T h0 hb hB g0 hg0
  exact NInstr.valid_map (V := Fin (m + 1)) (Y := Y) (J := J)
    (Function.Embedding.inl : Fin (m + 1) ↪ Fin (m + 1) ⊕ Zs) (.gate g0) h

omit [Fintype Zs] [DecidableEq Zs] [Fintype Y] [DecidableEq Y] in
/-- **The counts of the weight preparation**: `m + 1` elementary gates and no primitive call. -/
theorem wpConst_counts (m : ℕ) (r0 rb T : ℝ) (c : J → Bool) :
    nGatesN (wpConst m Zs Y J r0 rb T) = m + 1 ∧ nCallsN c (wpConst m Zs Y J r0 rb T) = 0 := by
  refine ⟨?_, nCallsN_nGatesOf _ _⟩
  rw [wpConst, nGatesN_nGatesOf, List.length_map, length_wpGates]

end WpCircuit

/-! ### The weight promise of constant forcing -/

section Promise

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- `√(2^m) = (√2)^m`. -/
theorem sqrt_two_pow (m : ℕ) : Real.sqrt (2 ^ m) = Real.sqrt 2 ^ m := by
  have h : (2 : ℝ) ^ m = (Real.sqrt 2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]

/-- **The source vectors of constant forcing**: if every forcing sample on the `2^m` nodes is
`b`, the forcing labels carry `(T/2^m) b`, the initial label `x₀`, the other labels `0`. -/
theorem zsrc_const (p : TParams) (x0 : P) (bs : ℕ → P) (bv : P) (hbs : ∀ q < p.M, bs q = bv)
    (s : Bool × (Fin p.m → Bool)) :
    p.zsrc x0 bs s = if s.1 then ((p.T / p.M : ℝ) : ℂ) • bv
      else if s.2 = (fun _ => false) then x0 else 0 := by
  unfold GateODE.Time.TParams.zsrc
  rw [hbs _ (GatePointerEncoding.wordValue_lt_pow s.2)]

/-- **The source mass of constant forcing** is `‖x₀‖ + T ‖b‖`. -/
theorem mass_const (p : TParams) (hT : 0 ≤ p.T) (x0 : P) (bs : ℕ → P) (bv : P)
    (hbs : ∀ q < p.M, bs q = bv) : p.mass x0 bs = srcB ‖x0‖ ‖bv‖ p.T := by
  rw [p.mass_eq hT, Finset.sum_congr rfl (fun q hq => by rw [hbs q (Finset.mem_range.mp hq)]),
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : ((p.M : ℕ) : ℝ) ≠ 0 := by exact_mod_cast p.M_pos.ne'
  unfold srcB
  field_simp

/-- **The weight amplitudes of constant forcing**. -/
theorem srcAmp_const (p : TParams) (hT : 0 ≤ p.T) (x0 : P) (bs : ℕ → P) (bv : P)
    (hbs : ∀ q < p.M, bs q = bv) (s : Bool × (Fin p.m → Bool)) :
    p.srcAmp x0 bs s =
      if s.1 then Real.sqrt (p.T * ‖bv‖ / srcB ‖x0‖ ‖bv‖ p.T) * ((Real.sqrt 2)⁻¹) ^ p.m
      else if s.2 = (fun _ => false) then Real.sqrt (‖x0‖ / srcB ‖x0‖ ‖bv‖ p.T) else 0 := by
  unfold GateODE.Time.TParams.srcAmp
  rw [zsrc_const p x0 bs bv hbs s, mass_const p hT x0 bs bv hbs]
  split_ifs with h1 h2
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hT (Nat.cast_nonneg _))]
    have hM : ((p.M : ℕ) : ℝ) = 2 ^ p.m := by push_cast; rfl
    rw [hM, inv_pow, ← sqrt_two_pow, ← div_eq_mul_inv,
      ← Real.sqrt_div' _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
    congr 1
    ring
  · rfl
  · rw [norm_zero, zero_div, Real.sqrt_zero]

/-- **The weight preparation of constant forcing satisfies the weight promise**: its first
column carries the amplitudes `√(‖z_s‖ / mass)` of the released source format, for the initial
vector `x₀` (`r₀ = ‖x₀‖`) and forcing samples equal to `b` (`r_b = ‖b‖`) on all `2^m` nodes. -/
theorem WpConst_srcAmp (p : TParams) (hT : 0 ≤ p.T) (x0 : P) (bs : ℕ → P) (bv : P)
    (hbs : ∀ q < p.M, bs q = bv) (y : Cfg (Fin (p.m + 1))) :
    WpConst p.m ‖x0‖ ‖bv‖ p.T y (fun _ => false) =
      ((p.srcAmp x0 bs (y 0, Fin.tail y) : ℝ) : ℂ) := by
  rw [WpConst_col, srcAmp_const p hT x0 bs bv hbs]
  split_ifs <;> rfl

end Promise

/-! ### The loading circuit -/

section Load

variable {S Zs Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Y] [DecidableEq Y]

/-- The placement of a controlled loading circuit: its control on the sector wire `0`. -/
def plCFun (m : ℕ) (S Zs : Type*) : (Unit ⊕ S) ⊕ Zs → (Fin (m + 1) ⊕ S) ⊕ Zs
  | .inl (.inl _) => .inl (.inl 0)
  | .inl (.inr s) => .inl (.inr s)
  | .inr z => .inr z

theorem plCFun_injective (m : ℕ) (S Zs : Type*) : Function.Injective (plCFun m S Zs) := by
  intro x y h
  rcases x with (u | s) | z <;> rcases y with (u' | s') | z' <;> simp_all [plCFun]

/-- The placement of a controlled loading circuit. -/
def plC (m : ℕ) (S Zs : Type*) : (Unit ⊕ S) ⊕ Zs ↪ (Fin (m + 1) ⊕ S) ⊕ Zs :=
  ⟨plCFun m S Zs, plCFun_injective m S Zs⟩

/-- **The loading circuit for constant forcing**: the supplied controlled loading circuits of
the initial state (`srcC false`, active on the sector `false`) and of the forcing state
(`srcC true`, active on the sector `true`), placed on the sector wire, the system and the
scratch. -/
def loadConst (m : ℕ) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    List (NInstr ((Fin (m + 1) ⊕ S) ⊕ Zs) Y J) :=
  (srcC false).map (NInstr.map (plC m S Zs)) ++ (srcC true).map (NInstr.map (plC m S Zs))

/-- The selected loading of constant forcing: the loading of the sector of the label (the same
on every forcing label). -/
def JlC (m : ℕ) (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) :
    Bool × (Fin m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ :=
  fun s => Jsrc s.1

/-- The ideal of a placed controlled loading circuit: `O` on the system when the sector wire
carries `c`. -/
def srcIdealL (m : ℕ) (c : Bool) (O : Reg S ℂ →L[ℂ] Reg S ℂ) :
    Reg (Fin (m + 1) ⊕ S) ℂ →L[ℂ] Reg (Fin (m + 1) ⊕ S) ℂ :=
  localOp (Sum.inr : S → Fin (m + 1) ⊕ S) Sum.inr_injective
    (fun y => if y (Sum.inl 0) = c then O else 1)

/-- The placed ideal of a controlled loading circuit. -/
theorem place_srcIdeal (m : ℕ) (c : Bool) (O : Reg S ℂ →L[ℂ] Reg S ℂ) :
    localOp (plC m S Zs) (plC m S Zs).injective (fun _ => liftB (X := Zs) (srcIdeal c O)) =
      liftB (X := Zs) (srcIdealL m c O) := by
  unfold liftB srcIdeal srcIdealL
  rw [GateODE.localOp_localOp' Sum.inl_injective Sum.inr_injective
      (fun s => (Sum.inl (Sum.inr s) : (Fin (m + 1) ⊕ S) ⊕ Zs))
      (fun _ _ h => Sum.inr_injective (Sum.inl_injective h)) (fun _ => rfl),
    GateODE.localOp_localOp (plC m S Zs).injective Sum.inl_injective,
    GateODE.localOp_localOp' ((plC m S Zs).injective.comp Sum.inl_injective) Sum.inr_injective
      (fun s => (Sum.inl (Sum.inr s) : (Fin (m + 1) ⊕ S) ⊕ Zs))
      (fun _ _ h => Sum.inr_injective (Sum.inl_injective h)) (fun _ => rfl)]
  apply localOp_congr
  intro z
  set z' := clearCfg (fun s => (Sum.inl (Sum.inr s) : (Fin (m + 1) ⊕ S) ⊕ Zs)) z
  have h1 : clearCfg (Sum.inr : S → Fin (m + 1) ⊕ S) (fun v => z' (Sum.inl v)) (Sum.inl 0) =
      z' (Sum.inl (Sum.inl 0)) :=
    clearCfg_apply_out _ _ _ (fun s h => by cases h)
  have h2 : clearCfg (Sum.inr : S → Unit ⊕ S) (fun t => z' (plC m S Zs (Sum.inl t)))
      (Sum.inl ()) = z' (Sum.inl (Sum.inl 0)) :=
    clearCfg_apply_out _ _ _ (fun s h => by cases h)
  simp only [Function.comp_apply, h1, h2]

/-- The two placed ideals compose to the selected loading of constant forcing. -/
theorem srcIdealL_comp (m : ℕ) (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) :
    srcIdealL m true (Jsrc true) ∘L srcIdealL m false (Jsrc false) = loadIdeal (JlC m Jsrc) := by
  unfold srcIdealL loadIdeal
  rw [localOp_comp]
  congr 1
  funext y
  simp only [JlC, srcLab]
  rcases Bool.eq_false_or_eq_true (y (Sum.inl 0)) with h | h <;> simp [h] <;> ext <;> rfl

theorem isUnitary_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {U : E →L[ℂ] E} (hU : IsUnitary U) (ψ : E) : ‖U ψ‖ ≤ ‖ψ‖ := by
  have h1 : (U†) ∘L U = 1 := by
    have := hU.1; rwa [star_eq_adjoint, mul_def] at this
  exact le_of_eq ((U.norm_map_iff_adjoint_comp_self).mpr h1 ψ)

/-- **The loading circuit of constant forcing approximates the selected loading** within the sum
of the accuracies of the two supplied circuits. -/
theorem loadConst_approx (m : ℕ) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
    (hprim : ∀ j, IsUnitary (prim j)) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ)
    (hJ : ∀ c, IsUnitary (Jsrc c)) (ζ₀ ζ₁ : ℝ) (hζ₀ : 0 ≤ ζ₀) (hζ₁ : 0 ≤ ζ₁)
    (h₀ : ApproxOn CleanX (nrun prim (srcC false)) (liftB (X := Zs) (srcIdeal false (Jsrc false)))
      ζ₀)
    (h₁ : ApproxOn CleanX (nrun prim (srcC true)) (liftB (X := Zs) (srcIdeal true (Jsrc true)))
      ζ₁) :
    ApproxOn CleanX (nrun prim (loadConst m srcC)) (liftB (X := Zs) (loadIdeal (JlC m Jsrc)))
      (ζ₀ + ζ₁) := by
  have hS : ∀ y : Cfg ((Fin (m + 1) ⊕ S) ⊕ Zs), CleanX y →
      CleanX (fun c => y (plC m S Zs c)) := by
    intro y hy z
    exact hy z
  have hA₀ := approxOn_localOp (plC m S Zs).injective (fun _ => nrun prim (srcC false))
    (fun _ => liftB (X := Zs) (srcIdeal false (Jsrc false))) hζ₀ hS (fun _ => h₀)
  have hA₁ := approxOn_localOp (plC m S Zs).injective (fun _ => nrun prim (srcC true))
    (fun _ => liftB (X := Zs) (srcIdeal true (Jsrc true))) hζ₁ hS (fun _ => h₁)
  rw [place_srcIdeal] at hA₀ hA₁
  have hU₀ : IsUnitary (liftB (X := Zs) (srcIdealL m false (Jsrc false))) :=
    liftB_isUnitary (localOp_isUnitary _ _ (fun y => by
      split_ifs
      · exact hJ false
      · exact isUnitary_one))
  have hC₁ : IsUnitary (localOp (plC m S Zs) (plC m S Zs).injective
      (fun _ => nrun prim (srcC true))) :=
    localOp_isUnitary _ _ (fun _ => nrun_isUnitary prim hprim _ (hsrcV true))
  have h := hA₀.comp (preserves_liftB _) (isUnitary_norm_le hU₀) hA₁ (isUnitary_norm_le hC₁) hζ₁
  rw [← liftB_comp, srcIdealL_comp] at h
  rw [loadConst, nrun_append, nrun_map, nrun_map]
  exact h

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Y] [DecidableEq Y] in
/-- The loading circuit of constant forcing is valid. -/
theorem loadConst_valid (m : ℕ) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) : ∀ i ∈ loadConst m srcC, i.Valid := by
  intro i hi
  rw [loadConst, List.mem_append] at hi
  rcases hi with hi | hi
  · exact valid_map_list _ _ (hsrcV false) i hi
  · exact valid_map_list _ _ (hsrcV true) i hi

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Y] [DecidableEq Y] in
/-- **The counts of the loading circuit**: the gates and calls of the two supplied circuits. -/
theorem loadConst_counts (m : ℕ) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (c : J → Bool) :
    nGatesN (loadConst m srcC) = nGatesN (srcC false) + nGatesN (srcC true) ∧
      nCallsN c (loadConst m srcC) = nCallsN c (srcC false) + nCallsN c (srcC true) := by
  refine ⟨?_, ?_⟩
  · rw [loadConst, nGatesN_append, nGatesN_map, nGatesN_map]
  · rw [loadConst, nCallsN_append, nCallsN_map, nCallsN_map]

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Y] [DecidableEq Y] in
/-- **The source gates of constant forcing** (equation `ode:eq:gate-constant-source`): the
source circuits `loadC = loadConst srcC` and `wpC = wpConst` of the released protocol have
`|loadC| + 2 |wpC| = |srcC false| + |srcC true| + 2 (m + 1)` elementary gates, and their calls
are those of the two supplied loading circuits. -/
theorem const_source_counts (m : ℕ) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (r0 rb T : ℝ) (c : J → Bool) :
    nGatesN (loadConst m srcC) + 2 * nGatesN (wpConst m Zs Y J r0 rb T) =
      nGatesN (srcC false) + nGatesN (srcC true) + 2 * (m + 1) ∧
    nCallsN c (loadConst m srcC) + 2 * nCallsN c (wpConst m Zs Y J r0 rb T) =
      nCallsN c (srcC false) + nCallsN c (srcC true) := by
  obtain ⟨hG, hC⟩ := loadConst_counts m srcC c
  obtain ⟨hG', hC'⟩ := wpConst_counts (Zs := Zs) (Y := Y) m r0 rb T c
  rw [hG, hC, hG', hC']
  simp

end Load

end

end SparseHamiltonian.GateBinaryNodes
