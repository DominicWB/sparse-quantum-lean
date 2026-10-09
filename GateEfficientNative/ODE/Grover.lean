import GateEfficientNative.ODE.Macro
import GateEfficientODE.Circuit.Agree

/-!
# Native reflections and amplification trials

On the native ODE register (with the trivial payload `ℂ`) the clean output
encoding `goodN` places the system qubits with every other wire zero, and the
seed is the all-zero state `sN`.  The two reflections of an amplification
step are exact zero tests on all wires except the native flag and pool
(`rgoodNG`, `rseedNG`: AND chains on the native pool, a phase on the native
flag); on configurations with a clean flag and pool they agree with
`1 - 2 goodN goodN†` and `1 - 2 |sN⟩⟨sN|` (`rgoodN_agrees`, `rseedN_agrees`).

For any native preparation circuit that never changes the native flag and
pool, one step `stepN` agrees with the released signed Grover step of the
actual preparation unitary, and the trial with `j` steps applied to the seed
is exactly the released actual Grover trial (`trialN_seed`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire zMat zMat_unitary negOne_unitary)
open GateODE (OInstr OWire AW goodF)
open scoped InnerProduct BigOperators

variable {a m r K k l f : ℕ} {S Zs Z : Type*} {nP bT bP A : ℕ}

/-! ### Wires and literals of the zero tests -/

section Lits

/-- The native flag. -/
def flgN : HWO a m r K k l f S Zs nP Z bT bP A := Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))

/-- The native pool. -/
def poolN : List (HWO a m r K k l f S Zs nP Z bT bP A) :=
  (List.finRange nP).map (fun i => Sum.inr (Sum.inr (Sum.inr (Sum.inr i))))

theorem poolN_nodup : (poolN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).Nodup := by
  unfold poolN
  refine (List.nodup_finRange nP).map ?_
  intro i j h
  simpa using h

theorem poolN_length : (poolN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).length = nP := by
  simp [poolN]

theorem mem_poolN (w : HWO a m r K k l f S Zs nP Z bT bP A) (hw : w ∈ poolN) :
    ∃ i, w = Sum.inr (Sum.inr (Sum.inr (Sum.inr i))) := by
  simp only [poolN, List.mem_map, List.mem_finRange, true_and] at hw
  obtain ⟨i, rfl⟩ := hw
  exact ⟨i, rfl⟩

variable [Fintype S] [Fintype Zs] [Fintype Z]

/-- Zero literals on every wire except the system, the native flag and the pool. -/
def zeroLitsN : List (HWO a m r K k l f S Zs nP Z bT bP A × Bool) :=
  (Finset.univ : Finset (AW a m r K k l f)).toList.map (fun w => (Sum.inl (Sum.inl w), false)) ++
  (Finset.univ : Finset (XW Z bT bP A)).toList.map (fun x => (Sum.inr (Sum.inl x), false)) ++
  (Finset.univ : Finset Zs).toList.map (fun z => (Sum.inr (Sum.inr (Sum.inl z)), false))

/-- Zero literals on the system wires. -/
def sysLits : List (HWO a m r K k l f S Zs nP Z bT bP A × Bool) :=
  (Finset.univ : Finset S).toList.map (fun s => (Sum.inl (Sum.inr s), false))

omit [Fintype S] in
theorem zeroLitsN_length :
    (zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs)
      (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).length =
      Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs := by
  simp only [zeroLitsN, List.length_append, List.length_map, Finset.length_toList,
    Finset.card_univ]

omit [Fintype Zs] [Fintype Z] in
theorem sysLits_length :
    (sysLits (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs)
      (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).length = Fintype.card S := by
  simp only [sysLits, List.length_map, Finset.length_toList, Finset.card_univ]

omit [Fintype S] in
theorem zeroLitsN_false : ∀ c ∈ (zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)),
    c.2 = false := by
  intro c hc
  simp only [zeroLitsN, List.mem_append, List.mem_map] at hc
  rcases hc with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> rfl

omit [Fintype Zs] [Fintype Z] in
theorem sysLits_false : ∀ c ∈ (sysLits (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)),
    c.2 = false := by
  intro c hc
  simp only [sysLits, List.mem_map] at hc
  obtain ⟨_, _, rfl⟩ := hc
  rfl

omit [Fintype S] in
theorem zeroLitsN_not_refl : ∀ c ∈ (zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k)
    (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)),
    ¬ reflWire c.1 := by
  intro c hc
  simp only [zeroLitsN, List.mem_append, List.mem_map] at hc
  rcases hc with (⟨_, _, rfl⟩ | ⟨_, _, rfl⟩) | ⟨_, _, rfl⟩ <;> exact fun h => h

omit [Fintype Zs] [Fintype Z] in
theorem sysLits_not_refl : ∀ c ∈ (sysLits (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)),
    ¬ reflWire c.1 := by
  intro c hc
  simp only [sysLits, List.mem_map] at hc
  obtain ⟨_, _, rfl⟩ := hc
  exact fun h => h

omit [Fintype S] [Fintype Zs] [Fintype Z] in
theorem reflWire_flgN : reflWire (flgN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) := trivial

omit [Fintype S] [Fintype Zs] [Fintype Z] in
theorem reflWire_poolN : ∀ w ∈ (poolN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)),
    reflWire w := by
  intro w hw
  obtain ⟨i, rfl⟩ := mem_poolN w hw
  trivial

/-- The gate list of the native good-subspace reflection. -/
def rgoodNG : List (Gate (HWO a m r K k l f S Zs nP Z bT bP A)) :=
  mcGate zeroLitsN poolN flgN zMat

/-- The gate list of the native seed reflection. -/
def rseedNG : List (Gate (HWO a m r K k l f S Zs nP Z bT bP A)) :=
  mcGate (zeroLitsN ++ sysLits) poolN flgN zMat

/-- The global sign. -/
def negGateN : Gate (HWO a m r K k l f S Zs nP Z bT bP A) :=
  ⟨[], Sum.inl (Sum.inl (Sum.inr OWire.ini)), -1⟩

omit [Fintype S] in
theorem rgoodNG_length : (rgoodNG (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).length ≤
      2 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs) +
        1 := by
  have h := mcGate_length_le (zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) poolN flgN zMat
  rw [zeroLitsN_length] at h
  exact h

theorem rseedNG_length : (rseedNG (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).length ≤
      2 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
        Fintype.card S) + 1 := by
  have h := mcGate_length_le ((zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) ++ sysLits)
    poolN flgN zMat
  rw [List.length_append, zeroLitsN_length, sysLits_length] at h
  exact h

omit [Fintype S] [Fintype Zs] [Fintype Z] in
theorem lits_ne_pool (c : HWO a m r K k l f S Zs nP Z bT bP A × Bool) (hc : ¬ reflWire c.1) :
    ∀ w ∈ (poolN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)), c.1 ≠ w := by
  intro w hw h
  exact hc (h ▸ reflWire_poolN w hw)

omit [Fintype S] [Fintype Zs] [Fintype Z] in
theorem lits_ne_flg (c : HWO a m r K k l f S Zs nP Z bT bP A × Bool) (hc : ¬ reflWire c.1) :
    c.1 ≠ flgN := fun h => hc (h ▸ reflWire_flgN)

omit [Fintype S] [Fintype Zs] [Fintype Z] in
theorem poolN_ne_flg : ∀ w ∈ (poolN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)), w ≠ flgN := by
  intro w hw
  obtain ⟨i, rfl⟩ := mem_poolN w hw
  simp [flgN]

omit [Fintype S] in
theorem rgoodNG_ok : ∀ g ∈ (rgoodNG (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)), GateOK 3 g := by
  intro g hg
  exact (mcGate_valid _ _ _ _ zMat_unitary poolN_nodup
    (fun c hc => lits_ne_flg c (zeroLitsN_not_refl c hc)) poolN_ne_flg
    (fun c hc => lits_ne_pool c (zeroLitsN_not_refl c hc)) g hg).mono (by norm_num)

theorem rseedNG_ok : ∀ g ∈ (rseedNG (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)), GateOK 3 g := by
  have hnr : ∀ c ∈ (zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) ++ sysLits,
      ¬ reflWire c.1 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact zeroLitsN_not_refl c hc
    · exact sysLits_not_refl c hc
  intro g hg
  exact (mcGate_valid _ _ _ _ zMat_unitary poolN_nodup
    (fun c hc => lits_ne_flg c (hnr c hc)) poolN_ne_flg
    (fun c hc => lits_ne_pool c (hnr c hc)) g hg).mono (by norm_num)

omit [Fintype S] [Fintype Zs] [Fintype Z] in
theorem negGateN_ok : GateOK 3 (negGateN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) :=
  ⟨by simp [negGateN], by simp [negGateN], negOne_unitary⟩

end Lits

/-! ### The clean output encoding and the seed -/

section Good

variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]

/-- Every wire except the system qubits is zero. -/
def NonSysZero (y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) : Prop :=
  (∀ w, y (Sum.inl (Sum.inl w)) = false) ∧ (∀ x, y (Sum.inr x) = false)

instance (y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) : Decidable (NonSysZero y) :=
  inferInstanceAs (Decidable ((∀ w, y (Sum.inl (Sum.inl w)) = false) ∧
    (∀ x, y (Sum.inr x) = false)))

/-- The clean output encoding of the native register. -/
def goodN : Reg S ℂ →L[ℂ] Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ :=
  sysEmb (goodF (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (P := Reg S ℂ))

omit [DecidableEq Zs] [DecidableEq Z] in
theorem goodN_apply (ψ : Reg S ℂ) (y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) :
    goodN ψ y = if NonSysZero y then ψ (fun s => y (Sum.inl (Sum.inr s))) else 0 := by
  simp only [goodN, sysEmb, goodF, comp_apply, cleanEmb_apply, fl_apply, GateODE.basL_apply,
    bas_apply, NonSysZero, funext_iff]
  split_ifs <;> simp_all

theorem norm_goodN (ψ : Reg S ℂ) :
    ‖goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (Zs := Zs) (nP := nP)
      (Z := Z) (bT := bT) (bP := bP) (A := A) ψ‖ = ‖ψ‖ := by
  rw [goodN, sysEmb, comp_apply, comp_apply, norm_cleanEmb, norm_fl, goodF, GateODE.basL_apply,
    norm_bas]

theorem goodN_isometry :
    (goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs)
      (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))† ∘L goodN = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp norm_goodN

/-- The system configuration with every other wire zero. -/
def sysCfg (s : Cfg S) : Cfg (HWO a m r K k l f S Zs nP Z bT bP A) :=
  Sum.elim (Sum.elim (fun _ => false) s) (fun _ => false)

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z] in
theorem nonSysZero_sysCfg (s : Cfg S) :
    NonSysZero (sysCfg (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (Zs := Zs)
      (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) s) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z] in
theorem sysCfg_of_nonSysZero (y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) (hy : NonSysZero y) :
    sysCfg (fun s => y (Sum.inl (Sum.inr s))) = y := by
  funext v
  rcases v with (w | s) | x
  · exact (hy.1 w).symm
  · rfl
  · exact (hy.2 x).symm

omit [DecidableEq Zs] [DecidableEq Z] in
theorem goodN_bas (s : Cfg S) (p : ℂ) :
    goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (Zs := Zs) (nP := nP)
      (Z := Z) (bT := bT) (bP := bP) (A := A) (bas s p) = bas (sysCfg s) p := by
  apply PiLp.ext
  intro y
  rw [goodN_apply, bas_apply, bas_apply]
  by_cases hy : NonSysZero y
  · rw [if_pos hy]
    have e := sysCfg_of_nonSysZero y hy
    by_cases hs : (fun s' => y (Sum.inl (Sum.inr s'))) = s
    · rw [if_pos hs, if_pos (by rw [← e, hs])]
    · rw [if_neg hs, if_neg]
      intro h
      apply hs
      rw [h]
      rfl
  · rw [if_neg hy, if_neg]
    intro h
    exact hy (h ▸ nonSysZero_sysCfg s)

theorem goodN_adjoint_bas (x : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) (p : ℂ) :
    ((goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (Zs := Zs) (nP := nP)
      (Z := Z) (bT := bT) (bP := bP) (A := A))†) (bas x p) =
      if NonSysZero x then bas (fun s => x (Sum.inl (Sum.inr s))) p else 0 := by
  by_cases hx : NonSysZero x
  · rw [if_pos hx]
    have e : bas x p = goodN (bas (fun s => x (Sum.inl (Sum.inr s))) p) := by
      rw [goodN_bas, sysCfg_of_nonSysZero x hx]
    rw [e, ← comp_apply, goodN_isometry, one_apply_eq_self]
  · rw [if_neg hx]
    apply ext_inner_right ℂ
    intro ψ
    rw [adjoint_inner_left, inner_bas_left, goodN_apply, if_neg hx, inner_zero_right,
      inner_zero_left]

/-- The native seed: every wire zero. -/
def sN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ := bas (fun _ => false) 1

theorem norm_sN : ‖(sN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
    (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))‖ = 1 := by
  rw [sN, norm_bas, norm_one]

/-- The released seed vector of the qubit system: the all-zero state. -/
def seedV : Reg S ℂ := bas (fun _ => false) 1

theorem norm_seedV : ‖(seedV : Reg S ℂ)‖ = 1 := by
  rw [seedV, norm_bas, norm_one]

omit [DecidableEq Zs] [DecidableEq Z] in
theorem sN_eq_goodN : (sN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) = goodN seedV := by
  rw [sN, seedV, goodN_bas]
  congr 1
  funext v
  rcases v with (w | s) | x <;> rfl

omit [DecidableEq Zs] [DecidableEq Z] in
/-- The native seed is the clean embedding of the released seed state. -/
theorem sN_eq_cleanEmb :
    (sN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) =
      cleanEmb (fl (GateODE.seedState (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
        (f := f) (seedV : Reg S ℂ))) := by
  rw [sN_eq_goodN, goodN, sysEmb, comp_apply, comp_apply, goodF, GateODE.basL_apply]
  rfl

/-- The ideal reflection about the clean outputs. -/
def rgoodNI : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
    Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ :=
  PhaseSubspaceGates.phase (ODEHeraldedSuccess.successProjector goodN) (-1)

/-- The ideal reflection about the seed. -/
def rseedNI : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
    Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ :=
  PhaseSubspaceGates.phase (ODEGroverRay.projector sN) (-1)

theorem rgoodNI_bas (x : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) (p : ℂ) :
    rgoodNI (bas x p) = if NonSysZero x then -bas x p else bas x p := by
  rw [rgoodNI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
    ODEHeraldedSuccess.successProjector, comp_apply, goodN_adjoint_bas]
  by_cases hx : NonSysZero x
  · rw [if_pos hx, if_pos hx, goodN_bas, sysCfg_of_nonSysZero x hx]
    module
  · rw [if_neg hx, if_neg hx, map_zero, smul_zero, add_zero]

theorem rseedNI_bas (x : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) (p : ℂ) :
    rseedNI (bas x p) = if x = (fun _ => false) then -bas x p else bas x p := by
  rw [rseedNI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
    ODEGroverRay.projector_apply, sN, inner_bas_left, bas_apply]
  by_cases hx : x = fun _ => false
  · subst hx
    rw [if_pos rfl, if_pos rfl]
    have e : inner ℂ (1 : ℂ) p = p := by rw [RCLike.inner_apply]; simp
    rw [e, ← bas_smul, smul_eq_mul, mul_one]
    module
  · rw [if_neg (Ne.symm hx), if_neg hx, inner_zero_right, zero_smul, smul_zero, add_zero]

theorem rgoodNI_isUnitary : IsUnitary (rgoodNI (a := a) (m := m) (r := r) (K := K) (k := k)
    (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) :=
  PhaseSubspaceGates.phase_unitary _
    (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ goodN_isometry) _ (by simp)

theorem rseedNI_isUnitary : IsUnitary (rseedNI (a := a) (m := m) (r := r) (K := K) (k := k)
    (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) :=
  PhaseSubspaceGates.phase_unitary _ (ODEGroverRay.projector_isOrthogonalProjection _ norm_sN) _
    (by simp)

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z] in
theorem zeroOn_of_nonSysZero (y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A))
    (hy : NonSysZero y) : ZeroOn reflWire y := by
  intro w hw
  rcases w with v | x
  · exact absurd hw (not_reflWire_inl v)
  · exact hy.2 x

omit [DecidableEq Zs] [DecidableEq Z] in
theorem supp_goodN (φ : Reg S ℂ) :
    Supp (ZeroOn reflWire) (goodN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) φ) := by
  intro y hy
  rw [goodN_apply, if_neg (fun h => hy (zeroOn_of_nonSysZero y h))]

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] in
theorem supp_sN : Supp (ZeroOn reflWire) (sN (a := a) (m := m) (r := r) (K := K) (k := k)
    (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) :=
  supp_bas _ (fun _ _ => rfl) _

theorem preserves_rgoodNI : Preserves (ZeroOn reflWire) (rgoodNI (a := a) (m := m) (r := r)
    (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT)
    (bP := bP) (A := A)) := by
  intro ψ hψ
  have hrep : rgoodNI ψ = ψ + (-1 - 1 : ℂ) • goodN ((goodN†) ψ) := by
    rw [rgoodNI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
      ODEHeraldedSuccess.successProjector, comp_apply]
  rw [hrep]
  exact supp_add hψ (supp_smul _ (supp_goodN _))

theorem preserves_rseedNI : Preserves (ZeroOn reflWire) (rseedNI (a := a) (m := m) (r := r)
    (K := K) (k := k) (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT)
    (bP := bP) (A := A)) := by
  intro ψ hψ
  have hrep : rseedNI ψ = ψ + (-1 - 1 : ℂ) • (inner ℂ sN ψ • sN) := by
    rw [rseedNI, PhaseSubspaceGates.phase, add_apply, one_apply_eq_self, smul_apply,
      ODEGroverRay.projector_apply]
  rw [hrep]
  exact supp_add hψ (supp_smul _ (supp_smul _ supp_sN))

theorem rgoodNI_adjoint : (rgoodNI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))† = rgoodNI := by
  rw [← star_eq_adjoint, rgoodNI, PhaseSubspaceGates.phase_adjoint _
    (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ goodN_isometry).1]
  simp

theorem rseedNI_adjoint : (rseedNI (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A))† = rseedNI := by
  rw [← star_eq_adjoint, rseedNI, PhaseSubspaceGates.phase_adjoint _ (GateODE.projector_star _)]
  simp

/-! ### Agreement of the gate lists with the ideal reflections -/

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype S] in
theorem ctrlOK_zeroLitsN (x : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) (hx : ZeroOn reflWire x) :
    ctrlOK zeroLitsN x = true ↔ NonSysZero x := by
  rw [ctrlOK_iff]
  constructor
  · intro h
    refine ⟨fun w => h (Sum.inl (Sum.inl w), false) ?_, fun y => ?_⟩
    · simp [zeroLitsN, Finset.mem_toList]
    · rcases y with xw | (z | rw)
      · exact h (Sum.inr (Sum.inl xw), false) (by simp [zeroLitsN, Finset.mem_toList])
      · exact h (Sum.inr (Sum.inr (Sum.inl z)), false) (by simp [zeroLitsN, Finset.mem_toList])
      · exact hx _ trivial
  · intro h c hc
    rw [zeroLitsN_false c hc]
    simp only [zeroLitsN, List.mem_append, List.mem_map] at hc
    rcases hc with (⟨w, _, rfl⟩ | ⟨xw, _, rfl⟩) | ⟨z, _, rfl⟩
    · exact h.1 w
    · exact h.2 _
    · exact h.2 _

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] in
theorem ctrlOK_seedLits (x : Cfg (HWO a m r K k l f S Zs nP Z bT bP A)) (hx : ZeroOn reflWire x) :
    ctrlOK (zeroLitsN ++ sysLits) x = true ↔ x = fun _ => false := by
  rw [ctrlOK_iff]
  constructor
  · intro h
    have h1 : NonSysZero x := (ctrlOK_zeroLitsN x hx).mp
      ((ctrlOK_iff _ _).mpr (fun c hc => h c (List.mem_append_left _ hc)))
    funext v
    rcases v with (w | s) | y
    · exact h1.1 w
    · exact h (Sum.inl (Sum.inr s), false) (List.mem_append_right _ (by
        simp [sysLits, Finset.mem_toList]))
    · exact h1.2 y
  · rintro rfl c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (zeroLitsN_false c hc).symm
    · exact (sysLits_false c hc).symm

/-- The native pool wires. -/
def poolWire : HWO a m r K k l f S Zs nP Z bT bP A → Prop
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => True
  | _ => False

omit [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z] in
theorem zeroOn_pool_of_refl (x : Cfg (HWO a m r K k l f S Zs nP Z bT bP A))
    (hx : ZeroOn reflWire x) : ZeroOn poolWire x := by
  intro w hw
  rcases w with v | (xw | (z | (u | i)))
  · exact absurd hw id
  · exact absurd hw id
  · exact absurd hw id
  · exact absurd hw id
  · exact hx _ trivial

theorem mcGate_flg_agrees (ls : List (HWO a m r K k l f S Zs nP Z bT bP A × Bool))
    (hls : ∀ c ∈ ls, ¬ reflWire c.1) (hlen : ls.length ≤ nP + 1) (u : Matrix Bool Bool ℂ) :
    Agrees (ZeroOn poolWire) (gRun (Q := ℂ) (mcGate ls poolN flgN u)) (gateOp ls flgN u) :=
  mcGate_agrees _ _ _ _ (by rw [poolN_length]; exact hlen) poolN_nodup
    (fun c hc => lits_ne_flg c (hls c hc)) poolN_ne_flg (fun c hc => lits_ne_pool c (hls c hc))
    (ZeroOn poolWire)
    (fun x hx w hw => by
      obtain ⟨i, rfl⟩ := mem_poolN w hw
      exact hx _ trivial)
    (fun x b hx w hw => by
      rw [Function.update_of_ne]
      · exact hx w hw
      · rintro rfl
        exact hw)

/-- **The good-subspace reflection agrees with `1 - 2 goodN goodN†`** on a clean
native flag and pool. -/
theorem rgoodN_agrees
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs ≤
      nP + 1) :
    Agrees (ZeroOn reflWire) (gRun (Q := ℂ) (rgoodNG (a := a) (m := m) (r := r) (K := K) (k := k)
      (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)))
      rgoodNI := by
  apply agrees_of_bas
  intro x hx p
  have hflg : x flgN = false := hx flgN reflWire_flgN
  rw [rgoodNG, mcGate_flg_agrees _ zeroLitsN_not_refl (by rw [zeroLitsN_length]; exact hnP) zMat
    _ (supp_bas x (zeroOn_pool_of_refl x hx) p),
    gateOp_bas _ _ _ (fun c hc => lits_ne_flg c (zeroLitsN_not_refl c hc)), rgoodNI_bas]
  by_cases h0 : NonSysZero x
  · rw [if_pos ((ctrlOK_zeroLitsN x hx).mpr h0), if_pos h0, Fintype.sum_bool, hflg]
    have hu : Function.update x flgN false = x := by
      rw [← hflg, Function.update_eq_self]
    have hz1 : zMat true false = 0 := by simp [zMat]
    have hz0 : zMat false false = -1 := by simp [zMat]
    rw [hz1, hz0, zero_smul, zero_add, hu]
    module
  · rw [if_neg (fun h => h0 ((ctrlOK_zeroLitsN x hx).mp h)), if_neg h0]

/-- **The seed reflection agrees with `1 - 2 |sN⟩⟨sN|`** on a clean native flag
and pool. -/
theorem rseedN_agrees
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1) :
    Agrees (ZeroOn reflWire) (gRun (Q := ℂ) (rseedNG (a := a) (m := m) (r := r) (K := K) (k := k)
      (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)))
      rseedNI := by
  have hnr : ∀ c ∈ (zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) ++ sysLits,
      ¬ reflWire c.1 := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact zeroLitsN_not_refl c hc
    · exact sysLits_not_refl c hc
  apply agrees_of_bas
  intro x hx p
  have hflg : x flgN = false := hx flgN reflWire_flgN
  rw [rseedNG, mcGate_flg_agrees _ hnr
    (by rw [List.length_append, zeroLitsN_length, sysLits_length]; exact hnP) zMat
    _ (supp_bas x (zeroOn_pool_of_refl x hx) p),
    gateOp_bas _ _ _ (fun c hc => lits_ne_flg c (hnr c hc)), rseedNI_bas]
  by_cases h0 : x = fun _ => false
  · rw [if_pos ((ctrlOK_seedLits x hx).mpr h0), if_pos h0, Fintype.sum_bool, hflg]
    have hu : Function.update x flgN false = x := by
      rw [← hflg, Function.update_eq_self]
    have hz1 : zMat true false = 0 := by simp [zMat]
    have hz0 : zMat false false = -1 := by simp [zMat]
    rw [hz1, hz0, zero_smul, zero_add, hu]
    module
  · rw [if_neg (fun h => h0 ((ctrlOK_seedLits x hx).mp h)), if_neg h0]

end Good

/-! ### Steps and trials -/

section Trial

variable {Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z]
  [DecidableEq Z] [Fintype Y] [DecidableEq Y]

/-- One native amplification step: good reflection, inverse preparation, seed
reflection, preparation, global sign. -/
def stepN (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) :
    List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J) :=
  nGatesOf rgoodNG ++ ninv prepN ++ nGatesOf rseedNG ++ prepN ++ [NInstr.gate negGateN]

/-- The native trial with `j` amplification steps. -/
def trialN (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) (j : ℕ) :
    List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J) :=
  prepN ++ (List.replicate j (stepN prepN)).flatten

variable (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)

/-- The released signed Grover step of the actual native preparation. -/
def groverN (UN : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
    Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) :
    Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ] Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ :=
  ODEGroverProgram.operator UN (ODEGroverRay.projector sN)
    (ODEHeraldedSuccess.successProjector goodN)

theorem gateOp_negN :
    gateOp (Q := ℂ) (negGateN : Gate (HWO a m r K k l f S Zs nP Z bT bP A)).cs
      (negGateN : Gate (HWO a m r K k l f S Zs nP Z bT bP A)).t
      (negGateN : Gate (HWO a m r K k l f S Zs nP Z bT bP A)).u = -1 :=
  GateODE.gateOp_neg_one _

/-- **One native step agrees with the signed Grover step of the actual
preparation** on a clean native flag and pool. -/
theorem stepN_agrees
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN)) :
    Agrees (ZeroOn reflWire) (nrun prim (stepN prepN)) (groverN (nrun prim prepN)) := by
  have hg := rgoodN_agrees (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) (by omega)
  have hs := rseedN_agrees (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) hnP
  unfold stepN groverN ODEGroverProgram.operator
  simp only [nrun_append, nrun_ninv, nrun_nGatesOf, nrun_singleton, NInstr.eval_gate]
  rw [gateOp_negN]
  have h1 := hg.comp preserves_rgoodNI (Agrees.refl (ZeroOn reflWire) ((nrun prim prepN)†))
  have h2 := h1.comp (preserves_rgoodNI.comp hP.2) hs
  have h3 := h2.comp ((preserves_rgoodNI.comp hP.2).comp preserves_rseedNI)
    (Agrees.refl (ZeroOn reflWire) (nrun prim prepN))
  have h4 := h3.comp (((preserves_rgoodNI.comp hP.2).comp preserves_rseedNI).comp hP.1)
    (Agrees.refl (ZeroOn reflWire) (-1))
  intro ψ hψ
  rw [h4 ψ hψ]
  simp only [comp_apply, neg_apply, one_apply_eq_self, mul_apply_eq_comp, rgoodNI, rseedNI,
    star_eq_adjoint]

theorem preserves_groverN (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN)) :
    Preserves (ZeroOn reflWire) (groverN (nrun prim prepN)) := by
  have hpre : Preserves (ZeroOn reflWire) (-(nrun prim prepN ∘L rseedNI ∘L
      (nrun prim prepN)† ∘L rgoodNI)) :=
    preserves_neg (((preserves_rgoodNI.comp hP.2).comp preserves_rseedNI).comp hP.1)
  intro ψ hψ
  have e : groverN (nrun prim prepN) ψ = (-(nrun prim prepN ∘L rseedNI ∘L
      (nrun prim prepN)† ∘L rgoodNI)) ψ := by
    simp only [groverN, ODEGroverProgram.operator, neg_apply, mul_apply_eq_comp, comp_apply,
      rgoodNI, rseedNI, star_eq_adjoint]
  rw [e]
  exact hpre ψ hψ

theorem stepsN_agree
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (j : ℕ) (φ : Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) (hφ : Supp (ZeroOn reflWire) φ) :
    nrun prim (List.replicate j (stepN prepN)).flatten φ = (groverN (nrun prim prepN) ^ j) φ := by
  induction j generalizing φ with
  | zero => rfl
  | succ j ih =>
      rw [List.replicate_succ, List.flatten_cons, nrun_append, comp_apply,
        stepN_agrees prim hnP prepN hP φ hφ,
        ih _ (preserves_groverN prim prepN hP φ hφ), pow_succ, mul_apply_eq_comp]

/-- **The native trial is the released actual Grover trial of the actual
native preparation.** -/
theorem trialN_seed
    (hnP : Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
      Fintype.card S ≤ nP + 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hU : IsUnitary (nrun prim prepN)) (hP : Pres2 (ZeroOn reflWire) (nrun prim prepN))
    (j : ℕ) :
    nrun prim (trialN prepN j) sN = ODEGroverActual.trial goodN (nrun prim prepN) sN j := by
  rw [trialN, nrun_append, comp_apply,
    stepsN_agree prim hnP prepN hP j _ (hP.1 _ supp_sN)]
  unfold ODEGroverActual.trial ODEGroverActual.actualG
  congr 2
  rw [groverN, ODEGroverProgram.operator_eq_grover _ _ _ hU, ← GateODE.projector_map]

/-! ### Validity -/

omit [Fintype Y] [DecidableEq Y] [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] in
theorem stepN_valid (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hv : ∀ i ∈ prepN, i.Valid) : ∀ i ∈ stepN prepN, i.Valid := by
  intro i hi
  simp only [stepN, List.mem_append, List.mem_singleton] at hi
  rcases hi with (((h | h) | h) | h) | rfl
  · exact valid_nGatesOf _ rgoodNG_ok i h
  · exact valid_ninv _ hv i h
  · exact valid_nGatesOf _ rseedNG_ok i h
  · exact hv i h
  · exact negGateN_ok

omit [Fintype Y] [DecidableEq Y] [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] in
theorem trialN_valid (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hv : ∀ i ∈ prepN, i.Valid) (j : ℕ) : ∀ i ∈ trialN prepN j, i.Valid := by
  intro i hi
  simp only [trialN, List.mem_append, List.mem_flatten, List.mem_replicate] at hi
  rcases hi with h | ⟨l', ⟨_, rfl⟩, h⟩
  · exact hv i h
  · exact stepN_valid prepN hv i h

/-! ### Counts -/

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem trialN_nCalls (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (p : J → Bool) (j : ℕ) :
    nCallsN p (trialN prepN j) = (2 * j + 1) * nCallsN p prepN := by
  have hstep : nCallsN p (stepN prepN) = 2 * nCallsN p prepN := by
    have h3 : nCallsN p ([NInstr.gate negGateN] : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A)
        Y J)) = 0 := rfl
    simp only [stepN, nCallsN_append, nCallsN_nGatesOf, nCallsN_ninv, h3]
    ring
  rw [trialN, nCallsN_append, nCallsN_replicate, hstep]
  ring

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [Fintype Y] [DecidableEq Y] in
theorem trialN_nGates (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (j : ℕ) :
    nGatesN (trialN prepN j) ≤ (2 * j + 1) * nGatesN prepN +
      j * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
        Fintype.card S) + 3) := by
  have hstep : nGatesN (stepN prepN) ≤ 2 * nGatesN prepN +
      (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card Zs +
        Fintype.card S) + 3) := by
    have h1 := rgoodNG_length (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
    have h2 := rseedNG_length (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
    have h3 : nGatesN ([NInstr.gate negGateN] : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A)
        Y J)) = 1 := rfl
    simp only [stepN, nGatesN_append, nGatesN_nGatesOf, nGatesN_ninv, h3]
    omega
  rw [trialN, nGatesN_append, nGatesN_replicate]
  have h := Nat.mul_le_mul_left j hstep
  nlinarith [h]

end Trial

end

end SparseHamiltonian.GateNative
