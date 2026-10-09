import ZeroTimeGateODE.Assembly
import GateEfficientNative.ODE.Time

/-!
# Direct source assembly, time-dependent forcing: the circuits

The time-dependent preparation of Theorem `ode:thm:gates` is
`Wp · LCHS · LOAD · SELECT · PHASE · LCHS⁻¹ · Wp⁻¹`, with one call of the supplied weight
preparation `Wp` on the source label `(ini, q)` and one coherent call of the supplied loading
`J`.  Its zero-case counterpart keeps only the source part: on the source-label wires `srcTS`,
the system and the source scratch of a native ODE register,

`tzprepC loadC wpC = wpC · loadC · wpC⁻¹`,

where `wpC` and `loadC` are the supplied native circuits of `Wp` and of the selected loading
(placed by the released placements `GateNative.wpPl`, `GateNative.loadPl`) and `wpC⁻¹` is the
literal inverse of `wpC`.  There is no private call, no `U_J` gate and no matrix call besides
those the supplied circuits make.

* `tzprepC_counts`: `|loadC| + 2 |wpC|` gates and `calls(loadC) + 2 calls(wpC)` calls of every
  kind of primitive oracles.
* `tzprepC_approx`: within `3 ζs` of the lifted released counterpart `tzrelC` (the released
  weight preparation, loading and inverse weight preparation) when both circuits are within
  `ζs`.
* `tzrelC_decoded`: the clean decoded vector of `tzrelC` is `∑_c |Wp_{c,0}|² J_{s(c)} v`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Label cfgOf adjIf srcTS srcTS_injective)
open GateODE.Time (TOracles teval trun psel labAt wprep)
open scoped InnerProduct BigOperators

/-! ### The circuits -/

section Circuits

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}

/-- **The native zero-case preparation of the time-dependent solver**: the weight-preparation
circuit, the loading circuit and the literal inverse of the weight-preparation circuit, on the
source-label wires, the system and the source scratch. -/
def tzprepC (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) :
    List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J) :=
  wpC.map (NInstr.map wpPl) ++ loadC.map (NInstr.map loadPl) ++ (ninv wpC).map (NInstr.map wpPl)

/-- The released-model counterpart: the weight preparation, the loading and the inverse weight
preparation. -/
def tzrelC : List (OInstr (Wire a m r K) (OWire k l f)) :=
  [.src true false, .src false false, .src true true]

/-- The native macros of the released instructions of `tzrelC`. -/
def tzmacro (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) :
    OInstr (Wire a m r K) (OWire k l f) → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)
  | .src false false => loadC.map (NInstr.map loadPl)
  | .src false true => (ninv loadC).map (NInstr.map loadPl)
  | .src true false => wpC.map (NInstr.map wpPl)
  | .src true true => (ninv wpC).map (NInstr.map wpPl)
  | _ => []

/-- `tzprepC` is the macro substitution of `tzrelC`. -/
theorem tzprepC_eq_flatMap (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) :
    (tzprepC loadC wpC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) =
      (tzrelC : List (OInstr (Wire a m r K) (OWire k l f))).flatMap (tzmacro loadC wpC) := by
  simp only [tzprepC, tzrelC, tzmacro, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]

/-- Every instruction of the time-dependent zero-case preparation is valid. -/
theorem tzprepC_valid (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (hloadV : ∀ i ∈ loadC, i.Valid) (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ∀ i ∈ (tzprepC loadC wpC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)),
      i.Valid := by
  intro i hi
  simp only [tzprepC, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · exact valid_map_list _ _ hwpV i hi
  · exact valid_map_list _ _ hloadV i hi
  · exact valid_map_list _ _ (valid_ninv _ hwpV) i hi

/-- No instruction of the time-dependent zero-case preparation touches the native flag and
pool. -/
theorem tzprepC_not_touches (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) :
    ∀ i ∈ (tzprepC loadC wpC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)),
      ¬ i.Touches reflWire := by
  have hl : ∀ v, ¬ reflWire ((loadPl : (Fin (k + 1) ⊕ S) ⊕ Zs ↪
      HWO a m r K k l f S Zs nP Z bT bP A) v) := by
    intro v
    rcases v with (j | s) | z <;> exact fun h => h
  have hw : ∀ v,
      ¬ reflWire ((wpPl : Fin (k + 1) ⊕ Zs ↪ HWO a m r K k l f S Zs nP Z bT bP A) v) := by
    intro v
    rcases v with j | z <;> exact fun h => h
  intro i hi
  simp only [tzprepC, List.mem_append, List.mem_map] at hi
  rcases hi with (⟨i', _, rfl⟩ | ⟨i', _, rfl⟩) | ⟨i', _, rfl⟩
  · exact NInstr.not_touches_map _ _ hw i'
  · exact NInstr.not_touches_map _ _ hl i'
  · exact NInstr.not_touches_map _ _ hw i'

/-- **The counts of the time-dependent zero-case preparation**: the gates and calls of the
loading circuit and twice those of the weight-preparation circuit. -/
theorem tzprepC_counts (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) (q : J → Bool) :
    nGatesN (tzprepC loadC wpC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) =
      nGatesN loadC + 2 * nGatesN wpC ∧
    nCallsN q (tzprepC loadC wpC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) =
      nCallsN q loadC + 2 * nCallsN q wpC := by
  constructor
  · simp only [tzprepC, nGatesN_append, nGatesN_map, nGatesN_ninv]
    ring
  · simp only [tzprepC, nCallsN_append, nCallsN_map, nCallsN_ninv]
    ring

end Circuits

/-! ### The approximation of the released counterpart -/

section Approx

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- The time-dependent zero-case preparation never changes the native flag and pool. -/
theorem tzprepC_pres (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J))
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) :
    Pres2 (ZeroOn reflWire)
      (nrun prim (tzprepC loadC wpC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))) :=
  pres2_nrun_zeroOn prim reflWire _ (tzprepC_not_touches loadC wpC)

/-- The macro of a released loading or weight-preparation call approximates it within the
accuracy of the supplied circuits (the released `tsrcMacro_approx` on any native ODE
register). -/
theorem tzmacro_approx (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (v : Reg S ℂ) (σ : TOracles a k l (Reg S ℂ)) (hσ : σ.Unitary m) {ζs : ℝ} (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs) (c adj : Bool) :
    ApproxOn CleanX
      (nrun prim (tzmacro (a := a) (m := m) (r := r) (K := K) (f := f) (nP := nP) (Z := Z)
        (bT := bT) (bP := bP) (A := A) loadC wpC (.src c adj)))
      (liftB (conj (teval (m := m) (r := r) (K := K) (f := f) v σ (.src c adj)))) ζs := by
  cases c
  · have hS : ∀ y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A), CleanX y →
        CleanX (fun c => y ((loadPl (a := a) (m := m) (r := r) (K := K) (k := k)
          (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z)
          (bT := bT) (bP := bP) (A := A)) c)) :=
      fun y hy z => hy (Sum.inr (Sum.inl z))
    have hCU : IsUnitary (nrun prim loadC) := nrun_isUnitary prim hprim _ hloadV
    have hIU : IsUnitary (liftB (X := Zs) (loadIdeal σ.J)) :=
      liftB_isUnitary (loadIdeal_isUnitary _ hσ.load)
    rw [GateODE.Time.teval_load, liftB_conj_load loadPl (fun _ => rfl) (fun _ => rfl)
      (fun s => adjIf adj (σ.J s))]
    cases adj
    · simp only [tzmacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      exact hload
    · simp only [tzmacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      show ApproxOn CleanX (nrun prim (ninv loadC)) (liftB (loadIdeal (fun s => (σ.J s)†))) ζs
      rw [nrun_ninv, ← loadIdeal_adjoint, liftB_adjoint]
      exact hload.adjoint hCU hIU (by rw [← liftB_adjoint]; exact preserves_liftB _)
  · have hS : ∀ y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A), CleanX y →
        CleanX (fun c => y ((wpPl (a := a) (m := m) (r := r) (K := K) (k := k)
          (l := l) (f := f) (S := S) (Zs := Zs) (nP := nP) (Z := Z)
          (bT := bT) (bP := bP) (A := A)) c)) :=
      fun y hy z => hy (Sum.inr (Sum.inl z))
    have hCU : IsUnitary (nrun prim wpC) := nrun_isUnitary prim hprim _ hwpV
    have hIU : IsUnitary (liftB (X := Zs) (matOp (Q := ℂ) σ.Wp)) :=
      liftB_isUnitary (matOp_isUnitary _ hσ.prep_left hσ.prep_right)
    rw [GateODE.Time.teval_wprep, wprep, liftB_conj_wprep wpPl (fun _ => rfl)]
    cases adj
    · simp only [tzmacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      exact hwp
    · simp only [tzmacro]
      rw [nrun_map]
      apply approxOn_localOp _ _ _ hζs hS
      intro _
      show ApproxOn CleanX (nrun prim (ninv wpC)) (liftB (matOp σ.Wp.conjTranspose)) ζs
      rw [nrun_ninv, ← matOp_adjoint, liftB_adjoint]
      exact hwp.adjoint hCU hIU (by rw [← liftB_adjoint]; exact preserves_liftB _)

/-- **The native time-dependent zero-case preparation is within `3 ζs` of the lifted released
counterpart**, for any `U_J` and private operations (they are not called), if the loading and
weight-preparation circuits are within `ζs`. -/
theorem tzprepC_approx (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (loadC : List (NInstr ((Fin (k + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (k + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid)
    (v : Reg S ℂ) (σ : TOracles a k l (Reg S ℂ)) (hσ : σ.Unitary m) {ζs : ℝ} (hζs : 0 ≤ ζs)
    (hload : ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal σ.J)) ζs)
    (hwp : ApproxOn CleanX (nrun prim wpC) (liftB (matOp σ.Wp)) ζs) :
    ApproxOn CleanX
      (nrun prim (tzprepC loadC wpC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)))
      (liftB (conj (trun (m := m) (r := r) (K := K) (f := f) v σ tzrelC))) (3 * ζs) := by
  have hw : ∀ i ∈ (tzrelC : List (OInstr (Wire a m r K) (OWire k l f))),
      ApproxOn CleanX (nrun prim (tzmacro (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
        loadC wpC i)) (liftB (conj (teval (m := m) (r := r) (K := K) (f := f) v σ i))) ζs := by
    intro i hi
    simp only [tzrelC, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact tzmacro_approx prim hprim loadC hloadV wpC hwpV v σ hσ hζs hload hwp true false
    · exact tzmacro_approx prim hprim loadC hloadV wpC hwpV v σ hσ hζs hload hwp false false
    · exact tzmacro_approx prim hprim loadC hloadV wpC hwpV v σ hσ hζs hload hwp true true
  have hvalid : ∀ i ∈ (tzrelC : List (OInstr (Wire a m r K) (OWire k l f))),
      IsUnitary (teval (m := m) (r := r) (K := K) (f := f) v σ i) := by
    intro i hi
    simp only [tzrelC, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · rw [GateODE.Time.teval_wprep]
      exact GateODE.Time.wprep_isUnitary σ hσ false
    · rw [GateODE.Time.teval_load]
      exact GateODE.Time.psel_isUnitary _ (fun x => GateODE.adjIf_isUnitary _ _ (hσ.load _))
    · rw [GateODE.Time.teval_wprep]
      exact GateODE.Time.wprep_isUnitary σ hσ true
  have hprepV := tzprepC_valid (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) loadC hloadV wpC hwpV
  rw [tzprepC_eq_flatMap] at hprepV
  have hmacroV : ∀ i ∈ (tzrelC : List (OInstr (Wire a m r K) (OWire k l f))),
      ∀ j ∈ (tzmacro (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) loadC wpC i), j.Valid :=
    fun i hi j hj => hprepV j (List.mem_flatMap.mpr ⟨i, hi, hj⟩)
  have h := macro_flatMap_approx prim hprim (tzmacro loadC wpC)
    (teval (m := m) (r := r) (K := K) (f := f) v σ) (fun _ => ζs) tzrelC hw hvalid hmacroV
    (fun _ _ => hζs)
  have hsum : ((tzrelC : List (OInstr (Wire a m r K) (OWire k l f))).map
      (fun _ => ζs)).sum = 3 * ζs := by
    simp only [tzrelC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    ring
  rw [← tzprepC_eq_flatMap, prodOps_teval, hsum] at h
  exact h

end Approx

/-! ### The decoded vector of the released counterpart -/

section Decoded

variable {a m r K k l f : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The configuration carrying the source label of a word of the source-label wires. -/
abbrev srcCfg (c : Cfg (Fin (k + 1))) : Cfg (AW a m r K k l f) :=
  cfgOf ((c 0, Fin.tail c), fun _ => false)

theorem srcCfg_injective :
    Function.Injective (srcCfg (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)) := by
  intro c c' h
  have h1 := GateODE.cfgOf_injective h
  have h2 : ((c 0, Fin.tail c) : Bool × (Fin k → Bool)) = (c' 0, Fin.tail c') :=
    congrArg Prod.fst h1
  have e : (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).symm c =
      (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).symm c' := h2
  exact (Fin.consEquiv (fun _ : Fin (k + 1) => Bool)).symm.injective e

/-- The weight preparation on the clean configuration. -/
theorem wprep_zero (σ : TOracles a k l P) (u : P) :
    wprep (m := m) (r := r) (K := K) (f := f) σ false (bas (fun _ => false) u) =
      ∑ c, σ.Wp c (fun _ => false) • bas (srcCfg c) u := by
  unfold wprep
  simp only [Bool.false_eq_true, if_false]
  rw [GateODE.Time.localOp_matOp_bas]
  apply Finset.sum_congr rfl
  intro c _
  rw [GateODE.Time.overwrite_src_zero]

/-- The coordinate at the clean configuration of the inverse weight preparation. -/
theorem wprep_adj_apply_zero (σ : TOracles a k l P) (ψ : Reg (AW a m r K k l f) P) :
    wprep (m := m) (r := r) (K := K) (f := f) σ true ψ (fun _ => false) =
      ∑ c, star (σ.Wp c (fun _ => false)) • ψ (srcCfg c) := by
  unfold wprep
  simp only [if_true]
  rw [localOp_apply, matOp_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [Matrix.conjTranspose_apply, slice_apply, GateODE.Time.overwrite_src_zero]

/-- **The clean decoded vector of the released time-dependent zero-case preparation**:
`∑_c |Wp_{c,0}|² J_{(c₀, tail c)} v`. -/
theorem tzrelC_decoded (v : P) (σ : TOracles a k l P) :
    (goodF†) (trun (m := m) (r := r) (K := K) (f := f) v σ tzrelC (GateODE.seedState v)) =
      ∑ c : Cfg (Fin (k + 1)),
        (star (σ.Wp c (fun _ => false)) * σ.Wp c (fun _ => false)) • σ.J (c 0, Fin.tail c) v := by
  have hload : ∀ (c : Cfg (Fin (k + 1))) (u : P),
      teval (m := m) (r := r) (K := K) (f := f) v σ (.src false false) (bas (srcCfg c) u) =
        bas (srcCfg c) (σ.J (c 0, Fin.tail c) u) := by
    intro c u
    rw [GateODE.Time.teval_load, GateODE.Time.psel_bas]
    rfl
  have hcoord : ∀ c : Cfg (Fin (k + 1)),
      (∑ c', σ.Wp c' (fun _ => false) •
        bas (srcCfg (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) c')
          (σ.J (c' 0, Fin.tail c') v)) (srcCfg c) =
        σ.Wp c (fun _ => false) • σ.J (c 0, Fin.tail c) v := by
    intro c
    rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      simp only [WithLp.ofLp_smul, Pi.smul_apply, bas_apply]
      rw [if_neg (fun h => hc' (srcCfg_injective h).symm), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ c) h
  simp only [tzrelC, GateODE.Time.trun_cons, GateODE.Time.trun_nil, comp_apply,
    one_apply_eq_self, GateODE.Time.teval_wprep, GateODE.seedState]
  rw [wprep_zero, map_sum]
  simp only [map_smul, hload]
  rw [goodF, GateODE.basL_adjoint_apply, wprep_adj_apply_zero]
  apply Finset.sum_congr rfl
  intro c _
  rw [hcoord, smul_smul]

end Decoded

end

end SparseHamiltonian.ZeroTimeGateODE
