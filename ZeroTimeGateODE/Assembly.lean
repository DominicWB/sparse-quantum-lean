import ZeroTimeGateODE.Certificate
import GateEfficientNative.ODE.Constant

/-!
# Direct source assembly, constant forcing: the circuits

The zero-case preparation of Theorem `ode:thm:gates` (constant coefficients) is the source part
of the released preparation `SRC · LOAD · SRC⁻¹` without the LCHS coefficient register and
without the simulator: on the sector wire `ini` of a native ODE register,

`zprepC u srcC = R(u) · srcC false · srcC true · R(u)ᴴ`,

where `R(u)` is the one-qubit gate `u` on `ini` (for the zero case
`u = srcRot T r₀ r_b = rotC √(r₀/B) √(T r_b/B)`, `B = r₀ + T r_b`, the released source-label
rotation `GateODE.Params.srcMat 0`), and the supplied source circuits `srcC false` (the
initial-state interface `J₀` controlled by `ini = 0`) and `srcC true` (the forcing interface
`J_b` controlled by `ini = 1`) are placed on `ini`, the system and the source scratch by the
released placement `GateNative.srcPl`.  There is no private Cayley call, no `U_J` gate and no
matrix-oracle call besides those the source circuits make: the instructions are two elementary
gates and the instructions of the source circuits.

The released-model counterpart `zrelC u` (two gates and the two released source calls) has the
clean decoded vector `c² J₀ v + s² J_b v` for `u = rotC c s` (`zrelC_decoded`), which is
`(x₀ + T b) / B` under the released source promises (`srcRot_decoded`).  The native circuit is
within `2 ζs` of the lifted released one when both source circuits are within `ζs`
(`zprepC_approx`); its counts are `|srcC 0| + |srcC 1| + 2` gates and exactly the calls of the
source circuits (`zprepC_counts`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Label Oracles wiring adjIf)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-! ### The circuits -/

section Circuits

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}

/-- The rotation of the source sector: first column `(√(r₀/B), √(T r_b/B))`, `B = r₀ + T r_b`;
it is the released source-label rotation `GateODE.Params.srcMat 0` (`srcMat_zero`). -/
def srcRot (T r₀ rb : ℝ) : Matrix Bool Bool ℂ :=
  rotC (Real.sqrt (r₀ / (r₀ + T * rb))) (Real.sqrt (T * rb / (r₀ + T * rb)))

/-- The sector wire `ini` of a native ODE register. -/
def iniN : HWO a m r K k l f S Zs nP Z bT bP A := Sum.inl (Sum.inl (Sum.inr OWire.ini))

/-- **The native zero-case preparation (direct source assembly).**  The gate `u` on `ini`,
the source circuit `srcC false`, the source circuit `srcC true` and the gate `uᴴ` on `ini`;
the source circuits act on `ini`, the system and the source scratch (`srcPl`). -/
def zprepC (u : Matrix Bool Bool ℂ) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J) :=
  [NInstr.gate ⟨[], iniN, u⟩] ++ (srcC false).map (NInstr.map srcPl) ++
    (srcC true).map (NInstr.map srcPl) ++ [NInstr.gate ⟨[], iniN, u.conjTranspose⟩]

/-- The released-model counterpart of `zprepC`: the gate `u` on `ini`, the released calls of the
two source interfaces, and the gate `uᴴ` on `ini`. -/
def zrelC (u : Matrix Bool Bool ℂ) : List (OInstr (Wire a m r K) (OWire k l f)) :=
  [.gate ⟨[], Sum.inr OWire.ini, u⟩, .src false false, .src true false,
    .gate ⟨[], Sum.inr OWire.ini, u.conjTranspose⟩]

/-- The native macros of the released instructions occurring in `zrelC`: an elementary gate by
itself on the released wires, a source call by the placed source circuit or its literal
inverse. -/
def zmacro (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    OInstr (Wire a m r K) (OWire k l f) → List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)
  | .gate g => [NInstr.gate (GateODE.Gate.map (wEmb (S := S) (X' := OX Zs nP) (Z := Z)
      (bT := bT) (bP := bP) (A := A)) g)]
  | .src b adj => (if adj then ninv (srcC b) else srcC b).map (NInstr.map srcPl)
  | _ => []

/-- `zprepC` is the macro substitution of `zrelC`. -/
theorem zprepC_eq_flatMap (u : Matrix Bool Bool ℂ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    (zprepC u srcC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) =
      (zrelC u).flatMap (zmacro srcC) := by
  simp only [zprepC, zrelC, zmacro, List.flatMap_cons, List.flatMap_nil, Bool.false_eq_true,
    if_false, List.append_nil, List.append_assoc]
  rfl

theorem srcRot_unitary (T r₀ rb : ℝ) (hT : 0 ≤ T) (hr₀ : 0 ≤ r₀) (hrb : 0 ≤ rb)
    (hB : 0 < r₀ + T * rb) : UnitaryMat (srcRot T r₀ rb) := by
  apply rotC_unitary
  rw [Real.sq_sqrt (div_nonneg hr₀ hB.le), Real.sq_sqrt (div_nonneg (mul_nonneg hT hrb) hB.le)]
  field_simp

/-- The rotation of the zero case is the released source-label rotation. -/
theorem srcMat_zero (p : GateODE.Params) : p.srcMat 0 = srcRot p.T p.r₀ p.rb := rfl

end Circuits

/-! ### Validity, untouched wires and counts -/

section Public

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}

theorem unitaryMat_conjTranspose {u : Matrix Bool Bool ℂ} (hu : UnitaryMat u) :
    UnitaryMat u.conjTranspose := by
  constructor
  · rw [Matrix.conjTranspose_conjTranspose]; exact hu.2
  · rw [Matrix.conjTranspose_conjTranspose]; exact hu.1

/-- Every instruction of the zero-case preparation is valid. -/
theorem zprepC_valid (u : Matrix Bool Bool ℂ) (hu : UnitaryMat u)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    ∀ i ∈ (zprepC u srcC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)), i.Valid := by
  intro i hi
  simp only [zprepC, List.mem_append, List.mem_singleton] at hi
  rcases hi with ((rfl | hi) | hi) | rfl
  · exact ⟨by simp, by simp, hu⟩
  · exact valid_map_list _ _ (hsrcV false) i hi
  · exact valid_map_list _ _ (hsrcV true) i hi
  · exact ⟨by simp, by simp, unitaryMat_conjTranspose hu⟩

/-- The placed source circuits avoid the native flag and pool. -/
theorem srcPl_not_refl (v : (Unit ⊕ S) ⊕ Zs) :
    ¬ reflWire ((srcPl : (Unit ⊕ S) ⊕ Zs ↪ HWO a m r K k l f S Zs nP Z bT bP A) v) := by
  rcases v with (u | s) | z <;> exact fun h => h

/-- No instruction of the zero-case preparation touches the native flag and pool. -/
theorem zprepC_not_touches (u : Matrix Bool Bool ℂ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    ∀ i ∈ (zprepC u srcC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)),
      ¬ i.Touches reflWire := by
  intro i hi
  simp only [zprepC, List.mem_append, List.mem_singleton, List.mem_map] at hi
  rcases hi with ((rfl | ⟨i', _, rfl⟩) | ⟨i', _, rfl⟩) | rfl
  · exact fun h => h
  · exact NInstr.not_touches_map _ _ srcPl_not_refl i'
  · exact NInstr.not_touches_map _ _ srcPl_not_refl i'
  · exact fun h => h

/-- **The counts of the zero-case preparation**: two gates besides those of the source
circuits, and exactly the primitive calls of the source circuits, of every kind. -/
theorem zprepC_counts (u : Matrix Bool Bool ℂ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (q : J → Bool) :
    nGatesN (zprepC u srcC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) =
      nGatesN (srcC false) + nGatesN (srcC true) + 2 ∧
    nCallsN q (zprepC u srcC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) =
      nCallsN q (srcC false) + nCallsN q (srcC true) := by
  have g1 : nGatesN ([NInstr.gate ⟨[], iniN, u⟩] :
      List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) = 1 := rfl
  have g2 : nGatesN ([NInstr.gate ⟨[], iniN, u.conjTranspose⟩] :
      List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) = 1 := rfl
  have c1 : nCallsN q ([NInstr.gate ⟨[], iniN, u⟩] :
      List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) = 0 := rfl
  have c2 : nCallsN q ([NInstr.gate ⟨[], iniN, u.conjTranspose⟩] :
      List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)) = 0 := rfl
  constructor
  · simp only [zprepC, nGatesN_append, nGatesN_map, g1, g2]
    ring
  · simp only [zprepC, nCallsN_append, nCallsN_map, c1, c2]
    ring

end Public

/-! ### The approximation of the released zero-case preparation -/

section Approx

variable {a m r K k l f : ℕ} {S Zs Z Y J : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y]

/-- The native zero-case preparation never changes the native flag and pool. -/
theorem zprepC_pres (u : Matrix Bool Bool ℂ) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) :
    Pres2 (ZeroOn reflWire)
      (nrun prim (zprepC u srcC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))) :=
  pres2_nrun_zeroOn prim reflWire _ (zprepC_not_touches u srcC)

/-- The macro of a released gate is the lifted gate (exactly, on every input). -/
theorem zmacro_gate (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (g : GateCircuit.Gate (AW a m r K k l f))
    (v : Reg S ℂ) (σ : Oracles a (Label k l) (Reg S ℂ))
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) :
    ApproxOn CleanX
      (nrun prim (zmacro (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) srcC (.gate g)))
      (liftB (conj (OInstr.eval (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
        (f := f) v) σ (.gate g)))) 0 := by
  apply ApproxOn.of_agrees
  have e1 : nrun prim (zmacro (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) srcC (.gate g)) =
      gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
        (Sum.inl (Sum.inl g.t)) g.u := by
    simp only [zmacro, nrun_singleton, NInstr.eval_gate, GateODE.Gate.map, List.map_map]
    rfl
  have e2 : (liftB (X := XW Z bT bP A ⊕ OX Zs nP) (conj (OInstr.eval (wiring (a := a) (m := m)
      (r := r) (K := K) (k := k) (l := l) (f := f) v) σ (.gate g))) :
        Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ →L[ℂ]
          Reg (HWO a m r K k l f S Zs nP Z bT bP A) ℂ) =
      gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
        (Sum.inl (Sum.inl g.t)) g.u := by
    rw [OInstr.eval_gate, conj_gateOp]
    exact GateODE.localOp_gateOp Sum.inl_injective _ _ _
  rw [e1, e2]
  exact Agrees.refl _ _

/-- The macro of a released source call approximates it within the accuracy of the source
circuits. -/
theorem zmacro_src (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid)
    (v : Reg S ℂ) (σ : Oracles a (Label k l) (Reg S ℂ)) (hJ : ∀ c, IsUnitary (σ.J c))
    {ζs : ℝ} (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (σ.J c))) ζs)
    (b adj : Bool) :
    ApproxOn CleanX
      (nrun prim (zmacro (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
        (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) srcC (.src b adj)))
      (liftB (conj (OInstr.eval (wiring v) σ (.src b adj)))) ζs := by
  have hidealU : IsUnitary (liftB (X := Zs) (srcIdeal b (σ.J b))) :=
    liftB_isUnitary (srcIdeal_isUnitary b _ (hJ b))
  have hCU : IsUnitary (nrun prim (srcC b)) := nrun_isUnitary prim hprim _ (hsrcV b)
  have hS : ∀ y : Cfg (HWO a m r K k l f S Zs nP Z bT bP A), CleanX y →
      CleanX (fun c => y ((srcPl (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
        (S := S) (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) c)) := by
    intro y hy z
    exact hy (Sum.inr (Sum.inl z))
  rw [liftB_conj_eval_src, zmacro, nrun_map]
  apply approxOn_localOp _ _ _ hζs hS
  intro _
  cases adj
  · show ApproxOn CleanX (nrun prim (srcC b)) (liftB (srcIdeal b (σ.J b))) ζs
    exact hsrc b
  · show ApproxOn CleanX (nrun prim (ninv (srcC b))) (liftB (srcIdeal b ((σ.J b)†))) ζs
    rw [nrun_ninv, ← srcIdeal_adjoint, liftB_adjoint]
    exact (hsrc b).adjoint hCU hidealU (by rw [← liftB_adjoint]; exact preserves_liftB _)

/-- Substituting native macros `M` for a list of released instructions adds the errors (the
released `approxOn_flatMap`, for any semantics `ev` of the released instructions with the system
as payload). -/
theorem macro_flatMap_approx (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (M : OInstr (Wire a m r K) (OWire k l f) →
      List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (ev : OInstr (Wire a m r K) (OWire k l f) →
      Reg (AW a m r K k l f) (Reg S ℂ) →L[ℂ] Reg (AW a m r K k l f) (Reg S ℂ))
    (δ : OInstr (Wire a m r K) (OWire k l f) → ℝ) (gs : List (OInstr (Wire a m r K) (OWire k l f)))
    (h : ∀ i ∈ gs, ApproxOn CleanX (nrun prim (M i)) (liftB (conj (ev i))) (δ i))
    (hU : ∀ i ∈ gs, IsUnitary (ev i)) (hV : ∀ i ∈ gs, ∀ j ∈ M i, j.Valid)
    (hδ : ∀ i ∈ gs, 0 ≤ δ i) :
    ApproxOn CleanX (nrun prim (gs.flatMap M)) (liftB (conj (prodOps ev gs))) ((gs.map δ).sum) := by
  have h' := approxOn_flatMap prim CleanX M
    (fun i => liftB (X := XW Z bT bP A ⊕ OX Zs nP) (conj (ev i))) δ gs h
    (fun i _ => preserves_liftB _)
    (fun i hi ψ => IsUnitary.norm_apply_le (liftB_isUnitary (conj_isUnitary (hU i hi))) ψ)
    (fun i hi ψ => IsUnitary.norm_apply_le (nrun_isUnitary prim hprim _ (hV i hi)) ψ) hδ
  rw [prodOps_liftB_conj] at h'
  exact h'

/-- **The native zero-case preparation is within `2 ζs` of the lifted released zero-case
preparation**, for any `U_J` and private operations (they are not called), if both source
circuits are within `ζs` of the controlled source interfaces. -/
theorem zprepC_approx (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (hprim : ∀ j, IsUnitary (prim j))
    (u : Matrix Bool Bool ℂ) (hu : UnitaryMat u)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid)
    (v : Reg S ℂ) (σ : Oracles a (Label k l) (Reg S ℂ)) (hJ : ∀ c, IsUnitary (σ.J c))
    {ζs : ℝ} (hζs : 0 ≤ ζs)
    (hsrc : ∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (σ.J c))) ζs) :
    ApproxOn CleanX
      (nrun prim (zprepC u srcC : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J)))
      (liftB (conj (GateODE.run (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
        (f := f) v) σ (zrelC u)))) (2 * ζs) := by
  have hw : ∀ i ∈ (zrelC u : List (OInstr (Wire a m r K) (OWire k l f))),
      ApproxOn CleanX (nrun prim (zmacro (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)
        srcC i)) (liftB (conj (OInstr.eval (wiring (a := a) (m := m) (r := r) (K := K) (k := k)
          (l := l) (f := f) v) σ i))) (if i.isSrc false || i.isSrc true then ζs else 0) := by
    intro i hi
    simp only [zrelC, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact zmacro_gate prim _ v σ srcC
    · exact zmacro_src prim hprim srcC hsrcV v σ hJ hζs hsrc false false
    · exact zmacro_src prim hprim srcC hsrcV v σ hJ hζs hsrc true false
    · exact zmacro_gate prim _ v σ srcC
  have hvalid : ∀ i ∈ (zrelC u : List (OInstr (Wire a m r K) (OWire k l f))),
      IsUnitary (OInstr.eval (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
        (f := f) v) σ i) := by
    intro i hi
    simp only [zrelC, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact gateOp_isUnitary _ _ _ hu
    · exact GateODE.pctl_isUnitary _ _ (GateODE.adjIf_isUnitary _ _ (hJ false))
    · exact GateODE.pctl_isUnitary _ _ (GateODE.adjIf_isUnitary _ _ (hJ true))
    · exact gateOp_isUnitary _ _ _ (unitaryMat_conjTranspose hu)
  have hprepV := zprepC_valid (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) u hu srcC hsrcV
  rw [zprepC_eq_flatMap] at hprepV
  have hmacroV : ∀ i ∈ (zrelC u : List (OInstr (Wire a m r K) (OWire k l f))),
      ∀ j ∈ (zmacro (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A) srcC i), j.Valid :=
    fun i hi j hj => hprepV j (List.mem_flatMap.mpr ⟨i, hi, hj⟩)
  have h := macro_flatMap_approx prim hprim (zmacro srcC)
    (OInstr.eval (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v) σ)
    (fun i => if i.isSrc false || i.isSrc true then ζs else 0) (zrelC u) hw hvalid hmacroV
    (fun i _ => by split_ifs <;> linarith)
  have hsum : ((zrelC u : List (OInstr (Wire a m r K) (OWire k l f))).map
      (fun i => if i.isSrc false || i.isSrc true then ζs else 0)).sum = 2 * ζs := by
    simp only [zrelC, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, OInstr.isSrc]
    simp
    ring
  rw [← zprepC_eq_flatMap, prodOps_oeval, hsum] at h
  exact h

end Approx

/-! ### The decoded vector of the released zero-case preparation -/

section Decoded

variable {a m r K k l f : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The clean configuration with the sector wire set. -/
def iniCfg : Cfg (AW a m r K k l f) := Function.update (fun _ => false) (Sum.inr OWire.ini) true

theorem iniCfg_ne : (iniCfg (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)) ≠
    fun _ => false := by
  intro h
  have := congrFun h (Sum.inr OWire.ini)
  simp [iniCfg] at this

/-- A gate on `ini` applied to the clean configuration. -/
theorem gate_ini_zero (u : Matrix Bool Bool ℂ) (q : P) :
    gateOp [] (Sum.inr OWire.ini) u (bas (fun _ => false : Cfg (AW a m r K k l f)) q) =
      u false false • bas (fun _ => false) q + u true false • bas iniCfg q := by
  rw [gateOp_bas [] _ u (fun c hc => by simp at hc), if_pos (ctrlOK_nil _), Fintype.sum_bool]
  have h0 : Function.update (fun _ => false : Cfg (AW a m r K k l f)) (Sum.inr OWire.ini) false =
      fun _ => false := by
    funext w
    by_cases hw : w = Sum.inr OWire.ini
    · subst hw; simp
    · simp [hw]
  rw [h0]
  unfold iniCfg
  abel

/-- The coordinate of a gate on `ini` at the clean configuration. -/
theorem gate_ini_apply_zero (u : Matrix Bool Bool ℂ) (ψ : Reg (AW a m r K k l f) P) :
    gateOp [] (Sum.inr OWire.ini) u ψ (fun _ => false) =
      u false false • ψ (fun _ => false) + u false true • ψ iniCfg := by
  rw [gateOp_apply [] _ u (fun c hc => by simp at hc), if_pos (ctrlOK_nil _), Fintype.sum_bool]
  have h0 : Function.update (fun _ => false : Cfg (AW a m r K k l f)) (Sum.inr OWire.ini) false =
      fun _ => false := by
    funext w
    by_cases hw : w = Sum.inr OWire.ini
    · subst hw; simp
    · simp [hw]
  rw [h0]
  unfold iniCfg
  abel

/-- **The clean decoded vector of the released zero-case preparation**: for `u = rotC c s`,
`c² J₀ v + s² J_b v`. -/
theorem zrelC_decoded (c s : ℝ) (v : P) (σ : Oracles a (Label k l) P) :
    (goodF†) (GateODE.run (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v)
      σ (zrelC (rotC c s)) (GateODE.seedState v)) =
      ((c ^ 2 : ℝ) : ℂ) • σ.J false v + ((s ^ 2 : ℝ) : ℂ) • σ.J true v := by
  have hne := iniCfg_ne (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
  have hw : (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) v).ini =
      OWire.ini := rfl
  have hc0 : ctrlOK [((Sum.inr OWire.ini : AW a m r K k l f), false)] (fun _ => false) = true := by
    simp [ctrlOK]
  have hc1 : ctrlOK [((Sum.inr OWire.ini : AW a m r K k l f), true)] (fun _ => false) = false := by
    simp [ctrlOK]
  have he0 : ctrlOK [((Sum.inr OWire.ini : AW a m r K k l f), false)] iniCfg = false := by
    simp [ctrlOK, iniCfg]
  have he1 : ctrlOK [((Sum.inr OWire.ini : AW a m r K k l f), true)] iniCfg = true := by
    simp [ctrlOK, iniCfg]
  have h1 : gateOp [] (Sum.inr OWire.ini) (rotC c s)
      (bas (fun _ => false : Cfg (AW a m r K k l f)) v) =
      (c : ℂ) • bas (fun _ => false) v + (s : ℂ) • bas iniCfg v := by
    rw [gate_ini_zero]
    rfl
  have h2 : GateODE.pctl [((Sum.inr OWire.ini : AW a m r K k l f), false)] (σ.J false)
      ((c : ℂ) • bas (fun _ => false) v + (s : ℂ) • bas iniCfg v) =
      (c : ℂ) • bas (fun _ => false) (σ.J false v) + (s : ℂ) • bas iniCfg v := by
    rw [map_add, map_smul, map_smul, GateODE.pctl_bas, GateODE.pctl_bas, hc0, he0]
    simp only [if_true, Bool.false_eq_true, if_false]
  have h3 : GateODE.pctl [((Sum.inr OWire.ini : AW a m r K k l f), true)] (σ.J true)
      ((c : ℂ) • bas (fun _ => false) (σ.J false v) + (s : ℂ) • bas iniCfg v) =
      (c : ℂ) • bas (fun _ => false) (σ.J false v) + (s : ℂ) • bas iniCfg (σ.J true v) := by
    rw [map_add, map_smul, map_smul, GateODE.pctl_bas, GateODE.pctl_bas, hc1, he1]
    simp only [if_true, Bool.false_eq_true, if_false]
  have h4 : (goodF†) (gateOp [] (Sum.inr OWire.ini) (rotC c s).conjTranspose
      ((c : ℂ) • bas (fun _ => false : Cfg (AW a m r K k l f)) (σ.J false v) +
        (s : ℂ) • bas iniCfg (σ.J true v))) =
      ((c ^ 2 : ℝ) : ℂ) • σ.J false v + ((s ^ 2 : ℝ) : ℂ) • σ.J true v := by
    rw [goodF, GateODE.basL_adjoint_apply, gate_ini_apply_zero]
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, bas_apply,
      if_true, if_neg hne, if_neg (Ne.symm hne), smul_zero, add_zero, zero_add,
      Matrix.conjTranspose_apply, rotC, RCLike.star_def, Complex.conj_ofReal, smul_smul]
    push_cast
    ring_nf
  simp only [zrelC, GateODE.run_cons, GateODE.run_nil, comp_apply, one_apply_eq_self,
    OInstr.eval_gate, OInstr.eval_src, GateODE.seedState, hw, GateODE.adjIf, Bool.false_eq_true,
    if_false]
  rw [h1, h2, h3, h4]

end Decoded

end

end SparseHamiltonian.ZeroTimeGateODE
