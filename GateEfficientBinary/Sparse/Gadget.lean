import GateEfficientNative.Native.Private

/-!
# Controlled oracle calls from uncontrolled ones

Primitive oracle calls are never controlled in the native gate model. This file shows that the
standard gadget nevertheless applies the operator `G` of a call on a target register `T` exactly
when a control wire `c` has the value `pol`.

On the inactive branch `c = !pol`, a controlled swap (`cswapG`: one Fredkin gate per wire, each
a CNOT, a Toffoli and a CNOT gate) exchanges the target register with a clean dummy register
`Dm`. The call therefore acts on the clean input `0` and writes its image, the basis state `y₀`,
into the target register. The reference register `Rf`, which holds `y₀`, is XOR-ed into the
target register under the same control (`cxorG`), which clears it again, and a second controlled
swap restores the target register and returns the dummy register clean. On the active branch
`c = pol` the swaps and the XOR are switched off, so the call acts as `G`.

* `cfgRun_fredkinG`: a Fredkin gate swaps its two wires exactly when its control literal holds;
* `cfgRun_gadget_inactive`: the bookkeeping of configurations on the inactive branch;
* `gadget_agrees`: on states whose dummy register is clean and whose reference register holds
  `y₀`, the gadget acts as `G` controlled on `c = pol`;
* `gadget_preserves`, `gadget_valid`, `gadget_nGates`, `gadget_nCalls`: the controlled
  operator keeps such states, the gates of the gadget are elementary, and the gadget uses
  `7 |E|` elementary gates and no calls besides those of the call.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateODE (put put_apply bas_eq_put overwrite_apply_ι overwrite_apply_out)

variable {V E Y J : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- A Fredkin gate: swap the wires `a` and `b` when the wire `c` has the value `pol`, as a
CNOT, a Toffoli and a CNOT gate. -/
def fredkinG (c : V) (pol : Bool) (a b : V) : List (Gate V) :=
  [⟨[(b, true)], a, pauliX⟩, ⟨[(c, pol), (a, true)], b, pauliX⟩, ⟨[(b, true)], a, pauliX⟩]

/-- Swap the registers `T` and `Dm` when the wire `c` has the value `pol`. -/
def cswapG (c : V) (pol : Bool) (T Dm : E → V) : List (Gate V) :=
  (Finset.univ : Finset E).toList.flatMap (fun e => fredkinG c pol (T e) (Dm e))

/-- XOR the register `Rf` into the register `T` when the wire `c` has the value `pol`. -/
def cxorG (c : V) (pol : Bool) (Rf T : E → V) : List (Gate V) :=
  (Finset.univ : Finset E).toList.map (fun e => ⟨[(c, pol), (Rf e, true)], T e, pauliX⟩)

/-- The controlled-call gadget: on the inactive branch (`c = !pol`) the target register `T`
is exchanged with a clean dummy register `Dm` before and after the call, and the oracle
image `y₀` of the clean input, held in the reference register `Rf`, is XOR-ed away. -/
def gadget (c : V) (pol : Bool) (T Dm Rf : E → V) (call : List (NInstr V Y J)) :
    List (NInstr V Y J) :=
  nGatesOf (cswapG c (!pol) T Dm) ++ call ++ nGatesOf (cxorG c (!pol) Rf T) ++
    nGatesOf (cswapG c (!pol) T Dm)

/-! ### The Fredkin gate -/

omit [Fintype V] in
/-- A Fredkin gate swaps the wires `a` and `b` exactly when its control literal holds. -/
theorem cfgRun_fredkinG (c : V) (p : Bool) (a b : V) (hab : a ≠ b) (hca : c ≠ a)
    (x : Cfg V) (w : V) :
    cfgRun (fredkinG c p a b) x w =
      if x c = p then (if w = a then x b else if w = b then x a else x w) else x w := by
  simp only [fredkinG, cfgRun, Sim.flipCfg_eq_update, ctrlOK_cons, ctrlOK_nil, Bool.and_true,
    beq_true, Function.update_apply, hab, hab.symm, hca, ↓reduceIte]
  by_cases hp : x c = p
  · simp only [hp, beq_self_eq_true, Bool.true_and, ↓reduceIte]
    split_ifs <;> cases x a <;> cases x b <;> rfl
  · have hp' : (x c == p) = false := by simpa using hp
    simp only [hp', Bool.false_and, Bool.xor_false, ↓reduceIte, hp]
    split_ifs with h1 h2 <;> (try rw [h1]) <;> (try rw [h2]) <;> cases x a <;> cases x b <;> rfl

omit [Fintype V] [DecidableEq V] in
/-- The targets of a Fredkin gate are its two swapped wires. -/
theorem fredkinG_target {c : V} {p : Bool} {a b : V} {g : Gate V} (hg : g ∈ fredkinG c p a b) :
    g.t = a ∨ g.t = b := by
  simp only [fredkinG, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-! ### Exchanging two registers -/

section Swap

variable (c : V) (p : Bool) (T Dm : E → V)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The swap gates over a list of indices leave every wire outside both registers unchanged. -/
theorem cfgRun_swapList_out (l : List E) (x : Cfg V) (w : V) (hTw : ∀ e ∈ l, T e ≠ w)
    (hDw : ∀ e ∈ l, Dm e ≠ w) :
    cfgRun (l.flatMap (fun i => fredkinG c p (T i) (Dm i))) x w = x w := by
  apply cfgRun_apply_of_not_target
  intro g hg
  obtain ⟨e, he, hg⟩ := List.mem_flatMap.mp hg
  rcases fredkinG_target hg with h | h <;> rw [h]
  · exact hTw e he
  · exact hDw e he

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- When the control literal fails, the swap gates act as the identity. -/
theorem cfgRun_swapList_of_ne (hTD : ∀ e, T e ≠ Dm e) (hcT : ∀ e, T e ≠ c) (l : List E)
    (x : Cfg V) (hx : x c ≠ p) :
    cfgRun (l.flatMap (fun i => fredkinG c p (T i) (Dm i))) x = x := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      rw [List.flatMap_cons, cfgRun_append]
      have h1 : cfgRun (fredkinG c p (T e) (Dm e)) x = x := by
        funext w
        rw [cfgRun_fredkinG c p _ _ (hTD e) (hcT e).symm, if_neg hx]
      rw [h1, ih]

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- When the control literal holds, the swap gates over a list of distinct indices exchange
the two registers on these indices. -/
theorem cfgRun_swapList_eq (hT : Function.Injective T) (hDm : Function.Injective Dm)
    (hTD : ∀ e e', T e ≠ Dm e') (hcT : ∀ e, T e ≠ c) (hcD : ∀ e, Dm e ≠ c) (l : List E)
    (hl : l.Nodup) (x : Cfg V) (hx : x c = p) :
    (∀ e ∈ l, cfgRun (l.flatMap (fun i => fredkinG c p (T i) (Dm i))) x (T e) = x (Dm e)) ∧
      ∀ e ∈ l, cfgRun (l.flatMap (fun i => fredkinG c p (T i) (Dm i))) x (Dm e) = x (T e) := by
  induction l generalizing x with
  | nil => simp
  | cons e l ih =>
      obtain ⟨hel, hl'⟩ := List.nodup_cons.mp hl
      have hne : ∀ e' ∈ l, e' ≠ e := fun e' he' h => hel (h ▸ he')
      have hx1 : ∀ w, cfgRun (fredkinG c p (T e) (Dm e)) x w =
          if w = T e then x (Dm e) else if w = Dm e then x (T e) else x w := by
        intro w
        rw [cfgRun_fredkinG c p _ _ (hTD e e) (hcT e).symm, if_pos hx]
      have hx1c : cfgRun (fredkinG c p (T e) (Dm e)) x c = p := by
        rw [hx1, if_neg (hcT e).symm, if_neg (hcD e).symm, hx]
      obtain ⟨ih1, ih2⟩ := ih hl' _ hx1c
      simp only [List.flatMap_cons, cfgRun_append]
      refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
      · rcases List.mem_cons.mp he' with h | he'
        · rw [h, cfgRun_swapList_out c p T Dm l _ _ (fun e'' he'' h' => hne e'' he'' (hT h'))
            (fun e'' _ h' => hTD e e'' h'.symm), hx1, if_pos rfl]
        · rw [ih1 e' he', hx1, if_neg (fun h => hTD e e' h.symm),
            if_neg (fun h => hne e' he' (hDm h))]
      · rcases List.mem_cons.mp he' with h | he'
        · rw [h, cfgRun_swapList_out c p T Dm l _ _ (fun e'' _ h' => hTD e'' e h')
            (fun e'' he'' h' => hne e'' he'' (hDm h')), hx1, if_neg (fun h' => hTD e e h'.symm),
            if_pos rfl]
        · rw [ih2 e' he', hx1, if_neg (fun h => hne e' he' (hT h)), if_neg (fun h => hTD e' e h)]

omit [Fintype V] [DecidableEq E] in
/-- The controlled swap leaves every wire outside both registers unchanged. -/
theorem cfgRun_cswapG_out (x : Cfg V) (w : V) (hTw : ∀ e, T e ≠ w) (hDw : ∀ e, Dm e ≠ w) :
    cfgRun (cswapG c p T Dm) x w = x w :=
  cfgRun_swapList_out c p T Dm _ x w (fun e _ => hTw e) (fun e _ => hDw e)

omit [Fintype V] [DecidableEq E] in
/-- When the control literal fails, the controlled swap acts as the identity. -/
theorem cfgRun_cswapG_of_ne (hTD : ∀ e e', T e ≠ Dm e') (hcT : ∀ e, T e ≠ c) (x : Cfg V)
    (hx : x c ≠ p) : cfgRun (cswapG c p T Dm) x = x :=
  cfgRun_swapList_of_ne c p T Dm (fun e => hTD e e) hcT _ x hx

omit [Fintype V] [DecidableEq E] in
/-- When the control literal holds, the controlled swap moves `Dm` into `T`. -/
theorem cfgRun_cswapG_T (hT : Function.Injective T) (hDm : Function.Injective Dm)
    (hTD : ∀ e e', T e ≠ Dm e') (hcT : ∀ e, T e ≠ c) (hcD : ∀ e, Dm e ≠ c) (x : Cfg V)
    (hx : x c = p) (e : E) : cfgRun (cswapG c p T Dm) x (T e) = x (Dm e) :=
  (cfgRun_swapList_eq c p T Dm hT hDm hTD hcT hcD _ (Finset.nodup_toList _) x hx).1 e
    (Finset.mem_toList.mpr (Finset.mem_univ e))

omit [Fintype V] [DecidableEq E] in
/-- When the control literal holds, the controlled swap moves `T` into `Dm`. -/
theorem cfgRun_cswapG_Dm (hT : Function.Injective T) (hDm : Function.Injective Dm)
    (hTD : ∀ e e', T e ≠ Dm e') (hcT : ∀ e, T e ≠ c) (hcD : ∀ e, Dm e ≠ c) (x : Cfg V)
    (hx : x c = p) (e : E) : cfgRun (cswapG c p T Dm) x (Dm e) = x (T e) :=
  (cfgRun_swapList_eq c p T Dm hT hDm hTD hcT hcD _ (Finset.nodup_toList _) x hx).2 e
    (Finset.mem_toList.mpr (Finset.mem_univ e))

end Swap

/-! ### XOR-ing one register into another -/

section Xor

variable (c : V) (p : Bool) (Rf T : E → V)

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- The XOR gates over a list of indices leave every wire outside the target register
unchanged. -/
theorem cfgRun_xorList_out (l : List E) (x : Cfg V) (w : V) (hTw : ∀ e ∈ l, T e ≠ w) :
    cfgRun (l.map (fun i => (⟨[(c, p), (Rf i, true)], T i, pauliX⟩ : Gate V))) x w = x w := by
  apply cfgRun_apply_of_not_target
  intro g hg
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hg
  exact hTw e he

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- When the control literal fails, the XOR gates act as the identity. -/
theorem cfgRun_xorList_of_ne (l : List E) (x : Cfg V) (hx : x c ≠ p) :
    cfgRun (l.map (fun i => (⟨[(c, p), (Rf i, true)], T i, pauliX⟩ : Gate V))) x = x := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      have h1 : flipCfg [(c, p), (Rf e, true)] (T e) x = x := by
        unfold flipCfg
        rw [if_neg]
        simp [ctrlOK, hx]
      rw [List.map_cons]
      change cfgRun _ (flipCfg [(c, p), (Rf e, true)] (T e) x) = x
      rw [h1, ih]

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- When the control literal holds, the XOR gates over a list of distinct indices add the
source register to the target register on these indices. -/
theorem cfgRun_xorList_eq (hT : Function.Injective T) (hTR : ∀ e e', T e ≠ Rf e')
    (hcT : ∀ e, T e ≠ c) (l : List E) (hl : l.Nodup) (x : Cfg V) (hx : x c = p) :
    ∀ e ∈ l, cfgRun (l.map (fun i => (⟨[(c, p), (Rf i, true)], T i, pauliX⟩ : Gate V))) x
      (T e) = (x (T e) ^^ x (Rf e)) := by
  induction l generalizing x with
  | nil => simp
  | cons e l ih =>
      obtain ⟨hel, hl'⟩ := List.nodup_cons.mp hl
      have hne : ∀ e' ∈ l, e' ≠ e := fun e' he' h => hel (h ▸ he')
      have hx1 : flipCfg [(c, p), (Rf e, true)] (T e) x =
          Function.update x (T e) (x (T e) ^^ x (Rf e)) := by
        rw [Sim.flipCfg_eq_update]
        simp [ctrlOK, hx]
      have hx1c : Function.update x (T e) (x (T e) ^^ x (Rf e)) c = p := by
        rw [Function.update_of_ne (hcT e).symm, hx]
      intro e' he'
      rw [List.map_cons]
      change cfgRun _ (flipCfg [(c, p), (Rf e, true)] (T e) x) (T e') = _
      rw [hx1]
      rcases List.mem_cons.mp he' with h | he'
      · rw [h, cfgRun_xorList_out c p Rf T l _ _ (fun e'' he'' h' => hne e'' he'' (hT h')),
          Function.update_self]
      · rw [ih hl' _ hx1c e' he', Function.update_of_ne (fun h => hne e' he' (hT h)),
          Function.update_of_ne (fun h => hTR e e' h.symm)]

omit [Fintype V] [DecidableEq E] in
/-- The controlled XOR leaves every wire outside the target register unchanged. -/
theorem cfgRun_cxorG_out (x : Cfg V) (w : V) (hTw : ∀ e, T e ≠ w) :
    cfgRun (cxorG c p Rf T) x w = x w :=
  cfgRun_xorList_out c p Rf T _ x w (fun e _ => hTw e)

omit [Fintype V] [DecidableEq E] in
/-- When the control literal fails, the controlled XOR acts as the identity. -/
theorem cfgRun_cxorG_of_ne (x : Cfg V) (hx : x c ≠ p) : cfgRun (cxorG c p Rf T) x = x :=
  cfgRun_xorList_of_ne c p Rf T _ x hx

omit [Fintype V] [DecidableEq E] in
/-- When the control literal holds, the controlled XOR adds `Rf` to `T`. -/
theorem cfgRun_cxorG_T (hT : Function.Injective T) (hTR : ∀ e e', T e ≠ Rf e')
    (hcT : ∀ e, T e ≠ c) (x : Cfg V) (hx : x c = p) (e : E) :
    cfgRun (cxorG c p Rf T) x (T e) = (x (T e) ^^ x (Rf e)) :=
  cfgRun_xorList_eq c p Rf T hT hTR hcT _ (Finset.nodup_toList _) x hx e
    (Finset.mem_toList.mpr (Finset.mem_univ e))

end Xor

/-! ### Elementary gates and gate counts -/

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- Every gate of the controlled swap is a NOT gate with at most two controls, all off the
target. -/
theorem cnot_of_mem_cswapG (c : V) (p : Bool) (T Dm : E → V) (hTD : ∀ e e', T e ≠ Dm e')
    (hcD : ∀ e, Dm e ≠ c) (g : Gate V) (hg : g ∈ cswapG c p T Dm) :
    g.u = pauliX ∧ g.cs.length ≤ 2 ∧ ∀ l ∈ g.cs, l.1 ≠ g.t := by
  simp only [cswapG, List.mem_flatMap, fredkinG, List.mem_cons, List.not_mem_nil,
    or_false] at hg
  obtain ⟨e, _, rfl | rfl | rfl⟩ := hg
  · refine ⟨rfl, by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [hl]
    exact (hTD e e).symm
  · refine ⟨rfl, by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact (hcD e).symm
    · exact hTD e e
  · refine ⟨rfl, by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rw [hl]
    exact (hTD e e).symm

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- Every gate of the controlled XOR is a NOT gate with two controls, both off the target. -/
theorem cnot_of_mem_cxorG (c : V) (p : Bool) (Rf T : E → V) (hTR : ∀ e e', T e ≠ Rf e')
    (hcT : ∀ e, T e ≠ c) (g : Gate V) (hg : g ∈ cxorG c p Rf T) :
    g.u = pauliX ∧ g.cs.length ≤ 2 ∧ ∀ l ∈ g.cs, l.1 ≠ g.t := by
  simp only [cxorG, List.mem_map] at hg
  obtain ⟨e, _, rfl⟩ := hg
  refine ⟨rfl, by simp, fun l hl => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · exact (hcT e).symm
  · exact (hTR e e).symm

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The controlled swap is a reversible classical gate list. -/
theorem classical_cswapG (c : V) (p : Bool) (T Dm : E → V) (hTD : ∀ e e', T e ≠ Dm e')
    (hcD : ∀ e, Dm e ≠ c) : Classical (cswapG c p T Dm) := fun g hg =>
  ⟨(cnot_of_mem_cswapG c p T Dm hTD hcD g hg).1, (cnot_of_mem_cswapG c p T Dm hTD hcD g hg).2.2⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The controlled XOR is a reversible classical gate list. -/
theorem classical_cxorG (c : V) (p : Bool) (Rf T : E → V) (hTR : ∀ e e', T e ≠ Rf e')
    (hcT : ∀ e, T e ≠ c) : Classical (cxorG c p Rf T) := fun g hg =>
  ⟨(cnot_of_mem_cxorG c p Rf T hTR hcT g hg).1, (cnot_of_mem_cxorG c p Rf T hTR hcT g hg).2.2⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The gates of the controlled swap are elementary. -/
theorem gateOK_cswapG (c : V) (p : Bool) (T Dm : E → V) (hTD : ∀ e e', T e ≠ Dm e')
    (hcD : ∀ e, Dm e ≠ c) : ∀ g ∈ cswapG c p T Dm, GateOK 3 g := fun g hg => by
  obtain ⟨hu, hl, hc⟩ := cnot_of_mem_cswapG c p T Dm hTD hcD g hg
  exact ⟨by omega, hc, by rw [hu]; exact pauliX_unitary⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The gates of the controlled XOR are elementary. -/
theorem gateOK_cxorG (c : V) (p : Bool) (Rf T : E → V) (hTR : ∀ e e', T e ≠ Rf e')
    (hcT : ∀ e, T e ≠ c) : ∀ g ∈ cxorG c p Rf T, GateOK 3 g := fun g hg => by
  obtain ⟨hu, hl, hc⟩ := cnot_of_mem_cxorG c p Rf T hTR hcT g hg
  exact ⟨by omega, hc, by rw [hu]; exact pauliX_unitary⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The controlled swap uses three gates per wire. -/
theorem length_cswapG (c : V) (p : Bool) (T Dm : E → V) :
    (cswapG c p T Dm).length = 3 * Fintype.card E := by
  simp [cswapG, fredkinG, List.length_flatMap, mul_comm]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The controlled XOR uses one gate per wire. -/
theorem length_cxorG (c : V) (p : Bool) (Rf T : E → V) :
    (cxorG c p Rf T).length = Fintype.card E := by
  simp [cxorG]

/-! ### Correctness of the gadget -/

/-- The wire layout of the gadget: the target register `T` and the dummy register `Dm` are
injective, the registers `T`, `Dm` and the reference register `Rf` are pairwise disjoint, and
`T` and `Dm` avoid the control wire `c`. -/
structure GadgetLayout (c : V) (T Dm Rf : E → V) : Prop where
  inj_T : Function.Injective T
  inj_Dm : Function.Injective Dm
  T_ne_Dm : ∀ e e', T e ≠ Dm e'
  T_ne_Rf : ∀ e e', T e ≠ Rf e'
  Dm_ne_Rf : ∀ e e', Dm e ≠ Rf e'
  T_ne_c : ∀ e, T e ≠ c
  Dm_ne_c : ∀ e, Dm e ≠ c

omit [Fintype V] [DecidableEq E] in
/-- The configurations of the inactive branch. Starting from a configuration with a clean dummy
register and the reference register holding `y₀`, the swap, writing `y₀` into the (now clean)
target register, the XOR of the reference register and the second swap restore the
configuration. -/
theorem cfgRun_gadget_inactive {c : V} {T Dm Rf : E → V} (hL : GadgetLayout c T Dm Rf)
    (p : Bool) (y0 : Cfg E) (x : Cfg V) (hx : x c = p) (hxD : ∀ e, x (Dm e) = false)
    (hxR : ∀ e, x (Rf e) = y0 e) :
    cfgRun (cswapG c p T Dm) (cfgRun (cxorG c p Rf T)
      (overwrite T (cfgRun (cswapG c p T Dm) x) y0)) = x := by
  set x1 := cfgRun (cswapG c p T Dm) x with hx1
  set x2 := overwrite T x1 y0 with hx2
  set x3 := cfgRun (cxorG c p Rf T) x2 with hx3
  have h1c : x1 c = p := by
    rw [hx1, cfgRun_cswapG_out c p T Dm x c hL.T_ne_c hL.Dm_ne_c, hx]
  have h2c : x2 c = p := by
    rw [hx2, overwrite_apply_out T x1 y0 c hL.T_ne_c, h1c]
  have h3c : x3 c = p := by
    rw [hx3, cfgRun_cxorG_out c p Rf T x2 c hL.T_ne_c, h2c]
  funext w
  by_cases hwT : ∃ e, T e = w
  · obtain ⟨e, rfl⟩ := hwT
    rw [cfgRun_cswapG_T c p T Dm hL.inj_T hL.inj_Dm hL.T_ne_Dm hL.T_ne_c hL.Dm_ne_c x3 h3c e,
      hx3, cfgRun_cxorG_out c p Rf T x2 (Dm e) (fun e' => hL.T_ne_Dm e' e), hx2,
      overwrite_apply_out T x1 y0 (Dm e) (fun e' => hL.T_ne_Dm e' e), hx1,
      cfgRun_cswapG_Dm c p T Dm hL.inj_T hL.inj_Dm hL.T_ne_Dm hL.T_ne_c hL.Dm_ne_c x hx e]
  · by_cases hwD : ∃ e, Dm e = w
    · obtain ⟨e, rfl⟩ := hwD
      rw [cfgRun_cswapG_Dm c p T Dm hL.inj_T hL.inj_Dm hL.T_ne_Dm hL.T_ne_c hL.Dm_ne_c x3 h3c e,
        hx3, cfgRun_cxorG_T c p Rf T hL.inj_T hL.T_ne_Rf hL.T_ne_c x2 h2c e, hx2,
        overwrite_apply_ι hL.inj_T,
        overwrite_apply_out T x1 y0 (Rf e) (fun e' => hL.T_ne_Rf e' e), hx1,
        cfgRun_cswapG_out c p T Dm x (Rf e) (fun e' => hL.T_ne_Rf e' e)
          (fun e' => hL.Dm_ne_Rf e' e), hxR e, hxD e, Bool.xor_self]
    · simp only [not_exists] at hwT hwD
      rw [cfgRun_cswapG_out c p T Dm x3 w hwT hwD, hx3, cfgRun_cxorG_out c p Rf T x2 w hwT, hx2,
        overwrite_apply_out T x1 y0 w hwT, hx1, cfgRun_cswapG_out c p T Dm x w hwT hwD]

/-- A classical gate list fixing every configuration of `S` acts as the identity on
`S`-supported vectors. -/
theorem agrees_one_of_cfgRun (gs : List (Gate V)) (hgs : Classical gs) (S : Cfg V → Prop)
    (h : ∀ y, S y → cfgRun gs y = y) : Agrees S (gRun (Q := R) gs) 1 := by
  apply agrees_of_bas
  intro y hy q
  rw [gRun_classical_bas gs hgs y q, h y hy, one_apply_eq_self]

omit [CompleteSpace R] in
/-- A vector placed on the exposed wires at the outside configuration of `x` is supported on
the configurations that agree with `x` on a given outside wire `w`. -/
theorem supp_put_out {T : E → V} (hT : Function.Injective T) (x : Cfg V) (ψ : Reg E R) (w : V)
    (hw : ∀ e, T e ≠ w) : Supp (fun y => y w = x w) (put T hT x ψ) := by
  intro y hy
  rw [put_apply, if_neg]
  intro h
  exact hy (congrFun h ⟨w, hw⟩)

/-- **The controlled-call gadget.** If the call acts as the operator `G` on the target
register, and `G` maps the clean input to the basis state `y₀` with untouched payload, then
on states whose dummy register is clean and whose reference register holds `y₀`, the gadget
acts as `G` controlled on `c = pol`. -/
theorem gadget_agrees (prim : J → Reg Y R →L[ℂ] Reg Y R) (G : Reg E R →L[ℂ] Reg E R)
    (y0 : Cfg E) (hG0 : ∀ q, G (bas (fun _ => false) q) = bas y0 q)
    (c : V) (pol : Bool) (T Dm Rf : E → V) (hT : Function.Injective T)
    (hDm : Function.Injective Dm)
    (hTD : ∀ e e', T e ≠ Dm e') (hTR : ∀ e e', T e ≠ Rf e') (hDR : ∀ e e', Dm e ≠ Rf e')
    (hcT : ∀ e, T e ≠ c) (hcD : ∀ e, Dm e ≠ c)
    (call : List (NInstr V Y J)) (hcall : nrun prim call = localOp T hT (fun _ => G)) :
    Agrees (fun x => (∀ e, x (Dm e) = false) ∧ ∀ e, x (Rf e) = y0 e)
      (nrun prim (gadget c pol T Dm Rf call))
      (localOp T hT (fun x => if x c = pol then G else 1)) := by
  have hL : GadgetLayout c T Dm Rf := ⟨hT, hDm, hTD, hTR, hDR, hcT, hcD⟩
  have hA := classical_cswapG c (!pol) T Dm hTD hcD
  have hX := classical_cxorG c (!pol) Rf T hTR hcT
  have hrun : nrun prim (gadget c pol T Dm Rf call) =
      gRun (cswapG c (!pol) T Dm) ∘L gRun (cxorG c (!pol) Rf T) ∘L
        localOp T hT (fun _ => G) ∘L gRun (cswapG c (!pol) T Dm) := by
    simp only [gadget, nrun_append, nrun_nGatesOf, hcall]
  rw [hrun]
  apply agrees_of_bas
  rintro x ⟨hxD, hxR⟩ q
  simp only [comp_apply]
  rw [localOp_bas hT (fun x => if x c = pol then G else 1)]
  beta_reduce
  rw [clearCfg_apply_out T x c hcT]
  by_cases hxc : x c = pol
  · -- Active branch: the swaps and the XOR are switched off around the call.
    have hS : ∀ y : Cfg V, y c = x c → y c ≠ !pol := by
      intro y hy
      rw [hy, hxc]
      exact Bool.self_ne_not pol
    rw [if_pos hxc, gRun_classical_bas _ hA x q,
      cfgRun_cswapG_of_ne c (!pol) T Dm hTD hcT x (hS x rfl), localOp_bas hT (fun _ => G) x q]
    beta_reduce
    have hsupp := supp_put_out hT x (G (bas (fun e => x (T e)) q)) c hcT
    rw [agrees_one_of_cfgRun _ hX (fun y => y c = x c)
        (fun y hy => cfgRun_cxorG_of_ne c (!pol) Rf T y (hS y hy)) _ hsupp, one_apply_eq_self,
      agrees_one_of_cfgRun _ hA (fun y => y c = x c)
        (fun y hy => cfgRun_cswapG_of_ne c (!pol) T Dm hTD hcT y (hS y hy)) _ hsupp,
      one_apply_eq_self]
  · -- Inactive branch: the call acts on the clean dummy register and writes `y₀`.
    have hx' : x c = !pol := Bool.eq_not_of_ne hxc
    rw [if_neg hxc, one_apply_eq_self, ← bas_eq_put hT x q, gRun_classical_bas _ hA x q,
      localOp_bas hT (fun _ => G)]
    beta_reduce
    have h0 : (fun e => cfgRun (cswapG c (!pol) T Dm) x (T e)) = fun _ => false := by
      funext e
      rw [cfgRun_cswapG_T c (!pol) T Dm hT hDm hTD hcT hcD x hx' e, hxD e]
    rw [h0, hG0 q, put_bas hT, gRun_classical_bas _ hX, gRun_classical_bas _ hA,
      cfgRun_gadget_inactive hL (!pol) y0 x hx' hxD hxR]

/-- The controlled operator preserves clean dummies and references. -/
theorem gadget_preserves (G : Reg E R →L[ℂ] Reg E R) (y0 : Cfg E) (c : V) (pol : Bool)
    (T Dm Rf : E → V) (hT : Function.Injective T)
    (hTD : ∀ e e', T e ≠ Dm e') (hTR : ∀ e e', T e ≠ Rf e') :
    Preserves (fun x => (∀ e, x (Dm e) = false) ∧ ∀ e, x (Rf e) = y0 e)
      (localOp T hT (fun x => if x c = pol then G else 1) : Reg V R →L[ℂ] Reg V R) := by
  apply preserves_localOp
  rintro y b ⟨hyD, hyR⟩
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rw [overwrite_apply_out T y b (Dm e) (fun e' => hTD e' e)]
    exact hyD e
  · rw [overwrite_apply_out T y b (Rf e) (fun e' => hTR e' e)]
    exact hyR e

/-! ### Validity and costs -/

omit [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype Y] [DecidableEq Y] in
/-- The gates of the gadget are elementary. -/
theorem gadget_valid (c : V) (pol : Bool) (T Dm Rf : E → V) (hTD : ∀ e e', T e ≠ Dm e')
    (hTR : ∀ e e', T e ≠ Rf e') (hcT : ∀ e, T e ≠ c) (hcD : ∀ e, Dm e ≠ c)
    (call : List (NInstr V Y J)) (hcv : ∀ i ∈ call, i.Valid) :
    ∀ i ∈ gadget c pol T Dm Rf call, i.Valid := by
  intro i hi
  simp only [gadget, List.mem_append] at hi
  rcases hi with ((h | h) | h) | h
  · exact valid_nGatesOf _ (gateOK_cswapG c (!pol) T Dm hTD hcD) i h
  · exact hcv i h
  · exact valid_nGatesOf _ (gateOK_cxorG c (!pol) Rf T hTR hcT) i h
  · exact valid_nGatesOf _ (gateOK_cswapG c (!pol) T Dm hTD hcD) i h

omit [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype Y] [DecidableEq Y] in
/-- Counts: `7 |E|` gates besides the call. -/
theorem gadget_nGates (c : V) (pol : Bool) (T Dm Rf : E → V) (call : List (NInstr V Y J)) :
    nGatesN (gadget c pol T Dm Rf call) = nGatesN call + 7 * Fintype.card E := by
  simp only [gadget, nGatesN_append, nGatesN_nGatesOf, length_cswapG, length_cxorG]
  ring

omit [Fintype V] [DecidableEq V] [DecidableEq E] [Fintype Y] [DecidableEq Y] in
/-- The gadget makes exactly the calls of `call`. -/
theorem gadget_nCalls (p : J → Bool) (c : V) (pol : Bool) (T Dm Rf : E → V)
    (call : List (NInstr V Y J)) :
    nCallsN p (gadget c pol T Dm Rf call) = nCallsN p call := by
  simp only [gadget, nCallsN_append, nCallsN_nGatesOf, zero_add, add_zero]

end

end SparseHamiltonian.GateBinary
