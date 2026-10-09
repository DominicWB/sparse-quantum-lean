import GateEfficientODE.Gadgets.Uniform

/-!
# Wires, labels and clean configurations of the solver

Besides the wires `Wire a m r K` of the released simulator, the solver has

* `ini`: the source sector (`false` initial state, `true` forcing);
* `src i`, `i < k`: the quadrature node word (`2^k` nodes);
* `lch j`, `j < l`: the LCHS label word (`2^l` labels);
* `flg`: one flag, and `pool i`, `i < f`: clean flags for AND chains.

The label of a configuration is read from `ini`, `src` and `lch`
(`labOf`); `cfgOf z` is the configuration carrying the label `z` with every
other wire clear.  `WorkClean` states that the flag and the pool are clear.
-/

namespace SparseHamiltonian.GateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire anc_injective)
open scoped InnerProduct BigOperators

/-- The solver wires. -/
inductive OWire (k l f : ℕ)
  | ini
  | src (i : Fin k)
  | lch (i : Fin l)
  | flg
  | pool (i : Fin f)
  deriving DecidableEq, Fintype

/-- All wires: simulator wires and solver wires. -/
abbrev AW (a m r K k l f : ℕ) := Wire a m r K ⊕ OWire k l f

variable {a m r K k l f : ℕ}

/-- The work wires of the solver. -/
def OWire.isWork : OWire k l f → Bool
  | .flg => true
  | .pool _ => true
  | _ => false

/-- The flag and the pool are clear. -/
def WorkClean (x : Cfg (AW a m r K k l f)) : Prop :=
  ∀ o : OWire k l f, o.isWork = true → x (Sum.inr o) = false

/-- The pool is clear. -/
def PoolClean (x : Cfg (AW a m r K k l f)) : Prop :=
  ∀ i : Fin f, x (Sum.inr (OWire.pool i)) = false

theorem poolClean_of_workClean {x : Cfg (AW a m r K k l f)} (hx : WorkClean x) :
    PoolClean x := fun i => hx (.pool i) rfl

/-- The pool as a list of wires. -/
def poolList : List (AW a m r K k l f) :=
  (List.finRange f).map (fun i => Sum.inr (OWire.pool i))

theorem mem_poolList (w : AW a m r K k l f) : w ∈ poolList ↔ ∃ i, w = Sum.inr (OWire.pool i) := by
  simp only [poolList, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩

theorem poolList_nodup : (poolList (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f)).Nodup := by
  unfold poolList
  refine (List.nodup_finRange f).map ?_
  intro i j h
  cases h
  rfl

theorem poolList_length : (poolList (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f)).length = f := by
  simp [poolList]

theorem poolClean_iff (x : Cfg (AW a m r K k l f)) :
    PoolClean x ↔ ∀ w ∈ poolList, x w = false := by
  constructor
  · intro h w hw
    obtain ⟨i, rfl⟩ := (mem_poolList w).mp hw
    exact h i
  · intro h i
    exact h _ ((mem_poolList _).mpr ⟨i, rfl⟩)

/-! ### Labels -/

/-- Labels: the source sector, the quadrature node word and the LCHS word. -/
abbrev Label (k l : ℕ) := (Bool × (Fin k → Bool)) × (Fin l → Bool)

/-- The label carried by a configuration of the solver wires. -/
def labOf (y : Cfg (OWire k l f)) : Label k l :=
  ((y .ini, fun i => y (.src i)), fun j => y (.lch j))

/-- The configuration carrying a label, every other wire clear. -/
def cfgOf (z : Label k l) : Cfg (AW a m r K k l f)
  | Sum.inl _ => false
  | Sum.inr .ini => z.1.1
  | Sum.inr (.src i) => z.1.2 i
  | Sum.inr (.lch j) => z.2 j
  | Sum.inr .flg => false
  | Sum.inr (.pool _) => false

@[simp] theorem labOf_cfgOf (z : Label k l) :
    labOf (fun o => cfgOf (a := a) (m := m) (r := r) (K := K) (f := f) z (Sum.inr o)) = z := by
  rfl

@[simp] theorem cfgOf_inl (z : Label k l) (s : Wire a m r K) :
    cfgOf (f := f) z (Sum.inl s) = false := rfl

theorem workClean_cfgOf (z : Label k l) :
    WorkClean (cfgOf (a := a) (m := m) (r := r) (K := K) (f := f) z) := by
  intro o ho
  cases o <;> first | rfl | (simp [OWire.isWork] at ho)

theorem cfgOf_injective :
    Function.Injective (cfgOf (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)) := by
  intro z z' h
  have := congrArg (fun x : Cfg (AW a m r K k l f) => labOf (fun o => x (Sum.inr o))) h
  simpa using this

theorem outPart_cfgOf_injective (z z' : Label k l)
    (h : outPart Sum.inl (cfgOf (a := a) (m := m) (r := r) (K := K) (f := f) z) =
      outPart Sum.inl (cfgOf z')) : z = z' := by
  have hw : ∀ o : OWire k l f, cfgOf (a := a) (m := m) (r := r) (K := K) (f := f) z (Sum.inr o) =
      cfgOf (a := a) (m := m) (r := r) (K := K) (f := f) z' (Sum.inr o) := by
    intro o
    have := congrFun h ⟨Sum.inr o, fun s hs => by cases hs⟩
    exact this
  have := congrArg labOf (funext hw)
  simpa using this

/-- The zero configuration carries the zero label. -/
theorem cfgOf_zero :
    cfgOf (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      ((false, fun _ => false), fun _ => false) = fun _ => false := by
  funext w
  rcases w with s | o
  · rfl
  · cases o <;> rfl

/-- The wiring of the solver for a public seed vector. -/
def wiring {P : Type*} (v : P) : Wiring (Wire a m r K) (OWire k l f) a (Label k l) P :=
  ⟨Wire.anc, anc_injective, .ini, labOf, v⟩

/-! ### Tree registers -/

/-- The LCHS label wires. -/
def lchTS : Fin l → AW a m r K k l f := fun j => Sum.inr (OWire.lch j)

theorem lchTS_injective : Function.Injective (lchTS (a := a) (m := m) (r := r) (K := K) (k := k)
    (l := l) (f := f)) := by
  intro i j h
  cases h
  rfl

/-- The LCHS label register with the pool. -/
def lchTree : TreePool (AW a m r K k l f) l := ⟨lchTS, poolList⟩

theorem lchTree_ok (hl : l ≤ f + 1) :
    (lchTree (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)).OK WorkClean where
  inj := lchTS_injective
  nodup := poolList_nodup
  len := by rw [lchTree, poolList_length]; exact hl
  disj := by
    intro i w hw
    obtain ⟨j, rfl⟩ := (mem_poolList w).mp hw
    intro h
    cases h
  clean := by
    intro x hx w hw
    obtain ⟨j, rfl⟩ := (mem_poolList w).mp hw
    exact hx (.pool j) rfl
  stable := by
    intro x i b hx o ho
    rw [Function.update_of_ne]
    · exact hx o ho
    · intro h
      cases h
      simp [OWire.isWork] at ho

/-- The source label wires: `ini` and the quadrature node word. -/
def srcTS : Fin (k + 1) → AW a m r K k l f :=
  Fin.cases (Sum.inr OWire.ini) (fun i => Sum.inr (OWire.src i))

theorem srcTS_injective : Function.Injective (srcTS (a := a) (m := m) (r := r) (K := K) (k := k)
    (l := l) (f := f)) := by
  intro i j h
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · simp [srcTS] at h
  · simp [srcTS] at h
  · simp only [srcTS, Fin.cases_succ, Sum.inr.injEq, OWire.src.injEq] at h
    rw [h]

end

end SparseHamiltonian.GateODE
