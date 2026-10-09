import GateEfficientHamiltonian.Circuit.Instr

/-!
# Clean flags and many-controlled gates

Basis-column formulas for the single-wire operations, reversible classical
gate lists as maps of configurations, and the transfer principle used for
every flag computation: a gate controlled by flags agrees, on clean inputs,
with the ideal gate controlled by the predicates those flags hold.

The AND-chain `mcGate` implements a gate controlled by any number `k ≥ 1` of
literals with `2k - 1` elementary gates (each touching at most three wires)
and `k - 1` clean flags, which are returned clean.
-/

namespace SparseHamiltonian.GateCircuit

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-! ### Basis columns -/

omit [Fintype W] in
theorem update_eq_iff (x y : Cfg W) (t : W) (b : Bool) :
    Function.update y t b = x ↔ (b = x t ∧ Function.update y t false = Function.update x t false) := by
  constructor
  · intro h
    subst h
    refine ⟨by simp, ?_⟩
    funext w
    by_cases hw : w = t
    · subst hw; simp
    · simp [Function.update_of_ne hw]
  · rintro ⟨hb, h⟩
    funext w
    by_cases hw : w = t
    · subst hw; simp [hb]
    · have := congrFun h w
      simpa [Function.update_of_ne hw] using this

theorem condOp_bas (t : W) (u : Cfg W → Matrix Bool Bool ℂ) (x : Cfg W) (q : Q) :
    condOp t u (bas x q) =
      ∑ b : Bool, u (Function.update x t false) b (x t) • bas (Function.update x t b) q := by
  apply PiLp.ext
  intro y
  rw [condOp_apply, WithLp.ofLp_sum]
  simp only [Finset.sum_apply, bas_apply, WithLp.ofLp_smul, Pi.smul_apply]
  by_cases hy : Function.update y t false = Function.update x t false
  · have hl : ∀ b, (Function.update y t b = x) ↔ b = x t := by
      intro b; rw [update_eq_iff]; simp [hy]
    have hr : ∀ b, (y = Function.update x t b) ↔ b = y t := by
      intro b
      rw [eq_comm, update_eq_iff]; simp [hy]
    simp only [hl, hr, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq' Finset.univ (x t), Finset.sum_ite_eq' Finset.univ (y t)]
    simp [hy]
  · have hl : ∀ b, ¬ (Function.update y t b = x) := by
      intro b h; rw [update_eq_iff] at h; exact hy h.2
    have hr : ∀ b, ¬ (y = Function.update x t b) := by
      intro b h; rw [eq_comm, update_eq_iff] at h; exact hy h.2.symm
    simp [hl, hr]

theorem gateOp_bas (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ)
    (ht : ∀ c ∈ cs, c.1 ≠ t) (x : Cfg W) (q : Q) :
    gateOp cs t u (bas x q) = if ctrlOK cs x then
      ∑ b : Bool, u b (x t) • bas (Function.update x t b) q else bas x q := by
  rw [gateOp, condOp_bas, ctrlOK_update cs t ht]
  split_ifs
  · rfl
  · rw [Finset.sum_eq_single (x t)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h

theorem gateOp_pauliX_bas (cs : List (W × Bool)) (t : W) (ht : ∀ c ∈ cs, c.1 ≠ t)
    (x : Cfg W) (q : Q) : gateOp cs t pauliX (bas x q) = bas (flipCfg cs t x) q := by
  rw [gateOp_pauliX cs t ht]
  apply PiLp.ext
  intro y
  rw [permOp_apply]
  simp only [bas_apply]
  have : (flipEquiv cs t ht).symm y = x ↔ y = flipCfg cs t x := by
    constructor
    · intro h; rw [← h]; exact (flipCfg_flipCfg cs t ht y).symm
    · intro h; rw [h]; exact flipCfg_flipCfg cs t ht x
  simp only [this]

/-! ### Reversible classical gate lists -/

/-- A list of controlled NOT gates, each target off its own controls. -/
def Classical (gs : List (Gate W)) : Prop :=
  ∀ g ∈ gs, g.u = pauliX ∧ ∀ c ∈ g.cs, c.1 ≠ g.t

/-- The configuration map of a classical gate list. -/
def cfgRun : List (Gate W) → Cfg W → Cfg W
  | [], x => x
  | g :: gs, x => cfgRun gs (flipCfg g.cs g.t x)

omit [Fintype W] in
theorem cfgRun_append (gs hs : List (Gate W)) (x : Cfg W) :
    cfgRun (gs ++ hs) x = cfgRun hs (cfgRun gs x) := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

omit [Fintype W] [DecidableEq W] in
theorem classical_append {gs hs : List (Gate W)} (h₁ : Classical gs) (h₂ : Classical hs) :
    Classical (gs ++ hs) := by
  intro g hg
  rcases List.mem_append.mp hg with h | h
  · exact h₁ g h
  · exact h₂ g h

theorem gRun_classical_bas (gs : List (Gate W)) (hgs : Classical gs) (x : Cfg W) (q : Q) :
    gRun gs (bas x q) = bas (cfgRun gs x) q := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      rw [gRun_cons, comp_apply]
      obtain ⟨hu, ht⟩ := hgs g List.mem_cons_self
      have hg : g.op (bas x q) = bas (flipCfg g.cs g.t x) q := by
        rw [Gate.op, hu]
        exact gateOp_pauliX_bas g.cs g.t ht x q
      rw [hg, ih (fun h hh => hgs h (List.mem_cons_of_mem g hh))]
      rfl

omit [Fintype W] in
theorem flipCfg_update (cs : List (W × Bool)) (f t : W) (hf : f ≠ t)
    (hc : ∀ c ∈ cs, c.1 ≠ t) (x : Cfg W) (b : Bool) :
    flipCfg cs f (Function.update x t b) = Function.update (flipCfg cs f x) t b := by
  unfold flipCfg
  rw [ctrlOK_update cs t hc]
  split_ifs
  · rw [Function.update_of_ne hf, Function.update_comm hf]
  · rfl

omit [Fintype W] in
/-- A classical list commutes with updates of a wire it neither reads nor writes. -/
theorem cfgRun_update (gs : List (Gate W)) (t : W)
    (ht : ∀ g ∈ gs, g.t ≠ t ∧ ∀ c ∈ g.cs, c.1 ≠ t) (x : Cfg W) (b : Bool) :
    cfgRun gs (Function.update x t b) = Function.update (cfgRun gs x) t b := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      obtain ⟨h1, h2⟩ := ht g List.mem_cons_self
      simp only [cfgRun]
      rw [flipCfg_update g.cs g.t t h1 h2]
      exact ih (fun h hh => ht h (List.mem_cons_of_mem g hh)) _

omit [Fintype W] in
/-- A classical list leaves every wire it does not target unchanged. -/
theorem cfgRun_apply_of_not_target (gs : List (Gate W)) (w : W)
    (hw : ∀ g ∈ gs, g.t ≠ w) (x : Cfg W) : cfgRun gs x w = x w := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
      simp only [cfgRun]
      rw [ih (fun h hh => hw h (List.mem_cons_of_mem g hh))]
      unfold flipCfg
      split_ifs
      · rw [Function.update_of_ne (Ne.symm (hw g List.mem_cons_self))]
      · rfl

/-! ### Gate lists and unitarity -/

/-- Every gate in the list has a unitary matrix. -/
def AllUnitary (gs : List (Gate W)) : Prop := ∀ g ∈ gs, UnitaryMat g.u

theorem gRun_isUnitary (gs : List (Gate W)) (h : AllUnitary gs) :
    IsUnitary (gRun (Q := Q) gs) := by
  induction gs with
  | nil => exact isUnitary_one
  | cons g gs ih =>
      rw [gRun_cons, ← mul_def]
      exact (ih (fun h' hh => h h' (List.mem_cons_of_mem g hh))).mul
        (gateOp_isUnitary g.cs g.t g.u (h g List.mem_cons_self))

omit [Fintype W] [DecidableEq W] in
theorem classical_allUnitary {gs : List (Gate W)} (h : Classical gs) : AllUnitary gs := by
  intro g hg
  rw [(h g hg).1]
  exact pauliX_unitary

theorem gRun_gInv_comp (gs : List (Gate W)) (h : AllUnitary gs) :
    gRun (Q := Q) (gInv gs) ∘L gRun gs = 1 := by
  rw [gRun_gInv]
  have := (gRun_isUnitary (Q := Q) gs h).1
  rwa [star_eq_adjoint, mul_def] at this

/-! ### The transfer principle -/

/-- A gate controlled by literals that, after the basis map `f`, hold exactly the
ideal predicate `pred`, agrees with the ideal controlled gate. -/
theorem gate_after_map (S : Cfg W → Prop) (C : Reg W Q →L[ℂ] Reg W Q) (f : Cfg W → Cfg W)
    (cs : List (W × Bool)) (t : W) (u : Matrix Bool Bool ℂ) (ht : ∀ c ∈ cs, c.1 ≠ t)
    (pred : Cfg W → Bool)
    (hC : ∀ x, S x → ∀ q, C (bas x q) = bas (f x) q)
    (hSt : ∀ x b, S x → S (Function.update x t b))
    (hft : ∀ x b, S x → f (Function.update x t b) = Function.update (f x) t b)
    (hctrl : ∀ x, S x → ctrlOK cs (f x) = pred x)
    (hpred : ∀ x b, pred (Function.update x t b) = pred x) :
    Agrees S (gateOp cs t u ∘L C) (C ∘L condOp t (fun x => if pred x then u else 1)) := by
  apply agrees_of_bas
  intro x hx q
  rw [comp_apply, comp_apply, hC x hx, condOp_bas, map_sum, gateOp_bas cs t u ht, hctrl x hx]
  have hfx : f x t = x t := by
    have h := hft x (x t) hx
    rw [Function.update_eq_self] at h
    have h2 := congrFun h t
    rw [Function.update_self] at h2
    exact h2
  simp only [map_smul, hpred]
  cases hpx : pred x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_eq_single (x t)]
    · rw [Function.update_eq_self, hC x hx]; simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [↓reduceIte]
    apply Finset.sum_congr rfl
    intro b _
    rw [hC _ (hSt x b hx), hft x b hx, hfx]

/-! ### The AND chain -/

/-- Flag `fᵢ` receives the conjunction of the previous literal and `lᵢ`. -/
def andChain : (W × Bool) → List (W × Bool) → List W → List (Gate W)
  | _, [], _ => []
  | _, _ :: _, [] => []
  | p, l :: ls, f :: fs => ⟨[p, l], f, pauliX⟩ :: andChain (f, true) ls fs

/-- The literal holding the whole conjunction after the chain. -/
def andLast : (W × Bool) → List (W × Bool) → List W → (W × Bool)
  | p, [], _ => p
  | p, _ :: _, [] => p
  | _, _ :: ls, f :: fs => andLast (f, true) ls fs

/-- A literal holds in a configuration. -/
abbrev litOK (l : W × Bool) (x : Cfg W) : Bool := x l.1 == l.2

omit [Fintype W] [DecidableEq W] in
theorem andChain_length (p : W × Bool) (ls : List (W × Bool)) (fl : List W)
    (h : ls.length ≤ fl.length) : (andChain p ls fl).length = ls.length := by
  induction ls generalizing p fl with
  | nil => rfl
  | cons l ls ih =>
      cases fl with
      | nil => simp at h
      | cons f fs =>
          simp only [andChain, List.length_cons]
          rw [ih (f, true) fs (by simpa using h)]

omit [Fintype W] [DecidableEq W] in
theorem andChain_classical (p : W × Bool) (ls : List (W × Bool)) (fl : List W)
    (hp : ∀ f ∈ fl, p.1 ≠ f) (hl : ∀ l ∈ ls, ∀ f ∈ fl, l.1 ≠ f) (hnd : fl.Nodup) :
    Classical (andChain p ls fl) := by
  induction ls generalizing p fl with
  | nil => intro g hg; simp [andChain] at hg
  | cons l ls ih =>
      cases fl with
      | nil => intro g hg; simp [andChain] at hg
      | cons f fs =>
          intro g hg
          simp only [andChain, List.mem_cons] at hg
          rcases hg with rfl | hg
          · refine ⟨rfl, ?_⟩
            intro c hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact hp f List.mem_cons_self
            · exact hl c List.mem_cons_self f List.mem_cons_self
          · have hnd' := (List.nodup_cons.mp hnd)
            apply ih (f, true) fs
            · intro f' hf' heq
              have h : f = f' := heq
              exact hnd'.1 (h ▸ hf')
            · intro l' hl' f' hf'
              exact hl l' (List.mem_cons_of_mem l hl') f' (List.mem_cons_of_mem f hf')
            · exact hnd'.2
            · exact hg

omit [Fintype W] [DecidableEq W] in
/-- Wires touched by the chain are exactly its flags. -/
theorem andChain_targets (p : W × Bool) (ls : List (W × Bool)) (fl : List W)
    (g : Gate W) (hg : g ∈ andChain p ls fl) : g.t ∈ fl := by
  induction ls generalizing p fl with
  | nil => simp [andChain] at hg
  | cons l ls ih =>
      cases fl with
      | nil => simp [andChain] at hg
      | cons f fs =>
          simp only [andChain, List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem f (ih (f, true) fs hg)

omit [Fintype W] [DecidableEq W] in
theorem andChain_controls (p : W × Bool) (ls : List (W × Bool)) (fl : List W)
    (g : Gate W) (hg : g ∈ andChain p ls fl) (c : W × Bool) (hc : c ∈ g.cs) :
    c.1 = p.1 ∨ c.1 ∈ fl ∨ ∃ l ∈ ls, c.1 = l.1 := by
  induction ls generalizing p fl with
  | nil => simp [andChain] at hg
  | cons l ls ih =>
      cases fl with
      | nil => simp [andChain] at hg
      | cons f fs =>
          simp only [andChain, List.mem_cons] at hg
          rcases hg with rfl | hg
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inr ⟨c, List.mem_cons_self, rfl⟩)
          · rcases ih (f, true) fs hg with h | h | ⟨l', hl', h⟩
            · exact Or.inr (Or.inl (h ▸ List.mem_cons_self))
            · exact Or.inr (Or.inl (List.mem_cons_of_mem f h))
            · exact Or.inr (Or.inr ⟨l', List.mem_cons_of_mem l hl', h⟩)

omit [Fintype W] in
/-- On clean flags the chain leaves its conjunction on the last literal. -/
theorem andChain_last (p : W × Bool) (ls : List (W × Bool)) (fl : List W)
    (hlen : ls.length ≤ fl.length)
    (hp : ∀ f ∈ fl, p.1 ≠ f) (hl : ∀ l ∈ ls, ∀ f ∈ fl, l.1 ≠ f) (hnd : fl.Nodup)
    (x : Cfg W) (hx : ∀ f ∈ fl, x f = false) :
    litOK (andLast p ls fl) (cfgRun (andChain p ls fl) x) = (litOK p x && ctrlOK ls x) := by
  induction ls generalizing p fl x with
  | nil => simp [andChain, andLast, cfgRun, ctrlOK]
  | cons l ls ih =>
      cases fl with
      | nil => simp at hlen
      | cons f fs =>
          have hnd' := List.nodup_cons.mp hnd
          have hstep : cfgRun (andChain p (l :: ls) (f :: fs)) x =
              cfgRun (andChain (f, true) ls fs) (flipCfg [p, l] f x) := rfl
          have hlast : andLast p (l :: ls) (f :: fs) = andLast (f, true) ls fs := rfl
          rw [hstep, hlast]
          have hxf : x f = false := hx f List.mem_cons_self
          have hctrl2 : ctrlOK [p, l] x = (litOK p x && litOK l x) := by
            simp only [ctrlOK_cons, ctrlOK_nil, Bool.and_true, litOK]
          have hfx : flipCfg [p, l] f x f = (litOK p x && litOK l x) := by
            rw [← hctrl2]
            unfold flipCfg
            cases hc : ctrlOK [p, l] x
            · simp only [Bool.false_eq_true, ↓reduceIte, hxf]
            · simp only [↓reduceIte, Function.update_self, hxf, Bool.not_false]
          have hxw : ∀ w, w ≠ f → flipCfg [p, l] f x w = x w := by
            intro w hw
            unfold flipCfg
            split_ifs
            · rw [Function.update_of_ne hw]
            · rfl
          have hfs : ∀ f' ∈ fs, flipCfg [p, l] f x f' = false := by
            intro f' hf'
            have hne : f' ≠ f := fun h => hnd'.1 (h ▸ hf')
            rw [hxw f' hne]
            exact hx f' (List.mem_cons_of_mem f hf')
          have hrec := ih (f, true) fs (by simpa using hlen)
            (fun f' hf' heq => by
              have h : f = f' := heq
              exact hnd'.1 (h ▸ hf'))
            (fun l' hl' f' hf' => hl l' (List.mem_cons_of_mem l hl') f'
              (List.mem_cons_of_mem f hf'))
            hnd'.2 (flipCfg [p, l] f x) hfs
          rw [hrec]
          have hls : ctrlOK ls (flipCfg [p, l] f x) = ctrlOK ls x := by
            apply Bool.eq_iff_iff.mpr
            rw [ctrlOK_iff, ctrlOK_iff]
            constructor
            · intro h c hc
              rw [← hxw c.1 (hl c (List.mem_cons_of_mem l hc) f List.mem_cons_self)]
              exact h c hc
            · intro h c hc
              rw [hxw c.1 (hl c (List.mem_cons_of_mem l hc) f List.mem_cons_self)]
              exact h c hc
          rw [hls, ctrlOK_cons]
          have h1 : litOK (f, true) (flipCfg [p, l] f x) = (litOK p x && litOK l x) := by
            simp only [litOK, hfx, beq_true]
          rw [h1]
          simp only [litOK, Bool.and_assoc]

/-- A gate controlled by any nonempty list of literals, implemented by an
AND chain on clean flags. -/
def mcGate (ls : List (W × Bool)) (fl : List W) (t : W) (u : Matrix Bool Bool ℂ) :
    List (Gate W) :=
  match ls with
  | [] => [⟨[], t, u⟩]
  | l :: ls' => andChain l ls' fl ++ [⟨[andLast l ls' fl], t, u⟩] ++ gInv (andChain l ls' fl)

omit [Fintype W] [DecidableEq W] in
theorem mcGate_length_le (ls : List (W × Bool)) (fl : List W) (t : W) (u : Matrix Bool Bool ℂ) :
    (mcGate ls fl t u).length ≤ 2 * ls.length + 1 := by
  have key : ∀ (p : W × Bool) (ls' : List (W × Bool)) (fl : List W),
      (andChain p ls' fl).length ≤ ls'.length := by
    intro p ls' fl
    induction ls' generalizing p fl with
    | nil => simp [andChain]
    | cons l ls ih =>
        cases fl with
        | nil => simp [andChain]
        | cons f fs => simp only [andChain, List.length_cons]; have := ih (f, true) fs; omega
  cases ls with
  | nil => simp [mcGate]
  | cons l ls' =>
      simp only [mcGate, List.length_append, gInv_length, List.length_cons, List.length_nil]
      have := key l ls' fl
      omega

/-- Correctness of the many-controlled gate on clean flags. -/
theorem mcGate_agrees (ls : List (W × Bool)) (fl : List W) (t : W) (u : Matrix Bool Bool ℂ)
    (hlen : ls.length ≤ fl.length + 1) (hnd : fl.Nodup)
    (hlt : ∀ l ∈ ls, l.1 ≠ t) (hft : ∀ f ∈ fl, f ≠ t)
    (hlf : ∀ l ∈ ls, ∀ f ∈ fl, l.1 ≠ f)
    (S : Cfg W → Prop) (hS : ∀ x, S x → ∀ f ∈ fl, x f = false)
    (hSt : ∀ x b, S x → S (Function.update x t b)) :
    Agrees S (gRun (Q := Q) (mcGate ls fl t u)) (gateOp ls t u) := by
  cases ls with
  | nil =>
      intro ψ _
      simp only [mcGate]
      rw [gRun_singleton]
      rfl
  | cons l ls' =>
      simp only [mcGate]
      set ch := andChain l ls' fl
      have hcl : Classical ch := andChain_classical l ls' fl
        (fun f hf => hlf l List.mem_cons_self f hf)
        (fun l' hl' f hf => hlf l' (List.mem_cons_of_mem l hl') f hf) hnd
      have hlast : (andLast l ls' fl).1 ≠ t := by
        have key : ∀ (p : W × Bool) (ls'' : List (W × Bool)) (fl' : List W),
            p.1 ≠ t → (∀ f ∈ fl', f ≠ t) → (andLast p ls'' fl').1 ≠ t := by
          intro p ls'' fl' hp hf
          induction ls'' generalizing p fl' with
          | nil => exact hp
          | cons l'' ls'' ih =>
              cases fl' with
              | nil => exact hp
              | cons f fs =>
                  exact ih (f, true) fs (hf f List.mem_cons_self)
                    (fun f' hf' => hf f' (List.mem_cons_of_mem f hf'))
        exact key l ls' fl (hlt l List.mem_cons_self) hft
      have hchain_t : ∀ g ∈ ch, g.t ≠ t ∧ ∀ c ∈ g.cs, c.1 ≠ t := by
        intro g hg
        refine ⟨hft _ (andChain_targets l ls' fl g hg), ?_⟩
        intro c hc
        rcases andChain_controls l ls' fl g hg c hc with h | h | ⟨l', hl', h⟩
        · rw [h]; exact hlt l List.mem_cons_self
        · exact hft _ h
        · rw [h]; exact hlt l' (List.mem_cons_of_mem l hl')
      have hmain := gate_after_map (Q := Q) S (gRun ch) (cfgRun ch) [andLast l ls' fl] t u
        (by intro c hc; simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rw [hc]; exact hlast)
        (ctrlOK (l :: ls'))
        (fun x _ q => gRun_classical_bas ch hcl x q) hSt
        (fun x b _ => cfgRun_update ch t hchain_t x b)
        (by
          intro x hx
          have h := andChain_last l ls' fl (by simpa using hlen)
            (fun f hf => hlf l List.mem_cons_self f hf)
            (fun l' hl' f hf => hlf l' (List.mem_cons_of_mem l hl') f hf) hnd x (hS x hx)
          simp only [ctrlOK_cons, ctrlOK_nil, Bool.and_true]
          simpa [litOK] using h)
        (fun x b => ctrlOK_update (l :: ls') t hlt x b)
      intro ψ hψ
      rw [gRun_append, gRun_append, comp_apply, comp_apply, gRun_singleton]
      change gRun (gInv ch) ((gateOp [andLast l ls' fl] t u ∘L gRun ch) ψ) = _
      rw [hmain ψ hψ, comp_apply]
      have hinv := gRun_gInv_comp (Q := Q) ch (classical_allUnitary hcl)
      have := congrArg (fun F : Reg W Q →L[ℂ] Reg W Q => F
        (condOp t (fun x => if ctrlOK (l :: ls') x then u else 1) ψ)) hinv
      simp only [comp_apply] at this
      rw [this]
      rfl

end

end SparseHamiltonian.GateCircuit
