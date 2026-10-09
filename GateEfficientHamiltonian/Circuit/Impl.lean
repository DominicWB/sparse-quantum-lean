import GateEfficientHamiltonian.Circuit.Amplify

/-!
# Implementation relative to flag annotations

Gate-level circuits compute predicates into clean work wires, use them as
controls, and erase them again.  `Impl S f f' G O` states that the circuit
operator `G` maps the annotated basis state `f x` (work wires holding computed
predicates of `x`) to the image under `f'` of the ideal output `O |x⟩`, for
every configuration `x ∈ S`.  The annotation of a superposition is the linear
map `liftOp f`.  Implementations compose (`Impl.comp`), classical flag
computations change the annotation (`Impl.of_classical`), and a controlled
one-qubit gate whose controls hold the annotated predicate implements the
ideal predicate-controlled rotation (`Impl.gate`).  With identical trivial
annotations, implementation is agreement on `S` (`Impl.toAgrees`).

The many-controlled NOT `mcGate ls fl t pauliX` computes a conjunction into
`t` on clean chain flags (`mcGate_pauliX_bas`), and every gate of a
many-controlled gate has at most two controls (`mcGate_valid`).
-/

namespace SparseHamiltonian.GateCircuit

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-! ### Transport along configuration maps -/

/-- Transport of register vectors along a configuration map. -/
def liftOp (f : Cfg W → Cfg W) : Reg W Q →L[ℂ] Reg W Q :=
  ofCoords (fun z => ∑ y ∈ Finset.univ.filter (fun y => f y = z), coord y)

omit [CompleteSpace Q] in
theorem liftOp_apply (f : Cfg W → Cfg W) (ψ : Reg W Q) (z : Cfg W) :
    liftOp f ψ z = ∑ y ∈ Finset.univ.filter (fun y => f y = z), ψ y := by
  simp [liftOp, ofCoords_apply]

omit [CompleteSpace Q] in
theorem liftOp_bas (f : Cfg W → Cfg W) (x : Cfg W) (q : Q) :
    liftOp f (bas x q) = bas (f x) q := by
  apply PiLp.ext
  intro z
  rw [liftOp_apply, bas_apply]
  simp only [bas_apply]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : f x = z
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

omit [CompleteSpace Q] in
theorem liftOp_id : liftOp (Q := Q) (fun x : Cfg W => x) = 1 :=
  ext_bas_clm _ _ (fun x q => by rw [liftOp_bas]; rfl)

omit [CompleteSpace Q] in
theorem liftOp_congr {S : Cfg W → Prop} {f g : Cfg W → Cfg W} (ψ : Reg W Q) (hψ : Supp S ψ)
    (h : ∀ y, S y → f y = g y) : liftOp f ψ = liftOp g ψ := by
  rw [← sum_bas ψ, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : S y
  · rw [liftOp_bas, liftOp_bas, h y hy]
  · have : bas y (ψ y) = (0 : Reg W Q) := by
      rw [hψ y hy]; apply PiLp.ext; intro z; simp
    rw [this, map_zero, map_zero]

/-! ### Implementation relative to annotations -/

/-- `G` implements `O` on `S`, from annotation `f` to annotation `f'`. -/
def Impl (S : Cfg W → Prop) (f f' : Cfg W → Cfg W) (G O : Reg W Q →L[ℂ] Reg W Q) : Prop :=
  ∀ x, S x → ∀ q, G (bas (f x) q) = liftOp f' (O (bas x q))

omit [CompleteSpace Q] in
theorem Impl.apply {S : Cfg W → Prop} {f f' : Cfg W → Cfg W} {G O : Reg W Q →L[ℂ] Reg W Q}
    (h : Impl S f f' G O) (ψ : Reg W Q) (hψ : Supp S ψ) : G (liftOp f ψ) = liftOp f' (O ψ) := by
  conv_lhs => rw [← sum_bas ψ]
  conv_rhs => rw [← sum_bas ψ]
  rw [map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : S x
  · rw [liftOp_bas, h x hx]
  · have : bas x (ψ x) = (0 : Reg W Q) := by
      rw [hψ x hx]; apply PiLp.ext; intro y; simp
    rw [this]
    simp

omit [CompleteSpace Q] in
theorem Impl.comp {S : Cfg W → Prop} {f f' f'' : Cfg W → Cfg W}
    {G G' O O' : Reg W Q →L[ℂ] Reg W Q}
    (h₁ : Impl S f f' G O) (hO : Preserves S O) (h₂ : Impl S f' f'' G' O') :
    Impl S f f'' (G' ∘L G) (O' ∘L O) := by
  intro x hx q
  rw [comp_apply, h₁ x hx q, h₂.apply _ (hO _ (supp_bas x hx q)), comp_apply]

omit [CompleteSpace Q] in
theorem Impl.of_classical {S : Cfg W → Prop} {f f' : Cfg W → Cfg W} (G : Reg W Q →L[ℂ] Reg W Q)
    (hG : ∀ x, S x → ∀ q, G (bas (f x) q) = bas (f' x) q) : Impl S f f' G 1 := by
  intro x hx q
  rw [hG x hx q, one_apply_eq_self, liftOp_bas]

omit [CompleteSpace Q] in
theorem Impl.one {S : Cfg W → Prop} (f : Cfg W → Cfg W) :
    Impl S f f (1 : Reg W Q →L[ℂ] Reg W Q) 1 :=
  Impl.of_classical 1 (fun _ _ _ => rfl)

omit [CompleteSpace Q] in
theorem Impl.toAgrees {S : Cfg W → Prop} {G O : Reg W Q →L[ℂ] Reg W Q}
    (h : Impl S (fun x => x) (fun x => x) G O) : Agrees S G O := by
  apply agrees_of_bas
  intro x hx q
  rw [h x hx q, liftOp_id]
  rfl

omit [CompleteSpace Q] in
theorem Agrees.toImpl {S : Cfg W → Prop} {G O : Reg W Q →L[ℂ] Reg W Q} (h : Agrees S G O) :
    Impl S (fun x => x) (fun x => x) G O := by
  intro x hx q
  rw [h _ (supp_bas x hx q), liftOp_id]
  rfl

omit [CompleteSpace Q] in
/-- Replace the implementing operator by one that agrees with it on the annotated
configurations. -/
theorem Impl.congr_left {S S' : Cfg W → Prop} {f f' : Cfg W → Cfg W}
    {G G' O : Reg W Q →L[ℂ] Reg W Q} (h : Impl S f f' G O) (hG : Agrees S' G' G)
    (hf : ∀ x, S x → S' (f x)) : Impl S f f' G' O := by
  intro x hx q
  rw [hG _ (supp_bas _ (hf x hx) q), h x hx q]

omit [CompleteSpace Q] in
theorem Impl.congr_ideal {S : Cfg W → Prop} {f f' : Cfg W → Cfg W}
    {G O O' : Reg W Q →L[ℂ] Reg W Q} (h : Impl S f f' G O) (hO : O = O') : Impl S f f' G O' :=
  hO ▸ h

omit [CompleteSpace Q] in
theorem Impl.congr_maps {S : Cfg W → Prop} {f f' g g' : Cfg W → Cfg W}
    {G O : Reg W Q →L[ℂ] Reg W Q} (h : Impl S f f' G O) (hO : Preserves S O)
    (hf : ∀ x, S x → f x = g x) (hf' : ∀ x, S x → f' x = g' x) : Impl S g g' G O := by
  intro x hx q
  rw [← hf x hx, h x hx q]
  exact liftOp_congr _ (hO _ (supp_bas x hx q)) hf'

/-- A controlled gate whose controls hold, on annotated configurations, the
ideal predicate implements the predicate-controlled rotation. -/
theorem Impl.gate {S : Cfg W → Prop} {f : Cfg W → Cfg W} (cs : List (W × Bool)) (t : W)
    (u : Matrix Bool Bool ℂ) (ht : ∀ c ∈ cs, c.1 ≠ t) (pred : Cfg W → Bool)
    (hft : ∀ x b, S x → f (Function.update x t b) = Function.update (f x) t b)
    (hctrl : ∀ x, S x → ctrlOK cs (f x) = pred x)
    (hpred : ∀ x b, pred (Function.update x t b) = pred x) :
    Impl S f f (gateOp (Q := Q) cs t u) (condOp t (fun x => if pred x then u else 1)) := by
  intro x hx q
  rw [condOp_bas, map_sum, gateOp_bas cs t u ht, hctrl x hx]
  have hfx : f x t = x t := by
    have h := hft x (x t) hx
    rw [Function.update_eq_self] at h
    have h2 := congrFun h t
    rw [Function.update_self] at h2
    exact h2
  simp only [map_smul, liftOp_bas, hpred]
  cases hpx : pred x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Finset.sum_eq_single (x t)]
    · rw [Function.update_eq_self]; simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp only [↓reduceIte]
    apply Finset.sum_congr rfl
    intro b _
    rw [hft x b hx, hfx]

/-! ### Many-controlled NOT as a classical step -/

theorem mcGate_pauliX_bas (ls : List (W × Bool)) (fl : List W) (t : W)
    (hlen : ls.length ≤ fl.length + 1) (hnd : fl.Nodup)
    (hlt : ∀ l ∈ ls, l.1 ≠ t) (hft : ∀ f ∈ fl, f ≠ t)
    (hlf : ∀ l ∈ ls, ∀ f ∈ fl, l.1 ≠ f) (x : Cfg W) (hx : ∀ f ∈ fl, x f = false) (q : Q) :
    gRun (mcGate ls fl t pauliX) (bas x q) = bas (flipCfg ls t x) q := by
  have hA := mcGate_agrees (Q := Q) ls fl t pauliX hlen hnd hlt hft hlf
    (fun y => ∀ f ∈ fl, y f = false) (fun y hy => hy)
    (fun y b hy f hf => by rw [Function.update_of_ne (hft f hf)]; exact hy f hf)
  rw [hA (bas x q) (supp_bas (S := fun y => ∀ f ∈ fl, y f = false) x hx q),
    gateOp_pauliX_bas ls t hlt x q]

/-! ### Validity of the gates of a many-controlled gate -/

omit [Fintype W] [DecidableEq W] in
theorem andChain_cs_length (p : W × Bool) (ls : List (W × Bool)) (fl : List W) (g : Gate W)
    (hg : g ∈ andChain p ls fl) : g.cs.length = 2 := by
  induction ls generalizing p fl with
  | nil => simp [andChain] at hg
  | cons l ls ih =>
      cases fl with
      | nil => simp [andChain] at hg
      | cons f fs =>
          simp only [andChain, List.mem_cons] at hg
          rcases hg with rfl | hg
          · rfl
          · exact ih (f, true) fs hg

/-- Elementary validity of a gate: at most `k` controls, all off the target, and
a unitary matrix. -/
def GateOK (k : ℕ) (g : Gate W) : Prop :=
  g.cs.length ≤ k ∧ (∀ c ∈ g.cs, c.1 ≠ g.t) ∧ UnitaryMat g.u

omit [Fintype W] [DecidableEq W] in
theorem GateOK.mono {k k' : ℕ} {g : Gate W} (h : GateOK k g) (hk : k ≤ k') : GateOK k' g :=
  ⟨h.1.trans hk, h.2⟩

omit [Fintype W] [DecidableEq W] in
theorem gateOK_conj {k : ℕ} {g : Gate W} (h : GateOK k g) :
    GateOK k (⟨g.cs, g.t, g.u.conjTranspose⟩ : Gate W) := by
  refine ⟨h.1, h.2.1, ?_⟩
  constructor
  · rw [Matrix.conjTranspose_conjTranspose]; exact h.2.2.2
  · rw [Matrix.conjTranspose_conjTranspose]; exact h.2.2.1

omit [Fintype W] [DecidableEq W] in
theorem gInv_ok {k : ℕ} (gs : List (Gate W)) (h : ∀ g ∈ gs, GateOK k g) :
    ∀ g ∈ gInv gs, GateOK k g := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := mem_gInv gs g hg
  exact gateOK_conj (h g' hg')

omit [Fintype W] [DecidableEq W] in
theorem mcGate_valid (ls : List (W × Bool)) (fl : List W) (t : W) (u : Matrix Bool Bool ℂ)
    (hu : UnitaryMat u) (hnd : fl.Nodup)
    (hlt : ∀ l ∈ ls, l.1 ≠ t) (hft : ∀ f ∈ fl, f ≠ t)
    (hlf : ∀ l ∈ ls, ∀ f ∈ fl, l.1 ≠ f) :
    ∀ g ∈ mcGate ls fl t u, GateOK 2 g := by
  cases ls with
  | nil =>
      intro g hg
      simp only [mcGate, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg
      exact ⟨by simp, by simp, hu⟩
  | cons l ls' =>
      have hcl : Classical (andChain l ls' fl) := andChain_classical l ls' fl
        (fun f hf => hlf l List.mem_cons_self f hf)
        (fun l' hl' f hf => hlf l' (List.mem_cons_of_mem l hl') f hf) hnd
      have hch : ∀ g ∈ andChain l ls' fl, GateOK 2 g := by
        intro g hg
        refine ⟨(andChain_cs_length l ls' fl g hg).le, (hcl g hg).2, ?_⟩
        rw [(hcl g hg).1]; exact pauliX_unitary
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
      intro g hg
      simp only [mcGate, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | rfl) | hg
      · exact hch g hg
      · refine ⟨by simp, ?_, hu⟩
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rw [hc]; exact hlast
      · exact gInv_ok _ hch g hg

end

end SparseHamiltonian.GateCircuit
