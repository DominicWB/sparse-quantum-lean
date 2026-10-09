import GateEfficientBinary.Reversible.Adder

/-!
# Renaming wires and XOR-ing control conditions

Renaming the wires of a gate list along an injective map acts on the image wires as the
original list and leaves the other wires alone (`crun_map`, `crun_map_of_not_mem`). A gate list
in which no control wire is a target writes into every wire the exclusive or of the control
conditions of the gates targeting it (`crun_xor`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

variable {W W' : Type*} [DecidableEq W] [DecidableEq W']

/-- Renaming the wires of a gate. -/
def CGate.map (f : W → W') (g : CGate W) : CGate W' :=
  ⟨g.cs.map (fun c => (f c.1, c.2)), f g.t⟩

omit [DecidableEq W] [DecidableEq W'] in
theorem lits_map (f : W → W') (cs : List (W × Bool)) (z : W' → Bool) :
    lits (cs.map (fun c => (f c.1, c.2))) z = lits cs (z ∘ f) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons, lits, List.all_cons, Function.comp] at ih ⊢
      rw [ih]

theorem CGate.run_map (f : W → W') (hf : Function.Injective f) (g : CGate W) (z : W' → Bool) :
    (g.map f).run z ∘ f = g.run (z ∘ f) := by
  unfold CGate.run CGate.map
  simp only [lits_map]
  split_ifs
  · funext a
    simp only [Function.comp]
    by_cases ha : a = g.t
    · subst ha
      simp
    · rw [Function.update_of_ne (hf.ne ha), Function.update_of_ne ha]
      rfl
  · rfl

omit [DecidableEq W] in
theorem CGate.run_map_of_not_mem (f : W → W') (g : CGate W) (z : W' → Bool) (u : W')
    (hu : ∀ a, f a ≠ u) : (g.map f).run z u = z u :=
  CGate.run_apply_of_ne _ z u (fun he => hu g.t he.symm)

/-- Renamed gates act on the image wires as the original gates. -/
theorem crun_map (f : W → W') (hf : Function.Injective f) (gs : List (CGate W))
    (z : W' → Bool) : crun (gs.map (CGate.map f)) z ∘ f = crun gs (z ∘ f) := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      rw [List.map_cons, crun_cons, crun_cons, ih, CGate.run_map f hf]

omit [DecidableEq W] in
/-- Renamed gates leave the wires outside the image alone. -/
theorem crun_map_of_not_mem (f : W → W') (gs : List (CGate W)) (z : W' → Bool) (u : W')
    (hu : ∀ a, f a ≠ u) : crun (gs.map (CGate.map f)) z u = z u := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      rw [List.map_cons, crun_cons, ih, CGate.run_map_of_not_mem f g z u hu]

omit [DecidableEq W] [DecidableEq W'] in
theorem CGate.proper_map (f : W → W') (hf : Function.Injective f) (g : CGate W)
    (hg : g.Proper) : (g.map f).Proper := by
  intro c hc
  simp only [CGate.map, List.mem_map] at hc
  obtain ⟨c', hc', rfl⟩ := hc
  exact hf.ne (hg c' hc')

/-- Gates whose control wires are never targets XOR their control conditions into their
targets. -/
theorem crun_xor (gs : List (CGate W)) (h : ∀ g ∈ gs, ∀ c ∈ g.cs, ∀ g' ∈ gs, c.1 ≠ g'.t)
    (z : W → Bool) :
    crun gs z = fun u =>
      z u ^^ xorAll ((gs.filter (fun g => g.t = u)).map (fun g => lits g.cs z)) := by
  induction gs generalizing z with
  | nil =>
      funext u
      simp [xorAll]
  | cons g gs ih =>
      rw [crun_cons, ih (fun g' hg' c hc g'' hg'' => h g' (List.mem_cons_of_mem g hg') c hc g''
        (List.mem_cons_of_mem g hg''))]
      have hl : ∀ g' ∈ gs, lits g'.cs (g.run z) = lits g'.cs z := by
        intro g' hg'
        rw [CGate.run_eq]
        exact lits_congr _ _ _ (fun c hc =>
          Function.update_of_ne (h g' (List.mem_cons_of_mem g hg') c hc g List.mem_cons_self) _ _)
      funext u
      have hmap : ((gs.filter (fun g' => g'.t = u)).map (fun g' => lits g'.cs (g.run z))) =
          ((gs.filter (fun g' => g'.t = u)).map (fun g' => lits g'.cs z)) := by
        apply List.map_congr_left
        intro g' hg'
        exact hl g' (List.mem_filter.1 hg').1
      rw [hmap, CGate.run_eq]
      by_cases hu : g.t = u
      · subst hu
        rw [List.filter_cons_of_pos (by simp)]
        simp only [Function.update_self, List.map_cons, xorAll, List.foldr_cons, Bool.xor_assoc]
      · rw [List.filter_cons_of_neg (by simpa using hu), Function.update_of_ne (Ne.symm hu)]

end SparseHamiltonian.GateBinary
