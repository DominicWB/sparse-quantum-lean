import GateEfficientSynthesis.Hypothesis
import GateEfficientNative.ODE.Grover

/-!
# Gate sets for exact zero tests and actual inverses

The trials of Theorem `ode:thm:gates` run Grover iterations on the actual (finite-gate) preparation
and its actual inverse, with the two reflections and the global sign kept exact ("The two
reflections test the known initial state and the selected zero-output-work subspace. They use
reversible Boolean gates and a phase flip"). Over a finite gate set `𝒢` (a partial formalisation,
under this package's format hypotheses, of the finite-set statement: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates) this needs
two properties of `𝒢`, stated here as
explicit hypotheses:

* `AdjClosed 𝒢`: with every kind `(p, u)` the gate set contains its adjoint kind `(p, uᴴ)`.
  The literal inverse of a circuit over `𝒢` (`GateNative.ninv`, gates `⟨cs, t, uᴴ⟩`) is then
  again a circuit over `𝒢` (`GateOf.inv`), so the inverse preparation is the exact adjoint of
  the synthesised preparation.
* `zeroTestKinds ⊆ 𝒢`: the kinds of the gates of the exact zero tests. A zero test
  `mcGate ls fl t zMat` with at least two zero literals `ls` computes an AND chain on clean
  flags with doubly controlled NOT gates (control values `(0, 0)` for the first step and
  `(1, 0)` for the others), applies the phase `zMat = diag(-1, 1)` controlled by the last flag
  (value `1`) and uncomputes the chain with the same NOT gates (`pauliX` is self-adjoint, so
  this needs no adjoint closure); the global sign is the one-qubit matrix `-1`.

`gateOf_mcGate`: every gate of such a zero test is a gate of `𝒢`; `gateOf_rgoodNG`,
`gateOf_rseedNG`, `gateOf_negGateN`: the released native zero tests and sign of
`GateEfficientNative` on every native ODE register whose pool is large enough for them (they
have at least two literals, `two_le_zeroLitsN`).

Both hypotheses are stated assumptions, met over an enlarged gate set (`extra_hyps`): for every
synthesis hypothesis `Synthesis 𝒢₀ X L`, the gate set `closeKinds 𝒢₀`, which adds to `𝒢₀` the
adjoint kinds of its kinds and the four self-adjoint kinds of the exact zero tests
(`zeroTestKinds_adjClosed`), is finite and satisfies `Synthesis` with the same ancillas and length
function (`synthesis_closeKinds`), is closed under adjoints (`closeKinds_adjClosed`) and contains
`zeroTestKinds`; the gate counts are then gates of `closeKinds 𝒢₀`, not of `𝒢₀`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynthTrials

noncomputable section
open GateCircuit GateNative GateSynth
open GateCircuit.Sim (zMat)

/-! ### The two gate-set hypotheses -/

/-- **A gate set closed under adjoints**: with every kind `(p, u)` it contains `(p, uᴴ)`. -/
def AdjClosed (𝒢 : Set Kind) : Prop :=
  ∀ (p : List Bool) (u : Matrix Bool Bool ℂ), (p, u) ∈ 𝒢 → (p, u.conjTranspose) ∈ 𝒢

/-- **The kinds of the exact zero tests**: the NOT gate with two controls of values `(0, 0)`
and `(1, 0)`, the phase `zMat = diag(-1, 1)` with one control of value `1`, and the global
sign `-1`. -/
def zeroTestKinds : Set Kind :=
  {([false, false], pauliX), ([true, false], pauliX), ([true], zMat), ([], -1)}

theorem mem_zeroTestKinds_not (b : Bool) : ([b, false], pauliX) ∈ zeroTestKinds := by
  cases b <;> simp [zeroTestKinds]

theorem mem_zeroTestKinds_phase : ([true], zMat) ∈ zeroTestKinds := by
  simp [zeroTestKinds]

theorem mem_zeroTestKinds_sign : (([] : List Bool), (-1 : Matrix Bool Bool ℂ)) ∈ zeroTestKinds := by
  simp [zeroTestKinds]

/-- **The literal inverse of a gate of an adjoint-closed gate set is a gate of the set.** -/
theorem GateOf.inv {𝒢 : Set Kind} (hadj : AdjClosed 𝒢) {W : Type*} {g : Gate W}
    (h : GateOf 𝒢 g) : GateOf 𝒢 (⟨g.cs, g.t, g.u.conjTranspose⟩ : Gate W) :=
  ⟨h.1, hadj _ _ h.2⟩

/-! ### The shape of an AND chain -/

section Chain

variable {W : Type*}

/-- Every gate of an AND chain is a NOT gate with two controls: a literal of the list, after
the first literal or a flag of the chain with value `1`. -/
theorem andChain_shape (p : W × Bool) (ls : List (W × Bool)) (fl : List W) :
    ∀ g ∈ andChain p ls fl, g.u = pauliX ∧ ∃ p' l, g.cs = [p', l] ∧ l ∈ ls ∧
      (p' = p ∨ (p'.2 = true ∧ p'.1 ∈ fl)) := by
  induction ls generalizing p fl with
  | nil => intro g hg; simp [andChain] at hg
  | cons l ls ih =>
      cases fl with
      | nil => intro g hg; simp [andChain] at hg
      | cons f fs =>
          intro g hg
          simp only [andChain, List.mem_cons] at hg
          rcases hg with rfl | hg
          · exact ⟨rfl, p, l, rfl, List.mem_cons_self, Or.inl rfl⟩
          · obtain ⟨hu, p', l', hcs, hl', hp'⟩ := ih (f, true) fs g hg
            refine ⟨hu, p', l', hcs, List.mem_cons_of_mem _ hl', Or.inr ?_⟩
            rcases hp' with rfl | ⟨h1, h2⟩
            · exact ⟨rfl, List.mem_cons_self⟩
            · exact ⟨h1, List.mem_cons_of_mem _ h2⟩

/-- The literal holding the conjunction is the first literal or a flag with value `1`. -/
theorem andLast_cases (p : W × Bool) (ls : List (W × Bool)) (fl : List W) :
    andLast p ls fl = p ∨ ((andLast p ls fl).2 = true ∧ (andLast p ls fl).1 ∈ fl) := by
  induction ls generalizing p fl with
  | nil => exact Or.inl rfl
  | cons l ls ih =>
      cases fl with
      | nil => exact Or.inl rfl
      | cons f fs =>
          right
          change (andLast (f, true) ls fs).2 = true ∧ (andLast (f, true) ls fs).1 ∈ f :: fs
          rcases ih (f, true) fs with h | ⟨h1, h2⟩
          · rw [h]
            exact ⟨rfl, List.mem_cons_self⟩
          · exact ⟨h1, List.mem_cons_of_mem _ h2⟩

end Chain

/-! ### Zero tests over a gate set -/

section ZeroTest

variable {𝒢 : Set Kind} {W : Type*}

/-- **Every gate of an exact zero test is a gate of `𝒢`**: for at least two zero literals on
distinct wires, off the flags of the chain, and enough flags. The uncomputation of the AND chain
repeats its NOT gates (`pauliXᴴ = pauliX`), so no adjoint closure of `𝒢` is needed. -/
theorem gateOf_mcGate (hzt : zeroTestKinds ⊆ 𝒢) (ls : List (W × Bool)) (fl : List W) (t : W)
    (hfalse : ∀ c ∈ ls, c.2 = false) (hnd : (ls.map Prod.fst).Nodup)
    (hlf : ∀ c ∈ ls, ∀ f ∈ fl, c.1 ≠ f) (h2 : 2 ≤ ls.length) (hfl : ls.length ≤ fl.length + 1) :
    ∀ g ∈ mcGate ls fl t zMat, GateOf 𝒢 g := by
  obtain ⟨l, l₁, ls'', rfl⟩ : ∃ l l₁ ls'', ls = l :: l₁ :: ls'' := by
    match ls, h2 with
    | l :: l₁ :: ls'', _ => exact ⟨l, l₁, ls'', rfl⟩
  obtain ⟨f₁, fs, rfl⟩ : ∃ f₁ fs, fl = f₁ :: fs := by
    match fl, hfl with
    | f₁ :: fs, _ => exact ⟨f₁, fs, rfl⟩
  set ls' := l₁ :: ls'' with hls'
  have hnd' : l.1 ∉ ls'.map Prod.fst ∧ (ls'.map Prod.fst).Nodup := by
    simpa using hnd
  -- the gates of the chain
  have hch : ∀ g ∈ andChain l ls' (f₁ :: fs), GateOf 𝒢 g := by
    intro g hg
    obtain ⟨hu, p', l', hcs, hl', hp'⟩ := andChain_shape l ls' (f₁ :: fs) g hg
    have hl'f : l'.2 = false := hfalse l' (List.mem_cons_of_mem _ hl')
    have hne : p'.1 ≠ l'.1 := by
      rcases hp' with rfl | ⟨_, h2⟩
      · intro h
        exact hnd'.1 (List.mem_map.mpr ⟨l', hl', h.symm⟩)
      · exact fun h => hlf l' (List.mem_cons_of_mem _ hl') p'.1 h2 h.symm
    refine ⟨?_, ?_⟩
    · rw [hcs]
      simp [hne]
    · have hk : kind g = ([p'.2, false], pauliX) := by
        simp only [kind, hcs, hu, hl'f, List.map_cons, List.map_nil]
      rw [hk]
      exact hzt (mem_zeroTestKinds_not p'.2)
  -- the literal holding the conjunction is a flag with value `1`
  have hlast : (andLast l ls' (f₁ :: fs)).2 = true := by
    change (andLast (f₁, true) ls'' fs).2 = true
    rcases andLast_cases (f₁, true) ls'' fs with h | ⟨h1, _⟩
    · rw [h]
    · exact h1
  intro g hg
  simp only [mcGate, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hg | rfl) | hg
  · exact hch g hg
  · refine ⟨List.nodup_singleton _, ?_⟩
    have hk : kind (⟨[andLast l ls' (f₁ :: fs)], t, zMat⟩ : Gate W) = ([true], zMat) := by
      simp only [kind, List.map_cons, List.map_nil, hlast]
    rw [hk]
    exact hzt mem_zeroTestKinds_phase
  · -- the uncomputation repeats the NOT gates of the chain
    obtain ⟨h, hh, rfl⟩ := mem_gInv _ g hg
    have hu : h.u.conjTranspose = h.u := by
      rw [(andChain_shape l ls' (f₁ :: fs) h hh).1, pauliX_conjTranspose]
    rw [hu]
    exact hch h hh

end ZeroTest

/-! ### The native zero tests and sign -/

section Native

variable {𝒢 : Set Kind} {a m r K k l f : ℕ} {S Zs Z : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [Fintype Zs] [Fintype Z]

omit [Fintype S] in
theorem zeroLitsN_nodup :
    ((zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).map Prod.fst).Nodup := by
  simp only [zeroLitsN, List.map_append, List.map_map]
  refine List.Nodup.append (List.Nodup.append ?_ ?_ ?_) ?_ ?_
  · exact (Finset.nodup_toList _).map (fun _ _ h => by simpa using h)
  · exact (Finset.nodup_toList _).map (fun _ _ h => by simpa using h)
  · rw [List.disjoint_left]
    intro w h1 h2
    simp only [List.mem_map, Function.comp_apply] at h1 h2
    obtain ⟨_, _, rfl⟩ := h1
    obtain ⟨_, _, h⟩ := h2
    cases h
  · exact (Finset.nodup_toList _).map (fun _ _ h => by simpa using h)
  · rw [List.disjoint_left]
    intro w h1 h2
    simp only [List.mem_append, List.mem_map, Function.comp_apply] at h1 h2
    obtain ⟨_, _, rfl⟩ := h2
    rcases h1 with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;> cases h

theorem seedLitsN_nodup :
    (((zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) ++ sysLits).map
        Prod.fst).Nodup := by
  rw [List.map_append]
  refine List.Nodup.append zeroLitsN_nodup ?_ ?_
  · simp only [sysLits, List.map_map]
    exact (Finset.nodup_toList _).map (fun _ _ h => by simpa using h)
  · rw [List.disjoint_left]
    intro w h1 h2
    simp only [sysLits, zeroLitsN, List.map_append, List.map_map, List.mem_append,
      List.mem_map, Function.comp_apply] at h1 h2
    obtain ⟨_, _, rfl⟩ := h2
    rcases h1 with (⟨_, _, h⟩ | ⟨_, _, h⟩) | ⟨_, _, h⟩ <;> cases h

omit [Fintype S] in
/-- The native zero tests have at least two literals: the solver wires `ini` and `flg`. -/
theorem two_le_zeroLitsN :
    2 ≤ (zeroLitsN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)).length := by
  rw [zeroLitsN_length]
  have h : 1 < Fintype.card (GateODE.AW a m r K k l f) :=
    Fintype.one_lt_card_iff.mpr ⟨Sum.inr GateODE.OWire.ini, Sum.inr GateODE.OWire.flg,
      by simp⟩
  omega

omit [Fintype S] in
/-- **Every gate of the native good-subspace zero test is a gate of `𝒢`**, if the pool is large
enough for the zero tests. -/
theorem gateOf_rgoodNG (hzt : zeroTestKinds ⊆ 𝒢)
    (hnP : Fintype.card (GateODE.AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
      Fintype.card Zs ≤ nP + 1) :
    ∀ g ∈ (rgoodNG (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)), GateOf 𝒢 g :=
  gateOf_mcGate hzt _ _ _ zeroLitsN_false zeroLitsN_nodup
    (fun c hc => lits_ne_pool c (zeroLitsN_not_refl c hc)) two_le_zeroLitsN
    (by rw [zeroLitsN_length, poolN_length]; exact hnP)

/-- **Every gate of the native seed zero test is a gate of `𝒢`**, if the pool is large enough
for the zero tests. -/
theorem gateOf_rseedNG (hzt : zeroTestKinds ⊆ 𝒢)
    (hnP : Fintype.card (GateODE.AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
      Fintype.card Zs + Fintype.card S ≤ nP + 1) :
    ∀ g ∈ (rseedNG (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)), GateOf 𝒢 g := by
  refine gateOf_mcGate hzt _ _ _ ?_ seedLitsN_nodup ?_ ?_ ?_
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact zeroLitsN_false c hc
    · exact sysLits_false c hc
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact lits_ne_pool c (zeroLitsN_not_refl c hc)
    · exact lits_ne_pool c (sysLits_not_refl c hc)
  · rw [List.length_append]
    exact two_le_zeroLitsN.trans (Nat.le_add_right _ _)
  · rw [List.length_append, zeroLitsN_length, sysLits_length, poolN_length]
    exact hnP

omit [Fintype S] [Fintype Zs] [Fintype Z] in
/-- **The global sign is a gate of `𝒢`.** -/
theorem gateOf_negGateN (hzt : zeroTestKinds ⊆ 𝒢) :
    GateOf 𝒢 (negGateN (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f) (S := S)
      (Zs := Zs) (nP := nP) (Z := Z) (bT := bT) (bP := bP) (A := A)) :=
  ⟨List.nodup_nil, hzt mem_zeroTestKinds_sign⟩

end Native

/-! ### The gate-set hypotheses hold over an enlarged gate set -/

section Closure

/-- **The kinds of the exact zero tests are self-adjoint**: `pauliX`, `zMat` and `-1` are
Hermitian, so `zeroTestKinds` is closed under adjoints. -/
theorem zeroTestKinds_adjClosed : AdjClosed zeroTestKinds := by
  have hX : pauliX.conjTranspose = pauliX := pauliX_conjTranspose
  have hZ : zMat.conjTranspose = zMat := by
    funext b c
    cases b <;> cases c <;> simp [zMat, Matrix.conjTranspose_apply]
  have hN : (-1 : Matrix Bool Bool ℂ).conjTranspose = -1 := by
    rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  intro p u h
  simp only [zeroTestKinds, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h ⊢
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, hX⟩
  · exact Or.inr (Or.inl ⟨rfl, hX⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, hZ⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨rfl, hN⟩))

/-- The kinds of the exact zero tests form a finite set. -/
theorem zeroTestKinds_finite : zeroTestKinds.Finite :=
  (((Set.finite_singleton _).insert _).insert _).insert _

/-- **The closure of a gate set**: the kinds of `𝒢₀`, their adjoint kinds `(p, uᴴ)`, and the
kinds of the exact zero tests. -/
def closeKinds (𝒢₀ : Set Kind) : Set Kind :=
  𝒢₀ ∪ (fun k : Kind => (k.1, k.2.conjTranspose)) '' 𝒢₀ ∪ zeroTestKinds

/-- **The closure of a gate set is closed under adjoints.** -/
theorem closeKinds_adjClosed (𝒢₀ : Set Kind) : AdjClosed (closeKinds 𝒢₀) := by
  intro p u h
  rcases h with (h | ⟨⟨p', u'⟩, h', he⟩) | h
  · exact Or.inl (Or.inr ⟨(p, u), h, rfl⟩)
  · simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine Or.inl (Or.inl ?_)
    simpa only [Matrix.conjTranspose_conjTranspose] using h'
  · exact Or.inr (zeroTestKinds_adjClosed p u h)

/-- **Synthesis over the closure**: a synthesis hypothesis for `𝒢₀` gives one for
`closeKinds 𝒢₀` with the same ancillas and the same length function (the closure is finite,
and every gate of `𝒢₀` is a gate of the closure). -/
theorem synthesis_closeKinds {𝒢₀ : Set Kind} {X : Type*} [Fintype X] [DecidableEq X]
    {L : ℝ → ℕ} (hS : Synthesis 𝒢₀ X L) : Synthesis (closeKinds 𝒢₀) X L := by
  refine ⟨(hS.1.union (hS.1.image _)).union zeroTestKinds_finite, ?_⟩
  intro n hn p u hu ζ hζ
  obtain ⟨gs, hgs, hlen, happ⟩ := hS.2 n hn p u hu ζ hζ
  exact ⟨gs, fun g hg => ⟨(hgs g hg).1, (hgs g hg).2.1, Or.inl (Or.inl (hgs g hg).2.2)⟩,
    hlen, happ⟩

/-- **The extra gate-set hypotheses hold over an enlarged gate set**: for every synthesis
hypothesis `Synthesis 𝒢₀ X L`, the gate set `closeKinds 𝒢₀` (the kinds of `𝒢₀`, their adjoint
kinds and the four kinds of the exact zero tests) satisfies `Synthesis` with the same ancillas
and length function, is closed under adjoints, and contains the kinds of the exact zero tests. They
remain stated assumptions: the gate counts are then over `closeKinds 𝒢₀`, not over `𝒢₀`. -/
theorem extra_hyps {𝒢₀ : Set Kind} {X : Type*} [Fintype X] [DecidableEq X] {L : ℝ → ℕ}
    (hS : Synthesis 𝒢₀ X L) :
    Synthesis (closeKinds 𝒢₀) X L ∧ AdjClosed (closeKinds 𝒢₀) ∧
      zeroTestKinds ⊆ closeKinds 𝒢₀ :=
  ⟨synthesis_closeKinds hS, closeKinds_adjClosed 𝒢₀, fun _ hk => Or.inr hk⟩

end Closure

end

end SparseHamiltonian.GateSynthTrials
