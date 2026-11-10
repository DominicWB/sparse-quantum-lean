import SparseLowerBounds.Helpers.Ode.OuterGraph.Counting

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The inner parity graph of the joint search-parity adversary

Helper for `ODE/JointGraph` (proof of Lemma `odel:lem:outer`). On tuples `j ∈ ℤ_m^n`, two tuples are
joined when exactly one coordinate changes and its parity changes (`InnerAdj`). For `m` even:

* the graph flips the parity of the coordinate sum (`InnerAdj.sum_mod_ne`), so
  it is bipartite between even and odd tuples;
* it is regular of degree `d = n m / 2` (`card_innerAdj`);
* for a fixed membership query `(k, z)` the surviving edges are stars: a tuple
  has at most `m/2` neighbours that change coordinate `k`
  (`card_innerAdj_ne_le`), and at most one neighbour with coordinate `k` equal
  to a given `z ≠ j k` (`card_innerAdj_eq_le`). These are the row sums behind
  `‖G ∘ Δ_{k,z}‖ = √(m/2)` (eq. `odel:eq:innermask`).
-/

namespace SparseLowerBounds.ODE

noncomputable section

open Finset

variable {n m : ℕ}

/-- **The inner graph** (proof of Lemma `odel:lem:outer`): `j` and `e` differ in exactly one
coordinate `k`, and the parities of `j k` and `e k` differ. -/
def InnerAdj (j e : Fin n → Fin m) : Prop :=
  ∃ k, (∀ k', k' ≠ k → j k' = e k') ∧ (j k : ℕ) % 2 ≠ (e k : ℕ) % 2

instance (j : Fin n → Fin m) : DecidablePred (InnerAdj j) := fun e => by
  unfold InnerAdj; infer_instance

namespace InnerAdj

variable {j e : Fin n → Fin m}

theorem symm (h : InnerAdj j e) : InnerAdj e j := by
  obtain ⟨k, hk, hp⟩ := h
  exact ⟨k, fun k' hk' => (hk k' hk').symm, fun h => hp h.symm⟩

/-- Every coordinate at which joined tuples differ has differing parities (it is
the changed coordinate). -/
theorem parity_ne_of_ne (h : InnerAdj j e) {k : Fin n} (hk : j k ≠ e k) :
    (j k : ℕ) % 2 ≠ (e k : ℕ) % 2 := by
  obtain ⟨k₀, hk₀, hp⟩ := h
  by_cases hkk : k = k₀
  · subst hkk; exact hp
  · exact absurd (hk₀ k hkk) hk

/-- A neighbour is determined by its value at any coordinate where it differs. -/
theorem eq_update (h : InnerAdj j e) {k : Fin n} (hk : j k ≠ e k) :
    e = Function.update j k (e k) := by
  obtain ⟨k₀, hk₀, -⟩ := h
  have hkk : k = k₀ := by
    by_contra hne; exact hk (hk₀ k hne)
  subst hkk
  funext k'
  by_cases h' : k' = k
  · subst h'; simp
  · rw [Function.update_of_ne h']; exact (hk₀ k' h').symm

/-- Joined tuples have coordinate sums of opposite parity. -/
theorem sum_mod_ne (h : InnerAdj j e) :
    (∑ k, (j k : ℕ)) % 2 ≠ (∑ k, (e k : ℕ)) % 2 := by
  obtain ⟨k₀, hk₀, hp⟩ := h
  have hj := Finset.add_sum_erase (Finset.univ) (fun k => (j k : ℕ)) (Finset.mem_univ k₀)
  have he := Finset.add_sum_erase (Finset.univ) (fun k => (e k : ℕ)) (Finset.mem_univ k₀)
  have hrest : ∑ k ∈ Finset.univ.erase k₀, (j k : ℕ) = ∑ k ∈ Finset.univ.erase k₀, (e k : ℕ) :=
    Finset.sum_congr rfl fun k hk => by rw [hk₀ k (Finset.ne_of_mem_erase hk)]
  omega

end InnerAdj

/-- Changing one coordinate to a value of the other parity is an inner edge. -/
theorem innerAdj_update {j : Fin n → Fin m} {k : Fin n} {z : Fin m}
    (hz : (j k : ℕ) % 2 ≠ (z : ℕ) % 2) : InnerAdj j (Function.update j k z) :=
  ⟨k, fun k' hk' => (Function.update_of_ne hk' _ _).symm, by simpa using hz⟩

/-- **Inner degree** (proof of Lemma `odel:lem:outer`): for `m` even the inner graph is regular of
degree `d = n (m/2)`. -/
theorem card_innerAdj (hme : Even m) (j : Fin n → Fin m) :
    (univ.filter (InnerAdj j)).card = n * (m / 2) := by
  set S := (univ : Finset (Fin n × Fin m)).filter
    (fun p => (j p.1 : ℕ) % 2 ≠ (p.2 : ℕ) % 2) with hSdef
  have himg : univ.filter (InnerAdj j) = S.image (fun p => Function.update j p.1 p.2) := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_image, S]
    constructor
    · intro h
      obtain ⟨k, hk, hp⟩ := h
      refine ⟨(k, e k), hp, ?_⟩
      have hne : j k ≠ e k := fun h' => hp (by rw [h'])
      exact (InnerAdj.eq_update ⟨k, hk, hp⟩ hne).symm
    · rintro ⟨⟨k, z⟩, hz, rfl⟩
      exact innerAdj_update hz
  have hinj : Set.InjOn (fun p : Fin n × Fin m => Function.update j p.1 p.2) S := by
    rintro ⟨k, z⟩ hkz ⟨k', z'⟩ - heq
    simp only [S, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hkz
    simp only at heq
    have hzk : z ≠ j k := fun h => hkz (by rw [h])
    have hk : k = k' := by
      by_contra hne
      have := congrFun heq k
      rw [Function.update_self, Function.update_of_ne hne] at this
      exact hzk this
    subst hk
    have := congrFun heq k
    simp only [Function.update_self] at this
    rw [this]
  have hS : S.card = n * (m / 2) := by
    calc S.card = ∑ k : Fin n, ∑ z : Fin m,
          (if (j k : ℕ) % 2 ≠ (z : ℕ) % 2 then 1 else 0) := by
          rw [hSdef, Finset.card_filter, Fintype.sum_prod_type]
      _ = ∑ _k : Fin n, m / 2 := Finset.sum_congr rfl fun k _ => by
          rw [← Finset.card_filter]; exact card_fin_mod_two_ne hme _
      _ = n * (m / 2) := by simp
  rw [himg, Finset.card_image_of_injOn hinj, hS]

/-- **Masked inner star, centre side**: at most `m/2` neighbours change a given
coordinate `k`. -/
theorem card_innerAdj_ne_le (hme : Even m) (j : Fin n → Fin m) (k : Fin n) :
    (univ.filter (fun e => InnerAdj j e ∧ e k ≠ j k)).card ≤ m / 2 := by
  calc (univ.filter (fun e => InnerAdj j e ∧ e k ≠ j k)).card
      ≤ ((univ.filter (fun z : Fin m => (j k : ℕ) % 2 ≠ (z : ℕ) % 2)).image
          (Function.update j k)).card := by
        apply Finset.card_le_card
        intro e he
        simp only [mem_filter, mem_univ, true_and] at he
        simp only [mem_image, mem_filter, mem_univ, true_and]
        exact ⟨e k, he.1.parity_ne_of_ne (Ne.symm he.2), (he.1.eq_update (Ne.symm he.2)).symm⟩
    _ ≤ (univ.filter (fun z : Fin m => (j k : ℕ) % 2 ≠ (z : ℕ) % 2)).card := Finset.card_image_le
    _ = m / 2 := card_fin_mod_two_ne hme _

/-- **Masked inner star, leaf side**: at most one neighbour has coordinate `k`
equal to a given `z ≠ j k` (namely `update j k z`). -/
theorem card_innerAdj_eq_le (j : Fin n → Fin m) {k : Fin n} {z : Fin m} (hz : j k ≠ z) :
    (univ.filter (fun e => InnerAdj j e ∧ e k = z)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have key : ∀ e ∈ univ.filter (fun e => InnerAdj j e ∧ e k = z), e = Function.update j k z := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    have := he.1.eq_update (k := k) (by rw [he.2]; exact hz)
    rwa [he.2] at this
  intro e he e' he'
  rw [key e he, key e' he']

end

end SparseLowerBounds.ODE
end
