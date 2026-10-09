import SparseLowerBounds.ODE.Promise

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Counting tools for the joint search-parity adversary

Helper for `ODE/JointGraph` (Lemma `odel:lem:outer`, manuscript lines
3743-3798). The degree and the Schur-certificate row sums of the outer adversary
matrix are computed by moving sums over promised inputs to sums over triples
`(b, e₁, e₂)` (new odd candidate, new block of the old odd candidate, new block
of the new one):

* `sum_le_sum_of_injOn_support`: a sum is at most a nonnegative sum over a
  set into which its support injects (used in both directions);
* `sum_triple_ite`, `sum_triple_ite_le`: the sum of a product indicator over
  triples factorizes into cardinalities;
* `card_fin_lt_half`, `card_fin_not_lt_half`, `card_fin_mod_two_ne`: the half
  and parity classes of `Fin M` (`M` even) have `M/2` elements.
-/

namespace SparseLowerBounds.ODE

noncomputable section

open Finset

/-- **Injection transfer.** If `g` is injective on the support of `f`, and on
that support `f a ≤ h (g a)` with `h ≥ 0`, then `Σ f ≤ Σ h`. -/
theorem sum_le_sum_of_injOn_support {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ) (h : β → ℝ) (g : α → β)
    (hinj : ∀ a a', f a ≠ 0 → f a' ≠ 0 → g a = g a' → a = a')
    (hle : ∀ a, f a ≠ 0 → f a ≤ h (g a)) (hh : ∀ b, 0 ≤ h b) :
    ∑ a, f a ≤ ∑ b, h b := by
  classical
  set S := (univ : Finset α).filter (fun a => f a ≠ 0)
  have hS : ∀ a ∈ S, f a ≠ 0 := fun a ha => (Finset.mem_filter.mp ha).2
  calc ∑ a, f a = ∑ a ∈ S, f a := (Finset.sum_filter_ne_zero _).symm
    _ ≤ ∑ a ∈ S, h (g a) := Finset.sum_le_sum fun a ha => hle a (hS a ha)
    _ = ∑ b ∈ S.image g, h b := by
        rw [Finset.sum_image]
        intro a ha a' ha' hg
        exact hinj a a' (hS a ha) (hS a' ha') hg
    _ ≤ ∑ b, h b :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hh b)

/-- **Triple sums factorize**: the sum over `(b, e₁, e₂)` of `w` times the
indicator of `P b ∧ Q e₁ ∧ R b e₂` is `Σ_b [P b] #Q #(R b) w`. -/
theorem sum_triple_ite {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : α → Prop) (Q : β → Prop) (R : α → γ → Prop) [DecidablePred P] [DecidablePred Q]
    [∀ b, DecidablePred (R b)] (w : ℝ) :
    ∑ t : α × β × γ, (if P t.1 ∧ Q t.2.1 ∧ R t.1 t.2.2 then w else 0) =
      ∑ b, if P b then ((univ.filter Q).card : ℝ) * (univ.filter (R b)).card * w else 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type]
  by_cases hP : P b
  · simp only [hP, true_and, if_true]
    have hin : ∀ e₁ : β, (∑ e₂ : γ, if Q e₁ ∧ R b e₂ then w else 0) =
        if Q e₁ then ((univ.filter (R b)).card : ℝ) * w else 0 := by
      intro e₁
      by_cases hQ : Q e₁
      · simp only [hQ, true_and, if_true]
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      · simp [hQ]
    simp_rw [hin]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  · simp [hP]

/-- Upper bound form of `sum_triple_ite`, from cardinality bounds. -/
theorem sum_triple_ite_le {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (P : α → Prop) (Q : β → Prop) (R : α → γ → Prop) [DecidablePred P] [DecidablePred Q]
    [∀ b, DecidablePred (R b)] {w : ℝ} (hw : 0 ≤ w) {p q r : ℕ}
    (hP : (univ.filter P).card ≤ p) (hQ : (univ.filter Q).card ≤ q)
    (hR : ∀ b, (univ.filter (R b)).card ≤ r) :
    ∑ t : α × β × γ, (if P t.1 ∧ Q t.2.1 ∧ R t.1 t.2.2 then w else 0) ≤
      (p : ℝ) * q * r * w := by
  rw [sum_triple_ite]
  have hQ' : ((univ.filter Q).card : ℝ) ≤ q := by exact_mod_cast hQ
  have hP' : ((univ.filter P).card : ℝ) ≤ p := by exact_mod_cast hP
  calc ∑ b, (if P b then ((univ.filter Q).card : ℝ) * (univ.filter (R b)).card * w else 0)
      ≤ ∑ b, (if P b then (q : ℝ) * r * w else 0) := by
        refine Finset.sum_le_sum fun b _ => ?_
        split_ifs
        · have hR' : ((univ.filter (R b)).card : ℝ) ≤ r := by exact_mod_cast hR b
          have h0 : (0 : ℝ) ≤ (univ.filter (R b)).card := by positivity
          gcongr
        · exact le_refl _
    _ = ((univ.filter P).card : ℝ) * ((q : ℝ) * r * w) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (p : ℝ) * ((q : ℝ) * r * w) := by gcongr
    _ = (p : ℝ) * q * r * w := by ring

/-- The upper half `{b | M/2 ≤ b}` of `Fin M`, `M` even, has `M/2` elements. -/
theorem card_fin_not_lt_half {M : ℕ} (hMe : Even M) :
    ((univ : Finset (Fin M)).filter (fun b : Fin M => ¬ (b : ℕ) < M / 2)).card = M / 2 := by
  obtain ⟨h, rfl⟩ := hMe
  have hh : (h + h) / 2 = h := by omega
  rw [hh]
  calc ((univ : Finset (Fin (h + h))).filter (fun b : Fin (h + h) => ¬ (b : ℕ) < h)).card
      = (univ : Finset (Fin h)).card := by
        refine Finset.card_nbij' (fun b => ⟨(b : ℕ) - h, by have := b.isLt; omega⟩)
          (fun i => ⟨(i : ℕ) + h, by have := i.isLt; omega⟩) ?_ ?_ ?_ ?_
        · intro b _; simp
        · intro i _; simp
        · intro b hb
          simp only [coe_filter, Set.mem_setOf_eq] at hb
          ext; simp; omega
        · intro i _; ext; simp
    _ = h := Finset.card_fin h

/-- The lower half `{b | b < M/2}` of `Fin M`, `M` even, has `M/2` elements. -/
theorem card_fin_lt_half {M : ℕ} (hMe : Even M) :
    ((univ : Finset (Fin M)).filter (fun b : Fin M => (b : ℕ) < M / 2)).card = M / 2 := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M)))
    (fun b : Fin M => (b : ℕ) < M / 2)
  rw [card_fin_not_lt_half hMe, Finset.card_univ, Fintype.card_fin] at h
  obtain ⟨r, rfl⟩ := hMe
  omega

/-- The positions of `Fin m`, `m` even, whose parity differs from that of `p`
number `m/2`. -/
theorem card_fin_mod_two_ne {m : ℕ} (hme : Even m) (p : ℕ) :
    ((univ : Finset (Fin m)).filter (fun z : Fin m => p % 2 ≠ (z : ℕ) % 2)).card = m / 2 := by
  obtain ⟨h, rfl⟩ := hme
  have hh : (h + h) / 2 = h := by omega
  rw [hh]
  calc ((univ : Finset (Fin (h + h))).filter (fun z : Fin (h + h) => p % 2 ≠ (z : ℕ) % 2)).card
      = (univ : Finset (Fin h)).card := by
        refine Finset.card_nbij' (fun z => ⟨(z : ℕ) / 2, by have := z.isLt; omega⟩)
          (fun i => ⟨2 * (i : ℕ) + (1 - p % 2), by have := i.isLt; omega⟩) ?_ ?_ ?_ ?_
        · intro z _; simp
        · intro i _; simp; omega
        · intro z hz
          simp only [coe_filter, Set.mem_setOf_eq] at hz
          ext; simp; omega
        · intro i _; ext; simp; omega
    _ = h := Finset.card_fin h

end

end SparseLowerBounds.ODE
end
