import SparseLowerBounds.Helpers.Ode.OuterGraph.InnerGraph

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Opposite halves of the candidates

Helper for `ODE/JointGraph` (proof of Lemma `odel:lem:outer`). The outer adversary moves the odd
candidate between the two halves `{a < M/2}` and `{a ≥ M/2}` of the candidates (`OppHalf`). For `M`
even each half has `M/2` elements (`card_oppHalf`), and the half answers `halfSign` of candidates in
opposite halves are opposite (`halfSign_of_oppHalf`).
-/

namespace SparseLowerBounds.ODE

noncomputable section

open Finset

variable {M : ℕ}

/-- `a` and `b` lie in opposite halves of the candidates. -/
def OppHalf (M : ℕ) (a b : Fin M) : Prop := ((a : ℕ) < M / 2 ↔ ¬ (b : ℕ) < M / 2)

instance (M : ℕ) (a : Fin M) : DecidablePred (OppHalf M a) := fun b => by
  unfold OppHalf; infer_instance

theorem OppHalf.symm {a b : Fin M} (h : OppHalf M a b) : OppHalf M b a := by
  unfold OppHalf at *; tauto

theorem OppHalf.ne {a b : Fin M} (h : OppHalf M a b) : b ≠ a := by
  rintro rfl; unfold OppHalf at h; tauto

/-- For `M` even, the opposite half of any candidate has `M/2` elements. -/
theorem card_oppHalf (hMe : Even M) (a : Fin M) : (univ.filter (OppHalf M a)).card = M / 2 := by
  by_cases ha : (a : ℕ) < M / 2
  · rw [← card_fin_not_lt_half hMe]; congr 1; ext b; simp [OppHalf, ha]
  · rw [← card_fin_lt_half hMe]; congr 1; ext b; simp [OppHalf, ha]

theorem halfSign_of_oppHalf {a b : Fin M} (h : OppHalf M a b) :
    halfSign M b = -halfSign M a := by
  unfold halfSign
  by_cases ha : (a : ℕ) < M / 2
  · simp [ha, h.mp ha]
  · have hb : (b : ℕ) < M / 2 := by by_contra hb; exact ha (h.mpr hb)
    simp [ha, hb]


end

end SparseLowerBounds.ODE
end
