import GeneralODE.Block.HistoryCircuit

/-!
# Coefficients of the history combination

Slot-dependent coefficient states realise the implemented history matrix
`N⁻¹ (P₀ - S - C)`: the identity term uses the zeroth power `P₀`; the step
term uses the Taylor coefficients `c_k` of `V = ∑ c_k P_k` on the first `m`
steps and `P₀` on the padded copies, with the cyclic slot shift; the source
term uses the coefficients `d_k` of `Φ = ∑ d_k P_k` and a slot unitary sending
the forcing slot to the uniform superposition of the slots `1, …, m`.  Junk
labels pad both coefficient states to unit norm without contributing.
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit History
open scoped InnerProduct BigOperators ComplexConjugate

section Coefficients

variable (m K : ℕ) (N : ℝ) (c d : ℕ → ℝ)

/-- Cyclic shift of the time slots, fixing the forcing slot. -/
def slotShift : Slot m ≃ Slot m := Equiv.optionCongr (finRotate (2 * m + 1))

theorem slotShift_symm_some (j : ℕ) (hj : j < 2 * m + 1) (h1 : 1 ≤ j) :
    (slotShift m).symm (some ⟨j, hj⟩) = some ⟨j - 1, by omega⟩ := by
  apply (slotShift m).injective
  rw [Equiv.apply_symm_apply]
  change some ⟨j, hj⟩ = some ((finRotate (2 * m + 1)) ⟨j - 1, by omega⟩)
  congr 1
  have := finRotate_of_lt (n := 2 * m) (k := j - 1) (by omega)
  rw [this]
  ext
  simp
  omega

theorem slotShift_symm_none : (slotShift m).symm none = none := rfl

theorem slotShift_symm_zero : (slotShift m).symm (some ⟨0, by omega⟩) = some ⟨2 * m, by omega⟩ := by
  apply (slotShift m).injective
  rw [Equiv.apply_symm_apply]
  change some ⟨0, _⟩ = some ((finRotate (2 * m + 1)) ⟨2 * m, by omega⟩)
  congr 1
  rw [finRotate_last']

/-- Weight carried by the non-junk terms of the input state. -/
def restIn : Slot m → ℝ
  | none => 1 / N + (∑ k ∈ Finset.range (K + 1), d k) / N
  | some j => 1 / N + (if j.val < m then (∑ k ∈ Finset.range (K + 1), c k) / N
      else if j.val < 2 * m then 1 / N else 0)

/-- Weight carried by the non-junk terms of the output state. -/
def restOut : Slot m → ℝ
  | none => 1 / N
  | some j => 1 / N + (if 1 ≤ j.val ∧ j.val ≤ m then
      (∑ k ∈ Finset.range (K + 1), c k) / N + (∑ k ∈ Finset.range (K + 1), d k) / N
      else if m < j.val then 1 / N else 0)

/-- Real input amplitudes. -/
def ampIn (s : Slot m) (t : Term) (k : Fin (K + 1)) : ℝ :=
  match t with
  | .id => if k.val = 0 then Real.sqrt (1 / N) else 0
  | .step => match s with
    | none => 0
    | some j => if j.val < m then Real.sqrt (c k / N)
        else if j.val < 2 * m then (if k.val = 0 then Real.sqrt (1 / N) else 0) else 0
  | .src => match s with
    | none => Real.sqrt (d k / N)
    | some _ => 0
  | .junkIn => if k.val = 0 then Real.sqrt (1 - restIn m K N c d s) else 0
  | .junkOut => 0

/-- Real output amplitudes. -/
def ampOut (s : Slot m) (t : Term) (k : Fin (K + 1)) : ℝ :=
  match t with
  | .id => if k.val = 0 then Real.sqrt (1 / N) else 0
  | .step => match s with
    | none => 0
    | some j => if 1 ≤ j.val ∧ j.val ≤ m then -Real.sqrt (c k / N)
        else if m < j.val then (if k.val = 0 then -Real.sqrt (1 / N) else 0) else 0
  | .src => match s with
    | none => 0
    | some j => if 1 ≤ j.val ∧ j.val ≤ m then -Real.sqrt (d k / N) else 0
  | .junkIn => 0
  | .junkOut => if k.val = 0 then Real.sqrt (1 - restOut m K N c d s) else 0

/-- Input coefficient state. -/
def stateIn (s : Slot m) : EuclideanSpace ℂ (Term × Fin (K + 1)) :=
  WithLp.toLp 2 (fun q => (ampIn m K N c d s q.1 q.2 : ℂ))

/-- Output coefficient state. -/
def stateOut (s : Slot m) : EuclideanSpace ℂ (Term × Fin (K + 1)) :=
  WithLp.toLp 2 (fun q => (ampOut m K N c d s q.1 q.2 : ℂ))

end Coefficients

section Norms

variable (m K : ℕ) (N : ℝ) (c d : ℕ → ℝ)

theorem sum_fin_ite_zero {M : Type*} [AddCommMonoid M] (a : M) :
    ∑ k : Fin (K + 1), (if k.val = 0 then a else 0) = a := by
  rw [Fin.sum_univ_succ]
  simp

theorem sum_fin_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ k : Fin (K + 1), f k = ∑ k ∈ Finset.range (K + 1), f k :=
  Fin.sum_univ_eq_sum_range f (K + 1)

variable {m K N c d}

theorem norm_sq_state (a : Term → Fin (K + 1) → ℝ) :
    ‖(WithLp.toLp 2 (fun q : Term × Fin (K + 1) => (a q.1 q.2 : ℂ)) :
        EuclideanSpace ℂ (Term × Fin (K + 1)))‖ ^ 2 =
      ∑ t, ∑ k, a t k ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp [Complex.norm_real, sq_abs]

theorem sum_sq_ite_zero (a : ℝ) :
    ∑ k : Fin (K + 1), (if k.val = 0 then a else 0) ^ 2 = a ^ 2 := by
  have h : ∀ k : Fin (K + 1), (if k.val = 0 then a else 0) ^ 2 =
      (if k.val = 0 then a ^ 2 else 0) := by
    intro k; split_ifs <;> simp
  simp only [h]
  exact sum_fin_ite_zero K (a ^ 2)

theorem sum_sq_sqrt_div (hN : 0 < N) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ k : Fin (K + 1), Real.sqrt (f k / N) ^ 2 = (∑ k ∈ Finset.range (K + 1), f k) / N := by
  rw [Finset.sum_div, ← sum_fin_eq_range K (fun k => f k / N)]
  apply Finset.sum_congr rfl
  intro k _
  exact Real.sq_sqrt (div_nonneg (hf k) hN.le)

theorem sum_sq_neg_sqrt_div (hN : 0 < N) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ k : Fin (K + 1), (-Real.sqrt (f k / N)) ^ 2 = (∑ k ∈ Finset.range (K + 1), f k) / N := by
  simp only [neg_sq]
  exact sum_sq_sqrt_div hN f hf

theorem stateIn_norm (hN : 0 < N) (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k)
    (hrest : ∀ s, restIn m K N c d s ≤ 1)
    (s : Slot m) : ‖stateIn m K N c d s‖ = 1 := by
  have hsq : ‖stateIn m K N c d s‖ ^ 2 = 1 := by
    rw [stateIn, norm_sq_state, sum_term]
    have hr := hrest s
    have hpos : (0 : ℝ) ≤ 1 / N := by positivity
    have hid : ∑ k : Fin (K + 1), ampIn m K N c d s .id k ^ 2 = 1 / N := by
      simp only [ampIn]; rw [sum_sq_ite_zero, Real.sq_sqrt hpos]
    have hjunk : ∑ k : Fin (K + 1), ampIn m K N c d s .junkIn k ^ 2 =
        1 - restIn m K N c d s := by
      simp only [ampIn]; rw [sum_sq_ite_zero, Real.sq_sqrt (by linarith)]
    have hjo : ∑ k : Fin (K + 1), ampIn m K N c d s .junkOut k ^ 2 = 0 := by
      simp [ampIn]
    rw [hid, hjunk, hjo]
    rcases s with _ | j
    · have hstep : ∑ k : Fin (K + 1), ampIn m K N c d none .step k ^ 2 = 0 := by simp [ampIn]
      have hsrc : ∑ k : Fin (K + 1), ampIn m K N c d none .src k ^ 2 =
          (∑ k ∈ Finset.range (K + 1), d k) / N := by
        simp only [ampIn]; exact sum_sq_sqrt_div hN d hd
      rw [hstep, hsrc]
      simp only [restIn]
      ring
    · have hsrc : ∑ k : Fin (K + 1), ampIn m K N c d (some j) .src k ^ 2 = 0 := by simp [ampIn]
      have hstep : ∑ k : Fin (K + 1), ampIn m K N c d (some j) .step k ^ 2 =
          (if j.val < m then (∑ k ∈ Finset.range (K + 1), c k) / N
            else if j.val < 2 * m then 1 / N else 0) := by
        simp only [ampIn]
        split_ifs with h1 h2
        · exact sum_sq_sqrt_div hN c hc
        · rw [sum_sq_ite_zero, Real.sq_sqrt hpos]
        · simp
      rw [hstep, hsrc]
      simp only [restIn]
      ring
  have h0 : 0 ≤ ‖stateIn m K N c d s‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖stateIn m K N c d s‖ - 1)]

theorem stateOut_norm (hN : 0 < N) (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k)
    (hrest : ∀ s, restOut m K N c d s ≤ 1) (s : Slot m) :
    ‖stateOut m K N c d s‖ = 1 := by
  have hsq : ‖stateOut m K N c d s‖ ^ 2 = 1 := by
    rw [stateOut, norm_sq_state, sum_term]
    have hr := hrest s
    have hpos : (0 : ℝ) ≤ 1 / N := by positivity
    have hid : ∑ k : Fin (K + 1), ampOut m K N c d s .id k ^ 2 = 1 / N := by
      simp only [ampOut]; rw [sum_sq_ite_zero, Real.sq_sqrt hpos]
    have hjunk : ∑ k : Fin (K + 1), ampOut m K N c d s .junkOut k ^ 2 =
        1 - restOut m K N c d s := by
      simp only [ampOut]; rw [sum_sq_ite_zero, Real.sq_sqrt (by linarith)]
    have hji : ∑ k : Fin (K + 1), ampOut m K N c d s .junkIn k ^ 2 = 0 := by
      simp [ampOut]
    rw [hid, hjunk, hji]
    rcases s with _ | j
    · have hstep : ∑ k : Fin (K + 1), ampOut m K N c d none .step k ^ 2 = 0 := by simp [ampOut]
      have hsrc : ∑ k : Fin (K + 1), ampOut m K N c d none .src k ^ 2 = 0 := by simp [ampOut]
      rw [hstep, hsrc]
      simp only [restOut]
      ring
    · have hstep : ∑ k : Fin (K + 1), ampOut m K N c d (some j) .step k ^ 2 =
          (if 1 ≤ j.val ∧ j.val ≤ m then (∑ k ∈ Finset.range (K + 1), c k) / N
            else if m < j.val then 1 / N else 0) := by
        simp only [ampOut]
        split_ifs with h1 h2
        · exact sum_sq_neg_sqrt_div hN c hc
        · rw [show (fun k : Fin (K + 1) => (if k.val = 0 then -Real.sqrt (1 / N) else 0) ^ 2) =
            (fun k : Fin (K + 1) => (if k.val = 0 then Real.sqrt (1 / N) else 0) ^ 2) by
              funext k; split_ifs <;> simp]
          rw [sum_sq_ite_zero, Real.sq_sqrt hpos]
        · simp
      have hsrc : ∑ k : Fin (K + 1), ampOut m K N c d (some j) .src k ^ 2 =
          (if 1 ≤ j.val ∧ j.val ≤ m then (∑ k ∈ Finset.range (K + 1), d k) / N else 0) := by
        simp only [ampOut]
        split_ifs with h1
        · exact sum_sq_neg_sqrt_div hN d hd
        · simp
      rw [hstep, hsrc]
      simp only [restOut]
      split_ifs <;> ring
  have h0 : 0 ≤ ‖stateOut m K N c d s‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖stateOut m K N c d s‖ - 1)]

end Norms

section Identity

variable {m K : ℕ} {N : ℝ} {c d : ℕ → ℝ} {n : Type} [Fintype n] [DecidableEq n]

theorem entry_one {ι : Type*} [Fintype ι] [DecidableEq ι] (s' s : ι) :
    entry (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) s' s = if s' = s then 1 else 0 := by
  simp [entry, PiLp.single_apply]

theorem entry_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (s' s : ι) :
    entry (LookupOracle.permutationUnitary e).toContinuousLinearEquiv.toContinuousLinearMap s' s =
      if s' = e s then 1 else 0 := by
  simp [entry, LookupOracle.permutationUnitary_single, PiLp.single_apply]

/-- Uniform superposition of the slots `1, …, m`. -/
def uniformSlots (m : ℕ) : EuclideanSpace ℂ (Slot m) :=
  WithLp.toLp 2 (fun s => match s with
    | none => 0
    | some j => if 1 ≤ j.val ∧ j.val ≤ m then ((Real.sqrt m)⁻¹ : ℂ) else 0)

/-- The coefficient expression appearing in the block formula. -/
def termSum (t : Term) (R : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (f : Fin (K + 1) → Slot m → ℂ) (s' : Slot m) : ℂ :=
  ∑ k, conj (stateOut m K N c d s' (t, k)) *
    ∑ s, (stateIn m K N c d s (t, k) * f k s) * entry R s' s

theorem termSum_junkIn (R : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (f : Fin (K + 1) → Slot m → ℂ) (s' : Slot m) :
    termSum (N := N) (c := c) (d := d) .junkIn R f s' = 0 := by
  simp [termSum, stateOut, ampOut]

theorem termSum_junkOut (R : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (f : Fin (K + 1) → Slot m → ℂ) (s' : Slot m) :
    termSum (N := N) (c := c) (d := d) .junkOut R f s' = 0 := by
  simp [termSum, stateIn, ampIn]

theorem termSum_id (hN : 0 < N) (f : Fin (K + 1) → Slot m → ℂ) (s' : Slot m) :
    termSum (N := N) (c := c) (d := d) .id 1 f s' = (1 / N : ℝ) * f 0 s' := by
  unfold termSum
  simp only [entry_one, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [stateOut, stateIn, PiLp.toLp_apply, ampOut, ampIn, Complex.conj_ofReal]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false, Complex.ofReal_zero,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]

/-- Time slot `j` (the forcing slot if out of range). -/
def tslot (m : ℕ) (j : ℕ) : Slot m := if h : j < 2 * m + 1 then some ⟨j, h⟩ else none

theorem tslot_of_lt (j : ℕ) (h : j < 2 * m + 1) : tslot m j = some ⟨j, h⟩ := by
  simp [tslot, h]

theorem sum_entry_perm {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ ι) (g : ι → ℂ) (s' : ι) :
    ∑ s, g s * entry (LookupOracle.permutationUnitary e).toContinuousLinearEquiv.toContinuousLinearMap
      s' s = g (e.symm s') := by
  simp only [entry_perm, mul_ite, mul_one, mul_zero]
  have h : ∀ s, (s' = e s) = (s = e.symm s') := by
    intro s; apply propext; constructor
    · intro h; rw [h, Equiv.symm_apply_apply]
    · intro h; rw [h, Equiv.apply_symm_apply]
  simp only [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem termSum_step (hN : 0 < N) (hc : ∀ k, 0 ≤ c k) (f : Fin (K + 1) → Slot m → ℂ)
    (j : ℕ) (hj : j < 2 * m + 1) :
    termSum (N := N) (c := c) (d := d) .step
        (LookupOracle.permutationUnitary (slotShift m)).toContinuousLinearEquiv.toContinuousLinearMap
        f (some ⟨j, hj⟩) =
      if 1 ≤ j ∧ j ≤ m then -(∑ k : Fin (K + 1), ((c k / N : ℝ) : ℂ) * f k (tslot m (j - 1)))
      else if m < j then -(((1 / N : ℝ) : ℂ) * f 0 (tslot m (j - 1))) else 0 := by
  unfold termSum
  simp only [sum_entry_perm]
  split_ifs with h1 h2
  · rw [slotShift_symm_some m j hj h1.1, ← tslot_of_lt (m := m) (j - 1) (by omega), ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro k _
    simp only [stateOut, stateIn, PiLp.toLp_apply, ampOut, ampIn, h1, and_self, if_true,
      Complex.conj_ofReal]
    rw [tslot_of_lt (m := m) (j - 1) (by omega)]
    simp only [show j - 1 < m by omega, if_true]
    rw [Complex.ofReal_neg, neg_mul, ← mul_assoc, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (div_nonneg (hc k) hN.le)]
  · rw [slotShift_symm_some m j hj (by omega)]
    simp only [stateOut, stateIn, PiLp.toLp_apply, ampOut, ampIn, h1, if_false, h2, if_true,
      Complex.conj_ofReal]
    simp only [show ¬ (j - 1 < m) by omega, if_false, show j - 1 < 2 * m by omega, if_true]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, if_true, Fin.val_succ, Nat.succ_ne_zero, if_false,
      Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, add_zero, mul_zero]
    rw [tslot_of_lt (m := m) (j - 1) (by omega), Complex.ofReal_neg, neg_mul, ← mul_assoc,
      ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  · apply Finset.sum_eq_zero
    intro k _
    simp only [stateOut, PiLp.toLp_apply, ampOut, h1, if_false, h2, Complex.ofReal_zero,
      map_zero, zero_mul]

theorem termSum_step_none (f : Fin (K + 1) → Slot m → ℂ) :
    termSum (N := N) (c := c) (d := d) .step
        (LookupOracle.permutationUnitary (slotShift m)).toContinuousLinearEquiv.toContinuousLinearMap
        f none = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  simp [stateOut, ampOut]

theorem termSum_src (hN : 0 < N) (hd : ∀ k, 0 ≤ d k)
    (Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (hRc : ∀ s', entry Rc s' none = uniformSlots m s')
    (f : Fin (K + 1) → Slot m → ℂ) (s' : Slot m) :
    termSum (N := N) (c := c) (d := d) .src Rc f s' =
      match s' with
      | none => 0
      | some j => if 1 ≤ j.val ∧ j.val ≤ m then
          -(((Real.sqrt m)⁻¹ : ℝ) : ℂ) * ∑ k : Fin (K + 1), ((d k / N : ℝ) : ℂ) * f k none
          else 0 := by
  unfold termSum
  have hsum : ∀ k : Fin (K + 1), ∑ s, (stateIn m K N c d s (.src, k) * f k s) * entry Rc s' s =
      ((Real.sqrt (d k / N) : ℝ) : ℂ) * f k none * uniformSlots m s' := by
    intro k
    rw [Fintype.sum_option]
    simp only [stateIn, PiLp.toLp_apply, ampIn, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, add_zero, hRc]
  simp only [hsum]
  rcases s' with _ | ⟨j, hj⟩
  · apply Finset.sum_eq_zero; intro k _
    simp [stateOut, ampOut]
  · simp only
    split_ifs with h1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _
      simp only [stateOut, PiLp.toLp_apply, ampOut, h1, and_self, if_true, uniformSlots,
        Complex.conj_ofReal]
      rw [Complex.ofReal_neg]
      have hsq : ((Real.sqrt (d k / N) : ℝ) : ℂ) * ((Real.sqrt (d k / N) : ℝ) : ℂ) =
          ((d k / N : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (div_nonneg (hd k) hN.le)]
      push_cast at hsq ⊢
      linear_combination (-(↑(Real.sqrt ↑m))⁻¹ * f k none) * hsq
    · apply Finset.sum_eq_zero; intro k _
      simp [stateOut, ampOut, h1]

/-- The term-selected slot unitaries. -/
def slotUnitaries (Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m)) :
    Term → (EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
  | .id => 1
  | .step => (LookupOracle.permutationUnitary (slotShift m)).toContinuousLinearEquiv.toContinuousLinearMap
  | .src => Rc
  | .junkIn => 1
  | .junkOut => 1

/-- The implemented step polynomial `V = ∑ c_k P_k`. -/
def stepPoly (c : ℕ → ℝ) (Pk : Fin (K + 1) → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ∑ k : Fin (K + 1), ((c k : ℝ) : ℂ) • Pk k

omit [DecidableEq n] in
theorem stepPoly_apply (c : ℕ → ℝ) (Pk : Fin (K + 1) → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (v : EuclideanSpace ℂ n) (i : n) :
    stepPoly c Pk v i = ∑ k : Fin (K + 1), ((c k : ℝ) : ℂ) * Pk k v i := by
  simp [stepPoly, sum_apply, smul_apply]

omit [DecidableEq n] in
/-- The block of the history combination is `N⁻¹` times the history residual. -/
theorem block_eq_residual (hN : 0 < N) (hc : ∀ k, 0 ≤ c k) (hd : ∀ k, 0 ≤ d k)
    (Pk : Fin (K + 1) → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (hRc : ∀ s', entry Rc s' none = uniformSlots m s')
    (y : EuclideanSpace ℂ (Slot m × n)) (s' : Slot m) (i : n) :
    ((coefMap (stateOut m K N c d))† ∘L
        selMap (fun t => liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t)) ∘L
        specHom Term ((Fin (K + 1) × Slot m) × n) (selMap (fun c' : Fin (K + 1) × Slot m => Pk c'.1)) ∘L
        coefMap (stateIn m K N c d)) y (s', i) =
      ((1 / N : ℝ) : ℂ) * (residual m (Pk 0) (stepPoly c Pk) (stepPoly d Pk)
        ((RegisterEquivalences.productFlatten (Slot m) n).symm y)) s' i := by
  rw [block_formula]
  set f : Fin (K + 1) → Slot m → ℂ := fun k s => Pk k (slice y s) i with hf
  have hsplit : (∑ t, ∑ k, conj (stateOut m K N c d s' (t, k)) *
      ∑ s, (stateIn m K N c d s (t, k) * Pk k (slice y s) i) * entry (slotUnitaries Rc t) s' s) =
      ∑ t, termSum (N := N) (c := c) (d := d) t (slotUnitaries Rc t) f s' := rfl
  rw [hsplit, sum_term]
  simp only [slotUnitaries]
  rw [termSum_junkIn, termSum_junkOut, termSum_id hN, termSum_src hN hd Rc hRc, add_zero, add_zero]
  have hy (s : Slot m) : (RegisterEquivalences.productFlatten (Slot m) n).symm y s = slice y s := by
    ext a; rfl
  rcases s' with _ | ⟨j, hj⟩
  · rw [termSum_step_none]
    simp only [residual_none, hy]
    simp [hf]
  · rw [termSum_step hN hc f j hj]
    rw [residual_some]
    simp only [hy]
    have hseq : seq ((RegisterEquivalences.productFlatten (Slot m) n).symm y) (j - 1) =
        slice y (tslot m (j - 1)) := by
      rw [seq_of_lt _ (j - 1) (by omega), tslot_of_lt (m := m) (j - 1) (by omega), hy]
    rw [hseq]
    split_ifs with h1 h2
    · simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, stepPoly_apply, smul_eq_mul,
        coupling, hf]
      have e1 : (∑ x : Fin (K + 1), ((c ↑x / N : ℝ) : ℂ) *
          ((Pk x) (slice y (tslot m (j - 1)))).ofLp i) = ((1 / N : ℝ) : ℂ) *
          ∑ x : Fin (K + 1), ((c ↑x : ℝ) : ℂ) * ((Pk x) (slice y (tslot m (j - 1)))).ofLp i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); push_cast; ring
      have e2 : (∑ x : Fin (K + 1), ((d ↑x / N : ℝ) : ℂ) * ((Pk x) (slice y none)).ofLp i) =
          ((1 / N : ℝ) : ℂ) * ∑ x : Fin (K + 1), ((d ↑x : ℝ) : ℂ) * ((Pk x) (slice y none)).ofLp i := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x _ => ?_); push_cast; ring
      rw [e1, e2]
      ring
    · simp only [PiLp.sub_apply, hf]
      ring
    · simp only [hf, sub_zero]
      ring

end Identity

end

end SparseHamiltonian.GeneralODE.Registers
