import SparseHamiltonian.PolynomialUnitarity

/-!
# A reverse signal step for phase synthesis

The signal reflection sends `(P, sqrt(1-X²) Q)` to
`(X P + (1-X²) Q, sqrt(1-X²) (P-X Q))`.  A phase chosen from the
highest coefficients cancels the highest terms in both coordinates.  Together
with parity this removes one signal degree. Induction proves exact synthesis
of every normalized pair with the required parity and degree budgets.
The separate existence of a suitable approximating and complementary pair
is not asserted here.
-/

namespace SparseHamiltonian.PolynomialPhaseReduction

noncomputable section
open Polynomial
open scoped ComplexConjugate

/-- The good coordinate of the reverse reflection, preceded by a fixed phase. -/
def reverseGood (u : ℂ) (P Q : ℂ[X]) : ℂ[X] :=
  X * (C u * P) + (1 - X ^ 2) * Q

/-- The factored bad coordinate of that reverse reflection. -/
def reverseBad (u : ℂ) (P Q : ℂ[X]) : ℂ[X] := C u * P - X * Q

/-- A single signal reflection is an involution at the polynomial level. -/
theorem reflection_involution (P Q : ℂ[X]) :
    reverseGood 1 (reverseGood 1 P Q) (reverseBad 1 P Q) = P ∧
    reverseBad 1 (reverseGood 1 P Q) (reverseBad 1 P Q) = Q := by
  constructor <;> simp only [reverseGood, reverseBad, map_one, one_mul] <;> ring

/-- Equal-modulus coefficients can be aligned by one constant unit phase.
The zero coefficient case is included and uses phase one. -/
theorem exists_aligning_phase (p q : ℂ) (h : ‖p‖ = ‖q‖) :
    ∃ u : AmplitudePolynomialSequence.UnitPhase, (u : ℂ) * p = q := by
  by_cases hp : p = 0
  · have hq : q = 0 := norm_eq_zero.mp (by simpa [hp] using h.symm)
    refine ⟨⟨1, norm_one⟩, ?_⟩
    simp [hp, hq]
  · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
    refine ⟨⟨q / p, ?_⟩, ?_⟩
    · rw [norm_div, ← h, div_self hn]
    · exact div_mul_cancel₀ q hp

/-- Cancelling the last allowed coefficient lowers a degree bound by one. -/
theorem degree_drop (P : ℂ[X]) (n : ℕ) (hP : P.natDegree ≤ n + 1)
    (hzero : P.coeff (n + 1) = 0) : P.natDegree ≤ n := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  by_cases hkn : k = n + 1
  · simpa [hkn] using hzero
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- Coefficient form of parity, valid for either sign. -/
def HasParity (P : ℂ[X]) (n : ℕ) : Prop :=
  P.comp (-X) = C ((-1 : ℂ) ^ n) * P

/-- The coefficient immediately opposite the prescribed parity vanishes. -/
theorem parity_next_coeff_zero (P : ℂ[X]) (n : ℕ) (h : HasParity P n) :
    P.coeff (n + 1) = 0 := by
  have hc := congrArg (fun R : ℂ[X] => R.coeff (n + 1)) h
  have hneg : (-X : ℂ[X]) = C (-1) * X := by simp
  rw [hneg, comp_C_mul_X_coeff, coeff_C_mul, pow_succ] at hc
  have hz : (2 : ℂ) * ((-1 : ℂ) ^ n) * P.coeff (n + 1) = 0 := by
    linear_combination -hc
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))

/-- A parity constraint removes a last coefficient of the wrong parity. -/
theorem parity_degree_drop (P : ℂ[X]) (n : ℕ) (hP : P.natDegree ≤ n + 1)
    (hp : HasParity P n) : P.natDegree ≤ n :=
  degree_drop P n hP (parity_next_coeff_zero P n hp)

/-- The two forward parity classes exchange under a reverse signal step. -/
theorem reverse_parity (u : ℂ) (P Q : ℂ[X]) (n : ℕ)
    (hP : HasParity P (n + 1)) (hQ : HasParity Q n) :
    HasParity (reverseGood u P Q) n ∧ HasParity (reverseBad u P Q) (n + 1) := by
  unfold HasParity at *
  simp only [reverseGood, reverseBad, add_comp, sub_comp, mul_comp, pow_comp,
    X_comp, C_comp, one_comp, hP, hQ, pow_succ, map_mul, map_neg, map_one]
  constructor <;> ring

/-- Before cancellation the good coordinate has degree at most two higher. -/
theorem reverseGood_degree (u : ℂ) (P Q : ℂ[X]) (n : ℕ)
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n) :
    (reverseGood u P Q).natDegree ≤ n + 2 := by
  have hCP : (C u * P).natDegree ≤ n + 1 := (natDegree_C_mul_le u P).trans hP
  have hXP : (X * (C u * P)).natDegree ≤ n + 2 :=
    natDegree_mul_le.trans (by simpa only [natDegree_X] using (by omega : 1 + (C u * P).natDegree ≤ n + 2))
  have hfactor : (1 - X ^ 2 : ℂ[X]).natDegree ≤ 2 :=
    (natDegree_sub_le _ _).trans (by simp)
  have hQ' : ((1 - X ^ 2) * Q).natDegree ≤ n + 2 :=
    natDegree_mul_le.trans (by omega)
  exact (natDegree_add_le _ _).trans (max_le hXP hQ')

/-- Before cancellation the bad coordinate has degree at most one higher. -/
theorem reverseBad_degree (u : ℂ) (P Q : ℂ[X]) (n : ℕ)
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n) :
    (reverseBad u P Q).natDegree ≤ n + 1 := by
  have hCP : (C u * P).natDegree ≤ n + 1 := (natDegree_C_mul_le u P).trans hP
  have hXQ : (X * Q).natDegree ≤ n + 1 :=
    natDegree_mul_le.trans (by simpa only [natDegree_X] using (by omega : 1 + Q.natDegree ≤ n + 1))
  exact (natDegree_sub_le _ _).trans (max_le hCP hXQ)

/-- The two potentially leading coefficients have exactly the same cancellation. -/
theorem reverse_top_coefficients (u : ℂ) (P Q : ℂ[X]) (n : ℕ)
    (hQ : Q.natDegree ≤ n) :
    (reverseGood u P Q).coeff (n + 2) = u * P.coeff (n + 1) - Q.coeff n ∧
    (reverseBad u P Q).coeff (n + 1) = u * P.coeff (n + 1) - Q.coeff n := by
  constructor
  · have hrewrite : reverseGood u P Q = X * (C u * P) + Q - X ^ 2 * Q := by
      unfold reverseGood
      ring
    rw [hrewrite, coeff_sub, coeff_add]
    rw [show n + 2 = (n + 1) + 1 by omega, coeff_X_mul, coeff_C_mul]
    rw [show n + 1 + 1 = n + 2 by omega, coeff_X_pow_mul,
      coeff_eq_zero_of_natDegree_lt (show Q.natDegree < n + 2 by omega)]
    ring
  · simp only [reverseBad, coeff_sub, coeff_C_mul, coeff_X_mul]

/-- Alignment removes the leading terms; parity then removes the next terms.
Thus one reverse signal query reduces both degree budgets by one. -/
theorem reverse_degree_reduction (u : ℂ) (P Q : ℂ[X]) (n : ℕ)
    (hP : P.natDegree ≤ n + 2) (hQ : Q.natDegree ≤ n + 1)
    (hp : HasParity P (n + 2)) (hq : HasParity Q (n + 1))
    (halign : u * P.coeff (n + 2) = Q.coeff (n + 1)) :
    (reverseGood u P Q).natDegree ≤ n + 1 ∧
    (reverseBad u P Q).natDegree ≤ n := by
  have htop := reverse_top_coefficients u P Q (n + 1) hQ
  have hp' : P.natDegree ≤ n + 1 + 1 := by omega
  have hpar := reverse_parity u P Q (n + 1) hp hq
  have hgood := degree_drop (reverseGood u P Q) (n + 2)
    (by simpa only [Nat.add_assoc] using reverseGood_degree u P Q (n + 1) hp' hQ)
    (by simpa [Nat.add_assoc, halign] using htop.1)
  have hbad := degree_drop (reverseBad u P Q) (n + 1)
    (reverseBad_degree u P Q (n + 1) hp' hQ)
    (by simpa [Nat.add_assoc, halign] using htop.2)
  constructor
  · exact parity_degree_drop _ (n + 1) hgood hpar.1
  · have hsame : ((-1 : ℂ) ^ (n + 2)) = (-1 : ℂ) ^ n := by
      rw [pow_add]
      norm_num
    apply parity_degree_drop _ n hbad
    simpa only [HasParity, Nat.add_assoc, hsame] using hpar.2

/-- A constant polynomial with odd parity is zero. -/
theorem odd_constant_zero (P : ℂ[X]) (hP : P.natDegree ≤ 0)
    (hp : HasParity P 1) : P = 0 := by
  have heq := eq_C_of_natDegree_le_zero hP
  have hc := congrArg (fun R : ℂ[X] => R.coeff 0) hp
  have hneg : (-X : ℂ[X]) = C (-1) * X := by simp
  rw [hneg, comp_C_mul_X_coeff, coeff_C_mul] at hc
  norm_num at hc
  have hz : P.coeff 0 = 0 := by linear_combination (1 / 2 : ℂ) * hc
  simpa [hz] using heq

/-- The last reverse step reaches a constant good coordinate and zero bad coordinate. -/
theorem reverse_degree_one (u : ℂ) (P Q : ℂ[X])
    (hP : P.natDegree ≤ 1) (hQ : Q.natDegree ≤ 0)
    (hp : HasParity P 1) (hq : HasParity Q 0)
    (halign : u * P.coeff 1 = Q.coeff 0) :
    (reverseGood u P Q).natDegree ≤ 0 ∧ reverseBad u P Q = 0 := by
  have htop := reverse_top_coefficients u P Q 0 hQ
  have hpar := reverse_parity u P Q 0 hp hq
  have hgood := degree_drop (reverseGood u P Q) 1
    (reverseGood_degree u P Q 0 hP hQ) (by simpa [halign] using htop.1)
  have hbad := degree_drop (reverseBad u P Q) 0
    (reverseBad_degree u P Q 0 hP hQ) (by simpa [halign] using htop.2)
  exact ⟨parity_degree_drop _ 0 hgood hpar.1, odd_constant_zero _ hbad hpar.2⟩

/-- One forward reflection followed by a fixed phase on the good coordinate. -/
def forwardGood (u : ℂ) (P Q : ℂ[X]) : ℂ[X] := C u * reverseGood 1 P Q

/-- A reversed step reconstructs the input pair with the conjugate phase. -/
theorem reconstruct (u : AmplitudePolynomialSequence.UnitPhase) (P Q : ℂ[X]) :
    forwardGood (conj (u : ℂ)) (reverseGood u P Q) (reverseBad u P Q) = P ∧
    reverseBad 1 (reverseGood u P Q) (reverseBad u P Q) = Q := by
  have hu : conj (u : ℂ) * (u : ℂ) = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.property]
    norm_num
  have hC : C (conj (u : ℂ)) * C (u : ℂ) = (1 : ℂ[X]) := by
    rw [← C_mul, hu, map_one]
  constructor
  · calc
      _ = (C (conj (u : ℂ)) * C (u : ℂ)) * P := by
        simp only [forwardGood, reverseGood, reverseBad, map_one, one_mul]
        ring
      _ = P := by rw [hC, one_mul]
  · simp only [reverseGood, reverseBad, map_one, one_mul]
    ring

/-- A reverse step preserves the complete polynomial normalization identity. -/
theorem reverse_normalized (u : AmplitudePolynomialSequence.UnitPhase)
    (P Q : ℂ[X]) (h : PolynomialUnitarity.IsNormalized P Q) :
    PolynomialUnitarity.IsNormalized (reverseGood u P Q) (reverseBad u P Q) := by
  unfold PolynomialUnitarity.IsNormalized at *
  rw [reverseGood, reverseBad, PolynomialUnitarity.normForm_reflect,
    PolynomialUnitarity.normForm_phase]
  exact h

/-- A normalized pair always admits a phase that removes one signal degree.
No phase-existence assumption is supplied by the caller. -/
theorem exists_reverse_reduction (P Q : ℂ[X]) (n : ℕ)
    (hP : P.natDegree ≤ n + 2) (hQ : Q.natDegree ≤ n + 1)
    (hp : HasParity P (n + 2)) (hq : HasParity Q (n + 1))
    (h : PolynomialUnitarity.IsNormalized P Q) :
    ∃ u : AmplitudePolynomialSequence.UnitPhase,
      (reverseGood u P Q).natDegree ≤ n + 1 ∧
      (reverseBad u P Q).natDegree ≤ n ∧
      HasParity (reverseGood u P Q) (n + 1) ∧
      HasParity (reverseBad u P Q) n ∧
      PolynomialUnitarity.IsNormalized (reverseGood u P Q) (reverseBad u P Q) := by
  obtain ⟨u, hu⟩ := exists_aligning_phase _ _
    (PolynomialUnitarity.leading_coeff_norm P Q (n + 1) hP hQ h)
  have hd := reverse_degree_reduction u P Q n hP hQ hp hq hu
  have hpar := reverse_parity u P Q (n + 1) hp hq
  refine ⟨u, hd.1, hd.2, hpar.1, ?_, reverse_normalized u P Q h⟩
  have hsame : ((-1 : ℂ) ^ (n + 2)) = (-1 : ℂ) ^ n := by
    rw [pow_add]
    norm_num
  simpa only [HasParity, Nat.add_assoc, hsame] using hpar.2

/-- Lists of one-query reflections with fixed good-coordinate phases.
The terminal phase prepares a constant polynomial; the list head executes last. -/
def synthesized (v : AmplitudePolynomialSequence.UnitPhase) :
    List AmplitudePolynomialSequence.UnitPhase → ℂ[X] × ℂ[X]
  | [] => (C (v : ℂ), 0)
  | u :: us => (forwardGood u (synthesized v us).1 (synthesized v us).2,
    reverseBad 1 (synthesized v us).1 (synthesized v us).2)

/-- Conjugating a phase preserves its admissibility. -/
def conjugatePhase (u : AmplitudePolynomialSequence.UnitPhase) :
    AmplitudePolynomialSequence.UnitPhase := ⟨conj (u : ℂ), by simpa using u.property⟩

/-- Algebraic converse: every normalized pair with the required degrees and
parities is exactly synthesized by a terminal phase and `n+1` signal reflections.
This theorem includes degree-deficient and zero-leading-coefficient pairs. -/
theorem synthesis (n : ℕ) (P Q : ℂ[X])
    (hP : P.natDegree ≤ n + 1) (hQ : Q.natDegree ≤ n)
    (hp : HasParity P (n + 1)) (hq : HasParity Q n)
    (h : PolynomialUnitarity.IsNormalized P Q) :
    ∃ v : AmplitudePolynomialSequence.UnitPhase,
      ∃ us : List AmplitudePolynomialSequence.UnitPhase,
        us.length = n + 1 ∧ synthesized v us = (P, Q) := by
  induction n generalizing P Q with
  | zero =>
      obtain ⟨u, hu⟩ := exists_aligning_phase _ _
        (PolynomialUnitarity.leading_coeff_norm P Q 0 hP hQ h)
      have hr := reverse_degree_one u P Q hP hQ hp hq hu
      have hc := eq_C_of_natDegree_le_zero hr.1
      have hn := reverse_normalized u P Q h
      have hv : ‖(reverseGood u P Q).coeff 0‖ = 1 :=
        PolynomialUnitarity.constant_norm _ _ (hc ▸ hn)
      let v : AmplitudePolynomialSequence.UnitPhase :=
        ⟨(reverseGood u P Q).coeff 0, hv⟩
      refine ⟨v, [conjugatePhase u], rfl, ?_⟩
      change (forwardGood (conj (u : ℂ)) (C ((reverseGood u P Q).coeff 0)) 0,
        reverseBad 1 (C ((reverseGood u P Q).coeff 0)) 0) = (P, Q)
      rw [← hc, ← hr.2]
      exact Prod.ext (reconstruct u P Q).1 (reconstruct u P Q).2
  | succ n ih =>
      obtain ⟨u, hr, hs, hpr, hps, hn⟩ :=
        exists_reverse_reduction P Q n hP hQ hp hq h
      obtain ⟨v, us, hlen, heq⟩ := ih _ _ hr hs hpr hps hn
      refine ⟨v, conjugatePhase u :: us, by simp only [List.length_cons, hlen], ?_⟩
      simp only [synthesized, heq, conjugatePhase]
      exact Prod.ext (reconstruct u P Q).1 (reconstruct u P Q).2

/-- Specialization to odd good polynomials and even bad polynomials, with the
odd query budget used by amplitude multiplication. -/
theorem synthesis_odd (m : ℕ) (P Q : ℂ[X])
    (hP : P.natDegree ≤ 2 * m + 1) (hQ : Q.natDegree ≤ 2 * m)
    (hp : P.comp (-X) = -P) (hq : Q.comp (-X) = Q)
    (h : PolynomialUnitarity.IsNormalized P Q) :
    ∃ v : AmplitudePolynomialSequence.UnitPhase,
      ∃ us : List AmplitudePolynomialSequence.UnitPhase,
        us.length = 2 * m + 1 ∧ synthesized v us = (P, Q) := by
  apply synthesis (2 * m) P Q hP hQ
  · simpa only [HasParity, pow_add, pow_mul, neg_one_sq, one_pow, one_mul,
      pow_one, map_neg, map_one, neg_mul, one_mul] using hp
  · simpa only [HasParity, pow_mul, neg_one_sq, one_pow, map_one, one_mul] using hq
  · exact h

end
end SparseHamiltonian.PolynomialPhaseReduction
