import SparseLowerBounds.ODE.JointGraph

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Lemma `odel:lem:outer`: the joint search-parity adversary

Manuscript lines 3743-3798. For `M ≥ 2` even, `m ≥ 2` even (the paper assumes
`m ≥ 4`) and `n ≥ 1`, deciding
in which half of the candidates the unique odd candidate `a_*` of a promised
input lies (`ODE/Promise`) requires `Ω(n √(Mm))` membership queries. Here, with
explicit constants, in the bounded-error correlation form consumed by
`ODE/JointTheorem`: a Boolean program over the membership phase oracle
`x ↦ P.phase (membership x)` (any projection family `P`) whose final states
have signed correlation `β ≥ 0` with the answer `halfSign M (oddCand x)` makes at
least `β² n √(Mm) / 8` queries.

Proof (`ODE/JointGraph` and `Query/PositiveAdversary`): the outer adversary
matrix `Γ` on promised inputs (odd candidate moves across the halves, both
affected blocks change along one inner parity edge) has minimum degree
`D = (M/2) d²`, `d = nm/2`; every masked `Γ ∘ Δ_{c,k,z}` has a Schur certificate
with `λ = √(M/2) d √(m/2)` (eq. `odel:eq:outermask`); the observable gap turns
correlation `β` into overlap `≤ ‖φ₀‖² - β²/2`, and
`PositiveAdversary.decision_count_ge` gives `(β²/2) D ≤ 2 λ count`, i.e.
`count ≥ β² D / (4λ) = β² n √(Mm) / 8`.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian OracleCircuit
open scoped InnerProductSpace

/-- The arithmetic of the adversary ratio (lines 3791-3794): from
`(β²/2) (M/2) d² ≤ 2 λ Q` with `λ = √(M/2) d √(m/2)` and `d = n (m/2)`,
`Q ≥ β² n · 2 √(M/2) √(m/2) / 8`. -/
theorem outer_arith {a b A B β N Q : ℝ} (ha : a ^ 2 = A) (hb : b ^ 2 = B)
    (hpos : 0 < a * (N * B) * b)
    (h : β ^ 2 / 2 * (A * (N * B) ^ 2) ≤ 2 * (a * (N * B) * b) * Q) :
    β ^ 2 * N * (2 * a * b) / 8 ≤ Q := by
  subst ha hb
  have key : 2 * (a * (N * b ^ 2) * b) * (β ^ 2 * N * (2 * a * b) / 8) =
      β ^ 2 / 2 * (a ^ 2 * (N * b ^ 2) ^ 2) := by ring
  exact le_of_mul_le_mul_left (by rw [key]; exact h) (by linarith)

/-- **Lemma `odel:lem:outer`** (lines 3743-3798), explicit form: a Boolean
program over the joint membership oracle whose final states have signed
correlation at least `β ≥ 0` with the half answer, measured by a contraction
`A`, makes at least `β² n √(M m) / 8` queries. -/
theorem outer_count_ge {M n m : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hme : Even m) {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    (P : ProjFamily B (Fin M × Fin n × Fin m))
    (q : OracleCircuit.Program (fun x : Promised M n m => P.phase (membership x)))
    (φ₀ : B) (hφ₀ : ‖φ₀‖ ≤ 1) (A : B →L[ℂ] B) (hA : ‖A‖ ≤ 1) {β : ℝ} (hβ : 0 ≤ β)
    (hcorr : ∀ x, β ≤ halfSign M (oddCand x) * (⟪q.eval x φ₀, A (q.eval x φ₀)⟫_ℂ).re) :
    β ^ 2 * n * Real.sqrt ((M : ℝ) * m) / 8 ≤ q.count := by
  haveI : Nonempty (Promised M n m) := nonempty_promised (by omega) hn hm
  have hcount := PositiveAdversary.decision_count_ge P membership outerGamma outerGamma_nonneg
    outerGamma_symm outerLam_nonneg (outer_schurCert hM hMe hm hme)
    (outerDeg_le_sum_outerGamma hMe hme) (fun x => halfSign M (oddCand x))
    (fun x => abs_halfSign _) halfSign_oddCand_of_outerGamma_ne_zero q φ₀ hφ₀ A hA hβ hcorr
  unfold outerDeg outerLam at hcount
  rw [Nat.cast_mul] at hcount
  have hM2 : (1 : ℝ) ≤ ((M / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M / 2)
  have hm2 : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m / 2)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hMr : (M : ℝ) = 2 * ((M / 2 : ℕ) : ℝ) := by
    obtain ⟨r, hr⟩ := hMe
    exact_mod_cast (by omega : M = 2 * (M / 2))
  have hmr : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
    obtain ⟨r, hr⟩ := hme
    exact_mod_cast (by omega : m = 2 * (m / 2))
  have hsa := Real.sq_sqrt (show (0 : ℝ) ≤ ((M / 2 : ℕ) : ℝ) by positivity)
  have hsb := Real.sq_sqrt (show (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) by positivity)
  have hpa : 0 < Real.sqrt ((M / 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hpb : 0 < Real.sqrt ((m / 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt ((M : ℝ) * m) =
      2 * Real.sqrt ((M / 2 : ℕ) : ℝ) * Real.sqrt ((m / 2 : ℕ) : ℝ) := by
    rw [show (M : ℝ) * m = (2 * Real.sqrt ((M / 2 : ℕ) : ℝ) * Real.sqrt ((m / 2 : ℕ) : ℝ)) ^ 2 by
      rw [mul_pow, mul_pow, hsa, hsb, hMr, hmr]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  exact outer_arith hsa hsb (by positivity) hcount

end

end SparseLowerBounds.ODE
end
