import AdaptiveODELowerBound.Adversary.Decision
import SparseLowerBounds.ODE.JointTheorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lemma `odel:lem:outer` and Theorem `odel:thm:joint` for adaptive protocols, general form

Manuscript: Lemma `odel:lem:outer`, Theorem `odel:thm:joint` (proof: the heralded half
measurement and the at most two membership queries per matrix query) and Proposition
`odel:rem:homogeneous` (the same reduction with another decision observable).

* `outer_count_ge_tree` (`SparseLowerBounds.ODE.outer_count_ge` and
  `Release.outer_count_ge_retry` for trees): an adaptive protocol over any labelled family
  implemented with costs `w` by membership programs, whose heralded output has signed correlation
  at least `β ≥ 0` with the half answer `halfSign M (oddCand x)`, has worst-case cost at least
  `β² n √(M m) / 8`. From `Adversary.tree_decision_count_ge` with the outer adversary of the
  released library (`outerGamma`, `outer_schurCert`, `outerDeg_le_sum_outerGamma`,
  `halfSign_oddCand_of_outerGamma_ne_zero`) and `outer_arith`.
* `outer_general_tree` (`Homogeneous.outer_general` for trees): any target `ψ x` on which a
  Hermitian contraction `D` has ideal signed correlation `a ≥ 2ε` with the half answer; an
  accurate adaptive solver has cost at least `((2/3)(a - 2ε))² n √(M 2^μ) / 8`
  (`AdaptiveHamiltonianLowerBound.tree_correlation`, eq. `odel:eq:heraldcorr`).
* `joint_general_tree` (`joint_general_retry` for trees): the instance `ψ = jointTarget`,
  `D = halfObs`, `a = 1`, bound `jointCorr ε ² n √(M 2^μ) / 8`.
-/

namespace AdaptiveODELowerBound.Joint

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE OracleCircuit
open SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open LinearSystemLowerBound (corr)
open scoped InnerProduct InnerProductSpace

-- The nested time-addressed workspaces exceed the default instance size (as in `JointTheorem`).
set_option synthInstance.maxSize 1024

variable {W B L Fl E G : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] in
/-- **Lemma `odel:lem:outer` for adaptive protocols** (Lemma `odel:lem:outer`): an adaptive protocol
over any labelled family implemented with costs `w` by membership programs, whose heralded
output has signed correlation at least `β ≥ 0` with the half answer `halfSign M (oddCand x)`,
measured by a contraction `A`, has worst-case cost at least `β² n √(M m) / 8`. -/
theorem outer_count_ge_tree {M n m : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hme : Even m) (P : ProjFamily B (Fin M × Fin n × Fin m)) (Enc : W →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) (O : L → Promised M n m → W →L[ℂ] W)
    (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (T : Tree O Fl E) (A : E →L[ℂ] E) (hA : ‖A‖ ≤ 1) {β : ℝ} (hβ : 0 ≤ β)
    (hcorr : ∀ x, β ≤ halfSign M (oddCand x) * corr A (T.successDensity x)) :
    β ^ 2 * n * Real.sqrt ((M : ℝ) * m) / 8 ≤ T.worstCost w := by
  haveI : Nonempty (Promised M n m) := nonempty_promised (by omega) hn hm
  have hcount := Adversary.tree_decision_count_ge P membership outerGamma outerGamma_nonneg
    outerGamma_symm outerLam_nonneg (outer_schurCert hM hMe hm hme)
    (outerDeg_le_sum_outerGamma hMe hme) (fun x => halfSign M (oddCand x))
    (fun x => abs_halfSign _) halfSign_oddCand_of_outerGamma_ne_zero Enc hEnc hO w hw T A hA
    hβ hcorr
  unfold outerDeg outerLam at hcount
  rw [Nat.cast_mul] at hcount
  have hM2 : (1 : ℝ) ≤ ((M / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M / 2)
  have hm2 : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m / 2)
  have hMr : (M : ℝ) = 2 * ((M / 2 : ℕ) : ℝ) := by
    obtain ⟨r, hr⟩ := hMe
    exact_mod_cast (by omega : M = 2 * (M / 2))
  have hmr : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
    obtain ⟨r, hr⟩ := hme
    exact_mod_cast (by omega : m = 2 * (m / 2))
  have hsa := Real.sq_sqrt (show (0 : ℝ) ≤ ((M / 2 : ℕ) : ℝ) by positivity)
  have hsb := Real.sq_sqrt (show (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) by positivity)
  have hsq : Real.sqrt ((M : ℝ) * m) =
      2 * Real.sqrt ((M / 2 : ℕ) : ℝ) * Real.sqrt ((m / 2 : ℕ) : ℝ) := by
    rw [show (M : ℝ) * m = (2 * Real.sqrt ((M / 2 : ℕ) : ℝ) * Real.sqrt ((m / 2 : ℕ) : ℝ)) ^ 2 by
      rw [mul_pow, mul_pow, hsa, hsb, hMr, hmr]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  exact outer_arith hsa hsb (by positivity) hcount

/-- **The joint reduction for an arbitrary target, adaptive protocols** (proof of Theorem
`odel:thm:joint` and Proposition `odel:rem:homogeneous`): an adaptive protocol over any labelled
family implemented with costs `w` by membership programs, with success mass at least `2/3` and
conditional output `ε`-accurate for targets `ψ x` on which a Hermitian contraction `D` has ideal
signed correlation at least `a ≥ 2ε` with the half answer, has worst-case cost at least
`((2/3)(a - 2ε))² n √(M 2^μ) / 8`. -/
theorem outer_general_tree {M n μ : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    {S : Type*} [Fintype S] [DecidableEq S] {ε a : ℝ} (hεa : 2 * ε ≤ a)
    (P : ProjFamily B (Fin M × Fin n × Fin (2 ^ μ))) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    (O : L → Promised M n (2 ^ μ) → W →L[ℂ] W) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb S G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ T.successMass x) (ψ : Promised M n (2 ^ μ) → EuclideanSpace ℂ S)
    (D : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (hD : IsSelfAdjoint D) (hD1 : ‖D‖ ≤ 1)
    (hideal : ∀ x, a ≤ halfSign M (oddCand x) * (⟪ψ x, D (ψ x)⟫_ℂ).re)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x) (ψ x) ε) :
    (2 / 3 * (a - 2 * ε)) ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 8 ≤ T.worstCost w := by
  have hm := two_le_two_pow hμ
  have hβ : 0 ≤ 2 / 3 * (a - 2 * ε) := by linarith
  -- Eq. `odel:eq:heraldcorr`: heralded measurement of `D`, correlation with the half answer.
  have key : ∀ x, 2 / 3 * (a - 2 * ε) ≤ halfSign M (oddCand x) *
      corr (Readout.outObs e D) (T.successDensity x) := fun x =>
    AdaptiveHamiltonianLowerBound.tree_correlation e T x (ψ x) ε (hacc x) (hsucc x) D hD hD1
      (σ := halfSign M (oddCand x)) (a₀ := a) (abs_halfSign (oddCand x)).le (hideal x) hεa
  have h := outer_count_ge_tree hM hMe hn hm (even_two_pow hμ) P Enc hEnc O hO w hw T
    (Readout.outObs e D) ((Readout.norm_outObs_le e he D).trans hD1) hβ key
  push_cast at h
  exact h

/-- **Theorem `odel:thm:joint` for adaptive protocols, general form** (Theorem `odel:thm:joint`): an
adaptive protocol over any labelled family implemented with costs `w` by membership programs,
with success mass at least `2/3` and conditional output `ε`-accurate for
`x(T)/‖x(T)‖ = jointTarget` (`2ε ≤ 1`), has worst-case cost at least
`β² n √(M 2^μ) / 8`, `β = jointCorr ε = (2/3)(1 - 2ε)`. -/
theorem joint_general_tree {M n μ s : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n)
    (hμ : 1 ≤ μ) {ε : ℝ} (hε : 2 * ε ≤ 1)
    (P : ProjFamily B (Fin M × Fin n × Fin (2 ^ μ))) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    (O : L → Promised M n (2 ^ μ) → W →L[ℂ] W) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (T : Tree O Fl E) (e : E →L[ℂ] SysGarb (JointIndex M μ s) G) (he : e† ∘L e = 1)
    (hsucc : ∀ x, 2 / 3 ≤ T.successMass x)
    (hacc : ∀ x, DensityAccurate e (T.conditionalDensity x) (jointTarget M n μ s x) ε) :
    jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 8 ≤ T.worstCost w := by
  have h := outer_general_tree (S := JointIndex M μ s) (a := 1) hM hMe hn hμ hε P Enc hEnc O hO
    w hw T e he hsucc (jointTarget M n μ s) (halfObs M μ s) halfObs_isSelfAdjoint
    norm_halfObs_le
    (fun x => by rw [inner_halfObs_jointTarget]; nlinarith [halfSign_sq (oddCand x)]) hacc
  unfold jointCorr
  exact h

end

end AdaptiveODELowerBound.Joint
