import SparseLowerBounds.ODE.JointTheorem

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

/-!
# The joint reduction for an arbitrary readout target

Manuscript lines 3887-3897 (proof of Theorem `odel:thm:joint`) as used by Remark
`odel:rem:homogeneous` (lines 3935-3937, 3947-3949: "the same oracle simulation and adversary
reduction prove eq. `odel:eq:joint`"). `SparseLowerBounds.ODE.joint_general` is stated for the
basis targets `jointTarget` and the ideal correlation `1`. In the homogeneous variant the
normalised solution is not a basis state: it has probability at least `16/17` on the odd
candidate `a_*`, so the half indicator has ideal signed correlation `a ≥ 15/17`. `outer_general`
is `joint_general` with an arbitrary system type `S`, targets `ψ x`, a Hermitian contraction
`D` and an ideal signed correlation `a ≥ 2ε`: the heralded solver has Boolean cost at least
`((2/3)(a - 2ε))² n √(M 2^μ) / 8`. Proof: `Reduction.exists_boolean_program_inner`,
`Readout.heralded_correlation` (with ideal value `a`) and Lemma `odel:lem:outer`
(`outer_count_ge`), as in `joint_general`. `joint_general` is the instance
`(S, ψ, D, a) = (JointIndex M μ s, jointTarget, halfObs, 1)` (with `jointCorr ε = (2/3)(1 - 2ε)`).
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Readout
open SparseHamiltonian OracleCircuit
open scoped InnerProduct InnerProductSpace

/-- **The joint reduction for an arbitrary target** (lines 3887-3897, 3935-3937): any labelled
family whose labels are implementable with costs `w` by membership programs; a heralded solver
(success `≥ 2/3`, conditional accuracy `ε`) for targets `ψ x` on which a Hermitian contraction
`D` has ideal signed correlation at least `a ≥ 2ε` with the half answer `halfSign(a_*)`. Then
the Boolean cost is at least `((2/3)(a - 2ε))² n √(M 2^μ) / 8`.
`SparseLowerBounds.ODE.joint_general` is the instance `S = JointIndex M μ s`,
`ψ = jointTarget`, `D = halfObs`, `a = 1`. -/
theorem outer_general {M n μ : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    {S : Type*} [Fintype S] [DecidableEq S] {ε a : ℝ} (hεa : 2 * ε ≤ a) {W B L G : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (P : ProjFamily B (Fin M × Fin n × Fin (2 ^ μ))) (E : W →L[ℂ] B) (hE : E† ∘L E = 1)
    (O : L → Promised M n (2 ^ μ) → W →L[ℂ] W) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : W) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : W →L[ℂ] SysGarb S G) (he : e† ∘L e = 1)
    (herald : W →L[ℂ] W) (hherald : IsStarProjection herald)
    (hsucc : ∀ x, 2 / 3 ≤ ‖herald (p.eval x φ₀)‖ ^ 2)
    (ψ : Promised M n (2 ^ μ) → EuclideanSpace ℂ S)
    (D : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (hD : IsSelfAdjoint D) (hD1 : ‖D‖ ≤ 1)
    (hideal : ∀ x, a ≤ halfSign M (oddCand x) * (⟪ψ x, D (ψ x)⟫_ℂ).re)
    (hacc : ∀ x, HeraldedAccurate e herald (p.eval x φ₀) (ψ x) ε) :
    (2 / 3 * (a - 2 * ε)) ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 8 ≤ p.cost w := by
  obtain ⟨c, hcount, hc⟩ := Reduction.exists_boolean_program_inner E hE
    (fun x => P.isUnitary_phase (membership x)) hO w hw p
  have hm := two_le_two_pow hμ
  -- Lines 3935-3937: heralded half measurement, correlation `(2/3)(a - 2ε)`.
  have key : ∀ x, 2 / 3 * (a - 2 * ε) ≤ halfSign M (oddCand x) *
        (⟪p.eval x φ₀, (herald ∘L outObs e D ∘L herald) (p.eval x φ₀)⟫_ℂ).re ∧
      ‖herald ∘L outObs e D ∘L herald‖ ≤ 1 := fun x =>
    heralded_correlation e he herald hherald (p.eval x φ₀) (ψ x) ε (hacc x)
      (hsucc x) D hD hD1 (a := a) (abs_halfSign (oddCand x)).le (hideal x) hεa
  obtain ⟨x₀⟩ := nonempty_promised (M := M) (by omega) hn hm
  have hA := (Reduction.norm_encodeObs_le E hE _).trans (key x₀).2
  have hEφ : ‖E φ₀‖ ≤ 1 := (Reduction.norm_encode E hE φ₀).le.trans hφ₀
  have hβ : 0 ≤ 2 / 3 * (a - 2 * ε) := by linarith
  have h := outer_count_ge hM hMe hn hm (even_two_pow hμ) P c (E φ₀) hEφ _ hA hβ fun x => by
    rw [hc x φ₀]; exact (key x).1
  push_cast at h
  exact h.trans (by exact_mod_cast hcount)

end

end ODELowerBoundExtensions.Homogeneous
