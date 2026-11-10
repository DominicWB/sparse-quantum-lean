import ManuscriptConformance.WriterGeneralEndpoint

/-!
# Theorem `ode:thm:general` at `T = 0` with a writer value oracle (handover item B4)

`ode_thm_general_zero` (the case `T = 0` of Theorem `ode:thm:general`, direct preparation of the
initial state) converted to value access by a reversible writer specified only on a clean target
(`WriterAccess`), as `ode_thm_general_writer`: the released protocol over
`GeneralODE.physicalOracle` (any register parameters) is run with every circuit compiled and every
seed and output isometry encoded (`encodeProtocol`, through `impl_generalPhysical`). The converted
protocol has the success mass and conditional output of the released one on every instance, makes
no matrix query (locator or writer call) and no forcing call, and at most `40` calls of the
initial-state preparation in every history.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseHamiltonian.WriterAccess
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 4000000 in
/-- **Theorem `ode:thm:general` at `T = 0` with a writer value oracle.** The hypotheses of
`ode_thm_general_zero` and a supplied unitary writer `Wr x` with
`Wr x |a, 0⟩ = cw x a |a, w_a⟩` for the stored words `w_a = D.table x a` and any phases. The
converted protocol `A'` of the released protocol `A` (every value call replaced by writer, adder and
inverse writer on one more scratch register, every locator and source call by the same call with
the scratch register a spectator, every seed and output isometry encoded; the converted call on
the `i`-th copy a primitive call under a fixed unital star-algebra homomorphism `Φ i`) has the
success mass and conditional output of `A` on every instance, makes no matrix query and no forcing
call and at most `40` calls of the initial-state preparation in every history, and on every
instance with `x₀ ≠ 0` succeeds with probability at least `2/3` with conditional output within
trace distance `ε` of `x₀/‖x₀‖`, for every `ε ≥ 0`. -/
theorem ode_thm_general_zero_writer {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
    (Wr : X → WReg n Z →L[ℂ] WReg n Z) (cw : X → n × n → ℂ) (hWu : ∀ x, IsUnitary (Wr x))
    (hWr : ∀ x a, Wr x (EuclideanSpace.single (a, (0 : Z)) 1) =
      cw x a • EuclideanSpace.single (a, D.table x a) 1)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) (N Tn d m K w : ℕ) (hw : 0 < w) :
    ∃ (A : ODERepeatProtocol.Protocol (GeneralODE.physicalOracle D J₀ Jb N Tn d m K w)
        (EuclideanSpace ℂ n))
      (Ow : (Fin K × WQuery) ⊕ Bool → X →
        PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w) →L[ℂ]
          PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w))
      (Φ : Fin K → (WriterAccess.Space n Z →L[ℂ] WriterAccess.Space n Z) →⋆ₐ[ℂ]
        (PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w) →L[ℂ]
          PiLp 2 (fun _ : Z => GeneralODE.Register n Z N Tn d m K w)))
      (_ : ∀ i q x, Ow (.inl (i, q)) x = Φ i (writerOracles D Wr q x))
      (_ : ∀ b x, Ow (.inr b) x = diagHom (K' := GeneralODE.Register n Z N Tn d m K w) Z
        (GeneralODE.physicalOracle D J₀ Jb N Tn d m K w (.inr b) x))
      (A' : ODERepeatProtocol.Protocol Ow (EuclideanSpace ℂ n)),
      (∀ x, A'.successMass x = A.successMass x ∧
        A'.conditionalDensity x = A.conditionalDensity x) ∧
      A'.worstCost wMatG = 0 ∧ A'.worstCost (wSrcG true) = 0 ∧
      A'.worstCost (wSrcG false) ≤ 40 ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), v ≠ 0 →
        J₀ x seed = ODEStateNormalization.unitDirection v → ∀ ε : ℝ, 0 ≤ ε →
          HeraldedOutput A' x (ODEStateNormalization.unitDirection
            (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0)) ε := by
  obtain ⟨A, h1, h2, h3, h4⟩ := ode_thm_general_zero D J₀ Jb hJ₀ hJb seed hseed N Tn d m K w hw
  obtain ⟨Ow, circ, Φ, hI, hΦ, hU⟩ := impl_generalPhysical D Wr hWu cw hWr J₀ Jb hJ₀ hJb
    N Tn d m K w
  have hmat : A.worstCost (fun l => wcostG l wMatG) ≤
      2 * A.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) :=
    protocol_worstCost_le_mul A (w₁ := fun l => wcostG l wMatG)
      (w₂ := ODESourceQueryBudget.matrixWeight (fun _ => 1)) (k := 2) wcostG_wMat_le
  have hsrc : ∀ b : Bool, (fun l => wcostG (I := Fin K) l (wSrcG b)) =
      ODESourceQueryBudget.sourceWeight b :=
    fun b => funext (wcostG_wSrc b)
  refine ⟨A, Ow, Φ, hΦ, hU, encodeProtocol hI A,
    fun x => ⟨encodeProtocol_successMass hI A x, encodeProtocol_conditionalDensity hI A x⟩, ?_, ?_,
    ?_, ?_⟩
  · rw [encodeProtocol_worstCost]
    rw [h1, mul_zero] at hmat
    exact Nat.le_zero.mp hmat
  · rw [encodeProtocol_worstCost, hsrc true]
    exact h2
  · rw [encodeProtocol_worstCost, hsrc false]
    exact h3
  · intro x v b hv hJv ε hε
    obtain ⟨g1, g2, g3⟩ := h4 x v b hv hJv ε hε
    refine ⟨?_, ?_, ?_⟩
    · rw [encodeProtocol_successMass]; exact g1
    · rw [encodeProtocol_conditionalDensity]; exact g2
    · rw [encodeProtocol_conditionalDensity]; exact g3

end

end ManuscriptConformance
