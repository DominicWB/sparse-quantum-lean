import GeneralODE.Solver.Protocol
import GeneralODE.Native.BlockEncoding

/-!
# Theorem `ode:thm:general`: general constant-coefficient equations

The problem is `x' = A x + b`, `x(0) = x₀`, with `A = -M` for the sparse
matrix `M` of the released native access model (`ODEPublicSourceMesh.generator`)
and a known spectral bound `‖A‖ ≤ Λ`; no dissipativity or normality is
assumed.  The sources are the released unitary interfaces `J₀`, `J_b` with a
unit seed and public norms `‖x₀‖ = r₀`, `‖b‖ = r_b`.

**Hypothesis.**  The near-optimal block-input linear-system solver
(Costa et al.; Dalzell) is the hypothesis `BlockSolver f q₀`
(`Solver/Interface`): `f κ δ` calls of the block encoding and preparation
give success probability at least `q₀` and direction error `δ`.  Nothing
else from outside the paper is used.

**The algorithm** (`exists_protocol`).
* Lemma `ode:lem:block` (`NativeBlock.exists_native_block`): a native program
  `q` whose selected blocks approximate `A/(8√2 Λ)` and `I`.
* The block-encoded Taylor history (`Solver/System`, `Block/*`): `m = ⌈8√2 ΛT⌉`
  steps, Taylor degree `K`, the source term `h φ₁(Ah) b` from the source
  column, `m` final copies, normalisation `7`; it calls `q` exactly `K` times.
* The solver, with `κ = 7 κ_H = O(C̄ m)` and `δ = ε/(40 g)`, compiled to the
  native oracles: every native or source query inside a masked solver call
  becomes three uncontrolled calls (`Solver/Compose`).
* Final-time decoding, a damping qubit, randomized amplification with gain
  `5 g / √q₀` and at most four attempts (`Solver/Amplify`).

**Main theorem** (`general`).  For `0 < ε ≤ 1/2`, `Λ, T > 0`, `C̄, g ≥ 1` and
`0 < q₀ ≤ 1` there is one protocol, chosen before the unknown input, such that

* in every history, the number of native matrix queries is at most
  `40 (5g/√q₀) · f(κ, δ) · 3 K · 1327104 · shape(2s, 2(K+1), log(2/ε_n))`
  (`matrixBudget`) and each source interface is called at most
  `40 (5g/√q₀) · 3 f(κ, δ)` times (`sourceBudget`);
* for every input with `‖e^{tA}‖ ≤ C̄` and `‖x(t)‖ ≤ g ‖x(T)‖` on `[0,T]`
  and `x(T) ≠ 0`, the success probability is at least `175/256 > 2/3` and the
  conditional output is a density operator within trace distance `ε` of
  `x(T)/‖x(T)‖`.

All parameters are explicit (`Plan`).  The case `T = 0` (direct preparation)
is not treated here.
-/

namespace SparseHamiltonian.GeneralODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Registers History Implemented
  ODEStateNormalization Solver NativeBlock SparseStateOverlap
open scoped InnerProduct BigOperators ComplexConjugate Nat
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The register of the protocol: the masked native workspace of the solver
branches, with the damping qubit. -/
abbrev Register (n Z : Type) [Fintype n] [Fintype Z] (N Tn d m K w : ℕ) :=
  Amplify.Damped (NativeMaskedOracle.Physical (Fin w)
    ((Slot m × n) × HistAnc n (FlatBasis N n Z Tn d) m K))

/-- The physical oracles: the native sparse queries on one of `K` copies of
the block-encoding register (label `(i, l)`), and the two source interfaces
(labels `false`, `true`), each acting on the workspace of the released
native control with all other registers as spectators; the physical calls are
uncontrolled. -/
def physicalOracle (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (N Tn d m K w : ℕ) :
    ((Fin K × Query) ⊕ Bool) → X →
      Register n Z N Tn d m K w →L[ℂ] Register n Z N Tn d m K w :=
  Amplify.liftOracle (NativeMaskedProgram.oracle (ι := Fin w)
    (Sum.elim
      (fun il x => ((specHom (Slot m × n) (HistAnc n (FlatBasis N n Z Tn d) m K)).comp
          (specHom Term ((Ctl m K × n) × PowAnc (FlatBasis N n Z Tn d) m K)))
        (powOracle (facOracle (n := n) m K (flatOracle D N Tn d)) K il x))
      (sourceOracle (m := m) (a := HistAnc n (FlatBasis N n Z Tn d) m K) J₀ Jb)))

/-- Worst-case native matrix queries. -/
def matrixBudget (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (s : ℕ) (Λ T Cbar g ε : ℝ) : ℝ :=
  40 * Plan.gain g q₀ * (f (Plan.kappa Λ T Cbar) (Plan.delta g ε) *
    (3 * ((Plan.degree Λ T Cbar g ε : ℝ) * (1327104 * ImprovedPrecisionBudget.shape (2 * (s : ℝ))
      (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
      (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε))))))

/-- Worst-case calls of each source interface. -/
def sourceBudget (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (Λ T Cbar g ε : ℝ) : ℝ :=
  40 * Plan.gain g q₀ * (3 * f (Plan.kappa Λ T Cbar) (Plan.delta g ε))

/-- The guarantee of Theorem `ode:thm:general`: one protocol for all inputs. -/
def Outcome (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (seed : EuclideanSpace ℂ n)
    (Λ T Cbar g ε r₀ rb : ℝ) : Prop :=
  ∃ (Tn d w : ℕ) (prot : ODERepeatProtocol.Protocol
      (physicalOracle D J₀ Jb (Plan.arcDegree Λ T Cbar g ε) Tn d (Plan.steps Λ T)
        (Plan.degree Λ T Cbar g ε) w) (EuclideanSpace ℂ n)),
    (prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        matrixBudget f q₀ s Λ T Cbar g ε ∧
    (∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
        sourceBudget f q₀ Λ T Cbar g ε) ∧
    ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
      (v ≠ 0 → J₀ x seed = unitDirection v) → (b ≠ 0 → Jb x seed = unitDirection b) →
      (∀ t, 0 ≤ t → t ≤ T → ‖NormedSpace.exp (t • ODEPublicSourceMesh.generator D x)‖ ≤ Cbar) →
      (∀ t, 0 ≤ t → t ≤ T →
        ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b t‖ ≤
          g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) →
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
      Amplify.Outcome prot x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) ε

/-- The construction, for public norms with a nonzero right-hand side. -/
theorem exists_protocol (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (hsolver : BlockSolver f q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1)
    (hr : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 + r₀ ^ 2) :
    Outcome f q₀ D J₀ Jb seed Λ T Cbar g ε r₀ rb := by
  have hm : 1 ≤ Plan.steps Λ T := Plan.steps_pos hΛ hT
  have hN1 : 1 ≤ Plan.arcDegree Λ T Cbar g ε := Nat.le_add_left 1 _
  -- Lemma `ode:lem:block`
  obtain ⟨Tn, d, qP, Ein, Eout, hin, hout, hqP, hblk⟩ := exists_native_block D Λ hΛ hA
    (Plan.arcDegree Λ T Cbar g ε) hN1 (Plan.nativeError Λ T Cbar g ε)
    (Plan.nativeError_pos hΛ hT hC hg hε) (Plan.nativeError_le hΛ hT hC hg hε hε1)
  -- the history encoding
  have hτ0 : 0 ≤ Plan.alpha Λ * (T / Plan.steps Λ T) := by
    have := Plan.alpha_pos hΛ
    positivity
  have hτ1 : Plan.alpha Λ * (T / Plan.steps Λ T) ≤ 1 := by
    have hs : (0 : ℝ) < Plan.steps Λ T := by exact_mod_cast hm
    rw [← mul_div_assoc, div_le_one hs]
    exact Plan.alpha_mul_le Λ T
  -- the protocol
  obtain ⟨w, prot, h1, h2, h3⟩ := exists_protocol_of_block f q₀ hsolver hq₀ hq₀1
    (histData (Plan.steps Λ T) (Plan.degree Λ T Cbar g ε) hm (Plan.alpha Λ * (T / Plan.steps Λ T))
      hτ0 hτ1 (D.slot ⟨0, D.slots_pos⟩) (flatClean D (Plan.arcDegree Λ T Cbar g ε) Tn d)
      Ein Eout hin hout)
    (flatOracle D (Plan.arcDegree Λ T Cbar g ε) Tn d)
    (flatOracle_unitary D (Plan.arcDegree Λ T Cbar g ε) Tn d)
    (flatImage D (Plan.arcDegree Λ T Cbar g ε) Tn d)
    (flatOracle_valid D (Plan.arcDegree Λ T Cbar g ε) Tn d) qP
    (ODEPublicSourceMesh.generator D) J₀ Jb hJ₀ hJb seed hseed Λ T Cbar g ε (Plan.alpha Λ)
    (2 * Plan.nativeError Λ T Cbar g ε + (1 / 4) ^ Plan.arcDegree Λ T Cbar g ε / 2)
    (2 * Plan.nativeError Λ T Cbar g ε) r₀ rb rfl rfl rfl hm hT (Plan.alpha_pos hΛ)
    (Plan.alpha_mul_le Λ T) (Plan.eight_mul_le hΛ hT)
    (fun x => by
      change ‖-matrixOperator (D.matrix x)‖ ≤ Λ
      rw [norm_neg]
      exact hA x)
    (fun x => (hblk x).1) (fun x => (hblk x).2) hC hg hε hε1
    (Plan.budget_identity hΛ hT hC hg hε) (Plan.budget_matrix hΛ hT hC hg hε)
    (Plan.budget_taylor hΛ hT hC hg hε) hr
  unfold Outcome
  refine ⟨Tn, d, w, prot, h1.trans ?_, h2, h3⟩
  have hg0 : 0 ≤ 40 * Plan.gain g q₀ := by
    have := Plan.one_le_gain hg hq₀ hq₀1
    linarith
  have h2' : ∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
      sourceBudget f q₀ Λ T Cbar g ε := h2
  have hf : (0 : ℝ) ≤ f (Plan.kappa Λ T Cbar) (Plan.delta g ε) := by
    have h0 := (Nat.cast_nonneg _).trans (h2' true)
    unfold sourceBudget at h0
    have hgp : 0 < 40 * Plan.gain g q₀ := by
      have := Plan.one_le_gain hg hq₀ hq₀1
      linarith
    have h3f : 0 ≤ 3 * f (Plan.kappa Λ T Cbar) (Plan.delta g ε) := by
      by_contra hcon
      push Not at hcon
      have := mul_neg_of_pos_of_neg hgp hcon
      linarith
    linarith
  unfold matrixBudget
  apply mul_le_mul_of_nonneg_left _ hg0
  apply mul_le_mul_of_nonneg_left _ hf
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact mul_le_mul_of_nonneg_left hqP (Nat.cast_nonneg _)

omit [DecidableEq n] in
/-- The solution with zero data vanishes. -/
theorem solution_zero_zero (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (t : ℝ) :
    ODEConstantForcing.solution A 0 0 t = 0 := by
  simp [ODEConstantForcing.solution, ODEConstantForcing.response, ODEDissipative.trajectory]

/-- **Theorem `ode:thm:general`.** -/
theorem general (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (hsolver : BlockSolver f q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    Outcome f q₀ D J₀ Jb seed Λ T Cbar g ε r₀ rb := by
  by_cases hr : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 + r₀ ^ 2
  · exact exists_protocol f q₀ hsolver hq₀ hq₀1 D Λ T Cbar g ε r₀ rb hΛ hT hC hg hε hε1 hA
      J₀ Jb hJ₀ hJb seed hseed hr
  · have hr' : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * (0 : ℝ) ^ 2 + (1 : ℝ) ^ 2 := by norm_num
    obtain ⟨Tn, d, w, prot, h1, h2, -⟩ := exists_protocol f q₀ hsolver hq₀ hq₀1 D Λ T Cbar g ε
      1 0 hΛ hT hC hg hε hε1 hA J₀ Jb hJ₀ hJb seed hseed hr'
    unfold Outcome
    refine ⟨Tn, d, w, prot, h1, h2, ?_⟩
    intro x v b hv hb _ _ _ _ hne
    exfalso
    have hle : (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 + r₀ ^ 2 ≤ 0 := not_lt.mp hr
    have h0 : 0 ≤ (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 := by positivity
    have hm : (0 : ℝ) < Plan.steps Λ T := by exact_mod_cast Plan.steps_pos hΛ hT
    have hμ : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 := by
      have := Real.sqrt_pos.mpr hm
      positivity
    have hr₀ : r₀ = 0 := by nlinarith [sq_nonneg r₀]
    have hrb : rb = 0 := by
      have : (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 ≤ 0 := by nlinarith [sq_nonneg r₀]
      have : rb ^ 2 ≤ 0 := by
        by_contra hcon
        push Not at hcon
        have := mul_pos hμ hcon
        linarith
      nlinarith [sq_nonneg rb]
    have hv0 : v = 0 := norm_eq_zero.mp (hv.trans hr₀)
    have hb0 : b = 0 := norm_eq_zero.mp (hb.trans hrb)
    apply hne
    rw [hv0, hb0]
    exact solution_zero_zero _ T

end

end SparseHamiltonian.GeneralODE
