import ManuscriptConformance.TaggedPairEntry
import SparseODE.ODENativeSimulation

/-!
# Lemma `ode:lem:tags` for an arbitrary supported pair entry: statement and simulation

`ode_lem_tags_rule` states Lemma `ode:lem:tags` for a matrix `K` computed by a public rule
`f i j (G i j) (G j i)`: the moment bounds with `p = 2s` at the known boundary `J`, and the native
circuit for the Cayley response of `C₀` with `24` original sparse calls (`6` row, `6` column,
`12` value), on a clean encoding independent of the unknown matrix, of `f` and of the Cayley
parameters; its literal adjoint implements the inverse at the same counts. No locator for the
support union occurs.

`native_at_scale_rule` composes the circuit with the sharp-clock simulation of
`SparseODE.ODEFixedTaggedQuery` (the active layer has `72` calls), and
`exists_rescaling_rule_simulations` chooses one public rescaling for every rule with the given
radius: the actual native program simulates `exp(-i t K)` to full-output error `ε` with at most
`663552 · (√(2s) ρ t + √(2s ρ t log(2/ε)) + log(2/ε))` original sparse calls (Eq. `ode:eq:hs`).
-/

namespace SparseHamiltonian.ODETaggedPairEntry

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Literal primitive circuit for one active chronological layer of the rule's Cayley action. -/
def activeProgram (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (T d r : ℕ) :
    MultiOracleCircuit.Program (ODENativeActive.oracle D T d) :=
  NativeWholeProgramActive.program (C := PUnit.{1}) (ODENativeCayley.oracle D)
    (ODENativeCayley.cleanBasis D) (program D f γ ρ) T d r

@[simp] theorem activeProgram_count (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ)
    (T d r : ℕ) : (activeProgram D f γ ρ T d r).count = 72 := by
  rw [activeProgram, NativeWholeProgramActive.program_count, program_count]

theorem activeProgram_cost (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ) (T d r : ℕ)
    (w : Query → ℕ) :
    (activeProgram D f γ ρ T d r).cost w =
      18 * w .rowLocation + 18 * w .columnLocation + 36 * w .value := by
  rw [activeProgram, NativeWholeProgramActive.program_cost, program_cost]
  ring

/-- Correctness on arbitrary coherent public and private amplitudes, with all native-control
ancillas returned to their common clean state. -/
theorem activeProgram_intertwines (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ)
    (T d r : ℕ) (x : X) :
    (activeProgram D f γ ρ T d r).eval x ∘L
        (ODENativeActive.embedding D T d).toContinuousLinearMap =
      (ODENativeActive.embedding D T d).toContinuousLinearMap ∘L
        ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
          (ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ) T d r := by
  exact NativeWholeProgramActive.program_clean_intertwines
    (C := PUnit.{1}) (B := ODENativeCayley.Basis n Z)
    (P := EuclideanSpace ℂ n) (V := ODETaggedMoments.PrivateSpace n)
    (ODENativeCayley.oracle D) (ODENativeCayley.oracle_unitary D)
    (ODENativeCayley.cleanBasis D) (ODENativeCayley.image D)
    (ODENativeCayley.valid D) (program D f γ ρ)
    (ODENativeActive.publicEmbedding D) (ODENativeActive.privateEmbedding D)
    (fun x => ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ)
    (fun x => FlatMaskedAccess.singleton_intertwines
      (V := ODETaggedMoments.PrivateSpace n) (B := ODENativeCayley.Basis n Z)
      ((program D f γ ρ).eval x)
      (ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ)
      (ODENativeCayley.clean D) (program_intertwines D f γ ρ x)) T d r x

theorem activeProgram_implementsOn (D : Data X n Z s) (f : PairRule n) (γ ρ : ℝ)
    (T d r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (ODENativeActive.oracle D T d)
      (fun x => ReuseLayerFactorization.activeClock (P := EuclideanSpace ℂ n)
        (ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ) T d r)
      (ODENativeActive.embedding D T d).toContinuousLinearMap 72 :=
  ⟨activeProgram D f γ ρ T d r, activeProgram_intertwines D f γ ρ T d r,
    (activeProgram_count D f γ ρ T d r).le⟩

/-- Every active clock letter of the sharp schedule is the rule's `72`-call layer. -/
theorem active_implementsOn_rule (D : Data X n Z s) (f : PairRule n) (γ ρ t ε : ℝ) (r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (ODENativeSimulation.oracle D γ ρ t ε)
      (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
        (P := EuclideanSpace ℂ n)
        (ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ)
        (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε r)
      (ODENativeSimulation.embedding D γ ρ t ε).toContinuousLinearMap 72 :=
  activeProgram_implementsOn D f γ ρ (ODENativeSimulation.slots (s : ℝ) γ ρ t ε)
    (ODENativeSimulation.degree (s : ℝ) γ ρ t ε) r

/-- An actual primitive sparse-oracle simulation of `exp(-i t K)` for the rule's matrix, at a
supplied public rescaling. The assumptions concern only the rule, the entry energies and scalar
parameters; there is no controlled-oracle or implementation premise. -/
theorem native_at_scale_rule (D : Data X n Z s) (f : PairRule n)
    (hf₀ : ∀ i j, f i j 0 0 = 0) (hf : ∀ i j u v, f j i v u = star (f i j u v))
    (γ ρ t ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hγOne : γ ≤ 1)
    (ht : 0 ≤ t) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrow : ∀ x i, ∑ j, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2)
    (hcol : ∀ x j, ∑ i, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2)
    (hBudget : time (2 * (s : ℝ)) (ρ * t) γ * moment γ +
      width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * t)
          (ImprovedPrecisionBudget.targetLog ε)) :
    ∃ p : MultiOracleCircuit.Program
        (K := ODENativeActive.Physical n Z (ODENativeSimulation.slots (s : ℝ) γ ρ t ε)
          (ODENativeSimulation.degree (s : ℝ) γ ρ t ε)) (ODENativeSimulation.oracle D γ ρ t ε),
      (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
        (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) ∧
      (ODENativeSimulation.input D γ ρ t ε)† ∘L ODENativeSimulation.input D γ ρ t ε = 1 ∧
      (ODENativeSimulation.output D γ ρ t ε)† ∘L ODENativeSimulation.output D γ ρ t ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L ODENativeSimulation.input D γ ρ t ε -
          ODENativeSimulation.output D γ ρ t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (pairMatrix f (D.matrix x)))‖ ≤ ε := by
  obtain ⟨p, hCount, hIn, hOut, hAction⟩ :=
    ODEFixedTaggedQuery.query_certificate
      (Label := Query)
      (K := ODENativeActive.Physical n Z (ODENativeSimulation.slots (s : ℝ) γ ρ t ε)
        (ODENativeSimulation.degree (s : ℝ) γ ρ t ε)) D
      (fun x => pairMatrix f (D.matrix x)) ρ hρ
      (fun x => pairMatrix_isHermitian f hf (D.matrix x))
      (fun x i j h₀ h₁ => pairMatrix_support f hf₀ (D.matrix x) i j h₀ h₁)
      hrow hcol γ t ε hγ hγOne ht hε hεOne hBudget (ODENativeSimulation.oracle D γ ρ t ε)
      (ODENativeActive.oracle_unitary D (ODENativeSimulation.slots (s : ℝ) γ ρ t ε)
        (ODENativeSimulation.degree (s : ℝ) γ ρ t ε))
      (ODENativeSimulation.embedding D γ ρ t ε).toContinuousLinearMap
      (ODENativeSimulation.embedding D γ ρ t ε).adjoint_comp_self
      72 (fun r _ => active_implementsOn_rule D f γ ρ t ε r)
  refine ⟨p, ?_, hIn, hOut, hAction⟩
  calc
    (p.count : ℝ) ≤ 9216 * (72 : ℝ) * ImprovedPrecisionBudget.shape
        (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) := hCount
    _ = 663552 * ImprovedPrecisionBudget.shape
        (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) := by ring

/-- One public rescaling, physical register and input/output encoding serve every admissible rule
with the given radius: the schedule depends only on `2s`, `ρ t` and `ε`. -/
theorem exists_rescaling_rule_simulations (D : Data X n Z s) (ρ t ε : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ f : PairRule n, (∀ i j, f i j 0 0 = 0) →
        (∀ i j u v, f j i v u = star (f i j u v)) →
        (∀ x i, ∑ j, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2) →
        (∀ x j, ∑ i, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2) →
        ∃ p : MultiOracleCircuit.Program
            (K := ODENativeActive.Physical n Z (ODENativeSimulation.slots (s : ℝ) γ ρ t ε)
              (ODENativeSimulation.degree (s : ℝ) γ ρ t ε))
            (ODENativeSimulation.oracle D γ ρ t ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
            (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) ∧
          (ODENativeSimulation.input D γ ρ t ε)† ∘L ODENativeSimulation.input D γ ρ t ε = 1 ∧
          (ODENativeSimulation.output D γ ρ t ε)† ∘L
            ODENativeSimulation.output D γ ρ t ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L ODENativeSimulation.input D γ ρ t ε -
              ODENativeSimulation.output D γ ρ t ε ∘L
                NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                  SparseStateOverlap.matrixOperator (pairMatrix f (D.matrix x)))‖ ≤ ε := by
  have hs : (1 : ℝ) ≤ s := by
    have hsNat : 1 ≤ s := D.slots_pos
    exact_mod_cast hsNat
  have hsTwo : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision
      (2 * (s : ℝ)) (ρ * t) ε hsTwo (mul_nonneg hρ.le ht) hε hεOne
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro f hf₀ hf hrow hcol
  exact native_at_scale_rule D f hf₀ hf γ ρ t ε hρ hγ hγOne ht hε hεOne hrow hcol hBudget

end
end SparseHamiltonian.ODETaggedPairEntry

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.ODETaggedPairEntry
  NativeSparseBlockEncoding OracleCircuit
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- **Lemma `ode:lem:tags`** for a matrix `K` computed by a public rule from `G i j`, `G j i` and
the known edge. The rule vanishes on two zero entries (so `K` is supported on
`supp(G) ∪ supp(G†)`) and is conjugate symmetric (so `K = K†`); the row and column norms of `K`
are at most `ρ > 0`. Then the moment bounds hold with `p = 2s` at the known boundary `J`, and the
fixed `24`-call native program (chosen before the instance `x`) implements the Cayley action of
`γ C₀` exactly on a clean encoding independent of `x`, `f`, `γ` and `ρ`, with `6` row, `6` column
and `12` value calls; the literal adjoint implements the inverse at the same counts. -/
theorem ode_lem_tags_rule (D : Data X n Z s) (f : PairRule n)
    (hf₀ : ∀ i j, f i j 0 0 = 0) (hf : ∀ i j u v, f j i v u = star (f i j u v))
    (ρ : ℝ) (hρ : 0 < ρ) (x : X)
    (hr : ∀ i, ∑ j, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2)
    (hc : ∀ j, ∑ i, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2) (γ : ℝ) :
    (ODEFixedTaggedMoments.boundary D)† ∘L ODEFixedTaggedMoments.boundary D = 1 ∧
    (ODEFixedTaggedMoments.generator D x (pairMatrix f (D.matrix x)) ρ)† =
      ODEFixedTaggedMoments.generator D x (pairMatrix f (D.matrix x)) ρ ∧
    ‖ODEFixedTaggedMoments.generator D x (pairMatrix f (D.matrix x)) ρ‖ ≤
      Real.sqrt (2 * (s : ℝ)) ∧
    ‖ODEFixedTaggedMoments.generator D x (pairMatrix f (D.matrix x)) ρ ∘L
      ODEFixedTaggedMoments.boundary D‖ ≤ 1 ∧
    (ODEFixedTaggedMoments.boundary D)† ∘L
        ODEFixedTaggedMoments.generator D x (pairMatrix f (D.matrix x)) ρ ∘L
          ODEFixedTaggedMoments.boundary D =
      ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ •
        SparseStateOverlap.matrixOperator (pairMatrix f (D.matrix x)) ∧
    ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ =
      ImprovedCayleyMoments.cayleyAction
        (CayleyClockInterface.scaled
          (ODEFixedTaggedMoments.generator D x (pairMatrix f (D.matrix x)) ρ) γ)
        (ODEFixedTaggedMoments.inverse D x (pairMatrix f (D.matrix x)) ρ γ) ∧
    (program D f γ ρ).eval x ∘L (ODENativeCayley.clean D).toContinuousLinearMap =
      (ODENativeCayley.clean D).toContinuousLinearMap ∘L
        ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ ∧
    (program D f γ ρ).adjoint.eval x ∘L (ODENativeCayley.clean D).toContinuousLinearMap =
      (ODENativeCayley.clean D).toContinuousLinearMap ∘L
        (ODEFixedTaggedMoments.action D x (pairMatrix f (D.matrix x)) ρ γ)† ∧
    (∀ w : Query → ℕ, (program D f γ ρ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value) ∧
    (∀ w : Query → ℕ, (program D f γ ρ).adjoint.cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 12 * w .value) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ODEFixedTaggedMoments.native_moment_certificate D x
    (pairMatrix f (D.matrix x)) (pairMatrix_isHermitian f hf (D.matrix x)) ρ hρ
    (fun i j h₀ h₁ => pairMatrix_support f hf₀ (D.matrix x) i j h₀ h₁) hr hc
  exact ⟨h1, h2, h3, h4, h5,
    ODEFixedTaggedMoments.action_eq_cayley D x (pairMatrix f (D.matrix x)) ρ γ,
    program_intertwines D f γ ρ x, program_adjoint_intertwines D f γ ρ x,
    program_cost D f γ ρ, program_adjoint_cost D f γ ρ⟩

/-- The baseline simulation of `exp(-i t K)` for a rule's matrix from the original sparse
oracles only (Eq. `ode:eq:hs`), with one public rescaling for every admissible rule. -/
theorem ode_lem_tags_rule_simulation (D : Data X n Z s) (ρ t ε : ℝ)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ f : PairRule n, (∀ i j, f i j 0 0 = 0) →
        (∀ i j u v, f j i v u = star (f i j u v)) →
        (∀ x i, ∑ j, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2) →
        (∀ x j, ∑ i, ‖pairMatrix f (D.matrix x) i j‖ ^ 2 ≤ ρ ^ 2) →
        ∃ p : MultiOracleCircuit.Program
            (K := ODENativeActive.Physical n Z (ODENativeSimulation.slots (s : ℝ) γ ρ t ε)
              (ODENativeSimulation.degree (s : ℝ) γ ρ t ε))
            (ODENativeSimulation.oracle D γ ρ t ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
            (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) ∧
          (ODENativeSimulation.input D γ ρ t ε)† ∘L ODENativeSimulation.input D γ ρ t ε = 1 ∧
          (ODENativeSimulation.output D γ ρ t ε)† ∘L
            ODENativeSimulation.output D γ ρ t ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L ODENativeSimulation.input D γ ρ t ε -
              ODENativeSimulation.output D γ ρ t ε ∘L
                NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                  SparseStateOverlap.matrixOperator (pairMatrix f (D.matrix x)))‖ ≤ ε :=
  exists_rescaling_rule_simulations D ρ t ε hρ ht hε hεOne

end
end ManuscriptConformance
