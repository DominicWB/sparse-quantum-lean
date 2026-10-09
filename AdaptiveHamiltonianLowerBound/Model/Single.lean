import SparseLinearSystems.Protocol.Tree
import LinearSystemLowerBound.Weight.TreeBound

set_option autoImplicit false

/-!
# A non-adaptive program as an adaptive protocol

A non-adaptive algorithm of the released lower bounds is one program `p` run on an
input-independent seed `φ₀`, whose final workspace state is the output. As an adaptive
protocol (`SparseLinearSystems.Protocol.Tree`) it is one fresh trial with a single trial
label, the identity as output isometry, and no test runs (`Single.tree`). It heralds success
with probability one when the program is unitary (`successMass_tree`), its heralded and
conditional outputs are the pure state `|p φ₀⟩⟨p φ₀|` (`successDensity_tree`,
`conditionalDensity_tree`), and its worst-case cost is the cost of the program
(`worstCost_tree`). The adaptive lower bounds therefore contain the non-adaptive ones for
unit seeds (`AdaptiveHamiltonianLowerBound.main_max_programs`).
-/

namespace AdaptiveHamiltonianLowerBound

noncomputable section
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap
open scoped InnerProduct

namespace Single

variable {K F X L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

/-- One run of `p` on the unit seed `φ₀`, read directly. -/
def trial (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1) :
    ODERepeatProtocol.TrialFamily O K where
  choices := 1
  choices_pos := one_pos
  circuit _ := p
  seed := φ₀
  seed_unit := hφ₀
  output := 1
  output_isometry := by
    ext v
    simp

/-- **A non-adaptive program as an adaptive protocol**: one fresh trial, then stop. -/
def tree (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1) : Tree O F K :=
  .final (.freshTrial (trial p φ₀ hφ₀) .abort)

theorem worstCost_tree (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1)
    (w : L → ℕ) : (tree F p φ₀ hφ₀).worstCost w = p.cost w := by
  simp only [tree, Tree.worstCost, ODERepeatProtocol.Protocol.worstCost,
    ODERepeatProtocol.TrialFamily.maxCost, trial, add_zero]
  exact le_antisymm (Finset.sup_le fun _ _ => le_rfl)
    (Finset.le_sup (f := fun _ : Fin 1 => p.cost w) (Finset.mem_univ 0))

theorem meanSuccess_trial (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1)
    (x : X) : (trial p φ₀ hφ₀).meanSuccess x = ‖p.eval x φ₀‖ ^ 2 := by
  simp [ODERepeatProtocol.TrialFamily.meanSuccess, ODERepeatProtocol.TrialFamily.probability,
    ODERepeatProtocol.TrialFamily.amplitude, trial]

theorem successMass_tree (p : MultiOracleCircuit.Program O) (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1)
    (x : X) (hU : OracleCircuit.IsUnitary (p.eval x)) :
    (tree F p φ₀ hφ₀).successMass x = 1 := by
  have hn : ‖p.eval x φ₀‖ = 1 := by
    rw [(p.eval x).norm_map_iff_adjoint_comp_self.mpr hU.1, hφ₀]
  simp only [tree, Tree.successMass, Tree.expect, ODERepeatProtocol.Protocol.successMass,
    ODERepeatProtocol.Protocol.failureMass, meanSuccess_trial, hn]
  norm_num

theorem successDensity_tree [FiniteDimensional ℂ K] (p : MultiOracleCircuit.Program O)
    (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1) (x : X) :
    (tree F p φ₀ hφ₀).successDensity x = ODEMixedOutput.pureOperator (p.eval x φ₀) := by
  simp only [tree, Tree.successDensity, Tree.expect, ODERepeatProtocol.Protocol.successDensity,
    smul_zero, add_zero, ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus]
  simp [ODERepeatProtocol.TrialFamily.amplitude, trial]

theorem conditionalDensity_tree [FiniteDimensional ℂ K] (p : MultiOracleCircuit.Program O)
    (φ₀ : K) (hφ₀ : ‖φ₀‖ = 1) (x : X) (hU : OracleCircuit.IsUnitary (p.eval x)) :
    (tree F p φ₀ hφ₀).conditionalDensity x = ODEMixedOutput.pureOperator (p.eval x φ₀) := by
  rw [Tree.conditionalDensity, successMass_tree p φ₀ hφ₀ x hU, successDensity_tree]
  simp

end Single

end

end AdaptiveHamiltonianLowerBound
