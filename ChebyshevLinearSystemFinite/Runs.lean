import ChebyshevLinearSystemFinite.GateApprox
import SparseLinearSystems.Protocol.Leaf
import SparseLinearSystems.Circuit.Facts

set_option autoImplicit false

/-!
# Measured runs with approximate known gates

A run of the released protocol layer (`Protocol.TestRun`) is a public program `C`, a public unit
seed `ψ` and a public flag isometry `F`; its unnormalised success vector is `F† C_x ψ` (`amp`)
and its Born success probability `‖F† C_x ψ‖²`. A final attempt is the same kind of datum with
the output isometry as its flag.

`RunApprox t t' e` (an implementation `t'` of the ideal run `t` with approximate known gates): the
circuit of `t'` is a known-gate approximation of the circuit of `t` (`GateApprox`, same oracle
calls), the seed of `t'` is within `e_ψ` of the ideal seed, the flag of `t'` within `e_F` of the
ideal flag in operator norm, and the three errors sum to at most `e`. Then `e` bounds the quantity
`ε_syn` of the manuscript, "the change in its unnormalised success vector due to all known-gate
approximations in a test or final attempt":

* `RunApprox.amp_sub_le`: `‖F'† C'_x ψ' - F† C_x ψ‖ ≤ e` for every input;
* `RunApprox.probability_sub_le`: both success vectors have norm at most one, so the success
  probabilities differ by at most `2 e` (manuscript, before equation `qls:eq:bernoulli`;
  `probability_sub_le_of_amp`);
* `RunApprox.cost_eq`: the implemented run makes exactly the oracle calls of the ideal one.

`AmpApprox P t t' e` states the manuscript's hypothesis itself, by its effect: `t'` has the
weighted cost of `t` for every weighting of the labels (the same number of calls of every
oracle), and on every input satisfying `P` its success vector differs from that of `t` by at
most `e` (`AmpApprox.amp_sub_le`, `AmpApprox.probability_sub_le`). Nothing is assumed about how
the known gates, the seed or the flag are approximated. `RunApprox.ampApprox`: a `RunApprox`
within `e` is an `AmpApprox` within `e`, for every `P`.

`repeatLeaf t k` is the released final leaf built from a run: at most `k` fresh attempts,
stopping at the first heralded success (`Protocol.single`).
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open ContinuousLinearMap SparseHamiltonian OracleCircuit SparseLinearSystems Protocol
open scoped InnerProduct

variable {K F X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {O : L → X → K →L[ℂ] K}

/-! ### The success vector -/

/-- The unnormalised success vector `F† C_x ψ` of a run. -/
def amp (t : TestRun O F) (x : X) : F := (t.flag†) (t.circuit.eval x t.seed)

theorem probability_eq_amp (t : TestRun O F) (x : X) : t.probability x = ‖amp t x‖ ^ 2 := rfl

theorem amp_norm_le (t : TestRun O F) (x : X) (hU : IsUnitary (t.circuit.eval x)) :
    ‖amp t x‖ ≤ 1 := by
  have h1 : ‖t.circuit.eval x t.seed‖ = 1 := by
    rw [(t.circuit.eval x).norm_map_iff_adjoint_comp_self.mpr hU.1, t.seed_unit]
  calc ‖amp t x‖ ≤ ‖t.circuit.eval x t.seed‖ := Facts.adjoint_norm_le _ t.flag_isometry _
    _ = 1 := h1

/-- **Probabilities from success vectors** (manuscript, before equation `qls:eq:bernoulli`): with
unitary oracles both success vectors have norm at most one, so if they differ by at most `e` at
an input, the success probabilities differ there by at most `2 e`. -/
theorem probability_sub_le_of_amp (hO : ∀ l x, IsUnitary (O l x)) {t t' : TestRun O F}
    {e : ℝ} (x : X) (h : ‖amp t' x - amp t x‖ ≤ e) :
    |t'.probability x - t.probability x| ≤ 2 * e := by
  have h0 := amp_norm_le t x (t.circuit.eval_unitary hO x)
  have h0' := amp_norm_le t' x (t'.circuit.eval_unitary hO x)
  rw [probability_eq_amp, probability_eq_amp]
  have hfac : ‖amp t' x‖ ^ 2 - ‖amp t x‖ ^ 2 =
      (‖amp t' x‖ - ‖amp t x‖) * (‖amp t' x‖ + ‖amp t x‖) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc |‖amp t' x‖ - ‖amp t x‖| * (‖amp t' x‖ + ‖amp t x‖) ≤ e * 2 :=
        mul_le_mul ((abs_norm_sub_norm_le _ _).trans h) (by linarith) (by positivity)
          ((norm_nonneg _).trans h)
    _ = 2 * e := by ring

/-! ### Implementations with approximate known gates -/

/-- **An implementation of a run with approximate known gates.** The implemented circuit is a
known-gate approximation of the ideal circuit (same oracle calls, gate errors summing to
`e_C`), the implemented seed is within `e_ψ` of the ideal seed and the implemented flag within
`e_F` of the ideal flag (operator norm), and `e_C + e_ψ + e_F ≤ e`. -/
def RunApprox (t t' : TestRun O F) (e : ℝ) : Prop :=
  ∃ eC eψ eF : ℝ, GateApprox t.circuit t'.circuit eC ∧ ‖t'.seed - t.seed‖ ≤ eψ ∧
    ‖t'.flag - t.flag‖ ≤ eF ∧ eC + eψ + eF ≤ e

namespace RunApprox

/-- The ideal run implements itself with error zero (exact gates). -/
theorem refl (t : TestRun O F) : RunApprox t t 0 :=
  ⟨0, 0, 0, GateApprox.refl _, by rw [sub_self, norm_zero], by rw [sub_self, norm_zero],
    by norm_num⟩

theorem mono {t t' : TestRun O F} {e e' : ℝ} (h : RunApprox t t' e) (hee : e ≤ e') :
    RunApprox t t' e' := by
  obtain ⟨eC, eψ, eF, hC, hψ, hF, he⟩ := h
  exact ⟨eC, eψ, eF, hC, hψ, hF, he.trans hee⟩

/-- The implemented run makes exactly the oracle calls of the ideal run. -/
theorem cost_eq {t t' : TestRun O F} {e : ℝ} (h : RunApprox t t' e) (w : L → ℕ) :
    t'.circuit.cost w = t.circuit.cost w := by
  obtain ⟨eC, eψ, eF, hC, -⟩ := h
  exact hC.cost_eq w

/-- **The success vector changes by at most `e`**, for every input. -/
theorem amp_sub_le (hO : ∀ l x, IsUnitary (O l x)) {t t' : TestRun O F} {e : ℝ}
    (h : RunApprox t t' e) (x : X) : ‖amp t' x - amp t x‖ ≤ e := by
  obtain ⟨eC, eψ, eF, hC, hψ, hF, he⟩ := h
  have hU := t.circuit.eval_unitary hO x
  have hU' := t'.circuit.eval_unitary hO x
  have hn' : ‖t'.circuit.eval x t'.seed‖ = 1 := by
    rw [(t'.circuit.eval x).norm_map_iff_adjoint_comp_self.mpr hU'.1, t'.seed_unit]
  -- the circuit outputs
  have hout : ‖t'.circuit.eval x t'.seed - t.circuit.eval x t.seed‖ ≤ eC + eψ := by
    have e1 : t'.circuit.eval x t'.seed - t.circuit.eval x t.seed =
        (t'.circuit.eval x t'.seed - t.circuit.eval x t'.seed) +
          t.circuit.eval x (t'.seed - t.seed) := by
      rw [map_sub]; abel
    rw [e1]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have := hC.eval_apply_sub_le hO x t'.seed
      rwa [t'.seed_unit, mul_one] at this
    · calc ‖t.circuit.eval x (t'.seed - t.seed)‖ ≤ ‖t.circuit.eval x‖ * ‖t'.seed - t.seed‖ :=
            (t.circuit.eval x).le_opNorm _
        _ ≤ 1 * eψ := mul_le_mul hU.norm_le_one hψ (norm_nonneg _) zero_le_one
        _ = eψ := one_mul _
  -- the flags
  have e2 : amp t' x - amp t x =
      ((t'.flag - t.flag)†) (t'.circuit.eval x t'.seed) +
        (t.flag†) (t'.circuit.eval x t'.seed - t.circuit.eval x t.seed) := by
    simp only [amp, map_sub, sub_apply]
    abel
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖((t'.flag - t.flag)†) (t'.circuit.eval x t'.seed)‖ ≤ eF := by
    calc ‖((t'.flag - t.flag)†) (t'.circuit.eval x t'.seed)‖ ≤
          ‖(t'.flag - t.flag)†‖ * ‖t'.circuit.eval x t'.seed‖ := le_opNorm _ _
      _ = ‖t'.flag - t.flag‖ := by rw [hn', mul_one, LinearIsometryEquiv.norm_map]
      _ ≤ eF := hF
  have h2 := (Facts.adjoint_norm_le _ t.flag_isometry
    (t'.circuit.eval x t'.seed - t.circuit.eval x t.seed)).trans hout
  linarith

/-- **The success probability changes by at most `2 e`**: both success vectors have norm at
most one. -/
theorem probability_sub_le (hO : ∀ l x, IsUnitary (O l x)) {t t' : TestRun O F} {e : ℝ}
    (h : RunApprox t t' e) (x : X) : |t'.probability x - t.probability x| ≤ 2 * e :=
  probability_sub_le_of_amp hO x (h.amp_sub_le hO x)

end RunApprox

/-! ### Implementations specified by their effect -/

/-- **An implementation of a run within `e` on the inputs satisfying `P`**, specified by its effect
(the manuscript's `ε_syn`, "the change in its unnormalised success vector due to all known-gate
approximations"): the implemented run `t'` has the weighted cost of the ideal run `t` for every
weighting of the labels, and on every input satisfying `P` its unnormalised success vector differs
from that of `t` by at most `e`. -/
def AmpApprox (P : X → Prop) (t t' : TestRun O F) (e : ℝ) : Prop :=
  (∀ w : L → ℕ, t'.circuit.cost w = t.circuit.cost w) ∧ ∀ x, P x → ‖amp t' x - amp t x‖ ≤ e

namespace AmpApprox

variable {P : X → Prop} {t t' : TestRun O F} {e : ℝ}

/-- Enlarging the error budget. -/
theorem mono (h : AmpApprox P t t' e) {e' : ℝ} (hee : e ≤ e') : AmpApprox P t t' e' :=
  ⟨h.1, fun x hx => (h.2 x hx).trans hee⟩

/-- The implemented run has the weighted cost of the ideal run, for every weighting. -/
theorem cost_eq (h : AmpApprox P t t' e) (w : L → ℕ) : t'.circuit.cost w = t.circuit.cost w :=
  h.1 w

/-- The success vector changes by at most `e` on every input satisfying `P`. -/
theorem amp_sub_le (h : AmpApprox P t t' e) {x : X} (hx : P x) : ‖amp t' x - amp t x‖ ≤ e :=
  h.2 x hx

/-- **The success probability changes by at most `2 e`** on every input satisfying `P`. -/
theorem probability_sub_le (hO : ∀ l x, IsUnitary (O l x)) (h : AmpApprox P t t' e) {x : X}
    (hx : P x) : |t'.probability x - t.probability x| ≤ 2 * e :=
  probability_sub_le_of_amp hO x (h.2 x hx)

end AmpApprox

/-- **The decomposition bounds the effect**: an implementation with approximate known gates,
seed and flag within `e` (`RunApprox`) is an implementation within `e` on every set of inputs
(`AmpApprox`), by `RunApprox.cost_eq` and `RunApprox.amp_sub_le`. -/
theorem RunApprox.ampApprox (hO : ∀ l x, IsUnitary (O l x)) {t t' : TestRun O F} {e : ℝ}
    (h : RunApprox t t' e) (P : X → Prop) : AmpApprox P t t' e :=
  ⟨h.cost_eq, fun x _ => h.amp_sub_le hO x⟩

/-! ### Final leaves from runs -/

/-- **The final leaf of a run**: at most `k` fresh attempts of the run (seed, circuit, output
isometry), stopping at the first heralded success. -/
def repeatLeaf (t : TestRun O F) (k : ℕ) : ODERepeatProtocol.Protocol O F :=
  ODERepeatProtocol.Protocol.repeatTrials
    (single t.circuit t.seed t.seed_unit t.flag t.flag_isometry) k

theorem repeatLeaf_successMass (t : TestRun O F) (k : ℕ) (x : X) :
    (repeatLeaf t k).successMass x = 1 - (1 - ‖amp t x‖ ^ 2) ^ k :=
  single_successMass _ _ _ _ _ x k

theorem repeatLeaf_leafDir (t : TestRun O F) (k : ℕ) (x : X) :
    leafDir x (repeatLeaf t (k + 1)) = ODEStateNormalization.unitDirection (amp t x) :=
  leafDir_single _ _ _ _ _ x k

theorem repeatLeaf_spec (t : TestRun O F) (k : ℕ) (x : X) (hU : IsUnitary (t.circuit.eval x)) :
    0 ≤ (repeatLeaf t (k + 1)).successMass x ∧ (repeatLeaf t (k + 1)).successMass x ≤ 1 ∧
      ((repeatLeaf t (k + 1)).successMass x ≠ 0 → ‖leafDir x (repeatLeaf t (k + 1))‖ = 1) ∧
      (repeatLeaf t (k + 1)).successDensity x =
        (((repeatLeaf t (k + 1)).successMass x : ℝ) : ℂ) •
          ODEMixedOutput.pureOperator (leafDir x (repeatLeaf t (k + 1))) := by
  rw [repeatLeaf_leafDir]
  exact single_leaf_spec _ _ _ _ _ x hU (k + 1)

/-- The worst-case cost of the final leaf: `k` attempts. -/
theorem repeatLeaf_worstCost (t : TestRun O F) (k : ℕ) (w : L → ℕ) :
    (repeatLeaf t k).worstCost w = k * t.circuit.cost w := by
  rw [repeatLeaf, ODERepeatProtocol.Protocol.repeat_worstCost]
  congr 1
  exact Finset.sup_const (Finset.univ_nonempty (α := Fin 1)) _

end

end ChebyshevLinearSystemFinite
