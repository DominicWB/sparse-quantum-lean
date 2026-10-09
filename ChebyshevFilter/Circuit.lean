import ChebyshevFilter.Operator
import SparseHamiltonian.WeightedClock

set_option autoImplicit false

/-!
# The normalisation-one LCU circuit with `d` signed walk steps

The proof of Proposition `qls:prop:chebyshev` implements `F_{b,d}(W) = ∑_{j=-d}^{d} p_j W^j`
on a coefficient register `ℂ^{2d+1} ⊗ V` (`Reg d V`; register value `j` carries the power
`j - d ∈ [-d, d]`, `power`):

* the seed prepares `∑_j √p_j |j⟩ ⊗ v` (`seed`, the released `WeightedClock.boundary`); it is
  an isometry since `p_j ≥ 0` and `∑_j p_j = 1` (`seed_isometry`);
* signed step `l = 1, …, d` applies `W` on the branches with `j - d ≥ l`, `W†` on those with
  `j - d ≤ -l`, and nothing on the others (`stepDir`, `signedStep`);
* after all `d` steps branch `j` has received exactly `W^{j-d}` (`signedSteps_eq`), so
  projecting back onto the seed gives `F_{b,d}(W)` itself (`lcu_compression`): there is no
  LCU normalisation factor and no amplitude amplification.

The cost of one signed step is the subject of Lemma `qls:lem:signedwalk` (`SignedWalk.lean`).
-/

namespace ChebyshevFilter

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseLinearSystems SparseLinearSystems.UnitaryFilter
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The coefficient register `ℂ^{2d+1} ⊗ V`. -/
abbrev Reg (d : ℕ) (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :=
  PiLp 2 (fun _ : Fin (2 * d + 1) => V)

/-- The power `j - d ∈ [-d, d]` carried by register value `j`. -/
def power (d : ℕ) (j : Fin (2 * d + 1)) : ℤ := ((j : ℕ) : ℤ) - d

theorem power_mem (d : ℕ) (j : Fin (2 * d + 1)) : power d j ∈ Finset.Icc (-(d : ℤ)) d := by
  have := j.isLt
  rw [Finset.mem_Icc, power]
  omega

/-- Register sums are sums over the powers `-d, …, d`. -/
theorem sum_power {M : Type*} [AddCommMonoid M] (f : ℤ → M) (d : ℕ) :
    ∑ j : Fin (2 * d + 1), f (power d j) = ∑ z ∈ Finset.Icc (-(d : ℤ)) d, f z := by
  apply Finset.sum_bij (fun j _ => power d j)
  · intro j _
    exact power_mem d j
  · intro a _ c _ h
    rw [power, power] at h
    exact Fin.ext (by omega)
  · intro z hz
    rw [Finset.mem_Icc] at hz
    refine ⟨⟨(z + d).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    rw [power]
    simp only
    omega
  · intro j _
    rfl

/-- Direction of signed step `l` on register value `j`: `W` (`some true`) when `j - d ≥ l`,
`W†` (`some false`) when `j - d ≤ -l`, inactive (`none`) otherwise. -/
def stepDir (d l : ℕ) (j : Fin (2 * d + 1)) : Option Bool :=
  if (l : ℤ) ≤ power d j then some true else if power d j ≤ -(l : ℤ) then some false else none

/-- The step selected by a direction: `W`, `W†` or `1`. -/
def dirOp (W : V →L[ℂ] V) : Option Bool → V →L[ℂ] V
  | some true => W
  | some false => W†
  | none => 1

/-- **Signed walk step `l`.** -/
def signedStep (W : V →L[ℂ] V) (d l : ℕ) : Reg d V →L[ℂ] Reg d V :=
  WeightedClock.diagonal (fun j => dirOp W (stepDir d l j))

/-- Signed steps `1, …, l`, the first applied first. -/
def signedSteps (W : V →L[ℂ] V) (d : ℕ) : ℕ → (Reg d V →L[ℂ] Reg d V)
  | 0 => 1
  | l + 1 => signedStep W d (l + 1) * signedSteps W d l

/-- The power received after `l` signed steps by a branch with target power `z`. -/
def clampPow (l : ℕ) (z : ℤ) : ℤ := max (-(l : ℤ)) (min z l)

theorem wpow_zero' (W : V →L[ℂ] V) : wpow W 0 = 1 := by
  rw [show ((0 : ℤ)) = ((0 : ℕ) : ℤ) by simp, wpow_natCast, pow_zero]

/-- One more signed step on one branch. -/
theorem dirOp_comp_wpow (W : V →L[ℂ] V) (d l : ℕ) (j : Fin (2 * d + 1)) :
    (dirOp W (stepDir d (l + 1) j)).comp (wpow W (clampPow l (power d j))) =
      wpow W (clampPow (l + 1) (power d j)) := by
  set z := power d j
  rw [stepDir]
  by_cases h1 : ((l + 1 : ℕ) : ℤ) ≤ z
  · have e1 : clampPow l z = (l : ℤ) := by rw [clampPow]; omega
    have e2 : clampPow (l + 1) z = ((l + 1 : ℕ) : ℤ) := by rw [clampPow]; omega
    rw [if_pos h1, e1, e2, dirOp, wpow_natCast, wpow_natCast, pow_succ']
    rfl
  · rw [if_neg h1]
    by_cases h2 : z ≤ -((l + 1 : ℕ) : ℤ)
    · have e1 : clampPow l z = -(l : ℤ) := by rw [clampPow]; omega
      have e2 : clampPow (l + 1) z = -((l + 1 : ℕ) : ℤ) := by rw [clampPow]; omega
      rw [if_pos h2, e1, e2, dirOp, wpow_neg_natCast, wpow_neg_natCast, pow_succ']
      rfl
    · have e : clampPow (l + 1) z = clampPow l z := by rw [clampPow, clampPow]; omega
      rw [if_neg h2, e, dirOp]
      exact ContinuousLinearMap.id_comp _

/-- **After `l` signed steps** branch `j` carries `W^{clamp_l(j - d)}`. -/
theorem signedSteps_eq (W : V →L[ℂ] V) (d l : ℕ) :
    signedSteps W d l =
      WeightedClock.diagonal (fun j : Fin (2 * d + 1) => wpow W (clampPow l (power d j))) := by
  induction l with
  | zero =>
    have h : ∀ j : Fin (2 * d + 1), wpow W (clampPow 0 (power d j)) = 1 := by
      intro j
      rw [show clampPow 0 (power d j) = 0 by rw [clampPow]; omega, wpow_zero']
    simp only [signedSteps, h]
    exact WeightedClock.diagonal_one.symm
  | succ l ih =>
    rw [signedSteps, ih, signedStep, mul_def, WeightedClock.diagonal_comp]
    congr 1
    funext j
    exact dirOp_comp_wpow W d l j

/-- **All `d` signed steps** give `W^{j-d}` on branch `j`. -/
theorem signedSteps_full (W : V →L[ℂ] V) (d : ℕ) :
    signedSteps W d d = WeightedClock.diagonal (fun j : Fin (2 * d + 1) => wpow W (power d j)) := by
  rw [signedSteps_eq]
  congr 1
  funext j
  have := power_mem d j
  rw [Finset.mem_Icc] at this
  rw [show clampPow d (power d j) = power d j by rw [clampPow]; omega]

/-- The coefficient seed `∑_j √p_{j-d} |j⟩ ⊗ v`. -/
def seed (b : ℝ) (d : ℕ) : V →L[ℂ] Reg d V :=
  WeightedClock.boundary (fun j : Fin (2 * d + 1) => filterCoeff b d (power d j)) (fun _ => 1)

theorem adjoint_one_eq : ((1 : V →L[ℂ] V)†) = 1 := by
  rw [← star_eq_adjoint, star_one]

/-- **Normalisation one**: the seed is an isometry, since `p_j ≥ 0` and `∑_j p_j = 1`. -/
theorem seed_isometry {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) :
    ((seed (V := V) b d)†) ∘L seed b d = 1 := by
  have hJ : ∀ _ : Fin (2 * d + 1), ((1 : V →L[ℂ] V)†).comp (1 : V →L[ℂ] V) = 1 :=
    fun _ => by rw [adjoint_one_eq]; rfl
  have hsum : ∑ j : Fin (2 * d + 1), filterCoeff b d (power d j) = 1 := by
    rw [sum_power (filterCoeff b d) d, sum_filterCoeff hb d]
  exact WeightedClock.boundary_isometry _ (fun j => filterCoeff_nonneg hb d _) hsum _ hJ

/-- **The LCU circuit**: the `d` signed steps, compressed to the seed, give exactly
`F_{b,d}(W)`. -/
theorem lcu_compression (W : V →L[ℂ] V) {b : ℝ} (hb : b ∈ Set.Ioo (-1 : ℝ) 1) (d : ℕ) :
    ((seed (V := V) b d)†) ∘L (signedSteps W d d ∘L seed b d) = filterOp W b d := by
  rw [seed, signedSteps_full, WeightedClock.boundary_compression _
    (fun j => filterCoeff_nonneg hb d _), filterOp,
    ← sum_power (fun z => ((filterCoeff b d z : ℝ) : ℂ) • wpow W z) d]
  apply Finset.sum_congr rfl
  intro j _
  rw [adjoint_one_eq]
  rfl

end

end ChebyshevFilter
