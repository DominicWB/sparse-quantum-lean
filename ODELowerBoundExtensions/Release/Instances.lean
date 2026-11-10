import ODELowerBoundExtensions.Release.Normal
import ODELowerBoundExtensions.Release.Strip
import TimeDependentExtensions.ODE.Theorem
import SparseLowerBounds.Hamiltonian.Accuracy
import LinearSystemLowerBound.Weight.Bias
import GeneralODE.Block.HistoryEncoding
import SparseLowerBounds.ODE.Uniqueness

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released general-mesh ODE solver on a family of the class

Manuscript: eqs. `odel:eq:upper` and `odel:eq:refined` (the upper bounds compared with Theorem
`odel:thm:combined`) and the released Theorem `ode:thm:time` on general meshes,
`TimeDependentExtensions.ODE.solver`. This module runs the released solver on a family of the
class with `D = 0` (generators `iH`, `H` Hermitian) and shows that its output is a retry solver of
the family, with the released query bound.

**Solver data.** On the `R`-fold refinement `refineFamily F R` (`Release/Refine`): the sampled-time
input `refineData F.data R`, the mesh `t_r` of its breakpoints, `η_H = 1` and `η_D = 0`
(`hamiltonianPart (iH) = H`, `dissipativePart (iH) = 0`), time `T = τ`, `g = ḡ`, the initial norm
`r₀ = ‖x₀‖`, the forcing norms `rb_r = ‖b_{r/R}‖`, any unit seed and any unitary source interfaces
`J₀`, `J_b` that map the seed to `x₀/‖x₀‖` and to `b_k/‖b_k‖` (the premises of the released
`Outcome`). One public choice is `releaseJ₀`, `releaseJb` with seed `e_{i₀}` (`seedVec`): fixed
unitaries `prepUnitary` (any unitary when the vector is `0`), independent of the hidden input
(`releaseSources_public`). The generator and forcing samples are exact (integrated sample errors
`0`), so the solver's error budget is its public part `publicError ≤ ε B/(2000 ḡ)`, i.e.
`s Λ ((Σ_k len_k² ‖b_k‖)/(2R) + KR (τ/N) B) ≤ ε B/(2000 ḡ)` (`refine_quadrature`,
`refine_meshMass`), which holds for `R`, then `N`, large (`exists_release_params`). Neither `R`,
`N`, the mesh, `d` nor the source interfaces enter the query counts.

**Statements.**

* `ReleaseProtocol F R ι N d J₀ J_b p Θ ℓ g ε`: `p` is the released four-attempt protocol
  `ODECompleteTrial.algorithm` of one public circuit family over the release's physical oracle
  with source interfaces `J₀`, `J_b` that satisfies the released complete certificate
  `ODECompleteTrial.Certificate` for every input and every solution (target `x(T)`).
* `exists_releaseProtocol`: under the class promises, `D = 0`, `T = τ`, the public conditions of the
  solver and any admissible source interfaces and seed, `TimeDependentExtensions.ODE.solver` gives
  such a protocol with `Θ = τ` (`theta (τ·1) (τ·0) = τ`), `ℓ = releaseLog ḡ ε = log(40000 ḡ/ε)`
  (the released solver, through `ImprovedODEQueryBudget.logBudget`, instantiates the absolute
  constant `C > 1` of eq. `odel:eq:precision`, which the paper leaves unspecified, as `40000`) and
  `g = ratio ḡ = 2ḡ`.
* `ReleaseProtocol.success`, `ReleaseProtocol.accurate` (the released trace distance, read by the
  clean readout `Hamiltonian.endpointReadout 1 i₀`, any `i₀`: the instance on `releaseOracle` of
  the oracle-generic `certificate_densityAccurate` of `Release/Strip`), `ReleaseProtocol.toRetrySolver`: the release's
  protocol is a retry solver of the family over `releaseOracle`; `ReleaseProtocol.worstCost_le`:
  its worst-case matrix-query count is at most `1274019840 g · queryShape(s, Θ, ℓ)`
  (`Certificate.matrix_queries`).

Only the general-mesh solver of Theorem `ode:thm:time` is connected here. The constant-coefficient
released solver `SparseHamiltonian.ODECompleteEndpoint.solver` (Theorem `ode:thm:main`) is not;
the general-mesh solver covers the same hard families, all of which have piecewise-constant
coefficients.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit TimeDependentExtensions
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The seed of the released solver: the basis vector `e_{i₀}`. -/
def seedVec (i₀ : N) : EuclideanSpace ℂ N := EuclideanSpace.single i₀ 1

/-- The seed `e_{i₀}` is a unit vector. -/
theorem norm_seedVec (i₀ : N) : ‖seedVec i₀‖ = 1 := by
  simp [seedVec]

open Classical in
/-- **A public preparation unitary**: a fixed unitary mapping the seed `e_{i₀}` to `u/‖u‖` (the
identity when `u = 0`). -/
def prepUnitary (i₀ : N) (u : EuclideanSpace ℂ N) : SysOp N :=
  if h : ∃ W : SysOp N, IsUnitary W ∧ W (seedVec i₀) = ODEStateNormalization.unitDirection u
  then Classical.choose h else 1

/-- The public preparation is unitary. -/
theorem prepUnitary_unitary (i₀ : N) (u : EuclideanSpace ℂ N) : IsUnitary (prepUnitary i₀ u) := by
  unfold prepUnitary
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact ⟨by simp, by simp⟩

/-- The preparation maps the seed to the direction of a nonzero vector. -/
theorem prepUnitary_seed (i₀ : N) {u : EuclideanSpace ℂ N} (hu : u ≠ 0) :
    prepUnitary i₀ u (seedVec i₀) = ODEStateNormalization.unitDirection u := by
  have h : ∃ W : SysOp N, IsUnitary W ∧ W (seedVec i₀) = ODEStateNormalization.unitDirection u :=
    GeneralODE.Registers.exists_unitary_single i₀ _ (ODEStateNormalization.unitDirection_norm u hu)
  unfold prepUnitary
  rw [dif_pos h]
  exact (Classical.choose_spec h).2

variable {X Z : Type*} [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- The released solver's initial-state interface: `e_{i₀} ↦ x₀/‖x₀‖`, independent of the input. -/
def releaseJ₀ (F : Family X N Z K s) (i₀ : N) : X → SysOp N := fun _ => prepUnitary i₀ F.init

/-- The released solver's forcing interface on the refined mesh: `e_{i₀} ↦ b_r/‖b_r‖`, independent
of the input. -/
def releaseJb (F : Family X N Z K s) (R : ℕ) (i₀ : N) : X → Fin (K * R) → SysOp N :=
  fun _ r => prepUnitary i₀ ((refineFamily F R).src r)

omit [Fintype Z] [AddCommGroup Z] in
/-- The released solver's source interfaces are public. -/
theorem releaseSources_public (F : Family X N Z K s) (R : ℕ) (i₀ : N) :
    PublicSources (releaseJ₀ F i₀) (releaseJb F R i₀) where
  initial_unitary _ := prepUnitary_unitary i₀ _
  forcing_unitary _ _ := prepUnitary_unitary i₀ _
  initial_const _ _ := rfl
  forcing_const _ _ := rfl

/-- **The release's logarithm** `ℓ = logBudget(ratio ḡ, accuracy ε)`. -/
def releaseLog (gbar ε : ℝ) : ℝ :=
  ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio gbar) (TimeDependentODE.accuracy ε)

/-- `ℓ = log(40000 ḡ/ε)`: the released solver (`ImprovedODEQueryBudget.logBudget`) instantiates
the absolute constant `C > 1` of eq. `odel:eq:precision` (unspecified in the
paper) as `C = 40000`. -/
theorem releaseLog_eq (gbar ε : ℝ) : releaseLog gbar ε = Real.log (40000 * gbar / ε) := by
  unfold releaseLog ImprovedODEQueryBudget.logBudget TimeDependentODE.ratio
    TimeDependentODE.accuracy
  congr 1
  rcases eq_or_ne ε 0 with rfl | h
  · simp
  · field_simp
    ring

/-- **The released protocol on a refined family**: `p` is the four-attempt protocol
`ODECompleteTrial.algorithm` of one public circuit family over the release's physical oracle with
source interfaces `J₀`, `J_b` that satisfies the released complete certificate for every input and
every solution (target `x(T)`), with parameters `Θ`, `ℓ`, `g`, `ε`. -/
def ReleaseProtocol [DecidableEq Z] (F : Family X N Z K s) (R : ℕ) (ι : Type*) [Fintype ι]
    [DecidableEq ι] (Nsl d : ℕ) (J₀ : X → SysOp N) (Jb : X → Fin (K * R) → SysOp N)
    (p : ODERepeatProtocol.Protocol (releaseOracle F R ι Nsl d J₀ Jb) (EuclideanSpace ℂ N))
    (Θ ell g ε : ℝ) : Prop :=
  ∃ (q : ℕ → MultiOracleCircuit.Program (releaseOracle F R ι Nsl d J₀ Jb)) (M : ℕ)
    (ψ : MeshSource.PhysicalSpace ι N Z (K * R) Nsl d)
    (Fo : EuclideanSpace ℂ N →L[ℂ] MeshSource.PhysicalSpace ι N Z (K * R) Nsl d),
    ∀ x sol, F.Solves x sol →
      ∃ hC : ODECompleteTrial.Certificate q M ψ Fo x (sol F.T) (s : ℝ) Θ ell g ε,
        ODECompleteTrial.algorithm hC.trial = p

variable [DecidableEq Z] {F : Family X N Z K s} {R : ℕ} {ι : Type*} [Fintype ι]
  [DecidableEq ι] {Nsl d : ℕ} {J₀ : X → SysOp N} {Jb : X → Fin (K * R) → SysOp N}
  {p : ODERepeatProtocol.Protocol (releaseOracle F R ι Nsl d J₀ Jb) (EuclideanSpace ℂ N)}
  {Θ ell g ε : ℝ}

/-- The released protocol succeeds with probability at least `2/3` on every input that has a
solution. -/
theorem ReleaseProtocol.success (hp : ReleaseProtocol F R ι Nsl d J₀ Jb p Θ ell g ε) (x : X)
    (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) : 2 / 3 ≤ p.successMass x := by
  obtain ⟨q, M, ψ, Fo, h⟩ := hp
  obtain ⟨hC, hpC⟩ := h x sol hs
  subst hpC
  exact hC.success_two_thirds

/-- **The released protocol is `ε`-accurate** in the observable form of trace distance, read by
the clean readout `endpointReadout 1 i₀ : ℂ^N → ℂ^N ⊗ ℂ^N` (any garbage index `i₀`). -/
theorem ReleaseProtocol.accurate (hp : ReleaseProtocol F R ι Nsl d J₀ Jb p Θ ell g ε) (i₀ : N)
    (x : X) (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    DensityAccurate (Hamiltonian.endpointReadout (1 : SysOp N) i₀) (p.conditionalDensity x)
      (ODEStateNormalization.unitDirection (sol F.T)) ε := by
  obtain ⟨q, M, ψ, Fo, h⟩ := hp
  obtain ⟨hC, hpC⟩ := h x sol hs
  subst hpC
  exact certificate_densityAccurate hC i₀

/-- **The released query bound**: the worst-case number of matrix queries over all transcripts is
at most `1274019840 g · queryShape(s, Θ, ℓ)` (`Certificate.matrix_queries`). -/
theorem ReleaseProtocol.worstCost_le (hp : ReleaseProtocol F R ι Nsl d J₀ Jb p Θ ell g ε) (x : X)
    (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    (p.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by
  obtain ⟨q, M, ψ, Fo, h⟩ := hp
  obtain ⟨hC, hpC⟩ := h x sol hs
  subst hpC
  exact hC.matrix_queries

/-- **The released protocol as a retry solver** of a family all of whose inputs have a
solution, read by the clean readout `endpointReadout 1 i₀` (the released isometry
`Hamiltonian.endpointReadout_isometry`). -/
def ReleaseProtocol.toRetrySolver (hp : ReleaseProtocol F R ι Nsl d J₀ Jb p Θ ell g ε)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) (i₀ : N) :
    RetrySolver F (releaseOracle F R ι Nsl d J₀ Jb) (EuclideanSpace ℂ N) (EuclideanSpace ℂ N)
      ε where
  prot := p
  readout := Hamiltonian.endpointReadout (1 : SysOp N) i₀
  readout_isometry := Hamiltonian.endpointReadout_isometry 1 (by ext; simp) i₀
  success x := (hsol x).elim fun sol hs => hp.success x sol hs
  accurate := hp.accurate i₀

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Parameters of the released solver exist**: a refinement `R` and a slot count `N` meeting the
clock, Cayley and public error conditions. -/
theorem exists_release_params (F : Family X N Z K s) {τ gbar ε : ℝ} (hτ : 0 < τ)
    (hg : 1 ≤ gbar) (hε : 0 < ε) (hB : 0 < F.mass) :
    ∃ R : ℕ, 0 < R ∧ ∃ Nsl : ℕ, 0 < Nsl ∧ 8 * (s : ℝ) * τ ≤ Nsl ∧
      3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 ≤ TimeDependentODE.precision gbar ε * (Nsl : ℝ) ^ 2 ∧
      (s : ℝ) * F.data.scale * ((∑ k, F.len k ^ 2 * ‖F.src k‖) / R / 2 +
        ((K * R : ℕ) : ℝ) * (τ / Nsl) * F.mass) ≤ ε * F.mass / (2000 * gbar) := by
  set S := ∑ k, F.len k ^ 2 * ‖F.src k‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
  set a := (s : ℝ) * F.data.scale with ha
  have ha0 : 0 ≤ a := mul_nonneg (Nat.cast_nonneg s) F.data.scale_pos.le
  have hgpos : 0 < gbar := by linarith
  set tgt := ε * F.mass / (2000 * gbar) with htgt
  have htgt0 : 0 < tgt := by positivity
  obtain ⟨R, hR⟩ := exists_nat_gt (a * S / tgt)
  have hRpos : (0 : ℝ) < R := lt_of_le_of_lt (by positivity) hR
  have hR0 : 0 < R := by exact_mod_cast hRpos
  have hν : 0 < TimeDependentODE.precision gbar ε :=
    ImprovedODEQueryBudget.precision_pos _ _ (by unfold TimeDependentODE.ratio; linarith)
      (by unfold TimeDependentODE.accuracy; linarith)
  set ν := TimeDependentODE.precision gbar ε with hνdef
  set P := a * ((K * R : ℕ) : ℝ) * τ * F.mass with hP
  have hP0 : 0 ≤ P := by positivity
  set c1 := 8 * (s : ℝ) * τ with hc1
  have hc10 : 0 ≤ c1 := by positivity
  set c2 := 3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 / ν with hc2
  have hc20 : 0 ≤ c2 := by positivity
  have hc30 : 0 ≤ 2 * P / tgt := by positivity
  obtain ⟨Nsl, hN⟩ := exists_nat_gt (c1 + c2 + 2 * P / tgt + 1)
  have hN1 : (1 : ℝ) ≤ Nsl := by linarith
  have hNpos : (0 : ℝ) < Nsl := by linarith
  refine ⟨R, hR0, Nsl, by exact_mod_cast hNpos, by linarith, ?_, ?_⟩
  · have h2 : c2 ≤ (Nsl : ℝ) ^ 2 := by nlinarith
    have h3 := (div_le_iff₀ hν).1 h2
    linarith
  · have hA : a * S / R ≤ tgt := by
      rw [div_le_iff₀ hRpos]
      have := (div_lt_iff₀ htgt0).1 hR
      nlinarith
    have hB' : P / Nsl ≤ tgt / 2 := by
      rw [div_le_iff₀ hNpos]
      have h4 : 2 * P / tgt < Nsl := by linarith
      have := (div_lt_iff₀ htgt0).1 h4
      nlinarith
    have heq : a * (S / R / 2 + ((K * R : ℕ) : ℝ) * (τ / Nsl) * F.mass) =
        a * S / R / 2 + P / Nsl := by
      rw [hP]; ring
    rw [heq]
    linarith

omit [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The Hermitian part of a skew-Hermitian generator `iH` (`H` Hermitian) is `H`. -/
theorem hamiltonianPart_I_smul {H : Matrix N N ℂ} (hH : H.IsHermitian) :
    ODEMatrixEnergy.hamiltonianPart (Complex.I • H) = H := by
  have hc : (Complex.I • H).conjTranspose = (-Complex.I) • H := by
    rw [Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_I]
  rw [ODEMatrixEnergy.hamiltonianPart, hc]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  linear_combination (-H i j) * Complex.I_sq

omit [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The dissipative part of a skew-Hermitian generator `iH` (`H` Hermitian) is `0`. -/
theorem dissipativePart_I_smul {H : Matrix N N ℂ} (hH : H.IsHermitian) :
    ODEMatrixEnergy.dissipativePart (Complex.I • H) = 0 := by
  have hc : (Complex.I • H).conjTranspose = (-Complex.I) • H := by
    rw [Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_I]
  rw [ODEMatrixEnergy.dissipativePart, hc]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply, smul_eq_mul]
  ring

/-- **The released general-mesh solver on a family of the class** (Theorem `ode:thm:time` on
general meshes, `TimeDependentExtensions.ODE.solver`): for a family in the class (`η = 1`,
`g ≤ ḡ`) with `D = 0`, `T = τ` and positive mass, parameters `R`, `N` meeting the solver's public
conditions, any unit seed and any unitary source interfaces `J₀`, `J_b` mapping the seed to
`x₀/‖x₀‖` and to the refined forcing directions (the premises of the released `Outcome`), the solver
gives a degree `d` and a released protocol with `Θ = τ`, `ℓ = releaseLog ḡ ε` and
`g = ratio ḡ`. -/
theorem exists_releaseProtocol (F : Family X N Z K s) {τ gbar ε : ℝ} (hF : F.InClass 1 gbar)
    (hskew : ∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H)
    (hT : F.T = τ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 < F.mass)
    (hK : 0 < K) (R : ℕ) (hR : 0 < R) (Nsl : ℕ) (hN : 0 < Nsl) (hClock : 8 * (s : ℝ) * τ ≤ Nsl)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * τ) ^ 3 ≤
      TimeDependentODE.precision gbar ε * (Nsl : ℝ) ^ 2)
    (hErr : (s : ℝ) * F.data.scale * ((∑ k, F.len k ^ 2 * ‖F.src k‖) / R / 2 +
      ((K * R : ℕ) : ℝ) * (τ / Nsl) * F.mass) ≤ ε * F.mass / (2000 * gbar))
    (J₀ : X → SysOp N) (Jb : X → Fin (K * R) → SysOp N) (hJ₀ : ∀ x, IsUnitary (J₀ x))
    (hJb : ∀ x r, IsUnitary (Jb x r)) (seed : EuclideanSpace ℂ N) (hseed : ‖seed‖ = 1)
    (hJ₀s : F.init ≠ 0 → ∀ x, J₀ x seed = ODEStateNormalization.unitDirection F.init)
    (hJbs : ∀ x r, (refineFamily F R).src r ≠ 0 →
      Jb x r seed = ODEStateNormalization.unitDirection ((refineFamily F R).src r)) :
    ∃ (d : ℕ) (p : ODERepeatProtocol.Protocol
        (releaseOracle F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) Nsl d J₀ Jb)
        (EuclideanSpace ℂ N)),
      ReleaseProtocol F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) Nsl d J₀ Jb p τ
        (releaseLog gbar ε) (TimeDependentODE.ratio gbar) ε := by
  have hM : 0 < K * R := Nat.mul_pos hK hR
  set t := (refineFamily F R).start with ht
  set rb : Fin (K * R) → ℝ := fun r => ‖(refineFamily F R).src r‖ with hrb
  have hmesh : TimeDependentExtensions.IsMesh t (K * R) τ := by
    have h := refine_isMesh F R hR
    rwa [hT] at h
  have hmass : TimeDependentExtensions.MeshSampling.mass ‖F.init‖ t rb = F.mass :=
    refine_meshMass F R hR
  -- `D = 0`: the parts of the generator `iH` of every refined piece.
  have hparts : ∀ y : X × Fin (K * R),
      ODEMatrixEnergy.hamiltonianPart ((refineData F.data R).matrix y) =
          Complex.I⁻¹ • F.data.matrix (y.1, stageOf K R y.2) ∧
        ODEMatrixEnergy.dissipativePart ((refineData F.data R).matrix y) = 0 := by
    intro y
    obtain ⟨H, hH, hx⟩ := hskew y.1 (stageOf K R y.2)
    have hm : (refineData F.data R).matrix y = F.data.matrix (y.1, stageOf K R y.2) := rfl
    rw [hm, hx, hamiltonianPart_I_smul hH, dissipativePart_I_smul hH, smul_smul,
      inv_mul_cancel₀ Complex.I_ne_zero, one_smul]
    exact ⟨rfl, rfl⟩
  have hnormH : ∀ (y : X × Fin (K * R)) (i j : N),
      ‖ODEMatrixEnergy.hamiltonianPart ((refineData F.data R).matrix y) i j‖ =
        ‖F.data.matrix (y.1, stageOf K R y.2) i j‖ := by
    intro y i j
    rw [(hparts y).1, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_I,
      inv_one, one_mul]
  have hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart ((refineData F.data R).matrix y) i j‖ ^ 2
      ≤ (1 : ℝ) ^ 2 := by
    intro y i
    simp only [hnormH]
    exact hF.row_norm y.1 _ i
  have hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart ((refineData F.data R).matrix y) i j‖ ^ 2
      ≤ (1 : ℝ) ^ 2 := by
    intro y j
    simp only [hnormH]
    exact hF.col_norm y.1 _ j
  have hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart ((refineData F.data R).matrix y) i j‖ ^ 2
      ≤ (0 : ℝ) ^ 2 := by
    intro y i
    rw [(hparts y).2]
    simp
  have hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart ((refineData F.data R).matrix y) i j‖ ^ 2
      ≤ (0 : ℝ) ^ 2 := by
    intro y j
    rw [(hparts y).2]
    simp
  have hPSD : ∀ (y : X × Fin (K * R)) (w : EuclideanSpace ℂ N), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart ((refineData F.data R).matrix y)) w)).re := by
    intro y w
    rw [(hparts y).2]
    simp [SparseStateOverlap.matrixOperator]
  have hClock' : 8 * (s : ℝ) * ((1 + TimeDependentODE.radius gbar ε * 0) * τ) ≤ Nsl := by
    rw [mul_zero, add_zero, one_mul]; exact hClock
  have hCayley' : 3 * (Real.sqrt (2 * (s : ℝ)) * ((1 + TimeDependentODE.radius gbar ε * 0) * τ)) ^ 3
      ≤ TimeDependentODE.precision gbar ε * (Nsl : ℝ) ^ 2 := by
    rw [mul_zero, add_zero, one_mul]; exact hCayley
  obtain ⟨d, E, q, -, hOut⟩ := TimeDependentExtensions.ODE.solver (refineData F.data R) hM t hN
    1 0 τ gbar ε ‖F.init‖ rb zero_le_one le_rfl hτ hg hε hε1 hmesh
    (by rw [mul_zero, add_zero]; exact one_pos) hClock' hCayley' (norm_nonneg _)
    (fun _ => norm_nonneg _) (by rw [hmass]; exact hB) hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed
    hseed
  have hθ : ImprovedODEQueryBudget.theta (τ * 1) (τ * 0) (TimeDependentODE.ratio gbar)
      (TimeDependentODE.accuracy ε) = τ := by
    rw [mul_one, mul_zero, ImprovedODEQueryBudget.theta_zero_dissipation]
  have key : ∀ x sol, F.Solves x sol →
      ODECompleteTrial.Certificate q (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio gbar))
        (MeshSource.input (refineData F.data R) hM (Sum.inr false) Nsl d
          (ODECompiledSource.seed E (TimeDependentExtensions.ODE.coefficients (refineData F.data R) t τ gbar ε ‖F.init‖ rb)
            seed))
        (MeshSource.input (refineData F.data R) hM (Sum.inr false) Nsl d ∘L
          ODECompiledSource.output E (TimeDependentExtensions.ODE.coefficients (refineData F.data R) t τ gbar ε ‖F.init‖ rb))
        x (sol F.T) (s : ℝ) τ (releaseLog gbar ε) (TimeDependentODE.ratio gbar) ε := by
    intro x sol hs
    obtain ⟨sol', hs', hne, hmass'⟩ := hF.solution x
    have hend : sol F.T = sol' F.T := F.solves_endpoint_unique hs hs'
    have hG0 : ∀ r : Fin (K * R), (refineFamily F R).gen x r -
        SparseStateOverlap.matrixOperator ((refineData F.data R).matrix (x, r)) = 0 :=
      fun _ => sub_self _
    have hC := hOut x (fun r _ => (refineFamily F R).gen x r) (fun r _ => (refineFamily F R).src r)
      sol (fun r => (refineFamily F R).src r) (∑ k, ‖F.src k‖)
      (fun r _ _ => hF.accretive x (stageOf K R r))
      (fun _ => intervalIntegrable_const) (fun _ => intervalIntegrable_const)
      (fun r _ _ => Finset.single_le_sum (f := fun k => ‖F.src k‖) (fun k _ => norm_nonneg _)
        (Finset.mem_univ (stageOf K R r)))
      (fun r => refine_solves F R hs r) (by rw [hs.1]) (fun _ => rfl)
      (fun h => by rw [hs.1] at h ⊢; exact hJ₀s h x) (fun r h => hJbs x r h)
      (by rw [← hT, hend]; exact hne) (by rw [hmass, ← hT, hend]; exact hmass')
      (by
        simp only [hG0, sub_self, norm_zero, intervalIntegral.integral_zero,
          Finset.sum_const_zero, mul_zero, zero_add, TimeDependentExtensions.ODE.publicError]
        rw [refine_quadrature, hmass]
        exact hErr)
    have hsT : sol τ = sol F.T := by rw [hT]
    rw [hθ, hsT] at hC
    exact hC
  refine ⟨d, ?_⟩
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    obtain ⟨sol₀, hs₀, -⟩ := hF.solution x₀
    exact ⟨ODECompleteTrial.algorithm (key x₀ sol₀ hs₀).trial, q, _, _, _,
      fun x sol hs => ⟨key x sol hs, rfl⟩⟩
  · exact ⟨.abort, q, ODEGroverAverage.chosenIterations (TimeDependentODE.ratio gbar),
      MeshSource.input (refineData F.data R) hM (Sum.inr false) Nsl d
        (ODECompiledSource.seed E (TimeDependentExtensions.ODE.coefficients (refineData F.data R) t τ gbar ε ‖F.init‖ rb)
          seed), 0, fun x => (hX ⟨x⟩).elim⟩

end

end ODELowerBoundExtensions.Release
