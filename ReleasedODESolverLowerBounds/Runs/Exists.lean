import ReleasedODESolverLowerBounds.Runs.Model
import ConstantODELowerBound.Solution

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The released general-mesh solver on families with a dissipative part

Manuscript Theorem `ode:thm:time`: uniform sparse energy bounds `η_H`, `η_D` on the
Hermitian and dissipative parts, `D ⪰ 0`, and the public slot conditions with the radius
`η_H + R(ḡ, ε) η_D`.

* `exists_meshParams`: a refinement and a slot count meeting the clock, Cayley and public error
  conditions of the solver at the scale `ρ τ` (from
  `ODELowerBoundExtensions.Release.exists_release_params` at `max τ (ρ τ)`).
* `exists_meshProtocol`: the generalisation of
  `ODELowerBoundExtensions.Release.exists_releaseProtocol` from `D = 0` to split bounds: for a
  family in the class whose Hermitian and dissipative parts have row and column norms at most
  `η_H`, `η_D` on every stage, the solver gives a released protocol with
  `Θ = meshTheta τ ḡ ε η_H η_D`; `D ⪰ 0` is the accretivity of the class
  (`ConstantODELowerBound.Solution.dissipativePart_nonneg_of_accretive`).
  `exists_releaseProtocol_of_meshProtocol` recovers the package theorem as the instance
  `(η_H, η_D) = (1, 0)`.
* `meshRun_nonempty`: runs exist under these hypotheses (seed `e_{i₀}`, public preparations
  `ODELowerBoundExtensions.Release.releaseJ₀`, `releaseJb`).
* `parts_le_one_of_inClass`, `meshRun_nonempty_of_inClass`: every family of the class has parts
  with row and column norms at most `1`, so runs with `η_H = η_D = 1` exist on every family of
  the class with positive mass and at least one stage.
-/

namespace ReleasedODESolverLowerBounds.Runs

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE
open NativeSparseBlockEncoding OracleCircuit TimeDependentExtensions
open ODELowerBoundExtensions.Release (ReleaseProtocol releaseOracle refineData releaseLog
  PublicSources SysOp)
open ODELowerBoundExtensions.Release (refineFamily stageOf refine_isMesh refine_meshMass
  refine_solves refine_quadrature)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {K s : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Parameters of the released solver at the scale `ρ τ`**: a refinement `R` and a slot count
`N` meeting the clock and Cayley conditions at `ρ τ` and the public error condition at `τ`. -/
theorem exists_meshParams (F : Family X N Z K s) {τ gbar ε ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ)
    (hg : 1 ≤ gbar) (hε : 0 < ε) (hB : 0 < F.mass) :
    ∃ R : ℕ, 0 < R ∧ ∃ Nsl : ℕ, 0 < Nsl ∧ 8 * (s : ℝ) * (ρ * τ) ≤ Nsl ∧
      3 * (Real.sqrt (2 * (s : ℝ)) * (ρ * τ)) ^ 3 ≤
        TimeDependentODE.precision gbar ε * (Nsl : ℝ) ^ 2 ∧
      (s : ℝ) * F.data.scale * ((∑ k, F.len k ^ 2 * ‖F.src k‖) / R / 2 +
        ((K * R : ℕ) : ℝ) * (τ / Nsl) * F.mass) ≤ ε * F.mass / (2000 * gbar) := by
  have hm : 0 < max τ (ρ * τ) := lt_max_of_lt_left hτ
  obtain ⟨R, hR, Nsl, hN, hClock, hCayley, hErr⟩ :=
    ODELowerBoundExtensions.Release.exists_release_params F hm hg hε hB
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hle : ρ * τ ≤ max τ (ρ * τ) := le_max_right _ _
  have hle' : τ ≤ max τ (ρ * τ) := le_max_left _ _
  have hρτ : 0 ≤ ρ * τ := (mul_pos hρ hτ).le
  have hNpos : (0 : ℝ) < Nsl := by exact_mod_cast hN
  refine ⟨R, hR, Nsl, hN, ?_, ?_, ?_⟩
  · nlinarith
  · have hsq : 0 ≤ Real.sqrt (2 * (s : ℝ)) := Real.sqrt_nonneg _
    have h3 : (Real.sqrt (2 * (s : ℝ)) * (ρ * τ)) ^ 3 ≤
        (Real.sqrt (2 * (s : ℝ)) * max τ (ρ * τ)) ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg hsq hρτ) (mul_le_mul_of_nonneg_left hle hsq) 3
    linarith
  · refine le_trans ?_ hErr
    have hsc : 0 ≤ (s : ℝ) * F.data.scale := mul_nonneg hs0 F.data.scale_pos.le
    apply mul_le_mul_of_nonneg_left _ hsc
    have hdiv : τ / Nsl ≤ max τ (ρ * τ) / Nsl := div_le_div_of_nonneg_right hle' hNpos.le
    have hKR : (0 : ℝ) ≤ ((K * R : ℕ) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv hKR) hB.le
    linarith

/-- **The released general-mesh solver with split energy bounds** (Theorem `ode:thm:time`): for
a family in the class (`η = 1`, `g ≤ ḡ`) with `T = τ`, positive mass and at least one stage, split
bounds `η_H, η_D ≥ 0` with `η_H + R(ḡ, ε) η_D > 0` on the Hermitian and dissipative parts of
every stage, parameters meeting the solver's public conditions, a unit seed and unitary source
interfaces mapping it to `x₀/‖x₀‖` and to the refined forcing directions, the solver gives a
degree and a released protocol with `Θ = meshTheta τ ḡ ε η_H η_D`, `ℓ = releaseLog ḡ ε`,
`g = ratio ḡ`. -/
theorem exists_meshProtocol (F : Family X N Z K s) {τ gbar ε etaH etaD : ℝ}
    (hF : F.InClass 1 gbar) (hT : F.T = τ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hB : 0 < F.mass) (hK : 0 < K) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hρ : 0 < etaH + TimeDependentODE.radius gbar ε * etaD)
    (hrH : ∀ x k i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hcH : ∀ x k j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hrD : ∀ x k i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (hcD : ∀ x k j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (R : ℕ) (hR : 0 < R) (Nsl : ℕ) (hN : 0 < Nsl)
    (hClock : 8 * (s : ℝ) * ((etaH + TimeDependentODE.radius gbar ε * etaD) * τ) ≤ Nsl)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) * ((etaH + TimeDependentODE.radius gbar ε * etaD) *
      τ)) ^ 3 ≤ TimeDependentODE.precision gbar ε * (Nsl : ℝ) ^ 2)
    (hErr : (s : ℝ) * F.data.scale * ((∑ k, F.len k ^ 2 * ‖F.src k‖) / R / 2 +
      ((K * R : ℕ) : ℝ) * (τ / Nsl) * F.mass) ≤ ε * F.mass / (2000 * gbar))
    (J₀ : X → SysOp N) (Jb : X → Fin (K * R) → SysOp N) (hJ₀ : ∀ x, IsUnitary (J₀ x))
    (hJb : ∀ x r, IsUnitary (Jb x r)) (seed : EuclideanSpace ℂ N) (hseed : ‖seed‖ = 1)
    (hJ₀s : F.init ≠ 0 → ∀ x, J₀ x seed = ODEStateNormalization.unitDirection F.init)
    (hJbs : ∀ x r, (ODELowerBoundExtensions.Release.refineFamily F R).src r ≠ 0 →
      Jb x r seed =
        ODEStateNormalization.unitDirection ((ODELowerBoundExtensions.Release.refineFamily F R).src r)) :
    ∃ (d : ℕ) (p : ODERepeatProtocol.Protocol
        (releaseOracle F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) Nsl d J₀ Jb)
        (EuclideanSpace ℂ N)),
      ReleaseProtocol F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) Nsl d J₀ Jb p
        (meshTheta τ gbar ε etaH etaD) (releaseLog gbar ε) (TimeDependentODE.ratio gbar) ε := by
  have hM : 0 < K * R := Nat.mul_pos hK hR
  set t := (refineFamily F R).start with ht
  set rb : Fin (K * R) → ℝ := fun r => ‖(refineFamily F R).src r‖ with hrb
  have hmesh : TimeDependentExtensions.IsMesh t (K * R) τ := by
    have h := refine_isMesh F R hR
    rwa [hT] at h
  have hmass : TimeDependentExtensions.MeshSampling.mass ‖F.init‖ t rb = F.mass :=
    refine_meshMass F R hR
  -- The part bounds of every refined piece are those of its stage.
  have hrH' : ∀ (y : X × Fin (K * R)) i,
      ∑ j, ‖ODEMatrixEnergy.hamiltonianPart ((refineData F.data R).matrix y) i j‖ ^ 2 ≤
        etaH ^ 2 := fun y i => hrH y.1 (stageOf K R y.2) i
  have hcH' : ∀ (y : X × Fin (K * R)) j,
      ∑ i, ‖ODEMatrixEnergy.hamiltonianPart ((refineData F.data R).matrix y) i j‖ ^ 2 ≤
        etaH ^ 2 := fun y j => hcH y.1 (stageOf K R y.2) j
  have hrD' : ∀ (y : X × Fin (K * R)) i,
      ∑ j, ‖ODEMatrixEnergy.dissipativePart ((refineData F.data R).matrix y) i j‖ ^ 2 ≤
        etaD ^ 2 := fun y i => hrD y.1 (stageOf K R y.2) i
  have hcD' : ∀ (y : X × Fin (K * R)) j,
      ∑ i, ‖ODEMatrixEnergy.dissipativePart ((refineData F.data R).matrix y) i j‖ ^ 2 ≤
        etaD ^ 2 := fun y j => hcD y.1 (stageOf K R y.2) j
  have hPSD : ∀ (y : X × Fin (K * R)) (w : EuclideanSpace ℂ N), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart ((refineData F.data R).matrix y)) w)).re :=
    fun y w => ConstantODELowerBound.Solution.dissipativePart_nonneg_of_accretive
      (hF.accretive y.1 (stageOf K R y.2)) w
  obtain ⟨d, E, q, -, hOut⟩ := TimeDependentExtensions.ODE.solver (refineData F.data R) hM t hN
    etaH etaD τ gbar ε ‖F.init‖ rb hH hD hτ hg hε hε1 hmesh hρ hClock hCayley (norm_nonneg _)
    (fun _ => norm_nonneg _) (by rw [hmass]; exact hB) hrH' hcH' hrD' hcD' hPSD J₀ Jb hJ₀ hJb
    seed hseed
  have key : ∀ x sol, F.Solves x sol →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio gbar))
        (MeshSource.input (refineData F.data R) hM (Sum.inr false) Nsl d
          (ODECompiledSource.seed E (TimeDependentExtensions.ODE.coefficients
            (refineData F.data R) t τ gbar ε ‖F.init‖ rb) seed))
        (MeshSource.input (refineData F.data R) hM (Sum.inr false) Nsl d ∘L
          ODECompiledSource.output E (TimeDependentExtensions.ODE.coefficients
            (refineData F.data R) t τ gbar ε ‖F.init‖ rb))
        x (sol F.T) (s : ℝ) (meshTheta τ gbar ε etaH etaD) (releaseLog gbar ε)
        (TimeDependentODE.ratio gbar) ε := by
    intro x sol hs
    obtain ⟨sol', hs', hne, hmass'⟩ := hF.solution x
    have hend : sol F.T = sol' F.T := F.solves_endpoint_unique hs hs'
    have hG0 : ∀ r : Fin (K * R), (refineFamily F R).gen x r -
        SparseStateOverlap.matrixOperator ((refineData F.data R).matrix (x, r)) = 0 :=
      fun _ => sub_self _
    have hC := hOut x (fun r _ => (refineFamily F R).gen x r)
      (fun r _ => (refineFamily F R).src r) sol (fun r => (refineFamily F R).src r)
      (∑ k, ‖F.src k‖) (fun r _ _ => hF.accretive x (stageOf K R r))
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
    rw [hsT] at hC
    exact hC
  refine ⟨d, ?_⟩
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    obtain ⟨sol₀, hs₀, -⟩ := hF.solution x₀
    exact ⟨ODECompleteTrial.algorithm (key x₀ sol₀ hs₀).trial, q, _, _, _,
      fun x sol hs => ⟨key x sol hs, rfl⟩⟩
  · exact ⟨.abort, q, ODEGroverAverage.chosenIterations (TimeDependentODE.ratio gbar),
      MeshSource.input (refineData F.data R) hM (Sum.inr false) Nsl d
        (ODECompiledSource.seed E (TimeDependentExtensions.ODE.coefficients
          (refineData F.data R) t τ gbar ε ‖F.init‖ rb) seed), 0, fun x => (hX ⟨x⟩).elim⟩

/-- **Runs of the released general-mesh solver with split energy bounds exist** under the
hypotheses of `exists_meshProtocol` on the parts. -/
theorem meshRun_nonempty (F : Family X N Z K s) {τ gbar ε etaH etaD : ℝ}
    (hF : F.InClass 1 gbar) (hT : F.T = τ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hB : 0 < F.mass) (hK : 0 < K) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hρ : 0 < etaH + TimeDependentODE.radius gbar ε * etaD)
    (hrH : ∀ x k i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hcH : ∀ x k j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaH ^ 2)
    (hrD : ∀ x k i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (hcD : ∀ x k j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      etaD ^ 2)
    (i₀ : N) : Nonempty (MeshRun F τ gbar ε etaH etaD) := by
  obtain ⟨R, hR, Nsl, hN, hClock, hCayley, hErr⟩ := exists_meshParams F hτ hρ hg hε hB
  have hP := ODELowerBoundExtensions.Release.releaseSources_public F R i₀
  obtain ⟨d, p, hp⟩ := exists_meshProtocol F hF hT hτ hg hε hε1 hB hK hH hD hρ hrH hcH hrD hcD
    R hR Nsl hN hClock hCayley hErr (ODELowerBoundExtensions.Release.releaseJ₀ F i₀)
    (ODELowerBoundExtensions.Release.releaseJb F R i₀) hP.initial_unitary hP.forcing_unitary
    (ODELowerBoundExtensions.Release.seedVec i₀) (ODELowerBoundExtensions.Release.norm_seedVec i₀)
    (fun h0 _ => ODELowerBoundExtensions.Release.prepUnitary_seed i₀ h0)
    (fun _ _ h0 => ODELowerBoundExtensions.Release.prepUnitary_seed i₀ h0)
  exact ⟨⟨i₀, R, hR, Nsl, d, ODELowerBoundExtensions.Release.releaseJ₀ F i₀,
    ODELowerBoundExtensions.Release.releaseJb F R i₀, hP, p, hp⟩⟩

/-- `‖(a ± b)/2‖² ≤ (‖a‖² + ‖b‖²)/2` in the form used for the entries of the parts: if
`‖c‖ = 1/2` and `‖d‖ ≤ ‖a‖ + ‖b‖`, then `‖c d‖² ≤ (‖a‖² + ‖b‖²)/2`. -/
theorem norm_half_mul_sq_le {c d : ℂ} {a b : ℝ} (hc : ‖c‖ = 1 / 2) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hd : ‖d‖ ≤ a + b) : ‖c * d‖ ^ 2 ≤ (a ^ 2 + b ^ 2) / 2 := by
  rw [norm_mul, hc]
  have h0 := norm_nonneg d
  nlinarith [sq_nonneg (a - b)]

omit [Fintype N] [DecidableEq N] in
/-- The entries of the Hermitian part: `‖H_ij‖² ≤ (‖M_ij‖² + ‖M_ji‖²)/2`. -/
theorem norm_hamiltonianPart_sq_le (M : Matrix N N ℂ) (i j : N) :
    ‖ODEMatrixEnergy.hamiltonianPart M i j‖ ^ 2 ≤ (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2 := by
  rw [ODEMatrixEnergy.hamiltonianPart_apply]
  refine norm_half_mul_sq_le (by simp) (norm_nonneg _) (norm_nonneg _) ?_
  simpa [norm_star] using norm_sub_le (M i j) (star (M j i))

omit [Fintype N] [DecidableEq N] in
/-- The entries of the dissipative part: `‖D_ij‖² ≤ (‖M_ij‖² + ‖M_ji‖²)/2`. -/
theorem norm_dissipativePart_sq_le (M : Matrix N N ℂ) (i j : N) :
    ‖ODEMatrixEnergy.dissipativePart M i j‖ ^ 2 ≤ (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2 := by
  rw [ODEMatrixEnergy.dissipativePart_apply]
  refine norm_half_mul_sq_le (by simp) (norm_nonneg _) (norm_nonneg _) ?_
  simpa [norm_star] using norm_add_le (M i j) (star (M j i))

omit [DecidableEq N] in
/-- A matrix whose entries satisfy `‖P_ij‖² ≤ (‖M_ij‖² + ‖M_ji‖²)/2` has row and column norms at
most `1` when `M` does. -/
theorem part_rows_cols_le_one {M P : Matrix N N ℂ}
    (hP : ∀ i j, ‖P i j‖ ^ 2 ≤ (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2)
    (hr : ∀ i, ∑ j, ‖M i j‖ ^ 2 ≤ (1 : ℝ) ^ 2) (hc : ∀ j, ∑ i, ‖M i j‖ ^ 2 ≤ (1 : ℝ) ^ 2) :
    (∀ i, ∑ j, ‖P i j‖ ^ 2 ≤ (1 : ℝ) ^ 2) ∧ (∀ j, ∑ i, ‖P i j‖ ^ 2 ≤ (1 : ℝ) ^ 2) := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · calc ∑ j, ‖P i j‖ ^ 2 ≤ ∑ j, (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun j _ => hP i j
      _ = ((∑ j, ‖M i j‖ ^ 2) + ∑ j, ‖M j i‖ ^ 2) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ (1 : ℝ) ^ 2 := by linarith [hr i, hc i]
  · calc ∑ i, ‖P i j‖ ^ 2 ≤ ∑ i, (‖M i j‖ ^ 2 + ‖M j i‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun i _ => hP i j
      _ = ((∑ i, ‖M i j‖ ^ 2) + ∑ i, ‖M j i‖ ^ 2) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ ≤ (1 : ℝ) ^ 2 := by linarith [hr j, hc j]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The parts of every generator of the class have row and column norms at most one**:
`‖(M ± M†)/2‖_row ≤ (‖M‖_row + ‖M‖_col)/2 ≤ 1`. -/
theorem parts_le_one_of_inClass (F : Family X N Z K s) {gbar : ℝ} (hF : F.InClass 1 gbar) :
    (∀ x k i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, k)) i j‖ ^ 2 ≤ 1 ^ 2) ∧
      (∀ x k j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (F.data.matrix (x, k)) i j‖ ^ 2 ≤ 1 ^ 2) ∧
      (∀ x k i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤ 1 ^ 2) ∧
      (∀ x k j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤ 1 ^ 2) := by
  have hH := fun x k => part_rows_cols_le_one
    (norm_hamiltonianPart_sq_le (F.data.matrix (x, k))) (hF.row_norm x k) (hF.col_norm x k)
  have hD := fun x k => part_rows_cols_le_one
    (norm_dissipativePart_sq_le (F.data.matrix (x, k))) (hF.row_norm x k) (hF.col_norm x k)
  exact ⟨fun x k => (hH x k).1, fun x k => (hH x k).2, fun x k => (hD x k).1,
    fun x k => (hD x k).2⟩

/-- **Runs with `η_H = η_D = 1` exist on every family of the class** with `T = τ > 0`, positive
mass and at least one stage, for `ḡ ≥ 1` and `0 < ε ≤ 1`. -/
theorem meshRun_nonempty_of_inClass (F : Family X N Z K s) {τ gbar ε : ℝ}
    (hF : F.InClass 1 gbar) (hT : F.T = τ) (hτ : 0 < τ) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hB : 0 < F.mass) (hK : 0 < K) (i₀ : N) :
    Nonempty (MeshRun F τ gbar ε 1 1) := by
  obtain ⟨hrH, hcH, hrD, hcD⟩ := parts_le_one_of_inClass F hF
  have hrad : 0 ≤ TimeDependentODE.radius gbar ε := by
    unfold TimeDependentODE.radius ImprovedODEQueryBudget.radius TimeDependentODE.ratio
      TimeDependentODE.accuracy
    have h1 : 1 ≤ 20000 * (2 * gbar) / (ε / 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have := Real.log_nonneg h1
    linarith
  exact meshRun_nonempty F hF hT hτ hg hε hε1 hB hK zero_le_one zero_le_one (by linarith)
    hrH hcH hrD hcD i₀

/-- **The package's released protocol on skew-Hermitian families is the instance
`(η_H, η_D) = (1, 0)` of `exists_meshProtocol`**: under exactly the hypotheses of
`ODELowerBoundExtensions.Release.exists_releaseProtocol` (`D = 0` through `hskew`), the
dissipative parts vanish, the Hermitian parts have row and column norms at most `1`, and
`meshTheta τ ḡ ε 1 0 = τ`, so the conclusion is that of the package theorem. -/
theorem exists_releaseProtocol_of_meshProtocol (F : Family X N Z K s) {τ gbar ε : ℝ}
    (hF : F.InClass 1 gbar)
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
  obtain ⟨hrH, hcH, -, -⟩ := parts_le_one_of_inClass F hF
  have hD0 : ∀ x k, ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) = 0 := by
    intro x k
    obtain ⟨H, hH, hM⟩ := hskew x k
    rw [hM]
    exact ODELowerBoundExtensions.Release.dissipativePart_I_smul hH
  have hrD : ∀ x k i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      (0 : ℝ) ^ 2 := by
    intro x k i
    rw [hD0 x k]; simp
  have hcD : ∀ x k j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (F.data.matrix (x, k)) i j‖ ^ 2 ≤
      (0 : ℝ) ^ 2 := by
    intro x k j
    rw [hD0 x k]; simp
  have hρ1 : (1 : ℝ) + TimeDependentODE.radius gbar ε * 0 = 1 := by ring
  have h := exists_meshProtocol F hF hT hτ hg hε hε1 hB hK zero_le_one le_rfl
    (by rw [hρ1]; exact one_pos) hrH hcH hrD hcD R hR Nsl hN (by rwa [hρ1, one_mul])
    (by rwa [hρ1, one_mul]) hErr J₀ Jb hJ₀ hJb seed hseed hJ₀s hJbs
  rwa [meshTheta_one_zero] at h

end

end ReleasedODESolverLowerBounds.Runs
