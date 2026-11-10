import ManuscriptConformance.ODEUpper
import GeneralSourceExtensions.Mesh.Integral
import RepresentedSampleODE.Regular
import CleanWorkODE.Theorem

/-!
# Conformance: the time-dependent dissipative ODE solver

Theorem `ode:thm:time`, with the source access of eqs. `ode:eq:source-interface-mass` and
`ode:eq:source-interface-preparation` (Section `ode:sec:time`) and the represented-sample
convention of its proof:

* **Input.** `ẋ = -G(t)x + b(t)`, `x(0) = x₀`, on a public mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` with
  generator and forcing pieces `G_r`, `b_r` on `[t_r, t_{r+1}]`, the true path dissipative
  (`D(t) ⪰ 0`, `TimeDependentODE.Accretive`) with its propagator `U` on the pieces, classical on
  every closed piece (`formal_classicalPropagator`, below), `x(T) ≠ 0` and `B ≤ ḡ‖x(T)‖`,
  `B = ‖x₀‖ + ∫‖b‖` (`Mesh.meshScale`). The generator pieces are integrable
  (`RepresentedSampleODE.RegularPieces`; the integrated sample errors below presuppose it), and
  `x(T)` is given by the mild solution (`RepresentedSampleODE.MildSolution`: the propagated forcing
  `v ↦ U(T, v) b_r(v)` is integrable on every piece, as the certificate on the propagated vector
  integral presupposes, and `x(T) = U(T, 0) x₀ + ∑_r ∫ U(T, v) b_r(v) dv`). No continuity of the
  pieces is assumed, and the forcing may jump inside a mesh interval. Classical solutions of
  bounded pieces with an integrable propagated forcing are mild
  (`RepresentedSampleODE.MildSolution.of_solves`), in particular for continuous pieces
  (`MildSolution.of_continuous`, `RegularPieces.of_continuous`).
* **Access.** Coherent time-indexed native sparse oracles of the represented samples
  `D.matrix (x, r)`, one per mesh interval, with the uniform norm promises `η_H`, `η_D`; the source
  interface: nodes `v_i ∈ [0, T]`, coefficients `ω_i ∈ ℂ`, the weight preparation `P_w`
  (`GeneralSourceODE.Compiled.WeightPrep`), the loading unitaries `U_load` (`J`), their adjoints
  and phases; the mass condition `B_q ≤ c_q B` and the certificate
  `‖∫₀ᵀ U(T, v) b(v) dv - ∑ ω_i U(T, v_i) b(v_i)‖ ≤ ζ B`.
* **Certificates.** The integrated sample error `ΔG = ∑_r ∫ ‖G_r - G̃_r‖`, its dissipative part
  `ΔD = ∑_r ∫ ‖Herm(G_r - G̃_r)‖ ≤ ΔG` and the slot rounding `ΔR` (`Mesh.sampleError`,
  `RepresentedSampleODE.dissipativeError`, `Mesh.refinementError`) with the source tolerance:
  `ζ + c_q (ΔG + 2 ΔD + 2 ΔR) ≤ ε/(2000 ḡ)` and `6 R (ΔD + ΔR) ≤ ν` at the LCHS frequency radius
  `R = 4 log(8·10⁴ c_q ḡ/ε)` and precision `ν = ε/(4·10⁴ c_q ḡ)` (the certified integrated sampling
  errors of Theorem `ode:thm:time`; `Mesh.sampleError_le_of_lipschitz` bounds `ΔG` for Lipschitz
  pieces). The second budget bounds the dissipative part `R ΔD` of the integrated branch sample
  error `∑_r ∫ ‖K̃_{k,r} - K_k(u)‖ du ≤ ΔH + R ΔD`, `K_k = H + k D`, `|k| ≤ R` (the integrated form
  of the manuscript's represented-sample contribution to its branch certificate, after eq.
  `ode:eq:timedisc` in the proof of Theorem `ode:thm:time`).
* **Algorithm.** One protocol over the actual oracles (`MeshOracles.actualOracle`: the sampled-time
  matrix oracle on `N` clock slots and the supplied `P_w`, `U_load`, `P_w†`), fixed before the
  instance; `N` is a public choice satisfying the two clock conditions (`ode_thm_time_clock`). For
  finite implementations of the preparations (`ode_thm_time_approx`) the supplied operations may use
  a temporary work register (`CleanWorkODE.actualOracleW`); every fixed gate acts as the identity
  on it, and the protocol heralds on the output flag and a clean work register.

**Represented samples of any sign.** Only the true path is dissipative: the represented samples
need not have positive semidefinite dissipative parts (`RepresentedSampleODE`: the analysis runs on
their positive repairs, the circuits on the samples), as in the manuscript, which asks of them only
the uniform moment and norm promises and certified errors.

**Integrable pieces and mild solutions** (review item J). No continuity and no classical solution
are assumed: the solution need only be mild (`MildSolution`), as the manuscript asks of the forcing
only the source certificate (eq. `ode:eq:source-interface-mass`), and the generator pieces need only
be integrable (`RegularPieces`). **Formal restriction** `formal_classicalPropagator`: the propagator
of the generator pieces is classical on every closed mesh interval, so a jump of the generator lies
at a mesh point (the manuscript's known breakpoints in the proof of Theorem `ode:thm:time`); the
propagator is constructed for continuous pieces (`Mesh.exists_isMeshPropagator`). The manuscript
also allows more general certificates in place of Lipschitz bounds, which admit generators
discontinuous at unknown points, with Carathéodory propagators; these are not formalised.
**Conclusion form**: the guarantee is the heralded mixed-output form (`HeraldedOutput`: success at
least `2/3`, conditional trace distance at most `ε`). For exact source preparations,
`ode_thm_time_actual` (`ActualRuns`) adds for the same protocol the accuracy of every actual
successful trial and history (`TrialsClose`, `HistoriesClose`; for every actual trial with a
nonzero success branch, the per-run Euclidean form of `ode:thm:main`, inherited by
`ode:thm:time`); for approximate source preparations (`ode_thm_time_approx`) only the
mixed-output form is claimed. Certificates on the opposite branches `K_{±k}` of the same samples
may replace the two sampling budgets (`BranchCertificates`: `ode_thm_time_branch`,
`ode_thm_time_approx_branch`, `ode_thm_time_actual_branch`).
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

universe u v w

/-- `log(10⁴ (2 c_q ḡ)/(ε/2)) = log(4·10⁴ c_q ḡ/ε)`: the logarithm of the time-dependent budget. -/
theorem time_log_eq (cq gbar ε : ℝ) :
    ImprovedODEQueryBudget.logBudget (TimeDependentODE.ratio (cq * gbar))
        (TimeDependentODE.accuracy ε) = Real.log (40000 * cq * gbar / ε) := by
  unfold ImprovedODEQueryBudget.logBudget TimeDependentODE.ratio TimeDependentODE.accuracy
  congr 1
  rcases eq_or_ne ε 0 with h | h
  · subst h; simp
  · field_simp
    ring

/-- **The clock conditions can be met**: every large enough number `N` of clock slots satisfies
`8 s ρ T ≤ N` and `3 (√(2s) ρ T)³ ≤ ν N²`, `ρ = η_H + R η_D`, for the public `ν > 0`. -/
theorem ode_thm_time_clock (s : ℕ) (ρ T ν : ℝ) (hν : 0 < ν) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      8 * s * (ρ * T) ≤ N ∧ 3 * (Real.sqrt (2 * (s : ℝ)) * (ρ * T)) ^ 3 ≤ ν * (N : ℝ) ^ 2 := by
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (8 * s * (ρ * T))
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (3 * (Real.sqrt (2 * (s : ℝ)) * (ρ * T)) ^ 3 / ν)
  refine ⟨max (max N₁ N₂) 1, fun N hN => ⟨?_, ?_⟩⟩
  · have : (N₁ : ℝ) ≤ N := by exact_mod_cast (le_max_left _ _).trans ((le_max_left _ _).trans hN)
    linarith
  · have h2 : (N₂ : ℝ) ≤ N := by
      exact_mod_cast (le_max_right _ _).trans ((le_max_left _ _).trans hN)
    have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    have hsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    rw [div_le_iff₀ hν] at hN₂
    nlinarith

/-- **`formal_classicalPropagator`** (review item J): the propagator `U` of the generator pieces is
classical on every closed mesh interval (`Mesh.IsMeshPropagator`: from every start time and vector
the propagated vector solves `ẏ = -G_r(u) y` with a derivative at every point of each piece), so a
jump of the generator lies at a mesh point, the manuscript's known breakpoints (the proof of
Theorem `ode:thm:time`). The manuscript's more general certificates there also admit generators
discontinuous at unknown points, whose propagators are Carathéodory ones (not formalised). -/
abbrev formal_classicalPropagator {M : ℕ} {n : Type*} [Fintype n]
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (t : ℕ → ℝ) (T : ℝ)
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) : Prop :=
  Mesh.IsMeshPropagator G t T U

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time`**. Under uniform bounds `s`, `η_H`, `η_D` on the represented samples,
coherent time-indexed sparse oracles on a public mesh, the source access of eqs.
`ode:eq:source-interface-mass` and `ode:eq:source-interface-preparation` (absolute constant `c_q`),
and certified sampling errors, the guarantee and query bound of `ode:thm:main` hold: one protocol,
fixed before the instance, succeeds with probability at least `2/3` and has conditional output
within trace distance `ε` of `x(T)/‖x(T)‖` on every instance, with at most
`C (c_q ḡ) (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and `C (c_q ḡ)` source-preparation calls in every
history, `ℓ = log(4·10⁴ c_q ḡ/ε)`, `Θ = T η_H + T η_D ℓ`, `C = 2548039680`. Here `0 < ε ≤ 1` (the
manuscript has `ε ≤ 1/2`), and `T ≥ 0`. Stated explicitly: `1 ≤ ḡ` (implied: every admissible
instance has it, since on a dissipative path `‖x(T)‖ ≤ B`, as in the remark `g ≥ 1` after Theorem
`ode:thm:main`; the time-dependent gate-level theorem names it `formal_gbarOne`) and `1 ≤ c_q`
(harmless up to absolute constants: `c_q` is an absolute constant, and for `c_q < 1` the theorem
applies with `c_q = 1`, the mass condition being monotone in `c_q`, at the price of a certificate
budget finer by the factor `c_q`).

The represented samples may have dissipative parts of any sign; the sampling certificates are
`ζ + c_q (ΔG + 2 ΔD + 2 ΔR) ≤ ε/(2000 ḡ)` and `6 R (ΔD + ΔR) ≤ ν` (see the module docstring).

The generator pieces are integrable (`RegularPieces`) and the solution is mild (`MildSolution`);
no continuity and no classical solution are assumed. Formal restriction:
`formal_classicalPropagator` (the propagator of the generator pieces is classical on every closed
mesh interval). Conclusion form: mixed-output (see the module docstring). -/
theorem ode_thm_time :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ x a, IsUnitary (J x a)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (MeshOracles.actualOracle (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw J)
            (EuclideanSpace ℂ n)),
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  refine ⟨2548039680, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨d, tf, -, -, hC⟩ := RepresentedSampleODE.robust_approx_solver_nonneg_regular D hM t hN
    etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw
    hPw J hJ seed hSeed
  refine ⟨d, ODERepeatProtocol.Protocol.repeatTrials tf 4, fun x G b sol bv U ζ hG hreg hsol hUm
    hW hL0 hL hMass hInt hTarget hB hB1 hB2 => ?_⟩
  obtain ⟨hcert, -⟩ := hC x (Pw x) (J x) 0 G b sol bv U ζ (hPw x) (hJ x) le_rfl
    (by rw [sub_self, norm_zero]) (fun a => by rw [sub_self, norm_zero]) (by norm_num)
    (by rw [mul_zero]; positivity) hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB hB1 hB2
  refine ⟨⟨hcert.success_two_thirds, hcert.output_density, hcert.conditional_error⟩, ?_, ?_⟩
  · refine hcert.matrix_queries.trans (le_of_eq ?_)
    rw [ImprovedODEQueryBudget.queryShape, ImprovedODEQueryBudget.theta, time_log_eq]
    unfold TimeDependentODE.ratio
    ring
  · refine hcert.source_calls.trans ?_
    unfold TimeDependentODE.ratio
    have : 0 ≤ cq * gbar := by positivity
    nlinarith

/-- **The manuscript's clean-input operator error** (the temporary-work convention, eq.
`access:eq:full-output`): a supplied operation `A` on registers `α` and a temporary work register
`W` implements `U` within `δ` when the work register starts in its clean state `w₀`: the full-output
error (`FullOutputError`, eq. `hs:eq:fullerror`) for the clean encoding `ψ ↦ ψ ⊗ |w₀⟩`,
`‖A (ψ ⊗ |w₀⟩) - (U ψ) ⊗ |w₀⟩‖ ≤ δ` for every normalised `ψ`; the output must also return the work
register to `|w₀⟩` up to the error. -/
abbrev cleanInputError {α W : Type*} [Fintype α] [Fintype W] [DecidableEq W] (w₀ : W)
    (A : EuclideanSpace ℂ (α × W) →L[ℂ] EuclideanSpace ℂ (α × W))
    (U : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α) (δ : ℝ) : Prop :=
  FullOutputError A (CleanWorkODE.cleanPi (V := ℂ) w₀) U δ

/-- The full-output error is the homogeneous clean-input error of `CleanWorkODE`:
`‖A (J ψ) - J (V ψ)‖ ≤ ε ‖ψ‖` for every `ψ`. -/
theorem cleanErr_of_fullOutputError {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] {A : K →L[ℂ] K} {J : P →L[ℂ] K}
    {V : P →L[ℂ] P} {ε : ℝ} (h : FullOutputError A J V ε) : CleanWorkODE.CleanErr J A V ε := by
  intro ψ
  rcases eq_or_ne ψ 0 with rfl | hψ
  · simp
  · have hn : (0 : ℝ) < ‖ψ‖ := norm_pos_iff.mpr hψ
    have hc : ((‖ψ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    obtain ⟨u, hu1, hψu⟩ : ∃ u : P, ‖u‖ = 1 ∧ ψ = (‖ψ‖ : ℂ) • u := by
      refine ⟨((‖ψ‖ : ℂ)⁻¹) • ψ, ?_, ?_⟩
      · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
          inv_mul_cancel₀ hn.ne']
      · rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    calc ‖A (J ψ) - J (V ψ)‖ = ‖(‖ψ‖ : ℂ) • (A (J u) - J (V u))‖ := by
          conv_lhs => rw [hψu]
          rw [map_smul, map_smul, map_smul, map_smul, smul_sub]
      _ = ‖ψ‖ * ‖A (J u) - J (V u)‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
      _ ≤ ‖ψ‖ * ε := mul_le_mul_of_nonneg_left (h u hu1) hn.le
      _ = ε * ‖ψ‖ := mul_comm _ _

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` with finite implementations of the preparations** (Section
`ode:sec:time`, after eq. `ode:eq:source-interface-preparation`: "For finite implementations, the
sum of their clean-input operator errors is chosen within the allocated tolerance"). The supplied
`P_w` acts on the label register and a temporary work register `W` with clean state `w₀`, the
supplied `U_load` on the label, data and work registers, and `P_w†` is the adjoint of the supplied
`P_w`. `P_w` and `U_load` are each within `δ` of an exact preparation, `P` and the label-controlled
`∑_a |a⟩⟨a| ⊗ L(a)` with unitary completions `L(a)` (label-controlled loading, a hypothesis of this
package, not eq. `ode:eq:source-interface-preparation`; neither needs to be supplied), in the
manuscript's clean-input operator
error (`cleanInputError`), with `60 c_q ḡ δ ≤ min(1/400, ε/20)`; otherwise as `ode_thm_time`. The
protocol runs the package's trial family with every fixed gate acting as the identity on the work
register and heralds on the output flag and a clean work register
(`CleanWorkODE.work_approx_solver_nonneg_regular`).

Formal restriction: `formal_classicalPropagator` (as in `ode_thm_time`). -/
theorem ode_thm_time_approx :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ {W : Type} [Fintype W] [DecidableEq W] (w₀ : W)
          (Pw : X → CleanWorkODE.LabelW m W →L[ℂ] CleanWorkODE.LabelW m W),
        (∀ x, IsUnitary (Pw x)) →
        ∀ (J : X → CleanWorkODE.LoadW m n W →L[ℂ] CleanWorkODE.LoadW m n W),
        (∀ x, IsUnitary (J x)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (CleanWorkODE.actualOracleW (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d
              Pw J)
            (EuclideanSpace ℂ n)),
          ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
            (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
            (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
            cleanInputError w₀ (Pw x) P δ →
            cleanInputError w₀ (J x) (CleanWorkODE.ctrlL L) δ →
            60 * (cq * gbar) * δ ≤ 1 / 400 → 60 * (cq * gbar) * δ ≤ ε / 20 →
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep P (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              L (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  refine ⟨2548039680, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD W _ _ w₀ Pw hPw J hJ seed hSeed
  obtain ⟨d, tf, -, -, hC⟩ := CleanWorkODE.work_approx_solver_nonneg_regular D hM t hN
    etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD w₀
    Pw hPw J hJ seed hSeed
  refine ⟨d, ODERepeatProtocol.Protocol.repeatTrials tf 4, fun x P L δ G b sol bv U ζ hP hL hδ
    hPc hJc hδ1 hδε hG hreg hsol hUm hW hL0 hL' hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have hratio : 30 * TimeDependentODE.ratio (cq * gbar) * δ = 60 * (cq * gbar) * δ := by
    unfold TimeDependentODE.ratio; ring
  obtain ⟨hcert, -⟩ := hC x P L δ G b sol bv U ζ hP hL hδ (cleanErr_of_fullOutputError hPc)
    (cleanErr_of_fullOutputError hJc) (hratio ▸ hδ1)
    (hratio ▸ hδε) hG hreg hsol hUm hW hL0 hL' hMass hInt hTarget hB hB1 hB2
  refine ⟨⟨hcert.success_two_thirds, hcert.output_density, hcert.conditional_error⟩, ?_, ?_⟩
  · refine hcert.matrix_queries.trans (le_of_eq ?_)
    rw [ImprovedODEQueryBudget.queryShape, ImprovedODEQueryBudget.theta, time_log_eq]
    unfold TimeDependentODE.ratio
    ring
  · refine hcert.source_calls.trans ?_
    unfold TimeDependentODE.ratio
    have : 0 ≤ cq * gbar := by positivity
    nlinarith

end

end ManuscriptConformance
