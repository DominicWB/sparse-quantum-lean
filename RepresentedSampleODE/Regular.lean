import RepresentedSampleODE.Integral
import RepresentedSampleODE.Duhamel

/-!
# Represented samples of any sign, for integrable pieces and mild solutions

`robust_approx_solver_nonneg_path` asks of the generator and forcing pieces that they be
continuous on their closed mesh intervals, and of the solution that it solve the equation
classically on every piece; a classical solution cannot exist if the forcing jumps inside a mesh
interval. The manuscript accesses the forcing only through the source interface and its
certificate on the propagated vector integral, so its solution is the mild one, given by Duhamel's
formula. Here the endpoint is proved for

* **integrable generator pieces** (`RegularPieces`: the integrated sample errors `ΔG`, `ΔD`
  presuppose the integrals), with the propagator `U` of the pieces, classical on every closed piece
  (`Mesh.IsMeshPropagator`, so a jump of the generator lies at a mesh point);
* **mild solutions** (`MildSolution`): the propagated forcing `v ↦ U(T, v) b_r(v)` is integrable
  on every mesh interval (the certificate on the propagated vector integral presupposes the
  integrals) and `x(T) = U(T, 0) x(0) + ∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv`.

No continuity of either piece is assumed. A classical solution with bounded generator pieces and an
integrable propagated forcing is a mild solution (`MildSolution.of_solves`, by Duhamel's formula
`mesh_duhamel_bounded`), in particular for continuous pieces (`MildSolution.of_continuous`), and
continuous generator pieces are integrable (`RegularPieces.of_continuous`).

* `dissipative_intervalIntegrable`, `dissipativeError_le_sampleError_of_int`,
  `pathNegativity_bound_of_int`, `robustBudget_of_path_int`: the path negativity bounds for
  integrable pieces;
* `robust_approx_solver_nonneg_regular`: the combined endpoint (`RegularApproxOutcome`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions SparseHamiltonian.GeneralSourceExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients)
open SparseHamiltonian.GeneralSourceODE (SourceCall sources phases phases_norm)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale sampleError refinementError
  IsMeshPropagator)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

/-- **Regular pieces**: on every mesh interval the generator piece is interval integrable (the
integrated sample errors `ΔG`, `ΔD` presuppose it). -/
def RegularPieces {M : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (t : ℕ → ℝ) (G : Fin M → ℝ → V →L[ℂ] V) : Prop :=
  ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))

/-- Continuous generator pieces are regular. -/
theorem RegularPieces.of_continuous {M : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    {G : Fin M → ℝ → V →L[ℂ] V}
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1)))) :
    RegularPieces t G :=
  fun r => (hGc r).intervalIntegrable_of_Icc (hmesh.mono (Nat.le_succ r))

/-- **A mild solution on the mesh**: the propagated forcing `v ↦ U(T, v) b_r(v)` is interval
integrable on every mesh interval and the final value is given by Duhamel's formula,
`x(T) = U(T, 0) x(0) + ∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv`. -/
def MildSolution {M : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (t : ℕ → ℝ) (T : ℝ) (b : Fin M → ℝ → V) (sol : ℝ → V) (U : ℝ → V → ℝ → V) : Prop :=
  (∀ r : Fin M, IntervalIntegrable (fun v => U v (b r v) T) volume (t r) (t ((r : ℕ) + 1))) ∧
  sol T = U 0 (sol 0) T + ∑ r : Fin M, ∫ v in t r..t ((r : ℕ) + 1), U v (b r v) T

/-- **Classical solutions are mild**: for accretive bounded generator pieces with propagator `U`
and an integrable propagated forcing, every classical piecewise solution is a mild solution
(Duhamel's formula, `mesh_duhamel_bounded`). -/
theorem MildSolution.of_solves {M : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    {G : Fin M → ℝ → V →L[ℂ] V} {U : ℝ → V → ℝ → V} (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hΛ : ∀ r : Fin M, ∃ Λ : ℝ, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), ‖G r u‖ ≤ Λ)
    (b : Fin M → ℝ → V)
    (hint : ∀ r : Fin M,
      IntervalIntegrable (fun v => U v (b r v) T) volume (t r) (t ((r : ℕ) + 1)))
    (sol : ℝ → V) (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) :
    MildSolution t T b sol U := by
  refine ⟨hint, ?_⟩
  rw [mesh_duhamel_bounded hmesh hU hG hΛ b hint sol hsol]
  abel

/-- **Classical solutions of continuous pieces are mild.** -/
theorem MildSolution.of_continuous {M : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    {G : Fin M → ℝ → V →L[ℂ] V} {U : ℝ → V → ℝ → V} (hU : IsMeshPropagator G t T U)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1))))
    (b : Fin M → ℝ → V) (hbc : ∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1))))
    (sol : ℝ → V) (hsol : ∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) :
    MildSolution t T b sol U := by
  obtain ⟨-, hΛ, hint⟩ := continuous_pieces_regular hmesh hU hG hGc b hbc
  exact MildSolution.of_solves hmesh hU hG hΛ b hint sol hsol

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

omit [DecidableEq n] in
/-- The norm of the Hermitian part of an integrable operator path minus a constant is
integrable. -/
theorem dissipative_intervalIntegrable
    {G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {a b : ℝ}
    (hG : IntervalIntegrable G volume a b) (C : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    IntervalIntegrable (fun u => ‖ODEHermitianReduction.dissipativePart (G u - C)‖) volume a b := by
  have h1 : IntervalIntegrable (fun u => G u - C) volume a b := hG.sub intervalIntegrable_const
  have hadj : Continuous (fun A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => A†) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := EuclideanSpace ℂ n)
      (F := EuclideanSpace ℂ n)).continuous
  have hc : Continuous (fun A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n =>
      ‖ODEHermitianReduction.dissipativePart A‖) := by
    simp only [ODEHermitianReduction.dissipativePart, HermitianDilation.hermitianPart]
    exact ((continuous_id.add hadj).const_smul ((2 : ℂ)⁻¹)).norm
  refine h1.norm.mono_fun' (hc.comp_aestronglyMeasurable h1.aestronglyMeasurable_restrict_uIoc) ?_
  filter_upwards with u
  simp only [norm_norm]
  exact ODEHermitianReduction.norm_dissipativePart_le _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The dissipative sample error is at most the sample error, for integrable pieces. -/
theorem dissipativeError_le_sampleError_of_int (D : Data (X × Fin M) n Z s) (x : X)
    {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hGi : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) :
    dissipativeError D x t G ≤ sampleError D x t G := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hab := hmesh.mono (Nat.le_succ r)
  have h1 := dissipative_intervalIntegrable (hGi r)
    (SparseStateOverlap.matrixOperator (D.matrix (x, r)))
  have h2 : IntervalIntegrable
      (fun u => ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖)
      volume (t r) (t ((r : ℕ) + 1)) := ((hGi r).sub intervalIntegrable_const).norm
  exact intervalIntegral.integral_mono_on hab h1 h2
    (fun u _ => ODEHermitianReduction.norm_dissipativePart_le _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The path averages are negativity bounds**, for accretive integrable pieces. -/
theorem pathNegativity_bound_of_int (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ}
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGi : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    (r : Fin M) (w : EuclideanSpace ℂ n) :
    -pathNegativity D x t G r * ‖w‖ ^ 2 ≤
      (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re := by
  unfold pathNegativity
  set A := SparseStateOverlap.matrixOperator (D.matrix (x, r)) with hA
  split_ifs with hpos
  · set a := t r
    set b := t ((r : ℕ) + 1)
    have hab : a ≤ b := by linarith
    set f : ℝ → ℝ := fun u => ‖ODEHermitianReduction.dissipativePart (G r u - A)‖ with hf
    have hfint : IntervalIntegrable f MeasureTheory.volume a b :=
      dissipative_intervalIntegrable (hGi r) A
    set c : ℝ := (inner ℂ w (A w)).re with hc
    have key : ∀ u ∈ Icc a b, -(f u * ‖w‖ ^ 2) ≤ c := by
      intro u hu
      have h0 := hG r u hu w
      have h1 := re_inner_le_dissipative (G r u - A) w
      have e : (inner ℂ w ((G r u - A) w)).re = (inner ℂ w (G r u w)).re - c := by
        rw [hc, sub_apply, inner_sub_right, Complex.sub_re]
      rw [e] at h1
      simp only [hf]
      linarith
    have hint : ∫ u in a..b, -(f u * ‖w‖ ^ 2) ≤ ∫ u in a..b, c :=
      intervalIntegral.integral_mono_on hab ((hfint.mul_const (‖w‖ ^ 2)).neg)
        intervalIntegrable_const key
    have e1 : ∫ u in a..b, -(f u * ‖w‖ ^ 2) = -((∫ u in a..b, f u) * ‖w‖ ^ 2) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_mul_const]
    have e2 : ∫ u in a..b, c = (b - a) * c := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [e1, e2] at hint
    have hba : 0 < b - a := hpos
    set I : ℝ := ∫ u in a..b, f u with hI
    have e3 : -(I / (b - a)) * ‖w‖ ^ 2 = -(I * ‖w‖ ^ 2) / (b - a) := by ring
    rw [e3, div_le_iff₀ hba]
    linarith [mul_comm c (b - a)]
  · have h := re_inner_le_dissipative (-A) w
    rw [neg_apply, inner_neg_right, Complex.neg_re] at h
    have hd : ‖ODEHermitianReduction.dissipativePart (-A)‖ ≤ ‖A‖ :=
      (ODEHermitianReduction.norm_dissipativePart_le _).trans (norm_neg A).le
    have hm := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖w‖)
    linarith

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **`RobustBudget` from the true path**, for accretive integrable pieces. -/
theorem robustBudget_of_path_int (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) {N : ℕ}
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGi : ∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1)))
    {cq gbar ε ζ : ℝ}
    (h1 : ζ + cq * (sampleError D x t G + 2 * dissipativeError D x t G +
      2 * refinementError D t T N) ≤ ε / (2000 * gbar))
    (h2 : 6 * radius (cq * gbar) ε * (dissipativeError D x t G + refinementError D t T N) ≤
      precision (cq * gbar) ε) :
    RobustBudget D x t G T N cq gbar ε ζ := by
  refine ⟨pathNegativity D x t G, pathNegativity_nonneg D x hmesh G,
    pathNegativity_bound_of_int D x G hG hGi, ?_, ?_⟩
  · rw [negativity_pathNegativity D x hmesh G]
    exact h1
  · rw [negativity_pathNegativity D x hmesh G]
    exact h2

/-- `PathApproxIntegralOutcome` for integrable generator pieces (`RegularPieces`) and mild solutions
(`MildSolution`) in place of continuous pieces and classical solutions. -/
def RegularApproxOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (MeshOracles.actualOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J)
      (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      ‖Pw x - P‖ ≤ δ → (∀ a, ‖J x a - L a‖ ≤ δ) →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      RegularPieces t G →
      MildSolution t T b sol U →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
          ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + 2 * dissipativeError D x t G +
        2 * refinementError D t T N) ≤ ε / (2000 * gbar) →
      6 * radius (cq * gbar) ε * (dissipativeError D x t G + refinementError D t T N) ≤
        precision (cq * gbar) ε →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, approximate preparations,
every `T ≥ 0`, the certificate on the propagated vector integral, represented samples of any sign,
integrable pieces and mild solutions.** Under the hypotheses of `robust_approx_solver_nonneg_path`,
`RegularApproxOutcome` holds: the generator pieces need only be integrable on their mesh intervals
(`RegularPieces`), and the solution only be mild (`MildSolution`: an integrable propagated forcing
and Duhamel's formula for `x(T)`). -/
theorem robust_approx_solver_nonneg_regular (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (t : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ)
    (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RegularApproxOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  obtain ⟨d, tf, hch, hU, hC⟩ := robust_approx_solver_nonneg D hM t hN etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  refine ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG hreg hsol hUm
    hW hL0 hL' hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have hD : sol T - U 0 (sol 0) T =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T := by
    rw [hsol.2]
    abel
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * meshScale sol b t := by
    rw [hD]
    exact hInt
  exact hC x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG hreg hUm hW hL0 hL' hMass
    hCertP hTarget hB (robustBudget_of_path_int D x hmesh G hG hreg hB1 hB2)

end

end SparseHamiltonian.RepresentedSampleODE
