import TimeDependentExtensions.BlockEncoding.Native
import TimeDependentExtensions.Mesh.Duhamel
import SparseHamiltonian.AlignedMultiOracleProgram

set_option autoImplicit false

/-!
# Time-dependent simulation with time-indexed block encodings (`hs:eq:blockadditive`)

The chronological argument of Theorem `hs:thm:time` with the block-encoding interface of
`Native.lean` (`D_{0,r} = i O_r`, `Q = ν = 1`). The represented samples are
`H̃_r = α J† O_r J` (`blockSample`); the clock runs on `N` slots of length `T / N` with step
`w = α T / N`, and slot `k` uses the sample `σ k`.

* `core`: on any isometric encoding whose active layers are implemented at cost `q`, a program
  with at most `6 d q` queries, `d` the filter degree at `Q = ν = 1`, is within
  `2 (ε/3) + N (α T / N)³` of the ordered product of `exp(-i (T/N) H̃_{σ k})`.
* `exists_simulation`: with the controlled time-indexed oracle and three calls per active
  layer.
* `simulation`: on any mesh with breakpoints and the integrated certificate of
  `Hamiltonian.simulation`, under `4 α T ≤ N`, `9 (α T)³ ≤ ε N²` and `9 M α T ≤ ε N`, one
  unitary program and one clean encoding satisfy `‖𝒜 ι - ι U(T)‖ ≤ ε` with at most
  `2304 (α T + 1 + log(3/ε))` calls of the controlled time-indexed block encoding, including
  inverse calls: equation `hs:eq:blockadditive`, `𝒪(α_BE T + log(1/ε))`.
-/

namespace TimeDependentExtensions

namespace BlockEncoding

noncomputable section

open SparseHamiltonian SparseHamiltonian.TimeDependent ContinuousLinearMap OracleCircuit
open CayleyClockInterface MeasureTheory Set
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

/-- The represented sample `H̃_r = α J† O_r J`. -/
def blockSample {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (O : K →L[ℂ] K) (J : P →L[ℂ] K) (α : ℝ) : P →L[ℂ] P :=
  (α : ℂ) • compressed O J

section Core

variable {X P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] [FiniteDimensional ℂ K]
  {M : ℕ}

/-- The ordered product of the slot exponentials `exp(-i (T/N) H̃_{σ k})`. -/
def blockEvolution (O : X → Fin M → K →L[ℂ] K) (J : P →L[ℂ] K) (σ : ℕ → Fin M) (N : ℕ)
    (α T : ℝ) (x : X) : P →L[ℂ] P :=
  evolution (fun k => NormedSpace.exp ((-Complex.I * ((T / N : ℝ) : ℂ)) •
    blockSample (O x (σ k)) J α)) N

variable {Label K' : Type*}
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

set_option maxRecDepth 8192 in
/-- The chronological construction with block-encoded samples, on any isometric encoding of
the clock workspace whose active layers are implemented at cost `q`. -/
theorem core (O : X → Fin M → K →L[ℂ] K) (hOs : ∀ x r, star (O x r) = O x r)
    (hOu : ∀ x r, IsUnitary (O x r)) (J : P →L[ℂ] K) (hJ : J† ∘L J = 1) (σ : ℕ → Fin M)
    {N : ℕ} (hN : 0 < N) (α T ε : ℝ) (hα : 0 < α) (hT : 0 ≤ T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hStep : α * T / N ≤ 1 / 4)
    (O' : Label → X → K' →L[ℂ] K') (hO' : ∀ l x, IsUnitary (O' l x))
    (E : SharpClockQuery.Space (P := P) (V := K) (α * T / N) 1 1 N (ε / 3) →L[ℂ] K')
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree 1 ((N : ℝ) * (α * T / N) * 1) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O'
        (fun x => activeClockV (P := P) (fun k => privateAction (O x (σ k))) N
          (SharpFilterSchedule.degree 1 ((N : ℝ) * (α * T / N) * 1) (ε / 3)) r) E q) :
    ∃ p : MultiOracleCircuit.Program O',
      p.count ≤ 6 * SharpFilterSchedule.degree 1 ((N : ℝ) * (α * T / N) * 1) (ε / 3) * q ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.input (P := P) (V := K) (α * T / N) 1 1 N
            (ε / 3)) -
          (E ∘L SharpClockSimulation.output (P := P) (V := K) (α * T / N) 1 1 N (ε / 3)) ∘L
            blockEvolution O J σ N α T x‖ ≤
          2 * (ε / 3) + N * (α * T / N) ^ 3 := by
  classical
  let w := α * T / N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 ≤ w := div_nonneg (mul_nonneg hα.le hT) hNR.le
  have hD : ∀ x k, (privateAction (O x (σ k)))† ∘L privateAction (O x (σ k)) = 1 :=
    fun x k => privateAction_isometry _ (hOs x (σ k)) (hOu x (σ k))
  obtain ⟨p, hCount, hEval⟩ := implementationV_query_certificate
    (fun x k => privateAction (O x (σ k))) J w 1 1 N (ε / 3) le_rfl hw hStep hD hJ O' hO'
    E hE q hQuery
  have hOutIso := SharpClockSimulation.output_isometry (P := P) (V := K) w 1 1 N (ε / 3)
    le_rfl
  refine ⟨p, hCount, fun x => ⟨p.eval_unitary hO' x, ?_⟩⟩
  let H : ℕ → P →L[ℂ] P := fun k => compressed (O x (σ k)) J
  have hbq : Real.sqrt (1 / 2) ^ 2 ≤ 1 / 2 := by rw [Real.sq_sqrt (by norm_num)]
  obtain ⟨U, R, hRRight, _hRLeft, hCayley, _hIso, hImpl, _hDeg⟩ :=
    exists_precise_implementationV (fun k => privateAction (O x (σ k)))
      (fun k => resolvent (O x (σ k))) J H w 1 (Real.sqrt (1 / 2)) 1 N le_rfl hw hStep (hD x)
      hJ (fun k => resolvent_right _ (hOs x (σ k)) (hOu x (σ k)))
      (fun k => resolvent_left _ (hOs x (σ k)) (hOu x (σ k)))
      (fun k => resolvent_norm_le _ (hOu x (σ k)))
      (fun k => resolvent_boundary _ J hJ)
      (fun k => compressed_self_adjoint _ (hOs x (σ k)) J)
      (fun k => compressed_norm_le _ (hOu x (σ k)) J hJ)
      (fun k => endpoint_norm_le _ (hOs x (σ k)) (hOu x (σ k)) J hJ) hbq le_rfl (ε / 3)
      (by positivity) (by linarith)
  -- Each Cayley step is within `(α T / N)^3` of the slot exponential.
  let Xs : ℕ → P →L[ℂ] P := fun k => (-Complex.I * (w : ℂ)) • H k
  have hXA : ∀ k, Xs k = (-Complex.I * ((T / N : ℝ) : ℂ)) • blockSample (O x (σ k)) J α := by
    intro k
    change (-Complex.I * (w : ℂ)) • H k = _
    rw [blockSample, smul_smul]
    congr 1
    simp only [w]
    push_cast
    ring
  have hSkew : ∀ k, star (Xs k) = -Xs k := by
    intro k
    change star ((-Complex.I * (w : ℂ)) • H k) = -((-Complex.I * (w : ℂ)) • H k)
    rw [star_smul, compressed_self_adjoint _ (hOs x (σ k)) J]
    rw [← neg_smul]
    congr 1
    simp [Complex.conj_ofReal]
  have hXnorm : ∀ k, ‖Xs k‖ ≤ α * T / N := by
    intro k
    calc
      ‖Xs k‖ = w * ‖H k‖ := by
        change ‖(-Complex.I * (w : ℂ)) • H k‖ = _
        rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
          Real.norm_of_nonneg hw]
      _ ≤ w * 1 := mul_le_mul_of_nonneg_left (compressed_norm_le _ (hOu x (σ k)) J hJ) hw
      _ = α * T / N := mul_one w
  have hXone : ∀ k, ‖Xs k‖ ≤ 1 := fun k => (hXnorm k).trans (by linarith)
  have hnum : ∀ k, CayleyTransfer.cayleyNumerator w (H k) = 1 + (1 / 2 : ℂ) • Xs k := by
    intro k
    simp only [CayleyTransfer.cayleyNumerator, Xs, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have hden : ∀ k, CayleyTransfer.cayleyDenominator w (H k) = 1 - (1 / 2 : ℂ) • Xs k := by
    intro k
    simp only [CayleyTransfer.cayleyDenominator, Xs, smul_smul]
    rw [sub_eq_add_neg, ← neg_smul]
    congr 2
    ring
  have hUform : ∀ k, U k = (1 + (1 / 2 : ℂ) • Xs k) * R k := by
    intro k
    rw [hCayley k, hnum k]
    rfl
  have hRform : ∀ k, (1 - (1 / 2 : ℂ) • Xs k) * R k = 1 := by
    intro k
    rw [← hden k]
    exact hRRight k
  have hStepErr : ∀ k, ‖U k - NormedSpace.exp (Xs k)‖ ≤ (α * T / N) ^ 3 := by
    intro k
    have h := CayleyApproximation.cayley_power_exp_error_of_inverse (Xs k) (R k)
      (hXone k) (hSkew k) (hRform k) 1
    rw [pow_one, one_smul, Nat.cast_one, one_mul, ← hUform k] at h
    exact h.trans (pow_le_pow_left₀ (norm_nonneg _) (hXnorm k) 3)
  have hUnorm : ∀ k, ‖U k‖ ≤ 1 := by
    intro k
    rw [hUform k]
    exact CayleyTransfer.skew_cayley_norm_le_one (Xs k) (R k) (hSkew k) (hRform k)
  have hExpNorm : ∀ k, ‖NormedSpace.exp (Xs k)‖ ≤ 1 := fun k =>
    CayleyApproximation.skew_exp_norm_le (Xs k) (hSkew k)
  have hProd : ‖evolution U N - blockEvolution O J σ N α T x‖ ≤ N * (α * T / N) ^ 3 := by
    have hEq : blockEvolution O J σ N α T x =
        evolution (fun k => NormedSpace.exp (Xs k)) N := by
      simp only [blockEvolution, hXA]
    rw [hEq]
    exact evolution_sub_norm_le_mul U _ hUnorm hExpNorm hStepErr N
  have hOutNorm : ‖SharpClockSimulation.output (P := P) (V := K) w 1 1 N (ε / 3)‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have h := ((SharpClockSimulation.output (P := P) (V := K) w 1 1 N
      (ε / 3)).norm_map_iff_adjoint_comp_self.mpr hOutIso) v
    rw [h, one_mul]
  have hMain : ‖p.eval x ∘L (E ∘L SharpClockQuery.input (P := P) (V := K) w 1 1 N (ε / 3)) -
      (E ∘L SharpClockSimulation.output (P := P) (V := K) w 1 1 N (ε / 3)) ∘L
        evolution U N‖ ≤ 2 * (ε / 3) := by
    rw [hEval x, comp_assoc, ← comp_sub, EncodedOracle.norm_comp_eq E hE]
    exact hImpl
  calc
    _ ≤ ‖p.eval x ∘L (E ∘L SharpClockQuery.input (P := P) (V := K) w 1 1 N (ε / 3)) -
          (E ∘L SharpClockSimulation.output (P := P) (V := K) w 1 1 N (ε / 3)) ∘L
            evolution U N‖ +
        ‖(E ∘L SharpClockSimulation.output (P := P) (V := K) w 1 1 N (ε / 3)) ∘L
            evolution U N -
          (E ∘L SharpClockSimulation.output (P := P) (V := K) w 1 1 N (ε / 3)) ∘L
            blockEvolution O J σ N α T x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (ε / 3) + N * (α * T / N) ^ 3 := by
      apply add_le_add hMain
      rw [← comp_sub, comp_assoc, EncodedOracle.norm_comp_eq E hE]
      calc
        _ ≤ ‖SharpClockSimulation.output (P := P) (V := K) w 1 1 N (ε / 3)‖ *
            ‖evolution U N - blockEvolution O J σ N α T x‖ := opNorm_comp_le _ _
        _ ≤ 1 * (N * (α * T / N) ^ 3) :=
          mul_le_mul hOutNorm hProd (norm_nonneg _) zero_le_one
        _ = N * (α * T / N) ^ 3 := one_mul _

end Core

/-! ### The controlled time-indexed oracle -/

variable {X n B₀ : Type*} [Fintype n] [DecidableEq n] [Fintype B₀] [DecidableEq B₀] {M : ℕ}

/-- The filter degree at `Q = ν = 1` and step `α T / N`. -/
def degree (N : ℕ) (α T ε : ℝ) : ℕ :=
  SharpFilterSchedule.degree 1 ((N : ℝ) * (α * T / N) * 1) (ε / 3)

/-- The fixed clean input on `N` slots. -/
def input (hM : 0 < M) (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀)
    (hJ : J† ∘L J = 1) (σ : ℕ → Fin M) (N : ℕ) (α T ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical B₀ M N (degree N α T ε) :=
  (embedding hM b₀ J hJ σ N (degree N α T ε)).toContinuousLinearMap ∘L
    SharpClockQuery.input (P := EuclideanSpace ℂ n) (V := EuclideanSpace ℂ B₀)
      (α * T / N) 1 1 N (ε / 3)

/-- The fixed clean output on `N` slots. -/
def output (hM : 0 < M) (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀)
    (hJ : J† ∘L J = 1) (σ : ℕ → Fin M) (N : ℕ) (α T ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical B₀ M N (degree N α T ε) :=
  (embedding hM b₀ J hJ σ N (degree N α T ε)).toContinuousLinearMap ∘L
    SharpClockSimulation.output (P := EuclideanSpace ℂ n) (V := EuclideanSpace ℂ B₀)
      (α * T / N) 1 1 N (ε / 3)

set_option maxRecDepth 8192 in
omit [DecidableEq n] in
/-- An actual program of controlled time-indexed block-encoding queries approximates the
ordered product of the slot exponentials, uniformly over the unknown instance. -/
theorem exists_simulation (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hOs : ∀ x r, star (O x r) = O x r) (hOu : ∀ x r, IsUnitary (O x r)) (hM : 0 < M)
    (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (hJ : J† ∘L J = 1)
    (σ : ℕ → Fin M) {N : ℕ} (hN : 0 < N) (α T ε : ℝ) (hα : 0 < α) (hT : 0 ≤ T) (hε : 0 < ε)
    (hεOne : ε ≤ 1) (hStep : α * T / N ≤ 1 / 4) :
    ∃ p : MultiOracleCircuit.Program (oracle O N (degree N α T ε)),
      p.count ≤ 6 * degree N α T ε * 3 ∧
      (input hM b₀ J hJ σ N α T ε)† ∘L input hM b₀ J hJ σ N α T ε = 1 ∧
      (output hM b₀ J hJ σ N α T ε)† ∘L output hM b₀ J hJ σ N α T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input hM b₀ J hJ σ N α T ε -
            output hM b₀ J hJ σ N α T ε ∘L blockEvolution O J σ N α T x‖ ≤
          2 * (ε / 3) + N * (α * T / N) ^ 3 := by
  have hE := (embedding hM b₀ J hJ σ N (degree N α T ε)).adjoint_comp_self
  have hInIso := SharpClockQuery.input_isometry (P := EuclideanSpace ℂ n)
    (V := EuclideanSpace ℂ B₀) (α * T / N) 1 1 N (ε / 3) le_rfl
  have hOutIso := SharpClockSimulation.output_isometry (P := EuclideanSpace ℂ n)
    (V := EuclideanSpace ℂ B₀) (α * T / N) 1 1 N (ε / 3) le_rfl
  obtain ⟨p, hCount, hAction⟩ := core O hOs hOu J hJ σ hN α T ε hα hT hε hεOne hStep
    (oracle O N (degree N α T ε)) (oracle_unitary O hOu N _)
    (embedding hM b₀ J hJ σ N (degree N α T ε)).toContinuousLinearMap hE 3
    (fun r _ => implementsOn O hOu hM b₀ J hJ σ N _ r)
  exact ⟨p, hCount, Sampled.isometry_comp _ _ hE hInIso, Sampled.isometry_comp _ _ hE hOutIso,
    hAction⟩

/-! ### The complete theorem -/

/-- The complete workspace, including the alignment spectator. -/
abbrev Workspace (B₀ : Type*) [Fintype B₀] (M N : ℕ) (α T ε : ℝ) :=
  CleanOutputAlignment.Double (Physical B₀ M N (degree N α T ε))

/-- Each query is one controlled time-indexed block-encoding call with untouched spectator
registers. -/
abbrev alignedOracle (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀) (N : ℕ)
    (α T ε : ℝ) : Unit → X → Workspace B₀ M N α T ε →L[ℂ] Workspace B₀ M N α T ε :=
  AlignedMultiOracleProgram.oracle (oracle O N (degree N α T ε))

/-- The same known clean preparation at both ends; it depends only on public data. -/
def alignedInput (hM : 0 < M) (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀)
    (hJ : J† ∘L J = 1) (t : ℕ → ℝ) (N : ℕ) (α T ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Workspace B₀ M N α T ε :=
  AlignedMultiOracleProgram.input (input hM b₀ J hJ (pieceOf t T N hM) N α T ε)

theorem blockSample_self_adjoint {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (O : K →L[ℂ] K) (hO : star O = O) (J : P →L[ℂ] K) (α : ℝ) :
    star (blockSample O J α) = blockSample O J α := by
  rw [blockSample, star_smul, compressed_self_adjoint O hO J, Complex.star_def,
    Complex.conj_ofReal]

theorem blockSample_norm_le {P K : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (O : K →L[ℂ] K) (hU : IsUnitary O) (J : P →L[ℂ] K) (hJ : J† ∘L J = 1) {α : ℝ}
    (hα : 0 ≤ α) : ‖blockSample O J α‖ ≤ α := by
  rw [blockSample, norm_smul, Complex.norm_real, Real.norm_of_nonneg hα]
  simpa using mul_le_mul_of_nonneg_left (compressed_norm_le O hU J hJ) hα

theorem sampleIndex_of_lt (hM : 0 < M) {r : ℕ} (hr : r < M) :
    Sampled.sampleIndex hM r = ⟨r, hr⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hr)

set_option maxRecDepth 8192 in
omit [DecidableEq n] in
/-- **Equation `hs:eq:blockadditive`: time-dependent simulation with time-indexed block
encodings.** Coherent and controlled access to Hermitian unitaries `O_r` with
`J† O_r J = H̃_r / α` is supplied as the controlled time-indexed oracle. On any mesh, under
`4 α T ≤ N`, `9 (α T)³ ≤ ε N²` and `9 M α T ≤ ε N`, one input-independent unitary program and
one fixed clean encoding satisfy `‖𝒜 ι - ι U(T)‖ ≤ ε` for every instance, every path with
self-adjoint, interval-integrable pieces whose integrated sample errors
`∑_r ∫ ‖H_r(u) - H̃_r‖ du` are at most `ε / 9`, and every propagator of that path, with at most
`2304 (α T + 1 + log(3/ε))` queries, including inverse calls. -/
theorem simulation (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (hOs : ∀ x r, star (O x r) = O x r) (hOu : ∀ x r, IsUnitary (O x r)) (hM : 0 < M)
    (b₀ : B₀) (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (hJ : J† ∘L J = 1)
    (t : ℕ → ℝ) (α T ε : ℝ) (N : ℕ) (hα : 0 < α) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hN : 0 < N) (hmesh : IsMesh t M T)
    (hClock : 4 * (α * T) ≤ N) (hCayley : 9 * (α * T) ^ 3 ≤ ε * (N : ℝ) ^ 2)
    (hRefine : 9 * M * (α * T) ≤ ε * N) :
    ∃ p : MultiOracleCircuit.Program (alignedOracle O N α T ε),
      (p.count : ℝ) ≤ 2304 * (α * T + 1 + Real.log (3 / ε)) ∧
      (alignedInput hM b₀ J hJ t N α T ε)† ∘L alignedInput hM b₀ J hJ t N α T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ (Hp : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
          (U : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
          (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), star (Hp r u) = Hp r u) →
          (∀ r : Fin M, IntervalIntegrable (Hp r) volume (t r) (t ((r : ℕ) + 1))) →
          ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖Hp r u - blockSample (O x r) J α‖ ≤
            ε / 9 →
          U 0 = 1 →
          (∀ r : Fin M, SolvesOn (Hp r) U (t r) (t ((r : ℕ) + 1))) →
          ‖p.eval x ∘L alignedInput hM b₀ J hJ t N α T ε -
            alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ ≤ ε := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hStep : α * T / N ≤ 1 / 4 := by
    rw [div_le_iff₀ hNR]
    linarith
  let σ := pieceOf t T N hM
  obtain ⟨p, hCount, hIn, hOut, hAct⟩ := exists_simulation O hOs hOu hM b₀ J hJ σ hN α T ε hα
    hT.le hε hεOne hStep
  let q := AlignedMultiOracleProgram.program _ _ hIn hOut p
  refine ⟨q, ?_, AlignedMultiOracleProgram.input_isometry _ hIn, fun x => ⟨?_, ?_⟩⟩
  · have hqc : q.count = p.count := AlignedMultiOracleProgram.program_count _ _ hIn hOut p
    have hW : 0 ≤ (N : ℝ) * (α * T / N) * 1 := by positivity
    have hdeg : (degree N α T ε : ℝ) ≤ 128 * ((N : ℝ) * (α * T / N) * 1 +
        1 * (1 + SharpFilterSchedule.logBudget (ε / 3))) :=
      SharpFilterSchedule.degree_le 1 ((N : ℝ) * (α * T / N) * 1) (ε / 3) le_rfl hW
        (by positivity) (by linarith)
    have hWeq : (N : ℝ) * (α * T / N) * 1 = α * T := by field_simp
    have hlog : SharpFilterSchedule.logBudget (ε / 3) = Real.log (3 / ε) := by
      unfold SharpFilterSchedule.logBudget
      congr 1
      field_simp
    rw [hWeq, hlog] at hdeg
    have hpc : (p.count : ℝ) ≤ 6 * (degree N α T ε : ℝ) * 3 := by exact_mod_cast hCount
    have hdeg' : (degree N α T ε : ℝ) ≤ 128 * (α * T + 1 * (1 + Real.log (3 / ε))) := hdeg
    calc (q.count : ℝ) = (p.count : ℝ) := by exact_mod_cast hqc
      _ ≤ 6 * (degree N α T ε : ℝ) * 3 := hpc
      _ ≤ 6 * (128 * (α * T + 1 * (1 + Real.log (3 / ε)))) * 3 := by nlinarith
      _ = 2304 * (α * T + 1 + Real.log (3 / ε)) := by ring
  · exact q.eval_unitary (CoherentQuerySchedule.oracle_unitary _ (oracle_unitary O hOu N _)) x
  · intro Hp U hPath hInt hCert hU0 hU
    have hErr := (hAct x).2
    let A : ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      blockSample (O x (Sampled.sampleIndex hM r)) J α
    let Hq : ℕ → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n := fun r =>
      Hp (Sampled.sampleIndex hM r)
    have hEvol : blockEvolution O J σ N α T x = refinedEvolution A t T N M := by
      unfold blockEvolution refinedEvolution
      congr 1
      funext k
      have hk : Sampled.sampleIndex hM (slotPiece t T N M k) = σ k :=
        sampleIndex_of_lt hM (slotPiece_lt hM k)
      simp only [A, hk]
    rw [hEvol] at hErr
    have hPw : IsPiecewisePropagator Hq t M U := by
      refine ⟨hU0, fun r hr => ?_⟩
      have h := hU ⟨r, hr⟩
      simp only [Hq, sampleIndex_of_lt hM hr]
      exact h
    have hHq : ∀ r < M, ∀ u ∈ Icc (t r) (t (r + 1)), star (Hq r u) = Hq r u := by
      intro r hr u hu
      simp only [Hq, sampleIndex_of_lt hM hr]
      exact hPath ⟨r, hr⟩ u hu
    have hA : ∀ r, star (A r) = A r := fun r => blockSample_self_adjoint _ (hOs _ _) J α
    have hΛ : ∀ r, ‖A r‖ ≤ α := fun r => blockSample_norm_le _ (hOu _ _) J hJ hα.le
    have hIntq : ∀ r < M, IntervalIntegrable (Hq r) volume (t r) (t (r + 1)) := by
      intro r hr
      simp only [Hq, sampleIndex_of_lt hM hr]
      exact hInt ⟨r, hr⟩
    have hRef := refined_error A hmesh hT hN hPw hHq hA hΛ hIntq
    have hCertR : ∑ r ∈ Finset.range M, ∫ u in t r..t (r + 1), ‖Hq r u - A r‖ ≤ ε / 9 := by
      rw [← Fin.sum_univ_eq_sum_range (fun r => ∫ u in t r..t (r + 1), ‖Hq r u - A r‖) M]
      have hidx : ∀ r : Fin M, Sampled.sampleIndex hM r = r := fun r =>
        sampleIndex_of_lt hM r.isLt
      simpa only [Hq, A, hidx] using hCert
    have hOutNorm : ‖output hM b₀ J hJ σ N α T ε‖ ≤ 1 := by
      apply opNorm_le_bound _ zero_le_one
      intro v
      rw [((output hM b₀ J hJ σ N α T ε).norm_map_iff_adjoint_comp_self.mpr hOut) v, one_mul]
    let S := refinedEvolution A t T N M
    have hAligned := AlignedMultiOracleProgram.program_error _ _ hIn hOut p x (U T)
    change ‖q.eval x ∘L alignedInput hM b₀ J hJ t N α T ε -
      alignedInput hM b₀ J hJ t N α T ε ∘L U T‖ ≤ ε
    rw [show alignedInput hM b₀ J hJ t N α T ε = AlignedMultiOracleProgram.input
      (input hM b₀ J hJ σ N α T ε) from rfl, hAligned]
    have hCay : (N : ℝ) * (α * T / N) ^ 3 ≤ ε / 9 := by
      have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have heq : (N : ℝ) * (α * T / N) ^ 3 = (α * T) ^ 3 / (N : ℝ) ^ 2 := by
        field_simp
      rw [heq, div_le_iff₀ hNsq]
      linarith
    have hMis : (M : ℝ) * (T / N) * α ≤ ε / 9 := by
      have heq : (M : ℝ) * (T / N) * α = M * (α * T) / N := by
        field_simp
      rw [heq, div_le_iff₀ hNR]
      linarith
    calc
      _ ≤ ‖p.eval x ∘L input hM b₀ J hJ σ N α T ε - output hM b₀ J hJ σ N α T ε ∘L S‖ +
          ‖output hM b₀ J hJ σ N α T ε ∘L S - output hM b₀ J hJ σ N α T ε ∘L U T‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (2 * (ε / 3) + N * (α * T / N) ^ 3) + 1 * (ε / 9 + M * (T / N) * α) := by
        apply add_le_add hErr
        rw [← comp_sub]
        refine (opNorm_comp_le _ _).trans (mul_le_mul hOutNorm ?_ (norm_nonneg _) zero_le_one)
        rw [norm_sub_rev]
        exact hRef.trans (add_le_add_left hCertR _)
      _ ≤ ε := by linarith

end

end BlockEncoding

end TimeDependentExtensions
