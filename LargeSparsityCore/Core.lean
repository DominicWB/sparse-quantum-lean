import LargeSparsityCore.Parameters
import LargeSparsityCore.Smoothing

set_option autoImplicit false

/-!
# The abstract large-sparsity core

This module assembles the large-sparsity core (`opt:sec:core`) on abstract private data. The
private generator `K`, its Cayley transform `D`, the isolated spectral projections `P_±` and the
known boundary `J` are required to satisfy the block structure `CayleyBlocks.Spectral` with
`2q = cot(π/p)` and the moment bounds of `opt:eq:joint-moments` and `opt:eq:isolated-weights`
(`CoreData`):

* `‖R₁ P₀‖ ≤ Q₀ = 2q/h` on the bulk `P₀ = 1 - P₊ - P₋`;
* `‖P_± J‖² ≤ h/(2s)` (`w_iso = β/(2s)` with `β = h`);
* `‖K P₀ J‖² ≤ 2q²/s` and `‖K J‖² ≤ 2q²(1 + h)/s`;
* `‖J† K J‖ ≤ 1`.

With the parameters of `Parameters` (`N_s` slots of weight `v = a/N_s`, the product filter
`g_{B₀}^m g_p^k` of degree `d`), the amplified chronological clock (`implementation`) is an
isometry with full-output error at most `ε` for `e^{-i a J†KJ}` (`core_implementation`): the
filter estimate `‖f(D_g)‖ ≤ ε/3` (`CoreFilter.filter_bound`, `Parameters.Regime.filter_estimate`)
gives `2ε/3` after amplification (`Smoothing.exists_implementation`), and the Cayley
discretisation gives `ε/3` (`SparseHamiltonian.CayleyApproximation.hamiltonian_cayley_error`).
The catalyst `ν = (1 + 2q²(1 + h)/s)/2` (`opt:eq:nu-W`) satisfies `6aν ≤ d`
(`opt:eq:degree-catalyst`). The parameter `s ≥ 1` is real: the sparsity in the large-sparsity
core, the moment parameter `σ = sμ²/η²` in Appendix B.

`core_query` is the query form: if every synchronized active clock layer is implemented with `c`
calls of an oracle family on a fixed encoding, there is a program with at most `6 d c` calls,
unitary for every instance, with full-output error at most `ε` with the same known embedding on
input and output (the output preparation is aligned with the input preparation by the known
diagonal sign unitary `sign`). The degree is `d ≤ 21520 √(sτr)`
(`Parameters.Regime.degree_le_sqrt`).
-/

namespace LargeSparsityCore.Core

noncomputable section

open ContinuousLinearMap SparseHamiltonian CayleyBlocks Parameters
open GlobalResolvent ChronologicalResolvent OracleCircuit LabeledEncodedOracle
open ReuseLayerFactorization
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### The catalyst endpoint -/

theorem adjoint_R1 {K : V →L[ℂ] V} (hK : IsSelfAdjoint K) :
    (R1 K)† = (2 : ℂ)⁻¹ • (1 - Complex.I • K) := by
  rw [R1, map_smulₛₗ, map_add, map_smulₛₗ, adjoint_one, hK.adjoint_eq, map_inv₀, map_ofNat,
    Complex.conj_I, neg_smul, ← sub_eq_add_neg]

/-- `R₁† R₁ = (1 + K²)/4`. -/
theorem adjoint_R1_comp_R1 {K : V →L[ℂ] V} (hK : IsSelfAdjoint K) :
    (R1 K)† ∘L R1 K = (4 : ℂ)⁻¹ • (1 + K ∘L K) := by
  have e : (1 - Complex.I • K) ∘L (1 + Complex.I • K) =
      1 - (Complex.I * Complex.I) • (K ∘L K) := by
    simp only [sub_comp, comp_add, one_comp, comp_one, smul_comp, comp_smul]
    module
  rw [adjoint_R1 hK, R1, smul_comp, comp_smul, smul_smul, e, Complex.I_mul_I, neg_smul, one_smul,
    sub_neg_eq_add]
  norm_num

/-- `(R₁ J)† R₁ J = (1 + (K J)† K J)/4` for an isometry `J`. -/
theorem endpoint_gram {K : V →L[ℂ] V} (hK : IsSelfAdjoint K) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) :
    (R1 K ∘L J)† ∘L (R1 K ∘L J) = (4 : ℂ)⁻¹ • (1 + (K ∘L J)† ∘L (K ∘L J)) := by
  rw [adjoint_comp, adjoint_comp, hK.adjoint_eq, comp_assoc, ← comp_assoc (adjoint (R1 K)),
    adjoint_R1_comp_R1 hK]
  simp only [smul_comp, comp_smul, add_comp, comp_add, one_comp, hJ, comp_assoc]

/-- `‖R₁ J‖² ≤ (1 + ‖K J‖²)/4`. -/
theorem endpoint_sq_le {K : V →L[ℂ] V} (hK : IsSelfAdjoint K) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) : ‖R1 K ∘L J‖ ^ 2 ≤ (1 + ‖K ∘L J‖ ^ 2) / 4 := by
  have h1 : ‖R1 K ∘L J‖ ^ 2 = ‖(R1 K ∘L J)† ∘L (R1 K ∘L J)‖ := by
    rw [norm_adjoint_comp_self, sq]
  have h2 : ‖(K ∘L J)† ∘L (K ∘L J)‖ = ‖K ∘L J‖ ^ 2 := by
    rw [norm_adjoint_comp_self, sq]
  rw [h1, endpoint_gram hK J hJ, norm_smul]
  have h3 : ‖(1 : P →L[ℂ] P) + (K ∘L J)† ∘L (K ∘L J)‖ ≤ 1 + ‖K ∘L J‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [h2]
    gcongr
    exact ContinuousLinearMap.norm_id_le
  have h4 : ‖(4 : ℂ)⁻¹‖ = 1 / 4 := by norm_num
  rw [h4]
  linarith

/-- An isometry has norm at most one. -/
theorem norm_le_one_of_isometry {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →L[ℂ] F} (hA : A† ∘L A = 1) : ‖A‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro v
  have hh := (norm_map_iff_adjoint_comp_self A).mpr hA v
  simpa only [one_mul] using hh.le

/-! ### The circuit -/

/-- The filter coefficients `a_j` of `f = g_{B₀}^m g_p^k` (`opt:eq:filter`). -/
def coeff (s : ℝ) (τ ε : ℝ) : ℕ → ℝ :=
  (ProductFilter.poly (B0 s τ ε) (mval τ ε) (pval s τ ε) (kval τ ε)).coeff

variable (P V) in
/-- The coherent workspace of the core implementation. -/
abbrev Space (s : ℝ) (τ ε : ℝ) := Smoothing.Space P V (degree s τ ε) (steps s τ ε)

/-- The amplified chronological clock implementation of the core. -/
def implementation (s : ℝ) (τ ε : ℝ) (D : V →L[ℂ] V) (J : P →L[ℂ] V) :
    P →L[ℂ] Space P V s τ ε :=
  Smoothing.clockImplementation (coeff s τ ε) (degree s τ ε) D J (wval s τ ε) (steps s τ ε)

variable (P V) in
/-- The known input preparation of the coherent smoothing. -/
def input (s : ℝ) (τ ε : ℝ) : P →L[ℂ] Space P V s τ ε :=
  SmoothingLCU.input (P := P) (V := BlockOperator.H (steps s τ ε) V) (coeff s τ ε) (degree s τ ε)

variable (P V) in
/-- The known output preparation of the coherent smoothing. -/
def output (s : ℝ) (τ ε : ℝ) : P →L[ℂ] Space P V s τ ε :=
  SmoothingLCU.output (P := P) (V := BlockOperator.H (steps s τ ε) V) (coeff s τ ε) (degree s τ ε)

variable (P V) in
/-- The branch spaces of the coherent smoothing. -/
abbrev Branch (s : ℝ) (τ ε : ℝ) (i : ReuseWeights.Index (degree s τ ε)) :=
  SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H (steps s τ ε) V) (degree s τ ε) i

variable (P V) in
/-- The known diagonal sign unitary of the smoothing weights. -/
def sign (s : ℝ) (τ ε : ℝ) : Space P V s τ ε →L[ℂ] Space P V s τ ε :=
  WeightedClock.diagonal (fun i => CoherentLCU.coefficientPhase
    (ReuseWeights.weight (coeff s τ ε) (degree s τ ε) i) •
      (1 : Branch P V s τ ε i →L[ℂ] Branch P V s τ ε i))

/-- The sign unitary maps the output preparation to the input preparation. -/
theorem sign_comp_output (s : ℝ) (τ ε : ℝ) :
    sign P V s τ ε ∘L output P V s τ ε = input P V s τ ε := by
  unfold sign output input SmoothingLCU.output SmoothingLCU.input CoherentLCU.branchOutput
    CoherentLCU.branchInput
  rw [WeightedClock.diagonal_boundary]
  congr 1
  funext i
  rw [smul_comp, comp_smul, smul_smul, CoherentLCU.coefficientPhase_sq, one_smul, one_comp]

theorem sign_adjoint (s : ℝ) (τ ε : ℝ) : (sign P V s τ ε)† = sign P V s τ ε := by
  unfold sign
  rw [WeightedClock.diagonal_adjoint]
  congr 1
  funext i
  rw [map_smulₛₗ, CoherentLCU.coefficientPhase_conj, adjoint_one]

theorem sign_mul_self (s : ℝ) (τ ε : ℝ) : sign P V s τ ε ∘L sign P V s τ ε = 1 := by
  unfold sign
  rw [WeightedClock.diagonal_comp]
  have h : ∀ i, (CoherentLCU.coefficientPhase
      (ReuseWeights.weight (coeff s τ ε) (degree s τ ε) i) •
        (1 : Branch P V s τ ε i →L[ℂ] Branch P V s τ ε i)) ∘L
      (CoherentLCU.coefficientPhase (ReuseWeights.weight (coeff s τ ε) (degree s τ ε) i) •
        (1 : Branch P V s τ ε i →L[ℂ] Branch P V s τ ε i)) = 1 := by
    intro i
    rw [smul_comp, comp_smul, smul_smul, CoherentLCU.coefficientPhase_sq, one_smul, one_comp]
  simp only [h]
  exact WeightedClock.diagonal_one

theorem sign_unitary (s : ℝ) (τ ε : ℝ) : IsUnitary (sign P V s τ ε) := by
  constructor
  · change (sign P V s τ ε)† ∘L sign P V s τ ε = 1
    rw [sign_adjoint, sign_mul_self]
  · change sign P V s τ ε ∘L (sign P V s τ ε)† = 1
    rw [sign_adjoint, sign_mul_self]

/-- The hypotheses of the core on the private generator `K`, its Cayley transform `D`, the
isolated spectral projections `P_±` and the known boundary `J` (`opt:eq:joint-moments`,
`opt:eq:isolated-weights`, with `β = h`). -/
structure CoreData (s : ℝ) (τ ε : ℝ) (K D Pp Pm : V →L[ℂ] V) (J : P →L[ℂ] V) : Prop where
  spectral : Spectral K D Pp Pm (qval s τ ε)
  unitary : D† ∘L D = 1
  isometry : J† ∘L J = 1
  bulk_bound : ‖R1 K ∘L CayleyBlocks.bulk Pp Pm‖ ≤ Q0 s τ ε
  iso_p : ‖Pp ∘L J‖ ≤ sw s τ ε
  iso_m : ‖Pm ∘L J‖ ≤ sw s τ ε
  moment : ‖K ∘L CayleyBlocks.bulk Pp Pm ∘L J‖ ≤ sm s τ ε
  second : ‖K ∘L J‖ ^ 2 ≤ 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s
  boundary : ‖J† ∘L K ∘L J‖ ≤ 1

/-- The signed smoothing weights of the core filter have absolute mass two. -/
theorem mass {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε) : ∑ i : ReuseWeights.Index (degree s τ ε),
    |ReuseWeights.weight (coeff s τ ε) (degree s τ ε) i| = 2 :=
  ProductFilter.absolute_mass_two _ _ _ _ R.one_le_B0 R.one_le_p R.degree_pos

/-- The core filter coefficients sum to one. -/
theorem coeff_sum {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε) :
    ∑ j ∈ Finset.range (degree s τ ε + 1), coeff s τ ε j = 1 :=
  ProductFilter.coeff_sum _ _ _ _ R.one_le_B0 R.one_le_p

theorem input_isometry {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε) :
    (input P V s τ ε)† ∘L input P V s τ ε = 1 :=
  SmoothingLCU.input_isometry _ _ R.degree_pos (mass R)

theorem output_isometry {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε) :
    (output P V s τ ε)† ∘L output P V s τ ε = 1 :=
  SmoothingLCU.output_isometry _ _ R.degree_pos (mass R)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- **The abstract large-sparsity core.** In the regime `Parameters.Regime` and under the
hypotheses `CoreData`, the amplified chronological clock with the product filter is an isometry
with full-output error at most `ε` for `e^{-i a J†KJ}`, `a = sτ/q`. -/
theorem core_implementation [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε) {K D Pp Pm : V →L[ℂ] V} {J : P →L[ℂ] V}
    (h : CoreData s τ ε K D Pp Pm J) :
    (implementation s τ ε D J)† ∘L implementation s τ ε D J = 1 ∧
    ‖implementation s τ ε D J - output P V s τ ε ∘L
        NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) • (J† ∘L K ∘L J))‖ ≤ ε := by
  set H := J† ∘L K ∘L J with hHdef
  have hSelf : star H = H := by
    rw [hHdef, ContinuousLinearMap.star_eq_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
      h.spectral.self.adjoint_eq, comp_assoc]
  have hBoundary : J† ∘L R1 K ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H) := by
    rw [hHdef, R1]
    simp only [smul_comp, comp_smul, add_comp, comp_add, one_comp, h.isometry]
  have hν := R.nu_pos
  set Q := max ‖R1 K‖ (nu s τ ε) with hQdef
  have hQ : 0 < Q := lt_of_lt_of_le hν (le_max_right _ _)
  set b := Real.sqrt (nu s τ ε / 2) with hbdef
  have hEnd : ‖R1 K ∘L J‖ ≤ b := by
    apply Real.le_sqrt_of_sq_le
    have h1 := endpoint_sq_le h.spectral.self J h.isometry
    have h2 := h.second
    have e : nu s τ ε / 2 = (1 + 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s) / 4 := by
      unfold nu
      ring
    rw [e]
    linarith
  have hbq : b ^ 2 ≤ nu s τ ε / 2 := by
    rw [hbdef, Real.sq_sqrt (by positivity)]
  have hdeg : 6 * ((steps s τ ε : ℝ) * wval s τ ε * nu s τ ε) ≤ degree s τ ε := by
    rw [steps_mul_w]
    exact R.catalyst_le
  have hfb := CoreFilter.filter_bound h.spectral h.unitary J h.isometry h.bulk_bound h.iso_p
    h.iso_m h.moment R.rho0_mul_Q0 R.zeta_pos R.rho0_pos R.w_nonneg R.small_step R.sep
    R.lamp_inside R.lamm_inside (steps s τ ε) (B0 s τ ε) (mval τ ε) (pval s τ ε) (kval τ ε)
    R.one_le_B0 R.one_le_p R.one_le_m R.F_lamp R.F_lamm
  rw [steps_mul_w] at hfb
  have hfilter := hfb.trans R.filter_estimate
  have hε := R.ε_pos
  have hε1 := R.ε_le
  obtain ⟨U, R', hDen, hU, _hUT1, _hUT2, hIso, hErr⟩ :=
    Smoothing.exists_implementation (coeff s τ ε) (degree s τ ε) R.degree_pos (mass R)
      (coeff_sum R) D (R1 K) J H (wval s τ ε) Q b (nu s τ ε) (steps s τ ε) hQ R.w_nonneg
      (w_le_quarter s τ ε) h.unitary h.isometry h.spectral.cayley_right h.spectral.cayley_left
      (le_max_left _ _) hBoundary hSelf h.boundary hEnd hbq (le_max_right _ _) hdeg (ε / 3)
      (by positivity) (by linarith) hfilter
  have hw1 : wval s τ ε ≤ 1 := (w_le_quarter s τ ε).trans (by norm_num)
  have hCay := CayleyApproximation.hamiltonian_cayley_error H R' (wval s τ ε) R.w_nonneg hw1
    hSelf h.boundary hDen (steps s τ ε)
  have hTW : ((steps s τ ε : ℂ) * (wval s τ ε : ℂ)) = (aval s τ ε : ℂ) := by
    exact_mod_cast steps_mul_w s τ ε
  have hTarget : ‖U ^ steps s τ ε - NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) • H)‖ ≤
      ε / 3 := by
    have e : -Complex.I * (steps s τ ε : ℂ) * (wval s τ ε : ℂ) =
        -Complex.I * (aval s τ ε : ℂ) := by
      rw [mul_assoc, hTW]
    rw [hU]
    rw [e] at hCay
    exact hCay.trans R.cubic_le
  refine ⟨hIso, ?_⟩
  have := Smoothing.implementation_error_to_target (coeff s τ ε) (degree s τ ε) R.degree_pos
    (mass R) _ (U ^ steps s τ ε) _ _ _ _ (2 * (ε / 3)) (ε / 3) hErr hTarget
  calc _ ≤ 2 * (ε / 3) + ε / 3 := this
    _ = ε := by ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- **The abstract large-sparsity core, query form.** If every synchronized active clock layer
of the private operators `D x` is implemented with `c` calls of a unitary oracle family `O` on a
fixed encoding `E`, then a program with at most `6 d c` calls, unitary for every instance,
implements `e^{-i a J†K(x)J}` with full-output error at most `ε`, with the same known embedding
`E ∘ input` on input and output. -/
theorem core_query [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X Label : Type*} {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {s : ℝ} {τ ε : ℝ} (R : Regime s τ ε) (K D Pp Pm : X → V →L[ℂ] V)
    (J : P →L[ℂ] V) (hJ : J† ∘L J = 1) (h : ∀ x, CoreData s τ ε (K x) (D x) (Pp x) (Pm x) J)
    (O : Label → X → W →L[ℂ] W) (hO : ∀ l x, IsUnitary (O l x))
    (E : Space P V s τ ε →L[ℂ] W) (hE : E† ∘L E = 1) (c : ℕ)
    (hQuery : ∀ r < 2 * degree s τ ε, ImplementsOn O
      (fun x => activeClock (P := P) (D x) (steps s τ ε) (degree s τ ε) r) E c) :
    ∃ p : MultiOracleCircuit.Program O, p.count ≤ 6 * degree s τ ε * c ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L input P V s τ ε) - (E ∘L input P V s τ ε) ∘L
          NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) • (J† ∘L K x ∘L J))‖ ≤ ε := by
  obtain ⟨p, hcount, hp⟩ := Smoothing.implementation_query_certificate (coeff s τ ε)
    (degree s τ ε) R.degree_pos (mass R) D J (wval s τ ε) (steps s τ ε) R.w_nonneg
    (w_le_quarter s τ ε) (fun x => (h x).unitary) hJ O hO E hE c hQuery
  obtain ⟨pS, hpS, hcS⟩ := ImplementsOn.fixed (O := O) (X := X) hE (sign P V s τ ε)
    (sign_unitary s τ ε)
  have hEn : ‖E‖ ≤ 1 := norm_le_one_of_isometry hE
  have hSn : ‖sign P V s τ ε‖ ≤ 1 :=
    norm_le_one_of_isometry (by rw [sign_adjoint, sign_mul_self])
  refine ⟨.seq pS p, ?_, fun x => ⟨MultiOracleCircuit.Program.eval_unitary _ hO x, ?_⟩⟩
  · change pS.count + p.count ≤ _
    omega
  · obtain ⟨_, herr⟩ := core_implementation R (h x)
    have hEq : (MultiOracleCircuit.Program.seq pS p).eval x ∘L (E ∘L input P V s τ ε) =
        E ∘L (sign P V s τ ε ∘L implementation s τ ε (D x) J) := by
      change (pS.eval x ∘L p.eval x) ∘L (E ∘L input P V s τ ε) = _
      rw [input, comp_assoc, hp x, ← comp_assoc, hpS x, comp_assoc]
      rfl
    rw [hEq, ← sign_comp_output, comp_assoc, comp_assoc, ← comp_sub, ← comp_sub]
    calc ‖E ∘L (sign P V s τ ε ∘L (implementation s τ ε (D x) J - output P V s τ ε ∘L
          NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) • (J† ∘L K x ∘L J))))‖ ≤
          ‖E‖ * (‖sign P V s τ ε‖ * ‖implementation s τ ε (D x) J - output P V s τ ε ∘L
            NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) • (J† ∘L K x ∘L J))‖) :=
          (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
            (norm_nonneg _))
      _ ≤ 1 * (1 * ε) := by gcongr
      _ = ε := by ring

end

end LargeSparsityCore.Core
