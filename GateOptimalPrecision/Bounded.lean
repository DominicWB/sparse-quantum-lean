import GateOptimalPrecision.ClippedTheorem
import SparseHamiltonian.CayleyClockInterface
import SparseHamiltonian.ImprovedPrecisionBudget

/-!
# The bounded-logarithm regime at the gate level

Section `gate:sec:combine`: "If `h_a = log(e + L_a/Θ)` is bounded by the fixed threshold, use the
baseline gate-efficient Cayley construction. With `E_H` the orientation entry operator normalised
by `μ`, it uses `K₀ = √σ E_H`, `J₀†K₀J₀ = H/(√s η)`, `J₀†K₀²J₀ ⪯ I`, `‖K₀‖ ≤ √σ`. Its rescaling
optimisation gives `O(A + √(BL_a) + L_a)` calls. … The baseline gate proof uses exactly the
boundary, native Cayley and reuse circuits of Section `gate:sec:compiler`."

The interface is the generator form of the baseline (`SparseHamiltonian.CayleyClockInterface`):
a self-adjoint generator `K₀` on `a` ancilla qubits and the system with `‖K₀‖ ≤ √σ` and a
boundary `J₀ = U_J ι₀` with `‖K₀ J₀‖ ≤ 1`. For the public rescaling `γ` of the baseline
(`bdGamma`: `ImprovedPrecisionBudget.exists_rescaling_for_precision` at `(σ, θ, ε)`), the private
operation is the Cayley transform `D = (γK₀ + i)(γK₀ - i)⁻¹` (`cayleyGate`; the inverse exists in
finite dimension: `isUnit_sub_I`, `cayleyInv_right`, `cayleyInv_left`), and the circuit is the
released baseline circuit `Sim.simCircuit a τ Q qbar ε` with `τ = θ√σ/γ`, `Q = ⌈max(1, γ√σ)⌉`
and `qbar = (1 + γ²)/2` (`bdCircuit`).

**`bounded_gate_simulation`**: the circuit is valid, uses exactly `6d` private calls and `12d`
calls of `U_J` or `U_J†`, at most `200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3`
wires, `d ≤ 1536 (√σ θ + √(σθℓ) + ℓ)` with `ℓ = log(2/ε)`, and its full output is within `ε` of
`e^{-i θ√σ J₀†K₀J₀}`. `bounded_gate_simulation_neg` is the inverse circuit for the negative time.
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open CayleyClockInterface ImprovedCayleyMoments
open scoped InnerProduct InnerProductSpace BigOperators

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The Cayley transform of a self-adjoint generator -/

section Cayley

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- `K - i` is invertible for a self-adjoint `K` (finite dimension). -/
theorem isUnit_sub_I [FiniteDimensional ℂ V] {K : V →L[ℂ] V} (hK : star K = K) :
    IsUnit (K - Complex.I • (1 : V →L[ℂ] V)) := by
  have hsym : (K : V →ₗ[ℂ] V).IsSymmetric := IsSelfAdjoint.isSymmetric hK
  have hG : ∀ x, 0 ≤ (⟪x, (Complex.I • K) x⟫_ℂ).re := by
    intro x
    rw [smul_apply, inner_smul_right, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
      one_mul, zero_sub]
    have := hsym.im_inner_self_apply x
    simp only [RCLike.im_to_complex] at this
    have h' : (⟪x, K x⟫_ℂ).im = 0 := this
    rw [h', neg_zero]
  have hu := SignedFactorSimulation.isUnit_one_add_smul (Complex.I • K) hG (t := 1) zero_le_one
  have e : K - Complex.I • (1 : V →L[ℂ] V) =
      (-Complex.I) • (1 + ((1 : ℝ) : ℂ) • (Complex.I • K)) := by
    rw [Complex.ofReal_one, one_smul, smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg,
      one_smul, neg_smul]
    abel
  rw [e]
  have hc : IsUnit ((-Complex.I) • (1 : V →L[ℂ] V)) := by
    refine ⟨⟨(-Complex.I) • 1, Complex.I • 1, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, one_mul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    · rw [smul_mul_smul_comm, one_mul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  rw [show (-Complex.I) • (1 + ((1 : ℝ) : ℂ) • (Complex.I • K)) =
      ((-Complex.I) • (1 : V →L[ℂ] V)) * (1 + ((1 : ℝ) : ℂ) • (Complex.I • K)) by
    rw [smul_mul_assoc, one_mul]]
  exact hc.mul hu

/-- A left-unitary operator is unitary (finite dimension). -/
theorem isUnitary_of_star_mul_self [FiniteDimensional ℂ V] {U : V →L[ℂ] V}
    (h : star U * U = 1) : IsUnitary U := by
  have hinj : Function.Injective U := by
    intro x y hxy
    have := congrArg (fun v => (star U) v) hxy
    rwa [← mul_apply_eq_comp, ← mul_apply_eq_comp, h, one_apply_eq_self, one_apply_eq_self] at this
  have hbij : Function.Bijective U :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (U : V →ₗ[ℂ] V))).mp hinj⟩
  obtain ⟨u, hu⟩ := (ContinuousLinearMap.isUnit_iff_bijective).mpr hbij
  refine ⟨h, ?_⟩
  have h1 : star U = (u⁻¹ : (V →L[ℂ] V)ˣ) := by
    have h2 : (U * ((u⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V)) = 1 := by rw [← hu]; exact u.mul_inv
    calc star U = star U * (U * ((u⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V)) := by rw [h2, mul_one]
      _ = (star U * U) * ((u⁻¹ : (V →L[ℂ] V)ˣ) : V →L[ℂ] V) := by rw [mul_assoc]
      _ = _ := by rw [h, one_mul]
  rw [h1, ← hu]
  exact u.mul_inv

/-- The inverse of the Cayley denominator `K - i`. -/
def cayleyInv (K : V →L[ℂ] V) : V →L[ℂ] V := Ring.inverse (K - Complex.I • (1 : V →L[ℂ] V))

theorem cayleyInv_right [FiniteDimensional ℂ V] {K : V →L[ℂ] V} (hK : star K = K) :
    (K - Complex.I • (1 : V →L[ℂ] V)) * cayleyInv K = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_sub_I hK)

theorem cayleyInv_left [FiniteDimensional ℂ V] {K : V →L[ℂ] V} (hK : star K = K) :
    cayleyInv K * (K - Complex.I • (1 : V →L[ℂ] V)) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_sub_I hK)

/-- **The Cayley transform** `(K + i)(K - i)⁻¹` of a generator. -/
def cayleyGate (K : V →L[ℂ] V) : V →L[ℂ] V := cayleyAction K (cayleyInv K)

theorem cayleyGate_isUnitary [FiniteDimensional ℂ V] {K : V →L[ℂ] V} (hK : star K = K) :
    IsUnitary (cayleyGate K) :=
  isUnitary_of_star_mul_self (cayleyAction_star_mul_self K _ hK (cayleyInv_right hK))

end Cayley

/-! ### The public rescaling and the circuit -/

/-- The conditions of the rescaling optimiser. -/
def bdOK (σ θ ε : ℝ) : Prop := 1 ≤ σ ∧ 0 ≤ θ ∧ 0 < ε ∧ ε ≤ 1

open Classical in
/-- **The public rescaling** `γ` of the baseline for the schedule `(σ, θ)`. -/
def bdGamma (σ θ ε : ℝ) : ℝ :=
  if h : bdOK σ θ ε then
    Classical.choose (ImprovedPrecisionBudget.exists_rescaling_for_precision σ θ ε h.1 h.2.1
      h.2.2.1 h.2.2.2)
  else 1

theorem bdGamma_spec {σ θ ε : ℝ} (h : bdOK σ θ ε) :
    0 < bdGamma σ θ ε ∧ bdGamma σ θ ε ≤ 1 ∧ 1 ≤ bdGamma σ θ ε * Real.sqrt σ ∧
      time σ θ (bdGamma σ θ ε) * moment (bdGamma σ θ ε) +
        width σ (bdGamma σ θ ε) * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape σ θ (ImprovedPrecisionBudget.targetLog ε) := by
  unfold bdGamma
  rw [dif_pos h]
  exact Classical.choose_spec (ImprovedPrecisionBudget.exists_rescaling_for_precision σ θ ε
    h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- The compressed time `τ = θ√σ/γ`. -/
abbrev bdTau (σ θ ε : ℝ) : ℝ := time σ θ (bdGamma σ θ ε)

/-- The clock width `Q = ⌈max(1, γ√σ)⌉`. -/
abbrev bdQ (σ θ ε : ℝ) : ℝ := width σ (bdGamma σ θ ε)

/-- The boundary budget `qbar = (1 + γ²)/2`. -/
abbrev bdQbar (σ θ ε : ℝ) : ℝ := moment (bdGamma σ θ ε)

/-- **The bounded-regime gate circuit**: the released baseline circuit for the rescaled schedule.
-/
def bdCircuit (a : ℕ) (σ θ ε : ℝ) :
    List (Instr (SimWire a (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε)) :=
  simCircuit a (bdTau σ θ ε) (bdQ σ θ ε) (bdQbar σ θ ε) ε

/-- The private operation of the bounded regime: the Cayley transform of `γK₀`. -/
abbrev bdPriv {a : ℕ} (K₀ : Anc a P →L[ℂ] Anc a P) (σ θ ε : ℝ) : Anc a P →L[ℂ] Anc a P :=
  cayleyGate (scaled K₀ (bdGamma σ θ ε))

/-! ### The theorem -/

/-- **The bounded-logarithm regime, exact gates.** See the module docstring. -/
theorem bounded_gate_simulation [FiniteDimensional ℂ P] (a : ℕ) (UJ K₀ : Anc a P →L[ℂ] Anc a P)
    (hUJ : IsUnitary UJ) (hSelf : star K₀ = K₀) {σ θ ε : ℝ} (hσ : 1 ≤ σ)
    (hK : ‖K₀‖ ≤ Real.sqrt σ) (hKJ : ‖K₀ ∘L (UJ ∘L iota0)‖ ≤ 1) (hθ : 0 ≤ θ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    (∀ g ∈ bdCircuit a σ θ ε, g.Valid Wire.anc) ∧
    nPriv (bdCircuit a σ θ ε) = 6 * fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε ∧
    nUJ (bdCircuit a σ θ ε) = 12 * fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε ∧
    nGates (bdCircuit a σ θ ε) ≤
      200 * (fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε + 1) *
        (a + simM (bdTau σ θ ε) ε + simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε + 1) ∧
    Fintype.card (SimWire a (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε) =
      2 * a + 3 * simM (bdTau σ θ ε) ε + 6 * simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε + 3 ∧
    ‖run (simSem UJ (bdPriv K₀ σ θ ε)) (bdCircuit a σ θ ε) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * ((θ * Real.sqrt σ : ℝ) : ℂ)) •
          ((UJ ∘L iota0)† ∘L K₀ ∘L (UJ ∘L iota0)))‖ ≤ ε ∧
    (fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε : ℝ) ≤
      1536 * ImprovedPrecisionBudget.shape σ θ (ImprovedPrecisionBudget.targetLog ε) ∧
    TimeSchedule.steps (bdTau σ θ ε) (ε / 3) ≤ 2 ^ simM (bdTau σ θ ε) ε ∧
    2 ^ simM (bdTau σ θ ε) ε < 2 * TimeSchedule.steps (bdTau σ θ ε) (ε / 3) ∧
    2 * fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε + 2 ≤
      2 ^ simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε ∧
    2 ^ simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε ≤
      4 * (fDeg (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε + 1) := by
  have hok : bdOK σ θ ε := ⟨hσ, hθ, hε, hε1⟩
  obtain ⟨hγ, hγ1, -, hBudget⟩ := bdGamma_spec hok
  have hJ : (UJ ∘L iota0 (a := a) (P := P))† ∘L (UJ ∘L iota0) = 1 :=
    isometry_comp UJ iota0 (unitary_adj_comp hUJ) iota0_isometry
  have hSs : star (scaled K₀ (bdGamma σ θ ε)) = scaled K₀ (bdGamma σ θ ε) :=
    scaled_self_adjoint K₀ _ hSelf
  have hRr := cayleyInv_right hSs
  have hRl := cayleyInv_left hSs
  have hDu : IsUnitary (bdPriv K₀ σ θ ε) := cayleyGate_isUnitary hSs
  have hτ : 0 ≤ bdTau σ θ ε := div_nonneg (mul_nonneg hθ (Real.sqrt_nonneg _)) hγ.le
  have hRight : (1 - bdPriv K₀ σ θ ε) ∘L resolventAtOne (scaled K₀ (bdGamma σ θ ε)) = 1 :=
    one_sub_cayleyAction_mul_resolventAtOne _ _ hRr hRl
  have hLeft : resolventAtOne (scaled K₀ (bdGamma σ θ ε)) ∘L (1 - bdPriv K₀ σ θ ε) = 1 :=
    resolventAtOne_mul_one_sub_cayleyAction _ _ hRr
  obtain ⟨hv, h1, h2, h3, h4, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
    gate_efficient_simulation (P := P) a UJ (bdPriv K₀ σ θ ε)
      (resolventAtOne (scaled K₀ (bdGamma σ θ ε))) (compressed K₀ (UJ ∘L iota0) (bdGamma σ θ ε))
      hUJ hDu (bdTau σ θ ε) (bdQ σ θ ε) (endpoint (bdGamma σ θ ε)) (bdQbar σ θ ε) ε hτ
      (width_ge_one σ _) hRight hLeft (resolvent_norm K₀ σ _ hγ.le hK)
      (resolventAtOne_compression _ _ hJ) (compressed_self_adjoint K₀ _ _ hSelf)
      ((compressed_norm K₀ _ _ hγ.le hJ hKJ).trans hγ1) (endpoint_norm K₀ _ _ hSelf hJ hγ.le hKJ)
      (endpoint_sq _).le (moment_le_width σ _ hγ.le hγ1) hε hε1
  unfold bdCircuit
  refine ⟨hv, h1, h2, h3, h4, ?_, ?_, hm1, hm2, hr1, hr2⟩
  · rw [rescaled_exponent K₀ (UJ ∘L iota0) σ θ (bdGamma σ θ ε) hγ.ne'] at herr
    exact herr
  · have hlog : (1 : ℝ) + Real.log (1 / (ε / 3)) = ImprovedPrecisionBudget.circuitLog ε := by
      rw [ImprovedPrecisionBudget.circuitLog, one_div, inv_div]
    rw [hlog] at hdeg
    linarith

/-- **The bounded-logarithm regime for every real time**: the circuit for `|θ|`-schedule and its
literal inverse. With `θ ≥ 0` the compressed time; for a negative physical time the inverse
circuit simulates `e^{+i θ√σ J₀†K₀J₀}`. -/
theorem bounded_gate_simulation_neg [FiniteDimensional ℂ P] (a : ℕ)
    (UJ K₀ : Anc a P →L[ℂ] Anc a P) (hUJ : IsUnitary UJ) (hSelf : star K₀ = K₀) {σ θ ε : ℝ}
    (hσ : 1 ≤ σ) (hK : ‖K₀‖ ≤ Real.sqrt σ) (hKJ : ‖K₀ ∘L (UJ ∘L iota0)‖ ≤ 1) (hθ : 0 < θ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ‖run (simSem UJ (bdPriv K₀ σ θ ε)) (invList (bdCircuit a σ θ ε)) ∘L io -
        io ∘L NormedSpace.exp ((-Complex.I * ((-(θ * Real.sqrt σ) : ℝ) : ℂ)) •
          ((UJ ∘L iota0)† ∘L K₀ ∘L (UJ ∘L iota0)))‖ ≤ ε := by
  obtain ⟨hv, -, -, -, -, herr, -⟩ :=
    bounded_gate_simulation a UJ K₀ hUJ hSelf hσ hK hKJ hθ.le hε hε1
  have hok : bdOK σ θ ε := ⟨hσ, hθ.le, hε, hε1⟩
  have hSs : star (scaled K₀ (bdGamma σ θ ε)) = scaled K₀ (bdGamma σ θ ε) :=
    scaled_self_adjoint K₀ _ hSelf
  have hDu : IsUnitary (bdPriv K₀ σ θ ε) := cayleyGate_isUnitary hSs
  have hJself : star ((UJ ∘L iota0)† ∘L K₀ ∘L (UJ ∘L iota0)) =
      (UJ ∘L iota0)† ∘L K₀ ∘L (UJ ∘L iota0) := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_comp, adjoint_comp, adjoint_adjoint,
      ← star_eq_adjoint K₀, hSelf, comp_assoc]
  have hCu : IsUnitary (run (simSem (m := simM (bdTau σ θ ε) ε)
      (r := simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε)
      (K := simK a (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε) UJ (bdPriv K₀ σ θ ε))
      (bdCircuit a σ θ ε)) :=
    run_isUnitary (simSem (m := simM (bdTau σ θ ε) ε)
      (r := simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε)
      (K := simK a (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε) UJ (bdPriv K₀ σ θ ε)) hUJ hDu _ hv
  have hpos : 0 < θ * Real.sqrt σ := mul_pos hθ (Real.sqrt_pos.mpr (by linarith))
  rw [run_invList]
  generalize run (simSem (m := simM (bdTau σ θ ε) ε)
      (r := simR (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε)
      (K := simK a (bdQ σ θ ε) (bdTau σ θ ε) (bdQbar σ θ ε) ε) UJ (bdPriv K₀ σ θ ε))
    (bdCircuit a σ θ ε) = C at hCu herr ⊢
  refine err_inverse C hCu _ _ hJself (-(θ * Real.sqrt σ)) ε (by linarith) ?_
  rw [abs_neg, abs_of_pos hpos]
  exact herr

end

end GateOptimalPrecision


