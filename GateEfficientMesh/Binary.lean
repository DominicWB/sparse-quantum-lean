import GateEfficientMesh.Native
import GateEfficientBinaryTime.Budget

/-!
# Binary sparse data: integrated certificates

The time-dependent part of Theorem `hs:thm:gates` from time-indexed binary sparse oracles is
released for Lipschitz paths (`GateBinary.binary_time_simulation`, budget form
`GateBinary.binary_time_simulation_budget`). The released proof discharges every
implementation hypothesis of the native theorem (the slot-selected native identity
`sparse_nativeOK_time`, the CORDIC arithmetic `cordicArith_ok`, the Hadamard `U_J` and the clock
promises of every sample) and then applies `GateNative.native_time_simulation`. Here the same
public lemmas discharge the hypotheses of `native_slot_bounds`, which gives the error against
the ordered product of the slot exponentials of the lifted samples (`binary_slot_bounds`); the
integrated certificate on the matrix path then bounds the distance to every propagator of the
lifted path.

* `intervalIntegrable_map`, `integral_map_le`: a contractive linear map of operators preserves
  interval integrability and does not increase integrated norms.
* `lifted_sample`: the lifted sample is `(√s/γ) Hbin`, self-adjoint, of norm at most `√s/γ`.
* `intervalIntegrable_qlift`, `lifted_integral_le`: the qubit lift (the released algebra
  homomorphism `qliftHom`, contractive by `norm_qlift_le`) preserves interval integrability and
  does not increase the certificate.
* `binary_slot_bounds`: the released circuit `binaryTimeSim` with its counts, and the error
  `3ε/4 + ‖∏_r exp(-i (t/2^m) Ĥ_r) - U‖` against every operator `U`;
  `binary_slot_error_integral`, `binary_slot_error_piecewise`: the distance of the ordered
  product of the lifted slot exponentials from every integral-sense and every classical
  piecewise propagator of the lifted path is at most the certificate on the matrix path.

The endpoints `binary_time_simulation_certified` and `binary_time_simulation_budget_certified`
are in `BinaryTheorem`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh

noncomputable section

open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateCircuit.Sim (iota0 fDeg simR io Wire)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Data Query)
open MeasureTheory Set
open TimeDependentExtensions (IsPiecewisePropagator)
open IntegrablePathSimulation.Propagator (IsPropagator)
open scoped InnerProduct BigOperators

/-! ### Contractive linear images of operator paths -/

section Generic

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- A contractive linear map of operators preserves interval integrability. -/
theorem intervalIntegrable_map (L : (E →L[ℂ] E) →ₗ[ℂ] (P →L[ℂ] P)) (hL : ∀ A, ‖L A‖ ≤ ‖A‖)
    {f : ℝ → E →L[ℂ] E} {a c : ℝ} (hf : IntervalIntegrable f volume a c) :
    IntervalIntegrable (fun u => L (f u)) volume a c :=
  ⟨(L.mkContinuous 1 (fun A => by rw [one_mul]; exact hL A)).integrable_comp hf.1,
    (L.mkContinuous 1 (fun A => by rw [one_mul]; exact hL A)).integrable_comp hf.2⟩

/-- A contractive linear map of operators does not increase integrated sample errors. -/
theorem integral_map_le (L : (E →L[ℂ] E) →ₗ[ℂ] (P →L[ℂ] P)) (hL : ∀ A, ‖L A‖ ≤ ‖A‖)
    {f : ℝ → E →L[ℂ] E} (A : E →L[ℂ] E) {a c : ℝ} (hac : a ≤ c)
    (hf : IntervalIntegrable f volume a c) :
    ∫ u in a..c, ‖L (f u) - L A‖ ≤ ∫ u in a..c, ‖f u - A‖ := by
  apply intervalIntegral.integral_mono_on hac
  · exact ((intervalIntegrable_map L hL hf).sub intervalIntegrable_const).norm
  · exact (hf.sub intervalIntegrable_const).norm
  · intro u _
    rw [← map_sub]
    exact hL _

end Generic

/-! ### Lifted samples and paths -/

section Lift

variable {Y n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The lifted sample.** For a Hermitian sample with row and column norms at most one, its
qubit lift is `(√s/γ) Hbin` (the normalisation `α = √s/γ` of the native theorem), self-adjoint,
of norm at most `√s/γ`. -/
theorem lifted_sample (D : Data Y n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (y : Y)
    (hH : (D.matrix y).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix y i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix y i j‖ ^ 2 ≤ 1) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix y)) =
        ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) • Hbin (R := R) D en y γ ∧
      star (qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix y))) =
        qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix y)) ∧
      ‖qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix y))‖ ≤
        Real.sqrt (s : ℝ) / γ := by
  have hs0 : 0 < s := D.slots_pos
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs0)
  have hα : 0 < Real.sqrt (s : ℝ) / γ := div_pos hsq hγ
  have hsmul : qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix y)) =
      ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) • Hbin (R := R) D en y γ := by
    rw [Hbin_eq_smul D en y hH γ hγ.ne' hs0, smul_smul]
    have hc : ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) * ((γ / Real.sqrt (s : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, div_mul_div_comm, mul_comm (Real.sqrt (s : ℝ)) γ,
        div_self (mul_pos hγ hsq).ne', Complex.ofReal_one]
    rw [hc, one_smul]
  refine ⟨hsmul, ?_, ?_⟩
  · rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ hH]
  · rw [hsmul]
    have h1 := norm_Hbin_le (R := R) D en y γ hγ.le hγ1 hrow hcol
    calc ‖((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) • Hbin (R := R) D en y γ‖
        ≤ ‖((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ)‖ * ‖Hbin (R := R) D en y γ‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ Real.sqrt (s : ℝ) / γ * 1 := by
          rw [Complex.norm_real, Real.norm_of_nonneg hα.le]
          exact mul_le_mul_of_nonneg_left h1 hα.le
      _ = Real.sqrt (s : ℝ) / γ := mul_one _

/-- The lift of an interval-integrable operator path is interval integrable. -/
theorem intervalIntegrable_qlift (en : Cfg (Fin k) ≃ n)
    {f : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {a c : ℝ}
    (hf : IntervalIntegrable f volume a c) :
    IntervalIntegrable (fun u => qlift (R := R) en (f u)) volume a c :=
  intervalIntegrable_map (P := Reg (Fin k) R) (qliftHom (R := R) en).toAlgHom.toLinearMap
    (fun A => norm_qlift_le en A) hf

/-- The certificate of the lifted path is at most that of the path. -/
theorem lifted_integral_le (en : Cfg (Fin k) ≃ n)
    {f : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) {a c : ℝ} (hac : a ≤ c)
    (hf : IntervalIntegrable f volume a c) :
    ∫ u in a..c, ‖qlift (R := R) en (f u) - qlift (R := R) en A‖ ≤ ∫ u in a..c, ‖f u - A‖ :=
  integral_map_le (P := Reg (Fin k) R) (qliftHom (R := R) en).toAlgHom.toLinearMap
    (fun A => norm_qlift_le en A) A hac hf

end Lift

/-! ### The binary slot circuit -/

section Slot

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The binary slot circuit: counts and the error against any operator.** For time-indexed
binary sparse data in the released format (`k`-bit indices, `s = 2^σ` slots on the lowest
`σ` index bits, entries `c₀ (X + i Y)` with `b`-bit two's complement components) and an input
whose samples `H̃_r = D.matrix (x, r)` are Hermitian with row and column norms at most one, the
circuit `binaryTimeSim` (the native slot circuit with `U_J` from Hadamard gates, the
time-indexed compute circuit and the CORDIC arithmetic) has the released validity, call, gate
and qubit counts under the subdivision condition `steps τ' (ε/12) ≤ 2^m` (`τ' = √s t/γ`) and the
arithmetic budget `48 d ζ ≤ ε`, and its full output is within
`3ε/4 + ‖∏_r exp(-i (t/2^m) Ĥ_r) - U‖` of every operator `U`, where `Ĥ_r` is the lifted
sample (`HsT`). -/
theorem binary_slot_bounds (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    (hrow : ∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (hcol : ∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (t γ ε ζ : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hCayley : TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binaryTimeSim k b m σ hσ s γ c0 t ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) =
      12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
        (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) *
          (k + 1 + m + simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) *
          (2 * (28 * k) + 2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
              (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (Wire (k + 1) m
        (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4))
        (k + 1 + m + 2 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4)))
        (Fin k) Empty (SZ k b) (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A) =
      k + (2 * (k + 1) + 3 * m +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 3) +
        (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
          (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) ∧
    (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) ≤
      128 * (time (s : ℝ) t γ * moment γ + width (s : ℝ) γ * (1 + Real.log (12 / ε))) ∧
    2 * fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 2 ≤
      2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) ∧
    2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) ≤
      4 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) ∧
    ∀ U : Reg (Fin k) R →L[ℂ] Reg (Fin k) R,
      ‖nrun (primsT (R := R) D en x) (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ∘L
          sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U‖ ≤
        3 * ε / 4 + ‖slotEvolution (HsT (R := R) D en x) t m - U‖ := by
  have hs0 : 0 < s := by
    rw [hs]
    exact Nat.two_pow_pos σ
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs0)
  have hκ : 0 < γ * Real.sqrt s * c0 := by positivity
  obtain ⟨k0, hk0⟩ : ∃ q, D.slot q = zIdx en := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  have hxy : Function.Injective (Sum.elim (valXT k b m) (valYT k b m)) := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j <;> simp_all [valXT, valYT]
  have ho : ∀ i, Sum.elim (valXT k b m) (valYT k b m) i ≠
      Sum.inl (Sum.inr (sparseOpT k b m (γ * Real.sqrt s * c0)).o) := by
    intro i
    rcases i with i | i <;> simp [valXT, valYT]
  have har := cordicArith_ok b hb (valXT k b m) (valYT k b m) hxy _ ho _ ζ hκ hζ hζ1
  have hα : 0 < Real.sqrt (s : ℝ) / γ := div_pos hsq hγ
  have hαt : Real.sqrt (s : ℝ) / γ * t = time (s : ℝ) t γ := by
    unfold time
    ring
  have hfam : (fun w : Cfg (Fin m) => DbinT (R := R) D en x γ (wordEquivFin m w)) =
      fun w => unconj (qlift (R := R) (phiPR en)
        (FixedNativeCayleySimulation.action D (x, wordEquivFin m w) γ)) :=
    funext (fun w => DbinT_word D en x γ w)
  have hN : NativeOK (primsT (R := R) D en x) (sparseOpT k b m (γ * Real.sqrt s * c0))
      (selOp (fun w : Cfg (Fin m) => DbinT (R := R) D en x γ (wordEquivFin m w))) := by
    rw [hfam]
    exact sparse_nativeOK_time D en k0 hk0 c0 hdec x γ
  have hD : ∀ r < 2 ^ m, IsUnitary (DbinT (R := R) D en x γ r) := by
    intro r hr
    rw [DbinT, dif_pos hr]
    exact Dbin_isUnitary D en _ γ
  have hRight : ∀ r < 2 ^ m,
      (1 - DbinT (R := R) D en x γ r) ∘L R1binT (R := R) D en x γ r = 1 := by
    intro r hr
    rw [DbinT, R1binT, dif_pos hr, dif_pos hr]
    exact one_sub_Dbin_R1bin D en _ γ
  have hLeft : ∀ r < 2 ^ m,
      R1binT (R := R) D en x γ r ∘L (1 - DbinT (R := R) D en x γ r) = 1 := by
    intro r hr
    rw [DbinT, R1binT, dif_pos hr, dif_pos hr]
    exact R1bin_one_sub_Dbin D en _ γ
  have hR1 : ∀ r < 2 ^ m, ‖R1binT (R := R) D en x γ r‖ ≤ width (s : ℝ) γ := by
    intro r hr
    rw [R1binT, dif_pos hr]
    exact norm_R1bin_le D en _ γ hγ.le (hrow _)
  have hlift : ∀ r (hr : r < 2 ^ m), HsT (R := R) D en x r =
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix (x, ⟨r, hr⟩))) := by
    intro r hr
    rw [HsT, dif_pos hr]
  have hBoundary : ∀ r < 2 ^ m,
      (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
          R1binT (R := R) D en x γ r ∘L
            (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I •
          (((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ)⁻¹ • HsT (R := R) D en x r)) := by
    intro r hr
    have hne : ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    rw [R1binT, dif_pos hr, R1bin_boundary D en σ hσ hs hrange _ γ, hlift r hr,
      (lifted_sample D en _ (hHerm _) (hrow _) (hcol _) γ hγ hγ1).1, inv_smul_smul₀ hne]
  have hEndpoint : ∀ r < 2 ^ m, ‖R1binT (R := R) D en x γ r ∘L
      (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))‖ ≤
        endpoint γ := by
    intro r hr
    rw [R1binT, dif_pos hr]
    exact R1bin_endpoint D en σ hσ hs hrange _ γ hγ.le (hrow _) (hcol _)
  have hSelf : ∀ r < 2 ^ m, star (HsT (R := R) D en x r) = HsT (R := R) D en x r := by
    intro r hr
    rw [hlift r hr]
    exact (lifted_sample D en _ (hHerm _) (hrow _) (hcol _) γ hγ hγ1).2.1
  have hHs : ∀ r < 2 ^ m, ‖HsT (R := R) D en x r‖ ≤ Real.sqrt (s : ℝ) / γ := by
    intro r hr
    rw [hlift r hr]
    exact (lifted_sample D en _ (hHerm _) (hrow _) (hcol _) γ hγ hγ1).2.2
  obtain ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, herr⟩ :=
    native_slot_bounds (S := Fin k) (k + 1) m (primsT (R := R) D en x)
      (primsT_isUnitary D en x) (hadUJ k σ hσ) (hadUJ_ok σ hσ)
      (sparseOpT k b m (γ * Real.sqrt s * c0)) (sparseOpT_public k b m _)
      (binArithT k b m (γ * Real.sqrt s * c0) ζ) ζ hζ.le har
      (DbinT (R := R) D en x γ) (R1binT (R := R) D en x γ) hN (HsT (R := R) D en x) t
      (Real.sqrt (s : ℝ) / γ) (width (s : ℝ) γ) (endpoint γ) (moment γ) ε ht hα
      (width_ge_one _ _) (moment_le_width _ γ hγ.le hγ1) hε hε1
      (by rw [hαt]; exact hCayley) hD hRight hLeft hR1 hBoundary hEndpoint
      (endpoint_sq γ).le hSelf hHs (by rw [hαt]; exact hζε)
  rw [hαt] at hvalid hcalls hgates hcard hdeg hr1 hr2 herr
  have hV : (sparseOpT k b m (γ * Real.sqrt s * c0)).V = computeVT k b m := rfl
  rw [hV, computeVT_nGates, hadUJ_length] at hgates
  simp only [hV, computeVT_nCalls] at hcalls
  rw [card_SZ, Fintype.card_fin] at hcard
  unfold binaryTimeSim
  exact ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, herr⟩

/-- **The certificate of a matrix path bounds the distance of every propagator of its lift from
the slot product of the lifted samples** (integral-sense propagators). -/
theorem binary_slot_error_integral (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) (H : ℝ → Matrix n n ℂ) (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R)
    (hH : ∀ᵐ u, u ∈ Icc 0 t → (H u).IsHermitian)
    (hint : IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (H u)) volume 0 t)
    (hU : IsPropagator (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)))
      U t) :
    ‖U t - slotEvolution (HsT (R := R) D en x) t m‖ ≤
      ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
        ‖SparseStateOverlap.matrixOperator (H u) -
          SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ := by
  have hmesh := isMesh_slotMesh ht m
  have hlift : ∀ r (hr : r < 2 ^ m), HsT (R := R) D en x r =
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix (x, ⟨r, hr⟩))) := by
    intro r hr
    rw [HsT, dif_pos hr]
  have hH' : ∀ᵐ u, u ∈ Icc 0 t →
      star (qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) =
        qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)) := by
    filter_upwards [hH] with u hu hmem
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ (hu hmem)]
  have hSelf : ∀ r < 2 ^ m, star (HsT (R := R) D en x r) = HsT (R := R) D en x r := by
    intro r hr
    rw [hlift r hr, ← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ (hHerm _)]
  have h := slot_error_integral (HsT (R := R) D en x) ht m hU hH' hSelf
    (intervalIntegrable_qlift (R := R) en hint)
  refine h.trans (le_of_eq_of_le ?_ (Finset.sum_le_sum fun r _ => lifted_integral_le (R := R) en
    (SparseStateOverlap.matrixOperator (D.matrix (x, r))) (hmesh.mono (Nat.le_succ r))
    (hint.mono_set ?_)))
  · rw [← Fin.sum_univ_eq_sum_range (fun k => ∫ u in slotMesh t m k..slotMesh t m (k + 1),
      ‖qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)) - HsT (R := R) D en x k‖)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hlift r r.isLt]
  · rw [uIcc_of_le (hmesh.mono (Nat.le_succ r)), uIcc_of_le ht]
    exact Icc_subset_Icc (hmesh.nonneg r) (hmesh.le_last (by omega))

/-- The same for classical piecewise propagators of matrix paths with one piece per slot. -/
theorem binary_slot_error_piecewise (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    {t : ℝ} (ht : 0 ≤ t) (Hp : ℕ → ℝ → Matrix n n ℂ)
    (U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R)
    (hH : ∀ r < 2 ^ m, ∀ u ∈ Icc (slotMesh t m r) (slotMesh t m (r + 1)), (Hp r u).IsHermitian)
    (hint : ∀ r < 2 ^ m, IntervalIntegrable (fun u => SparseStateOverlap.matrixOperator (Hp r u))
      volume (slotMesh t m r) (slotMesh t m (r + 1)))
    (hU : IsPiecewisePropagator
      (fun r u => qlift (R := R) en (SparseStateOverlap.matrixOperator (Hp r u)))
      (slotMesh t m) (2 ^ m) U) :
    ‖U t - slotEvolution (HsT (R := R) D en x) t m‖ ≤
      ∑ r : Fin (2 ^ m), ∫ u in slotMesh t m r..slotMesh t m ((r : ℕ) + 1),
        ‖SparseStateOverlap.matrixOperator (Hp r u) -
          SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ := by
  have hmesh := isMesh_slotMesh ht m
  have hlift : ∀ r (hr : r < 2 ^ m), HsT (R := R) D en x r =
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix (x, ⟨r, hr⟩))) := by
    intro r hr
    rw [HsT, dif_pos hr]
  have hSelf : ∀ r < 2 ^ m, star (HsT (R := R) D en x r) = HsT (R := R) D en x r := by
    intro r hr
    rw [hlift r hr, ← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ (hHerm _)]
  have h := slot_error_piecewise (HsT (R := R) D en x) ht m hU
    (fun r hr u hu => by
      rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ (hH r hr u hu)])
    hSelf (fun r hr => intervalIntegrable_qlift (R := R) en (hint r hr))
  refine h.trans (le_of_eq_of_le ?_ (Finset.sum_le_sum fun r _ => lifted_integral_le (R := R) en
    (SparseStateOverlap.matrixOperator (D.matrix (x, r))) (hmesh.mono (Nat.le_succ r))
    (hint r r.isLt)))
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∫ u in slotMesh t m k..slotMesh t m (k + 1),
    ‖qlift (R := R) en (SparseStateOverlap.matrixOperator (Hp k u)) - HsT (R := R) D en x k‖)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [hlift r r.isLt]

end Slot

end

end SparseHamiltonian.GateMesh
