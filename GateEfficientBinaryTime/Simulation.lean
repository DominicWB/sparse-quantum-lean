import GateEfficientBinaryTime.Oracles
import GateEfficientBinary.Sparse.Simulation
import SparseHamiltonian.SparseValuePrecision

/-!
# Native gate-efficient time-dependent sparse simulation from binary data

This file instantiates the native time-dependent gate-level simulation theorem
(`GateNative.native_time_simulation`, the time-dependent gate-level simulation (Theorem
`hs:thm:time` with the circuit of `hs:thm:gates`), before finite-set synthesis) for time-indexed
binary sparse oracles (`Oracles`): the sample of slot `r` on input `x` is the matrix
`D.matrix (x, r)` of the released native sparse data `D : Data (X × Fin (2^m)) n (Cfg (VW b)) s`,
with `k`-bit indices, entries stored as two `b`-bit two's complement components with a public scale
`c₀`, and `s = 2^σ` slots that are the index words supported on the lowest `σ` bits. Every
hypothesis of the native theorem about the implementations is discharged:

* `U_J`: Hadamard gates (`hadUJ`, as in the time-independent case);
* the slot-selected native private operation: the time-indexed compute circuit and the decoder
  `γ √s c₀ (X + i Y)` (`sparseOpT`), with its native identity (`sparse_nativeOK_time`);
* the reversible arithmetic: the CORDIC circuit on the value wires (`binArithT`);
* the clock promises at every slot: those of the time-independent case for the sample of the
  slot, with the normalisation `α = √s/γ` (`compressed_eq_smul`).

The remaining hypotheses are those of the theorem: a Hermitian, `β`-Lipschitz matrix path `H`,
sample errors at most `δ`, the mesh conditions and the error budgets.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateCircuit.Sim (iota0 fDeg simR SimWire io Wire)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GatePointerEncoding (wordEquivFin)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The compressed generator is the rescaled matrix -/

section Compressed

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The compressed sparse generator at rescaling `γ` is `(γ/√s) H`. -/
theorem compressed_eq_smul (D : Data X n Z s) (y : X) (hH : (D.matrix y).IsHermitian) (γ : ℝ)
    (hγ : γ ≠ 0) (hs : 0 < s) :
    compressed (FixedNativeCayleySimulation.generator D y)
        (FixedNativeCayleySimulation.boundary D) γ =
      ((γ / Real.sqrt s : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix y) := by
  have h := FixedNativeCayleySimulation.physical_exponent D y hH 1 γ hγ
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs)
  have hsC : ((Real.sqrt (s : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
  have hγC : ((γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hγ
  have hT : ((time (s : ℝ) 1 γ : ℝ) : ℂ) ≠ 0 := by
    unfold time
    push_cast
    exact div_ne_zero (by rw [one_mul]; exact hsC) hγC
  have hc : (-Complex.I * ((time (s : ℝ) 1 γ : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) hT
  have h2 := congrArg (fun A => (-Complex.I * ((time (s : ℝ) 1 γ : ℝ) : ℂ))⁻¹ • A) h
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
  rw [h2]
  congr 1
  unfold time
  push_cast
  field_simp

end Compressed

/-! ### The slot families -/

section Families

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The compressed generator of a sample is the rescaled lifted sample. -/
theorem Hbin_eq_smul (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (y : X)
    (hH : (D.matrix y).IsHermitian) (γ : ℝ) (hγ : γ ≠ 0) (hs : 0 < s) :
    Hbin (R := R) D en y γ = ((γ / Real.sqrt s : ℝ) : ℂ) •
      qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix y)) := by
  rw [Hbin, compressed_eq_smul D y hH γ hγ hs, qlift_smul]

/-- The private operation of time slot `r` (the identity beyond the last slot). -/
def DbinT (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ)
    (r : ℕ) : Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R) :=
  if h : r < 2 ^ m then Dbin D en (x, ⟨r, h⟩) γ else 1

/-- The resolvent at one of time slot `r` (the identity beyond the last slot). -/
def R1binT (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ)
    (r : ℕ) : Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R) :=
  if h : r < 2 ^ m then R1bin D en (x, ⟨r, h⟩) γ else 1

/-- The lifted sample Hamiltonian of time slot `r` on the system qubits (zero beyond the last
slot). -/
def HsT (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (r : ℕ) :
    Reg (Fin k) R →L[ℂ] Reg (Fin k) R :=
  if h : r < 2 ^ m then qlift en (SparseStateOverlap.matrixOperator (D.matrix (x, ⟨r, h⟩)))
  else 0

theorem DbinT_word (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (γ : ℝ) (w : Cfg (Fin m)) :
    DbinT (R := R) D en x γ (wordEquivFin m w) = Dbin D en (x, wordEquivFin m w) γ := by
  rw [DbinT, dif_pos (wordEquivFin m w).isLt]

end Families

/-! ### The theorem -/

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b m : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The CORDIC arithmetic of the slot-selected private operation, for the decoder scale `κ`. -/
def binArithT (k b m : ℕ) (κ ζ : ℝ) : Arith (NB (Fin m) (PR k) (SZ k b)) :=
  cordicArith b (valXT k b m) (valYT k b m) κ ζ

/-- **The native time-dependent circuit from binary data**: the native slot circuit with `2^m`
time slots, `U_J` from Hadamard gates, the time-indexed compute circuit and the CORDIC
arithmetic, for the rescaling `γ`, the time `t`, the accuracy `ε` and the arithmetic accuracy
`ζ`. -/
def binaryTimeSim (k b m σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ) :=
  nativeSimT (S := Fin k) (k + 1) m (time (s : ℝ) t γ) (width (s : ℝ) γ) (moment γ) ε
    (hadUJ k σ hσ) (sparseOpT k b m (γ * Real.sqrt s * c0))
    (binArithT k b m (γ * Real.sqrt s * c0) ζ)

/-- **Native gate-efficient time-dependent sparse simulation from binary data** (Theorem
`hs:thm:time` with the circuit of `hs:thm:gates`, for time-indexed binary sparse oracles, before
finite-set synthesis). Let the time-indexed native sparse data `D` have `k`-bit indices (`en`),
`s = 2^σ` slots that are exactly the index words supported on the lowest `σ ≤ k` bits (`hrange`),
and entries stored as two `b`-bit two's complement components `X`, `Y`, `b ≥ 1`, with decoder
`c₀ (X + i Y)`, `c₀ > 0` (`hdec`). Let the `2^m` samples `H̃_j = D.matrix (x, j)` of an input `x` be
Hermitian with row and column norms at most one, let `t ≥ 0`, and let `H` be a Hermitian path on
`[0, t]` that is `β`-Lipschitz in operator norm (`β ≥ 0`) and within `δ` of the samples at the slot
times `j t/2^m`. For a rescaling `0 < γ ≤ 1`, accuracies `0 < ε ≤ 1` and `0 < ζ ≤ 1`, the mesh
conditions `steps τ' (ε/12) ≤ 2^m` and `8 β t² ≤ ε 2^m` (`τ' = √s t/γ`), the sample-error budget
`8 t δ ≤ ε` and the arithmetic budget `48 d ζ ≤ ε` (`d` the filter degree), the circuit
`binaryTimeSim` consists of valid instructions; it makes `12 d` times `2` row-location, `2`
column-location and `1` value calls of the coherent sampled-time oracles; its elementary gates are
at most `200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d (56 k + 2 |circ| + 2 bP + bT + 1)` (`r` the size of
the phase registers; `|circ|`, `bP`, `bT` of the arithmetic); it has the stated qubit count;
`d ≤ 128 (τ' q̄ + Q (1 + log (12/ε)))` and `2d + 2 ≤ 2^r ≤ 4 (d+1)`; the propagator of the lifted
path exists, and the full output of the circuit on the system embedding is within `ε` of `U(t)` for
every propagator `U` of the lifted path `qlift en (H u)`. -/
theorem binary_time_simulation (D : Data (X × Fin (2 ^ m)) n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ q, D.slot q = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hHerm : ∀ r, (D.matrix (x, r)).IsHermitian)
    (hrow : ∀ r i, ∑ j, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (hcol : ∀ r j, ∑ i, ‖D.matrix (x, r) i j‖ ^ 2 ≤ 1)
    (H : ℝ → Matrix n n ℂ) (t β δ γ ε ζ : ℝ) (ht : 0 ≤ t) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hPath : ∀ u ∈ Set.Icc 0 t, (H u).IsHermitian)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t,
      ‖SparseStateOverlap.matrixOperator (H u) - SparseStateOverlap.matrixOperator (H v)‖ ≤
        β * |u - v|)
    (hVal : ∀ r : Fin (2 ^ m),
      ‖SparseStateOverlap.matrixOperator (H (((r : ℕ) : ℝ) * t / 2 ^ m)) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δ)
    (hValBudget : 8 * t * δ ≤ ε)
    (hCayley : TimeSchedule.steps (time (s : ℝ) t γ) (ε / 12) ≤ 2 ^ m)
    (hFreeze : 8 * β * t ^ 2 ≤ ε * 2 ^ m)
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
    (∃ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 ∧
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t) ∧
    ∀ U : ℝ → Reg (Fin k) R →L[ℂ] Reg (Fin k) R, U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) U 0 t →
      ‖nrun (primsT (R := R) D en x) (binaryTimeSim k b m σ hσ s γ c0 t ε ζ) ∘L
          sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L U t‖ ≤ ε := by
  have hs0 : 0 < s := by
    rw [hs]
    exact Nat.two_pow_pos σ
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
    rw [hs]
    exact_mod_cast Nat.one_le_two_pow
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by linarith)
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
  have hsmul : ∀ r (hr : r < 2 ^ m), HsT (R := R) D en x r =
      ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) • Hbin (R := R) D en (x, ⟨r, hr⟩) γ := by
    intro r hr
    rw [HsT, dif_pos hr, Hbin_eq_smul D en _ (hHerm _) γ hγ.ne' hs0, smul_smul]
    have hc : ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) * ((γ / Real.sqrt (s : ℝ) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, div_mul_div_comm, mul_comm (Real.sqrt (s : ℝ)) γ,
        div_self (mul_pos hγ hsq).ne', Complex.ofReal_one]
    rw [hc, one_smul]
  have hBoundary : ∀ r < 2 ^ m,
      (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
          R1binT (R := R) D en x γ r ∘L
            (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I •
          (((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ)⁻¹ • HsT (R := R) D en x r)) := by
    intro r hr
    have hne : ((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    rw [R1binT, dif_pos hr, R1bin_boundary D en σ hσ hs hrange _ γ, hsmul r hr,
      inv_smul_smul₀ hne]
  have hEndpoint : ∀ r < 2 ^ m, ‖R1binT (R := R) D en x γ r ∘L
      (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))‖ ≤
        endpoint γ := by
    intro r hr
    rw [R1binT, dif_pos hr]
    exact R1bin_endpoint D en σ hσ hs hrange _ γ hγ.le (hrow _) (hcol _)
  have hSelf : ∀ r < 2 ^ m, star (HsT (R := R) D en x r) = HsT (R := R) D en x r := by
    intro r hr
    rw [HsT, dif_pos hr, ← qlift_star,
      SparseValuePrecision.matrixOperator_star_eq _ (hHerm _)]
  have hHs : ∀ r < 2 ^ m, ‖HsT (R := R) D en x r‖ ≤ Real.sqrt (s : ℝ) / γ := by
    intro r hr
    rw [hsmul r hr]
    have h1 := norm_Hbin_le (R := R) D en (x, ⟨r, hr⟩) γ hγ.le hγ1 (hrow _) (hcol _)
    calc ‖((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ) • Hbin (R := R) D en (x, ⟨r, hr⟩) γ‖
        ≤ ‖((Real.sqrt (s : ℝ) / γ : ℝ) : ℂ)‖ * ‖Hbin (R := R) D en (x, ⟨r, hr⟩) γ‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ Real.sqrt (s : ℝ) / γ * 1 := by
          rw [Complex.norm_real, Real.norm_of_nonneg hα.le]
          exact mul_le_mul_of_nonneg_left h1 hα.le
      _ = Real.sqrt (s : ℝ) / γ := mul_one _
  have hPath' : ∀ u ∈ Set.Icc 0 t,
      star (qlift (R := R) en (SparseStateOverlap.matrixOperator (H u))) =
        qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)) := by
    intro u hu
    rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq _ (hPath u hu)]
  have hLip' : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t,
      ‖qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)) -
        qlift (R := R) en (SparseStateOverlap.matrixOperator (H v))‖ ≤ β * |u - v| := by
    intro u hu v hv
    rw [← qlift_sub]
    exact (norm_qlift_le _ _).trans (hLip u hu v hv)
  have hVal' : ∀ r : ℕ, r < 2 ^ m →
      ‖qlift (R := R) en (SparseStateOverlap.matrixOperator (H ((r : ℝ) * t / 2 ^ m))) -
        HsT (R := R) D en x r‖ ≤ δ := by
    intro r hr
    rw [HsT, dif_pos hr, ← qlift_sub]
    exact (norm_qlift_le _ _).trans (hVal ⟨r, hr⟩)
  obtain ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, hex, herr⟩ :=
    native_time_simulation (S := Fin k) (k + 1) m (primsT (R := R) D en x)
      (primsT_isUnitary D en x) (hadUJ k σ hσ) (hadUJ_ok σ hσ)
      (sparseOpT k b m (γ * Real.sqrt s * c0)) (sparseOpT_public k b m _)
      (binArithT k b m (γ * Real.sqrt s * c0) ζ) ζ hζ.le har
      (DbinT (R := R) D en x γ) (R1binT (R := R) D en x γ) hN
      (fun u => qlift (R := R) en (SparseStateOverlap.matrixOperator (H u)))
      (HsT (R := R) D en x) t (Real.sqrt (s : ℝ) / γ) β δ (width (s : ℝ) γ) (endpoint γ)
      (moment γ) ε ht hα hβ (width_ge_one _ _) (moment_le_width _ γ hγ.le hγ1) hε hε1
      (by rw [hαt]; exact hCayley) hFreeze hD hRight hLeft hR1 hBoundary hEndpoint
      (endpoint_sq γ).le hSelf hHs hPath' hLip' hVal' hValBudget (by rw [hαt]; exact hζε)
  rw [hαt] at hvalid hcalls hgates hcard hdeg hr1 hr2 herr
  have hV : (sparseOpT k b m (γ * Real.sqrt s * c0)).V = computeVT k b m := rfl
  rw [hV, computeVT_nGates, hadUJ_length] at hgates
  simp only [hV, computeVT_nCalls] at hcalls
  rw [card_SZ, Fintype.card_fin] at hcard
  unfold binaryTimeSim
  exact ⟨hvalid, hcalls, hgates, hcard, hdeg, hr1, hr2, hex, herr⟩

end Main

end

end SparseHamiltonian.GateBinary
