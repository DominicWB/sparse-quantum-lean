import GeneralDecoder.Native
import GateEfficientBinary.Sparse.Simulation

/-!
# Native gate-efficient sparse Hamiltonian simulation from binary data with a general decoder

`GateBinary.binary_simulation` instantiates the native gate-level simulation theorem
(`GateNative.native_simulation`) for binary sparse oracles with the decoder `c₀ (X + i Y)` and the
CORDIC arithmetic. `binary_simulationD` is the same instantiation for the public decoder of the
data (`Data.decode`, which may depend on the edge) and every reversible arithmetic `ar` of the
decoded entry `γ √s decode(e, w)` (`ArithOK`, the arithmetic hypothesis of the native theorem: the
angle words of `θ = 2 arctan |γ √s decode(e, w)|` and `φ = arg decode(e, w)` within `ζ`, work
restored). The counts are those of `binary_simulation` with the gates and wires of `ar` in place
of the CORDIC arithmetic.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.GateCircuit.Sim (iota0 fDeg simM simR SimWire io)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native circuit from binary sparse data with the decoder of the data**: the native
simulation circuit with `U_J` from Hadamard gates, the compute circuit of the binary oracles with
the decoder `γ √s decode` and the arithmetic `ar`, for the rescaling `γ`, the time `τ` and the
accuracy `ε`. -/
def binarySimD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ) (hσ : σ ≤ k)
    (γ τ ε : ℝ) (ar : Arith (NB Empty (PR k) (SZ k b))) :=
  nativeSim (S := Fin k) (k + 1) (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε
    (hadUJ k σ hσ) (sparseOpD D en (γ * Real.sqrt s)) ar

/-- **Native gate-efficient sparse Hamiltonian simulation from binary data with the decoder of the
data** (Theorem `hs:thm:gates` before finite-set synthesis). As `GateBinary.binary_simulation`, for
any public decoder of the data and an arithmetic `ar` of the decoded entry `γ √s decode(e, w)` at
accuracy `ζ` (`har`): the circuit `binarySimD` consists of valid instructions;
it makes `12 d` times `2` row-location, `2` column-location and `1` value calls; its elementary
gates are at most `200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d (56 k + 2 |ar| + 2 bP + bT + 1)`; it
has the stated qubit count; its full output on the system embedding is within `ε` of `exp(-iτĤ)`
for the qubit lift `Ĥ` of the represented matrix; with the bounds of `native_simulation` on `d`
and the register sizes. -/
theorem binary_simulationD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ τ ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 ≤ ζ)
    (ar : Arith (NB Empty (PR k) (SZ k b)))
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((γ * Real.sqrt s : ℝ) : ℂ) * D.decode (phiE en (eword y)) (vword y)) ζ)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binarySimD D en σ hσ γ τ ε ar, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binarySimD D en σ hσ γ τ ε ar) =
      12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
        (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (binarySimD D en σ hσ γ τ ε ar) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) *
          (k + 1 + simM (time (s : ℝ) τ γ) (ε / 2) +
            simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
          (2 * (28 * k) + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2))
        (Fin k) Empty (SZ k b) ar.bT ar.bP ar.A) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + ar.bT + ar.bP + ar.A + 3) ∧
    ‖nrun (prims (R := R) D en x) (binarySimD D en σ hσ γ τ ε ar) ∘L
        sysEmb (io (P := Reg (Fin k) R)) - sysEmb (io (P := Reg (Fin k) R)) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ ε ∧
    (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) ≤
      128 * (time (s : ℝ) τ γ * moment γ + width (s : ℝ) γ * (1 + Real.log (6 / ε))) ∧
    TimeSchedule.steps (time (s : ℝ) τ γ) (ε / 6) ≤ 2 ^ simM (time (s : ℝ) τ γ) (ε / 2) ∧
    2 ^ simM (time (s : ℝ) τ γ) (ε / 2) < 2 * TimeSchedule.steps (time (s : ℝ) τ γ) (ε / 6) ∧
    2 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 2 ≤
      2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) ∧
    2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) ≤
      4 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) := by
  obtain ⟨k0, hk0⟩ : ∃ m, D.slot m = zIdx en := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  have hτ' : 0 ≤ time (s : ℝ) τ γ := div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) hγ.le
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
    native_simulation (k + 1) (prims (R := R) D en x) (prims_isUnitary D en x)
      (hadUJ k σ hσ) (hadUJ_ok σ hσ)
      (sparseOpD D en (γ * Real.sqrt s))
      (sparseOpD_public D en _) ar ζ hζ har
      (Dbin (R := R) D en x γ) (R1bin (R := R) D en x γ) (Hbin (R := R) D en x γ)
      (Dbin_isUnitary D en x γ) (sparse_nativeOKD D en k0 hk0 x γ)
      (time (s : ℝ) τ γ) (width (s : ℝ) γ) (endpoint γ) (moment γ) ε hτ' (width_ge_one _ _)
      (one_sub_Dbin_R1bin D en x γ) (R1bin_one_sub_Dbin D en x γ)
      (norm_R1bin_le D en x γ hγ.le hrow) (R1bin_boundary D en σ hσ hs hrange x γ)
      (Hbin_self D en x γ) (norm_Hbin_le D en x γ hγ.le hγ1 hrow hcol)
      (R1bin_endpoint D en σ hσ hs hrange x γ hγ.le hrow hcol) (endpoint_sq γ).le
      (moment_le_width _ γ hγ.le hγ1) hε hε1 hζε
  rw [sparseOpD_V, computeV_nGates, hadUJ_length] at hgates
  simp only [sparseOpD_V, computeV_nCalls] at hcalls
  rw [card_SZ, Fintype.card_fin] at hcard
  rw [Hbin_exponent D en x hH τ γ hγ.ne'] at herr
  unfold binarySimD
  exact ⟨hvalid, hcalls, hgates, hcard, herr, hdeg, hm1, hm2, hr1, hr2⟩

end

end SparseHamiltonian.GeneralDecoder
