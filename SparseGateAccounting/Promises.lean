import GateEfficientSchedule.Selective
import ManuscriptConformance.GateDecoderDefs

/-!
# Sparse access of general size on the manuscript's schedule: parameters and bridges

The data and the parameters of the explicit accounting of Theorem `hs:thm:gates`, for sparse access
of general size (`GeneralSparseAccess.QData`) with any public decoder:

* `normPad D η hη`: the padded data with the validity decoder (`QData.padDataE`: `k + 1`-bit index
  words, `s' = 2^⌈log₂ s⌉` slots, no zero word of the decoder needed), normalised by `η`; its
  primitive oracles are never called, only its Cayley operation is used as the ideal private
  operation;
* `padUJ D`: the Hadamard gates of `U_J` on `a = k + 2` ancillas and `k + 1` system qubits, with
  `C_J = ⌈log₂ s⌉ + 1` gates (`padUJ_length`);
* `clock s η t γ = η t √s' / γ`: the time `αT` of the schedule;
* `dg`, `rg`, `synG`: the degree `d`, the reuse register `r_reuse` and the count
  `G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J` of the gate occurrences to synthesise, with
  `G₀ ≤ 884 d (C_J + a + m + r)` (`synG_le`);
* `evolution_eq`: the rescaled exponent of the compressed generator is the exponent of the padded
  matrix; `error_low`: a bound on the padded register restricts to the clean marker.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.SparseGateAccounting

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateBinary
  GateSchedule GeneralSparseAccess CayleyClockInterface
open ManuscriptConformance (cleanAlong norm_cleanAlong)
open scoped InnerProduct

variable {X : Type*} {N s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The normalised padded data**: the padded data with the validity decoder divided by `η`. The
queried data are those of the padded data; the decoder is the validity decoder of `D.val` over
`η`. -/
abbrev normPad (D : QData X N s k b) (η : ℝ) (hη : 0 < η) :
    NativeSparseBlockEncoding.Data X (Cfg (Fin (k + 1))) (Cfg (VW b)) (sP s) :=
  NativeSparseRescaling.normalize D.padDataE η hη

/-- The padded slots fit the padded index register. -/
theorem sbP_le_succ (D : QData X N s k b) : sbP s ≤ k + 1 :=
  (sbP_le D.s_le_pow).trans (Nat.le_succ k)

/-- **`U_J` of the padded data**: Hadamard gates on the orientation wire and the lowest `⌈log₂ s⌉`
wires of the second index. -/
abbrev padUJ (D : QData X N s k b) : List (Gate (Fin (k + 1 + 1) ⊕ Fin (k + 1))) :=
  hadUJ (k + 1) (sbP s) (sbP_le_succ D)

/-- `C_J = ⌈log₂ s⌉ + 1`. -/
theorem padUJ_length (D : QData X N s k b) : (padUJ D).length = sbP s + 1 :=
  hadUJ_length _ _

/-- **The time `αT` of the schedule** at the signed time `t`: `η t √s' / γ`, with the padded slot
count `s' = 2^⌈log₂ s⌉`, `s ≤ s' < 2 s`. -/
abbrev clock (s : ℕ) (η t γ : ℝ) : ℝ := time ((sP s : ℕ) : ℝ) (η * t) γ

/-- The clock of `|t|` is the absolute value of the clock of `t`. -/
theorem abs_clock (s : ℕ) {η γ : ℝ} (hη : 0 < η) (hγ : 0 < γ) (t : ℝ) :
    |clock s η t γ| = clock s η |t| γ := by
  simp only [clock, time, abs_div, abs_mul, abs_of_pos hη, abs_of_pos hγ,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- The filter degree `d` of the schedule, for the clock budget `W = τ (1 + γ²)/2`. -/
abbrev dg (s : ℕ) (γ τ ε : ℝ) : ℕ := degreeMs (width ((sP s : ℕ) : ℝ) γ) (τ * moment γ) ε

/-- The reuse register `r_reuse = ⌈log₂(2d + 2)⌉` of the schedule. -/
abbrev rg (s : ℕ) (γ τ ε : ℝ) : ℕ := rMs (width ((sP s : ℕ) : ℝ) γ) τ (moment γ) ε

/-- **The gate occurrences to synthesise**: `G₀ = 200 (d+1)(a+m+r+1) + 84 d C_J`, for `a = k + 2`
and `C_J = ⌈log₂ s⌉ + 1`. -/
abbrev synG (k s : ℕ) (γ τ ε : ℝ) : ℕ :=
  200 * (dg s γ τ ε + 1) * (k + 1 + 1 + slotMs τ ε + rg s γ τ ε + 1) +
    84 * dg s γ τ ε * (sbP s + 1)

/-- The degree of the schedule is positive. -/
theorem dg_pos (s : ℕ) (γ : ℝ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ dg s γ τ ε := by
  have hQ := width_ge_one ((sP s : ℕ) : ℝ) γ
  have hm : 0 ≤ moment γ := by unfold moment; positivity
  have hk := (depthMs_admissible _ (τ * moment γ) ε hQ (mul_nonneg hτ hm) hε hε1).pos
  have hL := (SharpFilterSchedule.length_sub_one_bounds _ hQ).1
  have hL1 : 1 ≤ SharpFilterSchedule.length (width ((sP s : ℕ) : ℝ) γ) - 1 := by
    have : (1 : ℝ) ≤ ((SharpFilterSchedule.length (width ((sP s : ℕ) : ℝ) γ) - 1 : ℕ) : ℝ) :=
      hQ.trans hL
    exact_mod_cast this
  exact Nat.mul_pos hk hL1

/-- **The order of the known gates** (`hs:eq:gate-known`, and the known-gate term of
`hs:eq:gate-Gzero`): `G₀ ≤ 884 d (C_J + a + m + r)`. -/
theorem synG_le (k s : ℕ) (γ : ℝ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    synG k s γ τ ε ≤
      884 * (dg s γ τ ε * (sbP s + 1 + (k + 1 + 1) + slotMs τ ε + rg s γ τ ε)) := by
  have hd := dg_pos s γ hτ hε hε1
  simp only [synG]
  generalize dg s γ τ ε = d at hd ⊢
  generalize rg s γ τ ε = r
  generalize slotMs τ ε = m
  generalize sbP s = σ
  have h1 : d + 1 ≤ 2 * d := by omega
  have h2 : k + 1 + 1 + m + r + 1 ≤ 2 * (k + 1 + 1 + m + r) := by omega
  calc 200 * (d + 1) * (k + 1 + 1 + m + r + 1) + 84 * d * (σ + 1)
      ≤ 200 * (2 * d) * (2 * (k + 1 + 1 + m + r)) + 84 * d * (σ + 1) := by gcongr
    _ ≤ 884 * (d * (σ + 1 + (k + 1 + 1) + m + r)) := by
        nlinarith [Nat.zero_le (d * σ), Nat.zero_le d, Nat.zero_le (d * k), Nat.zero_le (d * m),
          Nat.zero_le (d * r)]

/-- **The exponent of the compressed generator is the exponent of the padded matrix**: the
rescalings `γ/√s'` and `1/η` cancel in the clock. -/
theorem evolution_eq (D : QData X N s k b) {η : ℝ} (hη : 0 < η) (x : X)
    (hH : ((normPad D η hη).matrix x).IsHermitian) (t : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    (-Complex.I * ((clock s η t γ : ℝ) : ℂ)) •
        Hbin (R := R) (normPad D η hη) (Equiv.refl _) x γ =
      (-Complex.I * (t : ℂ)) • qlift (R := R) (Equiv.refl _)
        (SparseStateOverlap.matrixOperator (D.padDataE.matrix x)) := by
  rw [clock, Hbin_exponent _ _ x hH (η * t) γ hγ.ne',
    NativeSparseRescaling.matrixOperator_normalize, qlift_smul, smul_smul]
  congr 1
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  push_cast
  field_simp

omit [CompleteSpace R] in
/-- **Restriction to the clean marker**: composing with the isometric embedding of `k` index qubits
with a clean marker does not increase an operator-norm bound. -/
theorem error_low {K : Type*} {_ : NormedAddCommGroup K} {_ : NormedSpace ℂ K}
    {A : Reg (Fin (k + 1)) R →L[ℂ] K} {ε : ℝ} (h : ‖A‖ ≤ ε) :
    ‖A ∘L cleanAlong (R := R) (Fin.castSuccEmb : Fin k ↪ Fin (k + 1))‖ ≤ ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ ((ContinuousLinearMap.opNorm_nonneg _).trans h)
    fun p => ?_
  have h1 := ContinuousLinearMap.le_of_opNorm_le _ h
    (cleanAlong (R := R) (Fin.castSuccEmb : Fin k ↪ Fin (k + 1)) p)
  rwa [norm_cleanAlong] at h1

end

end SparseHamiltonian.SparseGateAccounting
