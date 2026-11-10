import LargeSparsityCore.NativeMoments
import LargeSparsityCore.Core
import SparseHamiltonian.NativeCayleyActive
import SparseHamiltonian.NativeWholeProgramActiveContinuation2

set_option autoImplicit false

/-!
# The large-sparsity core on the native sparse oracles

This module verifies the hypotheses of the abstract core (`Core.CoreData`) for the joint
representation of `NativeOperators` and `NativeMoments` (`coreData`), with `β = h` and the
Cayley scale `q` of `Parameters`, and compiles the private Cayley operator to the original native
oracles:

* the logical program (six masked calls) is compiled by the released three-query construction and
  flattened to the native basis of the released active compiler (`physProgram`, eighteen native
  calls, `physProgram_intertwines`);
* every synchronized active clock layer is then implemented with `54` native calls on the fixed
  released clean encoding (`active_implementsOn`, via
  `SparseHamiltonian.NativeWholeProgramActive.clean_implementsOn`).

**Theorem** (`core_native`). In the regime `Parameters.Regime s τ ε` (`s ≥ 1`, `τ ≥ 1`,
`0 < ε ≤ 1/64`, `h ≥ 10⁴`, `sτ ≥ Lh`), for sparse data with Hermitian `H(x)` whose rows and columns
have Euclidean norm at most `η > 0`, there is a program over the released native oracle family
(`SparseHamiltonian.NativeCayleyActive.oracle`) with at most `324 d ≤ 324 · 21520 √(sτr)` calls,
unitary for every instance, and with full-output error at most `ε` for `e^{-i (τ/η) H}`, with the
same known isometry `input` (the coherent smoothing preparation followed by the fixed clean
encoding) on input and output (`opt:eq:core-degree`). `core_simulation` is the form for `e^{-itH}`
with `τ = η|t|`, for every sign of `t`.
-/

namespace LargeSparsityCore.Native

noncomputable section

set_option maxRecDepth 8192
set_option synthInstance.maxSize 2048

open ContinuousLinearMap SparseHamiltonian NativeSignedFactor OrientedNativeLayout
open NativeSparseBlockEncoding OracleCircuit CayleyBlocks SparseEdgeMoments Parameters
open LabeledEncodedOracle ReuseLayerFactorization
open scoped InnerProduct

/-- A squared pointwise bound gives an operator-norm bound. -/
theorem opNorm_le_of_sq {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {A : E →L[ℂ] F} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v, ‖A v‖ ^ 2 ≤ c ^ 2 * ‖v‖ ^ 2) : ‖A‖ ≤ c := by
  apply opNorm_le_bound _ hc
  intro v
  have h2 : ‖A v‖ ^ 2 ≤ (c * ‖v‖) ^ 2 := by rw [mul_pow]; exact h v
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-! ### The hypotheses of the core -/

/-- **The joint representation satisfies the hypotheses of the abstract core** (`β = h`). -/
theorem coreData (D : Data X n Z s) {τ ε η : ℝ} (R : Regime s τ ε) (hη : 0 < η) {x : X}
    (hP : Promise D η x) :
    Core.CoreData s τ ε (Kop D η (hval τ ε) (qval s τ ε) x) (Dop D η (hval τ ε) (qval s τ ε) x)
      (Ppl D η (hval τ ε) x) (Pmi D η (hval τ ε) x) (Jin D) := by
  have hh := R.h_pos
  have hq := R.q_pos
  have hs : (0 : ℝ) < s := by exact_mod_cast R.one_le_s
  have hK : ∀ v, ‖(Kop D η (hval τ ε) (qval s τ ε) x ∘L Jin D) v‖ ^ 2 ≤
      (Real.sqrt (2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s)) ^ 2 * ‖v‖ ^ 2 := by
    intro v
    rw [Real.sq_sqrt (by positivity), comp_apply]
    exact norm_K_input_sq_le D (qval s τ ε) hη hh.le hP v
  have hKn := opNorm_le_of_sq (Real.sqrt_nonneg _) hK
  refine ⟨spectral D η (hval τ ε) (qval s τ ε) x, Dop_isometry D η _ _ x, Jin_isometry D, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine (norm_R1_bulk_le D hη hh hq.le x).trans ?_
    have hQ := R.Q0_ge
    unfold Q0 at hQ ⊢
    linarith
  · apply opNorm_le_of_sq (sw_nonneg s τ ε)
    intro v
    rw [R.sw_sq, comp_apply]
    exact norm_Ppl_input_sq_le D hη hh.le hP v
  · apply opNorm_le_of_sq (sw_nonneg s τ ε)
    intro v
    rw [R.sw_sq, comp_apply]
    exact norm_Pmi_input_sq_le D hη hh.le hP v
  · apply opNorm_le_of_sq (sm_nonneg s τ ε)
    intro v
    rw [sm, Real.sq_sqrt (by positivity), comp_apply, comp_apply, ← comp_apply]
    exact norm_bulk_input_sq_le D (qval s τ ε) hη hh.le hP v
  · calc ‖Kop D η (hval τ ε) (qval s τ ε) x ∘L Jin D‖ ^ 2 ≤
          (Real.sqrt (2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hKn 2
      _ = 2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s := Real.sq_sqrt (by positivity)
  · have hJ : ‖(Jin D)†‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]
      exact Core.norm_le_one_of_isometry (Jin_isometry D)
    have h1 : Real.sqrt (2 * qval s τ ε ^ 2 * (1 + hval τ ε) / s) ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact R.second_le_one
    calc ‖(Jin D)† ∘L Kop D η (hval τ ε) (qval s τ ε) x ∘L Jin D‖ ≤
          ‖(Jin D)†‖ * ‖Kop D η (hval τ ε) (qval s τ ε) x ∘L Jin D‖ := opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hJ (hKn.trans h1) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-! ### The physical program -/

/-- The compiled physical program of the private Cayley operator on the flat native basis of the
released active compiler: eighteen native calls. -/
def physProgram (D : Data X n Z s) (η β q : ℝ) :
    MultiOracleCircuit.Program (NativeCayleyProgram.oracle D) :=
  FlatMaskedAccess.flatten (NativeSparseMaskedAccess.flatOracle D)
    (NativeMaskedProgram.compile (NativeSparseMaskedAccess.flatOracle D)
      (NativeSparseMaskedAccess.cleanBasis D) id OrientedNativeLayout.masks
      (logicalProgram D η β q))

@[simp] theorem physProgram_count (D : Data X n Z s) (η β q : ℝ) :
    (physProgram D η β q).count = 18 := by
  rw [physProgram, FlatMaskedAccess.flatten_count, NativeMaskedProgram.compile_count,
    logicalProgram_count]

/-- The fixed clean encoding of the private workspace in the flat native basis. -/
def privateEmbedding (D : Data X n Z s) :
    Space n Z →ₗᵢ[ℂ] NativeMaskedOracle.Logical PUnit.{1} (NativeCayleyProgram.Basis n Z) :=
  FlatMaskedAccess.singleton (FlatMaskedAccess.embedding
    (NativeMaskedOracle.input (ι := Bool) (NativeSparseMaskedAccess.cleanBasis D)))

/-- The physical program implements the private Cayley operator on the clean encoding. -/
theorem physProgram_intertwines (D : Data X n Z s) (η β q : ℝ) (x : X) :
    WeightedClock.diagonal (fun _ : PUnit.{1} => (physProgram D η β q).eval x) ∘L
        (privateEmbedding D).toContinuousLinearMap =
      (privateEmbedding D).toContinuousLinearMap ∘L Dop D η β q x := by
  apply FlatMaskedAccess.singleton_intertwines
  apply FlatMaskedAccess.flatten_intertwines
  rw [NativeSparseMaskedAccess.compile_eval, logicalProgram_eval]

/-- The fixed clean encoding of the whole chronological clock workspace. -/
def embedding (D : Data X n Z s) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := EuclideanSpace ℂ n)
      (V := ChronologicalResolvent.BlockOperator.H T (Space n Z)) d) →ₗᵢ[ℂ]
        NativeCayleyActive.Physical n Z T d :=
  NativeWholeProgramActive.cleanInput (C := PUnit.{1}) (NativeCayleyActive.publicEmbedding D)
    (privateEmbedding D) (NativeCayleyProgram.cleanBasis D) T d

/-- **Every active clock layer costs `54` native calls.** -/
theorem active_implementsOn (D : Data X n Z s) (η β q : ℝ) (T d r : ℕ) :
    ImplementsOn (NativeCayleyActive.oracle D T d)
      (fun x => activeClock (P := EuclideanSpace ℂ n) (Dop D η β q x) T d r)
      (embedding D T d).toContinuousLinearMap 54 := by
  have h := NativeWholeProgramActive.clean_implementsOn (C := PUnit.{1})
    (NativeCayleyProgram.oracle D) (NativeCayleyProgram.oracle_unitary D)
    (NativeCayleyProgram.cleanBasis D) (NativeCayleyProgram.image D)
    (NativeCayleyProgram.valid D) (physProgram D η β q) (NativeCayleyActive.publicEmbedding D)
    (privateEmbedding D) (fun x => Dop D η β q x) (physProgram_intertwines D η β q) T d r
  rw [physProgram_count] at h
  exact h

/-! ### The simulation -/

/-- The known input of the core simulation: the coherent smoothing preparation followed by the
fixed clean encoding. -/
def input (D : Data X n Z s) (τ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] NativeCayleyActive.Physical n Z (steps s τ ε) (degree s τ ε) :=
  (embedding D (steps s τ ε) (degree s τ ε)).toContinuousLinearMap ∘L
    Core.input (EuclideanSpace ℂ n) (Space n Z) s τ ε

theorem input_isometry (D : Data X n Z s) {τ ε : ℝ} (R : Regime s τ ε) :
    (input D τ ε)† ∘L input D τ ε = 1 := by
  apply (norm_map_iff_adjoint_comp_self (input D τ ε)).mp
  intro v
  rw [input, comp_apply, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact (norm_map_iff_adjoint_comp_self _).mpr (Core.input_isometry R) v

set_option maxHeartbeats 1000000 in
/-- **The large-sparsity core on the native oracles** (`opt:sec:core`). -/
theorem core_native (D : Data X n Z s) {τ ε η : ℝ} (R : Regime s τ ε) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian) (hP : ∀ x, Promise D η x) :
    (input D τ ε)† ∘L input D τ ε = 1 ∧
    ∃ p : MultiOracleCircuit.Program (NativeCayleyActive.oracle D (steps s τ ε) (degree s τ ε)),
      p.count ≤ 324 * degree s τ ε ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D τ ε - input D τ ε ∘L NormedSpace.exp
          ((-Complex.I * ((τ / η : ℝ) : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤
            ε := by
  obtain ⟨p, hcount, hp⟩ := Core.core_query R
    (fun x => Kop D η (hval τ ε) (qval s τ ε) x) (fun x => Dop D η (hval τ ε) (qval s τ ε) x)
    (fun x => Ppl D η (hval τ ε) x) (fun x => Pmi D η (hval τ ε) x) (Jin D) (Jin_isometry D)
    (fun x => coreData D R hη (hP x)) (NativeCayleyActive.oracle D (steps s τ ε)
      (degree s τ ε)) (NativeCayleyActive.oracle_unitary D _ _)
    (embedding D (steps s τ ε) (degree s τ ε)).toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self _) 54
    (fun r _ => active_implementsOn D η (hval τ ε) (qval s τ ε) _ _ r)
  refine ⟨input_isometry D R, p, by omega, fun x => ⟨(hp x).1, ?_⟩⟩
  have h := (hp x).2
  rw [compression D (qval s τ ε) hη R.h_pos (hH x) (hP x), smul_smul] at h
  have hs : (s : ℝ) ≠ 0 := (show (0 : ℝ) < s by linarith [R.one_le_s]).ne'
  have hq := R.q_pos.ne'
  have e : -Complex.I * (aval s τ ε : ℂ) * ((qval s τ ε / (s * η) : ℝ) : ℂ) =
      -Complex.I * ((τ / η : ℝ) : ℂ) := by
    rw [mul_assoc, ← Complex.ofReal_mul]
    congr 2
    unfold aval
    field_simp
  rw [e] at h
  exact h

omit [DecidableEq n] in
theorem matrixOperator_star {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    star (SparseStateOverlap.matrixOperator H) = SparseStateOverlap.matrixOperator H := by
  rw [ContinuousLinearMap.star_eq_adjoint, SparseValuePrecision.matrixOperator_adjoint, hH.eq]

/-- **The large-sparsity core for every time** (`opt:sec:core`, `opt:eq:core-degree`). For
`τ = η|t|` in the regime of `Parameters.Regime`, at most `6972480 √(sτr)` native calls give full
output error at most `ε` for `e^{-itH}`; negative time uses the inverse circuit. -/
theorem core_simulation (D : Data X n Z s) {η t ε : ℝ} (hη : 0 < η)
    (R : Regime s (η * |t|) ε) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hP : ∀ x, Promise D η x) :
    (input D (η * |t|) ε)† ∘L input D (η * |t|) ε = 1 ∧
    ∃ p : MultiOracleCircuit.Program
        (NativeCayleyActive.oracle D (steps s (η * |t|) ε) (degree s (η * |t|) ε)),
      (p.count : ℝ) ≤ 6972480 * Real.sqrt (s * (η * |t|) * rval (η * |t|) ε) ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D (η * |t|) ε - input D (η * |t|) ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨hin, p, hcount, hp⟩ := core_native D R hη hH hP
  refine ⟨hin, ?_⟩
  have hO := NativeCayleyActive.oracle_unitary D (steps s (η * |t|) ε) (degree s (η * |t|) ε)
  have htime : η * |t| / η = |t| := by field_simp
  have hcount' : (p.count : ℝ) ≤ 6972480 * Real.sqrt (s * (η * |t|) * rval (η * |t|) ε) := by
    have h1 : (p.count : ℝ) ≤ 324 * (degree s (η * |t|) ε : ℝ) := by exact_mod_cast hcount
    have h2 := R.degree_le_sqrt
    nlinarith
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨p, hcount', fun x => ⟨(hp x).1, ?_⟩⟩
    have h := (hp x).2
    have e : ((|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_nonneg ht]
    rw [htime, e] at h
    exact h
  · refine ⟨p.adjoint, by rw [MultiOracleCircuit.Program.count_adjoint]; exact hcount',
      fun x => ⟨(p.adjoint).eval_unitary hO x, ?_⟩⟩
    have h := LabeledAdjointSimulation.program_negative_time_error p hO (input D (η * |t|) ε)
      (input D (η * |t|) ε) (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
      (fun x => matrixOperator_star (hH x)) |t| ε (fun x => by
        have h := (hp x).2
        rw [htime] at h
        exact h) x
    have e : ((-|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_neg ht, neg_neg]
    rw [e] at h
    exact h

end

end LargeSparsityCore.Native
