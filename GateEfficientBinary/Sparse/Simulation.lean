import GateEfficientBinary.Sparse.Boundary
import GateEfficientBinary.Sparse.LiftNorm
import GateEfficientNative.Hamiltonian.Theorem

/-!
# Native gate-efficient sparse Hamiltonian simulation from binary data

This file instantiates the native gate-level simulation theorem
(`GateNative.native_simulation`, Theorem `hs:thm:gates` before finite-set synthesis) for sparse
Hamiltonians given by binary sparse oracles (`Sparse/Oracles`): `k`-bit indices, entries stored
as two `b`-bit two's complement components with a public scale `c₀`, `s = 2^σ` slots that are
the index words supported on the lowest `σ` bits. Every hypothesis of the native theorem is
discharged:

* `U_J`: Hadamard gates on the orientation wire and the lowest `σ` wires of the second index
  (`Sparse/Boundary`);
* the native private operation: the compute circuit of the binary oracles and the decoder
  `γ √s c₀ (X + i Y)` (`Sparse/Native`), with its native identity;
* the reversible arithmetic: the CORDIC circuit (`Cordic/Arith`);
* the clock promises: transported from the query-level sparse Cayley operation
  (`FixedNativeCayleySimulation`) through the qubit lift `elift`.

The simulated Hamiltonian is the qubit lift `Ĥ = qlift en (H)` of the represented matrix `H` on
the `k` system qubits, with an untouched reference register `R`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateCircuit.Sim (iota0 fDeg simM simR SimWire io)
open SparseHamiltonian.OracleCircuit CayleyClockInterface
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The lift of edge operators -/

section Qlift

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem qlift_smul (φ : Cfg V ≃ ι) (c : ℂ) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    qlift (R := R) φ (c • A) = c • qlift φ A :=
  map_smul (qliftHom (R := R) φ) c A

theorem qlift_add (φ : Cfg V ≃ ι) (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    qlift (R := R) φ (A + B) = qlift φ A + qlift φ B :=
  map_add (qliftHom (R := R) φ) A B

theorem qlift_sub (φ : Cfg V ≃ ι) (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    qlift (R := R) φ (A - B) = qlift φ A - qlift φ B :=
  map_sub (qliftHom (R := R) φ) A B

theorem qlift_star (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    qlift (R := R) φ (star A) = star (qlift φ A) :=
  map_star (qliftHom (R := R) φ) A

end Qlift

section Elift

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The lift of an operator of the oriented edge space to the ancilla register with the system
payload. -/
abbrev elift (en : Cfg (Fin k) ≃ n)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R) :=
  unconj (qlift (R := R) (phiPR en) A)

theorem elift_comp (en : Cfg (Fin k) ≃ n)
    (A B : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    elift (R := R) en (A ∘L B) = elift (R := R) en A ∘L elift (R := R) en B := by
  rw [elift, qlift_comp, unconj_comp]

theorem elift_one (en : Cfg (Fin k) ≃ n) :
    elift (R := R) en (1 : SparseEdgeMoments.OrientedSpace n →L[ℂ] _) = 1 := by
  rw [elift, qlift_one, unconj_one]

theorem elift_sub (en : Cfg (Fin k) ≃ n)
    (A B : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    elift (R := R) en (A - B) = elift (R := R) en A - elift (R := R) en B := by
  rw [elift, qlift_sub, unconj_sub]

theorem elift_adjoint (en : Cfg (Fin k) ≃ n)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    elift (R := R) en (A†) = (elift (R := R) en A)† := by
  rw [elift, qlift_adjoint, unconj_adjoint]

theorem norm_elift_le (en : Cfg (Fin k) ≃ n)
    (A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n) :
    ‖elift (R := R) en A‖ ≤ ‖A‖ :=
  (norm_unconj_le _).trans (norm_qlift_le _ _)

theorem elift_isUnitary (en : Cfg (Fin k) ≃ n)
    {A : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n}
    (hA : IsUnitary A) : IsUnitary (elift (R := R) en A) :=
  unconj_isUnitary (qlift_isUnitary _ hA)

end Elift

/-! ### Unitarity of the private operation -/

section Unitary

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The sparse edge Cayley action is unitary. -/
theorem orientedAction_isUnitary (H : Matrix n n ℂ) (s : ℕ) (γ : ℝ) :
    IsUnitary (OrientedEdgeCayley.action H s γ) := by
  have hA1 : star (OrientedEdgeCayley.action H s γ) * OrientedEdgeCayley.action H s γ = 1 := by
    rw [OrientedEdgeCayley.action_eq_cayley]
    exact ImprovedCayleyMoments.cayleyAction_star_mul_self _ _
      (scaled_self_adjoint _ γ (SparseEdgeMoments.generator_adjoint H s))
      (OrientedEdgeCayley.inverse_right H s γ)
  have hAM : OrientedEdgeCayley.action H s γ * OrientedEdgeCayley.lift (fun e =>
      star (ExactEdgeCayley.action (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H e.1 e.2))) = 1 := by
    rw [OrientedEdgeCayley.action, ← OrientedEdgeCayley.lift_mul]
    simp only [(ExactEdgeCayley.action_unitary _).2, OrientedEdgeCayley.lift_one]
  have hstar : star (OrientedEdgeCayley.action H s γ) = OrientedEdgeCayley.lift (fun e =>
      star (ExactEdgeCayley.action (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H e.1 e.2))) := by
    calc star (OrientedEdgeCayley.action H s γ)
        = star (OrientedEdgeCayley.action H s γ) * (OrientedEdgeCayley.action H s γ *
            OrientedEdgeCayley.lift (fun e => star (ExactEdgeCayley.action
              (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H e.1 e.2)))) := by rw [hAM, mul_one]
      _ = OrientedEdgeCayley.lift (fun e => star (ExactEdgeCayley.action
            (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * H e.1 e.2))) := by
          rw [← mul_assoc, hA1, one_mul]
  exact ⟨hA1, by rw [hstar, hAM]⟩

/-- The private Cayley operation with the locator conjugation is unitary. -/
theorem fixedAction_isUnitary {X Z : Type*} {s : ℕ} (D : Data X n Z s) (x : X) (γ : ℝ) :
    IsUnitary (FixedNativeCayleySimulation.action D x γ) :=
  UnitaryCayleyTransport.conjugate_unitary _ _ (FixedLocatorConjugation.locator_unitary D x)
    (orientedAction_isUnitary (D.matrix x) s γ)

end Unitary

/-! ### The gate-level operators and their clock promises -/

section Promises

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The private operation `D` on the ancilla register with the system payload. -/
def Dbin (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R) :=
  elift en (FixedNativeCayleySimulation.action D x γ)

/-- The resolvent at one `R₁ = (1 + i γK)/2` on the ancilla register with the system payload. -/
def R1bin (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    Reg (Fin (k + 1)) (Reg (Fin k) R) →L[ℂ] Reg (Fin (k + 1)) (Reg (Fin k) R) :=
  elift en (ImprovedCayleyMoments.resolventAtOne
    (scaled (FixedNativeCayleySimulation.generator D x) γ))

/-- The compressed generator `J† γK J` on the system qubits. -/
def Hbin (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    Reg (Fin k) R →L[ℂ] Reg (Fin k) R :=
  qlift en (compressed (FixedNativeCayleySimulation.generator D x)
    (FixedNativeCayleySimulation.boundary D) γ)

theorem Dbin_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    IsUnitary (Dbin (R := R) D en x γ) :=
  elift_isUnitary en (fixedAction_isUnitary D x γ)

theorem one_sub_Dbin_R1bin (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (γ : ℝ) : (1 - Dbin (R := R) D en x γ) ∘L R1bin (R := R) D en x γ = 1 := by
  have h := ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne _ _
    (FixedNativeCayleySimulation.inverse_right D x γ)
    (FixedNativeCayleySimulation.inverse_left D x γ)
  rw [← FixedNativeCayleySimulation.action_eq_cayley, mul_def] at h
  rw [Dbin, R1bin, ← elift_one (R := R) en, ← elift_sub, ← elift_comp, h, elift_one]

theorem R1bin_one_sub_Dbin (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (γ : ℝ) : R1bin (R := R) D en x γ ∘L (1 - Dbin (R := R) D en x γ) = 1 := by
  have h := ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction _ _
    (FixedNativeCayleySimulation.inverse_right D x γ)
  rw [← FixedNativeCayleySimulation.action_eq_cayley, mul_def] at h
  rw [Dbin, R1bin, ← elift_one (R := R) en, ← elift_sub, ← elift_comp, h, elift_one]

theorem norm_R1bin_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ)
    (hγ : 0 ≤ γ) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    ‖R1bin (R := R) D en x γ‖ ≤ width (s : ℝ) γ :=
  (norm_elift_le en _).trans (resolvent_norm _ (s : ℝ) γ hγ
    (FixedNativeCayleySimulation.generator_norm_le D x hrow))

theorem Hbin_self (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    star (Hbin (R := R) D en x γ) = Hbin (R := R) D en x γ := by
  rw [Hbin, ← qlift_star, compressed_self_adjoint _ _ γ
    (FixedNativeCayleySimulation.generator_self_adjoint D x)]

theorem norm_Hbin_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) : ‖Hbin (R := R) D en x γ‖ ≤ 1 :=
  (norm_qlift_le _ _).trans ((compressed_norm _ _ γ hγ
    (FixedNativeCayleySimulation.boundary_isometry D)
    (FixedNativeCayleySimulation.generator_boundary_norm_le D x hrow hcol)).trans hγ1)

/-- **The boundary promise** `(U_J ι₀)† R₁ (U_J ι₀) = (1 + i H)/2`. -/
theorem R1bin_boundary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (γ : ℝ) :
    (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))† ∘L
        R1bin (R := R) D en x γ ∘L
          (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • Hbin (R := R) D en x γ) := by
  rw [R1bin, boundary_lift σ hσ en D.slot hs hrange,
    show FixedLocatorConjugation.fixedBoundary D.slot = FixedNativeCayleySimulation.boundary D
      from rfl,
    ImprovedCayleyMoments.resolventAtOne_compression _ _
      (FixedNativeCayleySimulation.boundary_isometry D), qlift_smul, qlift_add, qlift_one,
    qlift_smul]
  rfl

theorem adjoint_comp_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : F →L[ℂ] F) (J : E →L[ℂ] F) :
    (A ∘L J)† ∘L (A ∘L J) = J† ∘L (A† ∘L A) ∘L J := by
  rw [adjoint_comp]
  simp only [comp_assoc]

/-- **The endpoint promise** `‖R₁ U_J ι₀‖ ≤ √((1 + γ²)/4)`. -/
theorem R1bin_endpoint (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (x : X) (γ : ℝ) (hγ : 0 ≤ γ) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    ‖R1bin (R := R) D en x γ ∘L
        (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))‖ ≤
      endpoint γ := by
  have hJ := FixedNativeCayleySimulation.boundary_isometry D
  have hKJ := FixedNativeCayleySimulation.generator_boundary_norm_le D x hrow hcol
  have hq := endpoint_norm _ _ γ (FixedNativeCayleySimulation.generator_self_adjoint D x) hJ hγ
    hKJ
  have hgram : (R1bin (R := R) D en x γ ∘L
      (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)))† ∘L
      (R1bin (R := R) D en x γ ∘L
        (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R))) =
      qlift en ((ImprovedCayleyMoments.resolventAtOne
        (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
          FixedNativeCayleySimulation.boundary D)† ∘L
        (ImprovedCayleyMoments.resolventAtOne
          (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
          FixedNativeCayleySimulation.boundary D)) := by
    rw [adjoint_comp_comp, adjoint_comp_comp, R1bin, ← elift_adjoint, ← elift_comp,
      boundary_lift σ hσ en D.slot hs hrange]
    rfl
  have h1 := norm_adjoint_comp_self (R1bin (R := R) D en x γ ∘L
    (UJop (R := R) (hadUJ k σ hσ) ∘L iota0 (a := k + 1) (P := Reg (Fin k) R)))
  rw [hgram] at h1
  have h2 := norm_qlift_le (R := R) en ((ImprovedCayleyMoments.resolventAtOne
    (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
      FixedNativeCayleySimulation.boundary D)† ∘L
    (ImprovedCayleyMoments.resolventAtOne
      (scaled (FixedNativeCayleySimulation.generator D x) γ) ∘L
      FixedNativeCayleySimulation.boundary D))
  rw [norm_adjoint_comp_self, h1] at h2
  have he : 0 ≤ endpoint γ := Real.sqrt_nonneg _
  exact (mul_self_le_mul_self_iff (norm_nonneg _) he).2
    (h2.trans (mul_le_mul hq hq (norm_nonneg _) he))

/-- The rescaling cancels in the simulated evolution. -/
theorem Hbin_exponent (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (hH : (D.matrix x).IsHermitian) (τ γ : ℝ) (hγ : γ ≠ 0) :
    (-Complex.I * (time (s : ℝ) τ γ : ℂ)) • Hbin (R := R) D en x γ =
      (-Complex.I * (τ : ℂ)) • qlift (R := R) en
        (SparseStateOverlap.matrixOperator (D.matrix x)) := by
  rw [Hbin, ← qlift_smul, FixedNativeCayleySimulation.physical_exponent D x hH τ γ hγ,
    qlift_smul]

end Promises

/-! ### The theorem -/

section Main

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The real components of the stored entry, as wires of the private operation. -/
def valX (k b : ℕ) : Fin b → BW k b := fun i => vB (Sum.inl i)

/-- The imaginary components of the stored entry, as wires of the private operation. -/
def valY (k b : ℕ) : Fin b → BW k b := fun i => vB (Sum.inr i)

/-- The CORDIC arithmetic of the binary private operation, for the decoder scale `κ`. -/
def binArith (k b : ℕ) (κ ζ : ℝ) : Arith (NB Empty (PR k) (SZ k b)) :=
  cordicArith b (valX k b) (valY k b) κ ζ

/-- **The native circuit from binary sparse data**: the native simulation circuit with `U_J`
from Hadamard gates, the compute circuit of the binary oracles and the CORDIC arithmetic, for
the rescaling `γ`, the time `τ`, the accuracy `ε` and the arithmetic accuracy `ζ`. -/
def binarySim (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 τ ε ζ : ℝ) :=
  nativeSim (S := Fin k) (k + 1) (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε
    (hadUJ k σ hσ) (sparseOp k b (γ * Real.sqrt s * c0))
    (binArith k b (γ * Real.sqrt s * c0) ζ)

theorem card_SZ (k b : ℕ) : Fintype.card (SZ k b) = 6 * k + 2 * b := by
  simp only [SZ, EW, VW, Fintype.card_sum, Fintype.card_fin]
  ring

/-- **Native gate-efficient sparse Hamiltonian simulation from binary data** (Theorem
`hs:thm:gates` for binary sparse oracles, before finite-set synthesis). Let the native sparse
data `D` have `k`-bit indices (`en`), `s = 2^σ` slots that are exactly the index words
supported on the lowest `σ ≤ k` bits (`hrange`), and entries stored as two `b`-bit two's
complement components `X`, `Y` with decoder `c₀ (X + i Y)`, `c₀ > 0` (`hdec`). For an input `x`
with a Hermitian matrix `H` of row and column norms at most one, a rescaling `0 < γ ≤ 1`, a
time `τ ≥ 0`, accuracies `0 < ε ≤ 1` and `0 < ζ ≤ 1` with `48 d ζ ≤ ε`, the circuit
`binarySim` consists of valid instructions; it makes `12 d` times `2` row-location, `2`
column-location and `1` value calls (`d` the filter degree); its elementary gates are at most
`200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d (56 k + 2 |arith| + 2 bP + bT + 1)`, with the CORDIC
counts of `cordicArith_counts`; it has the stated qubit count; its full output on the system
embedding is within `ε` of `exp(-iτĤ)` for the qubit lift `Ĥ` of `H` on the `k` system qubits,
the payload `R` an untouched reference; and `d ≤ 128 (τ' q̄ + Q (1 + log (6/ε)))`, while the
register sizes satisfy `steps τ' (ε/6) ≤ 2^m < 2 steps τ' (ε/6)` and `2d + 2 ≤ 2^r ≤ 4 (d+1)`,
as in `native_simulation`. -/
theorem binary_simulation (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (σ : ℕ)
    (hσ : σ ≤ k) (hs : s = 2 ^ σ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin σ → Bool, j = en (lowWord σ u))
    (hb : 0 < b) (c0 : ℝ) (hc0 : 0 < c0) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z)
    (x : X) (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) (γ τ ε ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hζε : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ binarySim k b σ hσ s γ c0 τ ε ζ, i.Valid) ∧
    (∀ p : Query → Bool, nCallsN p (binarySim k b σ hσ s γ c0 τ ε ζ) =
      12 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
        (2 * (if p Query.rowLocation then 1 else 0) +
          2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0))) ∧
    nGatesN (binarySim k b σ hσ s γ c0 τ ε ζ) ≤
      200 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) *
          (k + 1 + simM (time (s : ℝ) τ γ) (ε / 2) +
            simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) +
        84 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) * (σ + 1) +
        6 * fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) *
          (2 * (28 * k) + 2 * (binArith k b (γ * Real.sqrt s * c0) ζ).circ.length +
            (2 * (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
              (binArith k b (γ * Real.sqrt s * c0) ζ).bT + 1)) ∧
    Fintype.card (HW (SimWire (k + 1) (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2))
        (Fin k) Empty (SZ k b) (binArith k b (γ * Real.sqrt s * c0) ζ).bT
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP (binArith k b (γ * Real.sqrt s * c0) ζ).A) =
      k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
          6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
        (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
          (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
          (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) ∧
    ‖nrun (prims (R := R) D en x) (binarySim k b σ hσ s γ c0 τ ε ζ) ∘L
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
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by
    rw [hs]
    exact_mod_cast Nat.one_le_two_pow
  have hκ : 0 < γ * Real.sqrt s * c0 := by
    have : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by linarith)
    positivity
  obtain ⟨k0, hk0⟩ : ∃ m, D.slot m = zIdx en := by
    refine (hrange _).2 ⟨fun _ => false, ?_⟩
    unfold zIdx
    congr 1
    funext i
    simp [lowWord]
  have hxy : Function.Injective (Sum.elim (valX k b) (valY k b)) := by
    intro i j h
    rcases i with i | i <;> rcases j with j | j <;> simp_all [valX, valY, vB]
  have ho : ∀ i, Sum.elim (valX k b) (valY k b) i ≠
      Sum.inl (Sum.inr (sparseOp k b (γ * Real.sqrt s * c0)).o) := by
    intro i
    rcases i with i | i
    · exact vB_ne_oB _
    · exact vB_ne_oB _
  have har := cordicArith_ok b hb (valX k b) (valY k b) hxy _ ho _ ζ hκ hζ hζ1
  have hτ' : 0 ≤ time (s : ℝ) τ γ := div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) hγ.le
  obtain ⟨hvalid, hcalls, hgates, hcard, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
    native_simulation (k + 1) (prims (R := R) D en x) (prims_isUnitary D en x)
      (hadUJ k σ hσ) (hadUJ_ok σ hσ) (sparseOp k b (γ * Real.sqrt s * c0))
      (sparseOp_public k b _) (binArith k b (γ * Real.sqrt s * c0) ζ) ζ hζ.le har
      (Dbin (R := R) D en x γ) (R1bin (R := R) D en x γ) (Hbin (R := R) D en x γ)
      (Dbin_isUnitary D en x γ) (sparse_nativeOK D en k0 hk0 c0 hdec x γ)
      (time (s : ℝ) τ γ) (width (s : ℝ) γ) (endpoint γ) (moment γ) ε hτ' (width_ge_one _ _)
      (one_sub_Dbin_R1bin D en x γ) (R1bin_one_sub_Dbin D en x γ)
      (norm_R1bin_le D en x γ hγ.le hrow) (R1bin_boundary D en σ hσ hs hrange x γ)
      (Hbin_self D en x γ) (norm_Hbin_le D en x γ hγ.le hγ1 hrow hcol)
      (R1bin_endpoint D en σ hσ hs hrange x γ hγ.le hrow hcol) (endpoint_sq γ).le
      (moment_le_width _ γ hγ.le hγ1) hε hε1 hζε
  have hV : (sparseOp k b (γ * Real.sqrt s * c0)).V = computeV k b := rfl
  rw [hV, computeV_nGates, hadUJ_length] at hgates
  simp only [hV, computeV_nCalls] at hcalls
  rw [card_SZ, Fintype.card_fin] at hcard
  rw [Hbin_exponent D en x hH τ γ hγ.ne'] at herr
  unfold binarySim
  exact ⟨hvalid, hcalls, hgates, hcard, herr, hdeg, hm1, hm2, hr1, hr2⟩

end Main

end

end SparseHamiltonian.GateBinary
