import GateEfficientBinary.Sparse.Simulation

/-!
# Signed circuits from binary sparse data

Theorem `hs:thm:gates` of the accompanying paper assumes the hypotheses of Theorem `hs:thm:main`,
which simulates `exp(-itH)` for every real `t` (with `τ = η|t|`). The released binary-data
endpoints of `hs:thm:gates` build one circuit for every `τ ≥ 0`; for native implementations the
released `GateNative.native_simulation_signed` treats `t < 0` with the literal inverse of the
circuit for `|t|` (`GateNative.nativeSimSigned`, `GateNative.err_neg`). This file sets up that
construction for an arbitrary native circuit and for the binary-data circuit:

* `signed t C`: the circuit `C` if `0 ≤ t` and its literal inverse `GateNative.ninv C` (reversed,
  every instruction inverted) if `t < 0`; it keeps validity (`valid_signed`), the elementary gate
  count (`nGatesN_signed`) and every call count (`nCallsN_signed`), and a full-output error
  against `exp(-i|t|H)` on an embedding becomes the same error against `exp(-itH)` for
  self-adjoint `H` (`err_signed`);
* `qlift_matrixOperator_self`: the qubit lift of a Hermitian matrix is self-adjoint;
* `binarySimSigned`: the signed circuit of the released `GateBinary.binarySim` for the time
  `|t|`, on its wires (`binarySimSigned_of_nonneg`, `binarySimSigned_of_neg`), with its counts
  (`nGatesN_binarySimSigned`, `nCallsN_binarySimSigned`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSigned

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

/-! ### Signed native circuits -/

section Signed

variable {V Y J : Type*}

/-- **The circuit for a signed time** `t` from a circuit `C` for the time `|t|`: `C` itself if
`0 ≤ t`, its literal inverse `GateNative.ninv C` (the reversed list, every instruction inverted)
if `t < 0`. -/
def signed (t : ℝ) (C : List (NInstr V Y J)) : List (NInstr V Y J) :=
  if 0 ≤ t then C else ninv C

/-- For `t ≥ 0` the signed circuit is `C`. -/
theorem signed_of_nonneg {t : ℝ} (ht : 0 ≤ t) (C : List (NInstr V Y J)) : signed t C = C :=
  if_pos ht

/-- For `t < 0` the signed circuit is the literal inverse of `C`. -/
theorem signed_of_neg {t : ℝ} (ht : t < 0) (C : List (NInstr V Y J)) : signed t C = ninv C :=
  if_neg (not_le.2 ht)

/-- The signed circuit has the elementary gate count of `C`. -/
theorem nGatesN_signed (t : ℝ) (C : List (NInstr V Y J)) : nGatesN (signed t C) = nGatesN C := by
  unfold signed
  split_ifs
  · rfl
  · exact nGatesN_ninv C

/-- The signed circuit has every call count of `C` (a call of an inverse oracle counts as a call
of the oracle). -/
theorem nCallsN_signed (t : ℝ) (p : J → Bool) (C : List (NInstr V Y J)) :
    nCallsN p (signed t C) = nCallsN p C := by
  unfold signed
  split_ifs
  · rfl
  · exact nCallsN_ninv p C

/-- The signed circuit of a circuit of valid instructions consists of valid instructions. -/
theorem valid_signed (t : ℝ) (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid) :
    ∀ i ∈ signed t C, i.Valid := by
  unfold signed
  split_ifs
  · exact hC
  · exact valid_ninv C hC

variable [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y] {S : Type*} [Fintype S]
  [DecidableEq S]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The error of the signed circuit.** If a circuit `C` of valid instructions with unitary
primitive oracles is within `ε` of `exp(-i|t|H)` on an embedding `ι` of a system register and
`H` is self-adjoint, then `signed t C` is within `ε` of `exp(-itH)` on `ι`, for every real
`t`. -/
theorem err_signed (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (C : List (NInstr V Y J)) (hC : ∀ i ∈ C, i.Valid) (ι : Reg S R →L[ℂ] Reg V R)
    (H : Reg S R →L[ℂ] Reg S R) (hH : star H = H) (t ε : ℝ)
    (h : ‖nrun prim C ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * ((|t| : ℝ) : ℂ)) • H)‖ ≤ ε) :
    ‖nrun prim (signed t C) ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε := by
  unfold signed
  split_ifs with ht
  · rwa [abs_of_nonneg ht] at h
  · rw [nrun_ninv]
    exact err_neg _ (nrun_isUnitary prim hprim C hC) ι H hH t ε (lt_of_not_ge ht) h

end Signed

/-! ### The Hamiltonian of binary sparse data -/

section Hamiltonian

variable {n : Type*} [Fintype n] [DecidableEq n] {k : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The qubit lift `Ĥ = qlift en (H)` of a Hermitian matrix `H` on the `k` system qubits, with
the payload `R`, is self-adjoint. -/
theorem qlift_matrixOperator_self (en : Cfg (Fin k) ≃ n) (H : Matrix n n ℂ)
    (hH : H.IsHermitian) :
    star (qlift (R := R) en (SparseStateOverlap.matrixOperator H)) =
      qlift (R := R) en (SparseStateOverlap.matrixOperator H) := by
  rw [← qlift_star, SparseValuePrecision.matrixOperator_star_eq H hH]

end Hamiltonian

/-! ### The signed circuit from binary sparse data -/

/-- **The circuit from binary sparse data for a signed time** `t`: the released circuit
`GateBinary.binarySim` for the time `|t|` if `0 ≤ t` and its literal inverse if `t < 0`, on the
wires of the circuit for `|t|`, for the rescaling `γ`, the decoder scale `c₀`, the accuracy `ε`
and the arithmetic accuracy `ζ`. -/
def binarySimSigned (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ) :=
  signed t (binarySim k b σ hσ s γ c0 |t| ε ζ)

/-- For `t ≥ 0` the signed circuit is the released circuit for `|t| = t`. -/
theorem binarySimSigned_of_nonneg (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ)
    (ht : 0 ≤ t) :
    binarySimSigned k b σ hσ s γ c0 t ε ζ = binarySim k b σ hσ s γ c0 |t| ε ζ :=
  signed_of_nonneg ht _

/-- For `t < 0` the signed circuit is the literal inverse of the released circuit for `|t|`. -/
theorem binarySimSigned_of_neg (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ) (ht : t < 0) :
    binarySimSigned k b σ hσ s γ c0 t ε ζ = ninv (binarySim k b σ hσ s γ c0 |t| ε ζ) :=
  signed_of_neg ht _

/-- The signed circuit has the elementary gate count of the released circuit for `|t|`. -/
theorem nGatesN_binarySimSigned (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ) :
    nGatesN (binarySimSigned k b σ hσ s γ c0 t ε ζ) =
      nGatesN (binarySim k b σ hσ s γ c0 |t| ε ζ) :=
  nGatesN_signed t _

/-- The signed circuit has the call counts of the released circuit for `|t|`. -/
theorem nCallsN_binarySimSigned (k b σ : ℕ) (hσ : σ ≤ k) (s : ℕ) (γ c0 t ε ζ : ℝ)
    (p : Query → Bool) :
    nCallsN p (binarySimSigned k b σ hσ s γ c0 t ε ζ) =
      nCallsN p (binarySim k b σ hσ s γ c0 |t| ε ζ) :=
  nCallsN_signed t p _

end

end SparseHamiltonian.GateSigned
