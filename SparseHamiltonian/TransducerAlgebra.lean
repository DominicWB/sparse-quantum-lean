import SparseHamiltonian.BandCertificate

/-!
# Exact algebra for the sparse Hamiltonian transducer

This module proves the finite-dimensional algebra underlying the reuse and
smoothing step of `sparse_polylog_precision_bound.tex`. Public and private spaces
are separate finite index types. No circuit, resolvent estimate, or norm bound is
assumed proved here: the hypotheses below explicitly state the needed unitary
and transduction identities.
-/

namespace SparseHamiltonian

open Matrix
open scoped BigOperators Matrix

section Transducer

variable {P V : Type*} [Fintype V] [DecidableEq V]

/-- The two column identities of a unitary block matrix needed below. -/
theorem unitary_block_column_identities [Fintype P] [DecidableEq P]
    (A : Matrix P P ℂ) (B : Matrix P V ℂ)
    (C : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hS : (Matrix.fromBlocks A B C D)ᴴ * Matrix.fromBlocks A B C D = 1) :
    Aᴴ * B + Cᴴ * D = 0 ∧ Bᴴ * B + Dᴴ * D = 1 := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at hS
  constructor
  · have h := congrArg Matrix.toBlocks₁₂ hS
    simpa only [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₂] using h
  · have h := congrArg Matrix.toBlocks₂₂ hS
    simpa only [← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₂] using h

/-- The cancellation identity obtained before multiplying by the public unitary. -/
theorem adjoint_public_mul_exit [Fintype P]
    (A U : Matrix P P ℂ) (B : Matrix P V ℂ)
    (C Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hAB : Aᴴ * B + Cᴴ * D = 0)
    (hBD : Bᴴ * B + Dᴴ * D = 1)
    (hPublic : A + B * Γ = U) (hPrivate : C + D * Γ = Γ) :
    Uᴴ * B = Γᴴ * (1 - D) := by
  have hCancel : Uᴴ * B + Γᴴ * D = Γᴴ := by
    calc
      Uᴴ * B + Γᴴ * D =
          (A + B * Γ)ᴴ * B + (C + D * Γ)ᴴ * D := by
            rw [hPublic, hPrivate]
      _ = (Aᴴ * B + Cᴴ * D) + Γᴴ * (Bᴴ * B + Dᴴ * D) := by
        simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
          Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
        abel
      _ = Γᴴ := by rw [hAB, hBD, zero_add, Matrix.mul_one]
  have h := eq_sub_of_add_eq hCancel
  simpa only [Matrix.mul_sub, Matrix.mul_one] using h

/-- The exit block of a unitary transducer is determined by its catalyst.

This is the manuscript identity `B = U Γ† (I - D)`, with differently typed
public and private spaces and with no commutativity assumption.
-/
theorem exit_block_eq [Fintype P] [DecidableEq P]
    (A U : Matrix P P ℂ) (B : Matrix P V ℂ)
    (C Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hS : (Matrix.fromBlocks A B C D)ᴴ * Matrix.fromBlocks A B C D = 1)
    (hU : U * Uᴴ = 1)
    (hPublic : A + B * Γ = U) (hPrivate : C + D * Γ = Γ) :
    B = U * Γᴴ * (1 - D) := by
  obtain ⟨hAB, hBD⟩ := unitary_block_column_identities A B C D hS
  have h := adjoint_public_mul_exit A U B C Γ D hAB hBD hPublic hPrivate
  calc
    B = (U * Uᴴ) * B := by rw [hU, Matrix.one_mul]
    _ = U * (Uᴴ * B) := Matrix.mul_assoc _ _ _
    _ = U * (Γᴴ * (1 - D)) := by rw [h]
    _ = U * Γᴴ * (1 - D) := (Matrix.mul_assoc _ _ _).symm

/-- The same exit identity from the single stacked transduction equation. -/
theorem exit_block_eq_of_transduction [Fintype P] [DecidableEq P]
    (A U : Matrix P P ℂ) (B : Matrix P V ℂ)
    (C Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hS : (Matrix.fromBlocks A B C D)ᴴ * Matrix.fromBlocks A B C D = 1)
    (hU : U * Uᴴ = 1)
    (hTrans : Matrix.fromBlocks A B C D * Matrix.fromRows 1 Γ =
      Matrix.fromRows U Γ) :
    B = U * Γᴴ * (1 - D) := by
  rw [Matrix.fromBlocks_mul_fromRows, Matrix.mul_one, Matrix.mul_one] at hTrans
  have hPublic := congrArg Matrix.toRows₁ hTrans
  have hPrivate := congrArg Matrix.toRows₂ hTrans
  exact exit_block_eq A U B C Γ D hS hU hPublic hPrivate

/-- The private state after `n` consecutive reuse steps, without normalization. -/
def reusedPrivate (D : Matrix V V ℂ) (Γ : Matrix V P ℂ) (n : ℕ) :
    Matrix V P ℂ := (1 - D ^ n) * Γ

@[simp] theorem reusedPrivate_zero (D : Matrix V V ℂ) (Γ : Matrix V P ℂ) :
    reusedPrivate D Γ 0 = 0 := by
  simp [reusedPrivate]

/-- The explicit private state satisfies the actual affine update recurrence. -/
theorem reusedPrivate_succ
    (C Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hPrivate : C + D * Γ = Γ) (n : ℕ) :
    reusedPrivate D Γ (n + 1) = C + D * reusedPrivate D Γ n := by
  have hC : C = Γ - D * Γ := eq_sub_of_add_eq hPrivate
  rw [reusedPrivate, reusedPrivate, hC, pow_succ']
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_assoc]
  abel

/-- Any private trajectory with zero input and the reuse recurrence equals the
closed geometric expression. -/
theorem reusedPrivate_eq_of_recurrence
    (C Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hPrivate : C + D * Γ = Γ)
    (Q : ℕ → Matrix V P ℂ) (hZero : Q 0 = 0)
    (hStep : ∀ n, Q (n + 1) = C + D * Q n) (n : ℕ) :
    Q n = reusedPrivate D Γ n := by
  induction n with
  | zero => simpa only [reusedPrivate_zero] using hZero
  | succ n ih => rw [hStep, ih, reusedPrivate_succ C Γ D hPrivate]

/-- One public output in the reuse circuit, before averaging the time slots. -/
theorem reusedPublic_eq
    (A U : Matrix P P ℂ) (B : Matrix P V ℂ)
    (Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hPublic : A + B * Γ = U) (n : ℕ) :
    A + B * reusedPrivate D Γ n = U - B * D ^ n * Γ := by
  simp only [reusedPrivate, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
  rw [← hPublic]
  simp only [Matrix.mul_assoc]
  abel

/-- The unnormalized geometric polynomial. -/
def geometricSum (D : Matrix V V ℂ) (n : ℕ) : Matrix V V ℂ :=
  ∑ j ∈ Finset.range n, D ^ j

/-- Summing the public outputs gives the exact unnormalized reuse formula. -/
theorem reusedPublic_sum
    (A U : Matrix P P ℂ) (B : Matrix P V ℂ)
    (Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hPublic : A + B * Γ = U) (n : ℕ) :
    (∑ j ∈ Finset.range n, (A + B * reusedPrivate D Γ j)) =
      n • U - B * geometricSum D n * Γ := by
  simp_rw [reusedPublic_eq A U B Γ D hPublic]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    geometricSum, Matrix.sum_mul, Matrix.mul_sum]

/-- The averaged geometric polynomial appearing in the reuse circuit. -/
noncomputable def geometricAverage (D : Matrix V V ℂ) (n : ℕ) : Matrix V V ℂ :=
  (n : ℂ)⁻¹ • geometricSum D n

/-- Exact public block of the averaged reuse construction for nonzero length. -/
theorem reusedPublic_average
    (A U : Matrix P P ℂ) (B : Matrix P V ℂ)
    (Γ : Matrix V P ℂ) (D : Matrix V V ℂ)
    (hPublic : A + B * Γ = U) (n : ℕ) (hn : n ≠ 0) :
    (n : ℂ)⁻¹ • (∑ j ∈ Finset.range n, (A + B * reusedPrivate D Γ j)) =
      U - B * geometricAverage D n * Γ := by
  rw [reusedPublic_sum A U B Γ D hPublic n]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hn']
  simp only [geometricAverage, Matrix.mul_smul, Matrix.smul_mul]

/-- The geometric cancellation identity holds for arbitrary private operators. -/
theorem one_sub_mul_geometricSum (D : Matrix V V ℂ) (n : ℕ) :
    (1 - D) * geometricSum D n = 1 - D ^ n := by
  exact mul_neg_geom_sum D n

/-- Exact inverse of `I-D` for a cyclic query clock satisfying `D^(2q)=-I`. -/
noncomputable def cyclicResolvent (D : Matrix V V ℂ) (q : ℕ) : Matrix V V ℂ :=
  (2 : ℂ)⁻¹ • geometricSum D (2 * q)

/-- The finite clock resolvent is a right inverse; no spectral theorem is needed. -/
theorem cyclicResolvent_right_inverse (D : Matrix V V ℂ) (q : ℕ)
    (hCycle : D ^ (2 * q) = -1) :
    (1 - D) * cyclicResolvent D q = 1 := by
  rw [cyclicResolvent, Matrix.mul_smul, one_sub_mul_geometricSum, hCycle,
    sub_neg_eq_add, ← two_smul ℂ (1 : Matrix V V ℂ), inv_smul_smul₀ two_ne_zero]

/-- The same expression is a left inverse, giving a two-sided exact resolvent. -/
theorem cyclicResolvent_left_inverse (D : Matrix V V ℂ) (q : ℕ)
    (hCycle : D ^ (2 * q) = -1) :
    cyclicResolvent D q * (1 - D) = 1 := by
  rw [cyclicResolvent, Matrix.smul_mul]
  change (2 : ℂ)⁻¹ • ((∑ j ∈ Finset.range (2 * q), D ^ j) * (1 - D)) = 1
  rw [geom_sum_mul_neg, hCycle, sub_neg_eq_add,
    ← two_smul ℂ (1 : Matrix V V ℂ), inv_smul_smul₀ two_ne_zero]

/-- Exact smoothing cancellation.  `F` may in particular be a polynomial in `D`.

This is the algebraic part of the error identity after the LCU of reuse circuits.
The subsequent operator-norm estimate and coefficient normalization are separate
analytic obligations.
-/
theorem smoothing_cancellation [Fintype P]
    (U : Matrix P P ℂ) (B : Matrix P V ℂ) (Γ : Matrix V P ℂ)
    (D F : Matrix V V ℂ) (n : ℕ)
    (hExit : B = U * Γᴴ * (1 - D)) (hComm : D * F = F * D) :
    B * F * geometricSum D n * Γ = U * Γᴴ * F * (1 - D ^ n) * Γ := by
  have hComm' : (1 - D) * F = F * (1 - D) := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one]
    rw [hComm]
  rw [hExit]
  calc
    U * Γᴴ * (1 - D) * F * geometricSum D n * Γ =
        U * Γᴴ * ((1 - D) * F) * geometricSum D n * Γ := by
          simp only [Matrix.mul_assoc]
    _ = U * Γᴴ * (F * (1 - D)) * geometricSum D n * Γ := by rw [hComm']
    _ = U * Γᴴ * F * ((1 - D) * geometricSum D n) * Γ := by
          simp only [Matrix.mul_assoc]
    _ = U * Γᴴ * F * (1 - D ^ n) * Γ := by rw [one_sub_mul_geometricSum]

/-- Finite polynomial evaluation on a private operator. -/
def privatePolynomial (a : ℕ → ℂ) (degree : ℕ) (D : Matrix V V ℂ) :
    Matrix V V ℂ := ∑ j ∈ Finset.range (degree + 1), a j • D ^ j

/-- Scalar-coefficient private polynomials commute with the private operator. -/
theorem privatePolynomial_commutes (a : ℕ → ℂ) (degree : ℕ) (D : Matrix V V ℂ) :
    D * privatePolynomial a degree D = privatePolynomial a degree D * D := by
  simp only [privatePolynomial, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_succ', ← pow_succ]

/-- For a polynomial filter, smoothing cancellation has no extra commutation
hypothesis. -/
theorem polynomial_smoothing_cancellation [Fintype P]
    (U : Matrix P P ℂ) (B : Matrix P V ℂ) (Γ : Matrix V P ℂ)
    (D : Matrix V V ℂ) (a : ℕ → ℂ) (degree n : ℕ)
    (hExit : B = U * Γᴴ * (1 - D)) :
    B * privatePolynomial a degree D * geometricSum D n * Γ =
      U * Γᴴ * privatePolynomial a degree D * (1 - D ^ n) * Γ :=
  smoothing_cancellation U B Γ D (privatePolynomial a degree D) n hExit
    (privatePolynomial_commutes a degree D)

end Transducer

end SparseHamiltonian
