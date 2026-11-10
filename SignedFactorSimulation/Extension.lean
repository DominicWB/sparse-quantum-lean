import SignedFactorSimulation.Cascade

/-!
# Public registers of the factor's size

In the circuit every register is a copy of the factor's register `W`: the system `P` enters
through the known isometry `E : P → W`, and each public slot of a reuse circuit is a copy of `W`.
A colligation `(A, B, C, D)` with public space `P` is extended to the public space `W` by the
identity on the complement of the range of `E`:

  `A_W = E A E† + (I - E E†)`,  `B_W = E B`,  `C_W = C E†`,  `D_W = D`.

The extension conserves energy whenever the original colligation does (`ext_energy`), and it
compresses back: every Taylor coefficient of its transfer, and hence the uniform clock of its
reuse circuit, compressed by `E`, is that of the original (`transferCoeff_ext`,
`successfulBlock_ext`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.CoherentReuse
open scoped InnerProduct InnerProductSpace

variable {P W V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The public block on `W`: `A` on the range of `E`, the identity on its complement. -/
def extA (E : P →L[ℂ] W) (A : P →L[ℂ] P) : W →L[ℂ] W := E ∘L A ∘L E† + (1 - E ∘L E†)

/-- The private-to-public block on `W`. -/
def extB (E : P →L[ℂ] W) (B : V →L[ℂ] P) : V →L[ℂ] W := E ∘L B

/-- The public-to-private block on `W`. -/
def extC (E : P →L[ℂ] W) (C : P →L[ℂ] V) : W →L[ℂ] V := C ∘L E†

theorem isometry_adjoint_apply {E : P →L[ℂ] W} (hE : E† ∘L E = 1) (y : P) : (E†) (E y) = y := by
  have h := congrArg (fun T : P →L[ℂ] P => T y) hE
  simpa using h

theorem compress_extA {E : P →L[ℂ] W} (hE : E† ∘L E = 1) (A : P →L[ℂ] P) :
    E† ∘L extA E A ∘L E = A := by
  ext y
  simp [extA, isometry_adjoint_apply hE]

omit [CompleteSpace V] in
/-- Every Taylor coefficient of the extended transfer compresses to the original one. -/
theorem transferCoeff_ext {E : P →L[ℂ] W} (hE : E† ∘L E = 1) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (k : ℕ) :
    E† ∘L transferCoeff (extA E A) (extB E B) (extC E C) D k ∘L E = transferCoeff A B C D k := by
  cases k with
  | zero => exact compress_extA hE A
  | succ k =>
    ext y
    simp [transferCoeff, extB, extC, isometry_adjoint_apply hE]

omit [CompleteSpace V] in
/-- **Compression of the extended reuse circuit**: the uniform clock of `n` reuses of the
extended colligation, compressed by `E`, is the uniform clock of the original. -/
theorem successfulBlock_ext {E : P →L[ℂ] W} (hE : E† ∘L E = 1) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    E† ∘L successfulBlock (extA E A) (extB E B) (extC E C) D n ∘L E =
      successfulBlock A B C D n := by
  rw [successfulBlock_eq_sum, successfulBlock_eq_sum]
  have h : ∀ X : W →L[ℂ] W, E† ∘L X ∘L E = sandwich (E†) E X := fun X => rfl
  rw [h, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, sandwich_apply, transferCoeff_ext hE]

theorem norm_map_of_isometry {E : P →L[ℂ] W} (hE : E† ∘L E = 1) (y : P) : ‖E y‖ = ‖y‖ :=
  E.norm_map_iff_adjoint_comp_self.mpr hE y

omit [CompleteSpace V] in
/-- **Energy of the extension**: an energy-conserving colligation stays energy conserving when
its public space is extended from `P` to `W`. -/
theorem ext_energy {E : P →L[ℂ] W} (hE : E† ∘L E = 1) {A : P →L[ℂ] P} {B : V →L[ℂ] P}
    {C : P →L[ℂ] V} {D : V →L[ℂ] V}
    (h : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2) (x : W) (v : V) :
    ‖extA E A x + extB E B v‖ ^ 2 + ‖D v + extC E C x‖ ^ 2 = ‖x‖ ^ 2 + ‖v‖ ^ 2 := by
  set p : P := (E†) x with hp
  set y : W := x - E p with hy
  have hEy : (E†) y = 0 := by
    rw [hy, map_sub, isometry_adjoint_apply hE, hp, sub_self]
  have hpyth : ∀ z : P, ‖E z + y‖ ^ 2 = ‖z‖ ^ 2 + ‖y‖ ^ 2 := by
    intro z
    have horth : ⟪E z, y⟫_ℂ = 0 := by
      rw [← adjoint_inner_right, hEy, inner_zero_right]
    rw [@norm_add_sq ℂ, horth, map_zero, mul_zero, add_zero, norm_map_of_isometry hE]
  have h1 : extA E A x + extB E B v = E (A p + B v) + y := by
    simp only [extA, extB, add_apply, comp_apply, sub_apply, one_apply_eq_self, map_add, hy, hp]
    abel
  have h2 : extC E C x = C p := rfl
  have hx : x = E p + y := by rw [hy]; abel
  have hxn : ‖x‖ ^ 2 = ‖p‖ ^ 2 + ‖y‖ ^ 2 := by
    conv_lhs => rw [hx]
    exact hpyth p
  rw [h1, h2, hpyth, hxn]
  have := h p v
  linarith

end

end SignedFactorSimulation
