import SparseLowerBounds.LinearSystems.Gadget
import SparseLowerBounds.Hamiltonian.Rounding

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The search gadget `U_x` of `part:hsl`

Manuscript: eq. `hsl:eq:gadget`. For a one-hot string marked
at `j`, `U_x = S^{j+1}(2P_u - I)` has entries `(U_x)_{ab} = 2/m - x_{a-b-1 mod m}`.
This is literally the QLS gadget `LinearSystems.gadget m j` (entry formula
`2/m - [a - b - 1 ≡ j]`), which is reused: it is unitary
(`LinearSystems.gadget_mem_unitaryGroup`), real
(`LinearSystems.star_gadget_apply`), and dense for `m ≥ 3`
(`LinearSystems.gadget_apply_ne_zero`), with entry `(a, b)` depending only on
the membership bit at position `LinearSystems.gadgetPos a b`.

New here: on the known alternating vector `v = Z u`, `v_a = (-1)^a/√m`,
`U_x v = (-1)^j v` for even `m` (the chain construction of Section `part:hsl`, `gadget_mulVec_alt`).
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open scoped Matrix

variable {m : ℕ}

/-- The alternating unit vector `v = Z u`, `v_a = (-1)^a/√m`. -/
def alt (m : ℕ) : Fin m → ℂ := fun a => (-1 : ℂ) ^ (a : ℕ) / (Real.sqrt m : ℂ)

namespace Gadget

/-- `gadgetPos a b + b + 1 ≡ a (mod m)`, as an equation in `ℕ` usable by `omega`. -/
theorem gadgetPos_spec (a b : Fin m) :
    (LinearSystems.gadgetPos a b : ℕ) + b + 1 = a ∨
      (LinearSystems.gadgetPos a b : ℕ) + b + 1 = a + m := by
  have ha := a.isLt
  have hb := b.isLt
  unfold LinearSystems.gadgetPos
  simp only
  rcases lt_or_ge ((a : ℕ) + (m - 1 - b)) m with h | h
  · rw [Nat.mod_eq_of_lt h]; right; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; left; omega

/-- For fixed `a`, exactly one `b` queries bit `j`. -/
theorem gadgetPos_eq_iff (a b j : Fin m) :
    LinearSystems.gadgetPos a b = j ↔ b = LinearSystems.gadgetPos a j := by
  have ha := a.isLt
  have hb := b.isLt
  have hj := j.isLt
  rcases gadgetPos_spec a b with h1 | h1 <;> rcases gadgetPos_spec a j with h2 | h2 <;>
  · simp only [Fin.ext_iff]
    have := (LinearSystems.gadgetPos a b).isLt
    have := (LinearSystems.gadgetPos a j).isLt
    omega

/-- `(-1)^n` in `ℂ` depends only on `n mod 2`. -/
theorem neg_one_pow_eq_of_mod_two {n k : ℕ} (h : n % 2 = k % 2) :
    (-1 : ℂ) ^ n = (-1 : ℂ) ^ k := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-- `Σ_{a < 2k} (-1)^a = 0`. -/
theorem sum_range_neg_one_pow (k : ℕ) :
    ∑ a ∈ Finset.range (k + k), (-1 : ℂ) ^ a = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + (k + 1) = k + k + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, pow_succ, ← two_mul, pow_mul]
    simp

end Gadget

open Gadget

/-- `v` is real. -/
theorem star_alt (a : Fin m) : star (alt m a) = alt m a := by
  simp [alt, Complex.conj_ofReal]

/-- `v ⊥ u` for even `m`: `Σ_a (-1)^a = 0`, so the `2/m`-part of the gadget
annihilates `v` (the chain construction of Section `part:hsl`). -/
theorem sum_alt (hm : Even m) : ∑ a, alt m a = 0 := by
  obtain ⟨k, rfl⟩ := hm
  simp only [alt, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun a => (-1 : ℂ) ^ a), sum_range_neg_one_pow, zero_div]

/-- The shift part on `v`: for even `m` the queried position
`a - j - 1 mod m` has the parity of `a + j + 1`, so
`v_{a-j-1} = -(-1)^j v_a`. -/
theorem alt_gadgetPos (hm : Even m) (a j : Fin m) :
    alt m (LinearSystems.gadgetPos a j) = -((-1 : ℂ) ^ (j : ℕ) * alt m a) := by
  obtain ⟨k, rfl⟩ := hm
  have hp : ((LinearSystems.gadgetPos a j : ℕ)) % 2 = ((a : ℕ) + j + 1) % 2 := by
    rcases gadgetPos_spec a j with h | h <;> omega
  simp only [alt]
  rw [neg_one_pow_eq_of_mod_two hp, pow_succ, pow_add]
  ring

/-- **`U_x v = (-1)^j v`** (the chain construction of Section `part:hsl`), for even `m`. -/
theorem gadget_mulVec_alt (hm : Even m) (j : Fin m) :
    LinearSystems.gadget m j *ᵥ alt m = (-1 : ℂ) ^ (j : ℕ) • alt m := by
  funext a
  have hsum : ∑ b, alt m b = 0 := sum_alt hm
  have h2 : ∑ b, (if LinearSystems.gadgetPos a b = j then (1 : ℂ) else 0) * alt m b =
      alt m (LinearSystems.gadgetPos a j) := by
    simp only [gadgetPos_eq_iff a _ j, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, LinearSystems.gadget, Matrix.of_apply, sub_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsum, h2, alt_gadgetPos hm, Pi.smul_apply, smul_eq_mul]
  ring

/-- The reverse edge: `U_x† v = (-1)^j v` (unitarity and `((-1)^j)² = 1`). -/
theorem conjTranspose_gadget_mulVec_alt (hm : Even m) (j : Fin m) :
    (LinearSystems.gadget m j)ᴴ *ᵥ alt m = (-1 : ℂ) ^ (j : ℕ) • alt m := by
  have hU := Matrix.mem_unitaryGroup_iff'.mp (LinearSystems.gadget_mem_unitaryGroup j)
  have h1 : (LinearSystems.gadget m j)ᴴ *ᵥ (LinearSystems.gadget m j *ᵥ alt m) = alt m := by
    rw [Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  rw [gadget_mulVec_alt hm, Matrix.mulVec_smul] at h1
  have hc : ((-1 : ℂ) ^ (j : ℕ)) * ((-1 : ℂ) ^ (j : ℕ)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  calc (LinearSystems.gadget m j)ᴴ *ᵥ alt m
      = (((-1 : ℂ) ^ (j : ℕ)) * ((-1 : ℂ) ^ (j : ℕ))) •
          ((LinearSystems.gadget m j)ᴴ *ᵥ alt m) := by
        rw [hc, one_smul]
    _ = (-1 : ℂ) ^ (j : ℕ) • alt m := by rw [mul_smul, h1]

theorem norm_alt (hm0 : 0 < m) : ‖(WithLp.toLp 2 (alt m) : EuclideanSpace ℂ (Fin m))‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hterm : ∀ i, ‖(WithLp.toLp 2 (alt m) : EuclideanSpace ℂ (Fin m)) i‖ ^ 2 =
      1 / (m : ℝ) := by
    intro i
    simp only [alt, norm_div, norm_pow, norm_neg, norm_one, one_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  rw [mul_one_div_cancel hm, Real.sqrt_one]

end

end SparseLowerBounds.Hamiltonian
end
