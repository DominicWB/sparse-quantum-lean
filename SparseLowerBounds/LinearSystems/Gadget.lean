import SparseLowerBounds.Query.Ancilla

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The one-bit gadget `U_j`

Manuscript: the construction in the proof of Theorem `qlsl:thm:main` (`qlsl:eq:gadget`,
`qlsl:eq:logical`, `qlsl:eq:entries`). For a one-hot string `x = e_j` of length `m`, the gadget is
`U_x = S^{j+1} G` with the cyclic shift `S` and `G = 2|u⟩⟨u| - I`. We define it
directly by its entry formula (eq. `qlsl:eq:entries`)

  `(U_j)_{a b} = 2/m - [a - b - 1 ≡ j (mod m)]`,

which is how the reduction accesses it: entry `(a, b)` depends on exactly one
bit of the one-hot string, the bit at position `gadgetPos a b = a - b - 1 mod m`.

* `gadget_mem_unitaryGroup`: `U_j` is unitary, and it is real
  (`star_gadget_apply`), hence real orthogonal;
* `gadget_mulVec_logical`: for even `m`, `U_j |z_L⟩ = |(z ⊕ (j mod 2))_L⟩`
  (eq. `qlsl:eq:logical`), with
  `|0_L⟩ = √(2/m) Σ_{a even} |a⟩`, `|1_L⟩ = √(2/m) Σ_{a odd} |a⟩`;
* `gadget_apply_ne_zero`: for `m ≥ 3` every entry is nonzero, so the support is
  the full `m × m` block, independent of `j`.
-/

namespace SparseLowerBounds.LinearSystems

noncomputable section
open scoped Matrix

variable {m : ℕ}

/-- The queried position of entry `(a, b)`: `a - b - 1 mod m`. -/
def gadgetPos (a b : Fin m) : Fin m :=
  ⟨((a : ℕ) + (m - 1 - b)) % m, Nat.mod_lt _ a.pos⟩

/-- **Eq. `qlsl:eq:entries`** (eq. `qlsl:eq:entries`): `(U_j)_{ab} = 2/m - [a - b - 1 ≡ j]`. -/
def gadget (m : ℕ) (j : Fin m) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun a b => (2 / m : ℂ) - if gadgetPos a b = j then 1 else 0

/-- The logical basis state `|z_L⟩ = √(2/m) Σ_{a ≡ z (mod 2)} |a⟩`. -/
def logical (m : ℕ) (z : Bool) : Fin m → ℂ :=
  fun a => if decide ((a : ℕ) % 2 = 1) = z then (Real.sqrt (2 / m) : ℂ) else 0

/-! ### Index arithmetic for `gadgetPos` -/

/-- `gadgetPos a b + b + 1 ≡ a (mod m)`, as an equation in `ℕ` usable by `omega`. -/
theorem gadgetPos_spec (a b : Fin m) :
    (gadgetPos a b : ℕ) + b + 1 = a ∨ (gadgetPos a b : ℕ) + b + 1 = a + m := by
  have ha := a.isLt
  have hb := b.isLt
  unfold gadgetPos
  simp only
  rcases lt_or_ge ((a : ℕ) + (m - 1 - b)) m with h | h
  · rw [Nat.mod_eq_of_lt h]; right; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; left; omega

/-- For fixed `a`, `b ↦ gadgetPos a b` is an involution: exactly one `b` queries bit `j`. -/
theorem gadgetPos_eq_iff (a b j : Fin m) : gadgetPos a b = j ↔ b = gadgetPos a j := by
  have ha := a.isLt
  have hb := b.isLt
  have hj := j.isLt
  rcases gadgetPos_spec a b with h1 | h1 <;> rcases gadgetPos_spec a j with h2 | h2 <;>
  · simp only [Fin.ext_iff]
    have := (gadgetPos a b).isLt
    have := (gadgetPos a j).isLt
    omega

/-- `a ↦ gadgetPos a j` is injective. -/
theorem gadgetPos_inj (a c j : Fin m) : gadgetPos a j = gadgetPos c j ↔ a = c := by
  have ha := a.isLt
  have hc := c.isLt
  have hj := j.isLt
  rcases gadgetPos_spec a j with h1 | h1 <;> rcases gadgetPos_spec c j with h2 | h2 <;>
  · simp only [Fin.ext_iff]
    have := (gadgetPos a j).isLt
    have := (gadgetPos c j).isLt
    omega

/-- For even `m`, the parity of `gadgetPos a b + b + 1` is that of `a`. -/
theorem gadgetPos_mod_two (k : ℕ) (a b : Fin (k + k)) :
    ((gadgetPos a b : ℕ) + b + 1) % 2 = (a : ℕ) % 2 := by
  rcases gadgetPos_spec a b with h | h <;> omega

/-- Each parity class of `Fin (2k)` has `k` elements. -/
theorem sum_parity {R : Type*} [AddCommMonoid R] (k : ℕ) (z : Bool) (c : R) :
    ∑ a : Fin (k + k), (if decide ((a : ℕ) % 2 = 1) = z then c else 0) = k • c := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if decide (a % 2 = 1) = z then c else 0)]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show k + 1 + (k + 1) = k + k + 1 + 1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    have h1 : (k + k) % 2 = 0 := by omega
    have h2 : (k + k + 1) % 2 = 1 := by omega
    cases z <;> simp [h1, h2, succ_nsmul]

/-- Gram entry of two columns `x - e_p`, `x - e_q` of the gadget shape. -/
theorem sum_sub_ite_mul_sub_ite (p q : Fin m) (x : ℂ) :
    ∑ b : Fin m, (x - if b = p then 1 else 0) * (x - if b = q then 1 else 0) =
      m * x ^ 2 - 2 * x + if p = q then 1 else 0 := by
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one, one_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  by_cases h : p = q
  · subst h; simp; ring
  · simp [h, Ne.symm h]; ring

theorem star_gadget_apply_aux (j : Fin m) (a b : Fin m) :
    star (gadget m j a b) = gadget m j a b := by
  simp only [gadget, Matrix.of_apply]
  split_ifs <;> simp

/-- `U_j` is unitary (proof of Theorem `qlsl:thm:main`: `S` and `G` are unitary). -/
theorem gadget_mem_unitaryGroup (j : Fin m) : gadget m j ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext a c
  have hm : (m : ℂ) ≠ 0 := by have := a.pos; exact_mod_cast (by omega : m ≠ 0)
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, star_gadget_apply_aux]
  simp only [gadget, Matrix.of_apply, gadgetPos_eq_iff _ _ j]
  rw [sum_sub_ite_mul_sub_ite, Matrix.one_apply]
  have : (m : ℂ) * (2 / m) ^ 2 - 2 * (2 / m) = 0 := by field_simp; ring
  rw [this, zero_add]
  simp only [gadgetPos_inj]

/-- `U_j` has real entries. -/
theorem star_gadget_apply (j : Fin m) (a b : Fin m) : star (gadget m j a b) = gadget m j a b := by
  exact star_gadget_apply_aux j a b

/-- The logical states are unit vectors for even positive `m`. -/
theorem norm_logical (hm : Even m) (hm0 : 0 < m) (z : Bool) :
    ‖WithLp.toLp 2 (logical m z)‖ = 1 := by
  obtain ⟨k, rfl⟩ := hm
  rw [EuclideanSpace.norm_eq]
  have hterm : ∀ i, ‖logical (k + k) z i‖ ^ 2 =
      if decide ((i : ℕ) % 2 = 1) = z then (2 / ((k + k : ℕ) : ℝ)) else 0 := by
    intro i
    unfold logical
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt (by positivity)]
    · simp
  simp only [hterm, sum_parity]
  rw [Real.sqrt_eq_one, nsmul_eq_mul]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  push_cast
  field_simp
  ring

/-- **Eq. `qlsl:eq:logical`** (proof of Theorem `qlsl:thm:main`): for even `m`,
`U_j |z_L⟩ = |(z ⊕ (j mod 2))_L⟩`, with no global phase. -/
theorem gadget_mulVec_logical (hm : Even m) (j : Fin m) (z : Bool) :
    gadget m j *ᵥ logical m z = logical m (xor z (decide ((j : ℕ) % 2 = 1))) := by
  obtain ⟨k, rfl⟩ := hm
  funext a
  have hk : (k : ℂ) ≠ 0 := by have := a.pos; exact_mod_cast (by omega : k ≠ 0)
  have hsum : ∑ b, logical (k + k) z b = k • (Real.sqrt (2 / ((k + k : ℕ) : ℝ)) : ℂ) :=
    sum_parity k z _
  have h2 : ∑ b, (if gadgetPos a b = j then (1 : ℂ) else 0) * logical (k + k) z b =
      logical (k + k) z (gadgetPos a j) := by
    simp only [gadgetPos_eq_iff a _ j, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, gadget, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [hsum, h2]
  have hs : (2 / ((k + k : ℕ) : ℂ)) * (k • (Real.sqrt (2 / ((k + k : ℕ) : ℝ)) : ℂ)) =
      (Real.sqrt (2 / ((k + k : ℕ) : ℝ)) : ℂ) := by
    rw [nsmul_eq_mul, show ((k + k : ℕ) : ℂ) = 2 * k by push_cast; ring]
    field_simp
  rw [hs]
  have hp := gadgetPos_mod_two k a j
  unfold logical
  rcases Nat.mod_two_eq_zero_or_one (a : ℕ) with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one (j : ℕ) with hj | hj
  · have hq : (gadgetPos a j : ℕ) % 2 = 1 := by omega
    cases z <;> simp [ha, hj, hq]
  · have hq : (gadgetPos a j : ℕ) % 2 = 0 := by omega
    cases z <;> simp [ha, hj, hq]
  · have hq : (gadgetPos a j : ℕ) % 2 = 0 := by omega
    cases z <;> simp [ha, hj, hq]
  · have hq : (gadgetPos a j : ℕ) % 2 = 1 := by omega
    cases z <;> simp [ha, hj, hq]

/-- All entries are nonzero for `m ≥ 3` (proof of Theorem `qlsl:thm:main`; the manuscript uses
`m ≥ 4`), so the support is the whole block for every `j`. -/
theorem gadget_apply_ne_zero (hm : 3 ≤ m) (j : Fin m) (a b : Fin m) : gadget m j a b ≠ 0 := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  simp only [gadget, Matrix.of_apply]
  split_ifs
  · rw [sub_ne_zero]
    intro h
    rw [div_eq_one_iff_eq hm0] at h
    norm_cast at h
    omega
  · simpa using hm0

end

end SparseLowerBounds.LinearSystems
end
