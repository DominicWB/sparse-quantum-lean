import SparseHamiltonian.AveragingResolvent

/-!
# Exact period of the concrete cyclic clock

One complete circuit applies the return map `i O` independently in every slot.
For an involution `O`, two circuits therefore give minus the identity.  These
identities are algebraic and do not assume finite-dimensionality or a norm.
-/

namespace SparseHamiltonian.CyclicClock

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Before crossing the return edge, powers simply shift the slot index. -/
theorem clockStep_pow_apply_of_le (O : V →ₗ[ℂ] V) (q n : ℕ)
    (x : Fin (q + 1) → V) (j : Fin (q + 1)) (hn : n ≤ j.val) :
    (clockStep O q ^ n) x j = x ⟨j.val - n, by omega⟩ := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    obtain ⟨jv, hjv⟩ := j
    cases jv with
    | zero => simp at hn
    | succ jv =>
      rw [pow_succ', Module.End.mul_apply]
      change (clockStep O q ^ n) x (⟨jv, by omega⟩ : Fin (q + 1)) = _
      rw [ih _ (by simpa using hn)]
      apply congrArg x
      apply Fin.ext
      simp

/-- A full circuit applies the return map at every clock slot. -/
theorem clockStep_pow_cycle_apply (O : V →ₗ[ℂ] V) (q : ℕ)
    (x : Fin (q + 1) → V) (j : Fin (q + 1)) :
    (clockStep O q ^ (q + 1)) x j = Complex.I • O (x j) := by
  have hsplit : q + 1 = j.val + (q - j.val + 1) := by omega
  have hpow := congrArg (fun n : ℕ => clockStep O q ^ n) hsplit
  rw [hpow, pow_add, Module.End.mul_apply,
    clockStep_pow_apply_of_le O q j.val _ j (le_refl _)]
  simp only [Nat.sub_self]
  rw [pow_succ', Module.End.mul_apply]
  change Complex.I • O ((clockStep O q ^ (q - j.val)) x (Fin.last q)) = _
  rw [clockStep_pow_apply_of_le O q (q - j.val) x (Fin.last q) (by simp)]
  congr 2
  apply congrArg x
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- Two complete circuits equal minus the identity for an involutory return map. -/
theorem clockStep_pow_two_cycles (O : V →ₗ[ℂ] V) (q : ℕ)
    (hO : ∀ v, O (O v) = v) :
    clockStep O q ^ (2 * (q + 1)) = -1 := by
  apply LinearMap.ext
  intro x
  funext j
  rw [two_mul, pow_add, Module.End.mul_apply,
    clockStep_pow_cycle_apply, clockStep_pow_cycle_apply]
  simp only [map_smul, hO, smul_smul, Complex.I_mul_I]
  simp

end SparseHamiltonian.CyclicClock
