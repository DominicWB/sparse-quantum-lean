import GateEfficientHamiltonian.GateWalshWords
/-!
The word circuit's coefficient is identified with the normalisation used
by the released Hilbert-space uniform embedding.  This includes the empty
word register.  Relabelling is by the proved little-endian equivalence,
and the preparation identity is linear in an arbitrary payload.
-/

namespace SparseHamiltonian.GateWalshWords

noncomputable section

theorem half_nonneg : 0 ≤ half := by
  unfold half
  exact le_of_lt (one_div_pos.mpr (GateDyadicBoundary.rootDenominator_pos 1))

theorem half_sq : half ^ 2 = (2 : ℝ)⁻¹ := by
  have h := half_unit
  norm_num at h ⊢
  nlinarith

/-- The normalisation follows from nonnegativity and the square, without
assuming a whole-register preparation operation. -/
theorem half_pow_eq_uniformAmplitude (r : ℕ) :
    half ^ r = CoherentReuse.uniformAmplitude (2 ^ r) := by
  apply (sq_eq_sq₀ (pow_nonneg half_nonneg r) (by
    unfold CoherentReuse.uniformAmplitude
    positivity)).mp
  calc
    (half ^ r) ^ 2 = (half ^ 2) ^ r := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm r 2]
    _ = ((2 : ℝ)⁻¹) ^ r := by rw [half_sq]
    _ = ((2 ^ r : ℕ) : ℝ)⁻¹ := by simp [inv_pow]
    _ = CoherentReuse.uniformAmplitude (2 ^ r) ^ 2 :=
      (CoherentReuse.uniformAmplitude_sq (2 ^ r)).symm

theorem complex_half_pow_eq_uniformAmplitude (r : ℕ) :
    (half : ℂ) ^ r = (CoherentReuse.uniformAmplitude (2 ^ r) : ℂ) := by
  exact_mod_cast half_pow_eq_uniformAmplitude r

/-- The only relabelling used here is the concrete unsigned binary value. -/
def relabelCoordinates (f : State r) (j : Fin (2 ^ r)) : ℂ :=
  f ((GatePointerEncoding.wordEquivFin r).symm j)

theorem relabelCoordinates_prepares_uniform (r : ℕ) :
    relabelCoordinates (run (circuit r le_rfl) zeroState) =
      fun _ : Fin (2 ^ r) => (CoherentReuse.uniformAmplitude (2 ^ r) : ℂ) := by
  rw [circuit_prepares_constant]
  funext j
  exact complex_half_pow_eq_uniformAmplitude r

theorem wordEquivFin_zeroWord (r : ℕ) :
    (GatePointerEncoding.wordEquivFin r (zeroWord r)).val = 0 := by
  change GatePointerEncoding.wordValue (GatePointerEncoding.zeroWord r) = 0
  exact GatePointerEncoding.wordValue_zero r

theorem inverse_word_eq_zero_iff (j : Fin (2 ^ r)) :
    (GatePointerEncoding.wordEquivFin r).symm j = zeroWord r ↔ j.val = 0 := by
  constructor
  · intro h
    have he := congrArg (GatePointerEncoding.wordEquivFin r) h
    have hv := congrArg Fin.val he
    simpa only [Equiv.apply_symm_apply, wordEquivFin_zeroWord] using hv
  · intro h
    apply (GatePointerEncoding.wordEquivFin r).injective
    apply Fin.ext
    simpa only [Equiv.apply_symm_apply, wordEquivFin_zeroWord] using h

theorem relabelCoordinates_zeroState (r : ℕ) :
    relabelCoordinates (zeroState (r := r)) =
      fun j : Fin (2 ^ r) => if j.val = 0 then 1 else 0 := by
  funext j
  simp only [relabelCoordinates, zeroState, inverse_word_eq_zero_iff]

/-- Coordinate preparation carries arbitrary payload amplitudes unchanged.
The subsequent Hilbert-space construction proves that these coordinates
are realised by the bounded-arity gate list. -/
theorem relabelCoordinates_prepares_payload {E : Type*}
    [AddCommMonoid E] [Module ℂ E] (r : ℕ) (v : E) (j : Fin (2 ^ r)) :
    relabelCoordinates (run (circuit r le_rfl) zeroState) j • v =
      (CoherentReuse.uniformAmplitude (2 ^ r) : ℂ) • v := by
  rw [relabelCoordinates_prepares_uniform]

end
end SparseHamiltonian.GateWalshWords
