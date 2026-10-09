import SparseLowerBounds.Query.PhaseOracle
import SparseHamiltonian.LookupControlledGate

set_option autoImplicit false

/-!
# Reversible one-bit lookups are Boolean phase oracles

The search family of corollary `hs:cor:unitary` of the manuscript (lines
1833-1840) has one-bit entries, so its ordinary reversible entry lookup
`|a, z⟩ ↦ |a, z + f a⟩` over `ZMod 2`, with an arbitrary untouched payload
Hilbert space `W` (`SparseHamiltonian.LookupControlledGate.oracle`), is the
Boolean XOR oracle of the string `a ↦ (f a = 1)`. In the phase form of
`SparseLowerBounds.ProjFamily.phase` it is `1 - 2 Σ_{f a = 1} P a` with
`P a = |a⟩⟨a| ⊗ |−⟩⟨−| ⊗ 1_W` (`xorFamily`, `lookup_eq_phase`). The family
`xorFamily` is the construction `|−⟩⟨−|` on the bit of
`SparseLowerBounds.ProjFamily.withAncilla` and
`SparseLowerBounds.Hamiltonian.bitBooleanFamily`, for the `ZMod 2` payload
layout of `SparseHamiltonian.LookupControlledGate.oracle`; those are typed on a
`Fin 2` ancilla in front of the native space and do not apply directly.

A unital star-algebra homomorphism of operator algebras (tensoring with
identities, fixed coordinate changes, direct sums of copies) maps projection
families to projection families and phase oracles to phase oracles of the same
string (`mapFamily`, `phase_map`). This is the exact-identity form of the
spectator transport `SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate`
(the case `Φ A = 1_Ω ⊗ A`, image family `ProjFamily.spectate`). The package's
certificates `SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess` (with
`PhaseAccess.conj`, `PhaseAccess.spectate` and the layers of
`SparseLowerBounds/Helpers/HsRelease/Layers`) transport a cost-bounded
implementation on an encoded subspace through the release simulator's oracle
labels; here the released entry oracle of the unitary-implementation
corollary, a different wrapper stack, is identified with a phase oracle
exactly, so that a program over it is itself a program over a phase oracle with
the same count and no recompilation.
-/

namespace UnitaryImplementationExtensions.PhaseBridge

noncomputable section
open SparseLowerBounds SparseHamiltonian
open ContinuousLinearMap

section Map
variable {K K' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
variable {I : Type*}

/-- The image of a projection family under a star-algebra homomorphism. -/
def mapFamily (Φ : (K →L[ℂ] K) →⋆ₐ[ℂ] (K' →L[ℂ] K')) (P : ProjFamily K I) :
    ProjFamily K' I where
  proj i := Φ (P.proj i)
  isStarProjection i := (P.isStarProjection i).map Φ
  orthogonal i i' h := by rw [← map_mul, P.orthogonal i i' h, map_zero]

/-- A star-algebra homomorphism maps a phase oracle to the phase oracle of the
image family, for the same Boolean string. -/
theorem phase_map [Fintype I] (Φ : (K →L[ℂ] K) →⋆ₐ[ℂ] (K' →L[ℂ] K'))
    (P : ProjFamily K I) (y : I → Bool) :
    Φ (P.phase y) = (mapFamily Φ P).phase y := by
  simp only [ProjFamily.phase, map_sub, map_one, map_smul, map_sum]
  rfl

end Map

section Xor
variable (A W : Type*) [Fintype A] [DecidableEq A]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The address indicator `|a⟩⟨a| ⊗ 1 ⊗ 1_W` on address, bit and payload. -/
def addressIndicator (a : A) :
    PiLp 2 (fun _ : A × ZMod 2 => W) →L[ℂ] PiLp 2 (fun _ : A × ZMod 2 => W) :=
  WeightedClock.diagonal (fun j : A × ZMod 2 => if j.1 = a then (1 : W →L[ℂ] W) else 0)

/-- The bit flip `1 ⊗ X ⊗ 1_W`, a reversible lookup of the constant one. -/
def bitFlip :
    PiLp 2 (fun _ : A × ZMod 2 => W) →L[ℂ] PiLp 2 (fun _ : A × ZMod 2 => W) :=
  LookupControlledGate.oracle (X := Unit) (K := W) (fun _ _ => (1 : ZMod 2)) ()

omit [DecidableEq A] [CompleteSpace W] in
/-- The bit flip moves the bit amplitude by one. -/
@[simp] theorem bitFlip_apply (v : PiLp 2 (fun _ : A × ZMod 2 => W)) (a : A) (z : ZMod 2) :
    bitFlip A W v (a, z) = v (a, z + 1) := by
  have h : ∀ z : ZMod 2, z - 1 = z + 1 := by decide
  simp [bitFlip, h]

omit [Fintype A] [CompleteSpace W] in
/-- The address indicator keeps the amplitudes at address `a`. -/
@[simp] theorem addressIndicator_apply (a : A) (v : PiLp 2 (fun _ : A × ZMod 2 => W))
    (a' : A) (z : ZMod 2) :
    addressIndicator A W a v (a', z) = if a' = a then v (a', z) else 0 := by
  simp only [addressIndicator, WeightedClock.diagonal_apply]
  split_ifs <;> simp

omit [CompleteSpace W] in
/-- Pointwise form of `|a⟩⟨a| (1 - X)`. -/
theorem indicator_flip_apply (a : A) (v : PiLp 2 (fun _ : A × ZMod 2 => W))
    (a' : A) (z : ZMod 2) :
    (addressIndicator A W a * (1 - bitFlip A W)) v (a', z) =
      if a' = a then v (a', z) - v (a', z + 1) else 0 := by
  simp only [_root_.mul_apply_eq_comp, _root_.sub_apply, _root_.one_apply_eq_self,
    PiLp.sub_apply, addressIndicator_apply, bitFlip_apply]

omit [CompleteSpace W] in
/-- The address indicator commutes with the bit flip. -/
theorem indicator_mul_bitFlip (a : A) :
    addressIndicator A W a * bitFlip A W = bitFlip A W * addressIndicator A W a := by
  ext v ⟨a', z⟩
  simp

omit [CompleteSpace W] in
/-- `|a⟩⟨a| (1 - X)` squares to twice itself. -/
theorem indicator_flip_mul_self (a : A) :
    (addressIndicator A W a * (1 - bitFlip A W)) * (addressIndicator A W a * (1 - bitFlip A W)) =
      (2 : ℂ) • (addressIndicator A W a * (1 - bitFlip A W)) := by
  have h11 : ∀ z : ZMod 2, z + 1 + 1 = z := by decide
  ext v ⟨a', z⟩
  rw [_root_.mul_apply_eq_comp]
  simp only [smul_apply, PiLp.smul_apply, indicator_flip_apply]
  split_ifs with h
  · rw [h11, two_smul]
    abel
  · simp

omit [CompleteSpace W] in
/-- Different address indicators with the flip multiply to zero. -/
theorem indicator_flip_mul_of_ne {a a' : A} (h : a ≠ a') :
    (addressIndicator A W a * (1 - bitFlip A W)) * (addressIndicator A W a' * (1 - bitFlip A W)) =
      0 := by
  ext v ⟨b, z⟩
  rw [_root_.mul_apply_eq_comp, indicator_flip_apply, indicator_flip_apply,
    indicator_flip_apply]
  by_cases hb : b = a
  · subst hb
    rw [if_pos rfl, if_neg h, if_neg h, sub_zero]
    simp
  · rw [if_neg hb]
    simp

/-- The XOR projection family `P a = |a⟩⟨a| ⊗ |−⟩⟨−| ⊗ 1_W`, written as
`|a⟩⟨a| (1 - X) / 2`. -/
def xorFamily : ProjFamily (PiLp 2 (fun _ : A × ZMod 2 => W)) A where
  proj a := (2 : ℂ)⁻¹ • (addressIndicator A W a * (1 - bitFlip A W))
  isStarProjection a := by
    have hX : star (bitFlip A W) = bitFlip A W := by
      have h : ∀ z : ZMod 2, z + 1 = z - 1 := by decide
      ext v ⟨a', z⟩
      rw [star_eq_adjoint, bitFlip, LookupControlledGate.oracle_adjoint_apply,
        LookupControlledGate.oracle_apply, h]
    have hD : star (addressIndicator A W a) = addressIndicator A W a := by
      rw [star_eq_adjoint, addressIndicator, WeightedClock.diagonal_adjoint]
      congr 1
      funext j
      split_ifs
      · exact adjoint_id
      · exact map_zero _
    refine ⟨?_, ?_⟩
    · rw [IsIdempotentElem, smul_mul_smul_comm, indicator_flip_mul_self, smul_smul]
      norm_num
    · rw [IsSelfAdjoint, star_smul, star_mul, hD, star_sub, star_one, hX, sub_mul, mul_sub,
        one_mul, mul_one, indicator_mul_bitFlip, star_inv₀, star_ofNat]
  orthogonal a a' h := by
    rw [smul_mul_smul_comm, indicator_flip_mul_of_ne A W h, smul_zero]

variable {A W}

/-- **The one-bit reversible lookup is the XOR phase oracle.** -/
theorem lookup_eq_phase {X : Type*} (f : X → A → ZMod 2) (x : X) :
    LookupControlledGate.oracle (K := W) f x =
      (xorFamily A W).phase (fun a => decide (f x a = 1)) := by
  ext v ⟨a, z⟩
  simp only [ProjFamily.phase, xorFamily, sub_apply, _root_.one_apply_eq_self, smul_apply,
    _root_.sum_apply, PiLp.sub_apply, PiLp.smul_apply, WithLp.ofLp_sum,
    Finset.sum_apply, indicator_flip_apply, LookupControlledGate.oracle_apply, smul_ite,
    smul_zero, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq]
  have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have h1 : ∀ z : ZMod 2, z - 1 = z + 1 := by decide
  rcases hc (f x a) with h | h
  · rw [h, sub_zero, if_neg (by decide), sub_zero]
  · rw [h, if_pos rfl, smul_smul, h1]
    norm_num

end Xor

end
end UnitaryImplementationExtensions.PhaseBridge
