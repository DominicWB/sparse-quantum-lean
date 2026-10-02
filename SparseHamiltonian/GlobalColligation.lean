import SparseHamiltonian.TimeSchedule

/-!
# The full finite chronological colligation

The public exit and private chronological block are assembled into an actual
linear isometry on the Hilbert direct sum. Its Gram identities follow from
the local energy law, rather than being additional promises.
-/

namespace SparseHamiltonian.GlobalColligation

noncomputable section

open ContinuousLinearMap
open SparseHamiltonian.ChronologicalResolvent
open SparseHamiltonian.ChronologicalCatalyst
open SparseHamiltonian.FiniteChronologicalInverse
open scoped BigOperators InnerProduct

section Normed

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The finite public exit from a zero initial public state. -/
def publicExit (u : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ) :
    BlockOperator.H T V →L[ℂ] P :=
  ∑ k : Fin T, (u ^ (T - 1 - (k : ℕ))) ∘L B ∘L PiLp.proj 2 (fun _ : Fin T => V) k

theorem publicExit_apply (u : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ)
    (x : BlockOperator.H T V) :
    publicExit u B T x = forcedPublicState u B (extendSequence x) T := by
  rw [forcedPublicState_eq_sum, ← Fin.sum_univ_eq_sum_range]
  simp [publicExit, sum_apply, extendSequence_apply]

/-- The exit depends only on the finite input prefix. -/
theorem publicExit_restrict (u : P →L[ℂ] P) (B : V →L[ℂ] P) (T : ℕ)
    (y : ℕ → V) :
    publicExit u B T (restrictSequence T y) = forcedPublicState u B y T := by
  rw [forcedPublicState_eq_sum, ← Fin.sum_univ_eq_sum_range]
  simp [publicExit, sum_apply, restrictSequence_apply]

/-- The public action of the stacked catalyst is exactly the corresponding
power of the local public action. -/
theorem catalyst_public_transduction (Γ : P →L[ℂ] V) (U u : P →L[ℂ] P)
    (B : V →L[ℂ] P) (hPublic : u + B ∘L Γ = U) (T : ℕ) :
    u ^ T + publicExit u B T ∘L stackedResponse Γ U T = U ^ T := by
  ext p
  change (u ^ T) p + publicExit u B T
    (restrictSequence T (fun k => Γ ((U ^ k) p))) = (U ^ T) p
  rw [publicExit_restrict]
  exact catalyst_publicState Γ U u B hPublic p T

/-- Exact energy conservation with arbitrary initial public state. -/
theorem chronological_energy_sum_initial (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (y : ℕ → V) (p : P) (T : ℕ) :
    (∑ k ∈ Finset.range T, ‖R (y k) + A (publicState u B y p k)‖ ^ 2) +
      ‖publicState u B y p T‖ ^ 2 =
      (∑ k ∈ Finset.range T, ‖y k‖ ^ 2) + ‖p‖ ^ 2 := by
  induction T with
  | zero => simp
  | succ T hT =>
      have h := hStep (y T) (publicState u B y p T)
      rw [← publicState_succ] at h
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith

/-- The full energy law for the concrete finite blocks. -/
theorem chronological_full_energy (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (T : ℕ) (p : P) (x : BlockOperator.H T V) :
    ‖(u ^ T) p + publicExit u B T x‖ ^ 2 +
      ‖stackedResponse A u T p + chronologicalOperator R A u B T x‖ ^ 2 =
      ‖p‖ ^ 2 + ‖x‖ ^ 2 := by
  have h := chronological_energy_sum_initial R A u B hStep (extendSequence x) p T
  have hcoord (k : Fin T) :
      (stackedResponse A u T p + chronologicalOperator R A u B T x) k =
        R (extendSequence x k) + A (publicState u B (extendSequence x) p k) := by
    have hh := chronologicalOperator_apply R A u B (extendSequence x) k
    change chronologicalOperator R A u B T (restrictSequence T (extendSequence x)) k = _ at hh
    rw [restrict_extend] at hh
    simp only [PiLp.add_apply, stackedResponse_apply, hh, chronologicalPrivateState,
      publicState, map_add]
    abel
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp_rw [hcoord]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ‖R (extendSequence x k) + A (publicState u B (extendSequence x) p k)‖ ^ 2) T]
  have hin : (∑ k : Fin T, ‖x k‖ ^ 2) =
      ∑ k ∈ Finset.range T, ‖extendSequence x k‖ ^ 2 := by
    simpa only [extendSequence_apply] using
      (Fin.sum_univ_eq_sum_range (fun k => ‖extendSequence x k‖ ^ 2) T)
  rw [hin, publicExit_apply]
  change ‖publicState u B (extendSequence x) p T‖ ^ 2 + _ = _
  linarith

/-- A block map on the genuine Hilbert product, whose norm is the square root
of the sum of the two squared norms. -/
def blockMap {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (A : P →L[ℂ] P) (B : Q →L[ℂ] P) (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q) :
    WithLp 2 (P × Q) →L[ℂ] WithLp 2 (P × Q) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ P Q).symm.toContinuousLinearMap ∘L
    ((A ∘L WithLp.fstL 2 ℂ P Q + B ∘L WithLp.sndL 2 ℂ P Q).prod
      (C ∘L WithLp.fstL 2 ℂ P Q + D ∘L WithLp.sndL 2 ℂ P Q))

@[simp] theorem blockMap_apply {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (A : P →L[ℂ] P) (B : Q →L[ℂ] P) (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q)
    (x : WithLp 2 (P × Q)) :
    blockMap A B C D x = WithLp.toLp 2 (A x.fst + B x.snd, C x.fst + D x.snd) := rfl

/-- An exact two-output energy law proves norm preservation on the Hilbert
product, including when one of the component spaces is zero. -/
theorem blockMap_norm {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    (A : P →L[ℂ] P) (B : Q →L[ℂ] P) (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q)
    (hEnergy : ∀ p x, ‖A p + B x‖ ^ 2 + ‖C p + D x‖ ^ 2 = ‖p‖ ^ 2 + ‖x‖ ^ 2)
    (x : WithLp 2 (P × Q)) : ‖blockMap A B C D x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simpa only [WithLp.prod_norm_sq_eq_of_L2, blockMap_apply, WithLp.fst,
    WithLp.snd] using hEnergy x.fst x.snd

/-- The actual complete chronology preserves its Hilbert norm. -/
theorem chronological_blockMap_norm (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (T : ℕ) (x : WithLp 2 (P × BlockOperator.H T V)) :
    ‖blockMap (u ^ T) (publicExit u B T) (stackedResponse A u T)
      (chronologicalOperator R A u B T) x‖ = ‖x‖ :=
  blockMap_norm _ _ _ _ (chronological_full_energy R A u B hStep T) x

end Normed

section Hilbert

variable {P Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
variable [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The public-column Gram identity follows from total energy conservation. -/
theorem block_gram_public (A : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q)
    (hEnergy : ∀ p x, ‖A p + B x‖ ^ 2 + ‖C p + D x‖ ^ 2 = ‖p‖ ^ 2 + ‖x‖ ^ 2) :
    A† ∘L A + C† ∘L C = 1 := by
  have hInner := (LinearMap.norm_map_iff_inner_map_map (blockMap A B C D)).mp
    (blockMap_norm A B C D hEnergy)
  ext p
  apply ext_inner_right ℂ
  intro q
  have h := hInner (WithLp.toLp 2 (p, (0 : Q))) (WithLp.toLp 2 (q, (0 : Q)))
  simpa only [blockMap_apply, WithLp.prod_inner_apply, WithLp.fst,
    WithLp.snd, map_zero, add_zero, inner_zero_left, add_apply, comp_apply,
    inner_add_left, adjoint_inner_left, one_def, id_apply] using h

/-- Orthogonality of the two columns is derived by polarization of the energy
law on the actual Hilbert product. -/
theorem block_gram_mixed (A : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q)
    (hEnergy : ∀ p x, ‖A p + B x‖ ^ 2 + ‖C p + D x‖ ^ 2 = ‖p‖ ^ 2 + ‖x‖ ^ 2) :
    A† ∘L B + C† ∘L D = 0 := by
  have hInner := (LinearMap.norm_map_iff_inner_map_map (blockMap A B C D)).mp
    (blockMap_norm A B C D hEnergy)
  ext x
  apply ext_inner_right ℂ
  intro p
  have h := hInner (WithLp.toLp 2 ((0 : P), x)) (WithLp.toLp 2 (p, (0 : Q)))
  simpa only [blockMap_apply, WithLp.prod_inner_apply, WithLp.fst,
    WithLp.snd, map_zero, add_zero, zero_add, inner_zero_left, inner_zero_right,
    add_apply, comp_apply, inner_add_left, adjoint_inner_left, zero_apply] using h

/-- The private-column Gram identity follows from total energy conservation. -/
theorem block_gram_private (A : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q)
    (hEnergy : ∀ p x, ‖A p + B x‖ ^ 2 + ‖C p + D x‖ ^ 2 = ‖p‖ ^ 2 + ‖x‖ ^ 2) :
    B† ∘L B + D† ∘L D = 1 := by
  have hInner := (LinearMap.norm_map_iff_inner_map_map (blockMap A B C D)).mp
    (blockMap_norm A B C D hEnergy)
  ext x
  apply ext_inner_right ℂ
  intro y
  have h := hInner (WithLp.toLp 2 ((0 : P), x)) (WithLp.toLp 2 ((0 : P), y))
  simpa only [blockMap_apply, WithLp.prod_inner_apply, WithLp.fst,
    WithLp.snd, map_zero, zero_add, inner_zero_left, add_apply, comp_apply,
    inner_add_left, adjoint_inner_left, one_def, id_apply] using h

/-- In finite dimension, norm preservation also proves coisometry; no
surjectivity or reverse Gram identity needs to be promised separately. -/
theorem coisometry_of_norm_preserving [FiniteDimensional ℂ P]
    (U : P →L[ℂ] P) (hU : ∀ p, ‖U p‖ = ‖p‖) : U ∘L U† = 1 := by
  have hLeft := U.norm_map_iff_adjoint_comp_self.mp hU
  have hInj : Function.Injective U := by
    intro x y hxy
    have hx := congrArg (fun L : P →L[ℂ] P => L x) hLeft
    have hy := congrArg (fun L : P →L[ℂ] P => L y) hLeft
    simp only [comp_apply, one_def, id_apply, hxy] at hx hy
    exact hx.symm.trans hy
  have hSurj : Function.Surjective U :=
    (LinearMap.injective_iff_surjective (f := U.toLinearMap)).mp hInj
  ext x
  obtain ⟨y, rfl⟩ := hSurj x
  have h := congrArg (fun L : P →L[ℂ] P => U (L y)) hLeft
  simpa only [comp_apply, one_def, id_apply] using h

/-- The concrete finite block map is two-sided unitary in finite dimension. -/
theorem blockMap_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ Q]
    (A : P →L[ℂ] P) (B : Q →L[ℂ] P) (C : P →L[ℂ] Q) (D : Q →L[ℂ] Q)
    (hEnergy : ∀ p x, ‖A p + B x‖ ^ 2 + ‖C p + D x‖ ^ 2 = ‖p‖ ^ 2 + ‖x‖ ^ 2) :
    (blockMap A B C D)† ∘L blockMap A B C D = 1 ∧
      blockMap A B C D ∘L (blockMap A B C D)† = 1 := by
  exact ⟨(blockMap A B C D).norm_map_iff_adjoint_comp_self.mp
    (blockMap_norm A B C D hEnergy),
    coisometry_of_norm_preserving (blockMap A B C D) (blockMap_norm A B C D hEnergy)⟩

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- All three column Gram identities for the actual chronological blocks. -/
theorem chronological_gram (R : V →L[ℂ] V) (A : P →L[ℂ] V)
    (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (T : ℕ) :
    (u ^ T)† ∘L (u ^ T) + (stackedResponse A u T)† ∘L stackedResponse A u T = 1 ∧
    (u ^ T)† ∘L publicExit u B T +
      (stackedResponse A u T)† ∘L chronologicalOperator R A u B T = 0 ∧
    (publicExit u B T)† ∘L publicExit u B T +
      (chronologicalOperator R A u B T)† ∘L chronologicalOperator R A u B T = 1 := by
  have hEnergy := chronological_full_energy R A u B hStep T
  exact ⟨block_gram_public _ _ _ _ hEnergy,
    block_gram_mixed _ _ _ _ hEnergy, block_gram_private _ _ _ _ hEnergy⟩

/-- The full finite chronology is unitary on its actual Hilbert state space. -/
theorem chronological_blockMap_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (R : V →L[ℂ] V) (A : P →L[ℂ] V) (u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖R x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖p‖ ^ 2) (T : ℕ) :
    let M := blockMap (u ^ T) (publicExit u B T) (stackedResponse A u T)
      (chronologicalOperator R A u B T)
    M† ∘L M = 1 ∧ M ∘L M† = 1 := by
  exact blockMap_unitary _ _ _ _ (chronological_full_energy R A u B hStep T)

end Hilbert

end

end SparseHamiltonian.GlobalColligation
