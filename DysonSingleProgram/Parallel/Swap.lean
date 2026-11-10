import DysonSingleProgram.Coherent

set_option autoImplicit false

/-!
# Parking an attempt register

Manuscript: the proof of Lemma `odel:lem:dyson` and Section `odel:sec:main`
(known gates are free). The four attempts of the
released wrapper act on separate registers; the oracle acts on one main register. After an
attempt on the main register `V = ℂ^M ⊗ W` (cutoff label and workspace), the fixed unitary
`swapMain` exchanges the main register with a parking register `ℂ^{M × d}` (`d = dim W`) that
holds the coordinates of `V` in the basis `|j⟩ ⊗ b_c` (`b = stdOrthonormalBasis ℂ W`, the
coordinates of `Release.tens`). It permutes the orthonormal basis `|a⟩ ⊗ |i⟩ ⊗ |j⟩ ⊗ b_c` of
`ℂ^{M × d} ⊗ (ℂ^I ⊗ V)` (`b = stdOrthonormalBasis ℂ W`, which need not be the computational basis
of `W`); it is a fixed, query-free unitary.

* `coordV a`, `basisV a`: coordinates and basis vectors of `V`, `a = (j, c)`; `coordV_apply`,
  `coordV_basisV`, `inner_basisV_left`, `inner_basisV_right`, `sum_coordV_smul_basisV`: they
  form an orthonormal basis with its coordinate functionals;
* `swapMain I`: the swap on `ℂ^{M × d} ⊗ (ℂ^I ⊗ V)`, the register `I` a spectator;
  `swapMain_apply`, `swapMain_swapMain`, `inner_swapMain`: its action in coordinates, it is an
  involution and it is symmetric;
* `swapMain_unitary`, `swapMain_tens`: it is unitary and exchanges the parked vector with the
  main vector of a product state: `u ⊗ (ω ⊗ v) ↦ v ⊗ (ω ⊗ u)`.
-/

namespace DysonSingleProgram.Parallel

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open scoped InnerProduct InnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- The coordinate register of one attempt register `ℂ^M ⊗ W`: cutoff label and a coordinate of
`W` in `stdOrthonormalBasis ℂ W`. -/
abbrev Coord (M : ℕ) (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] : Type :=
  Fin M × Fin (Module.finrank ℂ W)

variable {M : ℕ}

/-- The coordinate `a = (j, c)` of `v ∈ ℂ^M ⊗ W`: the `c`-th coordinate of `v j`. -/
def coordV (a : Coord M W) : Joint (Fin M) W →L[ℂ] ℂ :=
  EuclideanSpace.proj a.2 ∘L
    (stdOrthonormalBasis ℂ W).repr.toLinearIsometry.toContinuousLinearMap ∘L Joint.proj a.1

/-- The basis vector `|j⟩ ⊗ b_c` of `ℂ^M ⊗ W`. -/
def basisV (a : Coord M W) : Joint (Fin M) W :=
  WithLp.toLp 2 (Pi.single a.1 (stdOrthonormalBasis ℂ W a.2))

/-- **The parking swap** on `ℂ^{M × d} ⊗ (ℂ^I ⊗ (ℂ^M ⊗ W))`: exchanges the parking register
with the coordinates of the main register, the register `I` a spectator. -/
def swapMain (I : Type) [Fintype I] :
    Joint (Coord M W) (Joint I (Joint (Fin M) W)) →L[ℂ]
      Joint (Coord M W) (Joint I (Joint (Fin M) W)) :=
  Joint.mk fun a => ∑ a' : Coord M W,
    Joint.fiber (fun _ : I => (coordV a).smulRight (basisV a')) ∘L Joint.proj a'

omit [CompleteSpace W] in
/-- The coordinate `a = (j, c)` is the `c`-th coordinate of `v j`. -/
theorem coordV_apply (a : Coord M W) (v : Joint (Fin M) W) :
    coordV a v = (stdOrthonormalBasis ℂ W).repr (v a.1) a.2 := rfl

omit [CompleteSpace W] in
/-- The coordinates of the basis vectors. -/
theorem coordV_basisV (a a' : Coord M W) :
    coordV a (basisV a') = if a' = a then 1 else 0 := by
  obtain ⟨j, c⟩ := a
  obtain ⟨j', c'⟩ := a'
  rw [coordV_apply]
  by_cases hj : j' = j
  · subst hj
    simp [basisV, OrthonormalBasis.repr_self, eq_comm]
  · simp [basisV, Ne.symm hj, hj]

omit [CompleteSpace W] in
/-- `⟪|j⟩ ⊗ b_c, v⟫` is the coordinate `(j, c)` of `v`. -/
theorem inner_basisV_left (a : Coord M W) (v : Joint (Fin M) W) :
    ⟪basisV a, v⟫_ℂ = coordV a v := by
  rw [coordV_apply, OrthonormalBasis.repr_apply_apply, PiLp.inner_apply,
    Finset.sum_eq_single a.1]
  · simp [basisV]
  · intro j _ hj
    simp [basisV, hj]
  · simp

omit [CompleteSpace W] in
/-- Basis expansion in `ℂ^M ⊗ W`: `Σ_a coordV a v • basisV a = v`. -/
theorem sum_coordV_smul_basisV (v : Joint (Fin M) W) :
    ∑ a : Coord M W, coordV a v • basisV a = v := by
  ext j
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    Fintype.sum_prod_type, coordV_apply, basisV, Pi.single_apply]
  rw [Finset.sum_eq_single j]
  · simpa using (stdOrthonormalBasis ℂ W).sum_repr (v j)
  · intro j' _ hj
    simp [Ne.symm hj]
  · simp

omit [CompleteSpace W] in
/-- Components of the parking swap: `(swapMain f) a i = Σ_{a'} coordV a (f a' i) • basisV a'`. -/
theorem swapMain_apply (I : Type) [Fintype I]
    (f : Joint (Coord M W) (Joint I (Joint (Fin M) W))) (a : Coord M W) (i : I) :
    swapMain I f a i = ∑ a' : Coord M W, coordV a (f a' i) • basisV a' := by
  simp [swapMain]

omit [CompleteSpace W] in
/-- The parking swap is an involution. -/
theorem swapMain_swapMain (I : Type) [Fintype I]
    (f : Joint (Coord M W) (Joint I (Joint (Fin M) W))) :
    swapMain I (swapMain I f) = f := by
  ext a i : 2
  simp_rw [swapMain_apply, map_sum, map_smul, coordV_basisV, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact sum_coordV_smul_basisV _

omit [CompleteSpace W] in
/-- `⟪v, |j⟩ ⊗ b_c⟫` is the conjugate coordinate `(j, c)` of `v`. -/
theorem inner_basisV_right (a : Coord M W) (v : Joint (Fin M) W) :
    ⟪v, basisV a⟫_ℂ = starRingEnd ℂ (coordV a v) := by
  rw [← inner_basisV_left, inner_conj_symm]

omit [CompleteSpace W] in
/-- The parking swap is symmetric. -/
theorem inner_swapMain (I : Type) [Fintype I]
    (f g : Joint (Coord M W) (Joint I (Joint (Fin M) W))) :
    ⟪swapMain I f, g⟫_ℂ = ⟪f, swapMain I g⟫_ℂ := by
  have key : ∀ F G : Joint (Coord M W) (Joint I (Joint (Fin M) W)),
      ⟪F, G⟫_ℂ = ∑ a, ∑ i, ⟪F a i, G a i⟫_ℂ := fun F G => by
    simp only [PiLp.inner_apply]
  rw [key, key]
  simp_rw [swapMain_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    inner_basisV_left, inner_basisV_right]
  refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_comm.trans ?_
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a' _ => mul_comm _ _

/-- The parking swap is unitary. -/
theorem swapMain_unitary (I : Type) [Fintype I] : IsUnitary (swapMain (M := M) (W := W) I) := by
  have hadj : (swapMain (M := M) (W := W) I).adjoint = swapMain I :=
    ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun f g => inner_swapMain I f g).symm
  have hsq : swapMain (M := M) (W := W) I * swapMain I = 1 :=
    ContinuousLinearMap.ext fun f => swapMain_swapMain I f
  refine ⟨?_, ?_⟩ <;> rw [ContinuousLinearMap.star_eq_adjoint, hadj, hsq]

omit [CompleteSpace W] in
/-- **The parking swap on product states**: `u ⊗ (ω ⊗ v) ↦ v ⊗ (ω ⊗ u)`. -/
theorem swapMain_tens (I : Type) [Fintype I] (u v : Joint (Fin M) W) (ω : I → ℂ) :
    swapMain I (ODELowerBoundExtensions.Release.tens u (WithLp.toLp 2 fun i => ω i • v)) =
      ODELowerBoundExtensions.Release.tens v (WithLp.toLp 2 fun i => ω i • u) := by
  ext a i : 2
  simp only [swapMain_apply, ODELowerBoundExtensions.Release.tens, PiLp.toLp_apply,
    PiLp.smul_apply, map_smul, smul_eq_mul, ← coordV_apply]
  simp_rw [mul_comm (coordV _ u), mul_smul, ← Finset.smul_sum, sum_coordV_smul_basisV]
  exact smul_comm _ _ _

end

end DysonSingleProgram.Parallel
