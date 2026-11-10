import DysonSingleProgram.Parallel.Stage
import ODELowerBoundExtensions.Dyson.Flagged

set_option autoImplicit false

/-!
# Computations with the first-success herald and readout

Manuscript: Section `odel:sec:main` (output model: success flag and conditional output density)
and the proof of Lemma `odel:lem:dyson`. Facts about the herald
`heraldStep` and the readout `outStep` of `Parallel/Stage.lean` used to show that a stage
reproduces a released retry protocol (`Parallel/Readout.lean`).

* `coordLift_sub_apply`, `coordLift_one_apply`, `coordLift_zero_apply`: `G ↦ 1 ⊗ G ⊗ 1` is
  affine-linear in coordinates (`ODELowerBoundExtensions.Release.coordLift`).
* `apply_eq_sum_single`, `liftObs_apply_apply`: the system observable `A ⊗ 1` in coordinates.
* `inner_succRead_liftObs`: the success readout is `Fo† ⊗ 1` in the coordinates of `W`, so
  `succRead† (A ⊗ 1) succRead = 1 ⊗ Fo A Fo† ⊗ 1`.
* `inner_failRead_liftObs`: `failRead† (A ⊗ 1) failRead = 1 ⊗ out† (A ⊗ 1) out`.
* `inner_outStep_liftObs`: the two garbage sectors of `outStep` never mix, so the readout
  observable after one more attempt is the sum of the success and the failure contributions.
* `norm_outStep`: `outStep` is an isometry when `Fo` and the previous readout are.
* `isStarProjection_heraldStep`: the herald after one more attempt is a projection.

The success projector `Π = Fo Fo†` is `ODELowerBoundExtensions.Dyson.encodedProjector Fo`; its
idempotence and self-adjointness are `encodedProjector_idem` and `encodedProjector_adjoint`.
-/

namespace DysonSingleProgram.Parallel

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit Register
open ODELowerBoundExtensions.Release (coordLift coordMatrix coordLift_apply coordLift_comp
  inner_coordLift coordLift_fiber tens jointFlatten jointSwap)
open ODELowerBoundExtensions.Dyson (encodedProjector_idem encodedProjector_adjoint
  one_sub_encodedProjector_adjoint adjoint_apply_self)
open scoped InnerProduct InnerProductSpace

section CoordLift

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {J H : Type*} [Fintype J] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `1 ⊗ (G - G') ⊗ 1 = 1 ⊗ G ⊗ 1 - 1 ⊗ G' ⊗ 1`. -/
theorem coordLift_sub_apply (G G' : W →L[ℂ] W) (f : Joint (J × Fin (Module.finrank ℂ W)) H) :
    coordLift (G - G') f = coordLift G f - coordLift G' f := by
  ext ⟨j, i⟩
  simp only [coordLift_apply, PiLp.sub_apply, ← Finset.sum_sub_distrib, ← sub_smul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp [coordMatrix, inner_sub_right]

/-- `1 ⊗ 1 ⊗ 1 = 1`. -/
theorem coordLift_one_apply (f : Joint (J × Fin (Module.finrank ℂ W)) H) :
    coordLift (1 : W →L[ℂ] W) f = f := by
  ext ⟨j, i⟩
  rw [coordLift_apply]
  have h : ∀ i', coordMatrix (1 : W →L[ℂ] W) i i' = if i = i' then 1 else 0 := fun i' => by
    change ⟪stdOrthonormalBasis ℂ W i, stdOrthonormalBasis ℂ W i'⟫_ℂ = _
    exact orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ W).orthonormal i i'
  simp [h]

/-- `1 ⊗ 0 ⊗ 1 = 0`. -/
theorem coordLift_zero_apply (f : Joint (J × Fin (Module.finrank ℂ W)) H) :
    coordLift (0 : W →L[ℂ] W) f = 0 := by
  ext ⟨j, i⟩
  simp [coordLift_apply, coordMatrix]

/-- `1 ⊗ G ⊗ 1` is symmetric when `G` is self-adjoint. -/
theorem inner_coordLift_symm [CompleteSpace W] {G : W →L[ℂ] W} (hG : G† = G)
    (f f' : Joint (J × Fin (Module.finrank ℂ W)) H) :
    ⟪coordLift G f, f'⟫_ℂ = ⟪f, coordLift G f'⟫_ℂ := by
  rw [inner_coordLift, hG]

end CoordLift

section Fiber

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {J : Type*} [Fintype J]

/-- `⟪(1 ⊗ G) v, (1 ⊗ G') v'⟫ = ⟪v, (1 ⊗ G† G') v'⟫`. -/
theorem inner_fiber_fiber (G G' : W →L[ℂ] W) (v v' : Joint J W) :
    ⟪Joint.fiber (fun _ => G) v, Joint.fiber (fun _ => G') v'⟫_ℂ =
      ⟪v, Joint.fiber (fun _ => G† ∘L G') v'⟫_ℂ := by
  simp only [PiLp.inner_apply, Joint.fiber_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- `1 ⊗ R` is symmetric when `R` is self-adjoint. -/
theorem inner_fiber_symm {R : W →L[ℂ] W} (hR : R† = R) (v v' : Joint J W) :
    ⟪Joint.fiber (fun _ => R) v, v'⟫_ℂ = ⟪v, Joint.fiber (fun _ => R) v'⟫_ℂ := by
  simp only [PiLp.inner_apply, Joint.fiber_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ContinuousLinearMap.adjoint_inner_right, hR]


end Fiber

section Readouts

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W] {M : ℕ} {N : Type} [Fintype N] [DecidableEq N]

/-- Coordinates of a system operator: `(A a)_i = Σ_{i'} (A e_{i'})_i a_{i'}`. -/
theorem apply_eq_sum_single (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (a : EuclideanSpace ℂ N) (i : N) :
    A a i = ∑ i', A (EuclideanSpace.single i' 1) i * a i' := by
  conv_lhs => rw [← (EuclideanSpace.basisFun N ℂ).sum_repr a]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, mul_comm]

/-- Components of the system observable on system ⊗ `ℂ^Γ ⊗ G`. -/
theorem liftObs_apply_apply {Γ G : Type*} [Fintype Γ] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (Φ : SysGarb N (Joint Γ G)) (i : N) (g : Γ) :
    Readout.liftObs A Φ i g = ∑ i', A (EuclideanSpace.single i' 1) i • Φ i' g := by
  rw [Readout.liftObs_apply]
  simp

omit [DecidableEq N] in
/-- Components of the success readout. -/
theorem succRead_apply (Fo : EuclideanSpace ℂ N →L[ℂ] W) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (w : Joint (Coord M W) H) (i : N) (j : Fin M) :
    succRead Fo H w i j = ∑ c, (Fo.adjoint (stdOrthonormalBasis ℂ W c)) i • w (j, c) := by
  simp [succRead]

omit [CompleteSpace W] [DecidableEq N] in
/-- The failure readout is the previous readout on every parked coordinate, with the registers
swapped. -/
theorem failRead_eq {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (out : H →L[ℂ] SysGarb N G)
    (w : Joint (Coord M W) H) :
    failRead out w = jointSwap (Coord M W) N G (WithLp.toLp 2 fun a => out (w a)) :=
  rfl

omit [CompleteSpace W] [DecidableEq N] in
/-- Components of the failure readout. -/
theorem failRead_apply {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (out : H →L[ℂ] SysGarb N G)
    (w : Joint (Coord M W) H) (i : N) (a : Coord M W) :
    failRead out w i a = out (w a) i :=
  rfl

variable {I Γ : Type} [Fintype I] [Fintype Γ]

omit [DecidableEq N] in
/-- The success sector of the readout after one more attempt. -/
theorem outStep_apply_inl (Fo : EuclideanSpace ℂ N →L[ℂ] W)
    (out : Joint I (Joint (Fin M) W) →L[ℂ] SysGarb N (Joint Γ (Joint (Fin M) W)))
    (f : Joint (Coord M W) (Joint I (Joint (Fin M) W))) (i : N) (b : Fin M × I) :
    outStep Fo out f i (Sum.inl b) =
      succRead Fo (Joint I (Joint (Fin M) W)) (coordLift (Fo ∘L Fo†) f) i b.1 b.2 :=
  rfl

omit [DecidableEq N] in
/-- The failure sector of the readout after one more attempt. -/
theorem outStep_apply_inr (Fo : EuclideanSpace ℂ N →L[ℂ] W)
    (out : Joint I (Joint (Fin M) W) →L[ℂ] SysGarb N (Joint Γ (Joint (Fin M) W)))
    (f : Joint (Coord M W) (Joint I (Joint (Fin M) W))) (i : N) (c : Coord M W × Γ) :
    outStep Fo out f i (Sum.inr c) = failRead out (coordLift (1 - Fo ∘L Fo†) f) i c.1 c.2 :=
  rfl

/-- `A = 1` acts trivially on system ⊗ garbage. -/
theorem liftObs_one_apply {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    (Φ : SysGarb N G) :
    Readout.liftObs (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) Φ = Φ := by
  ext i : 1
  rw [Readout.liftObs_apply]
  simp

/-- The system observable on the success readout acts on the decoded output:
`(A ⊗ 1)(succRead w)_{i j} = Σ_c (A Fo† b_c)_i w(j, c)`. -/
theorem liftObs_succRead_apply (Fo : EuclideanSpace ℂ N →L[ℂ] W) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (w : Joint (Coord M W) H) (i : N) (j : Fin M) :
    Readout.liftObs A (succRead Fo H w) i j =
      ∑ c, (A (Fo.adjoint (stdOrthonormalBasis ℂ W c))) i • w (j, c) := by
  rw [liftObs_apply_apply]
  simp only [succRead_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul, apply_eq_sum_single A _ i]

/-- **The success readout is `Fo† ⊗ 1`**: `succRead† (A ⊗ 1) succRead = 1 ⊗ Fo A Fo† ⊗ 1`. -/
theorem inner_succRead_liftObs (Fo : EuclideanSpace ℂ N →L[ℂ] W) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (w w' : Joint (Coord M W) H) :
    ⟪succRead Fo H w, Readout.liftObs A (succRead Fo H w')⟫_ℂ =
      ⟪w, coordLift (Fo ∘L A ∘L Fo†) w'⟫_ℂ := by
  have hexp : ∀ (u u' : Fin (Module.finrank ℂ W) → H) (s s' : Fin (Module.finrank ℂ W) → ℂ),
      ⟪∑ c, s c • u c, ∑ c', s' c' • u' c'⟫_ℂ =
        ∑ c, ∑ c', (starRingEnd ℂ) (s c) * s' c' * ⟪u c, u' c'⟫_ℂ := by
    intro u u' s s'
    rw [sum_inner]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [inner_smul_right]
    ring
  rw [PiLp.inner_apply]
  simp only [PiLp.inner_apply, liftObs_succRead_apply, succRead_apply, hexp,
    Fintype.sum_prod_type, coordLift_apply, inner_sum, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [← Finset.sum_mul]
  congr 1
  simp only [coordMatrix, Matrix.of_apply, ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply']

omit [CompleteSpace W] in
/-- The system observable on the failure readout is the previous readout's observable. -/
theorem liftObs_failRead {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (out : H →L[ℂ] SysGarb N G)
    (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (w : Joint (Coord M W) H) :
    Readout.liftObs A (failRead out w) = failRead (Readout.liftObs A ∘L out) w := by
  ext i a : 2
  rw [liftObs_apply_apply, failRead_apply, ContinuousLinearMap.comp_apply, Readout.liftObs_apply]
  rfl

omit [CompleteSpace W] [DecidableEq N] in
/-- Inner products of failure readouts:
`⟪failRead e w, failRead e' w'⟫ = Σ_a ⟪e (w a), e' (w' a)⟫`. -/
theorem inner_failRead {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] (out out' : H →L[ℂ] SysGarb N G)
    (w w' : Joint (Coord M W) H) :
    ⟪failRead out w, failRead out' w'⟫_ℂ = ∑ a, ⟪out (w a), out' (w' a)⟫_ℂ := by
  rw [failRead_eq, failRead_eq, LinearIsometryEquiv.inner_map_map, PiLp.inner_apply]

omit [CompleteSpace W] in
/-- **The failure readout is the previous readout on each parked coordinate**:
`failRead† (A ⊗ 1) failRead = 1 ⊗ out† (A ⊗ 1) out`. -/
theorem inner_failRead_liftObs {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (out : H →L[ℂ] SysGarb N G) (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (w w' : Joint (Coord M W) H) :
    ⟪failRead out w, Readout.liftObs A (failRead out w')⟫_ℂ =
      ⟪w, Joint.fiber (fun _ => Readout.outObs out A) w'⟫_ℂ := by
  rw [liftObs_failRead, inner_failRead, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Joint.fiber_apply, Readout.outObs]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- **The two garbage sectors of the readout do not mix**: the readout observable after one more
attempt is the success readout's on `Π ⊗ 1` plus the previous readout's on `(1 - Π) ⊗ 1`. -/
theorem inner_outStep_liftObs (Fo : EuclideanSpace ℂ N →L[ℂ] W)
    (out : Joint I (Joint (Fin M) W) →L[ℂ] SysGarb N (Joint Γ (Joint (Fin M) W)))
    (A : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (f f' : Joint (Coord M W) (Joint I (Joint (Fin M) W))) :
    ⟪outStep Fo out f, Readout.liftObs A (outStep Fo out f')⟫_ℂ =
      ⟪succRead Fo _ (coordLift (Fo ∘L Fo†) f),
          Readout.liftObs A (succRead Fo _ (coordLift (Fo ∘L Fo†) f'))⟫_ℂ +
        ⟪failRead out (coordLift (1 - Fo ∘L Fo†) f),
          Readout.liftObs A (failRead out (coordLift (1 - Fo ∘L Fo†) f'))⟫_ℂ := by
  have h1 : ∀ i (b : Fin M × I), Readout.liftObs A (outStep Fo out f') i (Sum.inl b) =
      Readout.liftObs A (succRead Fo _ (coordLift (Fo ∘L Fo†) f')) i b.1 b.2 := by
    intro i b
    simp only [liftObs_apply_apply, outStep_apply_inl]
    simp
  have h2 : ∀ i (c : Coord M W × Γ), Readout.liftObs A (outStep Fo out f') i (Sum.inr c) =
      Readout.liftObs A (failRead out (coordLift (1 - Fo ∘L Fo†) f')) i c.1 c.2 := by
    intro i c
    simp only [liftObs_apply_apply, outStep_apply_inr]
    simp
  conv_lhs => rw [PiLp.inner_apply]
  conv_rhs => rw [PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  congr 1
  · conv_rhs => rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_rhs => rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun ι _ => ?_
    rw [outStep_apply_inl, h1]
  · conv_rhs => rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_rhs => rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [outStep_apply_inr, h2]

/-- The readout observable of `A = 1` is `e† e`. -/
theorem outObs_one {K G : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (e : K →L[ℂ] SysGarb N G) :
    Readout.outObs e (1 : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) = e† ∘L e := by
  ext v : 1
  simp [Readout.outObs, liftObs_one_apply]

/-- **The readout after one more attempt is an isometry** when the output isometry `Fo` and the
previous readout are isometries. -/
theorem norm_outStep (Fo : EuclideanSpace ℂ N →L[ℂ] W) (hFo : Fo† ∘L Fo = 1)
    (out : Joint I (Joint (Fin M) W) →L[ℂ] SysGarb N (Joint Γ (Joint (Fin M) W)))
    (hout : out† ∘L out = 1) (f : Joint (Coord M W) (Joint I (Joint (Fin M) W))) :
    ‖outStep Fo out f‖ = ‖f‖ := by
  have key := inner_outStep_liftObs Fo out 1 f f
  rw [liftObs_one_apply, inner_succRead_liftObs, inner_failRead_liftObs, outObs_one, hout,
    Joint.fiber_one, one_apply_eq_self] at key
  have hG : Fo ∘L 1 ∘L Fo† = Fo ∘L Fo† := by ext v; simp
  set Q := coordLift (J := Fin M) (H := Joint I (Joint (Fin M) W)) (Fo ∘L Fo†) with hQ
  have hQQ : ∀ g, Q (Q g) = Q g := fun g => by
    rw [hQ, ← coordLift_comp, show (Fo ∘L Fo†) ∘L (Fo ∘L Fo†) = Fo ∘L Fo† from
      ContinuousLinearMap.ext (encodedProjector_idem Fo hFo)]
  have hQs : ∀ g g', ⟪Q g, g'⟫_ℂ = ⟪g, Q g'⟫_ℂ := fun g g' =>
    inner_coordLift_symm (encodedProjector_adjoint Fo) g g'
  have hQ' : coordLift (1 - Fo ∘L Fo†) f = f - Q f := by
    rw [coordLift_sub_apply, coordLift_one_apply]
  rw [hG, hQ', hQQ] at key
  have hff : ⟪outStep Fo out f, outStep Fo out f⟫_ℂ = ⟪f, f⟫_ℂ := by
    have e1 : ⟪Q f, Q f⟫_ℂ = ⟪f, Q f⟫_ℂ := by rw [hQs, hQQ]
    have e2 : ⟪Q f, f⟫_ℂ = ⟪f, Q f⟫_ℂ := hQs f f
    rw [key, inner_sub_left, inner_sub_right, inner_sub_right, e1, e2]
    ring
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hff
  have h2 : ‖outStep Fo out f‖ ^ 2 = ‖f‖ ^ 2 := by exact_mod_cast hff
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

end Readouts

section Herald

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W] {M : ℕ}

/-- **The herald after one more attempt is a projection**: `Π ⊗ 1 + (1 - Π) ⊗ P` for the
success projector `Π = Fo Fo†` and a projection `P`. -/
theorem isStarProjection_heraldStep {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Fo : E →L[ℂ] W) (hFo : Fo† ∘L Fo = 1) (P : H →L[ℂ] H) (hP : IsStarProjection P) :
    IsStarProjection (heraldStep (M := M) Fo P) := by
  set Q := coordLift (J := Fin M) (H := H) (Fo ∘L Fo†) with hQ
  set Q' := coordLift (J := Fin M) (H := H) (1 - Fo ∘L Fo†) with hQ'
  set Pf : Joint (Coord M W) H →L[ℂ] Joint (Coord M W) H := Joint.fiber (fun _ => P) with hPf
  have happ : ∀ f, heraldStep (M := M) Fo P f = Q f + Q' (Pf f) := fun f => rfl
  have hFF : ∀ v, Fo.adjoint (Fo v) = v := adjoint_apply_self Fo hFo
  have hPi : (Fo ∘L Fo†) ∘L (Fo ∘L Fo†) = Fo ∘L Fo† :=
    ContinuousLinearMap.ext (encodedProjector_idem Fo hFo)
  have hQQ : ∀ f, Q (Q f) = Q f := fun f => by rw [hQ, ← coordLift_comp, hPi]
  have hQQ' : ∀ f, Q (Q' f) = 0 := fun f => by
    rw [hQ, hQ', ← coordLift_comp]
    rw [show (Fo ∘L Fo†) ∘L (1 - Fo ∘L Fo†) = 0 by ext v; simp [hFF]]
    exact coordLift_zero_apply f
  have hQ'Q : ∀ f, Q' (Q f) = 0 := fun f => by
    rw [hQ, hQ', ← coordLift_comp]
    rw [show (1 - Fo ∘L Fo†) ∘L (Fo ∘L Fo†) = 0 by ext v; simp [hFF]]
    exact coordLift_zero_apply f
  have hQ'Q' : ∀ f, Q' (Q' f) = Q' f := fun f => by
    rw [hQ', ← coordLift_comp,
      show (1 - Fo ∘L Fo†) ∘L (1 - Fo ∘L Fo†) = 1 - Fo ∘L Fo† by ext v; simp [hFF]]
  have hQP : ∀ f, Q (Pf f) = Pf (Q f) := fun f => coordLift_fiber _ _ _
  have hQ'P : ∀ f, Q' (Pf f) = Pf (Q' f) := fun f => coordLift_fiber _ _ _
  have hP2 : ∀ g, P (P g) = P g := fun g =>
    congrArg (fun T : H →L[ℂ] H => T g) hP.isIdempotentElem.eq
  have hPP : ∀ f, Pf (Pf f) = Pf f := fun f => by
    ext a : 1
    simp [hPf, hP2]
  have hPs : P† = P := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hP.isSelfAdjoint.star_eq
  have hPa : (Fo ∘L Fo†)† = Fo ∘L Fo† := encodedProjector_adjoint Fo
  have hPis : (1 - Fo ∘L Fo†)† = 1 - Fo ∘L Fo† := one_sub_encodedProjector_adjoint Fo
  rw [isStarProjection_iff']
  constructor
  · ext f : 1
    simp only [mul_apply_eq_comp, happ, map_add, hQQ, hQQ', ← hQP, hQ'Q,
      ← hQ'P, hQ'Q', hPP, add_zero, zero_add]
  · rw [ContinuousLinearMap.star_eq_adjoint]
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro f g
    rw [happ, happ, inner_add_left, inner_add_right, inner_coordLift_symm hPa,
      inner_coordLift_symm hPis, inner_fiber_symm hPs, ← hQ'P]

end Herald

end

end DysonSingleProgram.Parallel
