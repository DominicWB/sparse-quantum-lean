import SparseODE.ODECompleteSuccess

/-!
# The trace norm of self-adjoint operators

For a self-adjoint operator `X` on a finite-dimensional complex Hilbert space,
`tnorm X` is the sum of its absolute eigenvalues, so that the released trace
distance is `hermitianTraceDistance A B = tnorm (A - B) / 2`
(`hermitianTraceDistance_eq_tnorm`). The eigenvector expansion gives the
Hölder bound `|Tr (Y X)| ≤ ‖Y‖ tnorm X` (`norm_tr_comp_le`), and the sign
operator of `X` attains it (`signOp`, `norm_signOp_le`, `tr_signOp`). These
give the triangle inequality (`tnorm_add_le`), the scaling bound
(`tnorm_smul_le`), the contraction of the trace norm under compressions
`V† X V` with `‖V‖ ≤ 1` (`tnorm_compress_le`), the triangle inequality of the
trace distance (`hermitianTraceDistance_triangle`), the pure-state bound
`TD(|u⟩⟨u|, |v⟩⟨v|) ≤ ‖u - v‖` (`hermitianTraceDistance_pure_le`), and the
fact that trace distance zero means equality (`eq_of_hermitianTraceDistance_le_zero`).
-/

namespace SparseHamiltonian.MixedOutputODE

noncomputable section
open ContinuousLinearMap ODEMixedOutput InnerProductSpace
open scoped InnerProduct BigOperators ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The trace of an operator. -/
abbrev tr (X : E →L[ℂ] E) : ℂ := LinearMap.trace ℂ E X.toLinearMap

/-- The trace norm of a self-adjoint operator: the sum of its absolute
eigenvalues. -/
def tnorm (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) : ℝ :=
  ∑ i : Fin (Module.finrank ℂ E), |hX.eigenvalues rfl i|

theorem tnorm_nonneg (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) : 0 ≤ tnorm X hX :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem tnorm_congr {X Y : E →L[ℂ] E} (h : X = Y) (hX : X.toLinearMap.IsSymmetric)
    (hY : Y.toLinearMap.IsSymmetric) : tnorm X hX = tnorm Y hY := by
  subst h
  rfl

theorem hermitianTraceDistance_eq_tnorm (A B : E →L[ℂ] E)
    (h : (A - B).toLinearMap.IsSymmetric) :
    hermitianTraceDistance A B h = tnorm (A - B) h / 2 := rfl

/-- The eigenvectors of `X`. -/
abbrev eig (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
  hX.eigenvectorBasis rfl

theorem apply_eig (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric)
    (i : Fin (Module.finrank ℂ E)) :
    X (eig X hX i) = (hX.eigenvalues rfl i : ℂ) • eig X hX i :=
  hX.apply_eigenvectorBasis rfl i

theorem tnorm_eq_diagonalMass (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) :
    tnorm X hX = diagonalMass (eig X hX) X := by
  unfold tnorm diagonalMass
  apply Finset.sum_congr rfl
  intro i _
  rw [apply_eig X hX i, inner_smul_right, inner_self_complex, OrthonormalBasis.norm_eq_one,
    Complex.ofReal_one, one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Hölder bound.** `|Tr (Y X)| ≤ ‖Y‖ tnorm X`. -/
theorem norm_tr_comp_le (Y X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) :
    ‖tr (Y ∘L X)‖ ≤ ‖Y‖ * tnorm X hX := by
  set b := eig X hX with hb
  have htr : tr (Y ∘L X) = ∑ i, (hX.eigenvalues rfl i : ℂ) * inner ℂ (b i) (Y (b i)) := by
    rw [tr, LinearMap.trace_eq_sum_inner _ b]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (b i) (Y (X (b i))) = _
    rw [apply_eig X hX i, map_smul, inner_smul_right]
  rw [htr]
  calc
    ‖∑ i, (hX.eigenvalues rfl i : ℂ) * inner ℂ (b i) (Y (b i))‖ ≤
        ∑ i, ‖(hX.eigenvalues rfl i : ℂ) * inner ℂ (b i) (Y (b i))‖ := norm_sum_le _ _
    _ ≤ ∑ i, |hX.eigenvalues rfl i| * ‖Y‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        ‖inner ℂ (b i) (Y (b i))‖ ≤ ‖b i‖ * ‖Y (b i)‖ := norm_inner_le_norm _ _
        _ ≤ ‖b i‖ * (‖Y‖ * ‖b i‖) :=
          mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _)
        _ = ‖Y‖ := by rw [b.norm_eq_one]; ring
    _ = ‖Y‖ * tnorm X hX := by
      rw [tnorm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The sign of an eigenvalue. -/
def sgn (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

theorem mul_sgn (r : ℝ) : r * sgn r = |r| := by
  unfold sgn
  split_ifs with h
  · rw [mul_one, abs_of_nonneg h]
  · rw [mul_neg_one, abs_of_neg (lt_of_not_ge h)]

theorem norm_sgn (r : ℝ) : ‖(sgn r : ℂ)‖ = 1 := by
  unfold sgn
  split_ifs <;> simp

/-- The sign operator of `X`. -/
def signOp (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) : E →L[ℂ] E :=
  ∑ i, (sgn (hX.eigenvalues rfl i) : ℂ) • rankOne ℂ (eig X hX i) (eig X hX i)

theorem inner_signOp (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric)
    (j : Fin (Module.finrank ℂ E)) (z : E) :
    inner ℂ (eig X hX j) (signOp X hX z) =
      (sgn (hX.eigenvalues rfl j) : ℂ) * inner ℂ (eig X hX j) z := by
  set b := eig X hX with hb
  have horth := b.orthonormal
  unfold signOp
  rw [sum_apply, inner_sum, Finset.sum_eq_single j]
  · rw [smul_apply, rankOne_apply, inner_smul_right, inner_smul_right, inner_self_complex,
      b.norm_eq_one, Complex.ofReal_one, one_pow, mul_one]
  · intro i _ hij
    rw [smul_apply, rankOne_apply, inner_smul_right, inner_smul_right,
      horth.inner_eq_zero (Ne.symm hij), mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem norm_signOp_le (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) :
    ‖signOp X hX‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  set b := eig X hX with hb
  have hsq : ‖signOp X hX z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (signOp X hX z), ← b.sum_sq_norm_inner_right z]
    apply Finset.sum_congr rfl
    intro j _
    rw [hb, inner_signOp, norm_mul, norm_sgn, one_mul]
  have h0 := norm_nonneg (signOp X hX z)
  have h1 := norm_nonneg z
  rw [one_mul]
  nlinarith [sq_nonneg (‖signOp X hX z‖ - ‖z‖), sq_nonneg (‖signOp X hX z‖ + ‖z‖)]

/-- The sign operator attains the Hölder bound. -/
theorem tr_signOp (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) :
    tr (signOp X hX ∘L X) = (tnorm X hX : ℂ) := by
  set b := eig X hX with hb
  rw [tr, LinearMap.trace_eq_sum_inner _ b, tnorm, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  change inner ℂ (b j) (signOp X hX (X (b j))) = _
  rw [hb, inner_signOp, apply_eig X hX j, inner_smul_right, inner_self_complex,
    OrthonormalBasis.norm_eq_one, Complex.ofReal_one, one_pow, mul_one, ← Complex.ofReal_mul,
    mul_comm, mul_sgn]

omit [FiniteDimensional ℂ E] in
theorem tr_add (A B : E →L[ℂ] E) : tr (A + B) = tr A + tr B := by
  simp only [tr, ContinuousLinearMap.toLinearMap_add, map_add]

omit [FiniteDimensional ℂ E] in
theorem tr_sub (A B : E →L[ℂ] E) : tr (A - B) = tr A - tr B := by
  simp only [tr, ContinuousLinearMap.toLinearMap_sub, map_sub]

omit [FiniteDimensional ℂ E] in
theorem tr_smul (c : ℂ) (A : E →L[ℂ] E) : tr (c • A) = c * tr A := by
  simp only [tr, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]

/-- The trace norm through its sign operator. -/
theorem tnorm_eq_norm_tr (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric) :
    tnorm X hX = ‖tr (signOp X hX ∘L X)‖ := by
  rw [tr_signOp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tnorm_nonneg X hX)]

/-- **Triangle inequality.** -/
theorem tnorm_add_le (X Y : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric)
    (hY : Y.toLinearMap.IsSymmetric) (hXY : (X + Y).toLinearMap.IsSymmetric) :
    tnorm (X + Y) hXY ≤ tnorm X hX + tnorm Y hY := by
  set S := signOp (X + Y) hXY
  have hS := norm_signOp_le (X + Y) hXY
  rw [tnorm_eq_norm_tr, comp_add, tr_add]
  calc
    ‖tr (S ∘L X) + tr (S ∘L Y)‖ ≤ ‖tr (S ∘L X)‖ + ‖tr (S ∘L Y)‖ := norm_add_le _ _
    _ ≤ ‖S‖ * tnorm X hX + ‖S‖ * tnorm Y hY :=
      add_le_add (norm_tr_comp_le S X hX) (norm_tr_comp_le S Y hY)
    _ ≤ 1 * tnorm X hX + 1 * tnorm Y hY :=
      add_le_add (mul_le_mul_of_nonneg_right hS (tnorm_nonneg X hX))
        (mul_le_mul_of_nonneg_right hS (tnorm_nonneg Y hY))
    _ = tnorm X hX + tnorm Y hY := by ring

/-- **Scaling.** -/
theorem tnorm_smul_le (c : ℂ) (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric)
    (hcX : (c • X).toLinearMap.IsSymmetric) :
    tnorm (c • X) hcX ≤ ‖c‖ * tnorm X hX := by
  set S := signOp (c • X) hcX
  have hS := norm_signOp_le (c • X) hcX
  rw [tnorm_eq_norm_tr, comp_smul, tr_smul, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg c)
  calc
    ‖tr (S ∘L X)‖ ≤ ‖S‖ * tnorm X hX := norm_tr_comp_le S X hX
    _ ≤ 1 * tnorm X hX := mul_le_mul_of_nonneg_right hS (tnorm_nonneg X hX)
    _ = tnorm X hX := one_mul _

/-- **Compressions contract the trace norm.** -/
theorem tnorm_compress_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (V : F →L[ℂ] E) (hV : ‖V‖ ≤ 1) (X : E →L[ℂ] E)
    (hX : X.toLinearMap.IsSymmetric) (hVX : (V† ∘L X ∘L V).toLinearMap.IsSymmetric) :
    tnorm (V† ∘L X ∘L V) hVX ≤ tnorm X hX := by
  set S := signOp (V† ∘L X ∘L V) hVX
  have hS := norm_signOp_le (V† ∘L X ∘L V) hVX
  have hcyc : tr (S ∘L (V† ∘L X ∘L V)) = tr ((V ∘L S ∘L V†) ∘L X) := by
    change LinearMap.trace ℂ F ((S ∘L V† ∘L X).toLinearMap ∘ₗ V.toLinearMap) =
      LinearMap.trace ℂ E (V.toLinearMap ∘ₗ (S ∘L V† ∘L X).toLinearMap)
    exact LinearMap.trace_comp_comm' _ _
  have hVS : ‖V ∘L S ∘L V†‖ ≤ 1 := by
    have hV' : ‖V†‖ ≤ 1 := by rw [ContinuousLinearMap.adjoint.norm_map]; exact hV
    calc
      ‖V ∘L S ∘L V†‖ ≤ ‖V‖ * (‖S‖ * ‖V†‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
          (norm_nonneg _))
      _ ≤ 1 * (1 * 1) := by gcongr
      _ = 1 := by norm_num
  rw [tnorm_eq_norm_tr, hcyc]
  calc
    ‖tr ((V ∘L S ∘L V†) ∘L X)‖ ≤ ‖V ∘L S ∘L V†‖ * tnorm X hX := norm_tr_comp_le _ X hX
    _ ≤ 1 * tnorm X hX := mul_le_mul_of_nonneg_right hVS (tnorm_nonneg X hX)
    _ = tnorm X hX := one_mul _

/-- The trace norm of a rank-one positive operator. -/
theorem tnorm_pure_le (u : E) (h : (pureOperator u).toLinearMap.IsSymmetric) :
    tnorm (pureOperator u) h ≤ ‖u‖ ^ 2 := by
  rw [tnorm_eq_diagonalMass, sq]
  exact diagonalMass_rankOne_le _ u u

/-- Trace norm zero means the operator vanishes. -/
theorem eq_zero_of_tnorm_le_zero (X : E →L[ℂ] E) (hX : X.toLinearMap.IsSymmetric)
    (h : tnorm X hX ≤ 0) : X = 0 := by
  have h0 : tnorm X hX = 0 := le_antisymm h (tnorm_nonneg X hX)
  have hev : ∀ i, hX.eigenvalues rfl i = 0 := by
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg
      (hX.eigenvalues rfl j))).mp h0 i (Finset.mem_univ i)
    exact abs_eq_zero.mp this
  ext z
  rw [← (eig X hX).sum_repr' z, map_sum, zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [map_smul, apply_eig X hX i, hev i, Complex.ofReal_zero, zero_smul, smul_zero]

/-- **Triangle inequality of the trace distance.** -/
theorem hermitianTraceDistance_triangle (A B C : E →L[ℂ] E)
    (hAB : (A - B).toLinearMap.IsSymmetric) (hBC : (B - C).toLinearMap.IsSymmetric)
    (hAC : (A - C).toLinearMap.IsSymmetric) :
    hermitianTraceDistance A C hAC ≤ hermitianTraceDistance A B hAB +
      hermitianTraceDistance B C hBC := by
  rw [hermitianTraceDistance_eq_tnorm, hermitianTraceDistance_eq_tnorm,
    hermitianTraceDistance_eq_tnorm]
  have hsum : A - C = (A - B) + (B - C) := by abel
  have hsym : ((A - B) + (B - C)).toLinearMap.IsSymmetric := by rw [← hsum]; exact hAC
  rw [tnorm_congr hsum hAC hsym]
  have := tnorm_add_le (A - B) (B - C) hAB hBC hsym
  linarith

/-- Trace distance zero means equality. -/
theorem eq_of_hermitianTraceDistance_le_zero (A B : E →L[ℂ] E)
    (h : (A - B).toLinearMap.IsSymmetric) (hd : hermitianTraceDistance A B h ≤ 0) :
    A = B := by
  rw [hermitianTraceDistance_eq_tnorm] at hd
  have : tnorm (A - B) h ≤ 0 := by linarith
  exact sub_eq_zero.mp (eq_zero_of_tnorm_le_zero _ h this)

/-- The pure-state bound: the trace distance of two pure states is at most
the distance of their unit vectors. -/
theorem hermitianTraceDistance_pure_le (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : (pureOperator u - pureOperator v).toLinearMap.IsSymmetric) :
    hermitianTraceDistance (pureOperator u) (pureOperator v) h ≤ ‖u - v‖ := by
  rw [hermitianTraceDistance_eq_diagonalMass]
  have := diagonalMass_pure_sub_le (h.eigenvectorBasis (n := Module.finrank ℂ E) rfl) u v hu hv
  linarith

omit [FiniteDimensional ℂ E] in
/-- Pure states are self-adjoint, so are their differences. -/
theorem pure_sub_isSymmetric (u v : E) :
    (pureOperator u - pureOperator v).toLinearMap.IsSymmetric :=
  (pureOperator_positive u).isSymmetric.sub (pureOperator_positive v).isSymmetric

/-- The pure-state bound up to a phase. -/
theorem hermitianTraceDistance_pure_phase_le (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ω : ℂ) (hω : ‖ω‖ = 1)
    (h : (pureOperator u - pureOperator v).toLinearMap.IsSymmetric) :
    hermitianTraceDistance (pureOperator u) (pureOperator v) h ≤ ‖ω • u - v‖ := by
  have hωu : ‖ω • u‖ = 1 := by rw [norm_smul, hω, hu, one_mul]
  have hphase : pureOperator (ω • u) = pureOperator u := pureOperator_phase ω hω u
  have h' : (pureOperator (ω • u) - pureOperator v).toLinearMap.IsSymmetric :=
    pure_sub_isSymmetric _ _
  have hle := hermitianTraceDistance_pure_le (ω • u) v hωu hv h'
  have heq : hermitianTraceDistance (pureOperator u) (pureOperator v) h =
      hermitianTraceDistance (pureOperator (ω • u)) (pureOperator v) h' := by
    rw [hermitianTraceDistance_eq_tnorm, hermitianTraceDistance_eq_tnorm]
    rw [tnorm_congr (by rw [hphase]) h h']
  rw [heq]
  exact hle

end

end SparseHamiltonian.MixedOutputODE
