import SignedFactorSimulation.Query
import SignedFactorSimulation.Mesh
import OptimalPrecision.Weights.Theorem
import OptimalPrecision.Tail.Lemma
import SparseHamiltonian.LabeledAdjointSimulation

/-!
# The circuit for a factor with `q ≥ 1`

This module assembles the construction of Sections `opt:sec:factor` and `opt:sec:tail` for given
`q ≥ 1` and order `M ≥ 1`: the clock weights of Theorem `opt:thm:weights`
(`n = clockLength q M ≤ 27 qM` reuse lengths, total variation at most `3000`), a finite mesh of `m`
slots with step `v = qM/m`, the signed LCU attenuated to `s₀ = sin(π/(2·3⁸))`, and eight rounds of
amplification.

The workspace is flattened to `ℂ^ι ⊗ W`, a Hilbert sum of copies of `W` indexed by a finite
label type `ι` (`flat`, `Lbl`), so that one factor query is `I_ι ⊗ U` (`flat_liftU`).

* `amplified_error`: an amplified and sign-aligned LCU whose initial block is within `e₀` of
  `s₀ W` has full-output error at most `√(2 · 7⁸ e₀)`;
* `core`: if `M ≥ 2·27² q²Mδ` and the factorial tail `2 · 3001 (e² 27² q²Mδ/M)^M` of
  Lemma `opt:lem:tail` is at most `ε²/(4·7⁸)`, there is a program with at most
  `2·3⁸·27·qM` factor queries whose full output is within `ε` of `e^{-i q²M C}`.
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open Complex ContinuousLinearMap Finset OptimalPrecision OptimalPrecision.Tail SparseHamiltonian
  SparseHamiltonian.OracleCircuit SparseHamiltonian.ChronologicalResolvent
open scoped InnerProduct InnerProductSpace ComplexOrder

/-! ### Flattening to copies of `W` -/

section Flat

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- The labels of the registers of the workspace: a branch, then a private or public slot. -/
abbrev Lbl (n m : ℕ) := Σ i : Br n, Fin m ⊕ Fin (brLen n i)

/-- The known flattening of the structured workspace to `ℂ^Lbl ⊗ W`. -/
def flat (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n m : ℕ) :
    Work W n m ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Lbl n m => W) :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun i : Br n =>
    (PiLp.sumPiLpEquivProdLpPiLp (𝕜 := ℂ) 2 (fun _ : Fin m ⊕ Fin (brLen n i) => W)).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (i : Br n) (_ : Fin m ⊕ Fin (brLen n i)) => W)).symm

/-- **The lifted query is `I ⊗ U`**: after flattening, the lifted factor query applies `U` to
every copy of `W`. -/
theorem flat_liftU (U : W →L[ℂ] W) (n m : ℕ) :
    (flat W n m).conjStarAlgEquiv (liftU U n m) =
      WeightedClock.diagonal (fun _ : Lbl n m => U) := by
  ext z ⟨i, j⟩
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, WeightedClock.diagonal_apply]
  cases j with
  | inl k =>
    simp [flat, liftU, liftBr]
    rfl
  | inr k =>
    simp [flat, liftU, liftBr]
    rfl

end Flat

section Embed

variable {P H L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

/-- An embedding transported along a known register equivalence. -/
def embed (e : H ≃ₗᵢ[ℂ] L) (J : P →L[ℂ] H) : P →L[ℂ] L :=
  e.toLinearIsometry.toContinuousLinearMap ∘L J

theorem equiv_adjoint_comp (e : H ≃ₗᵢ[ℂ] L) :
    (e.toLinearIsometry.toContinuousLinearMap)† ∘L e.toLinearIsometry.toContinuousLinearMap =
      1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (fun x => e.norm_map x)

theorem embed_isometry (e : H ≃ₗᵢ[ℂ] L) {J : P →L[ℂ] H} (hJ : J† ∘L J = 1) :
    (embed e J)† ∘L embed e J = 1 := by
  rw [embed, adjoint_comp, comp_assoc, ← comp_assoc _ _ J, equiv_adjoint_comp, one_comp', hJ]

omit [CompleteSpace P] in
/-- The full-output error is unchanged by a known change of register layout. -/
theorem embed_error (e : H ≃ₗᵢ[ℂ] L) (F : H →L[ℂ] H) (J : P →L[ℂ] H) (V : P →L[ℂ] P) :
    ‖e.conjStarAlgEquiv F ∘L embed e J - embed e J ∘L V‖ = ‖F ∘L J - J ∘L V‖ := by
  have h : e.conjStarAlgEquiv F ∘L embed e J - embed e J ∘L V =
      e.toLinearIsometry.toContinuousLinearMap ∘L (F ∘L J - J ∘L V) := by
    ext y
    simp [embed]
  rw [h]
  exact EncodedOracle.norm_comp_eq _ (equiv_adjoint_comp e) _

end Embed

theorem Implements.of_oracle_eq {X K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {O O' F : X → K →L[ℂ] K} {c : ℕ} (h : ∀ x, O x = O' x)
    (hF : Implements O F c) : Implements O' F c := by
  have hOO : O = O' := funext h
  subst hOO
  exact hF

/-! ### Amplification and alignment -/

section Amplified

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_le_one_of_isometry {V : P →L[ℂ] P} (hV : V† ∘L V = 1) : ‖V‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  rw [V.norm_map_iff_adjoint_comp_self.mpr hV x, one_mul]

/-- **The amplified, aligned circuit**: eight rounds of amplification of `S` (input `I`,
output `J`), followed by a known unitary `Σ` with `Σ J = I`. If the initial block is within
`e₀` of `sin(π/(2·3⁸)) Wt` for a unitary `Wt`, the full output is within `√(2 · 7⁸ e₀)` of
`I Wt`. -/
theorem amplified_error {S : K →L[ℂ] K} (hS : IsUnitary S) {I J : P →L[ℂ] K}
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) {Sg : K →L[ℂ] K} (hSg : IsUnitary Sg)
    (hSgJ : Sg ∘L J = I) {Wt : P →L[ℂ] P} (hWt : IsUnitary Wt) {e₀ : ℝ}
    (hblock : ‖J† ∘L (S ∘L I) - (ampS 8 0 : ℂ) • Wt‖ ≤ e₀) (he : 7 ^ 8 * e₀ ≤ 7 / 16) :
    ‖(Sg ∘L ampCirc S I J 8) ∘L I - I ∘L Wt‖ ≤ Real.sqrt (2 * (7 ^ 8 * e₀)) := by
  have hSl : S† ∘L S = 1 := hS.1
  have hT : (S ∘L I)† ∘L (S ∘L I) = 1 := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc _ _ I, hSl, one_comp', hI]
  have hWl : Wt† ∘L Wt = 1 := hWt.1
  have hWr : Wt ∘L Wt† = 1 := hWt.2
  have h8 := ampIter_block_error J (S ∘L I) hJ hT hWr (norm_le_one_of_isometry hWl) 8 hblock he
    8 le_rfl
  rw [ampS_top, Complex.ofReal_one, one_smul] at h8
  have hfull := full_output_error J (ampIter J (S ∘L I) 8) hJ
    (ampIter_isometry J (S ∘L I) hJ hT 8) hWl h8
  rw [ampIter_eq_ampCirc hS hI hJ 8] at hfull
  have h : (Sg ∘L ampCirc S I J 8) ∘L I - I ∘L Wt =
      Sg ∘L (ampCirc S I J 8 ∘L I - J ∘L Wt) := by
    rw [comp_sub, ← hSgJ]
    simp only [comp_assoc]
  rw [h, EncodedOracle.norm_comp_eq Sg hSg.1]
  exact hfull

end Amplified

/-! ### The circuit for `q ≥ 1` -/

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

theorem Known.Cop_star (K : Known P W) (U : W →L[ℂ] W) : star (K.Cop U) = K.Cop U := by
  simp only [Known.Cop, star_eq_adjoint, adjoint_comp, adjoint_adjoint, K.Z_adjoint, comp_assoc]

/-- The evolution `e^{-i T C}` for `C = B† Z B`. -/
theorem Known.evolution_unitary (K : Known P W) (U : W →L[ℂ] W) (T : ℝ) :
    IsUnitary (NormedSpace.exp ((-(I * (T : ℂ))) • K.Cop U)) := by
  rw [← neg_mul]
  exact LabeledAdjointSimulation.evolution_unitary (K.Cop U) (K.Cop_star U) T

theorem ampS_mul_le : ampS 8 0 * 3000 ≤ 1 := by
  have h := ampS_zero_le 8
  have hp := Real.pi_lt_d2
  have h0 : 0 ≤ ampS 8 0 := ampS_nonneg 8 0 (by norm_num)
  have : ampS 8 0 ≤ 3.15 / (2 * 3 ^ 8) := h.trans (by gcongr)
  norm_num at this
  linarith

/-- A mesh size meeting the budget of `opt:eq:finite-mesh`. -/
theorem exists_mesh {a η : ℝ} (ha : 0 < a) (hη : 0 < η) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 0 < m ∧ 8 * a * n ≤ m ∧ 128 * 3000 * a ^ 3 * n ^ 4 / m ^ 2 ≤ η / 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : 0 ≤ 768000 * a ^ 3 * n ^ 4 / η := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (8 * a * n + 768000 * a ^ 3 * n ^ 4 / η + 1)
  have h8 : 0 ≤ 8 * a * n := by positivity
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hm0 : 0 < m := by exact_mod_cast (lt_of_lt_of_le one_pos hm1)
  refine ⟨m, hm0, by linarith, ?_⟩
  have hmB : 768000 * a ^ 3 * n ^ 4 / η ≤ m := by linarith
  have hmm : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hkey : 768000 * a ^ 3 * n ^ 4 ≤ η * m ^ 2 := by
    rw [div_le_iff₀ hη] at hmB
    nlinarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The circuit for `q ≥ 1`** (Sections `opt:sec:factor` and `opt:sec:tail`). For the factor
interface with `D ⪯ δ I`, `q ≥ 1`, `M ≥ 1`, `M ≥ 2·27² q²Mδ` and a factorial tail
`2 · 3001 (e² 27² q²Mδ/M)^M ≤ ε²/(4·7⁸)`, there are a finite register label type `ι`, a known
isometric input `P → ℂ^ι ⊗ W` and a program whose only oracle is the factor query `I_ι ⊗ U` (with
its adjoint), with at most `2·3⁸·27·qM` queries and full-output error at most `ε` for
`e^{-i q²M C}`. -/
theorem core [FiniteDimensional ℂ P] [FiniteDimensional ℂ W] (K : Known P W) {X : Type*}
    (U : X → W →L[ℂ] W) (hU : ∀ x, IsUnitary (U x)) {q : ℝ} (hq : 1 ≤ q) {M : ℕ} (hM : 1 ≤ M)
    {δ : ℝ} (hδ : 0 ≤ δ) (hD : ∀ x, K.Dop (U x) ≤ (δ : ℂ) • (1 : P →L[ℂ] P))
    (hMb : 2 * 27 ^ 2 * (q ^ 2 * M * δ) ≤ M) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (htail : 2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * (q ^ 2 * M * δ) / M) ^ M ≤
      ε ^ 2 / (4 * 7 ^ 8)) :
    ∃ (ι : Type) (_ : Fintype ι) (inp : P →L[ℂ] PiLp 2 (fun _ : ι => W))
      (p : Program (fun x => WeightedClock.diagonal (fun _ : ι => U x))),
      inp† ∘L inp = 1 ∧ (p.count : ℝ) ≤ 2 * 3 ^ 8 * 27 * (q * M) ∧
      ∀ x, ‖p.eval x ∘L inp - inp ∘L
        NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • K.Cop (U x))‖ ≤ ε := by
  -- the clock weights
  set n := clockLength q M with hn_def
  set lam := clockWeight q M with hlam_def
  have hn1 : 1 ≤ n := by simp [hn_def, clockLength]
  have hnle : (n : ℝ) ≤ 27 * (q * M) := clockLength_le hq hM
  have hlam : ∑ j ∈ Icc 1 n, |lam j| ≤ 3000 := sum_abs_clockWeight_le hq hM
  -- the error budget
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  set a : ℝ := q * M with ha_def
  have ha : 0 < a := by positivity
  set η : ℝ := ε ^ 2 / (2 * 7 ^ 8) with hη_def
  have hη : 0 < η := by positivity
  set s : ℝ := ampS 8 0 with hs_def
  have hs0 : 0 ≤ s := ampS_nonneg 8 0 (by norm_num)
  have hs1 : s ≤ 1 := by have := ampS_mul_le; linarith
  have hsl : s * ∑ j ∈ Icc 1 n, |lam j| ≤ 1 :=
    (mul_le_mul_of_nonneg_left hlam hs0).trans ampS_mul_le
  have hsη : s * η ≤ η := mul_le_of_le_one_left hη.le hs1
  have hη8 : 7 ^ 8 * η = ε ^ 2 / 2 := by rw [hη_def]; ring
  have hε2 : ε ^ 2 ≤ 1 / 4 := by
    have := pow_le_pow_left₀ hε.le hε1 2
    norm_num at this
    linarith
  have he : 7 ^ 8 * (s * η) ≤ 7 / 16 := by
    have := mul_le_mul_of_nonneg_left hsη (by norm_num : (0 : ℝ) ≤ 7 ^ 8)
    linarith
  have hfin : Real.sqrt (2 * (7 ^ 8 * (s * η))) ≤ ε := by
    rw [Real.sqrt_le_left hε.le]
    have := mul_le_mul_of_nonneg_left hsη (by norm_num : (0 : ℝ) ≤ 7 ^ 8)
    linarith
  have htailη : 2 * (3000 + 1) * (Real.exp 2 * 27 ^ 2 * (q ^ 2 * M * δ) / M) ^ M ≤ η / 2 :=
    htail.trans (le_of_eq (by rw [hη_def]; ring))
  -- the mesh
  obtain ⟨m, hm0, hm8, hmesh⟩ := exists_mesh ha hη n hn1
  set v : ℝ := a / m with hv_def
  have hv : 0 ≤ v := by positivity
  -- the structured circuit
  set I' := lcuIn (V := BlockOperator.H m W) K.E s lam n with hI'_def
  set J' := lcuOut (V := BlockOperator.H m W) K.E s lam n with hJ'_def
  have hI : I'† ∘L I' = 1 := lcuIn_isometry K.E_isometry hs0 hsl
  have hJ : J'† ∘L J' = 1 := lcuOut_isometry K.E_isometry hs0 hsl
  set S : X → Work W n m →L[ℂ] Work W n m := fun x =>
    lcuSelect (wA K.E v m) (wB (K.priv q (U x)) K.E v m) (wC K.E v m)
      (cascD (K.priv q (U x)) K.E v m) n with hS_def
  have hSimp : Implements (fun x => liftU (U x) n m) S (n * 2) :=
    select_implements K q hv m hn1 U hU
  have hLift : ∀ x, IsUnitary (liftU (U x) n m) := fun x => liftU_unitary (hU x) n m
  have hSu : ∀ x, IsUnitary (S x) := fun x => hSimp.unitary hLift x
  have hFimp : Implements (fun x => liftU (U x) n m)
      (fun x => lcuSign (W := W) (V := BlockOperator.H m W) s lam n * ampCirc (S x) I' J' 8)
      (0 + 3 ^ 8 * (n * 2)) :=
    (Implements.fixed (O := fun x => liftU (U x) n m)
      (lcuSign (W := W) (V := BlockOperator.H m W) s lam n)
      (lcuSign_unitary s lam n)).mul (ampCirc_implements hSimp hI hJ 8)
  -- the error of the structured circuit
  have hblock : ∀ x, ‖J'† ∘L (S x ∘L I') - (ampS 8 0 : ℂ) •
      NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • K.Cop (U x))‖ ≤ s * η := by
    intro x
    have hblock0 : J'† ∘L (S x ∘L I') = (s : ℂ) • ∑ j ∈ Icc 1 n,
        (lam j : ℂ) • ces (cascTransfer (K.priv q (U x)) K.E v m) j :=
      cascade_block K.E_isometry _ v m s lam n
    have hmeshx := K.finite_mesh (q := q) (by linarith) (hU x) ha.le hn1 hm0 hm8 hlam
    have htailx := tail_estimate hq hM hnle hlam
      (fun k j hjk hkM => clock_moments hq hM hjk hkM) hδ (K.Dop_nonneg (U x)) (hD x)
      (K.neg_Dop_le_Cop (U x)) (K.Cop_le_Dop (U x)) hMb
    have hX : ‖∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (cascTransfer (K.priv q (U x)) K.E v m) j -
        NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • K.Cop (U x))‖ ≤ η := by
      have h1 := norm_sub_le_norm_sub_add_norm_sub
        (∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (cascTransfer (K.priv q (U x)) K.E v m) j)
        (∑ j ∈ Icc 1 n, (lam j : ℂ) • ces (Fop a q (K.Cop (U x)) (K.Dop (U x))) j)
        (NormedSpace.exp ((-(I * ((q ^ 2 * M : ℝ) : ℂ))) • K.Cop (U x)))
      have h2 := hmeshx.trans hmesh
      have h3 := htailx.trans htailη
      linarith
    rw [hblock0, ← hs_def, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left hX hs0
  have herr := fun x => le_trans (amplified_error (hSu x) hI hJ (lcuSign_unitary (W := W)
    (V := BlockOperator.H m W) s lam n) (lcuSign_comp_lcuOut K.E s lam n)
    (K.evolution_unitary (U x) (q ^ 2 * M)) (hblock x) he) hfin
  -- flattening
  have hflat := Implements.of_oracle_eq (fun x => flat_liftU (U x) n m)
    (hFimp.transport (flat W n m))
  obtain ⟨p, hpeval, hpcount⟩ := hflat
  refine ⟨Lbl n m, inferInstance, embed (flat W n m) I', p, embed_isometry _ hI, ?_, ?_⟩
  · have hc : p.count ≤ 3 ^ 8 * (n * 2) := by simpa using hpcount
    have hc' : (p.count : ℝ) ≤ 3 ^ 8 * (n * 2) := by exact_mod_cast hc
    calc (p.count : ℝ) ≤ 3 ^ 8 * (n * 2) := hc'
      _ ≤ 3 ^ 8 * (27 * (q * M) * 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hnle (by norm_num)
      _ = 2 * 3 ^ 8 * 27 * (q * M) := by ring
  · intro x
    rw [hpeval x]
    beta_reduce
    rw [ContinuousLinearMap.mul_def, embed_error]
    convert herr x using 4

end

end SignedFactorSimulation
