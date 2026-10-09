import LinearSystemLowerBound.Weight.Kernel
import SparseLinearSystems.Protocol.Tree

/-!
# The XOR bound for adaptive protocols

The released adaptive protocols (`SparseLinearSystems.Protocol.Tree`) perform fresh measured
runs, branch classically on their outcomes and end with bounded fresh-trial preparations.
For inputs `j : ι → Fin m`, an oracle family whose labels have weight growth `C ^ w l` and a
decoder observable `M` with `‖M‖ ≤ 1`, the parity correlation of the heralded output satisfies

`|∑_j (-1)^{F(j)} Re tr(M σ_j)| ≤ 2^{-|ι|} C^{worstCost} m^{|ι|}`

(`tree_xor`), where `σ_j` is the unnormalised heralded output on input `j` (failure
contributes nothing).  The proof carries a positive semidefinite kernel through the tree
(`tree_bound`, `protocol_bound`): a measured run splits the kernel (`gram_split`), every run
multiplies its potential by at most `C ^ cost` (`pot_growth`), and the parity bound controls
each heralded output (`parity_kernel_bound`).
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
variable {K F E L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ### Correlation with a decoder -/

section Corr

/-- Correlation `Re tr(M A)` of an output operator with a decoder observable. -/
def corr (M A : E →L[ℂ] E) : ℝ :=
  (LinearMap.trace ℂ E ((M ∘L A : E →L[ℂ] E) : E →ₗ[ℂ] E)).re

omit [CompleteSpace E] in
theorem corr_add (M A B : E →L[ℂ] E) : corr M (A + B) = corr M A + corr M B := by
  simp only [corr, comp_add, ContinuousLinearMap.toLinearMap_add, map_add, Complex.add_re]

omit [CompleteSpace E] in
theorem corr_smul_real (M A : E →L[ℂ] E) (c : ℝ) : corr M ((c : ℂ) • A) = c * corr M A := by
  simp only [corr, comp_smul, ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul,
    Complex.re_ofReal_mul]

omit [CompleteSpace E] in
theorem corr_zero (M : E →L[ℂ] E) : corr M 0 = 0 := by
  simp [corr]

omit [CompleteSpace E] in
theorem corr_sum {α : Type*} (s : Finset α) (M : E →L[ℂ] E) (A : α → E →L[ℂ] E) :
    corr M (∑ i ∈ s, A i) = ∑ i ∈ s, corr M (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [corr_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, corr_add, ih]

omit [CompleteSpace E] in
theorem corr_pure [FiniteDimensional ℂ E] (M : E →L[ℂ] E) (a : E) :
    corr M (ODEMixedOutput.pureOperator a) = (⟪a, M a⟫_ℂ).re := by
  simp only [corr, ODEMixedOutput.pureOperator, InnerProductSpace.comp_rankOne,
    InnerProductSpace.trace_rankOne]

end Corr

/-! ### The parity functional -/

section ParityFun

/-- `Λ(G, f) = ∑_j (-1)^{F(j)} Re G_jj f(j)`. -/
def parityFun (G : Matrix (ι → Fin m) (ι → Fin m) ℂ) (f : (ι → Fin m) → ℝ) : ℝ :=
  ∑ j, parSign j * ((G j j).re * f j)

theorem parityFun_add (G : Matrix (ι → Fin m) (ι → Fin m) ℂ) (f g : (ι → Fin m) → ℝ) :
    parityFun G (fun j => f j + g j) = parityFun G f + parityFun G g := by
  simp only [parityFun, mul_add, Finset.sum_add_distrib]

theorem parityFun_mul (G : Matrix (ι → Fin m) (ι → Fin m) ℂ) (c : ℝ) (f : (ι → Fin m) → ℝ) :
    parityFun G (fun j => c * f j) = c * parityFun G f := by
  simp only [parityFun, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem parityFun_sum {α : Type*} (s : Finset α) (G : Matrix (ι → Fin m) (ι → Fin m) ℂ)
    (f : α → (ι → Fin m) → ℝ) :
    parityFun G (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, parityFun G (f i) := by
  simp only [parityFun, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [CompleteSpace K] in
theorem parityFun_hadamard_gram (G : Matrix (ι → Fin m) (ι → Fin m) ℂ) (v : (ι → Fin m) → K)
    (f : (ι → Fin m) → ℝ) :
    parityFun (G ⊙ Matrix.gram ℂ v) f = parityFun G (fun j => ‖v j‖ ^ 2 * f j) := by
  simp only [parityFun, Matrix.hadamard_apply, Matrix.gram_apply, inner_self_cpx]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
  ring

end ParityFun

/-! ### Fresh runs -/

section Runs

variable {O : L → (ι → Fin m) → K →L[ℂ] K}

/-- One fresh run multiplies the potential of the kernel by at most `C ^ cost`. -/
theorem pot_run {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (hG : G.PosSemidef) (w : L → ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hO : ∀ l, Growth (O l) (C ^ w l))
    (hO' : ∀ l, Growth (fun j => star (O l j)) (C ^ w l))
    (p : MultiOracleCircuit.Program O) (seed : K) (hseed : ‖seed‖ = 1) :
    pot (G ⊙ Matrix.gram ℂ (fun j => p.eval j seed)) ≤ C ^ p.cost w * pot G := by
  have h := pot_growth hG (growth_program O w C hC hO hO' p)
    (WithLp.toLp 2 (fun _ => seed) : Fam (ι → Fin m) K)
  simp only [joint_apply] at h
  rwa [hadamard_gram_const G seed hseed] at h

/-- A measured run splits the potential. -/
theorem pot_split {G : Matrix (ι → Fin m) (ι → Fin m) ℂ} (Fl : E →L[ℂ] K)
    (hF : Fl† ∘L Fl = 1) (v : (ι → Fin m) → K) :
    pot (G ⊙ Matrix.gram ℂ (fun j => (Fl†) (v j))) +
        pot (G ⊙ Matrix.gram ℂ (fun j => v j - Fl ((Fl†) (v j)))) =
      pot (G ⊙ Matrix.gram ℂ v) := by
  rw [gram_split Fl hF v, Matrix.hadamard_add, pot_add]

/-- Failure weight of a unitary run: `1 - ‖F† v‖² = ‖v - F F† v‖²`. -/
theorem failure_weight (Fl : E →L[ℂ] K) (hF : Fl† ∘L Fl = 1) (v : K) (hv : ‖v‖ = 1) :
    1 - ‖(Fl†) v‖ ^ 2 = ‖v - Fl ((Fl†) v)‖ ^ 2 := by
  have h := ODERepeatProtocol.herald_probability_partition Fl hF v
  rw [hv] at h
  linarith

end Runs

/-! ### Final protocols -/

section Protocols

variable [FiniteDimensional ℂ E] {O : L → (ι → Fin m) → K →L[ℂ] K}

/-- **Kernel bound for a final protocol.** -/
theorem protocol_bound (hm : Even m) (hm0 : m ≠ 0) (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, Growth (O l) (C ^ w l))
    (hO' : ∀ l, Growth (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) :
    ∀ (p : ODERepeatProtocol.Protocol O E) (G : Matrix (ι → Fin m) (ι → Fin m) ℂ),
      G.PosSemidef →
      |parityFun G (fun j => corr M (p.successDensity j))| ≤
        (1 / 2) ^ Fintype.card ι * C ^ p.worstCost w * pot G := by
  have hC0 : 0 ≤ C := by linarith
  intro p
  induction p with
  | abort =>
      intro G hG
      simp only [ODERepeatProtocol.Protocol.successDensity, corr_zero, parityFun, mul_zero,
        Finset.sum_const_zero, abs_zero]
      exact mul_nonneg (by positivity) (pot_nonneg hG)
  | freshTrial t k ih =>
      intro G hG
      have hch : (0 : ℝ) < t.choices := by exact_mod_cast t.choices_pos
      set v : Fin t.choices → (ι → Fin m) → K := fun c j => (t.circuit c).eval j t.seed
      set a : Fin t.choices → Fam (ι → Fin m) E :=
        fun c => WithLp.toLp 2 (fun j => (t.output†) (v c j))
      set qv : Fin t.choices → (ι → Fin m) → K :=
        fun c j => v c j - t.output ((t.output†) (v c j))
      have hvnorm : ∀ c j, ‖v c j‖ = 1 := by
        intro c j
        rw [isUnitary_norm ((t.circuit c).eval_unitary hU j), t.seed_unit]
      -- the correlation of the recursive output
      have hcorr : ∀ j, corr M ((ODERepeatProtocol.Protocol.freshTrial t k).successDensity j) =
          ∑ c, ((t.choices : ℝ)⁻¹ * (⟪a c j, M (a c j)⟫_ℂ).re +
            (t.choices : ℝ)⁻¹ * (‖qv c j‖ ^ 2 * corr M (k.successDensity j))) := by
        intro j
        have hmean : 1 - t.meanSuccess j = (t.choices : ℝ)⁻¹ * ∑ c, ‖qv c j‖ ^ 2 := by
          have hfw : ∀ c, ‖qv c j‖ ^ 2 = 1 - t.probability j c := by
            intro c
            rw [← failure_weight t.output t.output_isometry (v c j) (hvnorm c j)]
            rfl
          simp only [hfw, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
          rw [ODERepeatProtocol.TrialFamily.meanSuccess]
          field_simp
        have h1 : ((t.choices : ℂ))⁻¹ = (((t.choices : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul,
          ODERepeatProtocol.Protocol.successDensity, corr_add, corr_smul_real,
          ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus, h1, corr_smul_real, corr_sum,
          hmean]
        simp only [corr_pure, ODERepeatProtocol.TrialFamily.amplitude, a, v]
        ring
      have hsplit : parityFun G
          (fun j => corr M ((ODERepeatProtocol.Protocol.freshTrial t k).successDensity j)) =
          ∑ c, (t.choices : ℝ)⁻¹ * (parityFun G (fun j => (⟪a c j, M (a c j)⟫_ℂ).re) +
            parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j))) := by
        simp only [hcorr]
        rw [parityFun_sum]
        apply Finset.sum_congr rfl
        intro c _
        rw [parityFun_add, parityFun_mul, parityFun_mul, parityFun_hadamard_gram, mul_add]
      rw [hsplit]
      have hbound : ∀ c, |parityFun G (fun j => (⟪a c j, M (a c j)⟫_ℂ).re) +
          parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j))| ≤
          (1 / 2) ^ Fintype.card ι * C ^ (t.maxCost w + k.worstCost w) * pot G := by
        intro c
        have hA := parity_kernel_bound hm hm0 hG M hM (a c)
        have hB := ih (G ⊙ Matrix.gram ℂ (qv c)) (hadamard_gram_posSemidef hG (qv c))
        have hpa : 0 ≤ pot (G ⊙ Matrix.gram ℂ (fun j => a c j)) :=
          pot_hadamard_gram_nonneg hG (a c)
        have hpq : 0 ≤ pot (G ⊙ Matrix.gram ℂ (qv c)) :=
          pot_hadamard_gram_nonneg hG (WithLp.toLp 2 (qv c))
        have hsum : pot (G ⊙ Matrix.gram ℂ (fun j => a c j)) +
            pot (G ⊙ Matrix.gram ℂ (qv c)) = pot (G ⊙ Matrix.gram ℂ (v c)) :=
          pot_split t.output t.output_isometry (v c)
        have hrun : pot (G ⊙ Matrix.gram ℂ (v c)) ≤ C ^ (t.circuit c).cost w * pot G :=
          pot_run hG w hC0 hO hO' (t.circuit c) t.seed t.seed_unit
        have hcost : C ^ (t.circuit c).cost w ≤ C ^ t.maxCost w :=
          pow_le_pow_right₀ hC (t.cost_le_maxCost w c)
        have hk1 : 1 ≤ C ^ k.worstCost w := one_le_pow₀ hC
        have hpG : 0 ≤ pot G := pot_nonneg hG
        have hhalf : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card ι := by positivity
        calc _ ≤ |parityFun G (fun j => (⟪a c j, M (a c j)⟫_ℂ).re)| +
              |parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j))| :=
              abs_add_le _ _
          _ ≤ (1 / 2) ^ Fintype.card ι * pot (G ⊙ Matrix.gram ℂ (fun j => a c j)) +
              (1 / 2) ^ Fintype.card ι * C ^ k.worstCost w * pot (G ⊙ Matrix.gram ℂ (qv c)) :=
              add_le_add hA hB
          _ ≤ (1 / 2) ^ Fintype.card ι * C ^ k.worstCost w *
              (pot (G ⊙ Matrix.gram ℂ (fun j => a c j)) + pot (G ⊙ Matrix.gram ℂ (qv c))) := by
              nlinarith [mul_le_mul_of_nonneg_left hk1 (mul_nonneg hhalf hpa)]
          _ ≤ (1 / 2) ^ Fintype.card ι * C ^ k.worstCost w *
              (C ^ (t.circuit c).cost w * pot G) := by
              rw [hsum]
              exact mul_le_mul_of_nonneg_left hrun (by positivity)
          _ ≤ (1 / 2) ^ Fintype.card ι * C ^ k.worstCost w * (C ^ t.maxCost w * pot G) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact mul_le_mul_of_nonneg_right hcost hpG
          _ = (1 / 2) ^ Fintype.card ι * C ^ (t.maxCost w + k.worstCost w) * pot G := by
              rw [pow_add]; ring
      calc |∑ c, (t.choices : ℝ)⁻¹ * (parityFun G (fun j => (⟪a c j, M (a c j)⟫_ℂ).re) +
            parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j)))|
          ≤ ∑ c, |(t.choices : ℝ)⁻¹ * (parityFun G (fun j => (⟪a c j, M (a c j)⟫_ℂ).re) +
            parityFun (G ⊙ Matrix.gram ℂ (qv c)) (fun j => corr M (k.successDensity j)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _c : Fin t.choices, (t.choices : ℝ)⁻¹ *
            ((1 / 2) ^ Fintype.card ι * C ^ (t.maxCost w + k.worstCost w) * pot G) := by
            apply Finset.sum_le_sum
            intro c _
            rw [abs_mul, abs_of_pos (inv_pos.mpr hch)]
            exact mul_le_mul_of_nonneg_left (hbound c) (inv_nonneg.mpr hch.le)
        _ = (1 / 2) ^ Fintype.card ι * C ^ (ODERepeatProtocol.Protocol.freshTrial t k).worstCost w *
            pot G := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ODERepeatProtocol.Protocol.worstCost]
            field_simp

end Protocols

/-! ### Trees -/

section Trees

variable [FiniteDimensional ℂ E] {O : L → (ι → Fin m) → K →L[ℂ] K}

/-- **Kernel bound for an adaptive protocol.** -/
theorem tree_bound (hm : Even m) (hm0 : m ≠ 0) (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, Growth (O l) (C ^ w l))
    (hO' : ∀ l, Growth (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) :
    ∀ (T : Tree O F E) (G : Matrix (ι → Fin m) (ι → Fin m) ℂ), G.PosSemidef →
      |parityFun G (fun j => corr M (T.successDensity j))| ≤
        (1 / 2) ^ Fintype.card ι * C ^ T.worstCost w * pot G := by
  have hC0 : 0 ≤ C := by linarith
  intro T
  induction T with
  | final p =>
      intro G hG
      exact protocol_bound hm hm0 hU w C hC hO hO' M hM p G hG
  | test t s f ihs ihf =>
      intro G hG
      set v : (ι → Fin m) → K := fun j => t.circuit.eval j t.seed
      set qv : (ι → Fin m) → K := fun j => v j - t.flag ((t.flag†) (v j))
      have hvnorm : ∀ j, ‖v j‖ = 1 := by
        intro j
        rw [isUnitary_norm (t.circuit.eval_unitary hU j), t.seed_unit]
      have hsd : ∀ j, corr M ((Tree.test t s f).successDensity j) =
          ‖(t.flag†) (v j)‖ ^ 2 * corr M (s.successDensity j) +
            ‖qv j‖ ^ 2 * corr M (f.successDensity j) := by
        intro j
        have hfw := failure_weight t.flag t.flag_isometry (v j) (hvnorm j)
        change corr M ((algebraMap ℝ ℂ (t.probability j)) • s.successDensity j +
          (algebraMap ℝ ℂ (1 - t.probability j)) • f.successDensity j) = _
        have hfw' : ‖qv j‖ ^ 2 = 1 - ‖(t.flag†) (v j)‖ ^ 2 := hfw.symm
        rw [corr_add]
        erw [corr_smul_real, corr_smul_real]
        simp only [Algebra.algebraMap_self, RingHom.id_apply, TestRun.probability]
        rw [hfw']
      have hsplit : parityFun G (fun j => corr M ((Tree.test t s f).successDensity j)) =
          parityFun (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j)))
            (fun j => corr M (s.successDensity j)) +
          parityFun (G ⊙ Matrix.gram ℂ qv) (fun j => corr M (f.successDensity j)) := by
        simp only [hsd]
        rw [parityFun_add, parityFun_hadamard_gram, parityFun_hadamard_gram]
      rw [hsplit]
      have hGs := hadamard_gram_posSemidef hG (fun j => (t.flag†) (v j))
      have hGf := hadamard_gram_posSemidef hG qv
      have hS := ihs _ hGs
      have hF := ihf _ hGf
      have hps : 0 ≤ pot (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j))) := pot_nonneg hGs
      have hpf : 0 ≤ pot (G ⊙ Matrix.gram ℂ qv) := pot_nonneg hGf
      have hsum := pot_split (G := G) t.flag t.flag_isometry v
      have hrun : pot (G ⊙ Matrix.gram ℂ v) ≤ C ^ t.circuit.cost w * pot G :=
        pot_run hG w hC0 hO hO' t.circuit t.seed t.seed_unit
      have hms : C ^ s.worstCost w ≤ C ^ max (s.worstCost w) (f.worstCost w) :=
        pow_le_pow_right₀ hC (le_max_left _ _)
      have hmf : C ^ f.worstCost w ≤ C ^ max (s.worstCost w) (f.worstCost w) :=
        pow_le_pow_right₀ hC (le_max_right _ _)
      have hhalf : 0 ≤ (1 / 2 : ℝ) ^ Fintype.card ι := by positivity
      have hpG : 0 ≤ pot G := pot_nonneg hG
      set Cm := C ^ max (s.worstCost w) (f.worstCost w)
      calc _ ≤ |parityFun (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j)))
              (fun j => corr M (s.successDensity j))| +
            |parityFun (G ⊙ Matrix.gram ℂ qv) (fun j => corr M (f.successDensity j))| :=
            abs_add_le _ _
        _ ≤ (1 / 2) ^ Fintype.card ι * C ^ s.worstCost w *
              pot (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j))) +
            (1 / 2) ^ Fintype.card ι * C ^ f.worstCost w * pot (G ⊙ Matrix.gram ℂ qv) :=
            add_le_add hS hF
        _ ≤ (1 / 2) ^ Fintype.card ι * Cm *
              (pot (G ⊙ Matrix.gram ℂ (fun j => (t.flag†) (v j))) +
                pot (G ⊙ Matrix.gram ℂ qv)) := by
            nlinarith [mul_le_mul_of_nonneg_left hms (mul_nonneg hhalf hps),
              mul_le_mul_of_nonneg_left hmf (mul_nonneg hhalf hpf)]
        _ ≤ (1 / 2) ^ Fintype.card ι * Cm * (C ^ t.circuit.cost w * pot G) := by
            rw [hsum]
            exact mul_le_mul_of_nonneg_left hrun (by positivity)
        _ = (1 / 2) ^ Fintype.card ι * C ^ (Tree.test t s f).worstCost w * pot G := by
            simp only [Cm, Tree.worstCost, pow_add]
            ring

end Trees

/-! ### The XOR bound -/

section XOR

theorem kron_row_sum (a : Matrix (Fin m) (Fin m) ℂ) (j : ι → Fin m) :
    ∑ j', kron (ι := ι) a j j' = ∏ b, ∑ q, a (j b) q := by
  simp only [kron_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem weight_row_sum (hm : m ≠ 0) (q : Fin m) : ∑ q', weight m q q' = 1 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  simp only [weight, avg, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The potential of the trivial kernel is the number of inputs. -/
theorem pot_onesKernel (hm : m ≠ 0) : pot (onesKernel ι m) = (m : ℝ) ^ Fintype.card ι := by
  have hw : (weight m)ᴴ * weight m = weight m * weight m := by rw [weight_conjTranspose]
  have hrow : ∀ q, ∑ q', (weight m * weight m) q q' = 1 := by
    intro q
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, weight_row_sum hm, mul_one]
  have hwsq : wsq ι m = kron (weight m * weight m) := by
    rw [wsq, kron_conjTranspose, kron_mul, hw]
  simp only [pot, onesKernel, Matrix.of_apply, mul_one, hwsq, kron_row_sum, hrow,
    Finset.prod_const_one, Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  norm_cast
  rw [Finset.prod_const, Finset.card_univ]

/-- **XOR bound for adaptive protocols.**  For even `m`, an oracle family whose labels have
weight growth `C ^ w l` (both directions) and a decoder `M` with `‖M‖ ≤ 1`, the parity
correlation of the heralded output is at most `2^{-|ι|} C^{worstCost} m^{|ι|}`. -/
theorem tree_xor [FiniteDimensional ℂ E] {O : L → (ι → Fin m) → K →L[ℂ] K}
    (hm : Even m) (hm0 : m ≠ 0) (hU : ∀ l j, OracleCircuit.IsUnitary (O l j))
    (w : L → ℕ) (C : ℝ) (hC : 1 ≤ C) (hO : ∀ l, Growth (O l) (C ^ w l))
    (hO' : ∀ l, Growth (fun j => star (O l j)) (C ^ w l))
    (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖) (T : Tree O F E) :
    |∑ j, parSign j * corr M (T.successDensity j)| ≤
      (1 / 2) ^ Fintype.card ι * C ^ T.worstCost w * (m : ℝ) ^ Fintype.card ι := by
  have h := tree_bound hm hm0 hU w C hC hO hO' M hM T (onesKernel ι m) onesKernel_posSemidef
  rw [pot_onesKernel hm0] at h
  have hpf : parityFun (onesKernel ι m) (fun j => corr M (T.successDensity j)) =
      ∑ j, parSign j * corr M (T.successDensity j) := by
    simp [parityFun, onesKernel]
  rwa [hpf] at h

end XOR

end

end LinearSystemLowerBound
