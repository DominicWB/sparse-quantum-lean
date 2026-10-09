import LinearSystemLowerBound.Theorem

/-!
# Reading the output through a contraction into output and garbage registers

`lower_bound_sharp` identifies the output space `E` with the output register and a garbage
register `G` by a unitary `V`, which forces `dim E = N |G|`.  An algorithm on qubits whose
output register has dimension `2^a ≥ N` does not have this form when `N` is not a power of
two.  As in the `SparseLowerBounds` library (`Readout.Accurate`, an isometry `e` into system ⊗
garbage), the output is read here through any fixed linear map
`e : E → ℂ^{Ind} ⊗ ℂ^{G}` of norm at most one, in particular any isometry, and the reduced
output state is `Tr_G (e ρ e†)`.  For instance, if a qubit output register contains the
coordinate space of the hard family, an isometry `e` can send the basis states outside it to a
flag in the garbage register; `ρ ↦ Tr_G (e ρ e†)` is then a channel that fixes the target, so
it does not increase the trace distance to the target (this example is not formalised).

* `corr_readout`: `corr B (e A e†) = corr (e† B e) A`, by cyclicity of the trace;
* `norm_readout_le`: `e† B e` is a contraction when `B` and `e` are;
* `readout_contraction_of_isometry`: an isometry (`e† e = 1`) is a contraction;
* `readout_unitary`: for a unitary `V` the readout `V ρ V†` is `V.conjStarAlgEquiv ρ`, so the
  unitary identification of `lower_bound_sharp` is a special case;
* `tree_bias_readout`: heralded accuracy of the reduced state gives the signed correlation
  `(2/3)(p - 2ε)` for the decoder `e† (M ⊗ I_G) e`;
* `lower_bound_sharp_readout`, `lower_bound_readout`: Theorem `qlsl:thm:main` for this readout,
  with the constants `1/1536` and `1/3072`;
* `lower_bound_sharp_via_readout`: `lower_bound_sharp` (unitary identification) as the special
  case `e = V`.
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped InnerProductSpace InnerProduct
open SparseHamiltonian SparseLinearSystems.Protocol ContinuousLinearMap LinearSystemLowerBound.Hard
  LinearSystemLowerBound.Params LinearSystemLowerBound.Native

section Readout

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
  [FiniteDimensional ℂ E']

/-- **Correlations through a readout**: `corr B (e A e†) = corr (e† B e) A`. -/
theorem corr_readout (e : E →L[ℂ] E') (B : E' →L[ℂ] E') (A : E →L[ℂ] E) :
    corr B (e ∘L A ∘L adjoint e) = corr (adjoint e ∘L B ∘L e) A := by
  unfold corr
  congr 1
  have h1 : ((B ∘L e ∘L A ∘L adjoint e : E' →L[ℂ] E') : E' →ₗ[ℂ] E') =
      ((B ∘L e ∘L A : E →L[ℂ] E') : E →ₗ[ℂ] E') ∘ₗ ((adjoint e : E' →L[ℂ] E) : E' →ₗ[ℂ] E) := by
    ext v
    rfl
  have h2 : (((adjoint e ∘L B ∘L e) ∘L A : E →L[ℂ] E) : E →ₗ[ℂ] E) =
      ((adjoint e : E' →L[ℂ] E) : E' →ₗ[ℂ] E) ∘ₗ ((B ∘L e ∘L A : E →L[ℂ] E') : E →ₗ[ℂ] E') := by
    ext v
    rfl
  rw [h1, LinearMap.trace_comp_comm', h2]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] in
/-- `e† B e` is a contraction when `B` and `e` are. -/
theorem norm_readout_le (e : E →L[ℂ] E') (he : ∀ v, ‖e v‖ ≤ ‖v‖) (B : E' →L[ℂ] E')
    (hB : ∀ v, ‖B v‖ ≤ ‖v‖) (v : E) : ‖(adjoint e ∘L B ∘L e) v‖ ≤ ‖v‖ := by
  have he' : ‖e‖ ≤ 1 := opNorm_le_bound _ zero_le_one fun v => by rw [one_mul]; exact he v
  have hadj : ‖adjoint e‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact he'
  calc ‖(adjoint e ∘L B ∘L e) v‖ = ‖adjoint e (B (e v))‖ := rfl
    _ ≤ ‖adjoint e‖ * ‖B (e v)‖ := le_opNorm _ _
    _ ≤ 1 * ‖e v‖ := mul_le_mul hadj (hB _) (norm_nonneg _) zero_le_one
    _ ≤ ‖v‖ := by rw [one_mul]; exact he v

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] in
/-- An isometry (`e† e = 1`) is a contraction. -/
theorem readout_contraction_of_isometry (e : E →L[ℂ] E') (he : adjoint e ∘L e = 1) (v : E) :
    ‖e v‖ ≤ ‖v‖ :=
  ((norm_map_iff_adjoint_comp_self e).mpr he v).le

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] in
/-- For a unitary identification `V` the readout `V ρ V†` is `V.conjStarAlgEquiv ρ`. -/
theorem readout_unitary (V : E ≃ₗᵢ[ℂ] E') (A : E →L[ℂ] E) :
    (V : E →L[ℂ] E') ∘L A ∘L adjoint (V : E →L[ℂ] E') = V.conjStarAlgEquiv A := by
  ext v
  rw [LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rfl

end Readout

section Bias

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E]
variable {ι : Type*} {m : ℕ} {K F L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → (ι → Fin m) → K →L[ℂ] K}

/-- **Heralded accuracy through a readout**: if the reduced output state
`Tr_G (e ρ e†)` is within trace distance `ε` of `|u⟩⟨u|`, the decoder `e† (M ⊗ I_G) e` has
signed correlation at least `(2/3)(p - 2ε)`. -/
theorem tree_bias_readout {J G : Type*} [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G]
    (e : E →L[ℂ] EuclideanSpace ℂ (J × G)) (T : Tree O F E) (x : ι → Fin m)
    (M : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (u : EuclideanSpace ℂ J) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (p ε : ℝ)
    (hp : σ * (⟪u, M u⟫_ℂ).re = p) (hpε : 2 * ε ≤ p) (hsucc : 2 / 3 ≤ T.successMass x)
    (hdist : ∃ h : (ptrace (e ∘L T.conditionalDensity x ∘L adjoint e) -
        ODEMixedOutput.pureOperator u).toLinearMap.IsSymmetric,
      ODEMixedOutput.hermitianTraceDistance (ptrace (e ∘L T.conditionalDensity x ∘L adjoint e))
        (ODEMixedOutput.pureOperator u) h ≤ ε) :
    2 / 3 * (p - 2 * ε) ≤
      σ * corr (adjoint e ∘L ampl (G := G) M ∘L e) (T.successDensity x) := by
  obtain ⟨h, hd⟩ := hdist
  apply tree_bias_of_close T x _ σ p ε hpε hsucc
  have hc := abs_corr_sub_le M hM _ _ h
  rw [corr_pure, corr_ptrace, corr_readout] at hc
  rcases hσ with hσ | hσ <;> rw [hσ] at hp ⊢ <;> rw [abs_le] at hc <;> nlinarith [hc.1, hc.2]

end Bias

/-! ### The lower bound -/

variable {Z : Type*} [Fintype Z] [AddCommGroup Z] {K F L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Theorem `qlsl:thm:main`, sharp form, for any readout of norm at most one.**  As
`lower_bound_sharp`, with the output read through a fixed linear map
`e : E → ℂ^{Ind} ⊗ ℂ^{G}` with `‖e v‖ ≤ ‖v‖` (for instance an isometry,
`readout_contraction_of_isometry`) instead of a unitary identification: if the reduced
conditional output `Tr_G (e ρ_x e†)` is within trace distance `ε` of `|x_A⟩⟨x_A|` and
success has probability at least `2/3` on every input, the protocol makes in the worst case
more than `κ √s ln(1/ε) / 1536` weighted native queries. -/
theorem lower_bound_sharp_readout (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (e : E →L[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (he : ∀ v, ‖e v‖ ≤ ‖v‖) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (e ∘L T.conditionalDensity x ∘L adjoint e) -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (ptrace (e ∘L T.conditionalDensity x ∘L adjoint e))
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w := by
  obtain ⟨hpε, -⟩ := bias_ge κ ε hκ hε hε1
  exact lower_bound_of_bias κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO T
    (adjoint e ∘L ampl (G := G) (decoderOf κ ε s) ∘L e)
    (norm_readout_le e he _ (norm_ampl_le _ fun v => decoder_norm_le v)) fun x =>
      tree_bias_readout e T x (decoderOf κ ε s) (fun v => decoder_norm_le v) (target κ ε s x)
        (parSign x) (parSign_pm x) _ ε (target_correlation κ ε s hκ hs hε hε1 x) hpε
        (hT x).1 (hT x).2

/-- **Theorem `qlsl:thm:main` for any readout of norm at most one**, with the paper's
conservative constant: `Q > κ √s ln(1/ε) / 3072`. -/
theorem lower_bound_readout (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (e : E →L[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (he : ∀ v, ‖e v‖ ≤ ‖v‖) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (e ∘L T.conditionalDensity x ∘L adjoint e) -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (ptrace (e ∘L T.conditionalDensity x ∘L adjoint e))
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 3072 < T.worstCost w := by
  have h := lower_bound_sharp_readout κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO e he T hT
  have hL : 0 < Real.log (1 / ε) := by
    have := L_ge ε hε hε1; have := log_64_gt; linarith
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < s))
  have : 0 < κ * Real.sqrt s * Real.log (1 / ε) := by
    have : (0 : ℝ) < κ := by linarith
    positivity
  linarith

/-- **The unitary form is a special case**: `lower_bound_sharp`, for a unitary identification
`V` of the output space with output and garbage registers, follows from
`lower_bound_sharp_readout` with `e = V` (`readout_unitary`). -/
theorem lower_bound_sharp_via_readout (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z, ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)) -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)))
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w :=
  lower_bound_sharp_readout κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO
    (V : E →L[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (fun v => (V.norm_map v).le) T fun x => by
      rw [readout_unitary]
      exact hT x

end

end LinearSystemLowerBound
