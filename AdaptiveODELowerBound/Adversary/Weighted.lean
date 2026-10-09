import ODELowerBoundExtensions.Release.Kernel

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Weighted adversary progress of programs and retry protocols

Manuscript lines 4181-4234 (Lemma `odel:lem:outer`: the positive spectral adversary) and line
2673 (adaptive algorithms by purification and deferred measurement). This module prepares the
adversary bound for adaptive protocols (`Adversary/Kernel`): a measured run splits the inputs'
amplitude into a success and a failure branch of input-dependent weights, so the progress of a
later part of the protocol is weighted by the earlier branch amplitudes.

**Weighted progress.** For a nonnegative symmetric adversary matrix `Γ`, a multiplier kernel
`Λ : X → X → ℂ` and weights `c : X → ℝ` with `c ≥ 0` and `‖Λ x x'‖ ≤ c x c x'`, the weighted
progress `Σ_{x,x'} Γ x x' Re (Λ x x' (⟪ψ_x, ψ_{x'}⟫ - 1))` of a unit seed run through a program
over a family implemented by Boolean phase queries changes by at most
`2 λ cost Σ_x (c x)²` (`abs_progressW_program_le`). The proof rescales: with
`Λ' = Λ/(c c')` (`‖Λ'‖ ≤ 1`, zero where `c x c x' = 0`) and the states `c x • Enc ψ`, it is the
released program bound with a multiplier, `Release.abs_progressL_program_sub_le`, after the
Boolean compilation `Reduction.exists_boolean_program`.

**Retry protocols.** `abs_kernel_progressW_le`: the same bound for the release's protocol kernel
`Release.kernel p` with the worst-case cost `p.worstCost w`; it contains the released
`Release.abs_kernel_progress_le` (`Λ = 1`, `c = 1`). The step is
`Λ (κ_t κ_k - 1) = (Λ κ_k)(κ_t - 1) + Λ (κ_k - 1)` with `‖Λ κ_k‖ ≤ c c'`, and
`κ_t - 1 = (1/M) Σ_j (⟪V^j_x ψ, V^j_{x'} ψ⟫ - 1)`.
-/

namespace AdaptiveODELowerBound.Adversary

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open ODELowerBoundExtensions.Release (kernel)
open scoped InnerProduct InnerProductSpace

variable {E W X L B I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [Fintype X] [Fintype I] {O : L → X → W →L[ℂ] W}

/-- The rescaled multiplier `Λ x x' / (c x c x')`, set to zero where `c x c x' = 0`. -/
def rescale (Λ : X → X → ℂ) (c : X → ℝ) (x x' : X) : ℂ :=
  if c x * c x' = 0 then 0 else Λ x x' / ((c x * c x' : ℝ) : ℂ)

omit [Fintype X] [Fintype I] in
/-- A multiplier bounded by the weights rescales to a multiplier of modulus at most one. -/
theorem norm_rescale_le (Λ : X → X → ℂ) (c : X → ℝ) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ c x * c x')
    (x x' : X) : ‖rescale Λ c x x'‖ ≤ 1 := by
  unfold rescale
  split_ifs with h
  · simp
  · have hpos : 0 < c x * c x' := lt_of_le_of_ne ((norm_nonneg _).trans (hΛ x x')) (Ne.symm h)
    rw [norm_div, Complex.norm_of_nonneg hpos.le]
    exact (div_le_one hpos).mpr (hΛ x x')

omit [Fintype X] [Fintype I] in
/-- Undoing the rescaling: `(Λ / (c c')) · (c c') = Λ`, also where `c x c x' = 0`. -/
theorem rescale_mul (Λ : X → X → ℂ) (c : X → ℝ) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ c x * c x')
    (x x' : X) : rescale Λ c x x' * ((c x * c x' : ℝ) : ℂ) = Λ x x' := by
  unfold rescale
  split_ifs with h
  · have h0 : ‖Λ x x'‖ ≤ 0 := h ▸ hΛ x x'
    rw [zero_mul, eq_comm, ← norm_le_zero_iff]
    exact h0
  · have h1 : ((c x * c x' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
    exact div_mul_cancel₀ _ h1

omit [Fintype X] [Fintype I] in
/-- The rescaled multiplier on the states `c x • Enc u` reproduces `Λ x x' ⟪u, v⟫`. -/
theorem rescale_mul_inner (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1) (Λ : X → X → ℂ)
    (c : X → ℝ) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ c x * c x') (x x' : X) (u v : W) :
    rescale Λ c x x' * ⟪((c x : ℝ) : ℂ) • Enc u, ((c x' : ℝ) : ℂ) • Enc v⟫_ℂ =
      Λ x x' * ⟪u, v⟫_ℂ := by
  have hb : (Enc†) (Enc v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
      congrArg (fun A : W →L[ℂ] W => A v) hEnc
  rw [inner_smul_left, inner_smul_right, ← ContinuousLinearMap.adjoint_inner_right, hb,
    Complex.conj_ofReal, ← rescale_mul Λ c hΛ x x']
  push_cast
  ring

/-- **Weighted progress of one program** (the run of a unit seed): if every label of `O` is
implemented on the isometric encoding `Enc` by at most `w l` Boolean phase queries and the
multiplier `Λ` is bounded by the weights `c ≥ 0`, then
`|Σ_{x,x'} Γ x x' Re (Λ x x' (⟪p_x ψ, p_{x'} ψ⟫ - 1))| ≤ 2 λ (cost_w p) Σ_x (c x)²`. The left
side is `Release.progressL Γ Λ (fun x => p.eval x ψ) - Release.progressL Γ Λ (fun _ => ψ)`; the
same double-sum form is used for the protocol and tree kernels, which are not Gram matrices of a
given state family. -/
theorem abs_progressW_program_le (P : ProjFamily B I) (y : X → I → Bool) (Γ : X → X → ℝ)
    (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam) (Enc : W →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l))
    (Λ : X → X → ℂ) (c : X → ℝ) (hc : ∀ x, 0 ≤ c x) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ c x * c x')
    (p : MultiOracleCircuit.Program O) (ψ : W) (hψ : ‖ψ‖ = 1) :
    |∑ x, ∑ x', Γ x x' * (Λ x x' * (⟪p.eval x ψ, p.eval x' ψ⟫_ℂ - 1)).re| ≤
      2 * lam * p.cost w * ∑ x, c x ^ 2 := by
  obtain ⟨q, hcount, hcomm⟩ := Reduction.exists_boolean_program Enc hEnc
    (fun x => P.isUnitary_phase (y x)) hO w hw p
  have hev : ∀ x (u : W), q.eval x (Enc u) = Enc (p.eval x u) := fun x u => by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun A : W →L[ℂ] B => A u) (hcomm x)
  have hψψ : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    simp
  have heq : ∑ x, ∑ x', Γ x x' * (Λ x x' * (⟪p.eval x ψ, p.eval x' ψ⟫_ℂ - 1)).re =
      ODELowerBoundExtensions.Release.progressL Γ (rescale Λ c)
          (fun x => q.eval x (((c x : ℝ) : ℂ) • Enc ψ)) -
        ODELowerBoundExtensions.Release.progressL Γ (rescale Λ c)
          (fun x => ((c x : ℝ) : ℂ) • Enc ψ) := by
    simp only [ODELowerBoundExtensions.Release.progressL, ContinuousLinearMap.map_smul, hev,
      rescale_mul_inner Enc hEnc Λ c hΛ, hψψ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    rw [mul_sub, Complex.sub_re, mul_sub]
  have hn : ∀ x, ‖((c x : ℝ) : ℂ) • Enc ψ‖ ^ 2 = c x ^ 2 := fun x => by
    rw [norm_smul, Complex.norm_of_nonneg (hc x), Reduction.norm_encode Enc hEnc, hψ, mul_one]
  rw [heq]
  refine (ODELowerBoundExtensions.Release.abs_progressL_program_sub_le P y Γ hΓ0 hΓs hlam hcert
    (rescale Λ c) (norm_rescale_le Λ c hΛ) q (fun x => ((c x : ℝ) : ℂ) • Enc ψ)).trans ?_
  simp only [hn]
  have hq : (q.count : ℝ) ≤ p.cost w := by exact_mod_cast hcount
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (mul_nonneg two_pos.le hlam))
    (Finset.sum_nonneg fun x _ => sq_nonneg _)

/-- **Weighted progress of a retry protocol**: under the hypotheses of
`abs_progressW_program_le`, the protocol kernel satisfies
`|Σ_{x,x'} Γ x x' Re (Λ x x' (κ_p(x, x') - 1))| ≤ 2 λ worstCost_w(p) Σ_x (c x)²`. -/
theorem abs_kernel_progressW_le (P : ProjFamily B I) (y : X → I → Bool) (Γ : X → X → ℝ)
    (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam) (Enc : W →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l))
    (Λ : X → X → ℂ) (c : X → ℝ) (hc : ∀ x, 0 ≤ c x) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ c x * c x')
    (p : ODERepeatProtocol.Protocol O E) :
    |∑ x, ∑ x', Γ x x' * (Λ x x' * (kernel p x x' - 1)).re| ≤
      2 * lam * p.worstCost w * ∑ x, c x ^ 2 := by
  have h2 : 0 ≤ 2 * lam := mul_nonneg two_pos.le hlam
  have hC : 0 ≤ ∑ x, c x ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  induction p with
  | abort =>
    simp only [kernel, sub_self, mul_zero, Complex.zero_re, Finset.sum_const_zero, abs_zero]
    exact mul_nonneg (mul_nonneg h2 (Nat.cast_nonneg _)) hC
  | freshTrial t k ih =>
    -- one label: the weighted program bound with the multiplier `Λ κ_k`
    have hj : ∀ j, |∑ x, ∑ x', Γ x x' * ((Λ x x' * kernel k x x') *
        (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re| ≤
          2 * lam * t.maxCost w * ∑ x, c x ^ 2 := by
      intro j
      have hΛk : ∀ x x', ‖Λ x x' * kernel k x x'‖ ≤ c x * c x' := fun x x' => by
        rw [norm_mul]
        calc ‖Λ x x'‖ * ‖kernel k x x'‖ ≤ (c x * c x') * 1 :=
              mul_le_mul (hΛ x x') (ODELowerBoundExtensions.Release.norm_kernel_le hO k x x')
                (norm_nonneg _) (mul_nonneg (hc x) (hc x'))
          _ = c x * c x' := mul_one _
      refine (abs_progressW_program_le P y Γ hΓ0 hΓs hlam hcert Enc hEnc hO w hw
        (fun x x' => Λ x x' * kernel k x x') c hc hΛk (t.circuit j) t.seed t.seed_unit).trans ?_
      have hcj : ((t.circuit j).cost w : ℝ) ≤ t.maxCost w := by
        exact_mod_cast t.cost_le_maxCost w j
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcj h2) hC
    -- the kernel recursion `Λ (κ_t κ_k - 1) = (Λ κ_k)(κ_t - 1) + Λ (κ_k - 1)`
    have hM : (t.choices : ℂ) ≠ 0 := by exact_mod_cast t.choices_pos.ne'
    have hMr : (0 : ℝ) < t.choices := by exact_mod_cast t.choices_pos
    have hdec : ∀ x x', (Λ x x' * (kernel (.freshTrial t k) x x' - 1)).re =
        (t.choices : ℝ)⁻¹ * ∑ j, ((Λ x x' * kernel k x x') *
          (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re +
        (Λ x x' * (kernel k x x' - 1)).re := by
      intro x x'
      have hk : Λ x x' * (kernel (.freshTrial t k) x x' - 1) = ((((t.choices : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ j, (Λ x x' * kernel k x x') *
            (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)) +
          Λ x x' * (kernel k x x' - 1) := by
        show Λ x x' * (ODELowerBoundExtensions.Release.trialKernel t x x' * kernel k x x' - 1) = _
        unfold ODELowerBoundExtensions.Release.trialKernel
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one, Complex.ofReal_inv, Complex.ofReal_natCast]
        linear_combination (Λ x x' * kernel k x x') * inv_mul_cancel₀ hM
      rw [hk, Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum]
    have hsplit : ∑ x, ∑ x', Γ x x' * (Λ x x' * (kernel (.freshTrial t k) x x' - 1)).re =
        (t.choices : ℝ)⁻¹ * ∑ j, ∑ x, ∑ x', Γ x x' * ((Λ x x' * kernel k x x') *
          (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re +
        ∑ x, ∑ x', Γ x x' * (Λ x x' * (kernel k x x' - 1)).re := by
      simp only [hdec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [ODELowerBoundExtensions.Release.sum_sum_sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun x' _ => by ring
    have havg : |(t.choices : ℝ)⁻¹ * ∑ j, ∑ x, ∑ x', Γ x x' * ((Λ x x' * kernel k x x') *
        (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re| ≤
          2 * lam * t.maxCost w * ∑ x, c x ^ 2 := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hMr.le)]
      calc (t.choices : ℝ)⁻¹ * |∑ j, ∑ x, ∑ x', Γ x x' * ((Λ x x' * kernel k x x') *
            (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re|
          ≤ (t.choices : ℝ)⁻¹ *
              ∑ _j : Fin t.choices, 2 * lam * t.maxCost w * ∑ x, c x ^ 2 :=
            mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => hj j)) (inv_nonneg.mpr hMr.le)
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
              inv_mul_cancel₀ hMr.ne', one_mul]
    rw [hsplit]
    refine (abs_add_le _ _).trans ((add_le_add havg ih).trans (le_of_eq ?_))
    show _ = 2 * lam * ((t.maxCost w + k.worstCost w : ℕ) : ℝ) * ∑ x, c x ^ 2
    rw [Nat.cast_add]
    ring

end

end AdaptiveODELowerBound.Adversary
