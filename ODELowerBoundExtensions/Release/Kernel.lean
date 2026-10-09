import ODELowerBoundExtensions.Release.Model

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Gram kernel of a retry protocol and its adversary progress

Manuscript lines 3743-3798 (proof of Lemma `odel:lem:outer`: the positive spectral adversary of
`SparseLowerBounds/Query/PositiveAdversary`), extended from one program to the release's retry
protocols (`ODERepeatProtocol.Protocol`).

**Kernel.** Purify each attempt by its label register: the attempt with trial family `t` prepares
`(1/√M) Σ_j |j⟩ ⊗ V_x^j ψ`, `V_x^j = (t.circuit j).eval x`, on its own fresh register, and every
attempt is run (non-adaptively) whatever the earlier heralds. The Gram kernel of these purified
states is the product over attempts of the trial kernels
`κ_t(x, x') = (1/M) Σ_j ⟪V_x^j ψ, V_{x'}^j ψ⟫` (`trialKernel`, `kernel`). It has modulus at most one
(`norm_kernel_le`); `Release/Purify` realises it by explicit unit vectors.

**Progress.** For a nonnegative symmetric adversary matrix `Γ` and a multiplier kernel `Λ` with
`|Λ| ≤ 1`, the weighted progress `Σ_{x,x'} Γ x x' Re (Λ x x' ⟪ψ_x, ψ_{x'}⟫)` (`progressL`) changes
by at most `2 λ count Σ_x ‖ψ_x‖²` under a Boolean program (`abs_progressL_program_sub_le`): the
per-query step of `PositiveAdversary.abs_progress_query_sub_le` only uses
`|Re⟪P_i ψ_x, P_i ψ_{x'}⟫| ≤ ‖P_i ψ_x‖ ‖P_i ψ_{x'}‖`, which a multiplier of modulus at most one
keeps. Writing `κ_{t·k} - 1 = (κ_t - 1) κ_k + (κ_k - 1)` and compiling every trial circuit to a
Boolean program through the encoding (`Reduction.exists_boolean_program`, at most `cost w` queries)
gives the protocol bound `abs_kernel_progress_le`:
`|Σ_{x,x'} Γ x x' (Re κ_p(x, x') - 1)| ≤ 2 λ worstCost_w(p) |X|`.
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit
open scoped InnerProduct InnerProductSpace

variable {E K X L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {O : L → X → K →L[ℂ] K}

/-- **The Gram kernel of one fresh trial**: `κ_t(x, x') = (1/M) Σ_j ⟪V_x^j ψ, V_{x'}^j ψ⟫`. -/
def trialKernel (t : ODERepeatProtocol.TrialFamily O E) (x x' : X) : ℂ :=
  (t.choices : ℂ)⁻¹ * ∑ j, ⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ

/-- **The Gram kernel of a retry protocol**: the product of the trial kernels of its attempts
(every attempt purified on its own register). -/
def kernel : ODERepeatProtocol.Protocol O E → X → X → ℂ
  | .abort, _, _ => 1
  | .freshTrial t k, x, x' => trialKernel t x x' * kernel k x x'

/-- A trial kernel of unitary circuits has modulus at most one. -/
theorem norm_trialKernel_le (hO : ∀ l x, IsUnitary (O l x))
    (t : ODERepeatProtocol.TrialFamily O E) (x x' : X) : ‖trialKernel t x x'‖ ≤ 1 := by
  have hM : (0 : ℝ) < t.choices := by exact_mod_cast t.choices_pos
  have hterm : ∀ j, ‖⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ‖ ≤ 1 := by
    intro j
    refine (norm_inner_le_norm _ _).trans ?_
    rw [PositiveAdversary.norm_map_of_isUnitary ((t.circuit j).eval_unitary hO x),
      PositiveAdversary.norm_map_of_isUnitary ((t.circuit j).eval_unitary hO x'), t.seed_unit,
      one_mul]
  unfold trialKernel
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (t.choices : ℝ)⁻¹ * ‖∑ j, ⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ‖
      ≤ (t.choices : ℝ)⁻¹ * ∑ _j : Fin t.choices, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j))
          (inv_nonneg.mpr hM.le)
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          inv_mul_cancel₀ hM.ne']

/-- The protocol kernel has modulus at most one. -/
theorem norm_kernel_le (hO : ∀ l x, IsUnitary (O l x)) (p : ODERepeatProtocol.Protocol O E)
    (x x' : X) : ‖kernel p x x'‖ ≤ 1 := by
  induction p with
  | abort => simp [kernel]
  | freshTrial t k ih =>
    rw [kernel, norm_mul]
    exact mul_le_one₀ (norm_trialKernel_le hO t x x') (norm_nonneg _) ih

/-- The protocol kernel is one on the diagonal. -/
theorem kernel_self (hO : ∀ l x, IsUnitary (O l x)) (p : ODERepeatProtocol.Protocol O E)
    (x : X) : kernel p x x = 1 := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
    rw [kernel, ih, mul_one]
    have hM : (t.choices : ℂ) ≠ 0 := by exact_mod_cast t.choices_pos.ne'
    have hterm : ∀ j, ⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x t.seed⟫_ℂ = 1 := by
      intro j
      rw [inner_self_eq_norm_sq_to_K,
        PositiveAdversary.norm_map_of_isUnitary ((t.circuit j).eval_unitary hO x), t.seed_unit]
      simp
    unfold trialKernel
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ hM

section Progress

variable {B I : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [Fintype X] [Fintype I]

/-- **Weighted adversary progress** with a multiplier kernel `Λ`:
`Σ_{x,x'} Γ x x' Re (Λ x x' ⟪ψ_x, ψ_{x'}⟫)`. -/
def progressL (Γ : X → X → ℝ) (Λ : X → X → ℂ) (ψ : X → B) : ℝ :=
  ∑ x, ∑ x', Γ x x' * (Λ x x' * ⟪ψ x, ψ x'⟫_ℂ).re

omit [Fintype X] in
/-- **Complex bit-flip identity** (the complex form of `PositiveAdversary.re_inner_phase_sub`):
two phase oracles change an inner product exactly on the blocks where their strings differ,
`⟪O_a u, O_b v⟫ - ⟪u, v⟫ = -2 Σ_{i : a i ≠ b i} ⟪P_i u, P_i v⟫`. -/
theorem inner_phase_sub (P : ProjFamily B I) (a b : I → Bool) (u v : B) :
    ⟪P.phase a u, P.phase b v⟫_ℂ - ⟪u, v⟫_ℂ =
      ∑ i, (if a i = b i then (0 : ℂ) else -2) * ⟪P.proj i u, P.proj i v⟫_ℂ := by
  rw [PositiveAdversary.inner_eq_rest_add_sum P (P.phase a u),
    PositiveAdversary.inner_eq_rest_add_sum P u v, PositiveAdversary.rest_phase_apply,
    PositiveAdversary.rest_phase_apply]
  simp only [PositiveAdversary.proj_phase_apply, inner_smul_left, inner_smul_right]
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases a i <;> cases b i <;> simp <;> ring

omit [Fintype X] [Fintype I] in
/-- Exchange of a triple finite sum: `Σ_x Σ_x' Σ_i f = Σ_i Σ_x Σ_x' f`. -/
theorem sum_sum_sum_comm {Y J : Type*} [Fintype Y] [Fintype J] (f : Y → Y → J → ℝ) :
    ∑ x, ∑ x', ∑ i, f x x' i = ∑ i, ∑ x, ∑ x', f x x' i := by
  calc ∑ x, ∑ x', ∑ i, f x x' i = ∑ x, ∑ i, ∑ x', f x x' i :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x, ∑ x', f x x' i := Finset.sum_comm

/-- **One query with a multiplier.** With certificates `lam` for every bit and a multiplier
kernel of modulus at most one, a query of the phase oracle changes the weighted progress by at
most `2 lam Σ_x ‖ψ_x‖²` (the step of `PositiveAdversary.abs_progress_query_sub_le`). -/
theorem abs_progressL_query_sub_le (P : ProjFamily B I) (y : X → I → Bool)
    (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam)
    (Λ : X → X → ℂ) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ 1) (ψ : X → B) :
    |progressL Γ Λ (fun x => P.phase (y x) (ψ x)) - progressL Γ Λ ψ| ≤
      2 * lam * ∑ x, ‖ψ x‖ ^ 2 := by
  have hpt : ∀ x x', Γ x x' * (Λ x x' * ⟪P.phase (y x) (ψ x), P.phase (y x') (ψ x')⟫_ℂ).re -
      Γ x x' * (Λ x x' * ⟪ψ x, ψ x'⟫_ℂ).re = ∑ i, -2 * (PositiveAdversary.masked Γ y i x x' *
        (Λ x x' * ⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re) := by
    intro x x'
    rw [← mul_sub, ← Complex.sub_re, ← mul_sub, inner_phase_sub, Finset.mul_sum, Complex.re_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold PositiveAdversary.masked
    split_ifs
    · simp
    · simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.mul_im]
      norm_num
      ring
  have hdiff : progressL Γ Λ (fun x => P.phase (y x) (ψ x)) - progressL Γ Λ ψ =
      ∑ i, -2 * ∑ x, ∑ x', PositiveAdversary.masked Γ y i x x' *
        (Λ x x' * ⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re := by
    simp only [progressL, ← Finset.sum_sub_distrib, hpt, Finset.mul_sum]
    exact sum_sum_sum_comm _
  have hT : ∀ i, |∑ x, ∑ x', PositiveAdversary.masked Γ y i x x' *
      (Λ x x' * ⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re| ≤
        lam * ∑ x, ‖P.proj i (ψ x)‖ ^ 2 := by
    intro i
    have hu := PositiveAdversary.schur_bound Γ hΓ0 hΓs y i (hcert i)
      (fun x => ‖P.proj i (ψ x)‖)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ hu)
    refine Finset.sum_le_sum fun x _ => (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun x' _ => ?_)
    have hm := PositiveAdversary.masked_nonneg Γ hΓ0 y i x x'
    have hc : |(Λ x x' * ⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ).re| ≤
        ‖P.proj i (ψ x)‖ * ‖P.proj i (ψ x')‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul]
      calc ‖Λ x x'‖ * ‖⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ‖
          ≤ 1 * ‖⟪P.proj i (ψ x), P.proj i (ψ x')⟫_ℂ‖ :=
            mul_le_mul_of_nonneg_right (hΛ x x') (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact norm_inner_le_norm _ _
    rw [abs_mul, abs_of_nonneg hm, mul_assoc]
    exact mul_le_mul_of_nonneg_left hc hm
  have hre : ∑ i, lam * ∑ x, ‖P.proj i (ψ x)‖ ^ 2 = lam * ∑ x, ∑ i, ‖P.proj i (ψ x)‖ ^ 2 := by
    rw [← Finset.mul_sum, Finset.sum_comm]
  rw [hdiff]
  refine (PositiveAdversary.abs_sum_neg_two_mul_le hT).trans ?_
  rw [hre, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ =>
    PositiveAdversary.sum_norm_proj_sq_le P (ψ x)) (mul_nonneg two_pos.le hlam)

/-- **Program bound with a multiplier** (`PositiveAdversary.abs_progress_program_sub_le` with a
multiplier kernel of modulus at most one): a Boolean program changes the weighted progress by at
most `2 λ count Σ_x ‖ψ_x‖²`. -/
theorem abs_progressL_program_sub_le (P : ProjFamily B I) (y : X → I → Bool)
    (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam)
    (Λ : X → X → ℂ) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ 1)
    (q : OracleCircuit.Program (fun x => P.phase (y x))) (ψ : X → B) :
    |progressL Γ Λ (fun x => q.eval x (ψ x)) - progressL Γ Λ ψ| ≤
      2 * lam * q.count * ∑ x, ‖ψ x‖ ^ 2 := by
  induction q generalizing ψ with
  | fixed U hU =>
    show |progressL Γ Λ (fun x => U (ψ x)) - progressL Γ Λ ψ| ≤ 2 * lam * ((0 : ℕ) : ℝ) * _
    have h : progressL Γ Λ (fun x => U (ψ x)) = progressL Γ Λ ψ := by
      simp only [progressL, PositiveAdversary.inner_map_map_of_isUnitary hU]
    rw [h, sub_self, abs_zero, Nat.cast_zero, mul_zero, zero_mul]
  | query =>
    show |progressL Γ Λ (fun x => P.phase (y x) (ψ x)) - progressL Γ Λ ψ| ≤
      2 * lam * ((1 : ℕ) : ℝ) * _
    rw [Nat.cast_one, mul_one]
    exact abs_progressL_query_sub_le P y Γ hΓ0 hΓs hlam hcert Λ hΛ ψ
  | queryAdjoint =>
    show |progressL Γ Λ (fun x => star (P.phase (y x)) (ψ x)) - progressL Γ Λ ψ| ≤
      2 * lam * ((1 : ℕ) : ℝ) * _
    simp only [P.star_phase, Nat.cast_one, mul_one]
    exact abs_progressL_query_sub_le P y Γ hΓ0 hΓs hlam hcert Λ hΛ ψ
  | seq p r hp hr =>
    show |progressL Γ Λ (fun x => p.eval x (r.eval x (ψ x))) - progressL Γ Λ ψ| ≤
      2 * lam * ((p.count + r.count : ℕ) : ℝ) * _
    have hnorm : ∀ x, ‖r.eval x (ψ x)‖ = ‖ψ x‖ := fun x =>
      PositiveAdversary.norm_map_of_isUnitary
        (r.eval_unitary (fun x => P.isUnitary_phase (y x)) x) (ψ x)
    have h1 := hp (fun x => r.eval x (ψ x))
    have h2 := hr ψ
    simp only [hnorm] at h1
    have h3 := abs_add_le
      (progressL Γ Λ (fun x => p.eval x (r.eval x (ψ x))) -
        progressL Γ Λ (fun x => r.eval x (ψ x)))
      (progressL Γ Λ (fun x => r.eval x (ψ x)) - progressL Γ Λ ψ)
    rw [sub_add_sub_cancel] at h3
    rw [Nat.cast_add]
    calc _ ≤ _ := h3
      _ ≤ 2 * lam * p.count * ∑ x, ‖ψ x‖ ^ 2 + 2 * lam * r.count * ∑ x, ‖ψ x‖ ^ 2 :=
          add_le_add h1 h2
      _ = _ := by ring

/-- **Progress of a retry protocol.** If every label of `O` is implemented on the isometric
encoding `Enc` by at most `w l` queries of the Boolean phase oracle `x ↦ P.phase (y x)`, the
kernel of a protocol of unitary circuits satisfies
`|Σ_{x,x'} Γ x x' (Re κ_p(x, x') - 1)| ≤ 2 λ worstCost_w(p) |X|`. -/
theorem abs_kernel_progress_le (P : ProjFamily B I) (y : X → I → Bool)
    (Γ : X → X → ℝ) (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x)
    {lam : ℝ} (hlam : 0 ≤ lam) (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam)
    (Enc : K →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l))
    (p : ODERepeatProtocol.Protocol O E) :
    |∑ x, ∑ x', Γ x x' * ((kernel p x x').re - 1)| ≤
      2 * lam * p.worstCost w * Fintype.card X := by
  have hEi : ∀ a b : K, ⟪Enc a, Enc b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro a b
    have hb : (Enc†) (Enc b) = b := by
      simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
        congrArg (fun A : K →L[ℂ] K => A b) hEnc
    rw [← ContinuousLinearMap.adjoint_inner_right, hb]
  induction p with
  | abort =>
    simp only [kernel, Complex.one_re, sub_self, mul_zero, Finset.sum_const_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg two_pos.le hlam) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  | freshTrial t k ih =>
    have hφ : ‖Enc t.seed‖ = 1 := (Reduction.norm_encode Enc hEnc _).trans t.seed_unit
    have hφφ : ⟪t.seed, t.seed⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, t.seed_unit]
      simp
    -- one label: compile the circuit to a Boolean program and apply the program bound
    have hj : ∀ j, |∑ x, ∑ x', Γ x x' * (kernel k x x' *
        (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re| ≤
          2 * lam * t.maxCost w * Fintype.card X := by
      intro j
      obtain ⟨c, hcount, hcomm⟩ := Reduction.exists_boolean_program Enc hEnc
        (fun x => P.isUnitary_phase (y x)) hO w hw (t.circuit j)
      have hev : ∀ x, c.eval x (Enc t.seed) = Enc ((t.circuit j).eval x t.seed) := fun x => by
        simpa only [ContinuousLinearMap.comp_apply] using
          congrArg (fun A : K →L[ℂ] B => A t.seed) (hcomm x)
      have heq : ∑ x, ∑ x', Γ x x' * (kernel k x x' *
          (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re =
          progressL Γ (kernel k) (fun x => c.eval x ((fun _ => Enc t.seed) x)) -
            progressL Γ (kernel k) (fun _ => Enc t.seed) := by
        simp only [progressL, hev, hEi, hφφ, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
        rw [mul_sub, Complex.sub_re, mul_sub, mul_one]
      rw [heq]
      refine (abs_progressL_program_sub_le P y Γ hΓ0 hΓs hlam hcert (kernel k)
        (fun x x' => norm_kernel_le hO k x x') c (fun _ => Enc t.seed)).trans ?_
      simp only [hφ, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hc : (c.count : ℝ) ≤ t.maxCost w := by
        exact_mod_cast hcount.trans (t.cost_le_maxCost w j)
      have h2 : 0 ≤ 2 * lam := mul_nonneg two_pos.le hlam
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc h2) (Nat.cast_nonneg _)
    -- the kernel recursion `κ_{t·k} - 1 = κ_k (κ_t - 1) + (κ_k - 1)`
    have hM : (t.choices : ℂ) ≠ 0 := by exact_mod_cast t.choices_pos.ne'
    have hMr : (0 : ℝ) < t.choices := by exact_mod_cast t.choices_pos
    have hdec : ∀ x x', (kernel (.freshTrial t k) x x').re - 1 =
        (t.choices : ℝ)⁻¹ * ∑ j, (kernel k x x' *
          (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re +
        ((kernel k x x').re - 1) := by
      intro x x'
      have hc : kernel (.freshTrial t k) x x' = ((((t.choices : ℝ)⁻¹ : ℝ) : ℂ) *
          ∑ j, kernel k x x' *
            (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)) +
          kernel k x x' := by
        show trialKernel t x x' * kernel k x x' = _
        unfold trialKernel
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, mul_one, Complex.ofReal_inv, Complex.ofReal_natCast]
        linear_combination (kernel k x x') * inv_mul_cancel₀ hM
      rw [hc, Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum]
      ring
    have hsplit : ∑ x, ∑ x', Γ x x' * ((kernel (.freshTrial t k) x x').re - 1) =
        (t.choices : ℝ)⁻¹ * ∑ j, ∑ x, ∑ x', Γ x x' * (kernel k x x' *
          (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re +
        ∑ x, ∑ x', Γ x x' * ((kernel k x x').re - 1) := by
      simp only [hdec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [sum_sum_sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun x' _ => by ring
    have havg : |(t.choices : ℝ)⁻¹ * ∑ j, ∑ x, ∑ x', Γ x x' * (kernel k x x' *
        (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re| ≤
          2 * lam * t.maxCost w * Fintype.card X := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hMr.le)]
      calc (t.choices : ℝ)⁻¹ * |∑ j, ∑ x, ∑ x', Γ x x' * (kernel k x x' *
            (⟪(t.circuit j).eval x t.seed, (t.circuit j).eval x' t.seed⟫_ℂ - 1)).re|
          ≤ (t.choices : ℝ)⁻¹ * ∑ _j : Fin t.choices, 2 * lam * t.maxCost w * Fintype.card X :=
            mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun j _ => hj j)) (inv_nonneg.mpr hMr.le)
        _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
              inv_mul_cancel₀ hMr.ne', one_mul]
    rw [hsplit]
    refine (abs_add_le _ _).trans ((add_le_add havg ih).trans (le_of_eq ?_))
    show _ = 2 * lam * ((t.maxCost w + k.worstCost w : ℕ) : ℝ) * Fintype.card X
    rw [Nat.cast_add]
    ring

end Progress

end

end ODELowerBoundExtensions.Release
