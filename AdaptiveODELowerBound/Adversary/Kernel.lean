import AdaptiveODELowerBound.Adversary.Weighted
import AdaptiveHamiltonianLowerBound.Readout

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Gram kernel of an adaptive protocol and its adversary progress

Manuscript: Lemma `odel:lem:outer` and the end of the proof of Lemma `hsl:lem:precision`
("Purification and deferred measurement include adaptive and randomised algorithms"), for the
adaptive protocols `SparseLinearSystems.Protocol.Tree`.

**Kernel** (`treeKernel`). Defer the measurement of a test run: the run of `t` on input `x`
prepares `φ_x = C_x ψ`; its success branch is `Π φ_x` (`Π = F F†` the flag projection) followed
by the purification of the success subtree, its failure branch is `(1 - Π) φ_x` followed by that
of the failure subtree. The Gram kernel of these purified states is
`κ_T(x, x') = a κ_s(x, x') + (b - a) κ_f(x, x')` with `a = ⟪F† φ_x, F† φ_{x'}⟫`,
`b = ⟪φ_x, φ_{x'}⟫`; at a final leaf it is the release's retry kernel `Release.kernel p`.
`Adversary/Purify` realises it by explicit unit vectors.

**Progress** (`abs_treeKernel_progressW_le`, by induction on the tree). With the weighted
progress of `Adversary/Weighted`,
`Λ (κ_T - 1) = (Λ a)(κ_s - 1) + (Λ (b - a))(κ_f - 1) + Λ (b - 1)`, where
`‖Λ a‖ ≤ (c_x ‖F† φ_x‖)(c_{x'} ‖F† φ_{x'}‖)` and
`‖Λ (b - a)‖ ≤ (c_x ‖(1 - Π) φ_x‖)(c_{x'} ‖(1 - Π) φ_{x'}‖)`,
`‖F† φ_x‖² + ‖(1 - Π) φ_x‖² = 1`. The three terms cost `2λ` times
`worstCost(s) Σ c² p`, `worstCost(f) Σ c² (1 - p)` and `cost(t) Σ c²`, at most
`2 λ worstCost(T) Σ c²` in total. With `Λ = 1`, `c = 1`:
`|Σ_{x,x'} Γ x x' (Re κ_T(x, x') - 1)| ≤ 2 λ worstCost_w(T) |X|` (`abs_treeKernel_progress_le`).
-/

namespace AdaptiveODELowerBound.Adversary

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit SparseLinearSystems.Protocol
open ODELowerBoundExtensions.Release (kernel)
open scoped InnerProduct InnerProductSpace

variable {E W Fl X L B I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  {O : L → X → W →L[ℂ] W}

/-- **The Gram kernel of an adaptive protocol**: the retry kernel at a final leaf, and at a test
run `κ = ⟪F† φ_x, F† φ_{x'}⟫ κ_s + (⟪φ_x, φ_{x'}⟫ - ⟪F† φ_x, F† φ_{x'}⟫) κ_f`,
`φ_x = C_x ψ`. -/
def treeKernel : Tree O Fl E → X → X → ℂ
  | .final p, x, x' => kernel p x x'
  | .test t s f, x, x' =>
      ⟪(t.flag†) (t.circuit.eval x t.seed), (t.flag†) (t.circuit.eval x' t.seed)⟫_ℂ *
          treeKernel s x x' +
        (⟪t.circuit.eval x t.seed, t.circuit.eval x' t.seed⟫_ℂ -
          ⟪(t.flag†) (t.circuit.eval x t.seed), (t.flag†) (t.circuit.eval x' t.seed)⟫_ℂ) *
          treeKernel f x x'

/-- A multiplier bounded by the weights `c`, times a Gram entry of a state family `u`, is bounded
by the weights `c x ‖u x‖`. -/
theorem norm_mul_inner_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Λ : X → X → ℂ) (c : X → ℝ) (hc : ∀ x, 0 ≤ c x) (hΛ : ∀ x x', ‖Λ x x'‖ ≤ c x * c x')
    (u : X → V) (x x' : X) :
    ‖Λ x x' * ⟪u x, u x'⟫_ℂ‖ ≤ (c x * ‖u x‖) * (c x' * ‖u x'‖) := by
  rw [norm_mul]
  calc ‖Λ x x'‖ * ‖⟪u x, u x'⟫_ℂ‖ ≤ (c x * c x') * (‖u x‖ * ‖u x'‖) :=
        mul_le_mul (hΛ x x') (norm_inner_le_norm _ _) (norm_nonneg _) (mul_nonneg (hc x) (hc x'))
    _ = (c x * ‖u x‖) * (c x' * ‖u x'‖) := by ring

variable [Fintype X] [Fintype I]

/-- **Weighted progress of an adaptive protocol**: if every label of `O` is implemented on the
isometric encoding `Enc` by at most `w l` Boolean phase queries and the multiplier `Λ` is
bounded by the weights `c ≥ 0`, then
`|Σ_{x,x'} Γ x x' Re (Λ x x' (κ_T(x, x') - 1))| ≤ 2 λ worstCost_w(T) Σ_x (c x)²`. -/
theorem abs_treeKernel_progressW_le (P : ProjFamily B I) (y : X → I → Bool) (Γ : X → X → ℝ)
    (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam) (Enc : W →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l))
    (T : Tree O Fl E) (Λ : X → X → ℂ) (c : X → ℝ) (hc : ∀ x, 0 ≤ c x)
    (hΛ : ∀ x x', ‖Λ x x'‖ ≤ c x * c x') :
    |∑ x, ∑ x', Γ x x' * (Λ x x' * (treeKernel T x x' - 1)).re| ≤
      2 * lam * T.worstCost w * ∑ x, c x ^ 2 := by
  have h2 : 0 ≤ 2 * lam := mul_nonneg two_pos.le hlam
  induction T generalizing Λ c with
  | final p => exact abs_kernel_progressW_le P y Γ hΓ0 hΓs hlam hcert Enc hEnc hO w hw Λ c hc hΛ p
  | test t s f ihs ihf =>
    set φ : X → W := fun x => t.circuit.eval x t.seed with hφdef
    have hU : ∀ x, ‖φ x‖ = 1 := fun x => by
      rw [hφdef, PositiveAdversary.norm_map_of_isUnitary (t.circuit.eval_unitary hO x),
        t.seed_unit]
    have hpart : ∀ x, ‖(t.flag†) (φ x)‖ ^ 2 + ‖φ x - t.flag ((t.flag†) (φ x))‖ ^ 2 = 1 :=
      fun x => by
        rw [ODERepeatProtocol.herald_probability_partition t.flag t.flag_isometry (φ x), hU x,
          one_pow]
    -- the failure branch `(1 - Π) φ_x` with `Π = F F†`
    have hFF : ∀ u v : Fl, ⟪t.flag u, t.flag v⟫_ℂ = ⟪u, v⟫_ℂ := fun u v => by
      have hb : (t.flag†) (t.flag u) = u := by
        simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
          congrArg (fun A : Fl →L[ℂ] Fl => A u) t.flag_isometry
      rw [← ContinuousLinearMap.adjoint_inner_left, hb]
    have hL : ∀ u v : W, ⟪t.flag ((t.flag†) u), v⟫_ℂ = ⟪(t.flag†) u, (t.flag†) v⟫_ℂ :=
      fun u v => by rw [← ContinuousLinearMap.adjoint_inner_right]
    have hR : ∀ u v : W, ⟪u, t.flag ((t.flag†) v)⟫_ℂ = ⟪(t.flag†) u, (t.flag†) v⟫_ℂ :=
      fun u v => by rw [← ContinuousLinearMap.adjoint_inner_left]
    have hfail : ∀ x x', ⟪φ x, φ x'⟫_ℂ - ⟪(t.flag†) (φ x), (t.flag†) (φ x')⟫_ℂ =
        ⟪φ x - t.flag ((t.flag†) (φ x)), φ x' - t.flag ((t.flag†) (φ x'))⟫_ℂ := by
      intro x x'
      rw [inner_sub_left, inner_sub_right, inner_sub_right, hFF, hR, hL]
      ring
    -- `Λ (κ_T - 1) = (Λ a)(κ_s - 1) + (Λ (b - a))(κ_f - 1) + Λ (b - 1)`
    have hdec : ∀ x x', Λ x x' * (treeKernel (.test t s f) x x' - 1) =
        (Λ x x' * ⟪(t.flag†) (φ x), (t.flag†) (φ x')⟫_ℂ) * (treeKernel s x x' - 1) +
        (Λ x x' * ⟪φ x - t.flag ((t.flag†) (φ x)), φ x' - t.flag ((t.flag†) (φ x'))⟫_ℂ) *
          (treeKernel f x x' - 1) +
        Λ x x' * (⟪φ x, φ x'⟫_ℂ - 1) := by
      intro x x'
      show Λ x x' * (⟪(t.flag†) (φ x), (t.flag†) (φ x')⟫_ℂ * treeKernel s x x' +
          (⟪φ x, φ x'⟫_ℂ - ⟪(t.flag†) (φ x), (t.flag†) (φ x')⟫_ℂ) * treeKernel f x x' - 1) = _
      linear_combination (Λ x x' * (treeKernel f x x' - 1)) * hfail x x'
    have hsplit : ∑ x, ∑ x', Γ x x' * (Λ x x' * (treeKernel (.test t s f) x x' - 1)).re =
        ∑ x, ∑ x', Γ x x' * ((Λ x x' * ⟪(t.flag†) (φ x), (t.flag†) (φ x')⟫_ℂ) *
          (treeKernel s x x' - 1)).re +
        ∑ x, ∑ x', Γ x x' * ((Λ x x' *
          ⟪φ x - t.flag ((t.flag†) (φ x)), φ x' - t.flag ((t.flag†) (φ x'))⟫_ℂ) *
            (treeKernel f x x' - 1)).re +
        ∑ x, ∑ x', Γ x x' * (Λ x x' * (⟪φ x, φ x'⟫_ℂ - 1)).re := by
      simp only [hdec, Complex.add_re, mul_add, Finset.sum_add_distrib]
    -- the three pieces
    have h1 : |∑ x, ∑ x', Γ x x' * ((Λ x x' * ⟪(t.flag†) (φ x), (t.flag†) (φ x')⟫_ℂ) *
        (treeKernel s x x' - 1)).re| ≤
          2 * lam * s.worstCost w * ∑ x, (c x * ‖(t.flag†) (φ x)‖) ^ 2 :=
      ihs (fun x x' => Λ x x' * ⟪(t.flag†) (φ x), (t.flag†) (φ x')⟫_ℂ)
        (fun x => c x * ‖(t.flag†) (φ x)‖) (fun x => mul_nonneg (hc x) (norm_nonneg _))
        (norm_mul_inner_le Λ c hc hΛ fun x => (t.flag†) (φ x))
    have h3 : |∑ x, ∑ x', Γ x x' * ((Λ x x' *
        ⟪φ x - t.flag ((t.flag†) (φ x)), φ x' - t.flag ((t.flag†) (φ x'))⟫_ℂ) *
          (treeKernel f x x' - 1)).re| ≤
          2 * lam * f.worstCost w * ∑ x, (c x * ‖φ x - t.flag ((t.flag†) (φ x))‖) ^ 2 :=
      ihf (fun x x' => Λ x x' *
          ⟪φ x - t.flag ((t.flag†) (φ x)), φ x' - t.flag ((t.flag†) (φ x'))⟫_ℂ)
        (fun x => c x * ‖φ x - t.flag ((t.flag†) (φ x))‖)
        (fun x => mul_nonneg (hc x) (norm_nonneg _))
        (norm_mul_inner_le Λ c hc hΛ fun x => φ x - t.flag ((t.flag†) (φ x)))
    have h4 : |∑ x, ∑ x', Γ x x' * (Λ x x' * (⟪φ x, φ x'⟫_ℂ - 1)).re| ≤
        2 * lam * t.circuit.cost w * ∑ x, c x ^ 2 :=
      abs_progressW_program_le P y Γ hΓ0 hΓs hlam hcert Enc hEnc hO w hw Λ c hc hΛ t.circuit
        t.seed t.seed_unit
    have hsum : ∑ x, (c x * ‖(t.flag†) (φ x)‖) ^ 2 +
        ∑ x, (c x * ‖φ x - t.flag ((t.flag†) (φ x))‖) ^ 2 = ∑ x, c x ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      calc (c x * ‖(t.flag†) (φ x)‖) ^ 2 + (c x * ‖φ x - t.flag ((t.flag†) (φ x))‖) ^ 2 =
            c x ^ 2 * (‖(t.flag†) (φ x)‖ ^ 2 + ‖φ x - t.flag ((t.flag†) (φ x))‖ ^ 2) := by ring
        _ = c x ^ 2 := by rw [hpart x, mul_one]
    have hA : 0 ≤ ∑ x, (c x * ‖(t.flag†) (φ x)‖) ^ 2 :=
      Finset.sum_nonneg fun x _ => sq_nonneg _
    have hB : 0 ≤ ∑ x, (c x * ‖φ x - t.flag ((t.flag†) (φ x))‖) ^ 2 :=
      Finset.sum_nonneg fun x _ => sq_nonneg _
    have hms : (s.worstCost w : ℝ) ≤ (max (s.worstCost w) (f.worstCost w) : ℕ) := by
      exact_mod_cast le_max_left _ _
    have hmf : (f.worstCost w : ℝ) ≤ (max (s.worstCost w) (f.worstCost w) : ℕ) := by
      exact_mod_cast le_max_right _ _
    rw [hsplit]
    show _ ≤ 2 * lam * ((t.circuit.cost w + max (s.worstCost w) (f.worstCost w) : ℕ) : ℝ) *
      ∑ x, c x ^ 2
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
    calc _ ≤ 2 * lam * s.worstCost w * ∑ x, (c x * ‖(t.flag†) (φ x)‖) ^ 2 +
            2 * lam * f.worstCost w * ∑ x, (c x * ‖φ x - t.flag ((t.flag†) (φ x))‖) ^ 2 +
            2 * lam * t.circuit.cost w * ∑ x, c x ^ 2 := add_le_add (add_le_add h1 h3) h4
      _ ≤ 2 * lam * ((max (s.worstCost w) (f.worstCost w) : ℕ) : ℝ) *
              ∑ x, (c x * ‖(t.flag†) (φ x)‖) ^ 2 +
            2 * lam * ((max (s.worstCost w) (f.worstCost w) : ℕ) : ℝ) *
              ∑ x, (c x * ‖φ x - t.flag ((t.flag†) (φ x))‖) ^ 2 +
            2 * lam * t.circuit.cost w * ∑ x, c x ^ 2 :=
          add_le_add (add_le_add
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hms h2) hA)
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmf h2) hB)) le_rfl
      _ = 2 * lam * ((t.circuit.cost w + max (s.worstCost w) (f.worstCost w) : ℕ) : ℝ) *
            ∑ x, c x ^ 2 := by
          rw [Nat.cast_add, ← hsum]
          ring

/-- **Progress of an adaptive protocol** (`Release.abs_kernel_progress_le` for trees):
`|Σ_{x,x'} Γ x x' (Re κ_T(x, x') - 1)| ≤ 2 λ worstCost_w(T) |X|`. -/
theorem abs_treeKernel_progress_le (P : ProjFamily B I) (y : X → I → Bool) (Γ : X → X → ℝ)
    (hΓ0 : ∀ x x', 0 ≤ Γ x x') (hΓs : ∀ x x', Γ x x' = Γ x' x) {lam : ℝ} (hlam : 0 ≤ lam)
    (hcert : ∀ i, PositiveAdversary.SchurCert Γ y i lam) (Enc : W →L[ℂ] B)
    (hEnc : Enc† ∘L Enc = 1) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (y x)) (O l) Enc (w l))
    (T : Tree O Fl E) :
    |∑ x, ∑ x', Γ x x' * ((treeKernel T x x').re - 1)| ≤
      2 * lam * T.worstCost w * Fintype.card X := by
  have h := abs_treeKernel_progressW_le P y Γ hΓ0 hΓs hlam hcert Enc hEnc hO w hw T
    (fun _ _ => 1) (fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
  simpa only [one_mul, Complex.sub_re, Complex.one_re, one_pow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] using h

end

end AdaptiveODELowerBound.Adversary
