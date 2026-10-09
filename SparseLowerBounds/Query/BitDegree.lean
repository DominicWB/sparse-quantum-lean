import SparseLowerBounds.Query.SearchWeight

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Fourier degree of Boolean bit-oracle programs

The polynomial argument of Lemma `hsl:lem:precision` (manuscript lines
2355-2365). The hidden input is a string of `n` independent bits
`x : Fin n → Bool`, queried through the phase oracle
`bitOracle P x = 1 - 2 Σ_{k, x k} P k` of a projection family
`P : ProjFamily K (Fin n)` (`Query/PhaseOracle`).

Functions of the bits are expanded in the characters
`χ_S(x) = (-1)^{|{k ∈ S : x k}|}`; `degLE n V d` is the span of
`x ↦ χ_S(x) • v` with `|S| ≤ d` (Fourier degree at most `d`, equivalently
multilinear degree at most `d` after reducing `x_k² = x_k`).

* One query is affine in the characters: `bitOracle P x = R + Σ_k χ_{k}(x) P k`
  with `R = 1 - Σ_k P k`, so a program state after `q` queries
  (inverse queries included) has degree at most `q` (`program_mem_degLE`).
* Sesquilinear products add degrees (`inner_mem_degLE`), so the expectation of
  any input-independent operator has degree at most `2q`.
* The uniform average of the full parity against a function of degree
  `d < n` vanishes (`sum_bitParity_mul_eq_zero`): every character it contains
  omits some bit, whose balanced average vanishes.

Hence a program whose parity correlation is positive makes at least `n/2`
Boolean queries (`le_two_mul_count`, line 2362: `2q ≥ n`). No norm hypothesis
on the seed or the observable is needed.

## Proof route (helper statements)

1. *Characters.* `χ_∅ = 1`, `χ_{k}(x) = ±1` by `x k` (`chi_single`), real
   (`star_chi`), multiplicative `χ_S χ_T = χ_{S ∆ T}` (`chi_mul_chi`), balanced
   when `S ≠ ∅` (`sum_chi_eq_zero`), hence orthogonal
   (`sum_chi_mul_chi_eq_zero`); `|S ∆ T| ≤ |S| + |T|` (`card_symmDiff_le`).
2. *Degree calculus.* Generators (`chi_smul_mem_degLE`, `const_mem_degLE`),
   monotonicity (`degLE_mono`), multiplication by `χ_S` raises the degree by at
   most `|S|` (`mul_chi_mem_degLE`, `mul_chi_single_mem_degLE`), pointwise
   linear maps keep it (`map_mem_degLE`, `clm_apply_mem_degLE`).
3. *Programs.* Inverse queries are queries (`star_bitOracle`); one query raises
   the degree by one (`query_mem_degLE`); the induction is run for an arbitrary
   input-dependent state (`eval_apply_mem_degLE`, needed for `seq`), and
   `program_mem_degLE` is its constant-seed case.
4. *Correlation.* The generator identity `⟪χ_S v, A χ_T v'⟫ = χ_{S∆T} ⟪v, A v'⟫`
   (`inner_chi_smul`) gives `inner_mem_degLE`; `σ = χ_univ` is orthogonal to
   every `χ_S`, `S ≠ univ` (`sum_bitParity_mul_chi`).
-/

namespace SparseLowerBounds.BitDegree

noncomputable section
open SparseHamiltonian OracleCircuit
open scoped InnerProductSpace

variable {n : ℕ}

/-- The character `χ_S(x) = (-1)^{|{k ∈ S : x k}|}`. -/
def chi (S : Finset (Fin n)) (x : Fin n → Bool) : ℂ :=
  (-1) ^ (S.filter fun k => x k = true).card

/-- The parity `σ(X) = (-1)^{x_1 + ⋯ + x_n}` of `n` hidden bits (line 2345). -/
def bitParity (x : Fin n → Bool) : ℝ :=
  (-1) ^ (Finset.univ.filter fun k => x k = true).card

/-- Functions of `n` bits with values in `V` of Fourier degree at most `d`. -/
def degLE (n : ℕ) (V : Type*) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Submodule ℂ ((Fin n → Bool) → V) :=
  Submodule.span ℂ {f | ∃ S : Finset (Fin n), S.card ≤ d ∧ ∃ v : V, f = fun x => chi S x • v}

theorem bitParity_eq_chi (x : Fin n → Bool) : (bitParity x : ℂ) = chi Finset.univ x := by
  simp [bitParity, chi]

theorem abs_bitParity (x : Fin n → Bool) : |bitParity x| = 1 := by
  simp [bitParity]

/-! ### Characters -/

/-- Product form of a character over all coordinates. -/
theorem chi_eq_prod (S : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x = ∏ k, (if k ∈ S ∧ x k = true then (-1 : ℂ) else 1) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, chi]
  congr 2
  ext k
  simp

theorem chi_empty (x : Fin n → Bool) : chi ∅ x = 1 := by
  simp [chi]

/-- `χ_{k}(x) = -1` if bit `k` is set, `1` otherwise. -/
theorem chi_single (k : Fin n) (x : Fin n → Bool) :
    chi {k} x = if x k = true then -1 else 1 := by
  unfold chi
  rw [Finset.filter_singleton]
  split_ifs <;> simp

/-- Characters are real. -/
theorem star_chi (S : Finset (Fin n)) (x : Fin n → Bool) : star (chi S x) = chi S x := by
  simp [chi]

/-- `χ_S χ_T = χ_{S ∆ T}`: `|S ∩ X| + |T ∩ X| = |(S ∆ T) ∩ X| + 2 |S ∩ T ∩ X|`. -/
theorem chi_mul_chi (S T : Finset (Fin n)) (x : Fin n → Bool) :
    chi S x * chi T x = chi (symmDiff S T) x := by
  rw [chi_eq_prod, chi_eq_prod, chi_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hS : k ∈ S <;> by_cases hT : k ∈ T <;> cases hx : x k <;>
    simp [hS, hT, Finset.mem_symmDiff]

theorem chi_mul_self (S : Finset (Fin n)) (x : Fin n → Bool) : chi S x * chi S x = 1 := by
  rw [chi_mul_chi, symmDiff_self, Finset.bot_eq_empty, chi_empty]

theorem card_symmDiff_le (S T : Finset (Fin n)) : (symmDiff S T).card ≤ S.card + T.card := by
  exact (Finset.card_le_card Finset.symmDiff_subset_union).trans (Finset.card_union_le S T)

/-- A nonempty character is balanced: flipping one bit of `S` is an
involution of the cube that negates `χ_S` (lines 2361-2362). -/
theorem sum_chi_eq_zero {S : Finset (Fin n)} (hS : S.Nonempty) : ∑ x, chi S x = 0 := by
  obtain ⟨k, hk⟩ := hS
  simp_rw [chi_eq_prod]
  rw [show (∑ x : Fin n → Bool, ∏ i, (if i ∈ S ∧ x i = true then (-1 : ℂ) else 1))
      = ∏ i, ∑ b : Bool, (if i ∈ S ∧ b = true then (-1 : ℂ) else 1) from
      (Fintype.prod_sum fun i (b : Bool) => if i ∈ S ∧ b = true then (-1 : ℂ) else 1).symm]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])

/-- Orthogonality of distinct characters. -/
theorem sum_chi_mul_chi_eq_zero {S T : Finset (Fin n)} (hST : S ≠ T) :
    ∑ x, chi S x * chi T x = 0 := by
  simp_rw [chi_mul_chi]
  exact sum_chi_eq_zero (Finset.symmDiff_nonempty.mpr hST)

/-- The full parity is orthogonal to every character `χ_S` with `S ≠ univ`. -/
theorem sum_bitParity_mul_chi {S : Finset (Fin n)} (hS : S ≠ Finset.univ) :
    ∑ x, (bitParity x : ℂ) * chi S x = 0 := by
  simp_rw [bitParity_eq_chi]
  exact sum_chi_mul_chi_eq_zero (Ne.symm hS)

/-! ### Degree calculus -/

section Degree

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The generators of `degLE`. -/
theorem chi_smul_mem_degLE {d : ℕ} {S : Finset (Fin n)} (hS : S.card ≤ d) (v : V) :
    (fun x => chi S x • v) ∈ degLE n V d := by
  exact Submodule.subset_span ⟨S, hS, v, rfl⟩

/-- Input-independent functions have degree zero. -/
theorem const_mem_degLE (v : V) : (fun _ : Fin n → Bool => v) ∈ degLE n V 0 := by
  have h := chi_smul_mem_degLE (n := n) (d := 0) (S := ∅) (by simp) v
  simpa [chi_empty] using h

theorem degLE_mono {d d' : ℕ} (h : d ≤ d') : degLE n V d ≤ degLE n V d' := by
  exact Submodule.span_mono fun _ ⟨S, hS, v, hf⟩ => ⟨S, hS.trans h, v, hf⟩

/-- A linear map of functions that sends every generator of degree at most `d`
into `degLE n W d'` maps all of `degLE n V d` there. -/
theorem map_degLE_of_generators {d d' : ℕ}
    (L : ((Fin n → Bool) → V) →ₗ[ℂ] ((Fin n → Bool) → W))
    (hL : ∀ S : Finset (Fin n), S.card ≤ d → ∀ v : V,
      L (fun x => chi S x • v) ∈ degLE n W d')
    {f : (Fin n → Bool) → V} (hf : f ∈ degLE n V d) : L f ∈ degLE n W d' := by
  have h : degLE n V d ≤ (degLE n W d').comap L :=
    Submodule.span_le.mpr (by rintro _ ⟨S, hS, v, rfl⟩; exact hL S hS v)
  exact h hf

/-- Pointwise multiplication by the character `χ_S`, as a linear map. -/
def chiMul (S : Finset (Fin n)) : ((Fin n → Bool) → V) →ₗ[ℂ] ((Fin n → Bool) → V) where
  toFun f x := chi S x • f x
  map_add' f g := by funext x; simp [smul_add]
  map_smul' c f := by funext x; simp only [Pi.smul_apply, RingHom.id_apply]; exact smul_comm _ _ _

/-- Multiplying by `χ_S` raises the degree by at most `|S|`. -/
theorem mul_chi_mem_degLE {d : ℕ} {f : (Fin n → Bool) → V} (hf : f ∈ degLE n V d)
    (S : Finset (Fin n)) : (fun x => chi S x • f x) ∈ degLE n V (d + S.card) := by
  refine map_degLE_of_generators (chiMul S) (fun T hT v => ?_) hf
  have h : (chiMul S) (fun x => chi T x • v) = fun x => chi (symmDiff S T) x • v := by
    funext x
    change chi S x • chi T x • v = _
    rw [smul_smul, chi_mul_chi]
  rw [h]
  exact chi_smul_mem_degLE ((card_symmDiff_le S T).trans (by omega)) v

/-- Multiplying by one bit character `χ_{k}` raises the degree by at most one. -/
theorem mul_chi_single_mem_degLE {d : ℕ} {f : (Fin n → Bool) → V} (hf : f ∈ degLE n V d)
    (k : Fin n) : (fun x => chi {k} x • f x) ∈ degLE n V (d + 1) := by
  have h := mul_chi_mem_degLE hf {k}
  rwa [Finset.card_singleton] at h

/-- Pointwise application of an input-independent linear map keeps the degree. -/
theorem map_mem_degLE (A : V →ₗ[ℂ] W) {d : ℕ} {f : (Fin n → Bool) → V}
    (hf : f ∈ degLE n V d) : (fun x => A (f x)) ∈ degLE n W d := by
  refine map_degLE_of_generators (A.compLeft (Fin n → Bool)) (fun S hS v => ?_) hf
  have h : (A.compLeft (Fin n → Bool)) (fun x => chi S x • v) = fun x => chi S x • A v := by
    funext x
    change A (chi S x • v) = _
    rw [map_smul]
  rw [h]
  exact chi_smul_mem_degLE hS (A v)

end Degree

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- `map_mem_degLE` for a fixed bounded operator (fixed gates, `P.rest`, `P.proj k`). -/
theorem clm_apply_mem_degLE (A : K →L[ℂ] K) {d : ℕ} {f : (Fin n → Bool) → K}
    (hf : f ∈ degLE n K d) : (fun x => A (f x)) ∈ degLE n K d := by
  exact map_mem_degLE A.toLinearMap hf

/-! ### Programs -/

/-- One query is affine in the characters: `bitOracle P x = R + Σ_k χ_{k}(x) P k`. -/
theorem bitOracle_eq (P : ProjFamily K (Fin n)) (x : Fin n → Bool) :
    bitOracle P x = P.rest + ∑ k, chi {k} x • P.proj k := by
  have h : ∀ k, chi {k} x • P.proj k
      = P.proj k - (2 : ℂ) • (if x k = true then P.proj k else 0) := by
    intro k
    rw [chi_single]
    split_ifs
    · rw [neg_one_smul, two_smul]; abel
    · simp
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.sum_filter]
  simp only [bitOracle, ProjFamily.phase, ProjFamily.rest]
  abel

/-- An inverse query is the same query. -/
theorem star_bitOracle (P : ProjFamily K (Fin n)) (x : Fin n → Bool) :
    star (bitOracle P x) = bitOracle P x := by
  exact P.star_phase x

/-- **One query raises the degree by one** (lines 2357-2358): if the state `f` has
degree at most `d`, then `x ↦ bitOracle P x (f x)` has degree at most `d + 1`. -/
theorem query_mem_degLE (P : ProjFamily K (Fin n)) {d : ℕ} {f : (Fin n → Bool) → K}
    (hf : f ∈ degLE n K d) : (fun x => bitOracle P x (f x)) ∈ degLE n K (d + 1) := by
  have hfun : (fun x => bitOracle P x (f x)) =
      (fun x => P.rest (f x)) + ∑ k, fun x => chi {k} x • P.proj k (f x) := by
    funext x
    simp [bitOracle_eq, Finset.sum_apply]
  rw [hfun]
  refine Submodule.add_mem _ (degLE_mono (Nat.le_succ d) (clm_apply_mem_degLE _ hf)) ?_
  exact Submodule.sum_mem _ fun k _ => mul_chi_single_mem_degLE (clm_apply_mem_degLE _ hf) k

/-- The induction behind `program_mem_degLE`, for an arbitrary input-dependent
state (needed for `seq p q`, where `p` acts on the input-dependent output of `q`). -/
theorem eval_apply_mem_degLE (P : ProjFamily K (Fin n)) (q : Program (bitOracle P)) {d : ℕ}
    {f : (Fin n → Bool) → K} (hf : f ∈ degLE n K d) :
    (fun x => q.eval x (f x)) ∈ degLE n K (d + q.count) := by
  induction q generalizing d f with
  | fixed U hU => simpa using clm_apply_mem_degLE U hf
  | query => simpa using query_mem_degLE P hf
  | queryAdjoint => simpa [star_bitOracle] using query_mem_degLE P hf
  | seq p q hp hq =>
      simp only [Program.eval_seq, Program.count_seq]
      exact degLE_mono (by omega) (hp (hq hf))

/-- After a program with `q.count` queries (inverse queries included), the
state has Fourier degree at most `q.count` in the bits (lines 2357-2359). -/
theorem program_mem_degLE (P : ProjFamily K (Fin n)) (q : Program (bitOracle P)) (φ₀ : K) :
    (fun x => q.eval x φ₀) ∈ degLE n K q.count := by
  have h := eval_apply_mem_degLE P q (const_mem_degLE (n := n) φ₀)
  rw [zero_add] at h
  exact h

/-! ### Correlation -/

omit [CompleteSpace K] in
/-- The pairing of two generators is a generator:
`⟪χ_S v, A (χ_T v')⟫ = χ_{S ∆ T} ⟪v, A v'⟫` (characters are real). -/
theorem inner_chi_smul (A : K →L[ℂ] K) (S T : Finset (Fin n)) (v v' : K) (x : Fin n → Bool) :
    ⟪chi S x • v, A (chi T x • v')⟫_ℂ = chi (symmDiff S T) x * ⟪v, A v'⟫_ℂ := by
  rw [map_smul, inner_smul_left, inner_smul_right, starRingEnd_apply, star_chi, ← mul_assoc,
    chi_mul_chi]

/-- For a fixed left function `f`, the pairing `g ↦ (x ↦ ⟪f x, A (g x)⟫)` is linear. -/
def pairRight (A : K →L[ℂ] K) (f : (Fin n → Bool) → K) :
    ((Fin n → Bool) → K) →ₗ[ℂ] ((Fin n → Bool) → ℂ) where
  toFun g x := ⟪f x, A (g x)⟫_ℂ
  map_add' g g' := by funext x; simp [inner_add_right]
  map_smul' c g := by funext x; simp [inner_smul_right]

omit [CompleteSpace K] in
/-- `inner_mem_degLE` when the left factor is a generator. -/
theorem inner_chi_smul_mem_degLE (A : K →L[ℂ] K) {d d' : ℕ} {S : Finset (Fin n)}
    (hS : S.card ≤ d) (v : K) {g : (Fin n → Bool) → K} (hg : g ∈ degLE n K d') :
    (fun x => ⟪chi S x • v, A (g x)⟫_ℂ) ∈ degLE n ℂ (d + d') := by
  refine map_degLE_of_generators (pairRight A fun x => chi S x • v) (fun T hT v' => ?_) hg
  have h : (pairRight A fun x => chi S x • v) (fun x => chi T x • v')
      = fun x => chi (symmDiff S T) x • ⟪v, A v'⟫_ℂ := by
    funext x
    change ⟪chi S x • v, A (chi T x • v')⟫_ℂ = _
    rw [inner_chi_smul, smul_eq_mul]
  rw [h]
  exact chi_smul_mem_degLE ((card_symmDiff_le S T).trans (by omega)) _

omit [CompleteSpace K] in
/-- Degrees add under the sesquilinear pairing with any fixed operator
(lines 2359-2360: expectations have degree at most `2q`). -/
theorem inner_mem_degLE (A : K →L[ℂ] K) {d d' : ℕ} {f g : (Fin n → Bool) → K}
    (hf : f ∈ degLE n K d) (hg : g ∈ degLE n K d') :
    (fun x => ⟪f x, A (g x)⟫_ℂ) ∈ degLE n ℂ (d + d') := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨S, hS, v, rfl⟩ := hf
      exact inner_chi_smul_mem_degLE A hS v hg
  | zero =>
      have h : (fun x => ⟪(0 : (Fin n → Bool) → K) x, A (g x)⟫_ℂ) = 0 := by
        funext x; simp
      rw [h]
      exact Submodule.zero_mem _
  | add f₁ f₂ _ _ h₁ h₂ =>
      have h : (fun x => ⟪(f₁ + f₂) x, A (g x)⟫_ℂ)
          = (fun x => ⟪f₁ x, A (g x)⟫_ℂ) + fun x => ⟪f₂ x, A (g x)⟫_ℂ := by
        funext x; simp [inner_add_left]
      rw [h]
      exact Submodule.add_mem _ h₁ h₂
  | smul c f₁ _ h₁ =>
      have h : (fun x => ⟪(c • f₁) x, A (g x)⟫_ℂ)
          = (starRingEnd ℂ c) • fun x => ⟪f₁ x, A (g x)⟫_ℂ := by
        funext x; simp [inner_smul_left]
      rw [h]
      exact Submodule.smul_mem _ _ h₁

/-- The full parity is uncorrelated with every function of degree `d < n`
(lines 2360-2362). -/
theorem sum_bitParity_mul_eq_zero {d : ℕ} {g : (Fin n → Bool) → ℂ} (hg : g ∈ degLE n ℂ d)
    (hd : d < n) : ∑ x, (bitParity x : ℂ) * g x = 0 := by
  let Φ : ((Fin n → Bool) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∑ x, (bitParity x : ℂ) * g x
      map_add' := fun g g' => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c g => by simp [Finset.mul_sum, mul_left_comm] }
  have h : degLE n ℂ d ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨S, hS, c, rfl⟩
    have hSu : S ≠ Finset.univ := by
      rintro rfl
      simp at hS
      omega
    change ∑ x, (bitParity x : ℂ) * (chi S x • c) = 0
    simp_rw [smul_eq_mul, ← mul_assoc]
    rw [← Finset.sum_mul, sum_bitParity_mul_chi hSu, zero_mul]
  exact h hg

/-- **The precision obstruction** (lines 2356-2364): a Boolean bit program
with `2 q < n` queries has zero parity correlation for every seed and every
input-independent operator. -/
theorem program_correlation_eq_zero (P : ProjFamily K (Fin n)) (q : Program (bitOracle P))
    (φ₀ : K) (M : K →L[ℂ] K) (hq : 2 * q.count < n) :
    ∑ x, (bitParity x : ℂ) * ⟪q.eval x φ₀, M (q.eval x φ₀)⟫_ℂ = 0 := by
  exact sum_bitParity_mul_eq_zero
    (inner_mem_degLE M (program_mem_degLE P q φ₀) (program_mem_degLE P q φ₀)) (by omega)

/-- **`2q ≥ n`** (line 2362): a Boolean bit program whose (unnormalised)
parity correlation is positive makes at least `n/2` queries. -/
theorem le_two_mul_count (P : ProjFamily K (Fin n)) (q : Program (bitOracle P)) (φ₀ : K)
    (M : K →L[ℂ] K)
    (hcorr : 0 < ∑ x, bitParity x * (⟪q.eval x φ₀, M (q.eval x φ₀)⟫_ℂ).re) :
    n ≤ 2 * q.count := by
  by_contra hlt
  have h0 := congrArg Complex.re (program_correlation_eq_zero P q φ₀ M (by omega))
  rw [Complex.re_sum, Complex.zero_re] at h0
  simp_rw [Complex.re_ofReal_mul] at h0
  linarith

/-- Average form of `le_two_mul_count`: positive parity correlation averaged
over the `2ⁿ` uniformly random bit strings forces `2q ≥ n`. -/
theorem le_two_mul_count_avg (P : ProjFamily K (Fin n)) (q : Program (bitOracle P)) (φ₀ : K)
    (M : K →L[ℂ] K)
    (hcorr : 0 < ((2 : ℝ) ^ n)⁻¹ * ∑ x, bitParity x * (⟪q.eval x φ₀, M (q.eval x φ₀)⟫_ℂ).re) :
    n ≤ 2 * q.count := by
  exact le_two_mul_count P q φ₀ M (pos_of_mul_pos_right hcorr (by positivity))

end

end SparseLowerBounds.BitDegree
end
