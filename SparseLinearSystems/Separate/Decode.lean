import SparseLinearSystems.Separate.Native
import SparseLinearSystems.Separate.SolverInterface
import SparseODE.ODECompleteSuccess
import GeneralODE.Analysis.Decode

/-!
# Keeping the solver herald: routing, decoding and the selected vector

Corollary `qls:cor:separate`, decoding. The solver workspace sits in the flag-false sector of the
paired workspace (`sector false`). With the solver's fixed output selector `out`:

* `route` keeps the failure component `ψ - out out† ψ` in the flag-false sector and moves the
  selected vector `out† ψ` into the decoding cell `(true, w₀)` (`emb₁`). It is an isometry
  (`norm_route`), and `flip` is a fixed unitary extension of it (`flip_sector`).
* `decoderOp D x = lcu D̃₀` acts on the flag-true cells only (`decoderOp_sector`,
  `decoderOp_emb₁`).
* `selector D w₀` selects the lower data block of the decoding cell, signal `|0⟩`.

The solver herald, the decoder signal, the embedding work registers and the lower dilation sector
form one selection: the selected vector of the whole trial is `T (out† ψ)`, with
`T = π₂ J† (I - D₀)/2` (`selected`). Amplitude from a failed solver branch cannot be accepted.

`decode_contraction` is the error transfer through a contraction; `decode_success` gives, for the
enlarged solution, success at least `q₀/3` and direction error at most `3δ`.
-/

set_option autoImplicit false

namespace SparseLinearSystems.Separate

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048
set_option maxRecDepth 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n
local notation "Vsys" => SparseEdgeMoments.OrientedSpace n

/-! ### Herald routing -/

section Routing

variable (D : NativeSparseBlockEncoding.Data X n Z s) {w : ℕ} (w₀ : Fin w)

/-- A system vector in the decoding cell `(true, w₀)`, signal qubit `|0⟩`. -/
def emb₁ : Vsys →L[ℂ] Paired n Z w := cellIn (true, w₀) ∘L sysEnc D

theorem emb₁_apply (v : Vsys) : emb₁ D w₀ v = cellIn (true, w₀) (sysEnc D v) := rfl

theorem norm_emb₁ (v : Vsys) : ‖emb₁ D w₀ v‖ = ‖v‖ := by
  rw [emb₁_apply, norm_cellIn, norm_sysEnc]

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem norm_sector (u : Space (Pair (Reg n Z)) w) :
    ‖(sector false u : Paired n Z w)‖ = ‖u‖ := by
  simp only [sector, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]

theorem sector_emb₁_disjoint (u : Space (Pair (Reg n Z)) w) (v : Vsys) (p : Bool × Fin w) :
    (sector false u : Paired n Z w) p = 0 ∨ emb₁ D w₀ v p = 0 := by
  rcases p with ⟨f, i⟩
  cases f
  · right
    simp [emb₁_apply]
  · left
    simp

/-- **The herald routing**: the failure component stays in the flag-false sector, the selected
vector `out† ψ` moves into the decoding cell. -/
def route (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) :
    Space (Pair (Reg n Z)) w →L[ℂ] Paired n Z w :=
  sector false ∘L (1 - out ∘L out†) + emb₁ D w₀ ∘L out†

theorem route_apply (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (ψ : Space (Pair (Reg n Z)) w) :
    route D w₀ out ψ = sector false (ψ - out ((out†) ψ)) + emb₁ D w₀ ((out†) ψ) := by
  simp only [route, add_apply, comp_apply, sub_apply, one_apply_eq_self]

theorem norm_route (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (hout : out† ∘L out = 1)
    (ψ : Space (Pair (Reg n Z)) w) : ‖route D w₀ out ψ‖ = ‖ψ‖ := by
  have horth : inner ℂ (sector false (ψ - out ((out†) ψ)) : Paired n Z w)
      (emb₁ D w₀ ((out†) ψ)) = 0 :=
    inner_eq_zero_of_disjoint _ _ (sector_emb₁_disjoint D w₀ _ _)
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hp := ODERepeatProtocol.herald_probability_partition out hout ψ
  rw [norm_sector, norm_emb₁] at h
  rw [route_apply]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith

theorem route_isometry (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (hout : out† ∘L out = 1) :
    (route D w₀ out)† ∘L route D w₀ out = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_route D w₀ out hout)

theorem exists_flip (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (hout : out† ∘L out = 1) :
    ∃ F : Paired n Z w →L[ℂ] Paired n Z w, IsUnitary F ∧
      F ∘L sector false = route D w₀ out :=
  GeneralODE.Registers.exists_unitary_comp _ _ (sector_isometry false)
    (route_isometry D w₀ out hout)

/-- **The flag flip**: a fixed unitary extension of the herald routing. It depends only on the
public output selector. -/
def flip (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (hout : out† ∘L out = 1) :
    Paired n Z w →L[ℂ] Paired n Z w :=
  Classical.choose (exists_flip D w₀ out hout)

theorem flip_unitary (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (hout : out† ∘L out = 1) :
    IsUnitary (flip D w₀ out hout) :=
  (Classical.choose_spec (exists_flip D w₀ out hout)).1

theorem flip_sector (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (hout : out† ∘L out = 1)
    (ψ : Space (Pair (Reg n Z)) w) : flip D w₀ out hout (sector false ψ) = route D w₀ out ψ :=
  congrArg (fun A : Space (Pair (Reg n Z)) w →L[ℂ] Paired n Z w => A ψ)
    (Classical.choose_spec (exists_flip D w₀ out hout)).2

end Routing

/-! ### Decoder and selector -/

section Decoder

variable (D : NativeSparseBlockEncoding.Data X n Z s) {w : ℕ} (w₀ : Fin w)

/-- **The decoder** `lcu D̃₀`, on the flag-true cells. -/
def decoderOp (x : X) : Paired n Z w →L[ℂ] Paired n Z w :=
  MaskedProgram.masked (fun p : Bool × Fin w => p.1) (lcu (Cay D x))

theorem decoderOp_sector (x : X) (u : Space (Pair (Reg n Z)) w) :
    decoderOp D x (sector false u) = sector false u := by
  apply PiLp.ext
  intro p
  rcases p with ⟨f, i⟩
  cases f <;> simp [decoderOp]

theorem decoderOp_emb₁ (x : X) (v : Vsys) :
    decoderOp D x (emb₁ D w₀ v) = cellIn (true, w₀) (lcu (Cay D x) (sysEnc D v)) := by
  apply PiLp.ext
  intro p
  rcases p with ⟨f, i⟩
  cases f
  · simp [decoderOp, emb₁_apply]
  · by_cases hi : i = w₀
    · subst hi
      simp [decoderOp, emb₁_apply]
    · simp [decoderOp, emb₁_apply, hi]

/-- The lower data block `u ↦ (0, u)` as a continuous linear map. -/
def liftL : V0 →L[ℂ] HilbertRegularization.Double V0 :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ V0 V0).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ V0 V0

omit [DecidableEq n] [Fintype n] in
theorem liftL_apply (u : V0) : liftL u = lift u := rfl

omit [DecidableEq n] in
theorem liftL_adjoint : (liftL (n := n))† = WithLp.sndL 2 ℂ V0 V0 := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro p u
  rw [liftL_apply, lift, WithLp.prod_inner_apply]
  simp

/-- **The final selector**: the lower data block of the decoding cell, signal `|0⟩`. -/
def selector : V0 →L[ℂ] Paired n Z w := emb₁ D w₀ ∘L bdry D ∘L liftL

theorem norm_selector (u : V0) : ‖selector D w₀ u‖ = ‖u‖ := by
  rw [selector, comp_apply, comp_apply, norm_emb₁, norm_bdry, liftL_apply, norm_lift]

theorem selector_isometry : (selector D w₀)† ∘L selector D w₀ = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_selector D w₀)

theorem selector_adjoint_apply (y : Paired n Z w) :
    ((selector D w₀)†) y =
      WithLp.sndL 2 ℂ V0 V0 (((bdry D)†) (((sysEnc D)†) (y (true, w₀)))) := by
  rw [selector, emb₁, adjoint_comp, adjoint_comp, adjoint_comp, liftL_adjoint, cellIn_adjoint]
  rfl

/-- The decoded block of `lcu D̃₀` on the clean encoding is `C = (I - D₀)/2`. -/
theorem sysEnc_lcu (x : X) (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1)
    (a : Vsys) : ((sysEnc D)†) (lcu (Cay D x) (sysEnc D a)) = decoder (hyp D x hA1) a := by
  rw [sysEnc_adjoint_apply, sysEnc, comp_apply, lcu_cellIn_false, cay_clean, map_smul, map_sub,
    cl_adjoint_cl, cl_adjoint_cl, decoder_apply]

/-- **The selected vector of a trial** is `T (out† ψ)`, `T = π₂ J† (I - D₀)/2`: failure amplitude
of the solver is never selected. -/
theorem selected (x : X) (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1)
    (out : Vsys →L[ℂ] Space (Pair (Reg n Z)) w) (ψ : Space (Pair (Reg n Z)) w) :
    ((selector D w₀)†) (decoderOp D x (route D w₀ out ψ)) =
      decodeMap D x hA1 ((out†) ψ) := by
  rw [route_apply, map_add, decoderOp_sector, decoderOp_emb₁, map_add, selector_adjoint_apply,
    selector_adjoint_apply, cellIn_apply, if_pos rfl, sysEnc_lcu D x hA1]
  simp [decodeMap]

end Decoder

/-! ### Error transfer and success -/

section Analysis

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- Directions under a unit phase. -/
theorem unitDirection_unit_smul (ω : ℂ) (hω : ‖ω‖ = 1) (v : E) :
    ODEStateNormalization.unitDirection (ω • v) = ω • ODEStateNormalization.unitDirection v := by
  have hω0 : ω ≠ 0 := by
    intro h
    rw [h, norm_zero] at hω
    exact zero_ne_one hω
  rw [GeneralODE.Decode.unitDirection_smul ω hω0, hω, Complex.ofReal_one, div_one]

/-- **Decoding through a contraction.** If `θ ‖y‖ ≤ ‖T y‖` and `ω â` is within `δ < θ` of the
direction of `y`, then `‖T a‖ ≥ (θ - δ) ‖a‖` and the direction of `T a` is within `2δ/θ` of that
of `T y`, with the same phase. -/
theorem decode_contraction (T : E →L[ℂ] F) (hT : ∀ v, ‖T v‖ ≤ ‖v‖) (y a : E) (hy : y ≠ 0)
    (ha : a ≠ 0) (θ δ : ℝ) (hθy : θ * ‖y‖ ≤ ‖T y‖) (hδθ : δ < θ) (ω : ℂ) (hω : ‖ω‖ = 1)
    (hclose : ‖ω • ODEStateNormalization.unitDirection a -
      ODEStateNormalization.unitDirection y‖ ≤ δ) :
    (θ - δ) * ‖a‖ ≤ ‖T a‖ ∧
      ‖ω • ODEStateNormalization.unitDirection (T a) -
        ODEStateNormalization.unitDirection (T y)‖ ≤ 2 * δ / θ := by
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hclose
  have hθ : 0 < θ := lt_of_le_of_lt hδ0 hδθ
  set u := ODEStateNormalization.unitDirection y with hu
  set b := ODEStateNormalization.unitDirection a with hb
  have hTu : T u = ((‖y‖⁻¹ : ℝ) : ℂ) • T y := by
    rw [hu, ODEStateNormalization.unitDirection, ← Complex.coe_smul, map_smul]
  have hTa : T a = ((‖a‖ : ℝ) : ℂ) • T b := by
    rw [hb, ODEStateNormalization.unitDirection, ← Complex.coe_smul, map_smul, smul_smul]
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ han.ne', Complex.ofReal_one, one_smul]
  have hTun : θ ≤ ‖T u‖ := by
    rw [hTu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyn)]
    rw [le_inv_mul_iff₀ hyn]
    linarith
  have hdiff : ‖ω • T b - T u‖ ≤ δ := by
    rw [← map_smul, ← map_sub]
    exact (hT _).trans hclose
  have hTb : θ - δ ≤ ‖T b‖ := by
    have h1 : ‖T u‖ - ‖ω • T b‖ ≤ ‖ω • T b - T u‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le _ _
    rw [norm_smul, hω, one_mul] at h1
    linarith
  have hTbpos : 0 < ‖T b‖ := lt_of_lt_of_le (by linarith) hTb
  refine ⟨?_, ?_⟩
  · rw [hTa, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos han]
    nlinarith
  · have hTu0 : T u ≠ 0 := by
      intro h
      rw [h, norm_zero] at hTun
      linarith
    have hωTb0 : ω • T b ≠ 0 := by
      intro h
      rw [h, zero_sub, norm_neg] at hdiff
      linarith
    have hdir1 : ODEStateNormalization.unitDirection (T a) =
        ODEStateNormalization.unitDirection (T b) := by
      rw [hTa, Complex.coe_smul, GeneralODE.Decode.unitDirection_real_smul _ han]
    have hdir2 : ODEStateNormalization.unitDirection (T y) =
        ODEStateNormalization.unitDirection (T u) := by
      rw [hTu, Complex.coe_smul, GeneralODE.Decode.unitDirection_real_smul _ (inv_pos.mpr hyn)]
    rw [hdir1, hdir2, ← unitDirection_unit_smul ω hω]
    have he := ODEStateNormalization.unitDirection_error_le (T u) (ω • T b) hTu0 hωTb0
    have hTupos : 0 < ‖T u‖ := norm_pos_iff.mpr hTu0
    calc _ ≤ 2 * ‖ω • T b - T u‖ / ‖T u‖ := he
      _ ≤ 2 * δ / θ := by
        rw [div_le_div_iff₀ hTupos hθ]
        nlinarith [norm_nonneg (ω • T b - T u)]

end Analysis

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **Decoding the enlarged solution.** If the solver's selected vector `a` has `‖a‖² ≥ q₀` and
its direction is within `δ ≤ 1/80` of that of `y = -2i√s R₀ J (0, z)`, `z ≠ 0`, then the
decoded vector `T a` has `‖T a‖² ≥ q₀/3` and its direction is within `3δ` of that of `z`,
up to a phase. -/
theorem decode_success (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1) (z : V0) (hz : z ≠ 0) (a : Vsys)
    (q₀ δ : ℝ) (hq0 : 0 < q₀) (hq : q₀ ≤ ‖a‖ ^ 2) (hδ : δ ≤ 1 / 80) (ω : ℂ) (hω : ‖ω‖ = 1)
    (hclose : ‖ω • ODEStateNormalization.unitDirection a -
      ODEStateNormalization.unitDirection (solution D x z)‖ ≤ δ) :
    q₀ / 3 ≤ ‖decodeMap D x hA1 a‖ ^ 2 ∧
      ∃ ω' : ℂ, ‖ω'‖ = 1 ∧ ‖ω' • ODEStateNormalization.unitDirection (decodeMap D x hA1 a) -
        ODEStateNormalization.unitDirection z‖ ≤ 3 * δ := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hyl := solution_norm_lower D x hA1 z
  have hyu := solution_norm_upper D x hA1 z
  have hy : solution D x z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hyl
    nlinarith [mul_pos hsq hzn]
  have ha : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at hq
    nlinarith
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hclose
  have hTy := decode_solution D x hA1 z
  have hTyn : ‖decodeMap D x hA1 (solution D x z)‖ = Real.sqrt (s : ℝ) * ‖z‖ := by
    rw [hTy, norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hsq]
  have h22 : Real.sqrt 2 * (2 / 3) ≤ 1 := by
    have : Real.sqrt 2 ≤ 3 / 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    linarith
  have hθy : 2 / 3 * ‖solution D x z‖ ≤ ‖decodeMap D x hA1 (solution D x z)‖ := by
    rw [hTyn]
    nlinarith [mul_pos hsq hzn]
  obtain ⟨hnorm, hdir⟩ := decode_contraction (decodeMap D x hA1) (decode_norm_le D x hA1)
    (solution D x z) a hy ha (2 / 3) δ hθy (by linarith) ω hω hclose
  refine ⟨?_, ?_⟩
  · have hc : 0 ≤ 2 / 3 - δ := by linarith
    have h1 : (2 / 3 - δ) ^ 2 * ‖a‖ ^ 2 ≤ ‖decodeMap D x hA1 a‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg hc (norm_nonneg _)) hnorm 2
    have h2 : 1 / 3 ≤ (2 / 3 - δ) ^ 2 := by nlinarith
    nlinarith
  · have hc0 : (-Complex.I * (Real.sqrt (s : ℝ) : ℂ)) ≠ 0 := by
      have : ((Real.sqrt (s : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
      exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) this
    have hud : ODEStateNormalization.unitDirection (decodeMap D x hA1 (solution D x z)) =
        (-Complex.I) • ODEStateNormalization.unitDirection z := by
      rw [hTy, GeneralODE.Decode.unitDirection_smul _ hc0]
      congr 1
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hsq]
      have : ((Real.sqrt (s : ℝ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
      field_simp
    rw [hud] at hdir
    refine ⟨Complex.I * ω, by rw [norm_mul, Complex.norm_I, hω, one_mul], ?_⟩
    have he : (Complex.I * ω) • ODEStateNormalization.unitDirection (decodeMap D x hA1 a) -
        ODEStateNormalization.unitDirection z =
        Complex.I • (ω • ODEStateNormalization.unitDirection (decodeMap D x hA1 a) -
          (-Complex.I) • ODEStateNormalization.unitDirection z) := by
      rw [smul_sub, smul_smul, smul_smul]
      congr 1
      rw [show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg], one_smul]
    rw [he, norm_smul, Complex.norm_I, one_mul]
    calc _ ≤ 2 * δ / (2 / 3) := hdir
      _ = 3 * δ := by ring

end

end SparseLinearSystems.Separate
