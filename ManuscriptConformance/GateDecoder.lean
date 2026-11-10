import ManuscriptConformance.GateDecoderDefs
import ManuscriptConformance.GateGeneral
import GeneralDecoder.Budget
import GeneralDecoder.PadArith

/-!
# Conformance: Theorem `hs:thm:gates` for general decoders

Theorem `hs:thm:gates` asks, in its binary conclusion
(eq. `hs:eq:gate-binary`), that "the entries use an efficiently decoded binary
encoding" and that "decoding and reversible arithmetic have polynomial gate and workspace costs in
`b_data`, `log(N+1)` and `log(1/ξ)`". This file states it for every public decoder `val` of the
stored words, with that computational assumption (`comp_rotArith`: a reversible arithmetic on the
value word writing the local rotation parameters `2 arctan |κ val w|` and `arg (val w)` of the
native construction within `ζ`, for every rescaling `κ ∈ [1/η, √(2s)/η]`, the range of the
rescalings of the construction, with gates and work polynomial in `b_data`, the index width and
`log(1/ζ)`), for sparse access of general size:

* `hs_gates_dataDec`: binary sizes (`BinarySizes`) and the decoder of the data, which may depend
  on the edge, with the arithmetic assumption on the base wires (`comp_decArith`);
* `comp_decArith_padDataE`: the arithmetic assumption of the padded data with a validity decoder,
  from `comp_rotArith` (`GeneralDecoder.RotWordArith.flagLift`: the validity of the index pair
  computed on the index wires, the arithmetic run on the value word and its words copied under the
  validity);
* `hs_thm_gates_decoder`: general sizes and general decoders.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateBinary SparseHamiltonian.GateBitBudget
  SparseHamiltonian.GeneralSparseAccess SparseHamiltonian.GeneralDecoder
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR)
open CayleyClockInterface
open scoped InnerProduct

/-! ### The binary sizes and the arithmetic assumptions -/

/-- **The binary sizes** of the package's gate endpoints: `k`-bit indices (`en`), `s = 2^{s_b}`
slots enumerated by the low index words. -/
structure BinarySizes {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
    (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) :
    Prop where
  hsb : sb ≤ k
  hs : s = 2 ^ sb
  range : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)

/-- **The rotation arithmetic of the decoder of the data on the base wires** (computational
assumption): for every rescaling `κ > 0` in `[K₀, K]` and accuracy `ζ ∈ (0, 1]`, a reversible arithmetic
on the base wires of the binary private operation (`GateNative.ArithOK`: the angle words of
`2 arctan |κ decode(e, w)|` and `arg decode(e, w)` within `ζ`, work restored, independently of the
orientation) with gates and work wires at most `c_A (b_data + k + log₂(1/ζ) + 1)^{d_A}`. -/
def comp_decArith {X n : Type*} [Fintype n] [DecidableEq n] {s : ℕ} (cA : ℝ) (dA : ℕ)
    (bd k b : ℕ) (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    (K₀ K : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → K₀ ≤ κ → κ ≤ K → ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → ∃ ar : Arith (BW k b),
    ArithOK ar (Sum.inl (Sum.inr (oPR k)))
      (fun y => (κ : ℂ) * D.decode (phiE en (eword y)) (vword y)) ζ ∧
    ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) ≤
      cA * ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA

/-- **The rotation arithmetic of a decoder** (computational assumption of `hs:thm:gates` before eq.
`hs:eq:gate-binary`, for the native construction): for every rescaling `κ > 0` in `[K₀, K]` and
accuracy `ζ ∈ (0, 1]`, a reversible arithmetic on the value word (`GeneralDecoder.RotWordArith`:
the angle words of `2 arctan |κ val w|` and, for `val w ≠ 0`, of `arg (val w)` within `ζ`, work
restored) with gates and work wires at most `c_A (b_data + k + log₂(1/ζ) + 1)^{d_A}`. The theorems
ask it at the rescalings `κ ∈ [1/η, √(2s)/η]` of their constructions. -/
def comp_rotArith (cA : ℝ) (dA : ℕ) (bd k b : ℕ) (val : Cfg (VW b) → ℂ) (K₀ K : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → K₀ ≤ κ → κ ≤ K → ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
    ∃ (bT bP A : ℕ) (ar : RotWordArith b (fun z => (κ : ℂ) * val z) ζ bT bP A),
      ((ar.circ.length + bT + bP + A : ℕ) : ℝ) ≤
        cA * ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA

universe u v w

set_option maxHeartbeats 8000000 in
/-- **Theorem `hs:thm:gates`, eq. `hs:eq:gate-binary`, for the decoder of the data** (binary sizes).
For a finite gate set admitting single-qubit synthesis of length at most `c₁ log(1/ζ) + c₀` and an
exact decomposition of its controlled one-qubit gates, and the arithmetic assumption with
constants `c_A`, `d_A`, there are constants `C` and `K` such that: for sparse data with binary
sizes (`BinarySizes`) and any public decoder of the stored words (which may depend on the edge),
stored words of `2b` bits with `b ≤ b_data` and the rotation arithmetic of the decoder at the
rescalings `κ ∈ [1/η, √s/η]` (`comp_decArith`), every time `t` and `0 < ε ≤ 1/2`, one circuit over the
gate set and the primitive sparse oracles, fixed before the instance, uses at most
`552960 Q_base` primitive sparse queries, at most `C Q_base (𝔟 + 1)^K` gates with
`Q_base = √s η|t| + √(s η|t| log(1/ε)) + log(1/ε)` and
`𝔟 = b_data + log₂(N+1) + log₂((Q_base+1)/ε)`, and
on every instance whose matrix is Hermitian with row and column Euclidean norms at most `η` has
full-output error at most `ε` on the clean embedding, with an untouched reference. -/
theorem hs_gates_dataDec (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {n : Type v} [Fintype n] [DecidableEq n] {s k b : ℕ}
        (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
        (sb bd : ℕ) (η t ε : ℝ),
        BinarySizes D en sb → b ≤ bd → comp_decArith cA dA bd k b D en (1 / η) (Real.sqrt s / η) →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 552960 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd (Fintype.card n) (mainBound s (η * |t|) ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (prims (R := R) D en x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  set KG := max 3 dA with hKG
  set cP : ℝ := 93 + 4 * (cA * 24 ^ dA) with hcP
  have hcP0 : 0 ≤ cA * 24 ^ dA := by positivity
  set cN : ℝ := 200 * 9218 * cP with hcN
  set Cg : ℝ := cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') with hCg
  have hcN1 : 1 ≤ cN := by rw [hcN, hcP]; nlinarith
  have hCg0 : 0 ≤ Cg := by
    have : 0 ≤ Real.log (4 * cN) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := Cg + 1 with hC
  refine ⟨C, KG + 1, by rw [hC]; linarith, ?_⟩
  intro X n _ _ s k b D en sb bd η t ε hF hbd hdec hη hε hε2
  have hs1 : 1 ≤ s := by rw [hF.hs]; exact Nat.one_le_two_pow
  set τ : ℝ := η * |t| with hτdef
  have hτ : 0 ≤ τ := by positivity
  set q := mainBound s τ ε with hqdef
  have hq2 : 1 / 2 ≤ q := shape_ge_half s hτ hε hε2
  have hq0 : 0 < q := by linarith
  set εn : ℝ := ε / 2 with hεn
  have hεn0 : 0 < εn := by positivity
  have hεn2 : εn ≤ 1 / 2 := by linarith
  have hε1 : ε ≤ 1 := by linarith
  set qn := ImprovedPrecisionBudget.shape s τ (Real.log (1 / εn)) with hqndef
  have hqnq : qn ≤ 2 * q := shape_half_le s hτ hε hε2
  have hqn2 : 1 / 2 ≤ qn := shape_ge_half s hτ hεn0 hεn2
  have hqn0 : 0 < qn := by linarith
  -- the budget word
  set B := bitH bd (Fintype.card n) q ε + 1 with hBdef
  have hcard : Fintype.card n = 2 ^ k := card_eq_two_pow en
  have hY1 : 1 ≤ (q + 1) / ε := one_le_div_of_le hq0.le hε hε1
  have hlogN : (k : ℝ) ≤ Real.logb 2 ((Fintype.card n : ℝ) + 1) := by
    rw [hcard]; exact nat_le_logb k
  have hlogY : 0 ≤ Real.logb 2 ((q + 1) / ε) := logb_nonneg_of_one_le hY1
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBk : (k : ℝ) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBd : (bd : ℝ) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBY : Real.logb 2 ((q + 1) / ε) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hσk : (sb : ℝ) ≤ k := by exact_mod_cast hF.hsb
  have hB3 : B ≤ B ^ 3 := le_self_pow₀ hB1 (by norm_num)
  -- the word `log₂((q_n+1)/ε_n) ≤ 2 + B`
  have hYn : Real.logb 2 ((qn + 1) / εn) ≤ 2 + B := by
    have h1 : (qn + 1) / εn ≤ 2 ^ 2 * ((q + 1) / ε) ^ 1 := by
      rw [pow_one, hεn, div_le_iff₀ (by positivity)]
      have : 2 ^ 2 * ((q + 1) / ε) * (ε / 2) = 2 * (q + 1) := by field_simp
      rw [this]; linarith
    have h2 := logb_le_mul_pow _ (2 ^ 2) ((q + 1) / ε) 2 1 (by positivity) hY1 le_rfl h1
    push_cast at h2
    linarith
  -- the rescaling and the released budget
  obtain ⟨γ, hγ, hγ1, hγs, hdeg, hτq, hm, hr, hall⟩ :=
    binary_simulation_budgetD.{u, v, w} s hs1 τ εn hτ hεn0 hεn2
  set ζ : ℝ := εn / (221184 * qn) with hζdef
  have hζ0 : 0 < ζ := by positivity
  have hζ1 : ζ ≤ 1 := by
    rw [hζdef, div_le_one (by positivity)]; linarith
  have hζε : 221184 * qn * ζ ≤ εn := by
    have : 221184 * qn * ζ = εn := by rw [hζdef]; field_simp
    exact this.le
  have hζε' : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) : ℝ) * ζ ≤
      εn := by
    have h1 : 48 * (fDeg (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) : ℝ) * ζ ≤
        48 * (4608 * qn) * ζ := by
      apply mul_le_mul_of_nonneg_right _ hζ0.le
      linarith
    linarith
  set D' := NativeSparseRescaling.normalize D η hη with hD'
  -- the arithmetic at the rescaling `γ √s / η` and the accuracy `ζ`
  have hsq0 : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hs1)
  have hκ0 : 0 < γ * Real.sqrt s / η := by positivity
  have hκK : γ * Real.sqrt s / η ≤ Real.sqrt s / η := by
    apply div_le_div_of_nonneg_right _ hη.le
    nlinarith
  have hκm : 1 / η ≤ γ * Real.sqrt s / η := div_le_div_of_nonneg_right hγs hη.le
  obtain ⟨ar, har, hcost⟩ := hdec (γ * Real.sqrt s / η) hκ0 hκm hκK ζ hζ0 hζ1
  have hdecEq : (fun y : Cfg (BW k b) =>
      ((γ * Real.sqrt s : ℝ) : ℂ) * D'.decode (phiE en (eword y)) (vword y)) =
      fun y => ((γ * Real.sqrt s / η : ℝ) : ℂ) * D.decode (phiE en (eword y)) (vword y) := by
    funext y
    change ((γ * Real.sqrt s : ℝ) : ℂ) * (((η⁻¹ : ℝ) : ℂ) * D.decode _ _) = _
    push_cast
    ring
  have har' : ArithOK ar (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((γ * Real.sqrt s : ℝ) : ℂ) * D'.decode (phiE en (eword y)) (vword y)) ζ := by
    rw [hdecEq]
    exact har
  set Cn := binarySimD D' en sb hF.hsb γ τ εn ar with hCn
  -- the per-call cost
  have hlogζ : Real.logb 2 (1 / ζ) ≤ 20 + B := by
    have h1 : 1 / ζ ≤ 2 ^ 20 * ((q + 1) / ε) ^ 1 := by
      rw [pow_one, hζdef, one_div_div, div_le_iff₀ hεn0]
      have e : 2 ^ 20 * ((q + 1) / ε) * εn = 2 ^ 19 * (q + 1) := by
        rw [hεn]; field_simp
      rw [e]
      nlinarith
    have h2 := logb_le_mul_pow _ (2 ^ 20) ((q + 1) / ε) 20 1 (by positivity) hY1 le_rfl h1
    push_cast at h2
    linarith
  have hword : (bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1 ≤ 24 * B := by linarith
  have hword0 : 0 ≤ (bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1 := by
    have : 0 ≤ Real.logb 2 (1 / ζ) :=
      logb_nonneg_of_one_le (by rw [le_div_iff₀ hζ0]; linarith)
    linarith
  have hBK : 1 ≤ B ^ KG := one_le_pow₀ hB1
  have hBKG : B ≤ B ^ KG := le_self_pow₀ hB1 (by omega)
  have hB3K : B ^ 3 ≤ B ^ KG := pow_le_pow_right₀ hB1 (le_max_left 3 dA)
  have hBdK : B ^ dA ≤ B ^ KG := pow_le_pow_right₀ hB1 (le_max_right 3 dA)
  have hcostB : ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) ≤ cA * 24 ^ dA * B ^ KG := by
    have h1 : ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA ≤ (24 * B) ^ dA :=
      pow_le_pow_left₀ hword0 hword dA
    rw [mul_pow] at h1
    have h2 : cA * ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA ≤ cA * (24 ^ dA * B ^ dA) :=
      mul_le_mul_of_nonneg_left h1 hcA
    have h3 : cA * (24 ^ dA * B ^ dA) ≤ cA * 24 ^ dA * B ^ KG := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hBdK hcP0
    linarith
  have hpriv : (privGates (sparseOpD D' en (γ * Real.sqrt s)) ar : ℝ) ≤
      (57 + 4 * (cA * 24 ^ dA)) * B ^ KG := by
    have e : privGates (sparseOpD D' en (γ * Real.sqrt s)) ar =
        2 * (28 * k) + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) := by
      rw [privGates, sparseOpD_V, computeV_nGates]
    rw [e]
    push_cast
    have hc : ((ar.circ.length + ar.bT + ar.bP + ar.A : ℕ) : ℝ) =
        (ar.circ.length : ℝ) + ar.bT + ar.bP + ar.A := by push_cast; ring
    rw [hc] at hcostB
    have hA0 : (0 : ℝ) ≤ ar.A := Nat.cast_nonneg _
    have hT0 : (0 : ℝ) ≤ ar.bT := Nat.cast_nonneg _
    have hP0 : (0 : ℝ) ≤ ar.bP := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ ar.circ.length := Nat.cast_nonneg _
    have hk56 : 56 * (k : ℝ) + 1 ≤ 57 * B ^ KG := by nlinarith
    nlinarith
  -- the simulator words
  have hs1' : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hsk : (s : ℝ) ≤ 2 ^ k := by
    rw [hF.hs]; exact_mod_cast Nat.pow_le_pow_right (by norm_num) hF.hsb
  have htime0 : 0 ≤ time (s : ℝ) τ γ := by unfold CayleyClockInterface.time; positivity
  have hmW := simM_word _ k hs1' hsk htime0 hτq hqn0.le hεn0 (by linarith) hm
  have hrW := simR_word _ hqn0.le hεn0 (by linarith) hr
  have hinner : (privGates (sparseOpD D' en (γ * Real.sqrt s)) ar : ℝ) + (sb + 1) + (k + 1) +
      simM (time (s : ℝ) τ γ) (εn / 2) +
      simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) + 1 ≤
      cP * B ^ KG := by
    rw [hcP]
    nlinarith
  have hinner0 : 0 ≤ (privGates (sparseOpD D' en (γ * Real.sqrt s)) ar : ℝ) + (sb + 1) + (k + 1) +
      simM (time (s : ℝ) τ γ) (εn / 2) +
      simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) + 1 := by positivity
  set Nb : ℝ := 200 * (4608 * qn + 1) * ((privGates (sparseOpD D' en (γ * Real.sqrt s)) ar : ℝ) + (sb + 1) + (k + 1) +
      simM (time (s : ℝ) τ γ) (εn / 2) +
      simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (εn / 2) + 1) with hNb
  have hNb0 : 0 ≤ Nb := by positivity
  have hNbq : Nb ≤ q * cN * B ^ KG := by
    have h1 : 200 * (4608 * qn + 1) ≤ 200 * 9218 * q := by linarith
    have hcP0' : 0 ≤ cP := by rw [hcP]; positivity
    have h2 : Nb ≤ (200 * 9218 * q) * (cP * B ^ KG) :=
      mul_le_mul h1 hinner hinner0 (by positivity)
    have e : (200 * 9218 * q) * (cP * B ^ KG) = q * cN * B ^ KG := by
      rw [hcN]; ring
    exact h2.trans e.le
  -- the final gate bound
  have hfin : ∀ N : ℕ, (N : ℝ) ≤ Nb →
      ((N * L' (ε / 2 / (N + 1)) : ℕ) : ℝ) ≤ C * q * B ^ (KG + 1) := by
    intro N hN
    have h1 := gates_log_le hc₀' hc₁' hL' (ε' := ε / 2) (by positivity) (by linarith) N Nb hN
    have hcN2 : 2 ≤ cN := by rw [hcN, hcP]; nlinarith
    have hqcN : 1 ≤ q * cN := by nlinarith
    have h2 := synth_factor' (K := KG) hNb0 hq0 hqcN hcN1 hB1 hε hε1 hBY hc₀' hc₁' hNbq
    have h3 : q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) ≤
        C * q * B ^ (KG + 1) := by
      have e : q * cN * (c₁' * (Real.log (4 * cN) + KG + 2) + c₀') * B ^ (KG + 1) =
          Cg * (q * B ^ (KG + 1)) := by rw [hCg]; ring
      rw [e]
      have : 0 ≤ q * B ^ (KG + 1) := by positivity
      have hle : Cg ≤ C := by rw [hC]; linarith
      calc Cg * (q * B ^ (KG + 1)) ≤ C * (q * B ^ (KG + 1)) := mul_le_mul_of_nonneg_right hle this
        _ = C * q * B ^ (KG + 1) := by ring
    exact h1.trans (h2.trans h3)
  -- the promises
  let Prom : X → Prop := fun x => (D.matrix x).IsHermitian ∧
    (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧ (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
  by_cases hx : ∃ x, Prom x
  swap
  · refine ⟨Fin k, inferInstance, inferInstance, Function.Embedding.refl _, [], by simp, by simp,
      ?_, ?_, fun x hH hrow hcol => absurd ⟨x, hH, hrow, hcol⟩ hx⟩
    · simp only [nCallsN, List.countP_nil, Nat.cast_zero]; positivity
    · simp only [nGatesN, List.countP_nil, Nat.cast_zero]; positivity
  obtain ⟨x₀, hx₀⟩ := hx
  -- the native facts
  have hnat : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
      (x : X), Prom x →
      (∀ i ∈ Cn, i.Valid) ∧
      (∀ p : NativeSparseBlockEncoding.Query → Bool, (nCallsN p Cn : ℝ) ≤
        55296 * qn * (2 * (if p NativeSparseBlockEncoding.Query.rowLocation then 1 else 0) +
          2 * (if p NativeSparseBlockEncoding.Query.columnLocation then 1 else 0) +
          (if p NativeSparseBlockEncoding.Query.value then 1 else 0))) ∧
      (nGatesN Cn : ℝ) ≤ Nb ∧
      ‖nrun (prims (R := R) D' en x) Cn ∘L sysEmb (Sim.io (P := Reg (Fin k) R)) -
          sysEmb (Sim.io (P := Reg (Fin k) R)) ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            qlift (R := R) en (SparseStateOverlap.matrixOperator (D'.matrix x)))‖ ≤ εn := by
    intro R _ _ _ x hxp
    have hH' := NativeSparseRescaling.normalize_hermitian D η hη x hxp.1
    have hrow' := fun i => NativeSparseRescaling.normalized_row_energy D η hη x i (hxp.2.1 i)
    have hcol' := fun j => NativeSparseRescaling.normalized_column_energy D η hη x j (hxp.2.2 j)
    obtain ⟨hv, -⟩ := binary_simulationD (R := R) D' en sb hF.hsb hF.hs hF.range x hH' hrow' hcol'
      γ τ εn ζ hγ hγ1 hτ hεn0 (by linarith) hζ0.le ar har' hζε'
    obtain ⟨hc, hg, he⟩ := hall (R := R) D' en sb hF.hsb hF.hs hF.range x hH' hrow' hcol' ζ ar
      hζ0.le har' hζε
    -- fold the local definitions syntactically (unfolding them by `whnf` is too slow)
    rw [← hCn] at hv hc hg he
    rw [← hqndef] at hc hg
    rw [← hNb] at hg
    exact ⟨hv, hc, hg, he⟩
  -- the normalised data have the same oracles, and `e^{-iτH/η} = e^{-i|t|H}`
  have hprims : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
      (x : X), prims (R := R) D' en x = prims (R := R) D en x := by
    intro R _ _ _ x
    funext j; cases j <;> rfl
  have hexp : ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
      (x : X), (-Complex.I * (τ : ℂ)) •
        qlift (R := R) en (SparseStateOverlap.matrixOperator (D'.matrix x)) =
        (-Complex.I * ((|t| : ℝ) : ℂ)) •
          qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)) := by
    intro R _ _ _ x
    have h1 := NativeSparseRescaling.exponent_cancel D η hη x |t|
    have h2 := congrArg (qlift (R := R) en) h1
    rw [qlift, qlift, map_smul, map_smul] at h2
    rw [hτdef]
    push_cast at h2 ⊢
    exact h2
  obtain ⟨hv0, hc0, hg0, -⟩ := hnat (R := EuclideanSpace ℂ (ULift.{w} (Fin 1))) x₀ hx₀
  have hcalls5 : ∀ p : NativeSparseBlockEncoding.Query → Bool,
      (2 * (if p NativeSparseBlockEncoding.Query.rowLocation then 1 else 0) +
        2 * (if p NativeSparseBlockEncoding.Query.columnLocation then 1 else 0) +
        (if p NativeSparseBlockEncoding.Query.value then 1 else 0) : ℝ) ≤ 5 := by
    intro p
    split_ifs <;> norm_num
  -- the signed native circuit: the inverse circuit for negative time
  set Cs := if 0 ≤ t then Cn else ninv Cn with hCs
  have hCs_valid : ∀ i ∈ Cs, i.Valid := by
    rw [hCs]; split_ifs
    · exact hv0
    · exact valid_ninv _ hv0
  have hCs_calls : ∀ p, nCallsN p Cs = nCallsN p Cn := by
    intro p; rw [hCs]; split_ifs
    · rfl
    · exact nCallsN_ninv p Cn
  have hCs_gates : nGatesN Cs = nGatesN Cn := by
    rw [hCs]; split_ifs
    · rfl
    · exact nGatesN_ninv Cn
  have hε2' : (0 : ℝ) < ε / 2 := by positivity
  obtain ⟨hsv, hsk', hsg, hsc⟩ := synthBudget_spec hS hε2' Cs hCs_valid
  refine ⟨_, inferInstance, inferInstance, sysWire _ _ _ _ _ _ _ _, synthBudget hS (ε / 2) Cs,
    hsv, hsk', ?_, ?_, ?_⟩
  · -- the primitive calls
    rw [hsc, hCs_calls]
    have h1 := hc0 (fun _ => true)
    have h5 := hcalls5 (fun _ => true)
    have h2 := mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ 55296 * qn by positivity)
    have h3 : 55296 * qn * 5 ≤ 552960 * q := by linarith
    exact h1.trans (h2.trans h3)
  · -- the gates
    have h1 : (nGatesN (synthBudget hS (ε / 2) Cs) : ℝ) ≤
        ((nGatesN Cs * L' (ε / 2 / (nGatesN Cs + 1)) : ℕ) : ℝ) := by exact_mod_cast hsg
    have h2 := hfin (nGatesN Cs) (by rw [hCs_gates]; exact hg0)
    linarith
  · -- the full-output error
    intro R _ _ _ x hH hrow hcol
    obtain ⟨hv, -, -, he⟩ := hnat (R := R) x ⟨hH, hrow, hcol⟩
    rw [hprims x, hexp x] at he
    have hprim := prims_isUnitary (R := R) D en x
    have hU : OracleCircuit.IsUnitary (nrun (prims (R := R) D en x) Cn) :=
      nrun_isUnitary _ hprim _ hv
    have hHs : star (qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x))) =
        qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)) :=
      GateOptimalBinary.sysH_star D en x hH
    have herr' : ‖nrun (prims (R := R) D en x) Cs ∘L sysEmb (Sim.io (P := Reg (Fin k) R)) -
        sysEmb (Sim.io (P := Reg (Fin k) R)) ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          qlift (R := R) en (SparseStateOverlap.matrixOperator (D.matrix x)))‖ ≤ εn := by
      rw [hCs]
      split_ifs with ht
      · rw [show ((|t| : ℝ) : ℂ) = (t : ℂ) by rw [abs_of_nonneg ht]] at he
        exact he
      · push Not at ht
        rw [nrun_ninv]
        exact neg_time_error _ hU _ _ hHs ht he
    have h := synthBudget_error hS hε2' Cs hCs_valid (prims (R := R) D en x) hprim _
      (by intro p; exact (norm_sysEmb _ (fun φ => by rw [Sim.io_apply, norm_bas]) p).le) _ herr'
    rw [cleanEmb_sysEmb_io] at h
    have e : εn + ε / 2 = ε := by rw [hεn]; ring
    rw [e] at h
    exact fullOutputError_of_norm h


/-! ### The arithmetic of the padded data with a validity decoder -/

/-- The decoder of the padded data with a validity decoder, rescaled, is the validity decoder of
the wrapper. -/
theorem padDataE_decode_flag {X : Type*} {N s k b : ℕ} (D : QData X N s k b) (κ : ℝ) :
    (fun y : Cfg (BW (k + 1) b) =>
      (κ : ℂ) * D.padDataE.decode (phiE (Equiv.refl _) (eword y)) (vword y)) =
      flagDec N (fun z => (κ : ℂ) * D.val z) := by
  funext y
  rw [QData.padDataE_decode, pdecode_flag]
  unfold flagDec
  by_cases hv : evalidW N (eword y) = true
  · rw [if_pos hv, if_pos hv]
  · rw [if_neg hv, if_neg hv, mul_zero]

/-- **The arithmetic assumption of the padded data with a validity decoder**, from the rotation
arithmetic of the decoder on the value word: the validity of the index pair, the arithmetic, the
controlled copies and the uncomputation (`RotWordArith.flagLift`). -/
theorem comp_decArith_padDataE {cA : ℝ} {dA : ℕ} (hcA : 0 ≤ cA) {X : Type*} {N s k b bd : ℕ}
    (D : QData X N s k b) {K₀ K : ℝ} (h : comp_rotArith cA dA bd k b D.val K₀ K) :
    comp_decArith (3 * cA + 18) (max dA 1) bd (k + 1) b D.padDataE (Equiv.refl _) K₀ K := by
  intro κ hκ hκm hκK ζ hζ hζ1
  obtain ⟨bT, bP, A, ar, hcost⟩ := h κ hκ hκm hκK ζ hζ hζ1
  refine ⟨ar.flagLift (k := k) N, ?_, ?_⟩
  · rw [padDataE_decode_flag]
    exact ar.flagLift_ok N D.N_lt_pow_succ
  · have hlog : 0 ≤ Real.logb 2 (1 / ζ) :=
      Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hζ]; linarith)
    have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    set w : ℝ := (bd : ℝ) + ((k + 1 : ℕ) : ℝ) + Real.logb 2 (1 / ζ) + 1 with hw
    have hwk : (k : ℝ) + 2 ≤ w := by rw [hw]; push_cast; linarith
    have hw1 : 1 ≤ w := by linarith
    have hw0 : (bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1 ≤ w := by rw [hw]; push_cast; linarith
    have hw00 : 0 ≤ (bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1 := by linarith
    have h1 : ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA ≤ w ^ max dA 1 :=
      (pow_le_pow_left₀ hw00 hw0 dA).trans (pow_le_pow_right₀ hw1 (le_max_left _ _))
    have h2 : w ≤ w ^ max dA 1 := le_self_pow₀ hw1 (by omega)
    have hcostw : cA * ((bd : ℝ) + k + Real.logb 2 (1 / ζ) + 1) ^ dA ≤ cA * w ^ max dA 1 :=
      mul_le_mul_of_nonneg_left h1 hcA
    have hlen := RotWordArith.flagLift_length (k := k) N ar
    have hV := length_validC_le (k := k) N
    have e : (((ar.flagLift (k := k) N).circ.length + (ar.flagLift (k := k) N).bT +
        (ar.flagLift (k := k) N).bP + (ar.flagLift (k := k) N).A : ℕ) : ℝ) =
        ((2 * (validC (k := k) N).length + 2 * ar.circ.length + (bT + bP) + bT + bP +
          (bT + bP + A + (2 * k + 6)) : ℕ) : ℝ) := by
      rw [hlen, RotWordArith.flagLift_bT, RotWordArith.flagLift_bP, RotWordArith.flagLift_A,
        flagA, card_FW]
    rw [e]
    push_cast
    have hc : ((ar.circ.length + bT + bP + A : ℕ) : ℝ) = (ar.circ.length : ℝ) + bT + bP + A := by
      push_cast; ring
    rw [hc] at hcost
    have hV' : ((validC (k := k) N).length : ℝ) ≤ 4 * (k + 1) + 2 := by exact_mod_cast hV
    have hT0 : (0 : ℝ) ≤ bT := Nat.cast_nonneg _
    have hP0 : (0 : ℝ) ≤ bP := Nat.cast_nonneg _
    nlinarith


/-! ### Theorem `hs:thm:gates` for general sizes and general decoders -/

/-- The rotation arithmetic serves every smaller range of rescalings. -/
theorem comp_rotArith_mono {cA : ℝ} {dA bd k b : ℕ} {val : Cfg (VW b) → ℂ} {K₀ K K' : ℝ}
    (h : comp_rotArith cA dA bd k b val K₀ K) (hK : K' ≤ K) :
    comp_rotArith cA dA bd k b val K₀ K' :=
  fun κ hκ hκm hκK ζ hζ hζ1 => h κ hκ hκm (hκK.trans hK) ζ hζ hζ1

set_option maxHeartbeats 4000000 in
/-- **Theorem `hs:thm:gates`, eq. `hs:eq:gate-binary`, for sparse access of
general size and general decoders.** For a finite gate set admitting single-qubit synthesis of
length at most `c₁ log(1/ζ) + c₀` and an exact decomposition of its controlled one-qubit gates, and
the arithmetic assumption with constants `c_A`, `d_A`, there are constants `C` and `K` such that:
for sparse data of general size (`SparseHamiltonian.GeneralSparseAccess.QData`: an `N × N` matrix
with `s`-sparse lists, `1 ≤ s ≤ N`, on `k = ⌈log₂ N⌉`-qubit index registers, locators prescribed
on valid list inputs only, the value oracle XOR-writing a stored word on every pair of index
words) with any public decoder `val` of its stored words, stored words of `2b` bits with
`b ≤ b_data` and the rotation arithmetic of the decoder at the rescalings `κ ∈ [1/η, √(2s)/η]`
(`comp_rotArith`), every time `t` and `0 < ε ≤ 1/2`, one circuit over the gate set and the
supplied sparse oracles, fixed before the instance, uses at most `6635520 Q_base` primitive sparse
queries, at most `C Q_base (𝔟 + 1)^K` gates with
`Q_base = √s η|t| + √(s η|t| log(1/ε)) + log(1/ε)` and
`𝔟 = b_data + log₂(N+1) + log₂((Q_base+1)/ε)`, and on every instance whose matrix is Hermitian
with row
and column Euclidean norms at most `η > 0` has full-output error at most `ε` on the clean embedding
of the index register, against the evolution of the matrix extended by zero to the index words
`≥ N`, with an untouched reference. On an invalid index pair the rotation is that of the zero
entry, selected by the validity of the pair independently of the returned word (Section
`hs:sec:gates`, before eq. `hs:eq:gate-schedule`). As in eq. `hs:eq:gate-binary`, the work-qubit
count of eq. `hs:eq:gate-total` is not stated. -/
theorem hs_thm_gates_decoder (cA : ℝ) (dA : ℕ) (hcA : 0 ≤ cA) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (Kd : ℕ) {𝒢 : Set Kind}
    {X₁ X₂ : Type} [Fintype X₁] [DecidableEq X₁] [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ}
    (ext_singleQubitSynthesis : OneQubitSynthesis 𝒢 X₁ L)
    (ext_singleQubitLength : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (ext_controlDecomposition : ControlDecomposition 𝒢 X₂ Kd) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ {X : Type u} {N s k b : ℕ} (D : GeneralSparseAccess.QData X N s k b) (bd : ℕ)
        (η t ε : ℝ),
        2 ^ k < 2 * N → b ≤ bd →
        comp_rotArith cA dA bd k b D.val (1 / η) (Real.sqrt (2 * s) / η) →
        0 < η → 0 < ε → ε ≤ 1 / 2 →
        ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (sys : Fin k ↪ W)
          (Cc : List (NInstr W (PY k b) NativeSparseBlockEncoding.Query)),
          (∀ i ∈ Cc, i.Valid) ∧ (∀ g, NInstr.gate g ∈ Cc → GateOf 𝒢 g) ∧
          (nCallsN (fun _ => true) Cc : ℝ) ≤ 6635520 * mainBound s (η * |t|) ε ∧
          (nGatesN Cc : ℝ) ≤ C * mainBound s (η * |t|) ε *
            (bitH bd N (mainBound s (η * |t|) ε) ε + 1) ^ K ∧
          ∀ {R : Type w} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
            (x : X),
            (D.matrix x).IsHermitian → (∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            (∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) →
            FullOutputError (nrun (D.prims (R := R) x) Cc) (cleanAlong sys)
              (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                qlift (R := R) (Equiv.refl _) (SparseStateOverlap.matrixOperator (D.padMat x)))) ε := by
  obtain ⟨L', c₀', c₁', hc₀', hc₁', hS, hL'⟩ := synthesis_of_parts hc₀ hc₁
    ext_singleQubitSynthesis ext_singleQubitLength ext_controlDecomposition
  obtain ⟨C₀', K₀, hC₀', hbin⟩ := hs_gates_dataDec.{u, 0, w} (3 * cA + 18) (max dA 1)
    (by positivity) hc₀ hc₁ Kd ext_singleQubitSynthesis ext_singleQubitLength
    ext_controlDecomposition
  -- one constant for the gates and the calls of the circuit of the padded data
  set C₀ : ℝ := C₀' + 552960 with hC₀def
  have hC₀ : 0 < C₀ := by rw [hC₀def]; linarith
  have hC₀le : C₀' ≤ C₀ := by rw [hC₀def]; linarith
  have hC₀c : (552960 : ℝ) ≤ C₀ := by rw [hC₀def]; linarith
  set K' := max K₀ 2 with hK'
  set a : ℝ := 4 * 6 ^ K' with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  set cG : ℝ := (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
    c₀'))) * C₀ with hcG
  have hcG0 : 0 ≤ cG := by
    have h0 : 0 ≤ (a + 256) * C₀ := by positivity
    have : 0 ≤ Real.log (2 * ((a + 256) * C₀ + 2)) := Real.log_nonneg (by linarith)
    positivity
  set C : ℝ := cG + 1 with hC
  refine ⟨C, K', by rw [hC]; linarith, ?_⟩
  intro X N s k b D bd η t ε hk hbd hdec hη hε hε2
  have hεh : 0 < ε / 2 := by positivity
  have hε1 : ε ≤ 1 := by linarith
  -- the arithmetic of the padded data
  have hsP2 : Real.sqrt ((sP s : ℕ) : ℝ) / η ≤ Real.sqrt (2 * s) / η := by
    apply div_le_div_of_nonneg_right _ hη.le
    apply Real.sqrt_le_sqrt
    have h' : ((sP s : ℕ) : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (sP_lt D.slots_pos).le
    push_cast at h'
    exact h'
  have hdecP := comp_decArith_padDataE hcA D (comp_rotArith_mono hdec hsP2)
  have hsizes : BinarySizes D.padDataE (Equiv.refl _) (sbP s) :=
    ⟨(sbP_le D.s_le_pow).trans (Nat.le_succ k), rfl, fun j => pslot_range D.s_le_pow j⟩
  obtain ⟨W, _, _, sys, Cc, hv, hg, hcalls, hgates, herr⟩ :=
    hbin D.padDataE (Equiv.refl _) (sbP s) bd η t (ε / 2) hsizes hbd hdecP hη hεh (by linarith)
  -- the parameters
  set τ : ℝ := η * |t| with hτdef
  have hτ : 0 ≤ τ := by positivity
  set q := mainBound s τ ε with hqdef
  have hq2 : 1 / 2 ≤ q := by rw [hqdef, ← shape_eq_mainBound]; exact shape_ge_half s hτ hε hε2
  have hq0 : 0 < q := by linarith
  set q' := mainBound (sP s) τ (ε / 2) with hq'def
  have hq'q : q' ≤ 4 * q := mainBound_pad_le D.slots_pos hτ hε hε2
  have hq'0 : 0 ≤ q' := by
    have := shape_ge_half (sP s) hτ hεh (by linarith)
    rw [shape_eq_mainBound] at this
    linarith
  set B := bitH bd N q ε + 1 with hBdef
  have hY1 : 1 ≤ (q + 1) / ε := by rw [le_div_iff₀ hε]; linarith
  have hlogY : 0 ≤ Real.logb 2 ((q + 1) / ε) := Real.logb_nonneg one_lt_two hY1
  have hlogN : 0 ≤ Real.logb 2 ((N : ℝ) + 1) :=
    Real.logb_nonneg one_lt_two (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  have hB1 : 1 ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBY : Real.logb 2 ((q + 1) / ε) ≤ B := by rw [hBdef]; unfold bitH; linarith
  have hBk : (k : ℝ) ≤ B := by
    have := k_le_logb hk
    rw [hBdef]; unfold bitH; linarith
  have hBb : (b : ℝ) ≤ B := by
    have : (b : ℝ) ≤ bd := by exact_mod_cast hbd
    rw [hBdef]; unfold bitH; linarith
  -- the word of the padded data
  have hcard : Fintype.card (Cfg (Fin (k + 1))) = 2 ^ (k + 1) := card_eq_two_pow (Equiv.refl _)
  have hB' : bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1 ≤ 6 * B := by
    rw [hcard]
    have h1 := logb_pow_succ_le hk
    have h2 := logb_scale_le hq'0 hq'q hε
    rw [hBdef]
    unfold bitH
    linarith
  have hB'0 : 0 ≤ bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1 := by
    have := bitH_nonneg bd (Fintype.card (Cfg (Fin (k + 1)))) hq'0 hεh (by linarith)
    linarith
  have hpow : (bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1) ^ K₀ ≤
      6 ^ K' * B ^ K' := by
    calc (bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1) ^ K₀
        ≤ (6 * B) ^ K₀ := pow_le_pow_left₀ hB'0 hB' K₀
      _ = 6 ^ K₀ * B ^ K₀ := mul_pow _ _ _
      _ ≤ 6 ^ K' * B ^ K' :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) (le_max_left K₀ 2))
            (pow_le_pow_right₀ hB1 (le_max_left K₀ 2)) (by positivity) (by positivity)
  -- the counts of the circuit of the padded data
  have hq'c : (552960 : ℝ) * q' ≤ 552960 * (4 * q) := mul_le_mul_of_nonneg_left hq'q (by norm_num)
  have hnC : (nCallsN (fun _ => true) Cc : ℝ) ≤ 4 * C₀ * q := by
    have h1 : (552960 : ℝ) * (4 * q) ≤ C₀ * (4 * q) :=
      mul_le_mul_of_nonneg_right hC₀c (by linarith)
    linarith
  have hnG : (nGatesN Cc : ℝ) ≤ a * C₀ * q * B ^ K' := by
    have h2 : C₀' * q' * (bitH bd (Fintype.card (Cfg (Fin (k + 1)))) q' (ε / 2) + 1) ^ K₀ ≤
        C₀ * (4 * q) * (6 ^ K' * B ^ K') :=
      mul_le_mul (mul_le_mul hC₀le hq'q hq'0 hC₀.le) hpow (by positivity) (by positivity)
    have e : C₀ * (4 * q) * (6 ^ K' * B ^ K') = a * C₀ * q * B ^ K' := by rw [ha]; ring
    linarith
  have hG : (implG k b : ℝ) ≤ 64 * B := by
    unfold implG
    push_cast
    linarith
  -- the accuracy of the synthesis
  set n := nGatesN (subst (implPE N s) Cc) with hn
  set ζ : ℝ := ε / 2 / ((n : ℝ) + 1) with hζ
  have hζ0 : 0 < ζ := by positivity
  obtain ⟨hv', hg', hcalls', hgates', hn'⟩ :=
    genCircE_spec (N := N) (s := s) hS hζ0 Cc hv hg
  refine ⟨(W ⊕ GeneralSparseAccess.AW k b) ⊕ (X₂ ⊕ X₁), inferInstance, inferInstance,
    genSys (X₂ ⊕ X₁) sys, genCircE hS ζ N s Cc, hv', hg', ?_, ?_, ?_⟩
  · -- the calls
    have h1 : (nCallsN (fun _ => true) (genCircE hS ζ N s Cc) : ℝ) ≤
        3 * nCallsN (fun _ => true) Cc := by exact_mod_cast hcalls'
    linarith
  · -- the gates
    have h1 : (nGatesN (genCircE hS ζ N s Cc) : ℝ) ≤
        ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) := by
      exact_mod_cast hgates'
    have h2 : ((nGatesN Cc + implG k b * nCallsN (fun _ => true) Cc * (1 + L' ζ) : ℕ) : ℝ) ≤
        (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
          c₀'))) * C₀ * q * B ^ K' :=
      gen_gates_le (K := K') (le_max_right K₀ 2) hq2 hB1 hC₀.le ha0 hc₀' hc₁' hε hε1 hBY hnG
        hnC hG hn' hL'
    have h3 : cG * q * B ^ K' ≤ C * q * B ^ K' := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hq0.le
      linarith
    have e : (a + 256 * (1 + (c₁' * (Real.log (2 * ((a + 256) * C₀ + 2)) + (K' : ℝ) + 1) +
        c₀'))) * C₀ * q * B ^ K' = cG * q * B ^ K' := by rw [hcG]
    linarith
  · -- the error
    intro R _ _ _ x hH hrow hcol
    have hM := padForm_padDataE D
    have h1 := herr (R := R) x (hM.isHermitian x hH) (hM.row_le x hrow) (hM.col_le x hcol)
    have h2 := genCircE_error D hS hζ0 sys Cc hv x t (ε / 2) hεh.le h1
    intro ψ hψ
    refine (h2 ψ hψ).trans ?_
    have h3 : (n : ℝ) * ζ ≤ ε / 2 := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      rw [hζ, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith

end

end ManuscriptConformance
