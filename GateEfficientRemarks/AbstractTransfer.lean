import GateEfficientHamiltonian.Circuit.Theorem
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Lemma `hs:lem:abstract`: negative times and the second moment

Lemma `hs:lem:abstract` of the accompanying paper (the general boundary-resolvent simulation
lemma) simulates `e^{-itH}` for every real time `t`; its proof treats `t > 0` and uses "the
inverse circuit" for negative times. In the gate model of `GateEfficientHamiltonian` the
private operation `D` is supplied with its adjoint `D†`, and both may be called with a control.
This file prepares the statement of the lemma for every real `t`:

* `flipD`, `flipDs`: the circuit with the private calls `D` and `D†` exchanged; it runs, with
  the private operation `D`, as the original circuit with `D†` in place of `D`
  (`run_flipDs`), with the same counts and validity (`nPriv_flipDs`, `nUJ_flipDs`,
  `nGates_flipDs`, `valid_flipDs`);
* `resolvent_adjoint`: for a unitary `D` with the two-sided inverse `R₁` of `1 - D`,
  `R₁† = 1 - R₁`; hence the interface `hs:eq:interface` of `D` and `h` gives the interface of
  `D†` and `-h` with the inverse `1 - R₁` (`transfer_unitary`, `transfer_right`,
  `transfer_left`, `transfer_norm`, `transfer_boundary`, `transfer_moment`,
  `transfer_endpoint`);
* `adjoint_comp_self_le_iff`: the compressed second-moment bound of `hs:eq:interface` in the
  Loewner order, `T† T ≤ c • 1`, is the norm bound `‖T‖² ≤ c` (for `c ≥ 0`), the form of the
  released endpoint hypothesis `‖R₁ J‖ ≤ b`, `b² ≤ q̄/2` (`re_inner_moment`); in the paper's
  form `J† R† R J ≤ (ν/2) • 1 ↔ ‖R J‖² ≤ ν/2` (`second_moment_iff`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct

/-! ### Exchanging the private calls `D` and `D†` -/

section Flip

variable {W : Type*}

/-- The instruction with the private call `D` replaced by `D†` and `D†` by `D`; elementary
gates and calls of `U_J` are unchanged (`hs:lem:abstract`, negative times). -/
def flipD : Instr W → Instr W
  | .gate g => .gate g
  | .uj cs adj => .uj cs adj
  | .priv cs adj => .priv cs (!adj)

/-- The circuit with the private calls `D` and `D†` exchanged (`hs:lem:abstract`, negative
times). -/
def flipDs (gs : List (Instr W)) : List (Instr W) := gs.map flipD

/-- Exchanging `D` and `D†` keeps elementary gates (`hs:lem:abstract`). -/
theorem isGate_flipD (g : Instr W) : (flipD g).isGate = g.isGate := by
  cases g <;> rfl

/-- Exchanging `D` and `D†` keeps calls of `U_J` (`hs:lem:abstract`). -/
theorem isUJ_flipD (g : Instr W) : (flipD g).isUJ = g.isUJ := by
  cases g <;> rfl

/-- Exchanging `D` and `D†` keeps private calls (`hs:lem:abstract`). -/
theorem isPriv_flipD (g : Instr W) : (flipD g).isPriv = g.isPriv := by
  cases g <;> rfl

/-- The number of elementary gates is unchanged (`hs:lem:abstract`). -/
theorem nGates_flipDs (gs : List (Instr W)) : nGates (flipDs gs) = nGates gs := by
  simp only [nGates, flipDs, List.countP_map, Function.comp_def, isGate_flipD]

/-- The number of calls of `U_J` is unchanged (`hs:lem:abstract`). -/
theorem nUJ_flipDs (gs : List (Instr W)) : nUJ (flipDs gs) = nUJ gs := by
  simp only [nUJ, flipDs, List.countP_map, Function.comp_def, isUJ_flipD]

/-- The number of private calls is unchanged (`hs:lem:abstract`). -/
theorem nPriv_flipDs (gs : List (Instr W)) : nPriv (flipDs gs) = nPriv gs := by
  simp only [nPriv, flipDs, List.countP_map, Function.comp_def, isPriv_flipD]

/-- Validity is unchanged (`hs:lem:abstract`). -/
theorem valid_flipDs {a : ℕ} (anc : Fin a → W) (gs : List (Instr W))
    (h : ∀ g ∈ gs, g.Valid anc) : ∀ g ∈ flipDs gs, g.Valid anc := by
  intro g hg
  simp only [flipDs, List.mem_map] at hg
  obtain ⟨g', hg', rfl⟩ := hg
  have h' := h g' hg'
  cases g' with
  | gate g => exact h'
  | uj cs adj => exact h'
  | priv cs adj => exact h'

/-- **Exchanging `D` and `D†`**: run with the private operation `D`, the circuit `flipDs gs`
is the circuit `gs` run with the private operation `D†` (`hs:lem:abstract`). -/
theorem run_flipDs {a m r K : ℕ} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    [CompleteSpace P] (UJ D : Vsp a P →L[ℂ] Vsp a P) (gs : List (Instr (Wire a m r K))) :
    run (simSem UJ D) (flipDs gs) = run (simSem UJ (D†)) gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
      have e : flipDs (g :: gs) = flipD g :: flipDs gs := rfl
      rw [e, run_cons, run_cons, ih]
      congr 1
      cases g with
      | gate g => rfl
      | uj cs adj => rfl
      | priv cs adj =>
          cases adj
          · rfl
          · change oracleOp Wire.anc anc_injective cs D =
              oracleOp Wire.anc anc_injective cs ((D†)†)
            rw [adjoint_adjoint]

end Flip

/-! ### The interface of `D†` -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The resolvent at one of a unitary**: if `D` is unitary and `R₁` is the two-sided inverse
of `1 - D`, then `R₁† = 1 - R₁` (`hs:lem:abstract`, `ov:eq:response`). -/
theorem resolvent_adjoint (D R1 : E →L[ℂ] E) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) : R1† = 1 - R1 := by
  have hR : (1 - D) * R1 = 1 := by rw [mul_def]; exact hRight
  have hL : R1 * (1 - D) = 1 := by rw [mul_def]; exact hLeft
  have h1 : (1 - star D) * (-(R1 * D)) = 1 := by
    have e : (1 - star D) = -(star D) * (1 - D) := by
      rw [neg_mul, mul_sub, mul_one, hD.1]
      abel
    rw [e]
    calc -(star D) * (1 - D) * (-(R1 * D)) = star D * ((1 - D) * R1) * D := by noncomm_ring
      _ = 1 := by rw [hR, mul_one, hD.1]
  have h2 : star R1 * (1 - star D) = 1 := by
    rw [← star_one (E →L[ℂ] E), ← star_sub, ← star_mul, hR, star_one]
  have h3 : star R1 = 1 - R1 := by
    calc star R1 = star R1 * ((1 - star D) * (-(R1 * D))) := by rw [h1, mul_one]
      _ = star R1 * (1 - star D) * (-(R1 * D)) := by rw [mul_assoc]
      _ = -(R1 * D) := by rw [h2, one_mul]
      _ = R1 * (1 - D) - R1 := by noncomm_ring
      _ = 1 - R1 := by rw [hL]
  rw [← star_eq_adjoint]
  exact h3

/-- The adjoint of a unitary is unitary (`hs:lem:abstract`, negative times). -/
theorem transfer_unitary (D : E →L[ℂ] E) (hD : IsUnitary D) : IsUnitary (D†) := by
  rw [← star_eq_adjoint]
  exact hD.adjoint

/-- `1 - R₁` is a right inverse of `1 - D†` (`hs:lem:abstract`, negative times). -/
theorem transfer_right (D R1 : E →L[ℂ] E) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) :
    (1 - D†) ∘L (1 - R1) = 1 := by
  rw [← resolvent_adjoint D R1 hD hRight hLeft, ← mul_def, ← star_eq_adjoint, ← star_eq_adjoint,
    ← star_one (E →L[ℂ] E), ← star_sub, ← star_mul, mul_def, hLeft, star_one]

/-- `1 - R₁` is a left inverse of `1 - D†` (`hs:lem:abstract`, negative times). -/
theorem transfer_left (D R1 : E →L[ℂ] E) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) :
    (1 - R1) ∘L (1 - D†) = 1 := by
  rw [← resolvent_adjoint D R1 hD hRight hLeft, ← mul_def, ← star_eq_adjoint, ← star_eq_adjoint,
    ← star_one (E →L[ℂ] E), ← star_sub, ← star_mul, mul_def, hRight, star_one]

/-- `‖1 - R₁‖ = ‖R₁‖` (`hs:lem:abstract`, negative times). -/
theorem transfer_norm (D R1 : E →L[ℂ] E) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) : ‖1 - R1‖ = ‖R1‖ := by
  rw [← resolvent_adjoint D R1 hD hRight hLeft]
  exact LinearIsometryEquiv.norm_map _ _

/-- **The boundary identity for `-h`**: if `J` is an isometry and `J† R₁ J = (1 + i h)/2`, then
`J† (1 - R₁) J = (1 + i (-h))/2` (`hs:eq:interface`, negative times). -/
theorem transfer_boundary {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (J : F →L[ℂ] E) (hJ : J† ∘L J = 1) (R1 : E →L[ℂ] E) (h : F →L[ℂ] F)
    (hB : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • h)) :
    J† ∘L (1 - R1) ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • (-h)) := by
  rw [sub_comp, comp_sub, show (1 : E →L[ℂ] E) ∘L J = J from id_comp J, hJ, hB]
  module

/-- **The second moment for `1 - R₁`**: `((1 - R₁) J)† ((1 - R₁) J) = (R₁ J)† (R₁ J)`
(`hs:eq:interface`, negative times), since `(1 - R₁)† = R₁` and `R₁` commutes with `1 - R₁`. -/
theorem transfer_moment {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (D R1 : E →L[ℂ] E) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (J : F →L[ℂ] E) :
    ((1 - R1) ∘L J)† ∘L ((1 - R1) ∘L J) = (R1 ∘L J)† ∘L (R1 ∘L J) := by
  have hadj := resolvent_adjoint D R1 hD hRight hLeft
  have h1 : (1 - R1)† = R1 := by
    rw [map_sub, hadj, ← star_eq_adjoint, star_one]
    abel
  have h2 : R1 ∘L (1 - R1) = (1 - R1) ∘L R1 := by
    rw [comp_sub, sub_comp, show R1 ∘L (1 : E →L[ℂ] E) = R1 from comp_id R1,
      show (1 : E →L[ℂ] E) ∘L R1 = R1 from id_comp R1]
  rw [adjoint_comp, adjoint_comp, h1, hadj]
  simp only [comp_assoc]
  rw [← comp_assoc R1 (1 - R1), h2, comp_assoc]

/-- `‖(1 - R₁) J‖ = ‖R₁ J‖` (`hs:eq:interface`, negative times). -/
theorem transfer_endpoint {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (D R1 : E →L[ℂ] E) (hD : IsUnitary D)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (J : F →L[ℂ] E) :
    ‖(1 - R1) ∘L J‖ = ‖R1 ∘L J‖ := by
  have h := congrArg norm (transfer_moment D R1 hD hRight hLeft J)
  rw [norm_adjoint_comp_self, norm_adjoint_comp_self] at h
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp h

end Transfer

/-! ### The second moment in the Loewner order -/

section Moment

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- `re ⟪(c • 1 - T† T) x, x⟫ = c ‖x‖² - ‖T x‖²` for real `c` (`hs:eq:interface`). -/
theorem re_inner_moment (T : E →L[ℂ] F) (c : ℝ) (x : E) :
    RCLike.re (inner ℂ (((c : ℂ) • (1 : E →L[ℂ] E) - T† ∘L T) x) x) =
      c * ‖x‖ ^ 2 - ‖T x‖ ^ 2 := by
  have h1 : RCLike.re (inner ℂ (((c : ℂ) • (1 : E →L[ℂ] E)) x) x) = c * ‖x‖ ^ 2 := by
    rw [smul_apply, one_apply_eq_self, inner_smul_left, Complex.conj_ofReal, RCLike.re_to_complex,
      Complex.re_ofReal_mul, ← RCLike.re_to_complex, inner_self_eq_norm_sq]
  rw [sub_apply, inner_sub_left, map_sub, h1, apply_norm_sq_eq_inner_adjoint_left]

/-- **The compressed second-moment bound in the Loewner order** (`hs:eq:interface`): for
`c ≥ 0` and a bounded operator `T`, `T† T ≤ c • 1` in Mathlib's Loewner order on operators if
and only if `‖T‖² ≤ c`. With `T = R₀(1) J` and `c = ν/2` this identifies the paper's
`J† R₀(1)† R₀(1) J ⪯ (ν/2) I` with the released endpoint hypothesis `‖R₁ J‖ ≤ b`,
`b² ≤ q̄/2`. -/
theorem adjoint_comp_self_le_iff (T : E →L[ℂ] F) {c : ℝ} (hc : 0 ≤ c) :
    T† ∘L T ≤ (c : ℂ) • (1 : E →L[ℂ] E) ↔ ‖T‖ ^ 2 ≤ c := by
  rw [le_def]
  constructor
  · intro hpos
    have hx : ∀ x, ‖T x‖ ≤ Real.sqrt c * ‖x‖ := by
      intro x
      have h0 := hpos.re_inner_nonneg_left x
      rw [re_inner_moment] at h0
      have h1 : ‖T x‖ ^ 2 ≤ (Real.sqrt c * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hc]
        linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h1
    have h2 : ‖T‖ ≤ Real.sqrt c := opNorm_le_bound _ (Real.sqrt_nonneg c) hx
    have h3 := pow_le_pow_left₀ (norm_nonneg T) h2 2
    rwa [Real.sq_sqrt hc] at h3
  · intro hT
    rw [isPositive_def']
    refine ⟨?_, fun x => ?_⟩
    · refine IsSelfAdjoint.sub ?_ (isPositive_adjoint_comp_self T).isSelfAdjoint
      refine IsSelfAdjoint.smul ?_ (IsSelfAdjoint.one _)
      exact Complex.conj_ofReal c
    · change 0 ≤ RCLike.re (inner ℂ (((c : ℂ) • (1 : E →L[ℂ] E) - T† ∘L T) x) x)
      rw [re_inner_moment]
      have h1 : ‖T x‖ ≤ ‖T‖ * ‖x‖ := le_opNorm T x
      have h2 : ‖T x‖ ^ 2 ≤ (‖T‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h3 : (‖T‖ * ‖x‖) ^ 2 = ‖T‖ ^ 2 * ‖x‖ ^ 2 := mul_pow _ _ 2
      have h4 : ‖T‖ ^ 2 * ‖x‖ ^ 2 ≤ c * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hT (by positivity)
      linarith

/-- **The second moment of `hs:eq:interface` in the paper's form**: for operators
`R : F → F`, `J : E → F` and `ν ≥ 0`, `J† R† R J ≤ (ν/2) • 1` in the Loewner order if and only
if `‖R J‖² ≤ ν/2`, the form of the released endpoint hypothesis `‖R₁ J‖ ≤ b`, `b² ≤ q̄/2`. -/
theorem second_moment_iff (R : F →L[ℂ] F) (J : E →L[ℂ] F) {ν : ℝ} (hν : 0 ≤ ν) :
    J† ∘L R† ∘L R ∘L J ≤ ((ν / 2 : ℝ) : ℂ) • (1 : E →L[ℂ] E) ↔ ‖R ∘L J‖ ^ 2 ≤ ν / 2 := by
  rw [← adjoint_comp_self_le_iff (R ∘L J) (by linarith : (0 : ℝ) ≤ ν / 2), adjoint_comp]
  simp only [comp_assoc]

end Moment

end

end SparseHamiltonian.GateRemarks
