import SparseLowerBounds.ODE.JointCompile

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Theorem `odel:thm:joint`: joint time, sparsity and normalisation

Manuscript lines 3860-3905 (statement 3860-3868, proof 3869-3905). For `s ≥ 4`,
`τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`, the ODE promise `g ≤ ḡ` requires
`Q_A ≥ c_J ḡ √s τ` matrix queries, `c_J = 1/400` (`jointConst`), witnessed by
the joint family of `ODE/JointInstance` with `D = 0` (`jointFamily_skew`),
`η = 1`, `g = √M ≥ ḡ/√2` and dimension `O(ḡ² s)`.

Route (lines 3887-3897). Run the solver; on success measure the half indicator
(`halfObs`), on failure output a fair bit: by `Readout.heralded_correlation`
with `sgn = halfSign(a_*)`, ideal value `1` and success `≥ 2/3`, the
unconditional correlation is at least `β = (2/3)(1 - 2ε)` (`jointCorr`), no
division by the success probability. The solver compiles to a membership
program with at most `p.cost w` queries (`Reduction.exists_boolean_program_inner`;
`hardCost`: two per value query, `ODE/JointCompile`), and Lemma `odel:lem:outer`
(`outer_count_ge`) gives `β² n √(Mm)/8` membership queries. The parameters
(`ODE/Parameters`) give `n > τ/5` and `√(Mm) ≥ ḡ √s / 2`, hence
`Q ≥ β² ḡ √s τ / 160 ≥ ḡ √s τ / 400` for `ε ≤ 1/64`.
-/

namespace SparseLowerBounds.ODE

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Readout
open scoped InnerProduct InnerProductSpace

-- The nested time-addressed workspaces exceed the default instance size.
set_option synthInstance.maxSize 1024

/-- The explicit constant of Theorem `odel:thm:joint`: `c_J = 1/400`. -/
def jointConst : ℝ := 1 / 400

/-- The decision correlation `β = (2/3)(1 - 2ε)` (lines 3889-3894). -/
def jointCorr (ε : ℝ) : ℝ := 2 / 3 * (1 - 2 * ε)

/-- **Theorem `odel:thm:joint`, general form**: any labelled family whose labels
are implementable with costs `w` by membership programs; a heralded solver
(success `≥ 2/3`, conditional accuracy `ε`, `2ε ≤ 1`) for the targets
`x(T)/‖x(T)‖ = jointTarget` has Boolean cost at least `β² n √(M 2^μ) / 8`. -/
theorem joint_general {M n μ s : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    {ε : ℝ} (hε : 2 * ε ≤ 1) {W B L G : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (P : ProjFamily B (Fin M × Fin n × Fin (2 ^ μ))) (E : W →L[ℂ] B) (hE : E† ∘L E = 1)
    (O : L → Promised M n (2 ^ μ) → W →L[ℂ] W) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : W) (hφ₀ : ‖φ₀‖ ≤ 1)
    (e : W →L[ℂ] SysGarb (JointIndex M μ s) G) (he : e† ∘L e = 1)
    (herald : W →L[ℂ] W) (hherald : IsStarProjection herald)
    (hsucc : ∀ x, 2 / 3 ≤ ‖herald (p.eval x φ₀)‖ ^ 2)
    (hacc : ∀ x, HeraldedAccurate e herald (p.eval x φ₀) (jointTarget M n μ s x) ε) :
    jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 8 ≤ p.cost w := by
  obtain ⟨c, hcount, hc⟩ := Reduction.exists_boolean_program_inner E hE
    (fun x => P.isUnitary_phase (membership x)) hO w hw p
  have hm := two_le_two_pow hμ
  -- Lines 3887-3894: heralded half measurement, correlation `β` with `halfSign(a_*)`.
  have key : ∀ x, jointCorr ε ≤ halfSign M (oddCand x) *
        (⟪p.eval x φ₀, (herald ∘L outObs e (halfObs M μ s) ∘L herald) (p.eval x φ₀)⟫_ℂ).re ∧
      ‖herald ∘L outObs e (halfObs M μ s) ∘L herald‖ ≤ 1 := fun x =>
    heralded_correlation e he herald hherald (p.eval x φ₀) (jointTarget M n μ s x) ε (hacc x)
      (hsucc x) (halfObs M μ s) halfObs_isSelfAdjoint norm_halfObs_le (a := 1)
      (abs_halfSign (oddCand x)).le
      (by rw [inner_halfObs_jointTarget]; nlinarith [halfSign_sq (oddCand x)]) (by linarith)
  obtain ⟨x₀⟩ := nonempty_promised (M := M) (by omega) hn hm
  have hA := (Reduction.norm_encodeObs_le E hE _).trans (key x₀).2
  have hEφ : ‖E φ₀‖ ≤ 1 := (Reduction.norm_encode E hE φ₀).le.trans hφ₀
  have hβ : 0 ≤ jointCorr ε := by unfold jointCorr; linarith
  have h := outer_count_ge hM hMe hn hm (even_two_pow hμ) P c (E φ₀) hEφ _ hA hβ fun x => by
    rw [hc x φ₀]; exact (key x).1
  push_cast at h
  exact h.trans (by exact_mod_cast hcount)

/-- **Theorem `odel:thm:joint`, native form**: the joint family forces
`β² n √(M 2^μ) / 16` value queries (and as many matrix queries). -/
theorem joint_forces {M n μ s : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hμ : 1 ≤ μ)
    (hμs : 2 ^ μ ≤ s) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {ε : ℝ} (hε : 2 * ε ≤ 1) :
    (jointFamily M n μ s hμ hμs T hT).Forces ε
      (jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  intro ι _ G _ _ _ A
  have h := joint_general (s := s) hM hMe hn hμ hε (jointBoolean ι M n μ s)
    (ancillaEmbed _) ancillaEmbed_isometry ((jointFamily M n μ s hμ hμs T hT).access ι)
    (Family.access_unitary ι _) hardCost (implementsOn_joint ι hμ hμs T hT) A.prog A.seed
    A.seed_norm_le A.out A.out_isometry A.herald A.herald_proj A.success fun x => by
      have hx := A.accurate x _ (jointSol_solves x)
      rwa [jointFamily_T, unitDirection_jointSol_T hT] at hx
  exact Hamiltonian.native_bound_of_cost A.prog (by linarith)

/-- **The hard family at the parameters** `(s, τ, ḡ)` of lines 3870-3876:
`M = jointM ḡ`, `m = 2^{jointMu s}`, `n = jointN τ`, on `[0, τ]` (idle interval,
lines 3883-3884). -/
def jointFamilyAt (s : ℕ) (τ gbar : ℝ) (hs : 4 ≤ s) (hτ : 4 ≤ τ) :
    Family (Promised (jointM gbar) (jointN τ) (2 ^ jointMu s))
      (JointIndex (jointM gbar) (jointMu s) s) (Hamiltonian.Word (jointMu s)) (jointN τ + 2) s :=
  jointFamily (jointM gbar) (jointN τ) (jointMu s) s (one_le_jointMu (by omega))
    (two_pow_jointMu_le (by omega)) τ (jointN_time (by linarith))

/-- **The instance size** (lines 3866-3867, 3876): for `s ≥ 4` and `ḡ ≥ 2`, the hard
family has `g = √M ∈ [ḡ/√2, ḡ]` (`jointFamilyAt_g`) and dimension
`|JointIndex| = 2Mm + s ≤ 3 ḡ² s`. -/
theorem joint_instance_props {s : ℕ} {gbar : ℝ} (hs : 4 ≤ s) (hg : 2 ≤ gbar) :
    gbar / Real.sqrt 2 ≤ Real.sqrt (jointM gbar) ∧ Real.sqrt (jointM gbar) ≤ gbar ∧
      (Fintype.card (JointIndex (jointM gbar) (jointMu s) s) : ℝ) ≤ 3 * gbar ^ 2 * s := by
  refine ⟨div_sqrt_two_le_sqrt_jointM hg, sqrt_jointM_le (by linarith), ?_⟩
  rw [card_jointIndex]
  have hM := jointM_le gbar
  have hm : ((2 ^ jointMu s : ℕ) : ℝ) ≤ s := by exact_mod_cast two_pow_jointMu_le (by omega)
  push_cast at hm ⊢
  have hg2 : 1 ≤ gbar ^ 2 := by nlinarith
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have h1 := mul_le_mul hM hm (by positivity) (by positivity)
  have h2 := mul_le_mul_of_nonneg_right hg2 hs0
  linarith

/-- **`g = √M`** for the hard family at the parameters (lines 3845-3846, 3876): the mass
`B = 2` equals `√M ‖x(T)‖`, since `‖x(T)‖ = 2/√M` on every input. -/
theorem jointFamilyAt_g {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε)
    (x : Promised (jointM gbar) (jointN τ) (2 ^ jointMu s)) :
    (jointFamilyAt s τ gbar h.s_ge h.tau_ge).mass =
      Real.sqrt (jointM gbar) * ‖jointSol (jointM gbar) (jointN τ) (jointMu s) s τ x τ‖ := by
  have hM : 1 ≤ jointM gbar := by have := four_le_jointM h.gbar_ge; omega
  have hpos : 0 < Real.sqrt (jointM gbar) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  rw [norm_jointSol_T (jointN_time (by linarith [h.tau_ge])) x,
    show (jointFamilyAt s τ gbar h.s_ge h.tau_ge).mass = 2 from jointFamily_mass hM]
  field_simp

/-- `β = jointCorr ε ≥ 31/48` for `ε ≤ 1/64` (lines 3889-3894). -/
theorem jointCorr_ge {ε : ℝ} (hε : ε ≤ 1 / 64) : 31 / 48 ≤ jointCorr ε := corr_ge hε

/-- **The constant `c_J = 1/400`** (lines 3895-3897): on `JointRange`,
`ḡ √s τ / 400 ≤ β² n √(M m) / 16` (`ODE/Parameters.joint_numeric`). -/
theorem joint_bound_le {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) :
    jointConst * gbar * Real.sqrt s * τ ≤
      jointCorr ε ^ 2 * jointN τ * Real.sqrt ((jointM gbar : ℝ) * 2 ^ jointMu s) / 16 :=
  joint_numeric h.tau_ge h.gbar_ge (jointCorr_ge h.eps_le)

/-- **Theorem `odel:thm:joint`** (lines 3860-3905): for `s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`,
`0 < ε ≤ 1/64`, the joint family is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`;
`D = 0` is `jointFamily_skew`, `g = √M ∈ [ḡ/√2, ḡ]` is `jointFamilyAt_g` and
`joint_instance_props`) and forces `ḡ √s τ / 400` matrix queries (explicit constant
`c_J = 1/400`, `jointConst`), both value queries and total count. -/
theorem joint_witness {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) :
    (jointFamilyAt s τ gbar h.s_ge h.tau_ge).Witnesses τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  have hb := joint_bound_le h
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  refine ⟨jointFamily_inClass (sqrt_jointM_le (by linarith [h.gbar_ge])), jointFamily_T, ?_⟩
  intro ι _ G _ _ _ A
  have hf := joint_forces (s := s) (by omega) (even_jointM gbar) (one_le_jointN h.tau_ge)
    (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega))
    (jointN_time (by linarith [h.tau_ge])) (by linarith [h.eps_le]) ι G A
  exact ⟨hb.trans hf.1, hb.trans hf.2⟩

end

end SparseLowerBounds.ODE
end
