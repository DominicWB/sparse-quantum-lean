import DeferredMeasurementLowerBounds.Model.Measured
import SparseLinearSystems.Protocol.Tree
import DeferredMeasurementLowerBounds.Helpers.TreeContainment.Steps

set_option autoImplicit false

/-!
# The adaptive protocols of the package are measured algorithms

The adaptive protocol model of the package, `SparseLinearSystems.Protocol.Tree` (a classical
tree of fresh measured runs followed by a bounded fresh-trial protocol
`ODERepeatProtocol.Protocol`), is contained in the measured model `Measured` **for
finite-dimensional workspaces**, with the same success mass, heralded output, conditional output
and worst-case cost (`ofTree`). The restriction comes from the resets: an instrument has finitely
many outcomes, and a reset of an infinite-dimensional workspace to a fixed vector needs infinitely
many Kraus operators. The deferral of measured algorithms itself works in every dimension.

The translation uses only instruments:

* a known unitary is a one-outcome instrument (`unitaryStep`), so a program becomes a chain of
  unitaries and calls (`ofProgram`; `seq p q` runs `q` first);
* a reset of the workspace to a unit vector `ψ` is the instrument with Kraus operators
  `|ψ⟩⟨b_i|` for an orthonormal basis `b` of a finite-dimensional workspace (`reset`); a fresh run
  or a fresh trial starts with it;
* the two-outcome flag or herald measurement of an isometry `F` is the instrument
  `{F F†, 1 - F F†}` (`heraldKraus`);
* a uniformly random trial label is the instrument with the `c` Kraus operators `c^{-1/2} 1`
  (`coinKraus`).

The equalities need unitary oracle labels (the fresh-run failure probabilities of the tree model
are `1 - p`) and unit initial vectors; the workspace is finite-dimensional for the reset.
-/

namespace DeferredMeasurementLowerBounds.Model

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit SparseLinearSystems.Protocol
open scoped InnerProduct

variable {K E F X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {O : L → X → K →L[ℂ] K}

/-! ### Unitaries, programs, resets, heralds and coins -/

/-- A one-outcome instrument with a unitary Kraus operator is complete. -/
theorem unitaryStep_complete {U : K →L[ℂ] K} (hU : IsUnitary U) :
    ∑ j : Fin 1, ((fun _ : Fin 1 => U) j)† ∘L (fun _ : Fin 1 => U) j = 1 := by
  have h := hU.1
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] at h
  simpa only [Finset.univ_unique, Finset.sum_singleton] using h

/-- A known unitary, as a one-outcome instrument. -/
def unitaryStep (U : K →L[ℂ] K) (hU : IsUnitary U) (next : Measured O E) : Measured O E :=
  .instrument 1 (fun _ => U) (unitaryStep_complete hU) (fun _ => next)

/-- A program as a chain of known unitaries and calls before `next` (`seq p q` runs `q` first). -/
def ofProgram : MultiOracleCircuit.Program O → Measured O E → Measured O E
  | .fixed U hU, next => unitaryStep U hU next
  | .query l, next => .call l false next
  | .queryAdjoint l, next => .call l true next
  | .seq p q, next => ofProgram q (ofProgram p next)

/-- The reset Kraus operators `|ψ⟩⟨b_i|` for the standard orthonormal basis `b`. -/
def resetKraus [FiniteDimensional ℂ K] (ψ : K) : Fin (Module.finrank ℂ K) → K →L[ℂ] K :=
  fun i => (innerSL ℂ (stdOrthonormalBasis ℂ K i)).smulRight ψ

/-- The reset to a unit vector is a complete instrument. -/
theorem resetKraus_complete [FiniteDimensional ℂ K] {ψ : K} (hψ : ‖ψ‖ = 1) :
    ∑ i, (resetKraus ψ i)† ∘L resetKraus ψ i = 1 := by
  ext v
  apply ext_inner_left ℂ
  intro u
  rw [_root_.sum_apply, inner_sum, one_apply_eq_self]
  have hterm : ∀ i, inner ℂ u (((resetKraus ψ i)† ∘L resetKraus ψ i) v) =
      inner ℂ u (stdOrthonormalBasis ℂ K i) * inner ℂ (stdOrthonormalBasis ℂ K i) v := by
    intro i
    rw [ContinuousLinearMap.comp_apply, adjoint_inner_right]
    simp only [resetKraus, smulRight_apply, innerSL_apply_apply, inner_smul_left,
      inner_smul_right, inner_self_eq_norm_sq_to_K, hψ, inner_conj_symm]
    simp
    ring
  simp only [hterm]
  exact OrthonormalBasis.sum_inner_mul_inner _ u v

/-- **Reset** of the workspace to the unit vector `ψ` (the old state is discarded). -/
def reset [FiniteDimensional ℂ K] (ψ : K) (hψ : ‖ψ‖ = 1) (next : Measured O E) :
    Measured O E :=
  .instrument _ (resetKraus ψ) (resetKraus_complete hψ) (fun _ => next)

/-- The two-outcome herald of an isometry `G`: success `G G†`
(`ODEHeraldedSuccess.successProjector`), failure `1 - G G†`. -/
def heraldKraus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : H →L[ℂ] K) : Fin 2 → K →L[ℂ] K :=
  fun j => if j = 0 then ODEHeraldedSuccess.successProjector G
    else 1 - ODEHeraldedSuccess.successProjector G

/-- The herald of an isometry is a complete instrument. -/
theorem heraldKraus_complete {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {G : H →L[ℂ] K} (hG : G† ∘L G = 1) :
    ∑ j, (heraldKraus G j)† ∘L heraldKraus G j = 1 := by
  have hP := ODEHeraldedSuccess.successProjector_isOrthogonalProjection G hG
  rw [Fin.sum_univ_two]
  simp only [heraldKraus, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, if_true]
  rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.mul_def, star_sub, star_one, hP.1,
    sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hP.2]
  abel

/-- A uniformly random label among `c` values: Kraus operators `c^{-1/2} 1`. -/
def coinKraus (c : ℕ) : Fin c → K →L[ℂ] K :=
  fun _ => ((Real.sqrt c)⁻¹ : ℂ) • (1 : K →L[ℂ] K)

/-- A coin with at least one outcome is a complete instrument. -/
theorem coinKraus_complete {c : ℕ} (hc : 0 < c) :
    ∑ j, (coinKraus (K := K) c j)† ∘L coinKraus c j = 1 := by
  have hterm : ∀ j : Fin c, (coinKraus (K := K) c j)† ∘L coinKraus c j =
      ((c : ℂ)⁻¹) • (1 : K →L[ℂ] K) := by
    intro j
    rw [← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def]
    simp only [coinKraus, star_smul, star_one, smul_mul_smul, mul_one]
    congr 1
    rw [Complex.star_def, map_inv₀, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg c), Complex.ofReal_natCast]
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc', one_smul]

/-! ### The translation of protocols and trees -/

/-- A fresh-trial protocol as a measured algorithm: draw the trial label, reset to the seed,
run the trial circuit, herald; on success output, on failure continue. -/
def ofProtocol [FiniteDimensional ℂ K] : ODERepeatProtocol.Protocol O E → Measured O E
  | .abort => .reject
  | .freshTrial t k =>
      .instrument t.choices (coinKraus t.choices) (coinKraus_complete t.choices_pos) fun j =>
        reset t.seed t.seed_unit (ofProgram (t.circuit j)
          (.instrument 2 (heraldKraus t.output) (heraldKraus_complete t.output_isometry)
            fun i => if i = 0 then .output t.output t.output_isometry else ofProtocol k))

/-- **An adaptive protocol as a measured algorithm** on a finite-dimensional workspace: every
fresh run resets the workspace to its seed, runs its circuit and measures its flag; the outcome
selects the subtree. -/
def ofTree [FiniteDimensional ℂ K] : Tree O F E → Measured O E
  | .final p => ofProtocol p
  | .test t s f =>
      reset t.seed t.seed_unit (ofProgram t.circuit
        (.instrument 2 (heraldKraus t.flag) (heraldKraus_complete t.flag_isometry)
          fun i => if i = 0 then ofTree s else ofTree f))

/-! ### Semantics of the translation -/

/-- A program chain applies the program before its continuation. -/
theorem successDensity_ofProgram (p : MultiOracleCircuit.Program O) (next : Measured O E)
    (x : X) (φ : K) :
    (ofProgram p next).successDensity x φ = next.successDensity x (p.eval x φ) := by
  induction p generalizing next φ with
  | fixed U hU => simp [ofProgram, unitaryStep, Measured.successDensity]
  | query l => simp [ofProgram, Measured.successDensity, queryOp]
  | queryAdjoint l => simp [ofProgram, Measured.successDensity, queryOp]
  | seq p q ihp ihq =>
    rw [ofProgram, ihq, ihp, MultiOracleCircuit.Program.eval_seq, mul_apply_eq_comp]

/-- The success mass of a program chain. -/
theorem successMass_ofProgram (p : MultiOracleCircuit.Program O) (next : Measured O E)
    (x : X) (φ : K) :
    (ofProgram p next).successMass x φ = next.successMass x (p.eval x φ) := by
  induction p generalizing next φ with
  | fixed U hU => simp [ofProgram, unitaryStep, Measured.successMass]
  | query l => simp [ofProgram, Measured.successMass, queryOp]
  | queryAdjoint l => simp [ofProgram, Measured.successMass, queryOp]
  | seq p q ihp ihq =>
    rw [ofProgram, ihq, ihp, MultiOracleCircuit.Program.eval_seq, mul_apply_eq_comp]

/-- A program chain costs the program's cost plus the continuation's. -/
theorem worstCost_ofProgram (p : MultiOracleCircuit.Program O) (next : Measured O E)
    (w : L → ℕ) : (ofProgram p next).worstCost w = p.cost w + next.worstCost w := by
  induction p generalizing next with
  | fixed U hU => simp [ofProgram, unitaryStep, Measured.worstCost]
  | query l => simp [ofProgram, Measured.worstCost]
  | queryAdjoint l => simp [ofProgram, Measured.worstCost]
  | seq p q ihp ihq =>
    rw [ofProgram, ihq, ihp, MultiOracleCircuit.Program.cost_seq]
    omega

/-- After a reset only the squared norm of the old state remains. -/
theorem successDensity_reset [FiniteDimensional ℂ K] (ψ : K) (hψ : ‖ψ‖ = 1)
    (next : Measured O E) (x : X) (φ : K) :
    (reset ψ hψ next).successDensity x φ = ((‖φ‖ ^ 2 : ℝ) : ℂ) • next.successDensity x ψ := by
  have hk : ∀ i, resetKraus ψ i φ = inner ℂ (stdOrthonormalBasis ℂ K i) φ • ψ := by
    intro i
    simp only [resetKraus, smulRight_apply, innerSL_apply_apply]
  simp only [reset, Measured.successDensity, hk, Measured.successDensity_smul]
  rw [← OrthonormalBasis.sum_sq_norm_inner_right (stdOrthonormalBasis ℂ K) φ,
    Complex.ofReal_sum, Finset.sum_smul]

/-- The success mass after a reset. -/
theorem successMass_reset [FiniteDimensional ℂ K] (ψ : K) (hψ : ‖ψ‖ = 1)
    (next : Measured O E) (x : X) (φ : K) :
    (reset ψ hψ next).successMass x φ = ‖φ‖ ^ 2 * next.successMass x ψ := by
  have hk : ∀ i, resetKraus ψ i φ = inner ℂ (stdOrthonormalBasis ℂ K i) φ • ψ := by
    intro i
    simp only [resetKraus, smulRight_apply, innerSL_apply_apply]
  simp only [reset, Measured.successMass, hk, Measured.successMass_smul]
  rw [← OrthonormalBasis.sum_sq_norm_inner_right (stdOrthonormalBasis ℂ K) φ, Finset.sum_mul]

/-- A reset is free. -/
theorem worstCost_reset [FiniteDimensional ℂ K] (ψ : K) (hψ : ‖ψ‖ = 1)
    (next : Measured O E) (w : L → ℕ) : (reset ψ hψ next).worstCost w = next.worstCost w := by
  have hne : ψ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hψ
    exact zero_ne_one hψ
  haveI : Nontrivial K := nontrivial_of_ne ψ 0 hne
  haveI : Nonempty (Fin (Module.finrank ℂ K)) := Fin.pos_iff_nonempty.mp Module.finrank_pos
  simp only [reset, Measured.worstCost]
  exact Finset.sup_const Finset.univ_nonempty _

/-! ### One-step rules and scaled semantics of the translation -/

/-- The heralded output after the herald of an isometry `G`. -/
theorem successDensity_herald {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : H →L[ℂ] K) (hG : G† ∘L G = 1) (s f : Measured O E) (x : X) (v : K) :
    (Measured.instrument 2 (heraldKraus G) (heraldKraus_complete hG)
        fun i => if i = 0 then s else f).successDensity x v =
      s.successDensity x (G ((G†) v)) + f.successDensity x (v - G ((G†) v)) := by
  rw [successDensity_instrument, Fin.sum_univ_two]
  simp [heraldKraus, ODEHeraldedSuccess.successProjector]

/-- The success mass after the herald of an isometry `G`. -/
theorem successMass_herald {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : H →L[ℂ] K) (hG : G† ∘L G = 1) (s f : Measured O E) (x : X) (v : K) :
    (Measured.instrument 2 (heraldKraus G) (heraldKraus_complete hG)
        fun i => if i = 0 then s else f).successMass x v =
      s.successMass x (G ((G†) v)) + f.successMass x (v - G ((G†) v)) := by
  rw [successMass_instrument, Fin.sum_univ_two]
  simp [heraldKraus, ODEHeraldedSuccess.successProjector]

/-- The worst-case cost of the herald of an isometry: the larger of the two continuations. -/
theorem worstCost_herald {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (G : H →L[ℂ] K) (hG : G† ∘L G = 1) (s f : Measured O E) (w : L → ℕ) :
    (Measured.instrument 2 (heraldKraus G) (heraldKraus_complete hG)
        fun i => if i = 0 then s else f).worstCost w = max (s.worstCost w) (f.worstCost w) := by
  rw [worstCost_instrument, show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide,
    Finset.sup_insert, Finset.sup_singleton]
  simp

omit [CompleteSpace K] in
/-- The squared norm of a coin branch. -/
theorem norm_sq_coinKraus {c : ℕ} (hc : 0 < c) (j : Fin c) (φ : K) :
    ‖coinKraus (K := K) c j φ‖ ^ 2 = ‖φ‖ ^ 2 / c := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc'
  simp only [coinKraus, _root_.smul_apply, one_apply_eq_self,
    norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, mul_pow, inv_pow,
    Real.sq_sqrt hc'.le]
  ring

/-- **Scaled heralded output of a protocol**: for every initial vector `φ`, the translation of a
fresh-trial protocol outputs `‖φ‖²` times the heralded output of the protocol. -/
theorem successDensity_ofProtocol [FiniteDimensional ℂ K] (hO : ∀ l x, IsUnitary (O l x))
    (p : ODERepeatProtocol.Protocol O E) (x : X) (φ : K) :
    (ofProtocol p).successDensity x φ = ((‖φ‖ ^ 2 : ℝ) : ℂ) • p.successDensity x := by
  induction p generalizing φ with
  | abort =>
    simp [ofProtocol, Measured.successDensity, ODERepeatProtocol.Protocol.successDensity]
  | freshTrial t k ih =>
    have hdec : ∀ w : K, (t.output†) (t.output ((t.output†) w)) = (t.output†) w :=
      fun w => congrArg (fun A : E →L[ℂ] E => A ((t.output†) w)) t.output_isometry
    have hfail : ∀ j, ‖(t.circuit j).eval x t.seed - t.output ((t.output†)
        ((t.circuit j).eval x t.seed))‖ ^ 2 = 1 - t.probability x j := fun j =>
      (herald_norms t.output t.output_isometry (norm_eval_seed hO (t.circuit j) x t.seed_unit)).2
    rw [ofProtocol, successDensity_instrument]
    simp only [successDensity_reset, successDensity_ofProgram,
      successDensity_herald t.output t.output_isometry, ih,
      norm_sq_coinKraus t.choices_pos, successDensity_output, hdec, hfail]
    rw [ODERepeatProtocol.Protocol.successDensity, t.oneTrialDensity_eq_kraus,
      ← t.failureChoiceWeight_sum, Complex.ofReal_sum, Finset.sum_smul, Finset.smul_sum,
      ← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_add, smul_smul, ODERepeatProtocol.TrialFamily.amplitude]
    congr 1 <;> congr 1 <;> push_cast <;> ring

/-- **Scaled success mass of a protocol**, for every initial vector. -/
theorem successMass_ofProtocol [FiniteDimensional ℂ K] (hO : ∀ l x, IsUnitary (O l x))
    (p : ODERepeatProtocol.Protocol O E) (x : X) (φ : K) :
    (ofProtocol p).successMass x φ = ‖φ‖ ^ 2 * p.successMass x := by
  induction p generalizing φ with
  | abort =>
    simp [ofProtocol, Measured.successMass, ODERepeatProtocol.Protocol.successMass,
      ODERepeatProtocol.Protocol.failureMass]
  | freshTrial t k ih =>
    have hdec : ∀ w : K, (t.output†) (t.output ((t.output†) w)) = (t.output†) w :=
      fun w => congrArg (fun A : E →L[ℂ] E => A ((t.output†) w)) t.output_isometry
    have hfail : ∀ j, ‖(t.circuit j).eval x t.seed - t.output ((t.output†)
        ((t.circuit j).eval x t.seed))‖ ^ 2 = 1 - t.probability x j := fun j =>
      (herald_norms t.output t.output_isometry (norm_eval_seed hO (t.circuit j) x t.seed_unit)).2
    rw [ofProtocol, successMass_instrument]
    simp only [successMass_reset, successMass_ofProgram,
      successMass_herald t.output t.output_isometry, ih,
      norm_sq_coinKraus t.choices_pos, successMass_output, hdec, hfail]
    rw [ODERepeatProtocol.Protocol.freshTrial_successMass_eq, ← t.failureChoiceWeight_sum,
      ODERepeatProtocol.TrialFamily.meanSuccess, Finset.sum_div, Finset.sum_mul,
      ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ODERepeatProtocol.TrialFamily.probability, ODERepeatProtocol.TrialFamily.amplitude]
    ring

/-- The worst-case cost of the translation of a protocol. -/
theorem worstCost_ofProtocol [FiniteDimensional ℂ K] (p : ODERepeatProtocol.Protocol O E)
    (w : L → ℕ) : (ofProtocol p).worstCost w = p.worstCost w := by
  induction p with
  | abort => rfl
  | freshTrial t k ih =>
    rw [ofProtocol, worstCost_instrument]
    simp only [worstCost_reset, worstCost_ofProgram,
      worstCost_herald t.output t.output_isometry, ih, worstCost_output, Nat.zero_max]
    rw [finsetSup_add_const _ (Finset.univ_nonempty_iff.mpr ⟨⟨0, t.choices_pos⟩⟩)]
    rfl

/-- **Scaled heralded output of an adaptive protocol**, for every initial vector `φ`. -/
theorem successDensity_ofTree_smul [FiniteDimensional ℂ K] (hO : ∀ l x, IsUnitary (O l x))
    (T : Tree O F E) (x : X) (φ : K) :
    (ofTree T).successDensity x φ = ((‖φ‖ ^ 2 : ℝ) : ℂ) • T.successDensity x := by
  induction T generalizing φ with
  | final p => exact successDensity_ofProtocol hO p x φ
  | test t s f ihs ihf =>
    have hn := herald_norms t.flag t.flag_isometry (norm_eval_seed hO t.circuit x t.seed_unit)
    rw [ofTree, successDensity_reset, successDensity_ofProgram,
      successDensity_herald t.flag t.flag_isometry, ihs, ihf,
      hn.1, hn.2, tree_successDensity_test]
    rfl

/-- **Scaled success mass of an adaptive protocol**, for every initial vector `φ`. -/
theorem successMass_ofTree_smul [FiniteDimensional ℂ K] (hO : ∀ l x, IsUnitary (O l x))
    (T : Tree O F E) (x : X) (φ : K) :
    (ofTree T).successMass x φ = ‖φ‖ ^ 2 * T.successMass x := by
  induction T generalizing φ with
  | final p => exact successMass_ofProtocol hO p x φ
  | test t s f ihs ihf =>
    have hn := herald_norms t.flag t.flag_isometry (norm_eval_seed hO t.circuit x t.seed_unit)
    rw [ofTree, successMass_reset, successMass_ofProgram,
      successMass_herald t.flag t.flag_isometry, ihs, ihf,
      hn.1, hn.2, tree_successMass_test]
    rfl

/-- **Containment, success mass** (the adaptive algorithms of the lower bounds `hsl:thm:main`,
`qlsl:thm:main` and `odel:thm:combined`, protocols of Theorem `qls:thm:main`): on a
finite-dimensional workspace, for unitary labels and a unit initial vector, the measured
translation of an adaptive protocol heralds success with the protocol's probability. -/
theorem successMass_ofTree [FiniteDimensional ℂ K] (hO : ∀ l x, IsUnitary (O l x))
    (T : Tree O F E) (x : X) {φ : K} (hφ : ‖φ‖ = 1) :
    (ofTree T).successMass x φ = T.successMass x := by
  rw [successMass_ofTree_smul hO, hφ, one_pow, one_mul]

/-- **Containment, heralded output**, on a finite-dimensional workspace. -/
theorem successDensity_ofTree [FiniteDimensional ℂ K] (hO : ∀ l x, IsUnitary (O l x))
    (T : Tree O F E) (x : X) {φ : K} (hφ : ‖φ‖ = 1) :
    (ofTree T).successDensity x φ = T.successDensity x := by
  rw [successDensity_ofTree_smul hO, hφ, one_pow, Complex.ofReal_one, one_smul]

/-- **Containment, conditional output**, on a finite-dimensional workspace. -/
theorem conditionalDensity_ofTree [FiniteDimensional ℂ K] (hO : ∀ l x, IsUnitary (O l x))
    (T : Tree O F E) (x : X) {φ : K} (hφ : ‖φ‖ = 1) :
    (ofTree T).conditionalDensity x φ = T.conditionalDensity x := by
  rw [Measured.conditionalDensity, Tree.conditionalDensity, successMass_ofTree hO T x hφ,
    successDensity_ofTree hO T x hφ]

/-- **Containment, cost** (the adaptive algorithms of the lower bounds `hsl:thm:main`,
`qlsl:thm:main` and `odel:thm:combined`), on a finite-dimensional workspace: the same worst-case
weighted cost over all transcripts. -/
theorem worstCost_ofTree [FiniteDimensional ℂ K] (T : Tree O F E) (w : L → ℕ) :
    (ofTree T).worstCost w = T.worstCost w := by
  induction T with
  | final p => exact worstCost_ofProtocol p w
  | test t s f ihs ihf =>
    rw [ofTree, worstCost_reset, worstCost_ofProgram,
      worstCost_herald t.flag t.flag_isometry, ihs, ihf]
    rfl

/-- A protocol that succeeds with positive probability on some input has a unit vector in its
workspace (a seed). -/
theorem exists_unit_of_successMass_pos (T : Tree O F E) (x : X) (h : 0 < T.successMass x) :
    ∃ φ : K, ‖φ‖ = 1 := by
  cases T with
  | test t s f => exact ⟨t.seed, t.seed_unit⟩
  | final p =>
    cases p with
    | abort =>
      exfalso
      have h0 : (Tree.final (F := F) (ODERepeatProtocol.Protocol.abort (O := O)
          (E := E))).successMass x = 0 := by
        simp [Tree.successMass, Tree.expect, ODERepeatProtocol.Protocol.successMass,
          ODERepeatProtocol.Protocol.failureMass]
      linarith
    | freshTrial t k => exact ⟨t.seed, t.seed_unit⟩

end

end DeferredMeasurementLowerBounds.Model
