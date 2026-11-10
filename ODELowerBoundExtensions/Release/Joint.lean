import ODELowerBoundExtensions.Release.Adversary
import AdaptiveHamiltonianLowerBound.Readout

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:joint` for retry protocols

Manuscript: Theorem `odel:thm:joint` and its proof, for the release's retry protocols. As in
`SparseLowerBounds/ODE/JointTheorem`, with the same constants:

* `joint_general_retry` (`joint_general` for protocols): any labelled family whose labels are
  implemented with costs `w` by membership programs (`EncodedOracle.ImplementsOn` with the phase
  oracle `x ↦ P.phase (membership x)`); a retry protocol with success mass at least `2/3` and
  conditional output `ε`-accurate for `jointTarget` (`2ε ≤ 1`) has worst-case cost at least
  `β² n √(M 2^μ) / 8`, `β = jointCorr ε = (2/3)(1 - 2ε)`. Route: the heralded correlation
  `AdaptiveHamiltonianLowerBound.tree_correlation` of `Tree.final p` with the half observable
  `halfObs` (proof of Theorem `odel:thm:joint`, ideal value `halfSign(a_*)` by
  `inner_halfObs_jointTarget`), then `retry_decision_count_ge` (`Release/Adversary`) with the outer
  adversary of Lemma `odel:lem:outer` (`outerGamma`, `outer_schurCert`,
  `outerDeg_le_sum_outerGamma`, `halfSign_oddCand_of_outerGamma_ne_zero`) and the arithmetic
  `outer_arith`, as in `outer_count_ge`.
* `joint_forces_retry` (`joint_forces`): the joint family retry-forces `β² n √(M 2^μ) / 16` value
  queries, with the membership certificate `implementsOn_joint` and Boolean cost `hardCost`
  (two per value query, so `worstCost hardCost = 2 · worstCost valueWeight`).
* `joint_witness_retry` (`joint_witness`): on `JointRange`, the joint family at the parameters is in
  the class and retry-forces `c_J ḡ √s τ`, `c_J = 1/400` (`joint_bound_le`).
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open LinearSystemLowerBound (corr)
open scoped InnerProduct InnerProductSpace

-- The nested time-addressed workspaces exceed the default instance size (as in `JointTheorem`).
set_option synthInstance.maxSize 1024

/-- **Lemma `odel:lem:outer` for retry protocols** (`outer_count_ge` for protocols, Section
`odel:sec:main`): a retry protocol over any labelled family implemented with costs `w` by membership
programs, whose heralded output has signed correlation at least `β ≥ 0` with the half answer
`halfSign M (oddCand x)`, measured by a contraction `A`, has worst-case cost at least
`β² n √(M m) / 8`. -/
theorem outer_count_ge_retry {M n m : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hme : Even m) {W B L E : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    (P : ProjFamily B (Fin M × Fin n × Fin m)) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    (O : L → Promised M n m → W →L[ℂ] W) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (p : ODERepeatProtocol.Protocol O E) (A : E →L[ℂ] E) (hA : ‖A‖ ≤ 1) {β : ℝ} (hβ : 0 ≤ β)
    (hcorr : ∀ x, β ≤ halfSign M (oddCand x) * corr A (p.successDensity x)) :
    β ^ 2 * n * Real.sqrt ((M : ℝ) * m) / 8 ≤ p.worstCost w := by
  haveI : Nonempty (Promised M n m) := nonempty_promised (by omega) hn hm
  have hcount := retry_decision_count_ge P membership outerGamma outerGamma_nonneg
    outerGamma_symm outerLam_nonneg (outer_schurCert hM hMe hm hme)
    (outerDeg_le_sum_outerGamma hMe hme) (fun x => halfSign M (oddCand x))
    (fun x => abs_halfSign _) halfSign_oddCand_of_outerGamma_ne_zero Enc hEnc hO w hw p A hA
    hβ hcorr
  unfold outerDeg outerLam at hcount
  rw [Nat.cast_mul] at hcount
  have hM2 : (1 : ℝ) ≤ ((M / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ M / 2)
  have hm2 : (1 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m / 2)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hMr : (M : ℝ) = 2 * ((M / 2 : ℕ) : ℝ) := by
    obtain ⟨r, hr⟩ := hMe
    exact_mod_cast (by omega : M = 2 * (M / 2))
  have hmr : (m : ℝ) = 2 * ((m / 2 : ℕ) : ℝ) := by
    obtain ⟨r, hr⟩ := hme
    exact_mod_cast (by omega : m = 2 * (m / 2))
  have hsa := Real.sq_sqrt (show (0 : ℝ) ≤ ((M / 2 : ℕ) : ℝ) by positivity)
  have hsb := Real.sq_sqrt (show (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) by positivity)
  have hpa : 0 < Real.sqrt ((M / 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hpb : 0 < Real.sqrt ((m / 2 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt ((M : ℝ) * m) =
      2 * Real.sqrt ((M / 2 : ℕ) : ℝ) * Real.sqrt ((m / 2 : ℕ) : ℝ) := by
    rw [show (M : ℝ) * m = (2 * Real.sqrt ((M / 2 : ℕ) : ℝ) * Real.sqrt ((m / 2 : ℕ) : ℝ)) ^ 2 by
      rw [mul_pow, mul_pow, hsa, hsb, hMr, hmr]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hsq]
  exact outer_arith hsa hsb (by positivity) hcount

/-- **Theorem `odel:thm:joint` for retry protocols, general form**: a retry protocol over any
labelled family implemented with costs `w` by membership programs, with success mass at least
`2/3` and conditional output `ε`-accurate for `x(T)/‖x(T)‖ = jointTarget` (`2ε ≤ 1`), has worst-case
cost at least `β² n √(M 2^μ) / 8`, `β = jointCorr ε`. -/
theorem joint_general_retry {M n μ s : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n)
    (hμ : 1 ≤ μ) {ε : ℝ} (hε : 2 * ε ≤ 1) {W B L E G : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (P : ProjFamily B (Fin M × Fin n × Fin (2 ^ μ))) (Enc : W →L[ℂ] B) (hEnc : Enc† ∘L Enc = 1)
    (O : L → Promised M n (2 ^ μ) → W →L[ℂ] W) (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (fun x => P.phase (membership x)) (O l) Enc (w l))
    (p : ODERepeatProtocol.Protocol O E) (e : E →L[ℂ] SysGarb (JointIndex M μ s) G)
    (he : e† ∘L e = 1) (hsucc : ∀ x, 2 / 3 ≤ p.successMass x)
    (hacc : ∀ x, DensityAccurate e (p.conditionalDensity x) (jointTarget M n μ s x) ε) :
    jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 8 ≤ p.worstCost w := by
  have hm := two_le_two_pow hμ
  have hβ : 0 ≤ jointCorr ε := by unfold jointCorr; linarith
  -- Proof of Theorem `odel:thm:joint`: heralded half measurement, correlation `β` with `halfSign(a_*)`.
  have key : ∀ x, jointCorr ε ≤ halfSign M (oddCand x) *
      corr (Readout.outObs e (halfObs M μ s)) (p.successDensity x) := fun x =>
    AdaptiveHamiltonianLowerBound.tree_correlation (F := E) e
      (SparseLinearSystems.Protocol.Tree.final p) x (jointTarget M n μ s x) ε (hacc x)
      (hsucc x) (halfObs M μ s) halfObs_isSelfAdjoint norm_halfObs_le
      (σ := halfSign M (oddCand x)) (a₀ := 1) (abs_halfSign (oddCand x)).le
      (by rw [inner_halfObs_jointTarget]; nlinarith [halfSign_sq (oddCand x)]) (by linarith)
  have h := outer_count_ge_retry hM hMe hn hm (even_two_pow hμ) P Enc hEnc O hO w hw p
    (Readout.outObs e (halfObs M μ s)) ((Readout.norm_outObs_le e he _).trans norm_halfObs_le)
    hβ key
  push_cast at h
  exact h

/-- **Theorem `odel:thm:joint` for retry protocols, native form** (`joint_forces`): the joint
family retry-forces `β² n √(M 2^μ) / 16` value queries (and as many queries in total). -/
theorem joint_forces_retry {M n μ s : ℕ} (hM : 2 ≤ M) (hMe : Even M) (hn : 1 ≤ n)
    (hμ : 1 ≤ μ) (hμs : 2 ^ μ ≤ s) {T : ℝ} (hT : (n : ℝ) * (Real.pi / 2) + 1 ≤ T) {ε : ℝ}
    (hε : 2 * ε ≤ 1) :
    RetryForces (jointFamily M n μ s hμ hμs T hT) ε
      (jointCorr ε ^ 2 * n * Real.sqrt ((M : ℝ) * 2 ^ μ) / 16) := by
  intro ι _ E G _ _ _ _ _ _ _ A
  have h := joint_general_retry (s := s) hM hMe hn hμ hε (jointBoolean ι M n μ s)
    (ancillaEmbed _) ancillaEmbed_isometry ((jointFamily M n μ s hμ hμs T hT).access ι)
    (Family.access_unitary ι _) hardCost (implementsOn_joint ι hμ hμs T hT) A.prot A.readout
    A.readout_isometry A.success fun x => by
      have hx := A.accurate x _ (jointSol_solves x)
      rwa [jointFamily_T, unitDirection_jointSol_T hT] at hx
  have hhc : hardCost = fun q => 2 * AdaptiveHamiltonianLowerBound.Access.valueWeight q := by
    funext q; cases q <;> rfl
  rw [hhc, worstCost_mul] at h
  have hle : A.prot.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight ≤
      A.prot.worstCost (fun _ => 1) :=
    worstCost_mono _ fun q => by cases q <;> decide
  have hle' : (A.prot.worstCost AdaptiveHamiltonianLowerBound.Access.valueWeight : ℝ) ≤
      A.prot.worstCost (fun _ => 1) := by exact_mod_cast hle
  push_cast at h
  constructor <;> linarith

/-- **Theorem `odel:thm:joint` for retry protocols** (`joint_witness`): for `s ≥ 4`, `τ ≥ 4`,
`ḡ ≥ 2`, `0 < ε ≤ 1/64`, the joint family at the parameters is in the class and retry-forces
`ḡ √s τ / 400` queries (`c_J = jointConst = 1/400`). -/
theorem joint_witness_retry {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) :
    RetryWitnesses (jointFamilyAt s τ gbar h.s_ge h.tau_ge) τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  have hb := joint_bound_le h
  have hs := h.s_ge
  have hM := four_le_jointM h.gbar_ge
  refine ⟨jointFamily_inClass (sqrt_jointM_le (by linarith [h.gbar_ge])), jointFamily_T, ?_⟩
  intro ι _ E G _ _ _ _ _ _ _ A
  have hf := joint_forces_retry (s := s) (by omega) (even_jointM gbar)
    (one_le_jointN h.tau_ge) (one_le_jointMu (by omega)) (two_pow_jointMu_le (by omega))
    (jointN_time (by linarith [h.tau_ge])) (by linarith [h.eps_le]) ι E G A
  exact ⟨hb.trans hf.1, hb.trans hf.2⟩

end

end ODELowerBoundExtensions.Release
