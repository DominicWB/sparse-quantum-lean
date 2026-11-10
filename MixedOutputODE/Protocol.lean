import MixedOutputODE.Interface
import GeneralODE.Solver.Protocol

/-!
# The complete protocol for a mixed-output solver

Fix a history encoding `H` and a program `qP` whose two selected blocks
approximate `A(x)/α` and `I`. From the hypothesis `MixedBlockSolver f q₀` we
obtain one protocol, chosen before the input. The solver is compiled to the
native oracles and the two sources exactly as in the pure-output case
(`GeneralODE.Solver.composed`); its work register `W` is retained and the
final-copy decoder acts as `V ⊗ 1` (`tensorLeft`). The damped randomized
amplification of the released construction is applied to the joint event
"solver herald and final copy" with the actual selected vector as its own
target, so it preserves that vector exactly; four attempts give success
probability at least `175/256`. Discarding the work register (`ptrace`) then
leaves the selected reduced state.

The solver accuracy is `mixedDelta g ε = ε/(4096 g²)`. The selection estimate
(`selection`) bounds the actual selection probability below and the
trace distance of the reduced selected state by `2δ/(p - 2δ)`, where
`p ≥ θ²` is the ideal selection probability of the history solution; the
history accuracy contributes `ε/4` (`GeneralODE.Solver.system`). In every
history the protocol makes at most
`40 (5g/√q₀) f(κ, ε/(4096 g²)) · 3 K · count(qP)` calls of the matrix oracles
and `40 (5g/√q₀) · 3 f(κ, ε/(4096 g²))` calls of each source
(`exists_mixed_protocol_of_block`).
-/

namespace SparseHamiltonian.MixedOutputODE

noncomputable section
open ContinuousLinearMap OracleCircuit ODEMixedOutput ODEStateNormalization GeneralODE
  GeneralODE.Solver GeneralODE.Registers GeneralODE.History GeneralODE.Implemented
open scoped InnerProduct BigOperators ComplexConjugate Nat
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- The guarantee of a protocol whose output carries a retained work
register: success at least `175/256`, and after the work register is
discarded, a density operator within trace distance `η` of the target. -/
structure MixedOutcome {X K L' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {O' : L' → X → K →L[ℂ] K} {n W : Type*} [Fintype n] [Fintype W]
    [DecidableEq W] (prot : ODERepeatProtocol.Protocol O' (EuclideanSpace ℂ (n × W))) (x : X)
    (target : EuclideanSpace ℂ n) (η : ℝ) : Prop where
  success_lower : (175 : ℝ) / 256 ≤ prot.successMass x
  success_two_thirds : (2 : ℝ) / 3 ≤ prot.successMass x
  output_density : IsDensity (ptrace (prot.conditionalDensity x))
  conditional_error :
    ∃ h : (ptrace (prot.conditionalDensity x) -
        pureOperator (unitDirection target)).toLinearMap.IsSymmetric,
      hermitianTraceDistance (ptrace (prot.conditionalDensity x))
        (pureOperator (unitDirection target)) h ≤ η

variable {n PB X L : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]

/-- **The protocol for a fixed block-encoding program and a mixed-output
solver.** -/
theorem exists_mixed_protocol_of_block (f : ℝ → ℝ → ℝ) (q₀ : ℝ)
    (hsolver : MixedBlockSolver f q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (H : HistData n PB)
    (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (hO : ∀ l x, IsUnitary (O l x))
    (img : L → X → PB)
    (hvalid : ∀ l x, O l x (EuclideanSpace.single H.pb0 1) = EuclideanSpace.single (img l x) 1)
    (qP : MultiOracleCircuit.Program O) (Agen : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1)
    (Λ T Cbar g ε α δU ε0 r₀ rb : ℝ)
    (hc : H.c = taylorCoef (α * (T / H.m))) (hd : H.d = phiCoef (α * (T / H.m))) (hN : H.N = 7)
    (hm : 1 ≤ H.m) (hT : 0 < T) (hα : 0 < α) (hαT : α * T ≤ H.m) (hΛT : 8 * Λ * T ≤ H.m)
    (hA : ∀ x, ‖Agen x‖ ≤ Λ)
    (hUerr : ∀ x, ‖selBlock H.Ein H.Eout (qP.eval x) true - ((α⁻¹ : ℝ) : ℂ) • Agen x‖ ≤ δU)
    (h0err : ∀ x, ‖selBlock H.Ein H.Eout (qP.eval x) false - 1‖ ≤ ε0)
    (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hR1 : H.m * (H.K * ε0) ≤ Plan.budget Cbar g ε) (hR2 : H.m * δU ≤ Plan.budget Cbar g ε)
    (hR3 : H.m * ((Λ * (T / H.m)) ^ (H.K + 1) / ((H.K + 1) ! : ℝ)) ≤ Plan.budget Cbar g ε)
    (hr : 0 < (T / Real.sqrt H.m) ^ 2 * rb ^ 2 + r₀ ^ 2) :
    ∃ (w : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (prot : ODERepeatProtocol.Protocol
        (Amplify.liftOracle (NativeMaskedProgram.oracle (ι := Fin w) (totalOracle H O J₀ Jb)))
        (EuclideanSpace ℂ (n × W))),
      (prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          40 * Plan.gain g q₀ * (f (7 * kappaH H.m 2 (Real.exp 1) (2 * Cbar)) (mixedDelta g ε) *
            (3 * ((H.K : ℝ) * (qP.count : ℝ)))) ∧
      (∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          40 * Plan.gain g q₀ *
            (3 * f (7 * kappaH H.m 2 (Real.exp 1) (2 * Cbar)) (mixedDelta g ε))) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = unitDirection v) → (b ≠ 0 → Jb x seed = unitDirection b) →
        (∀ t, 0 ≤ t → t ≤ T → ‖NormedSpace.exp (t • Agen x)‖ ≤ Cbar) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖ODEConstantForcing.solution (Agen x) v b t‖ ≤
            g * ‖ODEConstantForcing.solution (Agen x) v b T‖) →
        ODEConstantForcing.solution (Agen x) v b T ≠ 0 →
        MixedOutcome prot x (ODEConstantForcing.solution (Agen x) v b T) ε := by
  set κ := 7 * kappaH H.m 2 (Real.exp 1) (2 * Cbar) with hκdef
  -- the solver
  obtain ⟨w, w₀, ctrl, W, hWf, hWd, S, out, hout', hScount, hsolve⟩ := hsolver H.Sys H.Anc
    H.clean (sourceSeed (n := n) H.m seed) (sourceSeed_norm seed hseed) κ (mixedDelta g ε)
    (one_le_seven_kappaH H.m Cbar hC) (mixedDelta_pos hg hε) (mixedDelta_le hg hε hε1)
  -- the composed program, its seed and decoder
  set μ : ℝ := T / Real.sqrt H.m with hμ
  set p := composed H O J₀ Jb hm qP μ r₀ rb hr ctrl S with hp
  set Jin := (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).toContinuousLinearMap
    with hJindef
  have hJin : Jin† ∘L Jin = 1 :=
    (NativeMaskedOracle.input (ι := Fin w) (refBasis H hm)).adjoint_comp_self
  set ψ := Jin (initial w₀ (embed H.clean (sourceSeed (n := n) H.m seed))) with hψdef
  have hψ : ‖ψ‖ = 1 := by
    rw [hψdef, hJindef, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map,
      norm_initial, (embed (s := H.Sys) H.clean).norm_map_iff_adjoint_comp_self.mpr
        (embed_isometry H.clean)]
    exact sourceSeed_norm seed hseed
  set Dc := Decode.decoder (n := n) H.m with hDcdef
  have hDc : Dc† ∘L Dc = 1 := Decode.decoder_isometry _ hm
  set Fo := Jin ∘L out ∘L tensorLeft (W := W) Dc with hFodef
  have hFo : Fo† ∘L Fo = 1 :=
    isometry_comp _ _ hJin (isometry_comp _ _ hout' (tensorLeft_isometry Dc hDc))
  have hg' : 1 ≤ Plan.gain g q₀ := Plan.one_le_gain hg hq₀ hq₀1
  have hSnn : (0 : ℝ) ≤ f κ (mixedDelta g ε) := (Nat.cast_nonneg _).trans hScount
  have hg0 : 0 ≤ 40 * Plan.gain g q₀ := by linarith
  refine ⟨w, W, hWf, hWd, Amplify.protocol p Fo hFo ψ hψ (Plan.gain g q₀) hg', ?_, ?_, ?_⟩
  · -- matrix queries
    have h1 := Amplify.protocol_worstCost p Fo hFo ψ hψ (Plan.gain g q₀) hg'
      (ODESourceQueryBudget.matrixWeight (fun _ => 1))
    have h2 := composed_matrix_cost H O J₀ Jb hm qP μ r₀ rb hr ctrl S (fun _ => 1)
    rw [MultiOracleCircuit.Program.cost_const, mul_one] at h2
    have h2' : (p.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        (S.count : ℝ) * (3 * ((H.K : ℝ) * (qP.count : ℝ))) := by
      exact_mod_cast h2
    have h3 : (S.count : ℝ) * (3 * ((H.K : ℝ) * (qP.count : ℝ))) ≤
        f κ (mixedDelta g ε) * (3 * ((H.K : ℝ) * (qP.count : ℝ))) :=
      mul_le_mul_of_nonneg_right hScount (by positivity)
    exact h1.trans (mul_le_mul_of_nonneg_left (h2'.trans h3) hg0)
  · -- source queries
    intro b'
    have h1 := Amplify.protocol_worstCost p Fo hFo ψ hψ (Plan.gain g q₀) hg'
      (ODESourceQueryBudget.sourceWeight b')
    have h2 := composed_source_cost H O J₀ Jb hm qP μ r₀ rb hr ctrl S b'
    have h2' : (p.cost (ODESourceQueryBudget.sourceWeight b') : ℝ) ≤ (S.count : ℝ) * 3 := by
      exact_mod_cast h2
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hg0)
    linarith
  · -- correctness on every valid input
    intro x v b hv hb hJv hJbv hCx hgx hne
    have hq : IsUnitary (qP.eval x) := qP.eval_unitary hO x
    set r := Real.sqrt (μ ^ 2 * rb ^ 2 + r₀ ^ 2) with hrdef
    have hr0 : 0 < r := Real.sqrt_pos.mpr hr
    have hϑ : 210 * Cbar * g * Plan.budget Cbar g ε < 1 := by
      rw [Plan.budget_mul hC hg]
      linarith
    obtain ⟨y, hMy, hκM, hy0, hθy, hdiry⟩ := system H (qP.eval x) hq (Agen x) v b Λ T Cbar g α
      δU ε0 (Plan.budget Cbar g ε) hc hd hm hT hα hαT hΛT (hA x) (hUerr x) (h0err x)
      hC hCx hg hgx (Plan.budget_pos hC hg hε).le hϑ hR1 hR2 hR3 hne r hr0
    rw [hN] at hκM
    -- the solver's guarantee
    have hU : (solverInput H O J₀ Jb qP μ r₀ rb hr x).1 = H.unitary (qP.eval x) :=
      uProgram_eval H J₀ Jb qP x
    have hB : (solverInput H O J₀ Jb qP μ r₀ rb hr x).2 =
        (prepProgram (m := H.m) (a := H.Anc) J₀ Jb μ r₀ rb hr).eval x :=
      bProgram_eval H O J₀ Jb μ r₀ rb hr x
    obtain ⟨hUu, hBu⟩ := solverInput_unitary H O J₀ Jb qP μ r₀ rb hr hO hJ₀ hJb x
    have hβ : ‖(r⁻¹ : ℝ) • rhsVector (n := n) H.m μ v b‖ = 1 := by
      rw [norm_smul, norm_rhsVector μ v b (by positivity), hv, hb, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr0)]
      exact inv_mul_cancel₀ hr0.ne'
    have hBβ : (solverInput H O J₀ Jb qP μ r₀ rb hr x).2
        (embed H.clean (sourceSeed (n := n) H.m seed)) =
        embed H.clean ((r⁻¹ : ℝ) • rhsVector (n := n) H.m μ v b) := by
      rw [hB]
      exact prepProgram_eval J₀ Jb μ r₀ rb hr seed v b x hv hb hJv hJbv H.clean
    have hκU : ∀ u, ‖u‖ ≤ κ *
        ‖block (s := H.Sys) H.clean (solverInput H O J₀ Jb qP μ r₀ rb hr x).1 u‖ := by
      rw [hU]
      exact hκM
    have hyβ : block (s := H.Sys) H.clean (solverInput H O J₀ Jb qP μ r₀ rb hr x).1 y =
        (r⁻¹ : ℝ) • rhsVector (n := n) H.m μ v b := by
      rw [hU]
      exact hMy
    obtain ⟨hq₀z, hsym, hTD⟩ := hsolve _ _ hUu hBu _ y hβ hBβ hκU hyβ
    generalize hzdef : (out†) (S.eval (solverInput H O J₀ Jb qP μ r₀ rb hr x)
      (initial w₀ (embed H.clean (sourceSeed (n := n) H.m seed)))) = z at hq₀z hsym hTD
    -- the ideal selection probability
    set yhat := unitDirection y with hyhat
    have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    have hDy : (Dc†) yhat = ((‖y‖⁻¹ : ℝ) : ℂ) • (Dc†) y := by
      rw [hyhat, unitDirection, ← Complex.coe_smul, map_smul]
    have hpsel : Plan.theta g ε ^ 2 ≤ ‖(Dc†) yhat‖ ^ 2 := by
      have hθ' : Plan.theta g ε * ‖y‖ ≤ ‖(Dc†) y‖ := by
        have : Plan.theta g ε = (1 - 210 * Cbar * g * Plan.budget Cbar g ε) / (8 * g) := by
          rw [Plan.budget_mul hC hg]
          rfl
        rw [this]
        exact hθy
      have hθ0 : 0 < Plan.theta g ε := Plan.theta_pos hg hε1
      have hnorm : ‖(Dc†) yhat‖ = ‖y‖⁻¹ * ‖(Dc†) y‖ := by
        rw [hDy, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyn)]
      have hlow : Plan.theta g ε ≤ ‖(Dc†) yhat‖ := by
        rw [hnorm, ← div_eq_inv_mul, le_div_iff₀ hyn]
        exact hθ'
      exact pow_le_pow_left₀ hθ0.le hlow 2
    have hp2 := mixed_select hg hε hε1 hpsel
    -- the solver output is nonzero
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hq₀z
      norm_num at hq₀z
      linarith
    -- selection from the mixed output
    obtain ⟨hsel_amp, hsym', hsel_TD⟩ := selection (W := W) z hz0 yhat Dc hDc (mixedDelta g ε)
      hsym hTD hp2
    generalize hddef : ((tensorLeft (W := W) Dc)†) z = d at hsel_amp hsym' hsel_TD
    -- the decoded output of the composed program
    have hdecoded : (Fo†) (p.eval x ψ) = d := by
      have hc' := composed_eval H O J₀ Jb hm qP μ r₀ rb hr img hvalid hO hJ₀ hJb ctrl S x
      rw [← hp, ← hJindef] at hc'
      have hc'' := congrArg (fun T' => T' (initial w₀ (embed H.clean
        (sourceSeed (n := n) H.m seed)))) hc'
      simp only [comp_apply] at hc''
      have hJJ : ∀ u, (Jin†) (Jin u) = u := fun u => by
        have := congrArg (fun T' => T' u) hJin
        simpa using this
      rw [hψdef, hc'', hFodef, adjoint_comp, adjoint_comp, comp_apply, comp_apply, hJJ, hzdef,
        hddef]
    -- the amplitude handed to the amplification
    have hamp : 1 / (2 * Plan.gain g q₀) ≤ ‖(Fo†) (p.eval x ψ)‖ := by
      rw [hdecoded]
      have h1 : Real.sqrt q₀ ≤ ‖z‖ := by
        have := Real.sqrt_le_sqrt hq₀z
        rwa [Real.sqrt_sq (norm_nonneg _)] at this
      have hgap : 0 ≤ ‖(Dc†) yhat‖ ^ 2 - 2 * mixedDelta g ε := by linarith
      have h2 : Real.sqrt (‖(Dc†) yhat‖ ^ 2 - 2 * mixedDelta g ε) * ‖z‖ ≤ ‖d‖ := by
        have hsq := Real.sqrt_le_sqrt hsel_amp
        rw [Real.sqrt_mul hgap, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
          at hsq
        exact hsq
      have h3 := mixed_amplitude hg hε hε1 hq₀ hpsel
      calc
        1 / (2 * Plan.gain g q₀) ≤
            Real.sqrt q₀ * Real.sqrt (‖(Dc†) yhat‖ ^ 2 - 2 * mixedDelta g ε) := h3
        _ ≤ ‖z‖ * Real.sqrt (‖(Dc†) yhat‖ ^ 2 - 2 * mixedDelta g ε) :=
          mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ = Real.sqrt (‖(Dc†) yhat‖ ^ 2 - 2 * mixedDelta g ε) * ‖z‖ := mul_comm _ _
        _ ≤ ‖d‖ := h2
    have hd0 : d ≠ 0 := by
      intro h0
      have : ‖(Fo†) (p.eval x ψ)‖ = 0 := by rw [hdecoded, h0, norm_zero]
      have hgp : 0 < 2 * Plan.gain g q₀ := by linarith
      have : 0 < 1 / (2 * Plan.gain g q₀) := by positivity
      linarith
    -- the amplification, with the actual selected vector as its own target
    have hOt : ∀ l y', IsUnitary
        (NativeMaskedProgram.oracle (ι := Fin w) (totalOracle H O J₀ Jb) l y') :=
      fun l y' => NativeMaskedOracle.oracle_unitary _
        (totalOracle_unitary H O J₀ Jb hO hJ₀ hJb l) y'
    have hself : ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((Fo†) (p.eval x ψ)) - unitDirection d‖ ≤ 0 :=
      ⟨1, norm_one, by rw [one_smul, hdecoded, sub_self, norm_zero]⟩
    have hout := Amplify.outcome p hOt Fo hFo ψ hψ (Plan.gain g q₀) hg' x d hd0 0 hamp hself
    obtain ⟨hsym0, hTD0⟩ := hout.conditional_error
    have hρ : (Amplify.protocol p Fo hFo ψ hψ (Plan.gain g q₀) hg').conditionalDensity x =
        pureOperator (unitDirection d) :=
      eq_of_hermitianTraceDistance_le_zero _ _ hsym0 hTD0
    -- the reduced selected state
    have hdirx : ‖unitDirection ((Dc†) yhat) -
        unitDirection (ODEConstantForcing.solution (Agen x) v b T)‖ ≤ 2 * (ε / 8) := by
      have heq : unitDirection ((Dc†) yhat) = unitDirection ((Dc†) y) := by
        rw [hDy, Complex.coe_smul]
        exact Decode.unitDirection_real_smul _ (inv_pos.mpr hyn) _
      rw [heq, ← Plan.budget_mul hC hg]
      exact hdiry
    have hDy0 : (Dc†) yhat ≠ 0 := by
      intro h0
      have : Plan.theta g ε ^ 2 ≤ 0 := by rw [h0, norm_zero] at hpsel; simpa using hpsel
      have := Plan.theta_pos hg hε1
      nlinarith
    have hxT0 : ODEConstantForcing.solution (Agen x) v b T ≠ 0 := hne
    refine
      { success_lower := hout.success_lower
        success_two_thirds := hout.success_two_thirds
        output_density := ?_
        conditional_error := ?_ }
    · rw [hρ]
      exact ptrace_isDensity (pureOperator_isDensity _ (unitDirection_norm d hd0))
    · rw [hρ]
      have hpure : (pureOperator (unitDirection ((Dc†) yhat)) -
          pureOperator (unitDirection (ODEConstantForcing.solution (Agen x) v b T))).toLinearMap.IsSymmetric :=
        pure_sub_isSymmetric _ _
      have hall : (ptrace (pureOperator (unitDirection d)) -
          pureOperator (unitDirection (ODEConstantForcing.solution (Agen x) v b T))).toLinearMap.IsSymmetric :=
        (ptrace_isPositive (pureOperator_positive _)).isSymmetric.sub
          (pureOperator_positive _).isSymmetric
      refine ⟨hall, ?_⟩
      have htri := hermitianTraceDistance_triangle _ _ _ hsym' hpure hall
      have hpd := hermitianTraceDistance_pure_le _ _ (unitDirection_norm _ hDy0)
        (unitDirection_norm _ hxT0) hpure
      have herr := mixed_error hg hε hε1 hpsel
      linarith

end

end SparseHamiltonian.MixedOutputODE
