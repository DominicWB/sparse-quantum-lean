import GeneralODE.Solver.Compose
import GeneralODE.Solver.System
import GeneralODE.Solver.Amplify
import GeneralODE.Plan

/-!
# The complete protocol for a fixed block-encoding program

Fix a history encoding `H` and a program `qP` over some unitary oracle family
`O` whose two selected blocks approximate `A(x)/α` and `I` for every input
`x`.  From the hypothesis `BlockSolver f q₀` we obtain one protocol, chosen
before the input: the solver with `κ = 7 κ_H(m, 2, e, 2C̄)` and
`δ = ε/(40 g)`, compiled to the oracles `O` and the two sources, decoded at
the final copies, damped and amplified with gain `5 g / √q₀`, and repeated at
most four times.  In every history it makes at most
`40 (5g/√q₀) f(κ,δ) · 3 K · count(qP)` calls of `O` and
`40 (5g/√q₀) · 3 f(κ,δ)` calls of each source; on every valid input its
success probability is at least `175/256` and its conditional output is
within trace distance `ε` of `x(T)/‖x(T)‖`.
-/

namespace SparseHamiltonian.GeneralODE.Solver

noncomputable section
open ContinuousLinearMap OracleCircuit Registers History Implemented ODEStateNormalization
open scoped InnerProduct BigOperators ComplexConjugate Nat
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

variable {n PB X L : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]

theorem one_le_seven_kappaH (m : ℕ) (Cbar : ℝ) (hC : 1 ≤ Cbar) :
    1 ≤ 7 * kappaH m 2 (Real.exp 1) (2 * Cbar) := by
  unfold kappaH
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : 0 ≤ 2 * Cbar * (2 * (m : ℝ) + 1) * (2 + 2 ^ 2 * Real.exp 1) := by positivity
  linarith

/-- **The protocol for a fixed block-encoding program.** -/
theorem exists_protocol_of_block (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (hsolver : BlockSolver f q₀)
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
    ∃ (w : ℕ) (prot : ODERepeatProtocol.Protocol
        (Amplify.liftOracle (NativeMaskedProgram.oracle (ι := Fin w) (totalOracle H O J₀ Jb)))
        (EuclideanSpace ℂ n)),
      (prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          40 * Plan.gain g q₀ * (f (7 * kappaH H.m 2 (Real.exp 1) (2 * Cbar)) (Plan.delta g ε) *
            (3 * ((H.K : ℝ) * (qP.count : ℝ)))) ∧
      (∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          40 * Plan.gain g q₀ * (3 * f (7 * kappaH H.m 2 (Real.exp 1) (2 * Cbar)) (Plan.delta g ε))) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = unitDirection v) → (b ≠ 0 → Jb x seed = unitDirection b) →
        (∀ t, 0 ≤ t → t ≤ T → ‖NormedSpace.exp (t • Agen x)‖ ≤ Cbar) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖ODEConstantForcing.solution (Agen x) v b t‖ ≤
            g * ‖ODEConstantForcing.solution (Agen x) v b T‖) →
        ODEConstantForcing.solution (Agen x) v b T ≠ 0 →
        Amplify.Outcome prot x (ODEConstantForcing.solution (Agen x) v b T) ε := by
  set κ := 7 * kappaH H.m 2 (Real.exp 1) (2 * Cbar) with hκdef
  -- the solver
  obtain ⟨w, w₀, ctrl, S, out, hout', hScount, hsolve⟩ := hsolver H.Sys H.Anc H.clean
    (sourceSeed (n := n) H.m seed) (sourceSeed_norm seed hseed) κ (Plan.delta g ε)
    (one_le_seven_kappaH H.m Cbar hC) (Plan.delta_pos hg hε) (Plan.delta_le hg hε hε1)
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
  set Fo := Jin ∘L out ∘L Decode.decoder (n := n) H.m with hFodef
  have hFo : Fo† ∘L Fo = 1 :=
    isometry_comp _ _ hJin (isometry_comp _ _ hout' (Decode.decoder_isometry _ hm))
  have hg' : 1 ≤ Plan.gain g q₀ := Plan.one_le_gain hg hq₀ hq₀1
  have hSnn : (0 : ℝ) ≤ f κ (Plan.delta g ε) := (Nat.cast_nonneg _).trans hScount
  have hg0 : 0 ≤ 40 * Plan.gain g q₀ := by linarith
  refine ⟨w, Amplify.protocol p Fo hFo ψ hψ (Plan.gain g q₀) hg', ?_, ?_, ?_⟩
  · -- matrix queries
    have h1 := Amplify.protocol_worstCost p Fo hFo ψ hψ (Plan.gain g q₀) hg'
      (ODESourceQueryBudget.matrixWeight (fun _ => 1))
    have h2 := composed_matrix_cost H O J₀ Jb hm qP μ r₀ rb hr ctrl S (fun _ => 1)
    rw [MultiOracleCircuit.Program.cost_const, mul_one] at h2
    have h2' : (p.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        (S.count : ℝ) * (3 * ((H.K : ℝ) * (qP.count : ℝ))) := by
      exact_mod_cast h2
    have h3 : (S.count : ℝ) * (3 * ((H.K : ℝ) * (qP.count : ℝ))) ≤
        f κ (Plan.delta g ε) * (3 * ((H.K : ℝ) * (qP.count : ℝ))) :=
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
    obtain ⟨hq₀z, ω, hω, hz⟩ := hsolve _ _ hUu hBu _ y hβ hBβ hκU hyβ
    -- decoding the final copies
    set z := (out†) (S.eval (solverInput H O J₀ Jb qP μ r₀ rb hr x)
      (initial w₀ (embed H.clean (sourceSeed (n := n) H.m seed)))) with hzdef
    have hθy' : Plan.theta g ε * ‖y‖ ≤ ‖((Decode.decoder (n := n) H.m)†) y‖ := by
      have : Plan.theta g ε = (1 - 210 * Cbar * g * Plan.budget Cbar g ε) / (8 * g) := by
        rw [Plan.budget_mul hC hg]
        rfl
      rw [this]
      exact hθy
    obtain ⟨hzamp, hzdir⟩ := Decode.decode (Decode.decoder (n := n) H.m)
      (Decode.decoder_isometry _ hm) y z hy0 (Plan.theta g ε) (Plan.delta g ε)
      (Plan.theta_pos hg hε1) hθy' (Plan.delta_lt_theta hg hε hε1) ω hω hz
    -- the decoded output of the composed program
    have hdecoded : (Fo†) (p.eval x ψ) = ((Decode.decoder (n := n) H.m)†) z := by
      have hc := composed_eval H O J₀ Jb hm qP μ r₀ rb hr img hvalid hO hJ₀ hJb ctrl S x
      rw [← hp, ← hJindef] at hc
      have hc' := congrArg (fun T' => T' (initial w₀ (embed H.clean
        (sourceSeed (n := n) H.m seed)))) hc
      simp only [comp_apply] at hc'
      have hJJ : ∀ u, (Jin†) (Jin u) = u := fun u => by
        have := congrArg (fun T' => T' u) hJin
        simpa using this
      rw [hψdef, hc', hFodef, adjoint_comp, adjoint_comp, comp_apply, comp_apply, hJJ, hzdef]
    have hamp : 1 / (2 * Plan.gain g q₀) ≤ ‖(Fo†) (p.eval x ψ)‖ := by
      rw [hdecoded]
      have h1 : Real.sqrt q₀ ≤ ‖z‖ := by
        have := Real.sqrt_le_sqrt hq₀z
        rwa [Real.sqrt_sq (norm_nonneg _)] at this
      have h2 := Plan.amplitude_bound hg hε hε1 hq₀
      have h3 : 0 ≤ Plan.theta g ε - Plan.delta g ε := by
        have := Plan.delta_lt_theta hg hε hε1
        linarith
      calc 1 / (2 * Plan.gain g q₀) ≤ Real.sqrt q₀ * (Plan.theta g ε - Plan.delta g ε) := h2
        _ ≤ ‖z‖ * (Plan.theta g ε - Plan.delta g ε) := mul_le_mul_of_nonneg_right h1 h3
        _ ≤ _ := hzamp
    have hdir : ∃ ω' : ℂ, ‖ω'‖ = 1 ∧
        ‖ω' • unitDirection ((Fo†) (p.eval x ψ)) -
          unitDirection (ODEConstantForcing.solution (Agen x) v b T)‖ ≤ ε := by
      refine ⟨ω, hω, ?_⟩
      rw [hdecoded]
      calc _ ≤ ‖ω • unitDirection (((Decode.decoder (n := n) H.m)†) z) -
              unitDirection (((Decode.decoder (n := n) H.m)†) y)‖ +
            ‖unitDirection (((Decode.decoder (n := n) H.m)†) y) -
              unitDirection (ODEConstantForcing.solution (Agen x) v b T)‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * Plan.delta g ε / Plan.theta g ε + 2 * (210 * Cbar * g * Plan.budget Cbar g ε) :=
            add_le_add hzdir hdiry
        _ = 2 * Plan.delta g ε / Plan.theta g ε + 2 * (ε / 8) := by rw [Plan.budget_mul hC hg]
        _ ≤ ε := Plan.direction_bound hg hε hε1
    have hOt : ∀ l y', IsUnitary
        (NativeMaskedProgram.oracle (ι := Fin w) (totalOracle H O J₀ Jb) l y') :=
      fun l y' => NativeMaskedOracle.oracle_unitary _
        (totalOracle_unitary H O J₀ Jb hO hJ₀ hJb l) y'
    exact Amplify.outcome p hOt Fo hFo ψ hψ (Plan.gain g q₀) hg' x _ hne ε hamp hdir

end

end SparseHamiltonian.GeneralODE.Solver
