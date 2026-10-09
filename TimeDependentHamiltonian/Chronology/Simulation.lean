import TimeDependentHamiltonian.Chronology.Colligation
import SparseHamiltonian.SharpClockQuery

/-!
# Amplified simulation with a slot-dependent chronological clock

The released smoothing LCU, coherent reuse and oblivious amplification are
generic in the four blocks of a unitary colligation. Applied to the
slot-dependent transducer they give an isometric implementation whose full
output is within `2 δ` of the clean output embedding applied to the ordered
product `U (T-1) ⋯ U 0` of the local Cayley steps (`exists_precise_implementationV`).

Each synchronized reuse layer is the released oracle-independent coupling
network followed by one active parallel slot action (`layerV_factor`). A
clean implementation of every active slot action at cost `q` therefore yields
an oracle program with at most `6 d q` queries, where `d` is the filter degree
(`implementationV_query_certificate`); the number of time slots does not
multiply the query count.
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap OracleCircuit LabeledEncodedOracle
open SparseHamiltonian.ChronologicalResolvent SparseHamiltonian.ChronologicalCatalyst
open SparseHamiltonian.GlobalColligation SparseHamiltonian.GlobalResolvent
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The amplified implementation of the slot-dependent chronological clock,
including every private and branch register. -/
def implementationV (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) :=
  AmplifiedSmoothing.implementation (SharpFilterSchedule.length Q)
    (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)
    (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (exitV D J (CayleyTransfer.c w) (CayleyTransfer.sigma w) T)
    (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J) ((CayleyTransfer.c w : ℂ) • 1) T)
    (privateV D J (CayleyTransfer.c w) (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) T)

/-- Energy conservation in the block order used by the smoothing compiler. -/
theorem step_energy (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) (hD : ∀ k, (D k)† ∘L D k = 1)
    (w : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4) (T : ℕ) (p : P)
    (v : BlockOperator.H T V) :
    ‖(((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T) p +
        exitV D J (CayleyTransfer.c w) (CayleyTransfer.sigma w) T v‖ ^ 2 +
      ‖privateV D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
          (CayleyTransfer.sigma w) T v +
        stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
          ((CayleyTransfer.c w : ℂ) • 1) T p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
  obtain ⟨_hκ, _hκUpper, hκc, hσc, _hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  have h := colligation_energy D J hJ hD (CayleyTransfer.c w) (CayleyTransfer.kappa w)
    (CayleyTransfer.sigma w) hκc hσc T p v
  rwa [add_comm (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
    ((CayleyTransfer.c w : ℂ) • 1) T p)] at h

set_option maxRecDepth 4096 in
/-- Clock promises at every sampled time give an isometric amplified
implementation whose complete output is within `2 δ` of the ordered product
of the local Cayley steps, with the sharp filter degree. -/
theorem exists_precise_implementationV
    (D R1 : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (H : ℕ → P →L[ℂ] P)
    (w Q b qbar : ℝ) (T : ℕ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : ∀ k, (D k)† ∘L D k = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ k, (1 - D k) ∘L R1 k = 1) (hLeft : ∀ k, R1 k ∘L (1 - D k) = 1)
    (hR1 : ∀ k, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k, J† ∘L R1 k ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k, ‖R1 k ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    ∃ (U R : ℕ → P →L[ℂ] P),
      (∀ k, CayleyTransfer.cayleyDenominator w (H k) ∘L R k = 1) ∧
      (∀ k, R k ∘L CayleyTransfer.cayleyDenominator w (H k) = 1) ∧
      (∀ k, U k = CayleyTransfer.cayleyNumerator w (H k) ∘L R k) ∧
      (implementationV D J w Q qbar T δ)† ∘L implementationV D J w Q qbar T δ = 1 ∧
      ‖implementationV D J w Q qbar T δ -
        SharpClockSimulation.output (P := P) (V := V) w Q qbar T δ ∘L evolution U T‖ ≤
          2 * δ ∧
      (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ : ℝ) ≤
        128 * ((T : ℝ) * w * qbar + Q * (1 + Real.log (1 / δ))) := by
  let c := CayleyTransfer.c w
  let κ := CayleyTransfer.kappa w
  let σ := CayleyTransfer.sigma w
  have hQpos : 0 < Q := by linarith
  obtain ⟨hκ, hκUpper, hκc, hσc, hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  have hcat := fun k => exists_local_catalyst (D k) (R1 k) J (H k) c κ σ w Q b qbar
    hQpos hw hκ hκUpper hκc hσc hσw (hD k) hJ (hRight k) (hLeft k) (hR1 k) (hBoundary k)
    (hSelf k) (hH k) (hEndpoint k) hbq hqQ
  choose Γ U hLocalPrivate hLocalPublic hUNorm hΓ using hcat
  have hcay := fun k => local_public_is_cayley (D k) (R1 k) J (Γ k) (H k) (U k) w hw
    hwQuarter (hRight k) (hLeft k) hJ (hBoundary k) (hSelf k) (hH k) (hLocalPrivate k)
    (hLocalPublic k)
  choose R hRRight hRLeft hCayley using hcay
  have hUnit := fun k => local_public_unitary (D k) (R1 k) J (Γ k) (H k) (U k) w hw
    hwQuarter (hRight k) (hLeft k) hJ (hBoundary k) (hSelf k) (hH k) (hLocalPrivate k)
    (hLocalPublic k)
  have hEvol := evolution_unitary U (fun k => (hUnit k).1) (fun k => (hUnit k).2) T
  have hPublic := colligation_public D J c σ Γ U hLocalPublic T
  have hPrivate := colligation_private D J c κ σ Γ U hLocalPrivate hLocalPublic T
  have hStep := step_energy D J hJ hD w hw hwQuarter T
  have hExit := exitV_identity D J hJ hD c κ σ hκc hσc Γ U hLocalPrivate hLocalPublic T
    hEvol.2
  have hf := filter_precisionV D R1 J H c κ σ w Q b qbar T hQ hw hκ hκUpper hκc hσc hσw
    hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δ hδ hδOne
  have hb : 0 ≤ b := (norm_nonneg _).trans (hEndpoint 0)
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ (T : ℝ) * w * qbar := by positivity
  have hNorm : ‖evolution U T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    rw [evolution_norm U hUNorm, one_mul]
  have hCost : ‖stackedV Γ U T‖ ^ 2 ≤ 3 * ((T : ℝ) * w * qbar) := by
    have h := stackedV_norm_sq_le Γ U hUNorm ((144 / 49 : ℝ) * w * qbar) hΓ T
    have hle : (T : ℝ) * ((144 / 49 : ℝ) * w * qbar) ≤ 3 * ((T : ℝ) * w * qbar) := by
      nlinarith
    linarith
  have hContract := privateV_norm_le_one D J hJ hD c κ σ hκc hσc T
  have hResidual : ‖smoothedTransducerResidual (evolution U T) (stackedV Γ U T)
      (averagedGeometricFilter (privateV D J c κ σ T) (SharpFilterSchedule.length Q) ^
        SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)
      (privateV D J c κ σ T) (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ)‖ ≤ δ := by
    apply smoothedTransducerResidual_norm_le_filter (W := 3 * ((T : ℝ) * w * qbar))
      (evolution U T) (stackedV Γ U T) _ (privateV D J c κ σ T) hNorm hContract hCost
      (SharpFilterSchedule.degree_pos Q _ δ hQ) _ hf.1
    have hdegree := hf.2.1
    nlinarith
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hd : 0 < SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ *
      (SharpFilterSchedule.length Q - 1) := SharpFilterSchedule.degree_pos Q _ δ hQ
  refine ⟨U, R, hRRight, hRLeft, hCayley, ?_, ?_, hf.2.2⟩
  · exact AmplifiedSmoothing.implementation_isometry (SharpFilterSchedule.length Q)
      (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ) hL hd _ _ _ _ hStep
  · exact AmplifiedSmoothing.implementation_error (SharpFilterSchedule.length Q)
      (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ) hL hd _ (evolution U T) _ _
      (stackedV Γ U T) _ hStep hPublic hPrivate hExit hEvol.1 hEvol.2 δ hδ.le hδOne
      hResidual

/-! ### Layers and queries -/

/-- Only unfinished branches run the parallel slot action. -/
def activeClockV (D : ℕ → V →L[ℂ] V) (T d r : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V) d) :=
  ReuseLayerFactorization.activeQuery (slotAction D T) d r

/-- One complete synchronized layer of the slot-dependent clock reuse. -/
def layerV (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) (r : ℕ) :
    SharpClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ]
      SharpClockQuery.Space (P := P) (V := V) w Q qbar T δ :=
  ReuseQuery.reuseLayer
    (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (exitV D J (CayleyTransfer.c w) (CayleyTransfer.sigma w) T)
    (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J) ((CayleyTransfer.c w : ℂ) • 1) T)
    (privateV D J (CayleyTransfer.c w) (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) T)
    (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r

/-- Each layer is the released oracle-independent coupling network followed
by one active parallel slot action. -/
theorem layerV_factor (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (w Q qbar : ℝ) (T : ℕ)
    (δ : ℝ) (r : ℕ) :
    layerV D J w Q qbar T δ r =
      ReuseLayerFactorization.couplingLayer J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r ∘L
      activeClockV D T (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r :=
  ReuseLayerFactorization.reuseLayer_factor _ _ _ _ (slotAction D T) _ r

variable {Label K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The fixed coupling adds no queries to an encoded active slot action. -/
theorem layerV_implementsOn [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (r q : ℕ) (O : Label → X → K →L[ℂ] K)
    (E : SharpClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ] K)
    (hE : E† ∘L E = 1)
    (hQuery : ImplementsOn O (fun x => activeClockV (P := P) (D x) T
      (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r) E q) :
    ImplementsOn O (fun x => layerV (D x) J w Q qbar T δ r) E q := by
  obtain ⟨_hκ, _hκUpper, hκc, hσc, _hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  have hFixed := ImplementsOn.fixed (O := O) hE
    (ReuseLayerFactorization.couplingLayer J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r)
    (ReuseLayerFactorization.couplingLayer_unitary J hJ _ _ _ hκc hσc T _ r)
  have h := (hFixed.mul hQuery).congr (fun x => (layerV_factor (D x) J w Q qbar T δ r).symm)
  simpa only [Nat.zero_add] using h

/-- Clean implementations of every active slot action compose into the
amplified slot-dependent clock on prepared vectors of the physical workspace. -/
theorem implementationV_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → ℕ → V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : ∀ x k, (D x k)† ∘L D x k = 1) (hJ : J† ∘L J = 1)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ,
      ImplementsOn O (fun x => activeClockV (P := P) (D x) T
        (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ * q ∧
      ∀ x, p.eval x ∘L (E ∘L SharpClockQuery.input (P := P) (V := V) w Q qbar T δ) =
        E ∘L implementationV (D x) J w Q qbar T δ := by
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  exact LabeledEncodedAmplification.implementation_query_certificate
    (SharpFilterSchedule.length Q) (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)
    hL (SharpFilterSchedule.degree_pos Q _ δ hQ) O hO E hE
    (fun _ => ((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (fun x => exitV (D x) J (CayleyTransfer.c w) (CayleyTransfer.sigma w) T)
    (fun _ => stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
      ((CayleyTransfer.c w : ℂ) • 1) T)
    (fun x => privateV (D x) J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T)
    (fun x => step_energy (D x) J hJ (hD x) w hw hwQuarter T) q
    (fun r hr => layerV_implementsOn D J hJ w Q qbar T δ hw hwQuarter r q O E hE
      (hQuery r hr))

end

end SparseHamiltonian.TimeDependent
