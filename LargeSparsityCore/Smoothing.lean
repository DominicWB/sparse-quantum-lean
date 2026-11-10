import SparseHamiltonian.SharpClockSimulation
import SparseHamiltonian.SharpLabeledActiveClockQuery

set_option autoImplicit false

/-!
# Amplified smoothing for an arbitrary filter

The released package builds its amplified signed smoothing (`SparseHamiltonian.AmplifiedSmoothing`)
for the repeated average `g_L^k`. The large-sparsity core uses the product filter
`g_{B₀}^m g_p^k` (`opt:eq:filter`). Every step of that construction is in fact
generic in the coefficient list `a` and degree `d`; this module states the generic versions:

* `implementation a d A B C D`: the reflection-amplified coherent signed smoothing of the full reuse
  circuits, with input and output preparations `SmoothingLCU.input a d`, `SmoothingLCU.output a d`;
* `implementation_isometry`, `implementation_error`: an isometry with full-output error at most
  `2δ` whenever the smoothing residual of the filter `∑ aⱼ Dʲ` is at most `δ`;
* `exists_implementation`: the clock version (template
  `SparseHamiltonian.SharpClockSimulation.exists_precise_implementation`), from the released clock
  promises and a filter bound `‖∑ aⱼ D_gʲ‖ ≤ δ` for the actual global private block;
* `implementation_query_certificate`: the labeled physical query certificate with at most
  `6 d q` calls when every synchronized active clock layer is implemented with `q` calls.

The coefficient hypotheses are those of `opt:eq:smoothing`: absolute signed weight two and
total mass one.
-/

namespace LargeSparsityCore.Smoothing

noncomputable section

open ContinuousLinearMap SparseHamiltonian
open GlobalResolvent ChronologicalResolvent ChronologicalCatalyst GlobalColligation
open OracleCircuit LabeledEncodedOracle ReuseLayerFactorization
open scoped InnerProduct BigOperators

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The coherent SELECT applied to the weighted uniform preparation. -/
def prepared (a : ℕ → ℝ) (d : ℕ) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) :=
  SmoothingLCU.circuit A B C D d ∘L SmoothingLCU.input a d

/-- One reflection amplification round of the coherent smoothing. -/
def implementation (a : ℕ → ℝ) (d : ℕ) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) :=
  reflectedAmplification (SmoothingLCU.output (P := P) (V := V) a d) (prepared a d A B C D)

theorem prepared_isometry (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ i : ReuseWeights.Index d, |ReuseWeights.weight a d i| = 2)
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2) :
    (prepared a d A B C D)† ∘L prepared a d A B C D = 1 := by
  unfold prepared
  rw [adjoint_comp, comp_assoc, ← comp_assoc ((SmoothingLCU.circuit A B C D _)†),
    SmoothingLCU.circuit_isometry A B C D hStep, one_def, id_comp]
  exact SmoothingLCU.input_isometry _ _ hd hmass

/-- The complete amplified output preserves norms. -/
theorem implementation_isometry (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ i : ReuseWeights.Index d, |ReuseWeights.weight a d i| = 2)
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2) :
    (implementation a d A B C D)† ∘L implementation a d A B C D = 1 :=
  reflectedAmplification_isometry _ _ (SmoothingLCU.output_isometry _ _ hd hmass)
    (prepared_isometry a d hd hmass A B C D hStep)

/-- Full-output error at most twice the smoothing residual of the filter `∑ aⱼ Dʲ`. -/
theorem implementation_error (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ i : ReuseWeights.Index d, |ReuseWeights.weight a d i| = 2)
    (hsum : ∑ j ∈ Finset.range (d + 1), a j = 1)
    (A U : P →L[ℂ] P) (B : V →L[ℂ] P) (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (hExit : B = U ∘L (Γ† ∘L (1 - D)))
    (hU : star U * U = 1) (hUU : U * star U = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hResidual : ‖smoothedTransducerResidual U Γ (∑ j ∈ Finset.range (d + 1), a j • D ^ j)
      D d‖ ≤ δ) :
    ‖implementation a d A B C D - SmoothingLCU.output (P := P) (V := V) a d ∘L U‖ ≤ 2 * δ := by
  apply reflectedAmplification_error_of_block_error _ _ U
    (SmoothingLCU.output_isometry _ _ hd hmass)
    (prepared_isometry a d hd hmass A B C D hStep) hU hUU hδ hδ1
  change ‖(2 : ℂ) • SmoothingLCU.successfulBlock _ _ A B C D - U‖ ≤ δ
  rw [SmoothingLCU.successfulBlock_eq _ _ hd A U B C Γ D hPublic hPrivate,
    smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul,
    norm_sub_rev, SmoothedReuse.weighted_expression_residual a d hd hsum U B Γ D hExit]
  exact hResidual

/-- A separate public approximation error adds linearly. -/
theorem implementation_error_to_target (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ i : ReuseWeights.Index d, |ReuseWeights.weight a d i| = 2)
    (A U E : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V) (δ ε : ℝ)
    (hImplementation : ‖implementation a d A B C D -
      SmoothingLCU.output (P := P) (V := V) a d ∘L U‖ ≤ δ)
    (hTarget : ‖U - E‖ ≤ ε) :
    ‖implementation a d A B C D - SmoothingLCU.output (P := P) (V := V) a d ∘L E‖ ≤ δ + ε := by
  let J := SmoothingLCU.output (P := P) (V := V) a d
  have hJ : ‖J‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro p
    have hh := (norm_map_iff_adjoint_comp_self J).mpr
      (SmoothingLCU.output_isometry _ _ hd hmass) p
    simpa only [one_mul] using hh.le
  calc
    ‖implementation a d A B C D - J ∘L E‖ ≤
      ‖implementation a d A B C D - J ∘L U‖ + ‖J ∘L U - J ∘L E‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ + ε := add_le_add hImplementation (by
      rw [← comp_sub]
      calc
        ‖J ∘L (U - E)‖ ≤ ‖J‖ * ‖U - E‖ := opNorm_comp_le _ _
        _ ≤ 1 * ‖U - E‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
        _ ≤ ε := by simpa only [one_mul] using hTarget)

/-- The amplified implementation of the full chronological clock transducer for the filter with
coefficients `a` and degree `d`. -/
def clockImplementation (a : ℕ → ℝ) (d : ℕ) (D : V →L[ℂ] V) (J : P →L[ℂ] V) (w : ℝ) (T : ℕ) :=
  implementation a d
    (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (publicExit ((CayleyTransfer.c w : ℂ) • 1)
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) T)
    (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
      ((CayleyTransfer.c w : ℂ) • 1) T)
    (globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T)

set_option maxRecDepth 4096 in
/-- **Generic clock implementation.** From the released clock promises and a filter
bound `‖∑ aⱼ D_gʲ‖ ≤ δ` for the actual global private block `D_g`, with degree at least six times
the weighted catalyst budget, the amplified circuit is an isometry with full-output error at most
`2δ` relative to the constructed Cayley power `U^T`. -/
theorem exists_implementation (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ i : ReuseWeights.Index d, |ReuseWeights.weight a d i| = 2)
    (hsum : ∑ j ∈ Finset.range (d + 1), a j = 1)
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (w Q b qbar : ℝ) (T : ℕ)
    (hQ : 0 < Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hdeg : 6 * ((T : ℝ) * w * qbar) ≤ d)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδOne : δ ≤ 1)
    (hfilter : ‖∑ j ∈ Finset.range (d + 1), a j • (globalPrivateBlock D J (CayleyTransfer.c w)
      (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) T) ^ j‖ ≤ δ) :
    ∃ (U R : P →L[ℂ] P),
      CayleyTransfer.cayleyDenominator w H ∘L R = 1 ∧
      U = CayleyTransfer.cayleyNumerator w H ∘L R ∧
      (U ^ T)† ∘L (U ^ T) = 1 ∧ (U ^ T) ∘L (U ^ T)† = 1 ∧
      (clockImplementation a d D J w T)† ∘L clockImplementation a d D J w T = 1 ∧
      ‖clockImplementation a d D J w T -
        SmoothingLCU.output (P := P) (V := BlockOperator.H T V) a d ∘L (U ^ T)‖ ≤ 2 * δ := by
  let c := CayleyTransfer.c w
  let κ := CayleyTransfer.kappa w
  let σ := CayleyTransfer.sigma w
  let A := ((c : ℂ) • (1 : P →L[ℂ] P)) ^ T
  let B := publicExit ((c : ℂ) • (1 : P →L[ℂ] P)) ((-(σ : ℂ)) • (J† ∘L D)) T
  let C := stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T
  let G := globalPrivateBlock D J c κ σ T
  obtain ⟨hκ, hκUpper, hκc, hσc, hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  obtain ⟨Γ, U, hLocalPrivate, hLocalPublic, _hUNorm, hPrivate, _hTrajectory, hCost⟩ :=
    exists_global_catalyst D R1 J H c κ σ w Q b qbar hQ hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ T
  obtain ⟨R, hRRight, _hRLeft, hCayley⟩ :=
    local_public_is_cayley D R1 J Γ H U w hw hwQuarter hRight hLeft hJ hBoundary
      hSelf hH hLocalPrivate hLocalPublic
  have hUnitary := local_public_unitary D R1 J Γ H U w hw hwQuarter
    hRight hLeft hJ hBoundary hSelf hH hLocalPrivate hLocalPublic
  have hPowUnitary := CayleyTransfer.unitary_pow U hUnitary.1 hUnitary.2 T
  have hPublic : A + B ∘L stackedResponse Γ U T = U ^ T :=
    catalyst_public_transduction Γ U ((c : ℂ) • 1)
      ((-(σ : ℂ)) • (J† ∘L D)) hLocalPublic T
  have hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖G v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
    intro p v
    have h := chronological_full_energy (localPrivateBlock D J κ) ((σ : ℂ) • J)
      ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D))
      (LocalRotation.local_step_energy D J c κ σ hκc hσc hD hJ) T p v
    change ‖A p + B v‖ ^ 2 + ‖C p + G v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 at h
    simpa only [add_comm (G v) (C p)] using h
  have hExit : B = (U ^ T) ∘L ((stackedResponse Γ U T)† ∘L (1 - G)) :=
    GlobalExit.clock_exit_block_eq D R1 J Γ H U w hw hwQuarter hD hJ hRight hLeft
      hBoundary hSelf hH hLocalPrivate hLocalPublic T
  have hNorm : ‖U ^ T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    have hh := (norm_map_iff_adjoint_comp_self (U ^ T)).mpr hPowUnitary.1 p
    rw [hh, one_mul]
  have hResidual : ‖smoothedTransducerResidual (U ^ T) (stackedResponse Γ U T)
      (∑ j ∈ Finset.range (d + 1), a j • G ^ j) G d‖ ≤ δ := by
    apply smoothedTransducerResidual_norm_le_filter (W := 3 * ((T : ℝ) * w * qbar))
      (U ^ T) (stackedResponse Γ U T) _ G hNorm
      (globalPrivateBlock_norm_le_one D J c κ σ T hκc hσc hD hJ) hCost hd _ hfilter
    linarith
  refine ⟨U, R, hRRight, hCayley, hPowUnitary.1, hPowUnitary.2, ?_, ?_⟩
  · exact implementation_isometry a d hd hmass A B C G hStep
  · exact implementation_error a d hd hmass hsum A (U ^ T) B C (stackedResponse Γ U T) G
      hStep hPublic hPrivate hExit hPowUnitary.1 hPowUnitary.2 δ hδ hδOne hResidual

section Query

variable {Label : Type*}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The complete coherent workspace of the generic smoothing. -/
abbrev Space (P V : Type*) [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (d T : ℕ) :=
  PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V) d)

/-- A physical program implements the generic amplified clock output on encoded input, with
at most `6 d q` calls when every synchronized active clock layer is implemented with `q` calls. -/
theorem implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (a : ℕ → ℝ) (d : ℕ) (hd : 0 < d)
    (hmass : ∑ i : ReuseWeights.Index d, |ReuseWeights.weight a d i| = 2)
    (D : X → V →L[ℂ] V) (J : P →L[ℂ] V) (w : ℝ) (T : ℕ) (hw : 0 ≤ w)
    (hwQuarter : w ≤ 1 / 4) (hD : ∀ x, (D x)† ∘L D x = 1) (hJ : J† ∘L J = 1)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : Space P V d T →L[ℂ] K) (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * d, ImplementsOn O (fun x => activeClock (P := P) (D x) T d r) E q) :
    ∃ p : MultiOracleCircuit.Program O, p.count ≤ 6 * d * q ∧
      ∀ x, p.eval x ∘L (E ∘L SmoothingLCU.input (P := P) (V := BlockOperator.H T V) a d) =
        E ∘L clockImplementation a d (D x) J w T := by
  let A := ((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T
  let B := fun x => publicExit ((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P))
    ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D x)) T
  let C := stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
    ((CayleyTransfer.c w : ℂ) • 1) T
  let G := fun x => globalPrivateBlock (D x) J (CayleyTransfer.c w)
    (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) T
  obtain ⟨_hκ, _hκUpper, hκc, hσc, _hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  have hStep : ∀ x p v, ‖A p + B x v‖ ^ 2 + ‖G x v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
    intro x p v
    have h := chronological_full_energy
      (localPrivateBlock (D x) J (CayleyTransfer.kappa w))
      ((CayleyTransfer.sigma w : ℂ) • J) ((CayleyTransfer.c w : ℂ) • 1)
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D x))
      (LocalRotation.local_step_energy (D x) J _ _ _ hκc hσc (hD x) hJ) T p v
    change ‖A p + B x v‖ ^ 2 + ‖C p + G x v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 at h
    simpa only [add_comm (G x v) (C p)] using h
  -- Each synchronized reuse layer is the fixed coupling after the active clock.
  have hLayer : ∀ r < 2 * d, ImplementsOn O
      (fun x => ReuseQuery.reuseLayer A (B x) C (G x) d r) E q := by
    intro r hr
    have hFixed := ImplementsOn.fixed (O := O) hE
      (couplingLayer J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T d r)
      (couplingLayer_unitary J hJ _ _ _ hκc hσc T d r)
    have h := (hFixed.mul (hQuery r hr)).congr (fun x =>
      (clockReuseLayer_factor (D x) J _ _ _ T d r).symm)
    simpa only [Nat.zero_add] using h
  have hCircuit := LabeledEncodedAmplification.circuit_implementsOn d q hd O E
    (fun _ => A) B (fun _ => C) G hLayer
  have hUnit (x : X) : IsUnitary (SmoothingLCU.circuit A (B x) C (G x) d) :=
    SmoothingLCU.circuit_unitary A (B x) C (G x) (hStep x) _
  obtain ⟨p, hp, hq⟩ := LabeledEncodedAmplification.threeSelect_implementsOn E hE hO hUnit
    (SmoothingLCU.input (P := P) (V := BlockOperator.H T V) a d)
    (SmoothingLCU.output (P := P) (V := BlockOperator.H T V) a d)
    (SmoothingLCU.input_isometry (P := P) (V := BlockOperator.H T V) _ _ hd hmass)
    (SmoothingLCU.output_isometry (P := P) (V := BlockOperator.H T V) _ _ hd hmass) hCircuit
  refine ⟨p, ?_, fun x => ?_⟩
  · calc p.count ≤ 3 * (2 * d * q) := hq
      _ = 6 * d * q := by ring
  · rw [← comp_assoc, hp, comp_assoc, clockImplementation, implementation, prepared,
      AmplificationQuery.smoothing_eq_threeSelect a d A (B x) C (G x) (hStep x)]

end Query

end

end LargeSparsityCore.Smoothing
