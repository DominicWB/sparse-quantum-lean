import SparseHamiltonian.LookupClockSimulation

/-!
# Ordinary-lookup simulation with an encoded public register

The logical public space is embedded into the lookup payload by one fixed
isometry. Private clock registers are unchanged. Two ordinary lookup calls
implement every active clock step on this image, with a common physical oracle
for all reuse indices. Thus the full-output simulation theorem has no query
implementation premise and applies to arbitrary compatible public registers.
-/

namespace SparseHamiltonian.EncodedLookupClockSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit MaskedLookupCurry EncodedOracle
open scoped InnerProduct
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {X C A Z : Type*} [Fintype C] [Fintype A] [Fintype Z] [AddCommGroup Z]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- A common ordinary lookup on the full physical simulation workspace, with
all simulation labels carried as spectators. It does not depend on reuse index. -/
def evolutionOracle (f : X → A → Z) (τ Q qbar ε : ℝ) (x : X) :
    ClockQuery.EvolutionSpace (P := Payload A Z)
      (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε →L[ℂ]
    ClockQuery.EvolutionSpace (P := Payload A Z)
      (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε :=
  ActiveLookupClock.ordinaryOracle C f (TimeSchedule.steps τ (ε / 3))
    (FilterSchedule.degree Q
      ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
      (ε / 3)) x

/-- The physical lookup is unitary on the whole ambient register space. -/
theorem evolutionOracle_unitary (f : X → A → Z) (τ Q qbar ε : ℝ) (x : X) :
    IsUnitary (evolutionOracle (C := C) f τ Q qbar ε x) :=
  ActiveLookupClock.ordinaryOracle_unitary C f _ _ x

/-- The schedule's fixed public-register encoding leaves every private register
unchanged and applies the same given isometry to every public reuse slot. -/
def evolutionEncoding (e : P →ₗᵢ[ℂ] Payload A Z) (τ Q qbar ε : ℝ) :
    ClockQuery.EvolutionSpace (P := P)
      (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε →L[ℂ]
    ClockQuery.EvolutionSpace (P := Payload A Z)
      (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε :=
  PublicRegisterEncoding.embedding e
    (FilterSchedule.degree Q
      ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
      (ε / 3))

omit [AddCommGroup Z] in
/-- The full fixed register encoding is an isometry. -/
theorem evolutionEncoding_isometry (e : P →ₗᵢ[ℂ] Payload A Z) (τ Q qbar ε : ℝ) :
    (evolutionEncoding (C := C) e τ Q qbar ε)† ∘L evolutionEncoding e τ Q qbar ε = 1 :=
  PublicRegisterEncoding.embedding_adjoint_comp e _

/-- The signed lookup clock factor and a fixed unitary preserve norms without
any separately assumed clock-unitarity promise. -/
theorem fixed_signed_isometry (f : X → A → Z)
    (F : PiLp 2 (fun _ : C => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : C => Payload A Z)) (hF : IsUnitary F) (m : C → ℤ) (x : X) :
    (F ∘L WeightedClock.diagonal (fun c => localSigned (m c) f x))† ∘L
      (F ∘L WeightedClock.diagonal (fun c => localSigned (m c) f x)) = 1 := by
  have hDiag := WeightedClock.diagonal_isometry (fun c => localSigned (m c) f x)
    (fun c => (localSigned_unitary (m c) f x).1)
  apply norm_map_iff_adjoint_comp_self _ |>.mp
  intro v
  rw [comp_apply, F.norm_map_iff_adjoint_comp_self.mpr hF.1]
  exact (WeightedClock.diagonal (fun c => localSigned (m c) f x)).norm_map_iff_adjoint_comp_self.mpr
    hDiag v

/-- All active clock implementation obligations are discharged by two ordinary
queries. The remaining assumptions are analytic promises of the specified
clock and a fixed public encoding, independent of the unknown table. -/
theorem evolution_query_certificate [FiniteDimensional ℂ P] (f : X → A → Z)
    (F : PiLp 2 (fun _ : C => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : C => Payload A Z)) (hF : IsUnitary F) (m : C → ℤ)
    (D R1 : X → PiLp 2 (fun _ : C => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : C => Payload A Z))
    (hFactor : ∀ x, D x = F ∘L WeightedClock.diagonal (fun c => localSigned (m c) f x))
    (e : P →ₗᵢ[ℂ] Payload A Z)
    (J : P →L[ℂ] PiLp 2 (fun _ : C => Payload A Z)) (H : X → P →L[ℂ] P)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hJ : J† ∘L J = 1)
    (hRight : ∀ x, (1 - D x) ∘L R1 x = 1)
    (hLeft : ∀ x, R1 x ∘L (1 - D x) = 1)
    (hR1 : ∀ x, ‖R1 x‖ ≤ Q)
    (hBoundary : ∀ x, J† ∘L R1 x ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H x))
    (hSelf : ∀ x, star (H x) = H x) (hH : ∀ x, ‖H x‖ ≤ 1)
    (hEndpoint : ∀ x, ‖R1 x ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ p : Program (evolutionOracle (C := C) f τ Q qbar ε),
      p.count ≤ 12 * FilterSchedule.degree Q (τ * qbar) (ε / 3) ∧
      (p.count : ℝ) ≤ 768 *
        (τ * qbar + Q * (1 + Real.log (3 * (Q + τ * qbar + 2) / ε))) ∧
      (evolutionEncoding (C := C) e τ Q qbar ε ∘L
        ClockQuery.evolutionInput (P := P) (V := PiLp 2 (fun _ : C => Payload A Z))
          τ Q qbar ε)† ∘L
        (evolutionEncoding e τ Q qbar ε ∘L ClockQuery.evolutionInput τ Q qbar ε) = 1 ∧
      (evolutionEncoding (C := C) e τ Q qbar ε ∘L
        ClockSimulation.evolutionOutput (P := P) (V := PiLp 2 (fun _ : C => Payload A Z))
          τ Q qbar ε)† ∘L
        (evolutionEncoding e τ Q qbar ε ∘L ClockSimulation.evolutionOutput τ Q qbar ε) = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (evolutionEncoding (C := C) e τ Q qbar ε ∘L
            ClockQuery.evolutionInput (P := P) (V := PiLp 2 (fun _ : C => Payload A Z))
              τ Q qbar ε) -
          evolutionEncoding (C := C) e τ Q qbar ε ∘L
            ClockSimulation.evolutionOutput (P := P) (V := PiLp 2 (fun _ : C => Payload A Z))
              τ Q qbar ε ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H x)‖ ≤ ε := by
  have hD (x : X) : (D x)† ∘L D x = 1 := by
    rw [hFactor]
    exact fixed_signed_isometry f F hF m x
  have hQuery : ∀ r < 2 * FilterSchedule.degree Q (τ * qbar) (ε / 3),
      ImplementsOn (evolutionOracle (C := C) f τ Q qbar ε)
        (fun x => ActiveClockQuery.evolutionActiveClock (P := P) (D x) τ Q qbar ε r)
        (evolutionEncoding e τ Q qbar ε) 2 := by
    intro r _hr
    have hPhysical := ActiveLookupClock.activeClock_fixed_signed_two_queries f F hF m
      (TimeSchedule.steps τ (ε / 3))
      (FilterSchedule.degree Q
        ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
        (ε / 3)) r
    have hPhysical' := hPhysical.congr (fun x => congrArg
      (fun D => ReuseLayerFactorization.activeClock (P := Payload A Z) D
        (TimeSchedule.steps τ (ε / 3))
        (FilterSchedule.degree Q
          ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
          (ε / 3)) r) (hFactor x).symm)
    exact PublicRegisterEncoding.activeClock_implementsOn e D _ _ r 2 _ hPhysical'
  obtain ⟨p, hn, hr, hi, ho, he⟩ :=
    EncodedActiveClockQuery.evolution_query_certificate D R1 J H τ Q b qbar ε hτ hQ
      hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hε hεOne
      (evolutionOracle (C := C) f τ Q qbar ε)
      (evolutionOracle_unitary f τ Q qbar ε)
      (evolutionEncoding e τ Q qbar ε) (evolutionEncoding_isometry e τ Q qbar ε) 2 hQuery
  refine ⟨p, ?_, ?_, hi, ho, he⟩
  · omega
  · simpa only [Nat.cast_ofNat, show (384 : ℝ) * 2 = 768 by norm_num] using hr

end
end SparseHamiltonian.EncodedLookupClockSimulation
