import SparseODE.ODESourceQueryBudget

/-!
# Herald transport through a fixed isometric workspace embedding

Source preparation can be compiled on a larger physical workspace.  An exact
state intertwining then transports the verified public decoding, successful
amplitude and normalized error to that implemented preparation.  Applying the
verified actual-circuit amplification theorem needs no new probability or
direction assumption on the enlarged circuit.

-/

namespace SparseHamiltonian.ODESourceHeraldLift

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct

variable {P K H : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A fixed isometric workspace extension preserves the clean output encoding. -/
theorem output_isometry (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) :
    (E ∘L F)† ∘L (E ∘L F) = 1 := by
  apply (E ∘L F).norm_map_iff_adjoint_comp_self.mp
  intro v
  rw [comp_apply, E.norm_map_iff_adjoint_comp_self.mpr hE,
    F.norm_map_iff_adjoint_comp_self.mpr hF]

/-- Decoding after an isometric extension returns the original public vector. -/
theorem decode_lift (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (v : K) :
    ((E ∘L F)†) (E v) = (F†) v := by
  have hLeft : (E†) (E v) = v :=
    congrArg (fun A : K →L[ℂ] K => A v) hE
  rw [adjoint_comp, comp_apply, hLeft]

/-- The physical herald component is the isometric image of the old herald. -/
theorem projected_lift (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (v : K) :
    ODEHeraldedSuccess.successProjector (E ∘L F) (E v) =
      E (ODEHeraldedSuccess.successProjector F v) := by
  simpa only [ODEHeraldedSuccess.successProjector, comp_apply] using
    congrArg (fun y : P => E (F y)) (decode_lift E hE F v)

/-- The extension does not dilute the successful amplitude. -/
theorem projected_norm_lift (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (v : K) :
    ‖ODEHeraldedSuccess.successProjector (E ∘L F) (E v)‖ =
      ‖ODEHeraldedSuccess.successProjector F v‖ := by
  rw [projected_lift E hE F v]
  exact E.norm_map_iff_adjoint_comp_self.mpr hE _

/-- Hence the physical herald probability is unchanged as well. -/
theorem probability_lift (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (v : K) :
    ‖ODEHeraldedSuccess.successProjector (E ∘L F) (E v)‖ ^ 2 =
      ‖ODEHeraldedSuccess.successProjector F v‖ ^ 2 := by
  rw [projected_norm_lift E hE F v]

/-- Only equality of the actually prepared states is required to transport
the amplitude; the two preparation operators need not agree elsewhere. -/
theorem amplitude_eq_of_state_eq (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K)
    (W' : H →L[ℂ] H) (ψ' : H) (hState : W' ψ' = E (W ψ)) :
    ODEGroverActual.amplitude (E ∘L F) W' ψ' =
      ODEGroverActual.amplitude F W ψ := by
  unfold ODEGroverActual.amplitude
  rw [hState, projected_norm_lift E hE F (W ψ)]

/-- The original public error is the implemented public error after lifting. -/
theorem decoded_eq_of_state_eq (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K)
    (W' : H →L[ℂ] H) (ψ' : H) (hState : W' ψ' = E (W ψ)) :
    ((E ∘L F)†) (W' ψ') = (F†) (W ψ) := by
  rw [hState, decode_lift E hE F (W ψ)]

/-- A counted source compiler may enlarge the workspace.  Once its actual
unitary prepares the embedded old state, the original amplitude and error
estimates give the verified randomized-amplification certificate on the new
physical workspace.  No error factor is introduced by the amplification. -/
theorem randomized_lift
    (E : K →L[ℂ] H) (hE : E† ∘L E = 1)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (ψ : K)
    (W' : H →L[ℂ] H) (hW' : IsUnitary W') (ψ' : H) (hψ' : ‖ψ'‖ = 1)
    (hState : W' ψ' = E (W ψ))
    (g : ℝ) (hg : 1 ≤ g)
    (hLower : 1 / (4 * g) ≤ ODEGroverActual.amplitude F W ψ)
    (hUpper : ODEGroverActual.amplitude F W ψ ≤ 1 / 2)
    (target : P) (η : ℝ)
    (hError : ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ ≤ η) :
    0 < ODEGroverAverage.chosenIterations g ∧
    (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
    (1 : ℝ) / 4 ≤ ODEGroverActual.meanProbability
      (E ∘L F) W' ψ' (ODEGroverAverage.chosenIterations g) ∧
    ∀ j : ℕ, ODEGroverActual.decoded (E ∘L F) W' ψ' j ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection (ODEGroverActual.decoded (E ∘L F) W' ψ' j) -
          unitDirection target‖ ≤ η := by
  have hAmplitude := amplitude_eq_of_state_eq E hE F W ψ W' ψ' hState
  have hNewLower : 1 / (4 * g) ≤ ODEGroverActual.amplitude (E ∘L F) W' ψ' := by
    rw [hAmplitude]
    exact hLower
  have hNewUpper : ODEGroverActual.amplitude (E ∘L F) W' ψ' ≤ 1 / 2 := by
    rw [hAmplitude]
    exact hUpper
  have hNewError :
      ‖unitDirection (((E ∘L F)†) (W' ψ')) - unitDirection target‖ ≤ η := by
    rw [decoded_eq_of_state_eq E hE F W ψ W' ψ' hState]
    exact hError
  exact ODEGroverActual.randomized_certificate (E ∘L F)
    (output_isometry E hE F hF) W' hW' ψ' hψ' g hg hNewLower hNewUpper
    target η hNewError

end
end SparseHamiltonian.ODESourceHeraldLift
