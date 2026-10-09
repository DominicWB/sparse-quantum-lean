import SparseLowerBounds.Query.Readout

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Reduction of labelled-oracle algorithms to Boolean programs

An algorithm is a `MultiOracleCircuit.Program` over a unitary labelled oracle
family `O : L → X → P →L[ℂ] P` on a logical workspace `P`. If every label is
implementable on a fixed isometric encoding `E : P →L[ℂ] K` by a program over
a Boolean base oracle `Q : X → K →L[ℂ] K` with cost `w l`
(`EncodedOracle.ImplementsOn`), then the whole algorithm compiles to one
Boolean program with at most `p.cost w` queries that intertwines `E`
(`EncodedMultiOracle.implements_compile`).

Seeds and observables transport through `E`: a seed `φ` becomes `E φ` (same
norm) and an observable `M` becomes `E M E†` (norm at most `‖M‖`), and every
expectation is preserved. So every correlation of the original algorithm is
a correlation of a Boolean program with the same seed norm and observable
bound, which is the form the adversary bounds consume.
-/

namespace SparseLowerBounds.Reduction

noncomputable section
open SparseHamiltonian OracleCircuit ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*}

/-- **Compilation to Boolean queries.** A labelled program whose labels are
encoded-implementable with costs `w` has a Boolean program with at most
`p.cost w` queries that agrees with it on the encoded subspace. -/
theorem exists_boolean_program (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    {Q : X → K →L[ℂ] K} (hQ : ∀ x, IsUnitary (Q x))
    {O : L → X → P →L[ℂ] P} (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (h : ∀ l, EncodedOracle.ImplementsOn Q (O l) E (w l))
    (p : MultiOracleCircuit.Program O) :
    ∃ c : OracleCircuit.Program Q, c.count ≤ p.cost w ∧
      ∀ x, c.eval x ∘L E = E ∘L p.eval x := by
  obtain ⟨c, hc, hcount⟩ := EncodedMultiOracle.implements_compile E hE hQ hO p w h
  exact ⟨c, hcount, hc⟩

/-- The encoded observable `E M E†`. -/
def encodeObs (E : P →L[ℂ] K) (M : P →L[ℂ] P) : K →L[ℂ] K := E ∘L M ∘L E†

/-- An isometric encoding preserves seed norms. -/
theorem norm_encode (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (φ : P) : ‖E φ‖ = ‖φ‖ :=
  E.norm_map_iff_adjoint_comp_self.mpr hE φ

theorem norm_encodeObs_le (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (M : P →L[ℂ] P) :
    ‖encodeObs E M‖ ≤ ‖M‖ := by
  have hadj : ‖E†‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    refine E.opNorm_le_bound zero_le_one fun v => ?_
    rw [E.norm_map_iff_adjoint_comp_self.mpr hE v, one_mul]
  calc ‖encodeObs E M‖ = ‖M ∘L E†‖ := EncodedOracle.norm_comp_eq E hE _
    _ ≤ ‖M‖ * ‖E†‖ := opNorm_comp_le _ _
    _ ≤ ‖M‖ * 1 := by gcongr
    _ = ‖M‖ := mul_one _

/-- Expectations are preserved: `⟪E φ, E M E† E φ⟫ = ⟪φ, M φ⟫`. -/
theorem inner_encodeObs (E : P →L[ℂ] K) (hE : E† ∘L E = 1) (M : P →L[ℂ] P) (φ : P) :
    ⟪E φ, encodeObs E M (E φ)⟫_ℂ = ⟪φ, M φ⟫_ℂ := by
  have hEv : (E†) (E φ) = φ := by
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using
      congrArg (fun A : P →L[ℂ] P => A φ) hE
  change ⟪E φ, E (M ((E†) (E φ)))⟫_ℂ = _
  rw [hEv, ← adjoint_inner_left E (M φ) (E φ), hEv]

/-- **Transport of correlations.** The compiled Boolean program, run on the
encoded seed and measured with the encoded observable, reproduces every
expectation of the labelled program on every input. -/
theorem exists_boolean_program_inner (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    {Q : X → K →L[ℂ] K} (hQ : ∀ x, IsUnitary (Q x))
    {O : L → X → P →L[ℂ] P} (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (h : ∀ l, EncodedOracle.ImplementsOn Q (O l) E (w l))
    (p : MultiOracleCircuit.Program O) :
    ∃ c : OracleCircuit.Program Q, c.count ≤ p.cost w ∧
      ∀ x (φ : P) (M : P →L[ℂ] P),
        ⟪c.eval x (E φ), encodeObs E M (c.eval x (E φ))⟫_ℂ =
          ⟪p.eval x φ, M (p.eval x φ)⟫_ℂ := by
  obtain ⟨c, hcount, hc⟩ := exists_boolean_program E hE hQ hO w h p
  refine ⟨c, hcount, fun x φ M => ?_⟩
  have h1 : c.eval x (E φ) = E (p.eval x φ) :=
    congrArg (fun A : P →L[ℂ] K => A φ) (hc x)
  rw [h1, inner_encodeObs E hE]

end

end SparseLowerBounds.Reduction
end
