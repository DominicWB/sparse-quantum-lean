import SparseHamiltonian.MultiOracleTransport
import SparseODE.ODEGroverProgram

set_option autoImplicit false

/-!
# Amplitude-amplification trial families

Manuscript lines 4687-4689 (proof of Lemma `odel:lem:dyson`): "Amplitude amplification with a
known lower bound on success probability costs `O(ḡ e^z)` and gives constant heralded success."
The released trials (`ODECountedAmplification.program`, `ODEGroverProgram.amplified`) run, for
the classically drawn cutoff `j`, the preparation `A` followed by `j` signed Grover steps
`U₁ A U₂ A† U₃` with fixed reflections.

`GroverShape q w a w' U₁ U₂ U₃` records this structure of a trial family `q` at the level of
evaluations and costs: one preparation program `a`, three fixed unitaries, `q j` evaluates to
`(U₁ A U₂ A† U₃)^j A` with `A = a(x)`, and its `w`-cost is `2j + 1` times the `w'`-cost of `a`.
It is preserved by every program map that conjugates evaluations by one fixed isometry and keeps
costs (`GroverShape.map`), such as the release's compilers and coordinate changes.
-/

namespace DysonSingleProgram

noncomputable section
open SparseHamiltonian OracleCircuit

variable {X L L' W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **Amplitude-amplification shape of a trial family** `q`: a preparation program `a` and fixed
unitaries `U₁ U₂ U₃` with `q j (x) = (U₁ a(x) U₂ a(x)† U₃)^j a(x)` and
`cost_w (q j) = (2j + 1) cost_{w'} a`. -/
structure GroverShape {O : L → X → W →L[ℂ] W} {O' : L' → X → W →L[ℂ] W}
    (q : ℕ → MultiOracleCircuit.Program O) (w : L → ℕ) (a : MultiOracleCircuit.Program O')
    (w' : L' → ℕ) (U₁ U₂ U₃ : W →L[ℂ] W) : Prop where
  unitary₁ : IsUnitary U₁
  unitary₂ : IsUnitary U₂
  unitary₃ : IsUnitary U₃
  eval_eq : ∀ (j : ℕ) (x : X),
    (q j).eval x = (U₁ * a.eval x * U₂ * star (a.eval x) * U₃) ^ j * a.eval x
  cost_eq : ∀ j : ℕ, (q j).cost w = (2 * j + 1) * a.cost w'

variable {W' L₂ L₂' : Type*} [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [CompleteSpace W']

/-- **Transport of the shape** along program maps that conjugate evaluations by one fixed
isometry `Φ` and keep the counted costs. -/
theorem GroverShape.map {O : L → X → W →L[ℂ] W} {O' : L' → X → W →L[ℂ] W}
    {O₂ : L₂ → X → W' →L[ℂ] W'} {O₂' : L₂' → X → W' →L[ℂ] W'}
    {q : ℕ → MultiOracleCircuit.Program O} {w : L → ℕ} {a : MultiOracleCircuit.Program O'}
    {w' : L' → ℕ} {U₁ U₂ U₃ : W →L[ℂ] W} (h : GroverShape q w a w' U₁ U₂ U₃)
    (Φ : W ≃ₗᵢ[ℂ] W')
    (f : MultiOracleCircuit.Program O → MultiOracleCircuit.Program O₂)
    (f' : MultiOracleCircuit.Program O' → MultiOracleCircuit.Program O₂')
    (w₂ : L₂ → ℕ) (w₂' : L₂' → ℕ)
    (hf : ∀ p x, (f p).eval x = Φ.conjStarAlgEquiv (p.eval x))
    (hf' : ∀ p x, (f' p).eval x = Φ.conjStarAlgEquiv (p.eval x))
    (hc : ∀ p, (f p).cost w₂ = p.cost w) (hc' : ∀ p, (f' p).cost w₂' = p.cost w') :
    GroverShape (fun j => f (q j)) w₂ (f' a) w₂' (Φ.conjStarAlgEquiv U₁)
      (Φ.conjStarAlgEquiv U₂) (Φ.conjStarAlgEquiv U₃) := by
  refine ⟨h.unitary₁.transport Φ, h.unitary₂.transport Φ, h.unitary₃.transport Φ, ?_, ?_⟩
  · intro j x
    rw [hf, h.eval_eq, hf']
    simp only [map_mul, map_pow, map_star]
  · intro j
    rw [hc, h.cost_eq, hc']

end

end DysonSingleProgram
