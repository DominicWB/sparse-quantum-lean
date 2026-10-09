import GateEfficientSynthesis.Payload

/-!
# Finite gate sets and the synthesis hypothesis

The gate-level libraries count *elementary gates*: one-qubit unitaries with at most three
literal controls (`GateOK 3`). Theorems `hs:thm:gates` and `ode:thm:gates` of the accompanying
paper finally compile every elementary gate over a finite gate set, using "a gate set admitting
single-qubit synthesis of length `O(log(1/ζ))` at accuracy `ζ`" (for example the construction
with at most two clean ancillas of Kliuchnikov, Maslov and Mosca), after decomposing controlled
known gates. These are results from other papers; they enter here as explicit hypotheses.

* `Kind`: a gate kind, the values of the control literals (in order) and the one-qubit matrix;
  a gate set is a set of kinds, `kind g` is the kind of a placed gate, and `GateOf 𝒢 g` states
  that `g` is a gate of `𝒢` placed on distinct wires (distinct control wires, kind in `𝒢`).
* `canon n p u`: the canonical gate with `n` controls of values `p` and matrix `u`, on the
  canonical wires `CW n` (the controls and the target).
* `Synthesis 𝒢 X L`: `𝒢` is finite, and every canonical gate with at most three controls and a
  unitary matrix is approximated within `ζ > 0` by at most `L ζ` valid gates of `𝒢` on the
  canonical wires and the clean ancilla wires `X`, in the full-output convention: for every
  input with the ancillas zero, the outputs differ by at most `ζ` times its norm, ancilla
  residues and phases included (`ApproxOn CleanX`, payload `ℂ`, i.e. finite matrices). Since
  phases are included, a gate set whose one-qubit matrices have determinants in a finite group
  (for example Clifford+T) meets the hypothesis only with ancillas: without them, the
  determinant of the product of a gate list on one wire stays in that group.
* The two results that the paper combines: `OneQubitSynthesis 𝒢 X L` (the case of no controls)
  and `ControlDecomposition 𝒢 X K` (every controlled gate acts on clean ancillas exactly as a
  product of at most `K` gates, each a gate of `𝒢` or an uncontrolled one-qubit unitary).
  `Synthesis.of_parts` (in `Parts.lean`) derives `Synthesis` from them.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap GateCircuit GateNative
open scoped InnerProduct

/-- A gate kind: the values of the control literals, in order, and the one-qubit matrix. -/
abbrev Kind := List Bool × Matrix Bool Bool ℂ

/-- The kind of a placed gate. -/
def kind {W : Type*} (g : Gate W) : Kind := (g.cs.map Prod.snd, g.u)

/-- Renaming the wires keeps the kind. -/
theorem kind_map {A W : Type*} (e : A → W) (g : Gate A) :
    kind (GateODE.Gate.map e g) = kind g := by
  simp [kind, GateODE.Gate.map, List.map_map, Function.comp_def]

/-- **A gate of the gate set `𝒢`**, placed on distinct wires: its control wires are distinct
(validity, `GateOK`, keeps them off the target) and its kind is in `𝒢`. -/
def GateOf (𝒢 : Set Kind) {W : Type*} (g : Gate W) : Prop :=
  (g.cs.map Prod.fst).Nodup ∧ kind g ∈ 𝒢

/-- Renaming the wires along an embedding keeps a gate of `𝒢`. -/
theorem GateOf.map {𝒢 : Set Kind} {A W : Type*} (f : A ↪ W) {g : Gate A} (h : GateOf 𝒢 g) :
    GateOf 𝒢 (GateODE.Gate.map f g) := by
  refine ⟨?_, by rw [kind_map]; exact h.2⟩
  have e : ((GateODE.Gate.map f g).cs.map Prod.fst) = (g.cs.map Prod.fst).map f := by
    simp [GateODE.Gate.map, List.map_map, Function.comp_def]
  rw [e]
  exact h.1.map f.injective

/-- The canonical wires of a gate with `n` controls: the controls and the target. -/
abbrev CW (n : ℕ) := Fin n ⊕ Unit

/-- The canonical gate with `n` controls of values `p` and the matrix `u`. -/
def canon (n : ℕ) (p : Fin n → Bool) (u : Matrix Bool Bool ℂ) : Gate (CW n) :=
  ⟨(List.finRange n).map (fun i => (Sum.inl i, p i)), Sum.inr (), u⟩

/-- **The synthesis hypothesis** for the finite gate set `𝒢`, the clean ancilla wires `X` and
the length function `L`: every one-qubit unitary with at most three controls is approximated
within every `ζ > 0`, in the full-output convention with clean ancillas, by at most `L ζ` valid
gates of `𝒢`. -/
def Synthesis (𝒢 : Set Kind) (X : Type*) [Fintype X] [DecidableEq X] (L : ℝ → ℕ) : Prop :=
  𝒢.Finite ∧ ∀ n : ℕ, n ≤ 3 → ∀ (p : Fin n → Bool) (u : Matrix Bool Bool ℂ), UnitaryMat u →
    ∀ ζ : ℝ, 0 < ζ → ∃ gs : List (Gate (CW n ⊕ X)),
      (∀ g ∈ gs, GateOK 3 g ∧ GateOf 𝒢 g) ∧ gs.length ≤ L ζ ∧
      ApproxOn (Q := ℂ) CleanX (gRun gs) (liftB (X := X) (Gate.op (canon n p u))) ζ

/-- **Single-qubit synthesis** over the finite gate set `𝒢` with the clean ancilla wires `X`:
every one-qubit unitary is approximated within every `ζ > 0`, in the full-output convention, by
at most `L ζ` valid gates of `𝒢`. -/
def OneQubitSynthesis (𝒢 : Set Kind) (X : Type*) [Fintype X] [DecidableEq X] (L : ℝ → ℕ) :
    Prop :=
  𝒢.Finite ∧ ∀ (u : Matrix Bool Bool ℂ), UnitaryMat u → ∀ ζ : ℝ, 0 < ζ →
    ∃ gs : List (Gate (CW 0 ⊕ X)), (∀ g ∈ gs, GateOK 3 g ∧ GateOf 𝒢 g) ∧ gs.length ≤ L ζ ∧
      ApproxOn (Q := ℂ) CleanX (gRun gs) (liftB (X := X) (Gate.op (canon 0 Fin.elim0 u))) ζ

/-- **Exact decomposition of controlled gates** with the clean ancilla wires `X`: every one-qubit
unitary with at most three controls acts on clean ancillas exactly as a product of at most `K`
valid gates, each a gate of `𝒢` or an uncontrolled one-qubit unitary. -/
def ControlDecomposition (𝒢 : Set Kind) (X : Type*) [Fintype X] [DecidableEq X] (K : ℕ) :
    Prop :=
  ∀ n : ℕ, n ≤ 3 → ∀ (p : Fin n → Bool) (u : Matrix Bool Bool ℂ), UnitaryMat u →
    ∃ gs : List (Gate (CW n ⊕ X)), (∀ g ∈ gs, GateOK 3 g ∧ (GateOf 𝒢 g ∨ g.cs = [])) ∧
      gs.length ≤ K ∧
      ApproxOn (Q := ℂ) CleanX (gRun gs) (liftB (X := X) (Gate.op (canon n p u))) 0

end

end SparseHamiltonian.GateSynth
