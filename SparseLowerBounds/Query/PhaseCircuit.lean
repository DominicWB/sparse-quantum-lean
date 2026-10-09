import SparseLowerBounds.Query.Ancilla
import SparseLowerBounds.Query.BitDegree

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The query–gate–unquery circuit for arbitrary Boolean strings

Manuscript lines 2283-2289 (two Boolean queries per value call) and the QLS
analogue, lines 5320-5331. This is the generic circuit behind every
compilation of a native value oracle to Boolean queries, for the phase oracle
`Q.phase y = 1 - 2 Σ_{i, y i} Q i` of an **arbitrary** string `y : I → Bool`
(`Query/PhaseOracle`). It covers both Boolean oracles used by the lower bounds:

* `oneHotOracle P j` is by definition `P.phase (fun ka => decide (j ka.1 = ka.2))`
  (search families, `oneHotOracle_eq_phase`);
* `bitOracle P x` is by definition `P.phase x` (precision family,
  `bitOracle_eq_phase`).

Contents:

* `hitProj Q y = Σ_{i, y i} Q i`, the part of the workspace that `y` marks, with
  `Q.phase y = 1 - 2 hitProj Q y` (`phase_eq_hitProj`, by `rfl`);
* on ancilla ⊗ `K` (`Joint (Fin 2) K`) the phase oracle of `Q.withAncilla`
  acts as Pauli `X` on the ancilla controlled by `S = hitProj Q y`:
  `(Ψ₀, Ψ₁) ↦ (Ψ₀ - SΨ₀ + SΨ₁, Ψ₁ - SΨ₁ + SΨ₀)`
  (`phase_withAncilla_apply_zero/one`);
* `circuit_intertwines`: the circuit `O_y (G₀ ⊕ G₁) O_y` maps the clean-ancilla
  encoding `v ↦ |0⟩ ⊗ v` (`ancillaEmbed`) to the encoding of `V v` whenever the
  two branch identities hold; `implementsOn_circuit` packages it as a
  two-query `EncodedOracle.ImplementsOn`;
* a spectator register is marked copywise (`hitProj_spectate_apply`);
* input-independent primitives cost no query (`implementsOn_const`,
  `implementsOn_of_eq`).

Generalised from the one-hot helper `Helpers/CompileReduction/AncillaCircuit`, with the same
proofs; this module does not import it.
-/

namespace SparseLowerBounds.PhaseCircuit

noncomputable section
open SparseHamiltonian OracleCircuit

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {I : Type*} [Fintype I]

omit [CompleteSpace K] in
theorem joint_sum_apply {J : Type*} [Fintype J] {ι : Type*} (S : Finset ι)
    (f : ι → Joint J K) (b : J) : (∑ i ∈ S, f i) b = ∑ i ∈ S, f i b :=
  map_sum (Joint.proj (K := K) b) f S

/-- The part of the workspace marked by the Boolean string `y`:
`hitProj Q y = Σ_{i, y i} Q i`. -/
def hitProj (Q : ProjFamily K I) (y : I → Bool) : K →L[ℂ] K :=
  ∑ i ∈ Finset.univ.filter (fun i => y i = true), Q.proj i

theorem hitProj_apply (Q : ProjFamily K I) (y : I → Bool) (v : K) :
    hitProj Q y v = ∑ i ∈ Finset.univ.filter (fun i => y i = true), Q.proj i v := by
  simp only [hitProj, _root_.sum_apply]

/-- `Q.phase y = 1 - 2 hitProj Q y`. -/
theorem phase_eq_hitProj (Q : ProjFamily K I) (y : I → Bool) :
    Q.phase y = 1 - (2 : ℂ) • hitProj Q y := rfl

omit [Fintype I] in
/-- The one-hot oracle is the phase oracle of the membership string. -/
theorem oneHotOracle_eq_phase {n m : ℕ} (P : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) :
    oneHotOracle P j = P.phase fun ka => decide (j ka.1 = ka.2) := rfl

omit [Fintype I] in
/-- The bit oracle is the phase oracle of the bit string. -/
theorem bitOracle_eq_phase {n : ℕ} (P : ProjFamily K (Fin n)) (x : Fin n → Bool) :
    bitOracle P x = P.phase x := rfl

omit [Fintype I] in
theorem withAncilla_proj_apply (Q : ProjFamily K I) (i : I) (Ψ : Joint (Fin 2) K) (b : Fin 2) :
    (Q.withAncilla.proj i Ψ) b = ∑ b', minusProj b b' • Q.proj i (Ψ b') := by
  change Joint.kernel minusProj (Joint.fiber (fun _ => Q.proj i) Ψ) b = _
  rw [Joint.kernel_apply]
  rfl

theorem hitProj_withAncilla_apply_zero (Q : ProjFamily K I) (y : I → Bool)
    (Ψ : Joint (Fin 2) K) :
    hitProj Q.withAncilla y Ψ 0 = (1 / 2 : ℂ) • (hitProj Q y (Ψ 0) - hitProj Q y (Ψ 1)) := by
  rw [hitProj_apply, joint_sum_apply, hitProj_apply, hitProj_apply, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [withAncilla_proj_apply, Fin.sum_univ_two]
  simp only [minusProj, Matrix.of_apply]
  norm_num
  module

theorem hitProj_withAncilla_apply_one (Q : ProjFamily K I) (y : I → Bool)
    (Ψ : Joint (Fin 2) K) :
    hitProj Q.withAncilla y Ψ 1 = (1 / 2 : ℂ) • (hitProj Q y (Ψ 1) - hitProj Q y (Ψ 0)) := by
  rw [hitProj_apply, joint_sum_apply, hitProj_apply, hitProj_apply, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [withAncilla_proj_apply, Fin.sum_univ_two]
  simp only [minusProj, Matrix.of_apply]
  norm_num
  module

/-- The phase oracle on ancilla ⊗ `K`, ancilla `0` branch. -/
theorem phase_withAncilla_apply_zero (Q : ProjFamily K I) (y : I → Bool) (Ψ : Joint (Fin 2) K) :
    Q.withAncilla.phase y Ψ 0 = Ψ 0 - hitProj Q y (Ψ 0) + hitProj Q y (Ψ 1) := by
  rw [phase_eq_hitProj]
  change Ψ 0 - ((2 : ℂ) • hitProj Q.withAncilla y Ψ) 0 = _
  rw [PiLp.smul_apply, hitProj_withAncilla_apply_zero]
  module

/-- The phase oracle on ancilla ⊗ `K`, ancilla `1` branch. -/
theorem phase_withAncilla_apply_one (Q : ProjFamily K I) (y : I → Bool) (Ψ : Joint (Fin 2) K) :
    Q.withAncilla.phase y Ψ 1 = Ψ 1 - hitProj Q y (Ψ 1) + hitProj Q y (Ψ 0) := by
  rw [phase_eq_hitProj]
  change Ψ 1 - ((2 : ℂ) • hitProj Q.withAncilla y Ψ) 1 = _
  rw [PiLp.smul_apply, hitProj_withAncilla_apply_one]
  module

/-- The spectator family marks the same part of every spectator copy. -/
theorem hitProj_spectate_apply (Ω : Type*) [Fintype Ω] (Q : ProjFamily K I) (y : I → Bool)
    (v : Joint Ω K) (ω : Ω) : hitProj (Q.spectate Ω) y v ω = hitProj Q y (v ω) := by
  rw [hitProj_apply, joint_sum_apply, hitProj_apply]
  rfl

omit [Fintype I] in
theorem ancillaEmbed_apply_zero (v : K) : ancillaEmbed K v 0 = v := by
  simp [ancillaEmbed]

omit [Fintype I] in
theorem ancillaEmbed_apply_one (v : K) : ancillaEmbed K v 1 = 0 := by
  simp [ancillaEmbed]

omit [Fintype I] in
/-- A controlled family of unitaries is unitary. -/
theorem isUnitary_fiber {J : Type*} [Fintype J] (F : J → K →L[ℂ] K)
    (hF : ∀ j, OracleCircuit.IsUnitary (F j)) : OracleCircuit.IsUnitary (Joint.fiber F) := by
  constructor
  · rw [Joint.star_fiber, Joint.fiber_mul,
      show (fun j => star (F j) * F j) = fun _ => (1 : K →L[ℂ] K) from funext fun j => (hF j).1,
      Joint.fiber_one]
  · rw [Joint.star_fiber, Joint.fiber_mul,
      show (fun j => F j * star (F j)) = fun _ => (1 : K →L[ℂ] K) from funext fun j => (hF j).2,
      Joint.fiber_one]

/-- **Query, controlled gate, unquery.** If the branch gates `G 0`, `G 1` and
the target `V` satisfy the two branch identities, then `O_y (G₀ ⊕ G₁) O_y`
implements `V` on the clean-ancilla encoding. -/
theorem circuit_intertwines (Q : ProjFamily K I) (y : I → Bool) (G : Fin 2 → K →L[ℂ] K)
    (V : K →L[ℂ] K)
    (h0 : ∀ v, G 0 (v - hitProj Q y v) - hitProj Q y (G 0 (v - hitProj Q y v)) +
      hitProj Q y (G 1 (hitProj Q y v)) = V v)
    (h1 : ∀ v, G 1 (hitProj Q y v) - hitProj Q y (G 1 (hitProj Q y v)) +
      hitProj Q y (G 0 (v - hitProj Q y v)) = 0) :
    (Q.withAncilla.phase y * (Joint.fiber G * Q.withAncilla.phase y)) ∘L ancillaEmbed K =
      ancillaEmbed K ∘L V := by
  refine ContinuousLinearMap.ext fun v => PiLp.ext fun b => ?_
  have e0 : Q.withAncilla.phase y (ancillaEmbed K v) 0 = v - hitProj Q y v := by
    rw [phase_withAncilla_apply_zero, ancillaEmbed_apply_zero, ancillaEmbed_apply_one, map_zero,
      add_zero]
  have e1 : Q.withAncilla.phase y (ancillaEmbed K v) 1 = hitProj Q y v := by
    rw [phase_withAncilla_apply_one, ancillaEmbed_apply_zero, ancillaEmbed_apply_one, map_zero,
      sub_zero, zero_add]
  fin_cases b
  · change Q.withAncilla.phase y
      (Joint.fiber G (Q.withAncilla.phase y (ancillaEmbed K v))) 0 = ancillaEmbed K (V v) 0
    rw [phase_withAncilla_apply_zero, Joint.fiber_apply, Joint.fiber_apply, e0, e1,
      ancillaEmbed_apply_zero, h0]
  · change Q.withAncilla.phase y
      (Joint.fiber G (Q.withAncilla.phase y (ancillaEmbed K v))) 1 = ancillaEmbed K (V v) 1
    rw [phase_withAncilla_apply_one, Joint.fiber_apply, Joint.fiber_apply, e0, e1,
      ancillaEmbed_apply_one, h1]

/-- **Two Boolean queries per primitive** (lines 2287-2289): a family `V x`
given, for every input, by the branch identities of `circuit_intertwines` for
one fixed pair of unitary branch gates, is implemented on the clean-ancilla
encoding with two queries to `x ↦ Q.withAncilla.phase (y x)`. -/
theorem implementsOn_circuit {X : Type*} (Q : ProjFamily K I) (y : X → I → Bool)
    (G : Fin 2 → K →L[ℂ] K) (hG : ∀ b, OracleCircuit.IsUnitary (G b)) (V : X → K →L[ℂ] K)
    (h0 : ∀ x v, G 0 (v - hitProj Q (y x) v) - hitProj Q (y x) (G 0 (v - hitProj Q (y x) v)) +
      hitProj Q (y x) (G 1 (hitProj Q (y x) v)) = V x v)
    (h1 : ∀ x v, G 1 (hitProj Q (y x) v) - hitProj Q (y x) (G 1 (hitProj Q (y x) v)) +
      hitProj Q (y x) (G 0 (v - hitProj Q (y x) v)) = 0) :
    EncodedOracle.ImplementsOn (fun x => Q.withAncilla.phase (y x)) V (ancillaEmbed K) 2 :=
  ⟨.seq .query (.seq (.fixed (Joint.fiber G) (isUnitary_fiber G hG)) .query),
    fun x => circuit_intertwines Q (y x) G (V x) (h0 x) (h1 x), le_rfl⟩

omit [Fintype I] in
/-- An input-independent unitary family costs no query on the clean-ancilla
encoding. -/
theorem implementsOn_const {X : Type*} {Q : X → Joint (Fin 2) K →L[ℂ] Joint (Fin 2) K}
    {O : X → K →L[ℂ] K} (x₀ : X) (hO : ∀ x, O x = O x₀) (hU : OracleCircuit.IsUnitary (O x₀)) :
    EncodedOracle.ImplementsOn Q O (ancillaEmbed K) 0 :=
  (EncodedOracle.ImplementsOn.fixed ancillaEmbed_isometry (O x₀) hU).congr fun x => (hO x).symm

omit [Fintype I] in
/-- The same with the fixed unitary named, so that no input `x₀` is needed (the
input type may be empty). -/
theorem implementsOn_of_eq {X : Type*} {Q : X → Joint (Fin 2) K →L[ℂ] Joint (Fin 2) K}
    {O : X → K →L[ℂ] K} (U : K →L[ℂ] K) (hU : OracleCircuit.IsUnitary U) (hO : ∀ x, O x = U) :
    EncodedOracle.ImplementsOn Q O (ancillaEmbed K) 0 :=
  (EncodedOracle.ImplementsOn.fixed ancillaEmbed_isometry U hU).congr fun x => (hO x).symm

end

end SparseLowerBounds.PhaseCircuit
end
