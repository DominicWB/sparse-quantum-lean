import SparseLowerBounds.LinearSystems.Gadget
import SparseLowerBounds.Query.Reduction

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helper: the query–gate–unquery circuit on the clean-ancilla encoding

Generic facts of the compilation of native queries to Boolean queries:

* `hitProj Q j = Σ_{(k,a) : j k = a} Q (k, a)`, the part of the workspace that
  the one-hot input `j` marks;
* the one-hot oracle of `Q.withAncilla` acts on ancilla ⊗ `K` as
  `(Ψ₀, Ψ₁) ↦ ((1 - S) Ψ₀ + S Ψ₁, S Ψ₀ + (1 - S) Ψ₁)` with `S = hitProj Q j`,
  i.e. as Pauli `X` on the ancilla controlled by `S`;
* the circuit `O_j · (G₀ ⊕ G₁) · O_j` maps the encoding `v ↦ |0⟩ ⊗ v` to the
  encoding of `V v` whenever `V` is given by the two branch identities
  `circuit_intertwines`;
* a family that is constant in the input costs no query.
-/

namespace SparseLowerBounds.Helpers.CompileReduction

noncomputable section
open SparseHamiltonian OracleCircuit

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {n m : ℕ}

omit [CompleteSpace K] in
theorem joint_sum_apply {J : Type*} [Fintype J] {ι : Type*} (s : Finset ι)
    (f : ι → Joint J K) (b : J) : (∑ i ∈ s, f i) b = ∑ i ∈ s, f i b :=
  map_sum (Joint.proj (K := K) b) f s

/-- The part of the workspace marked by the one-hot input `j`. -/
def hitProj {K' : Type*} [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
    (Q : ProjFamily K' (Fin n × Fin m)) (j : Fin n → Fin m) : K' →L[ℂ] K' :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n × Fin m => decide (j i.1 = i.2) = true), Q.proj i

theorem hitProj_apply (Q : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) (v : K) :
    hitProj Q j v =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n × Fin m => decide (j i.1 = i.2) = true),
        Q.proj i v := by
  simp only [hitProj, _root_.sum_apply]

theorem oneHotOracle_eq_hitProj (Q : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m) :
    oneHotOracle Q j = 1 - (2 : ℂ) • hitProj Q j := rfl

theorem withAncilla_proj_apply (Q : ProjFamily K (Fin n × Fin m)) (i : Fin n × Fin m)
    (Ψ : Joint (Fin 2) K) (b : Fin 2) :
    (Q.withAncilla.proj i Ψ) b = ∑ b', minusProj b b' • Q.proj i (Ψ b') := by
  change Joint.kernel minusProj (Joint.fiber (fun _ => Q.proj i) Ψ) b = _
  rw [Joint.kernel_apply]
  rfl

theorem hitProj_withAncilla_apply_zero (Q : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m)
    (Ψ : Joint (Fin 2) K) :
    hitProj Q.withAncilla j Ψ 0 = (1 / 2 : ℂ) • (hitProj Q j (Ψ 0) - hitProj Q j (Ψ 1)) := by
  rw [hitProj_apply, joint_sum_apply, hitProj_apply, hitProj_apply, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [withAncilla_proj_apply, Fin.sum_univ_two]
  simp only [minusProj, Matrix.of_apply]
  norm_num
  module

theorem hitProj_withAncilla_apply_one (Q : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m)
    (Ψ : Joint (Fin 2) K) :
    hitProj Q.withAncilla j Ψ 1 = (1 / 2 : ℂ) • (hitProj Q j (Ψ 1) - hitProj Q j (Ψ 0)) := by
  rw [hitProj_apply, joint_sum_apply, hitProj_apply, hitProj_apply, ← Finset.sum_sub_distrib,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [withAncilla_proj_apply, Fin.sum_univ_two]
  simp only [minusProj, Matrix.of_apply]
  norm_num
  module

/-- The one-hot oracle on ancilla ⊗ `K`, ancilla `0` branch. -/
theorem oneHot_withAncilla_apply_zero (Q : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m)
    (Ψ : Joint (Fin 2) K) :
    oneHotOracle Q.withAncilla j Ψ 0 = Ψ 0 - hitProj Q j (Ψ 0) + hitProj Q j (Ψ 1) := by
  rw [oneHotOracle_eq_hitProj]
  change Ψ 0 - ((2 : ℂ) • hitProj Q.withAncilla j Ψ) 0 = _
  rw [PiLp.smul_apply, hitProj_withAncilla_apply_zero]
  module

/-- The one-hot oracle on ancilla ⊗ `K`, ancilla `1` branch. -/
theorem oneHot_withAncilla_apply_one (Q : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m)
    (Ψ : Joint (Fin 2) K) :
    oneHotOracle Q.withAncilla j Ψ 1 = Ψ 1 - hitProj Q j (Ψ 1) + hitProj Q j (Ψ 0) := by
  rw [oneHotOracle_eq_hitProj]
  change Ψ 1 - ((2 : ℂ) • hitProj Q.withAncilla j Ψ) 1 = _
  rw [PiLp.smul_apply, hitProj_withAncilla_apply_one]
  module

/-- The spectator family marks the same part of every spectator copy. -/
theorem hitProj_spectate_apply (Ω : Type*) [Fintype Ω] (Q : ProjFamily K (Fin n × Fin m))
    (j : Fin n → Fin m) (v : Joint Ω K) (ω : Ω) :
    hitProj (Q.spectate Ω) j v ω = hitProj Q j (v ω) := by
  rw [hitProj_apply, joint_sum_apply, hitProj_apply]
  rfl

theorem ancillaEmbed_apply_zero (v : K) : ancillaEmbed K v 0 = v := by
  simp [ancillaEmbed]

theorem ancillaEmbed_apply_one (v : K) : ancillaEmbed K v 1 = 0 := by
  simp [ancillaEmbed]

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
the target `V` satisfy the two branch identities, then `O_j (G₀ ⊕ G₁) O_j`
implements `V` on the clean-ancilla encoding. -/
theorem circuit_intertwines (Q : ProjFamily K (Fin n × Fin m)) (j : Fin n → Fin m)
    (G : Fin 2 → K →L[ℂ] K) (V : K →L[ℂ] K)
    (h0 : ∀ v, G 0 (v - hitProj Q j v) - hitProj Q j (G 0 (v - hitProj Q j v)) +
      hitProj Q j (G 1 (hitProj Q j v)) = V v)
    (h1 : ∀ v, G 1 (hitProj Q j v) - hitProj Q j (G 1 (hitProj Q j v)) +
      hitProj Q j (G 0 (v - hitProj Q j v)) = 0) :
    (oneHotOracle Q.withAncilla j * (Joint.fiber G * oneHotOracle Q.withAncilla j)) ∘L
      ancillaEmbed K = ancillaEmbed K ∘L V := by
  refine ContinuousLinearMap.ext fun v => PiLp.ext fun b => ?_
  have e0 : oneHotOracle Q.withAncilla j (ancillaEmbed K v) 0 = v - hitProj Q j v := by
    rw [oneHot_withAncilla_apply_zero, ancillaEmbed_apply_zero, ancillaEmbed_apply_one, map_zero,
      add_zero]
  have e1 : oneHotOracle Q.withAncilla j (ancillaEmbed K v) 1 = hitProj Q j v := by
    rw [oneHot_withAncilla_apply_one, ancillaEmbed_apply_zero, ancillaEmbed_apply_one, map_zero,
      sub_zero, zero_add]
  fin_cases b
  · change oneHotOracle Q.withAncilla j
      (Joint.fiber G (oneHotOracle Q.withAncilla j (ancillaEmbed K v))) 0 = ancillaEmbed K (V v) 0
    rw [oneHot_withAncilla_apply_zero, Joint.fiber_apply, Joint.fiber_apply, e0, e1,
      ancillaEmbed_apply_zero, h0]
  · change oneHotOracle Q.withAncilla j
      (Joint.fiber G (oneHotOracle Q.withAncilla j (ancillaEmbed K v))) 1 = ancillaEmbed K (V v) 1
    rw [oneHot_withAncilla_apply_one, Joint.fiber_apply, Joint.fiber_apply, e0, e1,
      ancillaEmbed_apply_one, h1]

/-- An input-independent unitary family costs no query on the clean-ancilla
encoding. -/
theorem implementsOn_const {X : Type*} {Q : X → Joint (Fin 2) K →L[ℂ] Joint (Fin 2) K}
    {O : X → K →L[ℂ] K} (x₀ : X) (hO : ∀ x, O x = O x₀) (hU : OracleCircuit.IsUnitary (O x₀)) :
    EncodedOracle.ImplementsOn Q O (ancillaEmbed K) 0 :=
  (EncodedOracle.ImplementsOn.fixed ancillaEmbed_isometry (O x₀) hU).congr fun x => (hO x).symm

end

end SparseLowerBounds.Helpers.CompileReduction
end
