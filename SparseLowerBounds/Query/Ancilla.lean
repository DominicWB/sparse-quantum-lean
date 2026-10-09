import SparseLowerBounds.Query.XorWeight

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Ancilla, spectator and native-label bookkeeping

Instance-independent pieces of the compilation of native sparse primitives to
Boolean queries (manuscript lines 5320-5338 and 2283-2289):

* `ProjFamily.withAncilla`: the family `|−⟩⟨−| ⊗ Q i` on ancilla qubit ⊗ `K`,
  i.e. the XOR form of a Boolean oracle in the Hadamard basis of the response
  qubit;
* `ProjFamily.spectate`: the family `1_Ω ⊗ Q i` with an untouched spectator;
* `ancillaEmbed`: the clean-ancilla encoding `v ↦ |0⟩ ⊗ v`;
* `specOracles`: a native primitive acting on every spectator copy;
* `hardCost`: the Boolean cost of each native label (locations `0`, value `2`)
  and the label-count bookkeeping of `MultiOracleCircuit.Program`.
-/

namespace SparseLowerBounds

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open scoped InnerProduct

/-! ### Ancilla and spectator families -/

/-- `|−⟩⟨−|` on the ancilla qubit. -/
def minusProj : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun a b => if a = b then 1 / 2 else -1 / 2

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {I : Type*}

theorem minusProj_mul_self : minusProj * minusProj = minusProj := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [minusProj, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem minusProj_conjTranspose : minusProj.conjTranspose = minusProj := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [minusProj, Matrix.conjTranspose_apply]

theorem isStarProjection_kernel_minusProj :
    IsStarProjection (Joint.kernel minusProj : Joint (Fin 2) K →L[ℂ] Joint (Fin 2) K) :=
  ⟨show _ * _ = _ by rw [Joint.kernel_mul, minusProj_mul_self],
   show star _ = _ by rw [Joint.star_kernel, minusProj_conjTranspose]⟩

omit [CompleteSpace K] in
theorem fiber_zero {J : Type*} [Fintype J] :
    (Joint.fiber (fun _ : J => (0 : K →L[ℂ] K)) : Joint J K →L[ℂ] Joint J K) = 0 := by
  ext Ψ j
  simp [Joint.fiber_apply]

theorem isStarProjection_fiber_const {J : Type*} [Fintype J] {A : K →L[ℂ] K}
    (hA : IsStarProjection A) :
    IsStarProjection (Joint.fiber (fun _ : J => A) : Joint J K →L[ℂ] Joint J K) :=
  ⟨show _ * _ = _ by rw [Joint.fiber_mul, hA.isIdempotentElem.eq],
   show star _ = _ by rw [Joint.star_fiber, hA.isSelfAdjoint.star_eq]⟩

/-- The family `|−⟩⟨−| ⊗ Q i` on ancilla ⊗ `K`. -/
def ProjFamily.withAncilla (Q : ProjFamily K I) : ProjFamily (Joint (Fin 2) K) I where
  proj i := Joint.kernel minusProj * Joint.fiber (fun _ => Q.proj i)
  isStarProjection i :=
    isStarProjection_kernel_minusProj.mul (isStarProjection_fiber_const (Q.isStarProjection i))
      (Joint.kernel_comm_fiber_const _ _)
  orthogonal i i' h := by
    show Joint.kernel minusProj * Joint.fiber (fun _ => Q.proj i) *
      (Joint.kernel minusProj * Joint.fiber (fun _ => Q.proj i')) = 0
    rw [mul_assoc, ← mul_assoc (Joint.fiber _), ← Joint.kernel_comm_fiber_const, mul_assoc,
      Joint.fiber_mul, Q.orthogonal i i' h, fiber_zero, mul_zero, mul_zero]

/-- The family `1_Ω ⊗ Q i` on spectator ⊗ `K`. -/
def ProjFamily.spectate (Ω : Type*) [Fintype Ω] (Q : ProjFamily K I) : ProjFamily (Joint Ω K) I where
  proj i := Joint.fiber (fun _ => Q.proj i)
  isStarProjection i := isStarProjection_fiber_const (Q.isStarProjection i)
  orthogonal i i' h := by
    show Joint.fiber _ * Joint.fiber _ = 0
    rw [Joint.fiber_mul, Q.orthogonal i i' h, fiber_zero]

/-- The clean-ancilla encoding `v ↦ |0⟩ ⊗ v`. -/
def ancillaEmbed (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    K →L[ℂ] Joint (Fin 2) K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun b => if b = 0 then ContinuousLinearMap.id ℂ K else 0)

theorem ancillaEmbed_apply (v : K) (b : Fin 2) :
    ancillaEmbed K v b = if b = 0 then v else 0 := by
  change (if b = 0 then ContinuousLinearMap.id ℂ K else 0) v = _
  split_ifs <;> rfl

theorem ancillaEmbed_isometry : (ancillaEmbed K)† ∘L ancillaEmbed K = 1 := by
  ext v
  refine ext_inner_left ℂ fun w => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    PiLp.inner_apply, Fin.sum_univ_two]
  simp only [ancillaEmbed_apply]
  simp

/-- A primitive acting on every spectator copy: `1_Ω ⊗ O`. -/
def specOracles (Ω : Type*) [Fintype Ω] {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z]
    [AddCommGroup Z] {s : ℕ} (D : Data X n Z s) (l : Query) (x : X) :
    Joint Ω (SparseFlagEmbedding.Space (n × n) Z) →L[ℂ] Joint Ω (SparseFlagEmbedding.Space (n × n) Z) :=
  Joint.fiber fun _ => oracles D l x

theorem specOracles_unitary (Ω : Type*) [Fintype Ω] {X n Z : Type*} [Fintype n] [DecidableEq n]
    [Fintype Z] [AddCommGroup Z] {s : ℕ} (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (specOracles Ω D l x) := by
  have h := oracles_unitary D l x
  exact ⟨by simp only [specOracles, Joint.star_fiber, Joint.fiber_mul, h.1, Joint.fiber_one],
    by simp only [specOracles, Joint.star_fiber, Joint.fiber_mul, h.2, Joint.fiber_one]⟩

/-! ### Query costs -/

/-- Boolean cost of each native label: locations `0`, value `2`. -/
def hardCost : Query → ℕ
  | .rowLocation => 0
  | .columnLocation => 0
  | .value => 2

/-- A program's Boolean cost is twice its number of value queries. -/
theorem cost_hardCost {X : Type*} {O : Query → X → K →L[ℂ] K} (p : MultiOracleCircuit.Program O) :
    p.cost hardCost = 2 * p.labelCount .value := by
  induction p with
  | fixed U hU => rfl
  | query l => cases l <;> rfl
  | queryAdjoint l => cases l <;> rfl
  | seq p q hp hq =>
      rw [MultiOracleCircuit.Program.cost_seq, MultiOracleCircuit.Program.labelCount_seq, hp, hq,
        Nat.mul_add]

theorem labelCount_le_count {X L : Type*} [DecidableEq L] {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (l : L) : p.labelCount l ≤ p.count :=
  calc p.labelCount l = p.cost (fun k => if k = l then 1 else 0) := rfl
    _ ≤ p.cost (fun _ => 1) := p.cost_mono fun k => by split_ifs <;> omega
    _ = p.count := by rw [MultiOracleCircuit.Program.cost_const, mul_one]

end

end SparseLowerBounds
end
