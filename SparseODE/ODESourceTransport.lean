import SparseODE.ODESourceControls

/-!
# Canonical source and matrix sectors with a fixed routing unitary

Source calls act on the logical source register itself, while matrix calls
act on the native physical register. The direct-sum sector is a control bit.
The routing gate depends only on the known clean encoding, never on either
unknown oracle. Thus no arbitrary encoded source operation is made primitive.
The exact matrix counts below are for the sector-controlled native family;
connecting these controls to original native calls is a separate constant-cost
compiler obligation. Source controls are supplied in the access model.
-/

namespace SparseHamiltonian.ODESourceTransport

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {B K : Type*}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Space (B K : Type*) := WithLp 2 (B × K)

def sourceEmbedding : B →L[ℂ] Space B K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ B K).symm.toContinuousLinearMap ∘L
    (1 : B →L[ℂ] B).prod (0 : B →L[ℂ] K)

def matrixEmbedding : K →L[ℂ] Space B K :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ B K).symm.toContinuousLinearMap ∘L
    (0 : K →L[ℂ] B).prod (1 : K →L[ℂ] K)

omit [CompleteSpace B] [CompleteSpace K] in
@[simp] theorem sourceEmbedding_apply (b : B) :
    (sourceEmbedding : B →L[ℂ] Space B K) b = WithLp.toLp 2 (b, 0) := rfl

omit [CompleteSpace B] [CompleteSpace K] in
@[simp] theorem matrixEmbedding_apply (k : K) :
    (matrixEmbedding : K →L[ℂ] Space B K) k = WithLp.toLp 2 (0, k) := rfl

@[simp] theorem sourceEmbedding_adjoint_apply (v : Space B K) :
    ((sourceEmbedding : B →L[ℂ] Space B K)†) v = v.fst := by
  apply ext_inner_right ℂ
  intro b
  simp only [adjoint_inner_left, sourceEmbedding_apply, WithLp.prod_inner_apply,
    WithLp.fst, inner_zero_right, add_zero]

@[simp] theorem matrixEmbedding_adjoint_apply (v : Space B K) :
    ((matrixEmbedding : K →L[ℂ] Space B K)†) v = v.snd := by
  apply ext_inner_right ℂ
  intro k
  simp only [adjoint_inner_left, matrixEmbedding_apply, WithLp.prod_inner_apply,
    WithLp.snd, inner_zero_right, zero_add]

theorem sourceEmbedding_isometry :
    (sourceEmbedding : B →L[ℂ] Space B K)† ∘L sourceEmbedding = 1 := by
  ext b
  simp only [comp_apply, sourceEmbedding_adjoint_apply, sourceEmbedding_apply,
    WithLp.fst, one_def, id_apply]

theorem matrixEmbedding_isometry :
    (matrixEmbedding : K →L[ℂ] Space B K)† ∘L matrixEmbedding = 1 := by
  ext k
  simp only [comp_apply, matrixEmbedding_adjoint_apply, matrixEmbedding_apply,
    WithLp.snd, one_def, id_apply]

/-- Source access in its own canonical sector, controlled by the sector bit. -/
def sourceGate (S : B →L[ℂ] B) : Space B K →L[ℂ] Space B K :=
  SubspaceOracle.lift sourceEmbedding S

/-- Native matrix access in its own canonical sector. -/
def matrixGate (U : K →L[ℂ] K) : Space B K →L[ℂ] Space B K :=
  SubspaceOracle.lift matrixEmbedding U

@[simp] theorem sourceGate_apply (S : B →L[ℂ] B) (v : Space B K) :
    sourceGate S v = WithLp.toLp 2 (S v.fst, v.snd) := by
  simp only [sourceGate, SubspaceOracle.lift, add_apply, one_def, id_apply,
    comp_apply, sourceEmbedding_adjoint_apply, sub_apply, sourceEmbedding_apply]
  change WithLp.toLp 2
    (v.fst + (S v.fst - v.fst), v.snd + 0) = _
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · abel
  · exact add_zero _

@[simp] theorem matrixGate_apply (U : K →L[ℂ] K) (v : Space B K) :
    matrixGate U v = WithLp.toLp 2 (v.fst, U v.snd) := by
  simp only [matrixGate, SubspaceOracle.lift, add_apply, one_def, id_apply,
    comp_apply, matrixEmbedding_adjoint_apply, sub_apply, matrixEmbedding_apply]
  change WithLp.toLp 2
    (v.fst + 0, v.snd + (U v.snd - v.snd)) = _
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · exact add_zero _
  · abel

theorem sourceGate_adjoint (S : B →L[ℂ] B) :
    (sourceGate (K := K) S)† = sourceGate (K := K) (S†) := by
  ext v
  apply ext_inner_right ℂ
  intro u
  simp only [adjoint_inner_left, sourceGate_apply, WithLp.prod_inner_apply,
    WithLp.fst, WithLp.snd, adjoint_inner_left]

theorem matrixGate_adjoint (U : K →L[ℂ] K) :
    (matrixGate (B := B) U)† = matrixGate (B := B) (U†) := by
  ext v
  apply ext_inner_right ℂ
  intro u
  simp only [adjoint_inner_left, matrixGate_apply, WithLp.prod_inner_apply,
    WithLp.fst, WithLp.snd, adjoint_inner_left]

theorem sourceGate_unitary (S : B →L[ℂ] B) (hS : IsUnitary S) :
    IsUnitary (sourceGate (K := K) S) := by
  have hLeft (b : B) : (S†) (S b) = b :=
    congrArg (fun A : B →L[ℂ] B => A b) hS.1
  have hRight (b : B) : S ((S†) b) = b :=
    congrArg (fun A : B →L[ℂ] B => A b) hS.2
  change (sourceGate (K := K) S)† ∘L sourceGate S = 1 ∧
    sourceGate S ∘L (sourceGate (K := K) S)† = 1
  rw [sourceGate_adjoint]
  constructor
  · ext v
    simp only [comp_apply, sourceGate_apply, WithLp.fst, WithLp.snd,
      hLeft, one_def, id_apply]
  · ext v
    simp only [comp_apply, sourceGate_apply, WithLp.fst, WithLp.snd,
      hRight, one_def, id_apply]

theorem matrixGate_unitary (U : K →L[ℂ] K) (hU : IsUnitary U) :
    IsUnitary (matrixGate (B := B) U) := by
  have hLeft (k : K) : (U†) (U k) = k :=
    congrArg (fun A : K →L[ℂ] K => A k) hU.1
  have hRight (k : K) : U ((U†) k) = k :=
    congrArg (fun A : K →L[ℂ] K => A k) hU.2
  change (matrixGate (B := B) U)† ∘L matrixGate U = 1 ∧
    matrixGate U ∘L (matrixGate (B := B) U)† = 1
  rw [matrixGate_adjoint]
  constructor
  · ext v
    simp only [comp_apply, matrixGate_apply, WithLp.fst, WithLp.snd,
      hLeft, one_def, id_apply]
  · ext v
    simp only [comp_apply, matrixGate_apply, WithLp.fst, WithLp.snd,
      hRight, one_def, id_apply]

theorem sourceGate_source (S : B →L[ℂ] B) :
    sourceGate (K := K) S ∘L sourceEmbedding = sourceEmbedding ∘L S := by
  ext b
  simp only [comp_apply, sourceEmbedding_apply, sourceGate_apply,
    WithLp.fst, WithLp.snd]

theorem matrixGate_matrix (U : K →L[ℂ] K) :
    matrixGate (B := B) U ∘L matrixEmbedding = matrixEmbedding ∘L U := by
  ext k
  simp only [comp_apply, matrixEmbedding_apply, matrixGate_apply,
    WithLp.fst, WithLp.snd]

theorem matrixGate_mul (U V : K →L[ℂ] K) :
    matrixGate (B := B) (U * V) = matrixGate (B := B) U * matrixGate V := by
  change matrixGate (U ∘L V) = matrixGate U ∘L matrixGate V
  ext v
  simp only [comp_apply, matrixGate_apply, WithLp.fst, WithLp.snd]

/-- Explicit Julia completion of the known clean encoding. -/
def route (E : B →L[ℂ] K) : Space B K →L[ℂ] Space B K :=
  GlobalColligation.blockMap (0 : B →L[ℂ] B) (E†) E
    (1 - E ∘L E†)

@[simp] theorem route_apply (E : B →L[ℂ] K) (v : Space B K) :
    route E v = WithLp.toLp 2
      ((E†) v.snd, E v.fst + (v.snd - E ((E†) v.snd))) := by
  simp only [route, GlobalColligation.blockMap_apply, zero_apply, zero_add,
    sub_apply, one_def, id_apply, comp_apply]

theorem route_selfAdjoint (E : B →L[ℂ] K) : (route E)† = route E := by
  ext v
  apply ext_inner_right ℂ
  intro u
  simp only [adjoint_inner_left, route_apply, WithLp.prod_inner_apply,
    WithLp.fst, WithLp.snd, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, adjoint_inner_left, adjoint_inner_right]
  have h : inner ℂ v.snd (E ((E†) u.snd)) =
      inner ℂ (E ((E†) v.snd)) u.snd := by
    rw [← adjoint_inner_left E, adjoint_inner_right E]
  simp only [WithLp.snd] at h
  rw [h]
  ring

theorem route_involution (E : B →L[ℂ] K) (hE : E† ∘L E = 1)
    (v : Space B K) : route E (route E v) = v := by
  have hEv (b : B) : (E†) (E b) = b :=
    congrArg (fun A : B →L[ℂ] B => A b) hE
  rw [route_apply, route_apply]
  change WithLp.toLp 2
    ((E†) (E v.fst + (v.snd - E ((E†) v.snd))),
      E ((E†) v.snd) +
        (E v.fst + (v.snd - E ((E†) v.snd)) -
          E ((E†) (E v.fst + (v.snd - E ((E†) v.snd)))))) = v
  have hPair :
      ((E†) (E v.fst + (v.snd - E ((E†) v.snd))),
        E ((E†) v.snd) +
          (E v.fst + (v.snd - E ((E†) v.snd)) -
            E ((E†) (E v.fst + (v.snd - E ((E†) v.snd)))))) =
        (v.fst, v.snd) := by
    apply Prod.ext <;> simp only [map_add, map_sub, hEv] <;> abel
  exact congrArg (WithLp.toLp 2) hPair

theorem route_unitary (E : B →L[ℂ] K) (hE : E† ∘L E = 1) :
    IsUnitary (route E) := by
  have hsq : route E ∘L route E = 1 := by
    ext v
    exact route_involution E hE v
  change (route E)† ∘L route E = 1 ∧ route E ∘L (route E)† = 1
  rw [route_selfAdjoint]
  exact ⟨hsq, hsq⟩

theorem route_source (E : B →L[ℂ] K) :
    route E ∘L sourceEmbedding = matrixEmbedding ∘L E := by
  ext b
  simp only [comp_apply, sourceEmbedding_apply, route_apply, WithLp.fst,
    WithLp.snd, map_zero, sub_zero, add_zero, matrixEmbedding_apply]

theorem route_encoded (E : B →L[ℂ] K) (hE : E† ∘L E = 1) :
    route E ∘L matrixEmbedding ∘L E = sourceEmbedding := by
  have hEv (b : B) : (E†) (E b) = b :=
    congrArg (fun A : B →L[ℂ] B => A b) hE
  ext b
  simp only [comp_apply, matrixEmbedding_apply, route_apply, WithLp.fst,
    WithLp.snd, hEv, map_zero, sub_self, add_zero, sourceEmbedding_apply]

variable {X L : Type*}

def matrixOracle (O : L → X → K →L[ℂ] K) (l : L) (x : X) :
    Space B K →L[ℂ] Space B K := matrixGate (O l x)

def matrixProgram {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) :
    MultiOracleCircuit.Program (matrixOracle (B := B) O) :=
  EncodedMultiOracle.liftProgram matrixEmbedding matrixEmbedding_isometry p

theorem matrixProgram_cost {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (matrixProgram (B := B) p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (matrixProgram (B := B) p).cost w +
        (matrixProgram (B := B) q).cost w = p.cost w + q.cost w
      rw [hp, hq]

theorem matrixProgram_count {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) :
    (matrixProgram (B := B) p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (matrixProgram (B := B) p).count +
        (matrixProgram (B := B) q).count = p.count + q.count
      rw [hp, hq]

/-- Structural evaluation avoids unfolding the entire encoded compiler at
the product-space type. -/
theorem matrixProgram_eval_eq {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (x : X) :
    (matrixProgram (B := B) p).eval x = matrixGate (B := B) (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact matrixGate_adjoint (B := B) (O l x)
  | seq p q hp hq =>
      change (matrixProgram (B := B) p).eval x *
        (matrixProgram (B := B) q).eval x =
          matrixGate (B := B) (p.eval x * q.eval x)
      rw [hp, hq, matrixGate_mul]

theorem matrixProgram_eval {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (_hO : ∀ l x, IsUnitary (O l x)) (x : X) :
    (matrixProgram (B := B) p).eval x ∘L matrixEmbedding =
      matrixEmbedding ∘L p.eval x := by
  rw [matrixProgram_eval_eq]
  exact matrixGate_matrix (B := B) (p.eval x)

/-- The concrete routed call agrees with logical source preparation on the
native clean encoding. The two routing gates are known and query-free. -/
theorem routed_source (E : B →L[ℂ] K) (hE : E† ∘L E = 1)
    (S : B →L[ℂ] B) :
    route E ∘L sourceGate S ∘L route E ∘L matrixEmbedding ∘L E =
      matrixEmbedding ∘L E ∘L S := by
  have hEv (b : B) : (E†) (E b) = b :=
    congrArg (fun A : B →L[ℂ] B => A b) hE
  ext b
  simp only [comp_apply, matrixEmbedding_apply, route_apply, sourceGate_apply,
    WithLp.fst, WithLp.snd, hEv, map_zero, sub_self, add_zero]

end
end SparseHamiltonian.ODESourceTransport
