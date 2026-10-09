import LinearSystemLowerBound.Theorem
import SparseLinearSystems.Endpoint.Main

/-!
# The upper bound's algorithm is admissible: a matching characterisation

The released algorithm of Theorem `qls:thm:main` (`SparseLinearSystems.Endpoint.algorithm`)
is an adaptive protocol over the physical oracle family `physOracle D Ub T`: native sparse
queries in a fixed layout with branch, control, dummy and reference registers as spectators,
and the controlled right-hand-side preparation.  Native calls are closed under fixed layouts
(`NativeCall.conj`), spectator branches (`NativeCall.diagonal`, `NativeCall.masked_true`,
`NativeCall.spectator`), so every matrix label of `physOracle` is a native call
(`nativeCall_physOracle`), and for an input-independent right-hand side every label is
admissible with the weights `wMat` (`physOracle_admissible`).

On the hard family both theorems therefore apply to one and the same algorithm
(`upper_meets_lower`):

`κ √s ln(1/ε) / 1536 < worstCost wMat ≤ 4·10¹² √s κ ln(1/ε)`,

and no admissible algorithm achieves fewer than `κ √s ln(1/ε) / 1536` queries.
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix
open SparseHamiltonian SparseLinearSystems.Protocol LinearSystemLowerBound.Hard
  LinearSystemLowerBound.Params LinearSystemLowerBound.Native

namespace Native

variable {n m : ℕ} {N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- A space as a single spectator branch. -/
def unitLayout (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    V ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Unit => V) where
  toFun v := WithLp.toLp 2 (fun _ => v)
  invFun w := w ()
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv w := by ext u; rfl
  norm_map' v := by
    have h : ‖(WithLp.toLp 2 (fun _ : Unit => v) : PiLp 2 (fun _ : Unit => V))‖ ^ 2 = ‖v‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- A single native query (or its inverse, or the identity) is a native call. -/
theorem nativeCall_callOp (D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s)
    (c : Option (NativeSparseBlockEncoding.Query × Bool)) :
    NativeCall D (fun x => callOp D c x) := by
  refine ⟨Unit, inferInstance, unitLayout (NSpace N Z), fun _ => c, fun x => ?_⟩
  ext v
  rfl

variable {K K' : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

/-- Native calls are closed under fixed isometric layouts. -/
theorem NativeCall.conj {D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s}
    {O : (Fin n → Fin m) → K →L[ℂ] K} (h : NativeCall D O) (Φ : K ≃ₗᵢ[ℂ] K') :
    NativeCall D (fun x => Φ.conjStarAlgEquiv (O x)) := by
  obtain ⟨S, hS, ℓ, call, hO⟩ := h
  refine ⟨S, hS, Φ.symm.trans ℓ, call, fun x => ?_⟩
  ext v
  simp [hO, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- Native calls are closed under uniform spectator branches. -/
theorem NativeCall.diagonal {D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s}
    {O : (Fin n → Fin m) → K →L[ℂ] K} (h : NativeCall D O) (ι : Type) [Fintype ι] :
    NativeCall D (fun x => WeightedClock.diagonal (fun _ : ι => O x)) := by
  obtain ⟨S, hS, ℓ, call, hO⟩ := h
  refine ⟨Σ _ : ι, S, inferInstance,
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : ι => ℓ)).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : ι) (_ : S) => NSpace N Z)).symm,
    fun σ => call σ.2, fun x => ?_⟩
  ext v i
  simp only [hO, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, WeightedClock.diagonal_apply]
  rfl

theorem NativeCall.masked_true {D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s}
    {O : (Fin n → Fin m) → K →L[ℂ] K} (h : NativeCall D O) (ι : Type) [Fintype ι] :
    NativeCall D (fun x => MaskedProgram.masked (fun _ : ι => true) (O x)) := by
  have e : (fun x => MaskedProgram.masked (fun _ : ι => true) (O x)) =
      fun x => WeightedClock.diagonal (fun _ : ι => O x) := by
    funext x
    simp only [MaskedProgram.masked, if_true]
  rw [e]
  exact h.diagonal ι

theorem NativeCall.spectator {D : NativeSparseBlockEncoding.Data (Fin n → Fin m) N Z s}
    {B : Type} [Fintype B]
    {O : (Fin n → Fin m) → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} (h : NativeCall D O)
    (S₀ : Type) [Fintype S₀] :
    NativeCall D (fun x => LookupFromBasisOracle.spectator (S := S₀) (O x)) :=
  (h.diagonal S₀).conj (RegisterEquivalences.productFlatten S₀ B)

end Native

/-! ### The upper bound's physical oracles -/

section Physical

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

omit [DecidableEq Z] in
/-- **Every matrix label of the upper bound's physical oracle family is a native call.** -/
theorem nativeCall_physOracle {nH mH : ℕ}
    (D : NativeSparseBlockEncoding.Data (Fin nH → Fin mH) n Z s)
    (Ub : (Fin nH → Fin mH) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (T : ℕ)
    (q : NativeSparseBlockEncoding.Query) :
    NativeCall (K := SparseLinearSystems.Step.Phys n Z T) D
      (SparseLinearSystems.Step.physOracle D Ub T (Sum.inl q)) := by
  have h0 := nativeCall_callOp D (some (q, false))
  have h1 := h0.conj (NativeSparseMaskedAccess.layout (n := n) (Z := Z))
  have h2 := (h1.spectator ((Bool × NativeSparseMaskedAccess.Basis n Z) ×
    NativeSparseMaskedAccess.Basis n Z)).masked_true Bool
  have h3 := h2.conj (NativeDilationLayout.layout (B := NativeSparseMaskedAccess.Basis n Z))
  have h4 := (h3.spectator ((Bool × NativeCayleyProgram.Basis n Z) ×
    NativeCayleyProgram.Basis n Z)).masked_true (SparseLinearSystems.Step.Idx T)
  exact h4

omit [DecidableEq Z] in
/-- **The upper bound's oracle family is admissible** for an input-independent right-hand
side, with weight one for every native label and zero for the source. -/
theorem physOracle_admissible {nH mH : ℕ}
    (D : NativeSparseBlockEncoding.Data (Fin nH → Fin mH) n Z s)
    (Ub : (Fin nH → Fin mH) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hUb : ∀ x, OracleCircuit.IsUnitary (Ub x)) (hconst : ∀ x x', Ub x = Ub x') (T : ℕ)
    (l : SparseLinearSystems.Step.Lbl) :
    Admissible (K := SparseLinearSystems.Step.Phys n Z T) D
      (SparseLinearSystems.Step.physOracle D Ub T l) (SparseLinearSystems.Step.wMat l) := by
  rcases l with q | u
  · exact Or.inl ⟨nativeCall_physOracle D Ub T q, le_rfl⟩
  · refine Or.inr ⟨fun x x' => ?_, fun x => ?_⟩
    · change SparseLinearSystems.Source.sourceOracle Ub x =
        SparseLinearSystems.Source.sourceOracle Ub x'
      simp only [SparseLinearSystems.Source.sourceOracle, hconst x x']
    · exact SparseLinearSystems.Step.physOracle_unitary D Ub hUb T (Sum.inr u) x

end Physical

/-! ### The characterisation on the hard family -/

section Characterisation

set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000

/-- **Upper and lower bounds meet on the hard family.**  For the hard native data, the
identity as right-hand-side preparation and the public reference state `b`, the released
algorithm of Theorem `qls:thm:main` solves every instance, it is an adaptive protocol over
admissible labels with a clean output, so it satisfies the hypotheses of `lower_bound_sharp`
(through `lower_bound_sharp_clean`), and its worst-case number of native queries satisfies
`κ √s ln(1/ε) / 1536 < Q ≤ 4·10¹² √s κ ln(1/ε)`. -/
theorem upper_meets_lower (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) :
    ∃ D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) (ZMod 8) s,
      D.matrix = family κ ε s ∧
      (∀ x, SparseLinearSystems.Endpoint.Promise D κ x) ∧
      (∀ x, SparseLinearSystems.Endpoint.solutionState D (fun _ => 1) (rhsVec κ ε s) x =
        target κ ε s x) ∧
      κ * Real.sqrt s * Real.log (1 / ε) / 1536 <
        (SparseLinearSystems.Endpoint.algorithm D (fun _ => 1) (rhsVec κ ε s) κ ε).worstCost
          SparseLinearSystems.Step.wMat ∧
      ((SparseLinearSystems.Endpoint.algorithm D (fun _ => 1) (rhsVec κ ε s) κ ε).worstCost
          SparseLinearSystems.Step.wMat : ℝ) ≤
        4 * 10 ^ 12 * Real.sqrt s * κ * Real.log (1 / ε) := by
  obtain ⟨D, hDm, hrow, hcol, enc, henc⟩ := exists_access κ ε s hκ hs hε hε1
  have hprom : ∀ x, SparseLinearSystems.Endpoint.Promise D κ x := by
    intro x
    obtain ⟨h1, h2, h3⟩ := family_promise κ ε s hκ x
    refine ⟨?_, ?_, ?_⟩
    · change ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1
      rw [hDm]; exact h1
    · change IsUnit (SparseStateOverlap.matrixOperator (D.matrix x))
      rw [hDm]; exact h2
    · change ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ κ
      rw [hDm]; exact h3
  have hsol : ∀ x, SparseLinearSystems.Endpoint.solutionState D (fun _ => 1) (rhsVec κ ε s) x =
      target κ ε s x := by
    intro x
    change ODEStateNormalization.unitDirection (Ring.inverse
      (SparseStateOverlap.matrixOperator (D.matrix x)) ((1 : EuclideanSpace ℂ (Ind κ ε s) →L[ℂ] _)
        (rhsVec κ ε s))) = _
    rw [hDm]
    rfl
  have hUb : ∀ x : Inp κ ε s,
      OracleCircuit.IsUnitary (1 : EuclideanSpace ℂ (Ind κ ε s) →L[ℂ] EuclideanSpace ℂ (Ind κ ε s)) :=
    fun _ => OracleCircuit.isUnitary_one
  have hmain := SparseLinearSystems.Endpoint.main D (fun _ => 1) hUb (rhsVec κ ε s)
    (rhsVec_norm κ ε s hs) κ ε (by linarith) hε (by linarith)
  obtain ⟨hup, -, hguar⟩ := hmain
  refine ⟨D, hDm, hprom, hsol, ?_, hup⟩
  apply lower_bound_sharp_clean κ ε s hκ hs hε hε1 D hDm hrow hcol ⟨fun _ => enc, henc⟩
    (SparseLinearSystems.Step.physOracle D (fun _ => 1) (SparseLinearSystems.Endpoint.Tw s κ ε))
    SparseLinearSystems.Step.wMat
    (physOracle_admissible D (fun _ => 1) hUb (fun _ _ => rfl) _)
  intro x
  obtain ⟨-, hsucc, -, hd⟩ := hguar x (hprom x)
  rw [hsol x] at hd
  exact ⟨hsucc, hd⟩

end Characterisation

end

end LinearSystemLowerBound
