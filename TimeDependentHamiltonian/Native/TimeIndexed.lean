import TimeDependentHamiltonian.Chronology.Simulation
import SparseHamiltonian.NativeCayleyActive

/-!
# Coherent sampled-time oracles

The time-dependent access model of the manuscript (equation
`hs:eq:timeaccess`) adjoins a time register `|r⟩` to each primitive oracle and
applies the operation of the represented sample `H̃_r`:

  `O_time = ∑_r |r⟩⟨r| ⊗ O_r`.

One invocation of this coherent operation is one query, even when `r` is in
superposition. Here `O_r` is the released native oracle family for the sample
`r` (row locator, column locator and entry value, with their spectator
registers in a fixed layout), supplied by sparse data indexed by
`X × Fin M`: the unknown instance and the sampled time.

`timeIndexed F` is the block-diagonal operator `∑_r |r⟩⟨r| ⊗ F r` on the
register `Fin M × B`; `timeOracle F` is the corresponding coherent oracle
family. A program over the sampled oracles lifts to a program over the
coherent oracle with the same instructions and the same query counts, and its
evaluation is the block-diagonal sum of the sampled evaluations
(`liftProgram_eval`). A known valid input at one sampled time gives the
phase-fixed dummy input used by the released native control compiler
(`timeOracle_valid`).
-/

namespace SparseHamiltonian.TimeDependent

noncomputable section

open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 4096

section TimeRegister

variable {M : ℕ} {B : Type*} [Fintype B]

/-- The block-diagonal operator `∑_r |r⟩⟨r| ⊗ F r` on the time register and
payload. -/
def timeIndexed (F : Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    EuclideanSpace ℂ (Fin M × B) →L[ℂ] EuclideanSpace ℂ (Fin M × B) :=
  (RegisterEquivalences.productFlatten (Fin M) B).conjStarAlgEquiv
    (WeightedClock.diagonal F)

theorem timeIndexed_apply (F : Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (v : EuclideanSpace ℂ (Fin M × B)) (r : Fin M) (b : B) :
    timeIndexed F v (r, b) =
      F r ((RegisterEquivalences.productFlatten (Fin M) B).symm v r) b := rfl

theorem timeIndexed_mul (F G : Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    timeIndexed F * timeIndexed G = timeIndexed (fun r => F r * G r) := by
  rw [timeIndexed, timeIndexed, timeIndexed, ← map_mul]
  congr 1

theorem timeIndexed_star (F : Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    star (timeIndexed F) = timeIndexed (fun r => star (F r)) := by
  rw [timeIndexed, timeIndexed, ← map_star]
  congr 1
  simp only [star_eq_adjoint]
  exact WeightedClock.diagonal_adjoint F

theorem timeIndexed_one :
    timeIndexed (fun _ : Fin M => (1 : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)) = 1 := by
  rw [timeIndexed, WeightedClock.diagonal_one, map_one]

theorem timeIndexed_unitary (F : Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ r, IsUnitary (F r)) : IsUnitary (timeIndexed F) := by
  constructor
  · rw [timeIndexed_star, timeIndexed_mul]
    simp only [(hF _).1]
    exact timeIndexed_one
  · rw [timeIndexed_star, timeIndexed_mul]
    simp only [(hF _).2]
    exact timeIndexed_one

/-- Insert a payload into one slot of the time direct sum. -/
def slotInject (r : Fin M) :
    EuclideanSpace ℂ B →ₗᵢ[ℂ] PiLp 2 (fun _ : Fin M => EuclideanSpace ℂ B) where
  toFun v := WithLp.toLp 2 (Pi.single r v)
  map_add' v w := by
    apply PiLp.ext
    intro q
    by_cases h : q = r
    · subst h
      simp
    · simp [h]
  map_smul' z v := by
    apply PiLp.ext
    intro q
    by_cases h : q = r
    · subst h
      simp
    · simp [h]
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_eq_single r]
    · simp
    · intro q _ hq
      simp [hq]
    · simp

@[simp] theorem slotInject_apply (r : Fin M) (v : EuclideanSpace ℂ B) (q : Fin M) :
    slotInject r v q = if q = r then v else 0 := by
  by_cases h : q = r
  · subst h
    simp [slotInject]
  · simp [slotInject, h]

/-- Place a payload at one sampled time, with zero amplitude at other times. -/
def timeEmbed (r : Fin M) : EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin M × B) :=
  (RegisterEquivalences.productFlatten (Fin M) B).toLinearIsometry.comp (slotInject r)

theorem timeEmbed_apply (r : Fin M) (v : EuclideanSpace ℂ B) (q : Fin M) (b : B) :
    timeEmbed r v (q, b) = if q = r then v b else 0 := by
  change RegisterEquivalences.productFlatten (Fin M) B (slotInject r v) (q, b) = _
  rw [RegisterEquivalences.productFlatten_apply, slotInject_apply]
  by_cases h : q = r <;> simp [h]

theorem timeEmbed_symm_apply (r : Fin M) (v : EuclideanSpace ℂ B) (q : Fin M) :
    (RegisterEquivalences.productFlatten (Fin M) B).symm (timeEmbed r v) q =
      if q = r then v else 0 := by
  apply PiLp.ext
  intro b
  rw [RegisterEquivalences.productFlatten_symm_apply, timeEmbed_apply]
  by_cases h : q = r <;> simp [h]

/-- On a payload placed at time `r`, the coherent operation acts as `F r`. -/
theorem timeIndexed_timeEmbed (F : Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (r : Fin M) :
    timeIndexed F ∘L (timeEmbed r).toContinuousLinearMap =
      (timeEmbed r).toContinuousLinearMap ∘L F r := by
  ext v ⟨q, b⟩
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [timeIndexed_apply, timeEmbed_symm_apply, timeEmbed_apply]
  by_cases h : q = r
  · subst h
    simp
  · simp [h]

theorem timeEmbed_single [DecidableEq B] (r : Fin M) (b : B) :
    timeEmbed r (EuclideanSpace.single b (1 : ℂ)) = EuclideanSpace.single (r, b) (1 : ℂ) := by
  ext ⟨q, c⟩
  rw [timeEmbed_apply]
  by_cases h : q = r
  · subst h
    by_cases hc : c = b
    · subst hc
      simp
    · simp [hc]
  · simp [h]

end TimeRegister

section Programs

variable {X L : Type*} {M : ℕ} {B : Type*} [Fintype B]

/-- The coherent sampled-time oracle family. -/
def timeOracle (F : L → X × Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) :
    L → X → EuclideanSpace ℂ (Fin M × B) →L[ℂ] EuclideanSpace ℂ (Fin M × B) :=
  fun l x => timeIndexed (fun r => F l (x, r))

theorem timeOracle_unitary (F : L → X × Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l y, IsUnitary (F l y)) (l : L) (x : X) : IsUnitary (timeOracle F l x) :=
  timeIndexed_unitary _ (fun r => hF l (x, r))

/-- Every instruction keeps its label and direction; fixed gates act on the
payload and leave the time register untouched. -/
def liftProgram {F : L → X × Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B} :
    MultiOracleCircuit.Program F → MultiOracleCircuit.Program (timeOracle F)
  | .fixed U hU => .fixed (timeIndexed (fun _ => U)) (timeIndexed_unitary _ (fun _ => hU))
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (liftProgram p) (liftProgram q)

@[simp] theorem liftProgram_count
    {F : L → X × Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B}
    (p : MultiOracleCircuit.Program F) : (liftProgram p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp [liftProgram, hp, hq]

@[simp] theorem liftProgram_cost
    {F : L → X × Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B}
    (p : MultiOracleCircuit.Program F) (w : L → ℕ) :
    (liftProgram p).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp [liftProgram, hp, hq]

/-- The lifted program evaluates to the block-diagonal sum of the sampled
evaluations. -/
theorem liftProgram_eval
    {F : L → X × Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B}
    (p : MultiOracleCircuit.Program F) (x : X) :
    (liftProgram p).eval x = timeIndexed (fun r => p.eval (x, r)) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l =>
      change star (timeIndexed (fun r => F l (x, r))) = _
      rw [timeIndexed_star]
      rfl
  | seq p q hp hq =>
      change (liftProgram p).eval x * (liftProgram q).eval x = _
      rw [hp, hq, timeIndexed_mul]
      rfl

/-- A known valid input at one sampled time is valid for the coherent oracle. -/
theorem timeOracle_valid [DecidableEq B]
    (F : L → X × Fin M → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (a : B) (image : L → X × Fin M → B)
    (hvalid : ∀ l y, F l y (EuclideanSpace.single a 1) = EuclideanSpace.single (image l y) 1)
    (r₀ : Fin M) (l : L) (x : X) :
    timeOracle F l x (EuclideanSpace.single (r₀, a) 1) =
      EuclideanSpace.single (r₀, image l (x, r₀)) 1 := by
  rw [← timeEmbed_single]
  have h := congrArg (fun A => A (EuclideanSpace.single a (1 : ℂ)))
    (timeIndexed_timeEmbed (fun r => F l (x, r)) r₀)
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap] at h
  change timeIndexed (fun r => F l (x, r)) (timeEmbed r₀ (EuclideanSpace.single a 1)) = _
  rw [h, hvalid, timeEmbed_single]

end Programs

/-! ### The sampled native Cayley program -/

section Native

open NativeSparseBlockEncoding

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- The coherent sampled-time version of the released native query family. -/
abbrev sampledOracle (D : Data (X × Fin M) n Z s) :
    Query → X → EuclideanSpace ℂ (Fin M × NativeCayleyProgram.Basis n Z) →L[ℂ]
      EuclideanSpace ℂ (Fin M × NativeCayleyProgram.Basis n Z) :=
  timeOracle (NativeCayleyProgram.oracle D)

omit [DecidableEq Z] in
theorem sampledOracle_unitary (D : Data (X × Fin M) n Z s) (l : Query) (x : X) :
    IsUnitary (sampledOracle D l x) :=
  timeOracle_unitary _ (NativeCayleyProgram.oracle_unitary D) l x

/-- The released eighteen-query Cayley circuit, executed coherently at the
sampled time held in the time register. -/
def sampledProgram (D : Data (X × Fin M) n Z s) (γ : ℝ) :
    MultiOracleCircuit.Program (sampledOracle D) :=
  liftProgram (NativeCayleyProgram.program D γ)

@[simp] theorem sampledProgram_count (D : Data (X × Fin M) n Z s) (γ : ℝ) :
    (sampledProgram D γ).count = 18 := by
  simp [sampledProgram]

theorem sampledProgram_cost (D : Data (X × Fin M) n Z s) (γ : ℝ) (w : Query → ℕ) :
    (sampledProgram D γ).cost w =
      6 * w .rowLocation + 6 * w .columnLocation + 6 * w .value := by
  simp [sampledProgram]

/-- Clean encoding of the private Cayley register at sampled time `r`. -/
def sampledClean (D : Data (X × Fin M) n Z s) (r : Fin M) :
    SparseEdgeMoments.OrientedSpace n →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin M × NativeCayleyProgram.Basis n Z) :=
  (timeEmbed r).comp (NativeCayleyProgram.clean D)

/-- At sampled time `r`, the coherent program implements the locator-conjugated
Cayley action of the sample `r`. -/
theorem sampledProgram_intertwines (D : Data (X × Fin M) n Z s) (γ : ℝ) (x : X)
    (r : Fin M) :
    (sampledProgram D γ).eval x ∘L (sampledClean D r).toContinuousLinearMap =
      (sampledClean D r).toContinuousLinearMap ∘L
        FixedNativeCayleySimulation.action D (x, r) γ := by
  rw [sampledProgram, liftProgram_eval]
  change timeIndexed (fun q => (NativeCayleyProgram.program D γ).eval (x, q)) ∘L
      ((timeEmbed r).toContinuousLinearMap ∘L (NativeCayleyProgram.clean D).toContinuousLinearMap) =
    ((timeEmbed r).toContinuousLinearMap ∘L (NativeCayleyProgram.clean D).toContinuousLinearMap) ∘L _
  rw [← comp_assoc, timeIndexed_timeEmbed, comp_assoc,
    NativeCayleyProgram.program_intertwines, comp_assoc]

/-- The phase-fixed dummy input at sampled time `r₀`. -/
def sampledBasis (D : Data (X × Fin M) n Z s) (r₀ : Fin M) :
    Fin M × NativeCayleyProgram.Basis n Z :=
  (r₀, NativeCayleyProgram.cleanBasis D)

theorem sampledOracle_valid (D : Data (X × Fin M) n Z s) (r₀ : Fin M) (l : Query) (x : X) :
    sampledOracle D l x (EuclideanSpace.single (sampledBasis D r₀) 1) =
      EuclideanSpace.single (r₀, NativeCayleyProgram.image D l (x, r₀)) 1 :=
  timeOracle_valid _ _ _ (NativeCayleyProgram.valid D) r₀ l x

end Native

end

end SparseHamiltonian.TimeDependent
