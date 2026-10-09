import GeneralODE.Native.Branches
import GeneralODE.Block.HistoryEncoding
import SparseODE.ODEJointSimulation
import SparseODE.ODEFinalNativeBasis

/-!
# Lemma `ode:lem:block`: a block encoding of `A` from sparse access

Two runs of the released coherent native simulator implement all branch
evolutions `e^{-i u K_σ}` with nonnegative durations `u = max(±s, 0)`.  The
first run followed by the inverse of the second implements the signed
evolutions `e^{-i s K_σ}` with full-output error at most `2ε`, using only the
original sparse queries.  Between the branch states of the arcsine LCU the
resulting unitary has the block `A/(8√2 Λ)` up to `2ε + 4^{-N}/2`; between the
branch states of one padding branch it has the block `I` up to `2ε`.  After
flattening the registers, every native oracle maps one fixed basis vector to
a basis vector.  The query count is at most
`1327104 (√(2s)·2N + √(2s·2N·ℓ) + ℓ)` with `ℓ = log(2/ε)`.
-/

namespace SparseHamiltonian.GeneralODE.NativeBlock

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding ODEMatrixEnergy
  SparseStateOverlap LCU
open scoped BigOperators InnerProduct ComplexConjugate
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

section Durations

/-- Forward durations. -/
def uPlus (N : ℕ) (Λ : ℝ) (i : Branch N) : ℝ := max (sTab N Λ i) 0

/-- Backward durations. -/
def uMinus (N : ℕ) (Λ : ℝ) (i : Branch N) : ℝ := max (-sTab N Λ i) 0

theorem uPlus_nonneg (N : ℕ) (Λ : ℝ) (i : Branch N) : 0 ≤ uPlus N Λ i := le_max_right _ _

theorem uMinus_nonneg (N : ℕ) (Λ : ℝ) (i : Branch N) : 0 ≤ uMinus N Λ i := le_max_right _ _

theorem uPlus_le (N : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (i : Branch N) : uPlus N Λ i ≤ N / Λ := by
  have h := abs_sTab_le N Λ hΛ i
  have h0 : (0 : ℝ) ≤ N / Λ := by positivity
  exact max_le ((le_abs_self _).trans h) h0

theorem uMinus_le (N : ℕ) (Λ : ℝ) (hΛ : 0 < Λ) (i : Branch N) : uMinus N Λ i ≤ N / Λ := by
  have h := abs_sTab_le N Λ hΛ i
  have h0 : (0 : ℝ) ≤ N / Λ := by positivity
  exact max_le ((neg_le_abs _).trans h) h0

theorem uPlus_sub_uMinus (N : ℕ) (Λ : ℝ) (i : Branch N) :
    uPlus N Λ i - uMinus N Λ i = sTab N Λ i := by
  unfold uPlus uMinus
  rcases le_total 0 (sTab N Λ i) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

end Durations

section Evolution

/-- Composing the inverse of one evolution with another subtracts durations. -/
theorem exp_adjoint_mul {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (K : P →L[ℂ] P) (hK : star K = K) (a b : ℝ) :
    (NormedSpace.exp ((-Complex.I * (a : ℂ)) • K))† ∘L NormedSpace.exp ((-Complex.I * (b : ℂ)) • K) =
      NormedSpace.exp ((-Complex.I * ((b - a : ℝ) : ℂ)) • K) := by
  letI : NormedAlgebra ℚ (P →L[ℂ] P) := NormedAlgebra.restrictScalars ℚ ℂ _
  rw [LabeledAdjointSimulation.evolution_adjoint K hK a]
  have hcomm : Commute ((-Complex.I * ((-a : ℝ) : ℂ)) • K) ((-Complex.I * (b : ℂ)) • K) :=
    ((Commute.refl K).smul_left _).smul_right _
  rw [← ContinuousLinearMap.mul_def, ← NormedSpace.exp_add_of_commute hcomm]
  congr 1
  ext1 v
  simp only [add_apply, smul_apply]
  rw [← add_smul]
  congr 1
  push_cast
  ring

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem evolution_unitary (D : Data X n Z s) {ι : Type} [Fintype ι] [DecidableEq ι]
    (k u : ι → ℝ) (x : X) : IsUnitary (ODEJointSimulation.evolution D k u x) :=
  NativeMaskedOracle.diagonal_unitary _ (fun i =>
    LabeledAdjointSimulation.evolution_unitary _
      (SparseValuePrecision.matrixOperator_star_eq _ (lchsHamiltonian_isHermitian _ _)) (u i))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The signed branch evolution. -/
theorem signed_evolution (D : Data X n Z s) (N : ℕ) (Λ : ℝ) (x : X) :
    (ODEJointSimulation.evolution D (kTab N) (uMinus N Λ) x)† ∘L
        ODEJointSimulation.evolution D (kTab N) (uPlus N Λ) x =
      WeightedClock.diagonal (V := fun _ : Branch N => EuclideanSpace ℂ n)
        (fun i => branchEvolution N Λ (D.matrix x) i) := by
  unfold ODEJointSimulation.evolution
  rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
  congr 1
  funext i
  rw [exp_adjoint_mul _ (SparseValuePrecision.matrixOperator_star_eq _
    (lchsHamiltonian_isHermitian _ _)), uPlus_sub_uMinus]
  rfl

end Evolution

section Error

variable {P K X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- One forward run followed by the inverse of another implements the signed
evolution with twice the error. -/
theorem signed_program_error {F : L → X → K →L[ℂ] K}
    (pP pM : MultiOracleCircuit.Program F) (hF : ∀ l x, IsUnitary (F l x))
    (input output : P →L[ℂ] K) (VP VM : X → P →L[ℂ] P)
    (hVP : ∀ x, IsUnitary (VP x)) (hVM : ∀ x, IsUnitary (VM x)) (ε : ℝ) (x : X)
    (hP : ‖pP.eval x ∘L input - output ∘L VP x‖ ≤ ε)
    (hM : ‖pM.eval x ∘L input - output ∘L VM x‖ ≤ ε) :
    ‖(MultiOracleCircuit.Program.seq pM.adjoint pP).eval x ∘L input -
        input ∘L ((VM x)† ∘L VP x)‖ ≤ 2 * ε := by
  set U := pM.adjoint.eval x with hU
  have hUn : ‖U‖ ≤ 1 := Registers.norm_unitary_le U (pM.adjoint.eval_unitary hF x)
  have hVPn : ‖VP x‖ ≤ 1 := Registers.norm_unitary_le _ (hVP x)
  have hadj := LabeledAdjointSimulation.program_adjoint_error_eq pM hF input output VM hVM x
  have hsplit : (MultiOracleCircuit.Program.seq pM.adjoint pP).eval x ∘L input -
      input ∘L ((VM x)† ∘L VP x) =
      U ∘L (pP.eval x ∘L input - output ∘L VP x) + (U ∘L output - input ∘L (VM x)†) ∘L VP x := by
    change (U * pP.eval x) ∘L input - input ∘L ((VM x)† ∘L VP x) = _
    rw [ContinuousLinearMap.mul_def]
    ext1 v
    simp only [comp_apply, sub_apply, add_apply, map_sub]
    abel
  rw [hsplit]
  have h1 : ‖U ∘L (pP.eval x ∘L input - output ∘L VP x)‖ ≤ ε :=
    (opNorm_comp_le _ _).trans (by
      calc ‖U‖ * ‖pP.eval x ∘L input - output ∘L VP x‖ ≤ 1 * ε :=
            mul_le_mul hUn hP (norm_nonneg _) zero_le_one
        _ = ε := one_mul ε)
  have h2 : ‖(U ∘L output - input ∘L (VM x)†) ∘L VP x‖ ≤ ε :=
    (opNorm_comp_le _ _).trans (by
      have : ‖U ∘L output - input ∘L (VM x)†‖ ≤ ε := by rw [hU, hadj]; exact hM
      calc ‖U ∘L output - input ∘L (VM x)†‖ * ‖VP x‖ ≤ ε * 1 :=
            mul_le_mul this hVPn (norm_nonneg _) ((norm_nonneg _).trans this)
        _ = ε := mul_one ε)
  calc ‖U ∘L (pP.eval x ∘L input - output ∘L VP x) + (U ∘L output - input ∘L (VM x)†) ∘L VP x‖
      ≤ ‖U ∘L (pP.eval x ∘L input - output ∘L VP x)‖ +
          ‖(U ∘L output - input ∘L (VM x)†) ∘L VP x‖ := norm_add_le _ _
    _ ≤ ε + ε := add_le_add h1 h2
    _ = 2 * ε := by ring

end Error

section Main

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Flat register of the native block encoding. -/
abbrev FlatBasis (N : ℕ) (n Z : Type) [Fintype n] [Fintype Z] (T d : ℕ) :=
  FlatBranchNativeAccess.Basis (ActiveRegisterLayout.Label PUnit.{1} T d)
    (ODEJointNative.Basis (Branch N) n Z)

/-- Native sparse oracles, with every other register a spectator. -/
abbrev flatOracle (D : Data X n Z s) (N T d : ℕ) :=
  FlatBranchNativeAccess.flatOracle (ι := ActiveRegisterLayout.Label PUnit.{1} T d)
    (ODEJointNative.cayleyOracle (ι := Branch N) D)

/-- The fixed basis vector of the flat register. -/
def flatClean (D : Data X n Z s) (N T d : ℕ) : FlatBasis N n Z T d :=
  FlatBranchNativeAccess.cleanBasis (ODEFinalNativeBasis.clockBasis T d)
    (ODEJointNative.cleanBasis D (Sum.inr true : Branch N))

/-- Its images under the native oracles. -/
def flatImage (D : Data X n Z s) (N T d : ℕ) (l : Query) (x : X) : FlatBasis N n Z T d :=
  FlatBranchNativeAccess.imageBasis (ODEFinalNativeBasis.clockBasis T d)
    (ODEJointNative.cleanBasis D (Sum.inr true : Branch N)) (ODEJointNative.image D (Sum.inr true) l x)

/-- Every native oracle maps the fixed basis vector to a basis vector. -/
theorem flatOracle_valid (D : Data X n Z s) (N T d : ℕ) (l : Query) (x : X) :
    flatOracle D N T d l x (EuclideanSpace.single (flatClean D N T d) 1) =
      EuclideanSpace.single (flatImage D N T d l x) 1 :=
  FlatBranchNativeAccess.valid (ODEJointNative.cayleyOracle D) (ODEFinalNativeBasis.clockBasis T d)
    (ODEJointNative.cleanBasis D (Sum.inr true)) (ODEJointNative.image D (Sum.inr true))
    (ODEJointNative.valid D (Sum.inr true)) l x

omit [DecidableEq Z] in
theorem flatOracle_unitary (D : Data X n Z s) (N T d : ℕ) (l : Query) (x : X) :
    IsUnitary (flatOracle D N T d l x) :=
  FlatBranchNativeAccess.flatOracle_unitary _ (ODEJointNative.cayleyOracle_unitary D) l x

/-- Conjugating by a fixed isometric layout and compressing back is the identity. -/
theorem layout_compress {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (e : H ≃ₗᵢ[ℂ] K) (U : H →L[ℂ] H) :
    (e.toLinearIsometry.toContinuousLinearMap)† ∘L e.conjStarAlgEquiv U ∘L
        e.toLinearIsometry.toContinuousLinearMap = U := by
  have h := e.toLinearIsometry.adjoint_comp_self
  ext1 v
  have h2 : ((e.toLinearIsometry.toContinuousLinearMap)†) (e (U v)) = U v :=
    congrArg (fun T : H →L[ℂ] H => T (U v)) h
  simp only [comp_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change ((e.toLinearIsometry.toContinuousLinearMap)†) (e (U (e.symm (e v)))) = U v
  rw [LinearIsometryEquiv.symm_apply_apply, h2]

/-- **Lemma `ode:lem:block`.** -/
theorem exists_native_block (D : Data X n Z s) (Λ : ℝ) (hΛ : 0 < Λ)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ) (N : ℕ) (hN : 1 ≤ N)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ (T d : ℕ) (qP : MultiOracleCircuit.Program (flatOracle D N T d))
      (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (FlatBasis N n Z T d))),
      (∀ b, (Ein b)† ∘L Ein b = 1) ∧ (∀ b, (Eout b)† ∘L Eout b = 1) ∧
      (qP.count : ℝ) ≤ 1327104 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (2 * N)
        (ImprovedPrecisionBudget.targetLog ε) ∧
      ∀ x,
        ‖(Eout true)† ∘L qP.eval x ∘L Ein true -
            (((8 * Real.sqrt 2 * Λ)⁻¹ : ℝ) : ℂ) • (-matrixOperator (D.matrix x))‖ ≤
          2 * ε + (1 / 4) ^ N / 2 ∧
        ‖(Eout false)† ∘L qP.eval x ∘L Ein false - 1‖ ≤ 2 * ε := by
  have hrH : ∀ x i, ∑ j, ‖hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ Λ ^ 2 :=
    fun x => (NativeMatrix.hamiltonian_energy_le _ Λ (hA x)).1
  have hcH : ∀ x j, ∑ i, ‖hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ Λ ^ 2 :=
    fun x => (NativeMatrix.hamiltonian_energy_le _ Λ (hA x)).2
  have hrD : ∀ x i, ∑ j, ‖dissipativePart (D.matrix x) i j‖ ^ 2 ≤ Λ ^ 2 :=
    fun x => (NativeMatrix.dissipative_energy_le _ Λ (hA x)).1
  have hcD : ∀ x j, ∑ i, ‖dissipativePart (D.matrix x) i j‖ ^ 2 ≤ Λ ^ 2 :=
    fun x => (NativeMatrix.dissipative_energy_le _ Λ (hA x)).2
  have hNΛ : 0 < (N : ℝ) / Λ := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    positivity
  obtain ⟨γ, -, -, -, hsim⟩ := ODEJointSimulation.exists_coherent_native_simulation
    (ι := Branch N) D (Sum.inr true) Λ Λ 1 (N / Λ) ε hΛ.le hΛ.le (by positivity) hNΛ hε hε1
    hrH hcH hrD hcD
  set ρ := Λ + 1 * Λ with hρ
  have hρT : ρ * (N / Λ) = 2 * N := by rw [hρ]; field_simp; ring
  rw [hρT] at hsim
  set T := ODENativeSimulation.slots (s : ℝ) γ ρ (N / Λ) ε with hT
  set d := ODENativeSimulation.degree (s : ℝ) γ ρ (N / Λ) ε with hd
  set input := ODEJointSimulation.input (ι := Branch N) D (Sum.inr true) γ ρ (N / Λ) ε with hinput
  set output := ODEJointSimulation.output (ι := Branch N) D (Sum.inr true) γ ρ (N / Λ) ε
    with houtput
  obtain ⟨pP, hcP, hin, -, hP⟩ := hsim (kTab N) (uPlus N Λ) (abs_kTab_le N)
    (uPlus_nonneg N Λ) (uPlus_le N Λ hΛ)
  obtain ⟨pM, hcM, -, -, hM⟩ := hsim (kTab N) (uMinus N Λ) (abs_kTab_le N)
    (uMinus_nonneg N Λ) (uMinus_le N Λ hΛ)
  set layout := FlatBranchNativeAccess.layout (ι := ActiveRegisterLayout.Label PUnit.{1} T d)
    (B := ODEJointNative.Basis (Branch N) n Z) with hlayout
  set L := layout.toLinearIsometry.toContinuousLinearMap with hL
  have hLiso : L† ∘L L = 1 := layout.toLinearIsometry.adjoint_comp_self
  let q := MultiOracleCircuit.Program.seq pM.adjoint pP
  let qP : MultiOracleCircuit.Program (flatOracle D N T d) := q.transport layout
  -- the branch amplitudes
  let ain : Bool → EuclideanSpace ℂ (Branch N) := fun b =>
    if b then lcuIn (coef N) else EuclideanSpace.single (Sum.inr true) 1
  let aout : Bool → EuclideanSpace ℂ (Branch N) := fun b =>
    if b then lcuOut (coef N) else EuclideanSpace.single (Sum.inr true) 1
  have hain : ∀ b, ‖ain b‖ = 1 := by
    intro b; cases b
    · simp [ain]
    · exact norm_lcuIn (coef N) (sum_norm_coef N)
  have haout : ∀ b, ‖aout b‖ = 1 := by
    intro b; cases b
    · simp [aout]
    · exact norm_lcuOut (coef N) (sum_norm_coef N)
  let Ein : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (FlatBasis N n Z T d)) :=
    fun b => L ∘L input ∘L branchState (ain b)
  let Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (FlatBasis N n Z T d)) :=
    fun b => L ∘L input ∘L branchState (aout b)
  have hiso : ∀ a : EuclideanSpace ℂ (Branch N), ‖a‖ = 1 →
      (L ∘L input ∘L branchState a)† ∘L (L ∘L input ∘L branchState a) = 1 := by
    intro a ha
    exact Registers.isometry_comp _ _ hLiso
      (Registers.isometry_comp _ _ hin (branchState_isometry a ha))
  refine ⟨T, d, qP, Ein, Eout, fun b => hiso _ (hain b), fun b => hiso _ (haout b), ?_, ?_⟩
  · -- query count
    have hcount : (qP.count : ℝ) = (pM.count : ℝ) + pP.count := by
      change ((q.transport layout).count : ℝ) = _
      rw [MultiOracleCircuit.Program.count_transport]
      change ((pM.adjoint.count + pP.count : ℕ) : ℝ) = _
      rw [MultiOracleCircuit.Program.count_adjoint]
      push_cast
      ring
    rw [hcount]
    linarith
  · intro x
    -- the signed simulation error
    have herr := signed_program_error pP pM
      (ODEJointNative.oracle_unitary D _ _) input output
      (fun y => ODEJointSimulation.evolution D (kTab N) (uPlus N Λ) y)
      (fun y => ODEJointSimulation.evolution D (kTab N) (uMinus N Λ) y)
      (fun y => evolution_unitary D _ _ y) (fun y => evolution_unitary D _ _ y) ε x
      (hP x).2 (hM x).2
    rw [signed_evolution D N Λ x] at herr
    set G := WeightedClock.diagonal (V := fun _ : Branch N => EuclideanSpace ℂ n)
      (fun i => branchEvolution N Λ (D.matrix x) i) with hG
    -- the block of the native unitary
    have hblock : ∀ b, ‖(Eout b)† ∘L qP.eval x ∘L Ein b -
        (branchState (aout b))† ∘L G ∘L branchState (ain b)‖ ≤ 2 * ε := by
      intro b
      have hq : qP.eval x = layout.conjStarAlgEquiv (q.eval x) :=
        MultiOracleCircuit.Program.eval_transport layout q x
      have hcomp : (Eout b)† ∘L qP.eval x ∘L Ein b =
          (branchState (aout b))† ∘L input† ∘L (q.eval x ∘L input) ∘L branchState (ain b) := by
        change (L ∘L input ∘L branchState (aout b))† ∘L qP.eval x ∘L
          (L ∘L input ∘L branchState (ain b)) = _
        rw [hq, adjoint_comp, adjoint_comp]
        have hc := layout_compress layout (q.eval x)
        rw [← hL] at hc
        calc (branchState (aout b))† ∘L (input† ∘L L†) ∘L layout.conjStarAlgEquiv (q.eval x) ∘L
              (L ∘L input ∘L branchState (ain b))
            = (branchState (aout b))† ∘L input† ∘L
                (L† ∘L layout.conjStarAlgEquiv (q.eval x) ∘L L) ∘L input ∘L branchState (ain b) := by
              simp only [comp_assoc]
          _ = _ := by rw [hc]; simp only [comp_assoc]
      have hdiff : (Eout b)† ∘L qP.eval x ∘L Ein b - (branchState (aout b))† ∘L G ∘L branchState (ain b) =
          (branchState (aout b))† ∘L input† ∘L (q.eval x ∘L input - input ∘L G) ∘L
            branchState (ain b) := by
        rw [hcomp]
        have hIIv : ∀ w, (input†) (input w) = w := fun w => by
          have := congrArg (fun T => T w) hin
          simpa using this
        ext1 v
        simp only [comp_apply, sub_apply, map_sub, hIIv]
      rw [hdiff]
      have hbs : ‖branchState (P := EuclideanSpace ℂ n) (ain b)‖ ≤ 1 :=
        Registers.norm_le_one_of_isometry _ (branchState_isometry _ (hain b))
      have hbo : ‖(branchState (P := EuclideanSpace ℂ n) (aout b))†‖ ≤ 1 := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        exact Registers.norm_le_one_of_isometry _ (branchState_isometry _ (haout b))
      have hio : ‖input†‖ ≤ 1 := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        exact Registers.norm_le_one_of_isometry _ hin
      calc ‖(branchState (aout b))† ∘L input† ∘L (q.eval x ∘L input - input ∘L G) ∘L
            branchState (ain b)‖
          ≤ ‖(branchState (P := EuclideanSpace ℂ n) (aout b))†‖ * (‖input†‖ *
              (‖q.eval x ∘L input - input ∘L G‖ * ‖branchState (P := EuclideanSpace ℂ n) (ain b)‖)) := by
            refine (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
            refine (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
            exact opNorm_comp_le _ _
        _ ≤ 1 * (1 * (2 * ε * 1)) := by
            gcongr
        _ = 2 * ε := by ring
    refine ⟨?_, ?_⟩
    · -- the matrix block
      have hsum : (branchState (aout true))† ∘L G ∘L branchState (ain true) =
          ∑ i, coef N i • branchEvolution N Λ (D.matrix x) i := by
        rw [hG, branch_block]
        apply Finset.sum_congr rfl
        intro i _
        simp only [ain, aout, if_true]
        rw [lcu_pair]
      have happrox := lcu_block_approx N Λ hΛ (D.matrix x) (hA x)
      rw [← hsum] at happrox
      calc ‖(Eout true)† ∘L qP.eval x ∘L Ein true -
            (((8 * Real.sqrt 2 * Λ)⁻¹ : ℝ) : ℂ) • (-matrixOperator (D.matrix x))‖
          ≤ ‖(Eout true)† ∘L qP.eval x ∘L Ein true -
              (branchState (aout true))† ∘L G ∘L branchState (ain true)‖ +
            ‖(branchState (aout true))† ∘L G ∘L branchState (ain true) -
              (((8 * Real.sqrt 2 * Λ)⁻¹ : ℝ) : ℂ) • (-matrixOperator (D.matrix x))‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * ε + (1 / 4) ^ N / 2 := add_le_add (hblock true) happrox
    · -- the identity block
      have hone : (branchState (aout false))† ∘L G ∘L branchState (ain false) = 1 := by
        rw [hG, branch_block]
        simp only [ain, aout, Bool.false_eq_true, if_false]
        rw [Finset.sum_eq_single (Sum.inr true)]
        · rw [branchEvolution_inr]
          ext1 v
          simp
        · intro i _ hi
          ext1 v
          simp [hi]
        · simp
      rw [← hone]
      exact hblock false

end Main

end

end SparseHamiltonian.GeneralODE.NativeBlock
