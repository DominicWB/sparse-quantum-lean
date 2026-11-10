import SignedFactorSimulation.LCU
import SignedFactorSimulation.Amplify
import SparseHamiltonian.ActiveClockAlgebra
import SparseHamiltonian.OracleTransport

/-!
# Factor queries of the signed LCU

The oracle of Theorem `opt:thm:signed` is the factor unitary `U = U_B` and its adjoint. In the
structured workspace of the LCU (`Work`), every register has the size of `W`, and one factor
query is `U` applied to every register (`liftU`), the identity on the branch and slot labels.

"without a controlled version of the opaque preparation unitary being supplied separately": the
private unitary
`P = U† G U` of a reuse step is applied, on the branches that are still active, as
`liftU(U)† · (known controlled phase) · liftU(U)` (`liftU_conj`). On public registers and on
finished branches the two factor calls cancel. Each layer of the synchronized SELECT is a known
coupling network followed by this active private step (`select_eq_product`), so SELECT uses two
factor queries per layer (`select_implements`), and `n` layers in all.

The amplified circuit `ampCirc` performs `R` rounds of the three-SELECT reflection round
(`AmplificationQuery.threeSelect`) and uses `3^R` SELECT calls (`ampCirc_implements`); applied to
the input preparation it is the iterated amplification `ampIter` (`ampIter_eq_ampCirc`).
-/

set_option autoImplicit false

namespace SignedFactorSimulation

noncomputable section

open ContinuousLinearMap Finset OptimalPrecision SparseHamiltonian
  SparseHamiltonian.CoherentReuse SparseHamiltonian.ChronologicalResolvent
  SparseHamiltonian.GlobalColligation SparseHamiltonian.OracleCircuit
  SparseHamiltonian.ReuseLayerFactorization SparseHamiltonian.ActiveClockAlgebra
open scoped InnerProduct InnerProductSpace

/-! ### Block-diagonal maps on a product -/

section BlockDiag

variable {Q R : Type*}
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]
  [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [CompleteSpace Q] [CompleteSpace R] in
theorem blockMap_diag_apply (a : Q →L[ℂ] Q) (d : R →L[ℂ] R) (x : WithLp 2 (Q × R)) :
    blockMap a 0 0 d x = WithLp.toLp 2 (a x.fst, d x.snd) := by
  simp [blockMap_apply]

omit [CompleteSpace Q] [CompleteSpace R] in
theorem blockMap_diag_comp (a a' : Q →L[ℂ] Q) (d d' : R →L[ℂ] R) :
    blockMap a 0 0 d ∘L blockMap a' 0 0 d' = blockMap (a ∘L a') 0 0 (d ∘L d') := by
  ext x
  simp only [comp_apply, blockMap_diag_apply, WithLp.fst, WithLp.snd]

omit [CompleteSpace Q] [CompleteSpace R] in
theorem blockMap_diag_one : blockMap (1 : Q →L[ℂ] Q) 0 0 (1 : R →L[ℂ] R) = 1 := by
  ext x
  simp only [blockMap_diag_apply, one_apply_eq_self]
  rfl

theorem blockMap_diag_adjoint (a : Q →L[ℂ] Q) (d : R →L[ℂ] R) :
    (blockMap a 0 0 d)† = blockMap (a†) 0 0 (d†) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [adjoint_inner_left, blockMap_diag_apply, WithLp.prod_inner_apply, WithLp.fst,
    WithLp.snd, adjoint_inner_left]

end BlockDiag

variable {P W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-! ### The lifted factor query -/

/-- The structured workspace of the LCU with `n` reuse branches and cascades of `m` slots. -/
abbrev Work (W : Type*) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n m : ℕ) :=
  PiLp 2 (BrSpace W (BlockOperator.H m W) n)

/-- `U` on every register of one branch. -/
def liftBr (U : W →L[ℂ] W) (m L : ℕ) :
    ReuseSchedule.Space L W (BlockOperator.H m W) →L[ℂ]
      ReuseSchedule.Space L W (BlockOperator.H m W) :=
  blockMap (WeightedClock.diagonal (fun _ : Fin m => U)) 0 0
    (WeightedClock.diagonal (fun _ : Fin L => U))

/-- **One factor query**: `U` on every register of size `W` of the workspace. -/
def liftU (U : W →L[ℂ] W) (n m : ℕ) : Work W n m →L[ℂ] Work W n m :=
  WeightedClock.diagonal (fun i => liftBr U m (brLen n i))

/-- The private step on the branches that are active at layer `r`. -/
def actLayer {m : ℕ} (Q : BlockOperator.H m W →L[ℂ] BlockOperator.H m W) (n r : ℕ) :
    Work W n m →L[ℂ] Work W n m :=
  WeightedClock.diagonal (fun i => activeBranch Q (brLen n i) r)

theorem diagonal_const_adjoint (L : ℕ) (U : W →L[ℂ] W) :
    (WeightedClock.diagonal (fun _ : Fin L => U))† = WeightedClock.diagonal (fun _ : Fin L => U†) :=
  WeightedClock.diagonal_adjoint _

omit [CompleteSpace W] in
theorem diagonal_const_comp (L : ℕ) (U U' : W →L[ℂ] W) :
    WeightedClock.diagonal (fun _ : Fin L => U) ∘L WeightedClock.diagonal (fun _ : Fin L => U') =
      WeightedClock.diagonal (fun _ : Fin L => U ∘L U') :=
  WeightedClock.diagonal_comp _ _

omit [CompleteSpace W] in
theorem diagonal_const_one (L : ℕ) :
    WeightedClock.diagonal (fun _ : Fin L => (1 : W →L[ℂ] W)) = 1 :=
  WeightedClock.diagonal_one

theorem liftBr_adjoint (U : W →L[ℂ] W) (m L : ℕ) : (liftBr U m L)† = liftBr (U†) m L := by
  rw [liftBr, liftBr, blockMap_diag_adjoint, diagonal_const_adjoint, diagonal_const_adjoint]

omit [CompleteSpace W] in
theorem liftBr_comp (U U' : W →L[ℂ] W) (m L : ℕ) :
    liftBr U m L ∘L liftBr U' m L = liftBr (U ∘L U') m L := by
  rw [liftBr, liftBr, liftBr, blockMap_diag_comp, diagonal_const_comp, diagonal_const_comp]

omit [CompleteSpace W] in
theorem liftBr_one (m L : ℕ) : liftBr (1 : W →L[ℂ] W) m L = 1 := by
  rw [liftBr, diagonal_const_one, diagonal_const_one, blockMap_diag_one]

/-- **The control trick on one branch**: conjugating the known active phase by the lifted
query gives the active private step `U† G U`. -/
theorem liftBr_conj {U : W →L[ℂ] W} (hU : U† ∘L U = 1) (G : W →L[ℂ] W) (m L r : ℕ) :
    (liftBr U m L)† ∘L activeBranch (WeightedClock.diagonal (fun _ : Fin m => G)) L r ∘L
        liftBr U m L =
      activeBranch (WeightedClock.diagonal (fun _ : Fin m => U† * G * U)) L r := by
  rw [liftBr_adjoint]
  unfold activeBranch
  split
  · rw [sharedAction, sharedAction, liftBr, liftBr, blockMap_diag_comp, blockMap_diag_comp,
      diagonal_const_comp, diagonal_const_comp, one_comp', diagonal_const_comp, hU,
      diagonal_const_one, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, comp_assoc]
  · rw [one_comp', liftBr_comp, hU, liftBr_one]

/-- The lifted query on the whole workspace. -/
theorem liftU_conj {U : W →L[ℂ] W} (hU : U† ∘L U = 1) (G : W →L[ℂ] W) (n m r : ℕ) :
    (liftU U n m)† ∘L actLayer (WeightedClock.diagonal (fun _ : Fin m => G)) n r ∘L
        liftU U n m =
      actLayer (WeightedClock.diagonal (fun _ : Fin m => U† * G * U)) n r := by
  rw [liftU, actLayer, actLayer, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp,
    WeightedClock.diagonal_comp]
  congr 1
  funext i
  exact liftBr_conj hU G m (brLen n i) r

theorem liftU_unitary {U : W →L[ℂ] W} (hU : IsUnitary U) (n m : ℕ) :
    IsUnitary (liftU U n m) := by
  have h1 : U† ∘L U = 1 := hU.1
  have h2 : U ∘L U† = 1 := hU.2
  constructor
  · change (liftU U n m)† ∘L liftU U n m = 1
    rw [liftU, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [liftBr_adjoint, liftBr_comp, h1, liftBr_one]
    exact WeightedClock.diagonal_one
  · change liftU U n m ∘L (liftU U n m)† = 1
    rw [liftU, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    simp only [liftBr_adjoint, liftBr_comp, h2, liftBr_one]
    exact WeightedClock.diagonal_one

theorem actLayer_unitary {m : ℕ} {Q : BlockOperator.H m W →L[ℂ] BlockOperator.H m W}
    (hQ : IsUnitary Q) (n r : ℕ) : IsUnitary (actLayer Q n r) := by
  have h := fun i : Br n => activeBranch_unitary (P := W) Q hQ (brLen n i) r
  constructor
  · change (actLayer Q n r)† ∘L actLayer Q n r = 1
    rw [actLayer, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    exact (congrArg WeightedClock.diagonal (funext fun i => (h i).1)).trans
      WeightedClock.diagonal_one
  · change actLayer Q n r ∘L (actLayer Q n r)† = 1
    rw [actLayer, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    exact (congrArg WeightedClock.diagonal (funext fun i => (h i).2)).trans
      WeightedClock.diagonal_one

theorem diagonal_const_unitary (L : ℕ) {U : W →L[ℂ] W} (hU : IsUnitary U) :
    IsUnitary (WeightedClock.diagonal (fun _ : Fin L => U)) := by
  have h1 : U† ∘L U = 1 := hU.1
  have h2 : U ∘L U† = 1 := hU.2
  constructor
  · change (WeightedClock.diagonal (fun _ : Fin L => U))† ∘L
      WeightedClock.diagonal (fun _ : Fin L => U) = 1
    rw [diagonal_const_adjoint, diagonal_const_comp, h1, diagonal_const_one]
  · change WeightedClock.diagonal (fun _ : Fin L => U) ∘L
      (WeightedClock.diagonal (fun _ : Fin L => U))† = 1
    rw [diagonal_const_adjoint, diagonal_const_comp, h2, diagonal_const_one]

/-! ### The known coupling network -/

/-- The private-to-public block of the known coupling network on `W`. -/
def coupB (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) : BlockOperator.H m W →L[ℂ] W :=
  extB E (publicExit ((CayleyTransfer.c v : ℂ) • (1 : P →L[ℂ] P))
    ((-(CayleyTransfer.sigma v : ℂ)) • E†) m)

/-- The private block of the known coupling network. -/
def coupD (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) :
    BlockOperator.H m W →L[ℂ] BlockOperator.H m W :=
  chronologicalOperator (1 - (CayleyTransfer.kappa v : ℂ) • (E ∘L E†))
    ((CayleyTransfer.sigma v : ℂ) • E) ((CayleyTransfer.c v : ℂ) • 1)
    ((-(CayleyTransfer.sigma v : ℂ)) • E†) m

theorem wB_eq (Pr : W →L[ℂ] W) (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) :
    wB Pr E v m = coupB E v m ∘L WeightedClock.diagonal (fun _ : Fin m => Pr) := by
  rw [wB, cascB, coupB, extB, extB, comp_assoc, ← smul_comp,
    ChronologicalClockFactorization.publicExit_factor]

theorem cascD_eq (Pr : W →L[ℂ] W) (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) :
    cascD Pr E v m = coupD E v m ∘L WeightedClock.diagonal (fun _ : Fin m => Pr) :=
  ChronologicalClockFactorization.globalPrivateBlock_factor Pr E _ _ _ m

/-- The coupling network conserves energy. -/
theorem coup_energy {E : P →L[ℂ] W} (hE : E† ∘L E = 1) {v : ℝ} (hv : 0 ≤ v) (m : ℕ) (x : W)
    (y : BlockOperator.H m W) :
    ‖wA E v m x + coupB E v m y‖ ^ 2 + ‖coupD E v m y + wC E v m x‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  obtain ⟨hκ, hσ, -, -, -⟩ := cayley_scalars hv
  exact ext_energy hE (coupling_energy E hE _ _ _ hκ hσ m) x y

/-- The known coupling layer `r` of the synchronized SELECT. -/
def coupLayer (E : P →L[ℂ] W) (v : ℝ) (m n r : ℕ) : Work W n m →L[ℂ] Work W n m :=
  WeightedClock.diagonal (fun i => ReuseQuery.slotStep (wA E v m) (coupB E v m) (wC E v m)
    (coupD E v m) (brLen n i) r)

theorem coupLayer_unitary [FiniteDimensional ℂ W] {E : P →L[ℂ] W} (hE : E† ∘L E = 1) {v : ℝ}
    (hv : 0 ≤ v) (m n r : ℕ) : IsUnitary (coupLayer E v m n r) := by
  have h := fun i : Br n => slotStep_unitary (wA E v m) (coupB E v m) (wC E v m) (coupD E v m)
    (coup_energy hE hv m) (brLen n i) r
  constructor
  · change (coupLayer E v m n r)† ∘L coupLayer E v m n r = 1
    rw [coupLayer, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    exact (congrArg WeightedClock.diagonal (funext fun i => (h i).1)).trans
      WeightedClock.diagonal_one
  · change coupLayer E v m n r ∘L (coupLayer E v m n r)† = 1
    rw [coupLayer, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    exact (congrArg WeightedClock.diagonal (funext fun i => (h i).2)).trans
      WeightedClock.diagonal_one

/-- **The synchronized SELECT**: `n` layers, each a known coupling network after the active
private step. -/
theorem select_eq_product (Pr : W →L[ℂ] W) (E : P →L[ℂ] W) (v : ℝ) (m : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    lcuSelect (wA E v m) (wB Pr E v m) (wC E v m) (cascD Pr E v m) n =
      SynchronizedSelect.product (fun r => coupLayer E v m n r ∘L
        actLayer (WeightedClock.diagonal (fun _ : Fin m => Pr)) n r) n := by
  have h := SynchronizedSelect.schedule_eq
    (fun i : Br n => ReuseQuery.slotStep (wA E v m) (wB Pr E v m) (wC E v m) (cascD Pr E v m)
      (brLen n i)) (brLen n) n (brLen_le hn)
  change SynchronizedSelect.product (fun r => WeightedClock.diagonal
    (fun i : Br n => if r < brLen n i then ReuseQuery.slotStep (wA E v m) (wB Pr E v m)
      (wC E v m) (cascD Pr E v m) (brLen n i) r else 1)) n = _ at h
  simp only [ReuseQuery.padded_slotStep, ← ReuseQuery.fullReuse_eq_product] at h
  rw [lcuSelect, ← h]
  congr 1
  funext r
  rw [coupLayer, actLayer, WeightedClock.diagonal_comp]
  congr 1
  funext i
  rw [wB_eq, cascD_eq, slotStep_factor]

/-! ### Query programs -/

/-- One active private step uses two factor queries (`U`, then `U†`) around a known phase. -/
theorem actLayer_implements {X : Type*} (U : X → W →L[ℂ] W) (hU : ∀ x, IsUnitary (U x))
    {G : W →L[ℂ] W} (hG : IsUnitary G) (n m r : ℕ) :
    Implements (fun x => liftU (U x) n m)
      (fun x => actLayer (WeightedClock.diagonal (fun _ : Fin m => (U x)† * G * U x)) n r) 2 := by
  refine ⟨.seq (.seq .queryAdjoint
      (.fixed (actLayer (WeightedClock.diagonal (fun _ : Fin m => G)) n r)
        (actLayer_unitary (diagonal_const_unitary m hG) n r))) .query, fun x => ?_, le_rfl⟩
  simp only [Program.eval_seq, Program.eval_queryAdjoint, Program.eval_fixed, Program.eval_query]
  rw [← liftU_conj (hU x).1 G n m r, star_eq_adjoint, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def, comp_assoc]

/-- **SELECT uses `2n` factor queries.** -/
theorem select_implements [FiniteDimensional ℂ W] (K : Known P W) (q : ℝ) {v : ℝ} (hv : 0 ≤ v)
    (m : ℕ) {n : ℕ} (hn : 1 ≤ n) {X : Type*} (U : X → W →L[ℂ] W) (hU : ∀ x, IsUnitary (U x)) :
    Implements (fun x => liftU (U x) n m)
      (fun x => lcuSelect (wA K.E v m) (wB (K.priv q (U x)) K.E v m) (wC K.E v m)
        (cascD (K.priv q (U x)) K.E v m) n) (n * 2) := by
  have hLayer : ∀ r < n, Implements (fun x => liftU (U x) n m)
      (fun x => coupLayer K.E v m n r ∘L
        actLayer (WeightedClock.diagonal (fun _ : Fin m => K.priv q (U x))) n r) 2 := by
    intro r _
    have h := (Implements.fixed (O := fun x => liftU (U x) n m) (coupLayer K.E v m n r)
      (coupLayer_unitary K.E_isometry hv m n r)).mul
      (actLayer_implements U hU (K.phase_isUnitary q) n m r)
    simpa only [Nat.zero_add, Known.priv, ContinuousLinearMap.mul_def] using h
  exact (SynchronizedSelect.implements_product_uniform _ _ 2 n hLayer).congr
    (fun x => (select_eq_product _ _ _ _ hn).symm)

/-! ### Repeated amplification rounds -/

section Amplification

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- `R` rounds of the three-SELECT amplification circuit. -/
def ampCirc (S : K →L[ℂ] K) (I J : P →L[ℂ] K) : ℕ → K →L[ℂ] K
  | 0 => S
  | r + 1 => AmplificationQuery.threeSelect (ampCirc S I J r) I J

theorem threeSelect_unitary {S : K →L[ℂ] K} (hS : IsUnitary S) {I J : P →L[ℂ] K}
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) : IsUnitary (AmplificationQuery.threeSelect S I J) := by
  have hRI := AmplificationQuery.reflection_unitary I hI
  have hRJ := AmplificationQuery.reflection_unitary J hJ
  have h := ((((hS.mul hRI).mul hS.adjoint).mul hRJ).mul hS)
  have heq : AmplificationQuery.threeSelect S I J =
      -(S * rangeReflection I * star S * rangeReflection J * S) := by
    rw [AmplificationQuery.threeSelect, star_eq_adjoint]
    simp only [ContinuousLinearMap.mul_def, comp_assoc]
  rw [heq]
  constructor
  · rw [star_neg, neg_mul_neg]; exact h.1
  · rw [star_neg, neg_mul_neg]; exact h.2

theorem ampCirc_unitary {S : K →L[ℂ] K} (hS : IsUnitary S) {I J : P →L[ℂ] K}
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) (r : ℕ) : IsUnitary (ampCirc S I J r) := by
  induction r with
  | zero => exact hS
  | succ r ih => exact threeSelect_unitary ih hI hJ

/-- The amplified circuit applied to the input preparation is the iterated amplification. -/
theorem ampIter_eq_ampCirc {S : K →L[ℂ] K} (hS : IsUnitary S) {I J : P →L[ℂ] K}
    (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) (r : ℕ) :
    ampIter J (S ∘L I) r = ampCirc S I J r ∘L I := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [ampIter, ih, ampCirc]
    exact AmplificationQuery.reflectedAmplification_eq_threeSelect _ I J
      (ampCirc_unitary hS hI hJ r).2

/-- `R` rounds use `3^R` calls of SELECT. -/
theorem ampCirc_implements {X : Type*} {O S : X → K →L[ℂ] K} {c : ℕ}
    (hS : Implements O S c) {I J : P →L[ℂ] K} (hI : I† ∘L I = 1) (hJ : J† ∘L J = 1) (r : ℕ) :
    Implements O (fun x => ampCirc (S x) I J r) (3 ^ r * c) := by
  induction r with
  | zero => simpa [ampCirc] using hS
  | succ r ih =>
    have h := AmplificationQuery.threeSelect_implements I J hI hJ ih
    have e : 3 ^ (r + 1) * c = 3 * (3 ^ r * c) := by ring
    rw [e]
    exact h

end Amplification

end

end SignedFactorSimulation
