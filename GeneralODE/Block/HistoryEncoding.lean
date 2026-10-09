import GeneralODE.Block.HistoryBlock

/-!
# The history block encoding as one unitary

Fix one unitary `q` on an ancilla space `PB` and two pairs of isometric
encodings `E_in b, E_out b : n → PB` (`b = true` encodes the matrix block
`B_U`, `b = false` a block `B₀` close to the identity).  Then:

* the `i`-th factor of the power circuit is the standard form of `I ⊗ q`
  with control-selected encodings, using `E true` on the control values with
  `i < k`; its block is the control-selected family of `B_U` and `B₀`;
* `K` fresh factors have the block `|k, s⟩⟨k, s| ⊗ P_k` with
  `P_k = B₀^{K-k} B_U^k`, so every power uses exactly `K` calls of `q`;
* the history unitary `U_M` is the standard form of the term-selected slot
  unitaries after the power circuit, with the slot-dependent coefficient
  states of `HistoryBlock`; its block is `N⁻¹ (P₀ - S - C)`.
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit History
open scoped InnerProduct BigOperators ComplexConjugate
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

section Helpers

theorem adjoint_comp_self_of_isUnitary {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U : H →L[ℂ] H} (hU : IsUnitary U) : U† ∘L U = 1 := by
  have h := hU.1
  rwa [ContinuousLinearMap.star_eq_adjoint] at h

theorem comp_adjoint_self_of_isUnitary {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {U : H →L[ℂ] H} (hU : IsUnitary U) : U ∘L U† = 1 := by
  have h := hU.2
  rwa [ContinuousLinearMap.star_eq_adjoint] at h

/-- Selected unitaries form a unitary. -/
theorem selMap_unitary {C α : Type*} [Fintype C] [Fintype α]
    (U : C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)) (hU : ∀ c, IsUnitary (U c)) :
    IsUnitary (selMap U) := by
  constructor
  · rw [ContinuousLinearMap.star_eq_adjoint]
    exact selMap_isometry U (fun c => adjoint_comp_self_of_isUnitary (hU c))
  · rw [ContinuousLinearMap.star_eq_adjoint]
    change selMap U ∘L (selMap U)† = 1
    rw [selMap_adjoint, selMap_comp]
    simp only [fun c => comp_adjoint_self_of_isUnitary (hU c)]
    exact selMap_one

/-- Compositions of isometries are isometries. -/
theorem isometry_comp {A B C : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
    (F : B →L[ℂ] C) (G : A →L[ℂ] B) (hF : F† ∘L F = 1) (hG : G† ∘L G = 1) :
    (F ∘L G)† ∘L (F ∘L G) = 1 := by
  rw [adjoint_comp]
  calc G† ∘L F† ∘L (F ∘L G) = G† ∘L (F† ∘L F) ∘L G := by simp only [comp_assoc]
    _ = 1 := by rw [hF, one_comp_eq]; exact hG

/-- The line through a vector, as a map from the one-dimensional space. -/
def lineMap {ι : Type*} [Fintype ι] (u : EuclideanSpace ℂ ι) :
    EuclideanSpace ℂ Unit →L[ℂ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => v () • u
      map_add' := by intro v w; simp [add_smul]
      map_smul' := by intro c v; simp [smul_smul] }

theorem lineMap_apply {ι : Type*} [Fintype ι] (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ Unit) :
    lineMap u v = v () • u := rfl

theorem lineMap_isometry {ι : Type*} [Fintype ι] (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    (lineMap u)† ∘L lineMap u = 1 := by
  rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self]
  intro v
  rw [lineMap_apply, norm_smul, hu, mul_one, EuclideanSpace.norm_eq, Fintype.sum_unique,
    Real.sqrt_sq (norm_nonneg _)]

/-- A unit vector is the image of a basis vector under a unitary. -/
theorem exists_unitary_single {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (u : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) :
    ∃ W : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι,
      IsUnitary W ∧ W (EuclideanSpace.single a 1) = u := by
  obtain ⟨W, hW, hWA⟩ := exists_unitary_comp (P := EuclideanSpace ℂ Unit)
    (V := EuclideanSpace ℂ ι) (lineMap (EuclideanSpace.single a 1)) (lineMap u)
    (lineMap_isometry _ (by simp)) (lineMap_isometry u hu)
  refine ⟨W, hW, ?_⟩
  have h := congrArg (fun T : EuclideanSpace ℂ Unit →L[ℂ] EuclideanSpace ℂ ι =>
    T (EuclideanSpace.single () 1)) hWA
  simpa [lineMap_apply] using h

end Helpers

section Powers

variable {α : Type*} [Ring α]

/-- Ordered products of a threshold family. -/
theorem ordProd_threshold {σ : Type} [Fintype σ]
    (BU B0 : EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ σ) (k : ℕ) :
    ∀ K', ordProd (fun i => if i < k then BU else B0) K' = B0 ^ (K' - k) * BU ^ (min k K')
  | 0 => by simp [ordProd]
  | K' + 1 => by
      change (if K' < k then BU else B0) * ordProd (fun i => if i < k then BU else B0) K' = _
      rw [ordProd_threshold BU B0 k K']
      by_cases h : K' < k
      · rw [if_pos h, Nat.sub_eq_zero_of_le (by omega : K' + 1 ≤ k),
          Nat.sub_eq_zero_of_le (by omega : K' ≤ k), min_eq_right (by omega : K' ≤ k),
          min_eq_right (by omega : K' + 1 ≤ k)]
        simp [pow_succ']
      · rw [if_neg h, min_eq_left (by omega : k ≤ K'), min_eq_left (by omega : k ≤ K' + 1),
          show K' + 1 - k = (K' - k) + 1 by omega, pow_succ', mul_assoc]

end Powers

section Factors

variable {n PB : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]
variable (m K : ℕ)

/-- Control register of the power circuit: the power index and the slot. -/
abbrev Ctl (m K : ℕ) := Fin (K + 1) × Slot m

/-- Control-selected encodings for the `i`-th factor. -/
def facEnc (E : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB)) (i : ℕ) :
    EuclideanSpace ℂ (Ctl m K × n) →L[ℂ] EuclideanSpace ℂ (Ctl m K × PB) :=
  selMap (fun c : Ctl m K => E (decide (i < c.1.val)))

variable {m K}

omit [DecidableEq n] [DecidableEq PB] in
theorem facEnc_isometry (E : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hE : ∀ b, (E b)† ∘L E b = 1) (i : ℕ) :
    (facEnc m K E i)† ∘L facEnc m K E i = 1 :=
  selMap_isometry _ (fun _ => hE _)

/-- The selected block family of one factor. -/
def selBlock (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (b : Bool) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (Eout b)† ∘L q ∘L Ein b

/-- The `i`-th factor: standard form of `I ⊗ q` with selected encodings. -/
def factor (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (i : ℕ) :
    EuclideanSpace ℂ ((Ctl m K × n) × (Ctl m K × PB)) →L[ℂ]
      EuclideanSpace ℂ ((Ctl m K × n) × (Ctl m K × PB)) :=
  standardForm (((0 : Fin (K + 1)), (none : Slot m)), i0) (((0 : Fin (K + 1)), (none : Slot m)), pb0)
    (facEnc m K Ein i) (facEnc m K Eout i) (facEnc_isometry Ein hin i)
    (facEnc_isometry Eout hout i) (specHom (Ctl m K) PB q)

theorem factor_unitary (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (hq : IsUnitary q) (i : ℕ) :
    IsUnitary (factor (m := m) (K := K) i0 pb0 Ein Eout hin hout q i) :=
  standardForm_unitary _ _ _ _ _ _ _ (isUnitary_map _ hq)

/-- Clean ancilla of one factor. -/
def facClean (pb0 : PB) : Ctl m K × PB := (((0 : Fin (K + 1)), (none : Slot m)), pb0)

theorem blk_factor (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (i : ℕ) :
    blk (EuclideanSpace.single (facClean (m := m) (K := K) pb0) 1)
        (EuclideanSpace.single (facClean (m := m) (K := K) pb0) 1)
        (factor (m := m) (K := K) i0 pb0 Ein Eout hin hout q i) =
      selMap (fun c : Ctl m K => selBlock Ein Eout q (decide (i < c.1.val))) := by
  unfold factor facClean
  rw [blk_standardForm, facEnc, facEnc, selMap_block]
  rfl

/-- The power block `P_k = B₀^{K-k} B_U^k`. -/
def powBlock (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (K : ℕ) (k : Fin (K + 1)) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  selBlock Ein Eout q false ^ (K - k.val) * selBlock Ein Eout q true ^ k.val

/-- The power circuit with `K` fresh factors. -/
def powCircuit (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) :
    EuclideanSpace ℂ ((Ctl m K × n) × Anc (Ctl m K × PB) K) →L[ℂ]
      EuclideanSpace ℂ ((Ctl m K × n) × Anc (Ctl m K × PB) K) :=
  powOp (factor (m := m) (K := K) i0 pb0 Ein Eout hin hout q) K

theorem powCircuit_unitary (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (hq : IsUnitary q) :
    IsUnitary (powCircuit (m := m) (K := K) i0 pb0 Ein Eout hin hout q) :=
  powOp_unitary _ (factor_unitary i0 pb0 Ein Eout hin hout q hq) K

/-- Clean ancilla of the power circuit. -/
def powClean (pb0 : PB) : Anc (Ctl m K × PB) K := cleanAnc (facClean (m := m) (K := K) pb0) K

theorem blk_powCircuit (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) :
    blk (EuclideanSpace.single (powClean (m := m) (K := K) pb0) 1)
        (EuclideanSpace.single (powClean (m := m) (K := K) pb0) 1)
        (powCircuit (m := m) (K := K) i0 pb0 Ein Eout hin hout q) =
      selMap (fun c : Ctl m K => powBlock Ein Eout q K c.1) := by
  unfold powCircuit powClean
  rw [blk_powOp]
  simp only [blk_factor]
  rw [ordProd_selMap]
  congr 1
  funext c
  have h : (fun i => selBlock Ein Eout q (decide (i < c.1.val))) =
      (fun i => if i < c.1.val then selBlock Ein Eout q true else selBlock Ein Eout q false) := by
    funext i
    by_cases hi : i < c.1.val <;> simp [hi]
  rw [h, ordProd_threshold, min_eq_left (Nat.lt_succ_iff.mp c.1.isLt)]
  rfl

end Factors

section History

variable {n PB : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]
variable {m K : ℕ}

/-- Ancilla register of the power circuit. -/
abbrev PowAnc (PB : Type) (m K : ℕ) := Anc (Ctl m K × PB) K

/-- Ancilla register of the history unitary. -/
abbrev HistAnc (n PB : Type) (m K : ℕ) := Term × ((Ctl m K × n) × PowAnc PB m K)

/-- Encoding map of the history unitary, from coefficient states. -/
def histEnc (φ : Slot m → EuclideanSpace ℂ (Term × Fin (K + 1))) (pb0 : PB) :
    EuclideanSpace ℂ (Slot m × n) →L[ℂ] EuclideanSpace ℂ (Term × ((Ctl m K × n) × PowAnc PB m K)) :=
  selMap (fun _ : Term => ketR (σ := Ctl m K × n)
      (EuclideanSpace.single (powClean (m := m) (K := K) pb0) 1)) ∘L
    coefMap (n := n) φ

omit [DecidableEq n] in
theorem histEnc_isometry (φ : Slot m → EuclideanSpace ℂ (Term × Fin (K + 1)))
    (hφ : ∀ s, ‖φ s‖ = 1) (pb0 : PB) :
    (histEnc (n := n) φ pb0)† ∘L histEnc φ pb0 = 1 :=
  isometry_comp _ _ (selMap_isometry _ (fun _ => ketR_isometry _ (by simp)))
    (coefMap_isometry φ hφ)

/-- The core unitary: term-selected slot unitaries after the power circuit. -/
def histCore (Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (POW : EuclideanSpace ℂ ((Ctl m K × n) × PowAnc PB m K) →L[ℂ]
      EuclideanSpace ℂ ((Ctl m K × n) × PowAnc PB m K)) :
    EuclideanSpace ℂ (Term × ((Ctl m K × n) × PowAnc PB m K)) →L[ℂ]
      EuclideanSpace ℂ (Term × ((Ctl m K × n) × PowAnc PB m K)) :=
  selMap (fun t => actLeft (α := PowAnc PB m K)
      (liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t))) *
    specHom Term ((Ctl m K × n) × PowAnc PB m K) POW

theorem slotUnitaries_unitary (Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (hRc : IsUnitary Rc) (t : Term) : IsUnitary (slotUnitaries Rc t) := by
  cases t
  · exact isUnitary_one
  · exact LookupOracle.permutationUnitary_unitary _
  · exact hRc
  · exact isUnitary_one
  · exact isUnitary_one

omit [DecidableEq n] [DecidableEq PB] in
theorem histCore_unitary (Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (hRc : IsUnitary Rc)
    (POW : EuclideanSpace ℂ ((Ctl m K × n) × PowAnc PB m K) →L[ℂ]
      EuclideanSpace ℂ ((Ctl m K × n) × PowAnc PB m K)) (hPOW : IsUnitary POW) :
    IsUnitary (histCore Rc POW) :=
  (selMap_unitary _ (fun t => isUnitary_map _ (isUnitary_map _
    (slotUnitaries_unitary Rc hRc t)))).mul (isUnitary_map _ hPOW)

omit [DecidableEq n] in
/-- The block of the core between the history encodings. -/
theorem histCore_block (φin φout : Slot m → EuclideanSpace ℂ (Term × Fin (K + 1))) (pb0 : PB)
    (Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m))
    (POW : EuclideanSpace ℂ ((Ctl m K × n) × PowAnc PB m K) →L[ℂ]
      EuclideanSpace ℂ ((Ctl m K × n) × PowAnc PB m K))
    (Pk : Fin (K + 1) → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (hPOW : blk (EuclideanSpace.single (powClean (m := m) (K := K) pb0) 1)
        (EuclideanSpace.single (powClean (m := m) (K := K) pb0) 1) POW =
      selMap (fun c : Ctl m K => Pk c.1)) :
    (histEnc (n := n) φout pb0)† ∘L histCore Rc POW ∘L histEnc φin pb0 =
      (coefMap φout)† ∘L
        selMap (fun t => liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t)) ∘L
        specHom Term ((Fin (K + 1) × Slot m) × n) (selMap (fun c' : Fin (K + 1) × Slot m => Pk c'.1)) ∘L
        coefMap φin := by
  set e : EuclideanSpace ℂ (PowAnc PB m K) := EuclideanSpace.single (powClean (m := m) (K := K) pb0) 1
  have hadj : (selMap (fun _ : Term => ketR (σ := Ctl m K × n) e))† =
      selMap (fun _ : Term => braR (σ := Ctl m K × n) e) := by
    rw [selMap_adjoint]
    simp only [ketR_adjoint]
  -- the slot unitaries commute with removing the clean ancilla
  have hslot : selMap (fun _ : Term => braR (σ := Ctl m K × n) e) ∘L
      selMap (fun t => actLeft (α := PowAnc PB m K)
        (liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t))) =
      selMap (fun t => liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t)) ∘L
        selMap (fun _ : Term => braR (σ := Ctl m K × n) e) := by
    rw [selMap_comp, selMap_comp]
    congr 1
    funext t
    ext1 w
    exact braR_actLeft _ e w
  -- the power circuit between the clean ancillas is its block
  have hpow : selMap (fun _ : Term => braR (σ := Ctl m K × n) e) ∘L
      specHom Term ((Ctl m K × n) × PowAnc PB m K) POW ∘L
      selMap (fun _ : Term => ketR (σ := Ctl m K × n) e) =
      specHom Term ((Fin (K + 1) × Slot m) × n) (selMap (fun c' : Fin (K + 1) × Slot m => Pk c'.1)) := by
    rw [← hadj, selMap_block, ← selMap_const]
    congr 1
    funext t
    rw [ketR_adjoint]
    exact hPOW
  unfold histEnc histCore
  rw [adjoint_comp, hadj]
  simp only [ContinuousLinearMap.mul_def]
  calc (coefMap φout)† ∘L selMap (fun _ : Term => braR (σ := Ctl m K × n) e) ∘L
        (selMap (fun t => actLeft (α := PowAnc PB m K)
          (liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t))) ∘L
          specHom Term ((Ctl m K × n) × PowAnc PB m K) POW) ∘L
        selMap (fun _ : Term => ketR (σ := Ctl m K × n) e) ∘L coefMap φin
      = (coefMap φout)† ∘L
          (selMap (fun _ : Term => braR (σ := Ctl m K × n) e) ∘L
            selMap (fun t => actLeft (α := PowAnc PB m K)
              (liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t)))) ∘L
          (specHom Term ((Ctl m K × n) × PowAnc PB m K) POW ∘L
            selMap (fun _ : Term => ketR (σ := Ctl m K × n) e)) ∘L coefMap φin := by
        simp only [comp_assoc]
    _ = (coefMap φout)† ∘L
          selMap (fun t => liftSlot (n := n) (P := Fin (K + 1)) (slotUnitaries Rc t)) ∘L
          (selMap (fun _ : Term => braR (σ := Ctl m K × n) e) ∘L
            specHom Term ((Ctl m K × n) × PowAnc PB m K) POW ∘L
            selMap (fun _ : Term => ketR (σ := Ctl m K × n) e)) ∘L coefMap φin := by
        rw [hslot]
        simp only [comp_assoc]
    _ = _ := by rw [hpow]

end History

section Assembly

variable {n PB : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]

/-- All data of the history block encoding. -/
structure HistData (n PB : Type) [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB] where
  m : ℕ
  K : ℕ
  N : ℝ
  c : ℕ → ℝ
  d : ℕ → ℝ
  i0 : n
  pb0 : PB
  Ein : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB)
  Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB)
  hin : ∀ b, (Ein b)† ∘L Ein b = 1
  hout : ∀ b, (Eout b)† ∘L Eout b = 1
  Rc : EuclideanSpace ℂ (Slot m) →L[ℂ] EuclideanSpace ℂ (Slot m)
  N_pos : 0 < N
  c_nonneg : ∀ k, 0 ≤ c k
  d_nonneg : ∀ k, 0 ≤ d k
  restIn_le : ∀ s, restIn m K N c d s ≤ 1
  restOut_le : ∀ s, restOut m K N c d s ≤ 1
  Rc_unitary : IsUnitary Rc
  Rc_none : ∀ s', entry Rc s' none = uniformSlots m s'

/-- System register of the history unitary. -/
abbrev HistData.Sys (H : HistData n PB) := Slot H.m × n

/-- Ancilla register of the history unitary. -/
abbrev HistData.Anc (H : HistData n PB) := HistAnc n PB H.m H.K

/-- Clean ancilla of the history unitary. -/
def HistData.clean (H : HistData n PB) : H.Anc :=
  (Term.id, ((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0), powClean (m := H.m) (K := H.K) H.pb0))

def HistData.inEnc (H : HistData n PB) : EuclideanSpace ℂ H.Sys →L[ℂ] EuclideanSpace ℂ H.Anc :=
  histEnc (n := n) (stateIn H.m H.K H.N H.c H.d) H.pb0

def HistData.outEnc (H : HistData n PB) : EuclideanSpace ℂ H.Sys →L[ℂ] EuclideanSpace ℂ H.Anc :=
  histEnc (n := n) (stateOut H.m H.K H.N H.c H.d) H.pb0

theorem HistData.inEnc_isometry (H : HistData n PB) : H.inEnc† ∘L H.inEnc = 1 :=
  histEnc_isometry _ (stateIn_norm H.N_pos H.c_nonneg H.d_nonneg H.restIn_le) H.pb0

theorem HistData.outEnc_isometry (H : HistData n PB) : H.outEnc† ∘L H.outEnc = 1 :=
  histEnc_isometry _ (stateOut_norm H.N_pos H.c_nonneg H.d_nonneg H.restOut_le) H.pb0

/-- The power circuit for one fixed `q`. -/
def HistData.pow (H : HistData n PB) (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) :
    EuclideanSpace ℂ ((Ctl H.m H.K × n) × PowAnc PB H.m H.K) →L[ℂ]
      EuclideanSpace ℂ ((Ctl H.m H.K × n) × PowAnc PB H.m H.K) :=
  powCircuit (m := H.m) (K := H.K) H.i0 H.pb0 H.Ein H.Eout H.hin H.hout q

/-- The history unitary for one fixed `q`. -/
def HistData.unitary (H : HistData n PB) (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) :
    EuclideanSpace ℂ (H.Sys × H.Anc) →L[ℂ] EuclideanSpace ℂ (H.Sys × H.Anc) :=
  standardForm ((none : Slot H.m), H.i0) H.clean H.inEnc H.outEnc H.inEnc_isometry
    H.outEnc_isometry (histCore H.Rc (H.pow q))

theorem HistData.unitary_isUnitary (H : HistData n PB) (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (hq : IsUnitary q) : IsUnitary (H.unitary q) :=
  standardForm_unitary _ _ _ _ _ _ _ (histCore_unitary H.Rc H.Rc_unitary _
    (powCircuit_unitary _ _ _ _ _ _ q hq))

/-- The power blocks `P_k = B₀^{K-k} B_U^k` of `q`. -/
def HistData.Pk (H : HistData n PB) (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) (k : Fin (H.K + 1)) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  powBlock H.Ein H.Eout q H.K k

/-- Exact block of the history unitary: `N⁻¹` times the implemented residual. -/
theorem HistData.block_unitary (H : HistData n PB) (q : EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (y : EuclideanSpace ℂ H.Sys) (s' : Slot H.m) (i : n) :
    blk (EuclideanSpace.single H.clean 1) (EuclideanSpace.single H.clean 1) (H.unitary q) y (s', i) =
      ((1 / H.N : ℝ) : ℂ) * (residual H.m (H.Pk q 0) (stepPoly H.c (H.Pk q))
        (stepPoly H.d (H.Pk q))
        ((RegisterEquivalences.productFlatten (Slot H.m) n).symm y)) s' i := by
  unfold HistData.unitary
  rw [blk_standardForm]
  have hcore := histCore_block (n := n) (stateIn H.m H.K H.N H.c H.d)
    (stateOut H.m H.K H.N H.c H.d) H.pb0 H.Rc (H.pow q) (H.Pk q)
    (blk_powCircuit (m := H.m) (K := H.K) H.i0 H.pb0 H.Ein H.Eout H.hin H.hout q)
  unfold HistData.inEnc HistData.outEnc
  rw [hcore]
  exact block_eq_residual H.N_pos H.c_nonneg H.d_nonneg (H.Pk q) H.Rc H.Rc_none y s' i

end Assembly

end

end SparseHamiltonian.GeneralODE.Registers
