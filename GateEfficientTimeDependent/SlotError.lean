import GateEfficientTimeDependent.SlotSim

/-!
# The amplified slot-selected simulator and its error

The LCU circuit (`LCUT`) and one amplification round (`AMPT`) of the
released construction, with the slot-selected private call.  Between clean
inputs the LCU circuit is the signed average of coherent-reuse successful
blocks (`lcu_blockT`), whose effective transducer blocks are exactly those of
the slot-dependent chronological clock of `hs:thm:time`:
`netB ∘ (⊕ₖ D k) = exitV D J c σ` and `netG ∘ (⊕ₖ D k) = privateV D J c κ σ`
for `J = U_J ι₀` (`netB_slot`, `netG_slot`).  The released amplified
implementation `TimeDependent.implementationV` therefore has the same
successful block, and `GateBlockTransfer.amplified_error_le` transfers its
full-output error bound `2 δ` against the ordered product of the local
Cayley steps (`TimeDependent.exists_precise_implementationV`).  Each Cayley
step is within `w³` of the slot exponential, so on `2^m ≥ steps τ (ε/3)`
slots the ideal amplified circuit is within `ε` of the ordered product of
the slot exponentials `exp (-i w H k)`, `w = τ / 2^m` (`ampT_error`).

`simulationT` collects the gate-level statement: the released circuit
`ampI` with `2^m` slots (`simCircuitT`) consists of valid elementary
instructions, makes exactly `6 d` slot-selected private calls and `12 d`
calls of `U_J` or `U_J†`, uses at most `200 (d+1)(a+m+r+1)` elementary
gates on `2a + 3m + 6r + 3` wires, and approximates the ordered product
within `ε` on clean inputs, including every work register.  Only the slots
`k < 2^m` enter the hypotheses.
-/

namespace SparseHamiltonian.GateCircuit.SlotSim

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open scoped InnerProduct BigOperators
open GatePointerEncoding (wordValue wordEquivFin wordFin)
open ChronologicalResolvent GlobalColligation ChronologicalCatalyst GlobalResolvent
  CoherentReuse FiniteChronologicalInverse

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The LCU circuit -/

variable {L : ℕ}

/-- The ideal LCU circuit with the slot-selected private call. -/
def LCUT (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (N : ℕ) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  (PREP (fOut wt))† ∘L (RANGE hL nOf)† ∘L selectNT c σ UJ D N ∘L RANGE hL nOf ∘L PREP (fIn wt)

/-- **The LCU block.** Between clean inputs the LCU circuit is the signed
average of the coherent-reuse successful blocks of the slot action. -/
theorem lcu_blockT (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (N : ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ N) (hN : N ≤ cap r) (hr : 0 < r)
    (wt : Fin L → ℝ) (hwt : ∑ ℓ, |wt ℓ| = 2) (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (hκ : κ = 1 - c) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hUJ : UJ ∘L UJ† = 1) (ψ ψ' : P) :
    inner ℂ (bas (fun _ => false) ψ')
        (LCUT (K := K) (m := m) hL nOf wt c σ UJ D N (bas (fun _ => false) ψ)) =
      inner ℂ ψ' ((∑ ℓ, ((wt ℓ / 2 : ℝ) : ℂ) • successfulBlock (V := HV a m P) (blkA c (2 ^ m))
        (netB (m := m) c σ UJ ∘L TimeDependent.slotAction D (2 ^ m)) (netC (m := m) c σ UJ)
        (netG (m := m) c κ σ UJ ∘L TimeDependent.slotAction D (2 ^ m)) (nOf ℓ)) ψ) := by
  have hn' : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ 2 ^ r := fun ℓ =>
    ⟨(hn ℓ).1, by have := (hn ℓ).2; have := cap_succ r; omega⟩
  rw [LCUT, comp_apply, comp_apply, comp_apply, comp_apply, adjoint_inner_right,
    adjoint_inner_right,
    range_prep_zero hL nOf hn' hr _ (fOut_sq_sum wt hwt hL) (fun w hw => fOut_eq_zero wt hL w hw),
    range_prep_zero hL nOf hn' hr _ (fIn_sq_sum wt hwt hL) (fun w hw => fIn_eq_zero wt hL w hw),
    map_sum]
  simp only [map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  rw [sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [Finset.sum_eq_single ℓ]
  · rw [select_blockT c κ σ hunit hκ UJ D hUJ _ _ N (hn ℓ).2 hN ψ ψ', smul_apply,
      inner_smul_right, ← mul_assoc]
    congr 1
    rw [← fOut_mul_fIn wt hL ℓ]
    push_cast
    ring
  · intro ℓ' _ hne
    rw [selectNT_emb c κ σ hunit hκ UJ D hUJ N,
      inner_emb_ne _ _ (fun h => hne (labWord_injective hL h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem pres2_LCUT (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (N : ℕ) :
    Pres2 Clean (LCUT (K := K) (m := m) hL nOf wt c σ UJ D N) :=
  (pres2_PREP _).adj.comp ((pres2_RANGE _ _).adj.comp ((pres2_selectNT _ _ _ _ _).comp
    ((pres2_RANGE _ _).comp (pres2_PREP _))))

theorem LCUT_isUnitary (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k)) (N : ℕ) :
    IsUnitary (LCUT (K := K) (m := m) hL nOf wt c σ UJ D N) :=
  isUnitary_comp (isUnitary_adj (PREP_isUnitary _))
    (isUnitary_comp (isUnitary_adj (RANGE_isUnitary _ _))
      (isUnitary_comp (selectNT_isUnitary _ _ hunit _ _ hUJ hD _)
        (isUnitary_comp (RANGE_isUnitary _ _) (PREP_isUnitary _))))

theorem lcuT_agrees (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ)
    (hn : ∀ ℓ, nOf ℓ < 2 ^ r) (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (runT UJ D (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N))
      (LCUT hL nOf wt c σ UJ D N) := by
  have hKr : r ≤ K + 1 := by omega
  rw [lcuI, runT_append, runT_append, runT_append, runT_append, runT_ofGates, runT_ofGates,
    runT_ofGates, runT_ofGates, LCUT]
  have h1 := prep_agrees (P := P) (a := a) (m := m) (K := K) (fIn wt) hKr
  have h2 := range_agrees (P := P) (a := a) (m := m) (K := K) hL nOf hn hKr
  have h3 := selectT_agrees (r := r) UJ D c σ hK N
  have h4 := gInv_agrees _ _ (rangeG_ok hL nOf) h2 (RANGE_isUnitary _ _) (pres2_RANGE _ _).2
  have h5 := gInv_agrees _ _ (prepG_ok (fOut wt)) (prep_agrees (P := P) (a := a) (m := m) (K := K)
    (fOut wt) hKr) (PREP_isUnitary _) (pres2_PREP _).2
  exact (((h1.comp (pres2_PREP _).1 h2).comp ((pres2_RANGE _ _).comp (pres2_PREP _)).1 h3).comp
    ((pres2_selectNT _ _ _ _ _).comp ((pres2_RANGE _ _).comp (pres2_PREP _))).1 h4).comp
    ((pres2_RANGE _ _).adj.comp ((pres2_selectNT _ _ _ _ _).comp
      ((pres2_RANGE _ _).comp (pres2_PREP _)))).1 h5

/-! ### One amplification round -/

/-- The ideal amplified circuit with the slot-selected private call. -/
def AMPT (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (N : ℕ) :
    Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  -(LCUT hL nOf wt c σ UJ D N ∘L ZR ∘L (LCUT hL nOf wt c σ UJ D N)† ∘L ZR ∘L
    LCUT hL nOf wt c σ UJ D N)

theorem AMPT_io (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ)
    (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) (N : ℕ)
    (hLCU : LCUT (K := K) (m := m) hL nOf wt c σ UJ D N ∘L (LCUT hL nOf wt c σ UJ D N)† = 1) :
    AMPT (K := K) (m := m) hL nOf wt c σ UJ D N ∘L io =
      reflectedAmplification io (LCUT hL nOf wt c σ UJ D N ∘L io) := by
  set X := LCUT (K := K) (m := m) hL nOf wt c σ UJ D N
  have e : X ∘L ((1 : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) ∘L X†) = X ∘L X† := by
    ext v; rfl
  have h1 : rangeReflection (X ∘L io) = X ∘L ZR ∘L X† := by
    simp only [rangeReflection, ZR, adjoint_comp, comp_sub, sub_comp, comp_smul, smul_comp,
      comp_assoc]
    rw [e, hLCU]
  rw [reflectedAmplification, h1]
  simp only [AMPT, neg_comp, comp_assoc]
  rfl

theorem ampT_agrees (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (N : ℕ) (hn : ∀ ℓ, nOf ℓ < 2 ^ r) (hK : a + m + 2 * r ≤ K) :
    Agrees Clean (runT UJ D (ampI (a := a) (m := m) (K := K) hL nOf wt c σ N))
      (AMPT hL nOf wt c σ UJ D N) := by
  have hl := lcuT_agrees (P := P) (a := a) (m := m) (K := K) UJ D hL nOf wt c σ N hn hK
  have hlu := LCUT_isUnitary (K := K) (m := m) hL nOf wt c σ hunit UJ D hUJ hD N
  have hrunU : IsUnitary (runT (m := m) (r := r) (K := K) UJ D
      (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N)) :=
    runT_isUnitary UJ D hUJ hD _ (lcuI_valid hL nOf wt c σ hunit N)
  have hinv : Agrees Clean (runT UJ D (invList (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N)))
      ((LCUT (K := K) (m := m) hL nOf wt c σ UJ D N)†) := by
    rw [runT_invList]
    exact hl.adjoint hrunU hlu (pres2_LCUT _ _ _ _ _ _ _ _).2
  have hz := zr_agrees (P := P) (a := a) (m := m) (r := r) (K := K) (by omega)
  have hp : Agrees Clean (gRun (Q := P) [phaseG (a := a) (m := m) (r := r) (K := K)])
      (-1 : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) := by
    rw [gRun_singleton, phaseG_op]
    exact Agrees.refl _ _
  rw [ampI, runT_append, runT_append, runT_append, runT_append, runT_append, runT_ofGates,
    runT_ofGates]
  have hLp := pres2_LCUT (K := K) (m := m) (P := P) hL nOf wt c σ UJ D N
  have e1 := hl.comp hLp.1 hz
  have e2 := e1.comp (pres2_ZR.comp hLp).1 hinv
  have e3 := e2.comp (hLp.adj.comp (pres2_ZR.comp hLp)).1 hz
  have e4 := e3.comp (pres2_ZR.comp (hLp.adj.comp (pres2_ZR.comp hLp))).1 hl
  have e5 := e4.comp (hLp.comp (pres2_ZR.comp (hLp.adj.comp (pres2_ZR.comp hLp)))).1 hp
  convert e5 using 1
  ext v
  simp [AMPT]

/-- The successful block of the ideal LCU circuit as an operator. -/
theorem lcu_compressionT (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (N : ℕ)
    (hn : ∀ ℓ, 0 < nOf ℓ ∧ nOf ℓ ≤ N) (hN : N ≤ cap r) (hr : 0 < r)
    (wt : Fin L → ℝ) (hwt : ∑ ℓ, |wt ℓ| = 2) (c κ σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (hκ : κ = 1 - c) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hUJ : UJ ∘L UJ† = 1) :
    (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
        (LCUT (K := K) (m := m) hL nOf wt c σ UJ D N ∘L io) =
      ∑ ℓ, ((wt ℓ / 2 : ℝ) : ℂ) • successfulBlock (V := HV a m P) (blkA c (2 ^ m))
        (netB (m := m) c σ UJ ∘L TimeDependent.slotAction D (2 ^ m)) (netC (m := m) c σ UJ)
        (netG (m := m) c κ σ UJ ∘L TimeDependent.slotAction D (2 ^ m)) (nOf ℓ) := by
  ext ψ
  apply ext_inner_left ℂ
  intro ψ'
  rw [comp_apply, adjoint_inner_right, comp_apply, io_apply, io_apply]
  exact lcu_blockT hL nOf N hn hN hr wt hwt c κ σ hunit hκ UJ D hUJ ψ ψ'

/-! ### The effective blocks are those of the slot-dependent clock -/

theorem netB_slot (c σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P) :
    netB (m := m) c σ UJ ∘L TimeDependent.slotAction D (2 ^ m) =
      TimeDependent.exitV D (UJ ∘L iota0) c σ (2 ^ m) := by
  have hB : ((-(σ : ℂ)) • ((iota0 (a := a) (P := P))† ∘L 1)) ∘L UJ† =
      (-(σ : ℂ)) • (UJ ∘L iota0)† := by
    ext v
    simp only [comp_apply, smul_apply, one_apply_eq_self, adjoint_comp]
  rw [netB, blkB, publicExit_comp_diag, hB, TimeDependent.exitV]

theorem netG_slot (c κ σ : ℝ) (UJ : Vsp a P →L[ℂ] Vsp a P) (D : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (hUJ : UJ ∘L UJ† = 1) :
    netG (m := m) c κ σ UJ ∘L TimeDependent.slotAction D (2 ^ m) =
      TimeDependent.privateV D (UJ ∘L iota0) c κ σ (2 ^ m) := by
  have h1 : ∀ v, UJ ((UJ†) v) = v := by
    intro v
    have := congrArg (fun F : Vsp a P →L[ℂ] Vsp a P => F v) hUJ
    simpa using this
  have hR : UJ ∘L localPrivateBlock 1 (iota0 (a := a) (P := P)) κ ∘L UJ† =
      1 - (κ : ℂ) • ((UJ ∘L iota0) ∘L (UJ ∘L iota0)†) := by
    ext v
    simp only [localPrivateBlock, comp_apply, sub_apply, one_apply_eq_self, smul_apply,
      map_sub, map_smul, h1, adjoint_comp]
  have hA : UJ ∘L ((σ : ℂ) • (iota0 (a := a) (P := P))) = (σ : ℂ) • (UJ ∘L iota0) :=
    comp_smul _ _ _
  have hB : ((-(σ : ℂ)) • ((iota0 (a := a) (P := P))† ∘L 1)) ∘L UJ† =
      (-(σ : ℂ)) • (UJ ∘L iota0)† := by
    ext v
    simp only [comp_apply, smul_apply, one_apply_eq_self, adjoint_comp]
  rw [netG, blkG, globalPrivateBlock, chronological_diag, hR, hA, hB, TimeDependent.privateV]

/-! ### Cayley products -/

/-- The Cayley transform of a self-adjoint generator is an isometry. -/
theorem cayley_isometry (H R : P →L[ℂ] P) (w : ℝ) (hH : star H = H)
    (hR : CayleyTransfer.cayleyDenominator w H ∘L R = 1) :
    (CayleyTransfer.cayleyNumerator w H ∘L R)† ∘L (CayleyTransfer.cayleyNumerator w H ∘L R) = 1 := by
  let X : P →L[ℂ] P := (-Complex.I * (w : ℂ)) • H
  have hSkew : star X = -X := by
    simp only [X, star_smul, hH, star_mul, star_neg, Complex.star_def,
      Complex.conj_I, Complex.conj_ofReal]
    module
  have hDen : 1 - (1 / 2 : ℂ) • X = CayleyTransfer.cayleyDenominator w H := by
    simp only [X, CayleyTransfer.cayleyDenominator, smul_smul]
    module
  have hNum : 1 + (1 / 2 : ℂ) • X = CayleyTransfer.cayleyNumerator w H := by
    simp only [X, CayleyTransfer.cayleyNumerator, smul_smul]
    module
  have h := CayleyTransfer.skew_cayley_star_mul_self X R hSkew (by rw [hDen, mul_def]; exact hR)
  rw [hNum, star_eq_adjoint, mul_def, mul_def] at h
  exact h

/-- Ordered products of isometries are isometries. -/
theorem evolution_isometry (U : ℕ → P →L[ℂ] P) (hU : ∀ k, (U k)† ∘L U k = 1) (n : ℕ) :
    (TimeDependent.evolution U n)† ∘L TimeDependent.evolution U n = 1 := by
  induction n with
  | zero =>
      rw [TimeDependent.evolution_zero, ← star_eq_adjoint, star_one, one_def, id_comp]
  | succ n ih =>
      have h1 : (1 : P →L[ℂ] P) ∘L TimeDependent.evolution U n = TimeDependent.evolution U n := by
        ext v; rfl
      rw [TimeDependent.evolution_succ, mul_def, adjoint_comp, comp_assoc,
        ← comp_assoc ((U n)†) (U n), hU n, h1, ih]

theorem isometry_norm_le (A : P →L[ℂ] P) (hA : A† ∘L A = 1) : ‖A‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one (fun v => by
    rw [GateBlockTransfer.norm_apply_of_isometry A hA v, one_mul])

/-- Ordered products depend only on the factors used. -/
theorem evolution_eq_of_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U U' : ℕ → E →L[ℂ] E) (n : ℕ) (h : ∀ k < n, U k = U' k) :
    TimeDependent.evolution U n = TimeDependent.evolution U' n := by
  induction n with
  | zero => rw [TimeDependent.evolution_zero, TimeDependent.evolution_zero]
  | succ n ih =>
      rw [TimeDependent.evolution_succ, TimeDependent.evolution_succ, h n (Nat.lt_succ_self n),
        ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]

/-- The exponential of `-i w H` for a self-adjoint `H` is a contraction. -/
theorem exp_norm_le_one (H : P →L[ℂ] P) (hH : star H = H) (w : ℝ) :
    ‖NormedSpace.exp ((-Complex.I * (w : ℂ)) • H)‖ ≤ 1 := by
  apply CayleyApproximation.skew_exp_norm_le
  simp only [star_smul, hH, star_mul, star_neg, Complex.star_def, Complex.conj_I,
    Complex.conj_ofReal]
  module

/-- The ordered product of Cayley steps is within `n w³` of the ordered
product of the slot exponentials. -/
theorem cayley_evolution_error (H R U : ℕ → P →L[ℂ] P) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hRR : ∀ k, CayleyTransfer.cayleyDenominator w (H k) ∘L R k = 1)
    (hCay : ∀ k, U k = CayleyTransfer.cayleyNumerator w (H k) ∘L R k) (n : ℕ) :
    ‖TimeDependent.evolution U n -
        TimeDependent.evolution (fun k => NormedSpace.exp ((-Complex.I * (w : ℂ)) • H k)) n‖ ≤
      n * w ^ 3 := by
  have hUiso : ∀ k, (U k)† ∘L U k = 1 := by
    intro k
    rw [hCay k]
    exact cayley_isometry (H k) (R k) w (hSelf k) (hRR k)
  apply TimeDependent.evolution_sub_norm_le_mul
  · exact fun k => isometry_norm_le (U k) (hUiso k)
  · exact fun k => exp_norm_le_one (H k) (hSelf k) w
  · intro k
    have hR' : CayleyTransfer.cayleyDenominator w (H k) * R k = 1 := by
      rw [mul_def]; exact hRR k
    have h := CayleyApproximation.hamiltonian_cayley_error (H k) (R k) w hw hw1 (hSelf k) (hH k)
      hR' 1
    rw [pow_one, mul_def, ← hCay k] at h
    simpa using h

/-! ### The released bound for the slot-dependent clock -/

set_option maxRecDepth 8192 in
/-- The released amplified slot-dependent clock, with an explicit budget `W`. -/
theorem releasedV_bound (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P) (J : P →L[ℂ] Vsp a P)
    (H : ℕ → P →L[ℂ] P) (w Q b qbar : ℝ) (T : ℕ) (hQ : 1 ≤ Q) (hw : 0 ≤ w)
    (hwQuarter : w ≤ 1 / 4) (hD : ∀ k, (D k)† ∘L D k = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ k, (1 - D k) ∘L R1 k = 1) (hLeft : ∀ k, R1 k ∘L (1 - D k) = 1)
    (hR1 : ∀ k, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k, J† ∘L R1 k ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k, ‖R1 k ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) (W : ℝ) (hW : (T : ℝ) * w * qbar = W) :
    ∃ U R : ℕ → P →L[ℂ] P, (∀ k, CayleyTransfer.cayleyDenominator w (H k) ∘L R k = 1) ∧
      (∀ k, U k = CayleyTransfer.cayleyNumerator w (H k) ∘L R k) ∧
      ‖AmplifiedSmoothing.implementation (SharpFilterSchedule.length Q)
          (SharpFilterSchedule.depth Q W δ) (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
          (TimeDependent.exitV D J (CayleyTransfer.c w) (CayleyTransfer.sigma w) T)
          (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J) ((CayleyTransfer.c w : ℂ) • 1) T)
          (TimeDependent.privateV D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
            (CayleyTransfer.sigma w) T) -
        SmoothingLCU.output (P := P) (V := BlockOperator.H T (Vsp a P))
          (AveragingPolynomial.filter (SharpFilterSchedule.length Q)
            (SharpFilterSchedule.depth Q W δ)).coeff
          (SharpFilterSchedule.depth Q W δ * (SharpFilterSchedule.length Q - 1)) ∘L
          TimeDependent.evolution U T‖ ≤ 2 * δ ∧
      (SharpFilterSchedule.degree Q W δ : ℝ) ≤ 128 * (W + Q * (1 + Real.log (1 / δ))) := by
  subst hW
  obtain ⟨U, R, hRR, _hRL, hCay, _hIso, hImpl, hDeg⟩ :=
    TimeDependent.exists_precise_implementationV D R1 J H w Q b qbar T hQ hw hwQuarter hD hJ
      hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δ hδ hδOne
  exact ⟨U, R, hRR, hCay, hImpl, hDeg⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- **Error of the ideal amplified slot-selected circuit.**  With `2^m` slots
at least the released subdivision count, a reuse register with
`2d + 2 ≤ 2^r`, and the clock promises at every slot for `J = U_J ι₀`, the
ideal amplified circuit approximates the ordered product of the slot
exponentials on clean inputs within `ε`; the filter degree obeys the released
bound. -/
theorem ampT_error (UJ : Vsp a P →L[ℂ] Vsp a P) (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (H : ℕ → P →L[ℂ] P) (hUJ : IsUnitary UJ) (hDu : ∀ k, IsUnitary (D k))
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : ∀ k, (1 - D k) ∘L R1 k = 1) (hLeft : ∀ k, R1 k ∘L (1 - D k) = 1)
    (hR1 : ∀ k, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : TimeSchedule.steps τ (ε / 3) ≤ 2 ^ m) (hr : 0 < r)
    (hL : (fDeg Q τ qbar ε + 1) + (fDeg Q τ qbar ε + 1) ≤ 2 ^ r) :
    ‖AMPT (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDeg Q τ qbar ε) ∘L io -
      io ∘L TimeDependent.evolution
        (fun k => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H k)) (2 ^ m)‖ ≤ ε ∧
    (fDeg Q τ qbar ε : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (1 / (ε / 3)))) := by
  have hδ : 0 < ε / 3 := by positivity
  have hδ1 : ε / 3 ≤ 1 := by linarith
  obtain ⟨hw0, hwq, hcub, hTw⟩ := schedule_ge τ (ε / 3) hτ hδ (2 ^ m) hm
  change 0 ≤ stepW τ m at hw0
  change stepW τ m ≤ 1 / 4 at hwq
  change ((2 ^ m : ℕ) : ℝ) * stepW τ m ^ 3 ≤ ε / 3 at hcub
  change ((2 ^ m : ℕ) : ℝ) * stepW τ m = τ at hTw
  have hD : ∀ k, (D k)† ∘L D k = 1 := fun k => unitary_adj_comp (hDu k)
  have hUJc : UJ ∘L UJ† = 1 := unitary_comp_adj hUJ
  have hJ : (UJ ∘L iota0)† ∘L (UJ ∘L iota0) = 1 :=
    isometry_comp UJ iota0 (unitary_adj_comp hUJ) iota0_isometry
  obtain ⟨U, R, hRR, hCay, hImpl, hDeg⟩ :=
    releasedV_bound D R1 (UJ ∘L iota0) H (stepW τ m) Q b qbar (2 ^ m) hQ hw0 hwq hD hJ hRight
      hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ (ε / 3) hδ hδ1 (τ * qbar) (by rw [hTw])
  obtain ⟨_, _, hκc, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ m) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ m) ^ 2 + CayleyTransfer.sigma (stepW τ m) ^ 2 = 1 := by
    linarith
  have hLf : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    have := SharpFilterSchedule.length_ge Q
    linarith
  have hd0 : 0 < fDeg Q τ qbar ε := fDeg_pos Q τ qbar ε hQ
  have hJrel := SmoothingLCU.output_isometry (P := P) (V := HV a m P) (fCoef Q τ qbar ε)
    (fDeg Q τ qbar ε) hd0 (ReuseWeights.concrete_absolute_mass _ _ hLf hd0)
  have hTrel := AmplifiedSmoothing.prepared_isometry (SharpFilterSchedule.length Q)
    (fDepth Q τ qbar ε) hLf hd0 _ _ _ _
    (TimeDependent.step_energy D (UJ ∘L iota0) hJ hD (stepW τ m) hw0 hwq (2 ^ m))
  have hn : ∀ ℓ, 0 < labLen Q τ qbar ε ℓ ∧ labLen Q τ qbar ε ℓ ≤ 2 * fDeg Q τ qbar ε :=
    labLen_spec Q τ qbar ε hQ
  have hN : 2 * fDeg Q τ qbar ε ≤ cap r := by
    have := cap_succ r
    omega
  have hLCUu := LCUT_isUnitary (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit UJ D hUJ
    (fun k _ => hDu k) (2 * fDeg Q τ qbar ε)
  have hT' := isometry_comp (E := P) (F := Reg (Wire a m r K) P) (G := Reg (Wire a m r K) P) _
    (io (a := a) (m := m) (r := r) (K := K) (P := P)) (unitary_adj_comp hLCUu) io_isometry
  have hB := lcu_compressionT (K := K) (m := m) hL (labLen Q τ qbar ε) (2 * fDeg Q τ qbar ε) hn
    hN hr (labWt Q τ qbar ε) (labWt_mass Q τ qbar ε hQ) (CayleyTransfer.c (stepW τ m))
    (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit hκc UJ D hUJc
  rw [netB_slot, blkC_net, netG_slot _ _ _ UJ D hUJc] at hB
  have hB' : (io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L
      (LCUT (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDeg Q τ qbar ε) ∘L io) =
      (SmoothingLCU.output (P := P) (V := HV a m P) (fCoef Q τ qbar ε) (fDeg Q τ qbar ε))† ∘L
        AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) (fDepth Q τ qbar ε)
          (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
          (TimeDependent.exitV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
            (CayleyTransfer.sigma (stepW τ m)) (2 ^ m))
          (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
            (UJ ∘L iota0) (2 ^ m))
          (TimeDependent.privateV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
            (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) (2 ^ m)) := by
    rw [hB]
    change _ = SmoothingLCU.successfulBlock (fCoef Q τ qbar ε) (fDeg Q τ qbar ε) _ _ _ _
    rw [smoothing_block_eq]
    exact reindex_block (fDeg Q τ qbar ε) _ _ (fun n => successfulBlock _ _ _ _ n)
  have hUk : ∀ k, (U k)† ∘L U k = 1 := by
    intro k
    rw [hCay k]
    exact cayley_isometry (H k) (R k) _ (hSelf k) (hRR k)
  have hUiso : (TimeDependent.evolution U (2 ^ m))† ∘L TimeDependent.evolution U (2 ^ m) = 1 :=
    evolution_isometry U hUk (2 ^ m)
  have hAmp := GateBlockTransfer.amplified_error_le (P := P)
    (K := PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := HV a m P) (fDeg Q τ qbar ε)))
    (K' := Reg (Wire a m r K) P)
    (SmoothingLCU.output (P := P) (V := HV a m P) (fCoef Q τ qbar ε) (fDeg Q τ qbar ε))
    (AmplifiedSmoothing.prepared (SharpFilterSchedule.length Q) (fDepth Q τ qbar ε)
      (blkA (CayleyTransfer.c (stepW τ m)) (2 ^ m))
      (TimeDependent.exitV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
        (CayleyTransfer.sigma (stepW τ m)) (2 ^ m))
      (blkC (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
        (UJ ∘L iota0) (2 ^ m))
      (TimeDependent.privateV D (UJ ∘L iota0) (CayleyTransfer.c (stepW τ m))
        (CayleyTransfer.kappa (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) (2 ^ m)))
    (io (a := a) (m := m) (r := r) (K := K) (P := P))
    (LCUT (K := K) (m := m) hL (labLen Q τ qbar ε) (labWt Q τ qbar ε)
        (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) UJ D
        (2 * fDeg Q τ qbar ε) ∘L io)
    hJrel hTrel io_isometry hT' hB' (TimeDependent.evolution U (2 ^ m)) hUiso
  have hAmp2 := hAmp.trans hImpl
  have hCayErr := cayley_evolution_error H R U (stepW τ m) hw0 (by linarith) hSelf hH hRR hCay
    (2 ^ m)
  have hTarget : ‖TimeDependent.evolution U (2 ^ m) - TimeDependent.evolution
      (fun k => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H k)) (2 ^ m)‖ ≤ ε / 3 := by
    refine hCayErr.trans ?_
    exact_mod_cast hcub
  refine ⟨?_, hDeg⟩
  rw [AMPT_io hL _ _ _ _ UJ D _ (unitary_comp_adj hLCUu)]
  calc _ ≤ ‖reflectedAmplification io (LCUT (K := K) (m := m) hL (labLen Q τ qbar ε)
          (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
          UJ D (2 * fDeg Q τ qbar ε) ∘L io) - io ∘L TimeDependent.evolution U (2 ^ m)‖ +
          ‖io ∘L TimeDependent.evolution U (2 ^ m) - io ∘L TimeDependent.evolution
            (fun k => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H k)) (2 ^ m)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * (ε / 3) + ε / 3 := by
        apply add_le_add hAmp2
        rw [← comp_sub]
        calc _ ≤ ‖(io (a := a) (m := m) (r := r) (K := K) (P := P))‖ *
                ‖TimeDependent.evolution U (2 ^ m) - TimeDependent.evolution
                  (fun k => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H k)) (2 ^ m)‖ :=
              opNorm_comp_le _ _
          _ ≤ 1 * (ε / 3) := mul_le_mul io_norm_le hTarget (norm_nonneg _) zero_le_one
          _ = ε / 3 := one_mul _
    _ = ε := by ring

/-! ### The gate-level statement -/

/-- The released gate-level circuit `ampI` with `2^m` time slots; for
`m = simM τ ε` it is the released `simCircuit`. -/
def simCircuitT (a : ℕ) (τ Q qbar ε : ℝ) (m : ℕ) :
    List (Instr (Wire a m (simR Q τ qbar ε) (a + m + 2 * simR Q τ qbar ε))) :=
  ampI (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) (2 * fDeg Q τ qbar ε)

/-- A slot family clamped to the slots `0, …, n - 1`. -/
def clampAt {X : Type*} (n : ℕ) (f : ℕ → X) : ℕ → X := fun k => f (min k (n - 1))

theorem clampAt_of_lt {X : Type*} (n : ℕ) (f : ℕ → X) {k : ℕ} (hk : k < n) :
    clampAt n f k = f k := by
  unfold clampAt
  rw [min_eq_left (by omega)]

theorem min_pred_lt {n : ℕ} (hn : 0 < n) (k : ℕ) : min k (n - 1) < n := by omega

set_option maxRecDepth 8192 in
/-- **Gate-efficient time-dependent simulation, exact gates.**  For the
slot-selected private Cayley operations `D k` with the clock promises of the
released analysis at every slot `k < 2^m` for the Hamiltonians `H k`, the
released circuit with `2^m ≥ steps τ (ε/3)` slots consists of valid
elementary instructions, makes exactly `6d` slot-selected private calls and
`12d` calls of `U_J` or `U_J†`, uses at most `200 (d+1)(a+m+r+1)` elementary
gates on `2a + 3m + 6r + 3` wires, and its full output on clean inputs is
within `ε` of the ordered product `exp (-i w H (2^m - 1)) ⋯ exp (-i w H 0)`,
`w = τ / 2^m`. -/
theorem simulationT (a m : ℕ) (UJ : Vsp a P →L[ℂ] Vsp a P) (D R1 : ℕ → Vsp a P →L[ℂ] Vsp a P)
    (H : ℕ → P →L[ℂ] P) (hUJ : IsUnitary UJ) (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJ ∘L iota0)† ∘L R1 k ∘L (UJ ∘L iota0) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k < 2 ^ m, star (H k) = H k) (hH : ∀ k < 2 ^ m, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJ ∘L iota0)‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1) (hm : TimeSchedule.steps τ (ε / 3) ≤ 2 ^ m) :
    (∀ g ∈ simCircuitT a τ Q qbar ε m, g.Valid Wire.anc) ∧
    nPriv (simCircuitT a τ Q qbar ε m) = 6 * fDeg Q τ qbar ε ∧
    nUJ (simCircuitT a τ Q qbar ε m) = 12 * fDeg Q τ qbar ε ∧
    nGates (simCircuitT a τ Q qbar ε m) ≤
      200 * (fDeg Q τ qbar ε + 1) * (a + m + simR Q τ qbar ε + 1) ∧
    Fintype.card (Wire a m (simR Q τ qbar ε) (a + m + 2 * simR Q τ qbar ε)) =
      2 * a + 3 * m + 6 * simR Q τ qbar ε + 3 ∧
    ‖runT UJ D (simCircuitT a τ Q qbar ε m) ∘L io -
        io ∘L TimeDependent.evolution
          (fun k => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H k)) (2 ^ m)‖ ≤ ε ∧
    (fDeg Q τ qbar ε : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (1 / (ε / 3)))) := by
  obtain ⟨hr1, hr0, hr2⟩ := simR_spec Q τ qbar ε
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hcl := min_pred_lt hpos
  have hw0 : 0 ≤ stepW τ m := div_nonneg hτ (Nat.cast_nonneg _)
  have hwq : stepW τ m ≤ 1 / 4 := (schedule_ge τ (ε / 3) hτ (by positivity) (2 ^ m) hm).2.1
  obtain ⟨_, _, _, hσc, _⟩ := CayleyTransfer.scalar_promises (stepW τ m) hw0 hwq
  have hunit : CayleyTransfer.c (stepW τ m) ^ 2 + CayleyTransfer.sigma (stepW τ m) ^ 2 = 1 := by
    linarith
  have hN : 2 * fDeg Q τ qbar ε ≤ cap (simR Q τ qbar ε) + 1 := by
    have := cap_succ (simR Q τ qbar ε)
    omega
  obtain ⟨hc1, hc2, hc3⟩ := ampI_counts (a := a) (m := m) (K := a + m + 2 * simR Q τ qbar ε)
    (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ m))
    (CayleyTransfer.sigma (stepW τ m)) (2 * fDeg Q τ qbar ε) hN
  have hn : ∀ ℓ, labLen Q τ qbar ε ℓ < 2 ^ simR Q τ qbar ε := by
    intro ℓ
    have := (labLen_spec Q τ qbar ε hQ ℓ).2
    omega
  have hDc : ∀ k, IsUnitary (clampAt (2 ^ m) D k) := fun k => hD _ (hcl k)
  have hagree := ampT_agrees (P := P) (a := a) (m := m) (K := a + m + 2 * simR Q τ qbar ε) UJ
    (clampAt (2 ^ m) D) hUJ (fun k _ => hDc k) (simL Q τ qbar ε) (labLen Q τ qbar ε) (labWt Q τ qbar ε)
    (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m)) hunit
    (2 * fDeg Q τ qbar ε) hn le_rfl
  obtain ⟨herr, hdeg⟩ := ampT_error (K := a + m + 2 * simR Q τ qbar ε) (m := m) UJ
    (clampAt (2 ^ m) D) (clampAt (2 ^ m) R1) (clampAt (2 ^ m) H) hUJ hDc τ Q b qbar ε hτ hQ
    (fun k => hRight _ (hcl k)) (fun k => hLeft _ (hcl k)) (fun k => hR1 _ (hcl k))
    (fun k => hBoundary _ (hcl k)) (fun k => hSelf _ (hcl k)) (fun k => hH _ (hcl k))
    (fun k => hEndpoint _ (hcl k)) hbq hqQ hε hε1 hm hr0 (simL Q τ qbar ε)
  have hgb := gate_bound a m (simR Q τ qbar ε) (fDeg Q τ qbar ε) (2 ^ simR Q τ qbar ε) hr2
  have hrunD : runT UJ D (simCircuitT a τ Q qbar ε m) =
      runT UJ (clampAt (2 ^ m) D) (simCircuitT a τ Q qbar ε m) :=
    runT_congr UJ D _ (fun k hk => (clampAt_of_lt (2 ^ m) D hk).symm) _
  have hevol : TimeDependent.evolution
      (fun k => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • H k)) (2 ^ m) =
      TimeDependent.evolution
      (fun k => NormedSpace.exp ((-Complex.I * (stepW τ m : ℂ)) • clampAt (2 ^ m) H k)) (2 ^ m) :=
    evolution_eq_of_lt _ _ (2 ^ m) (fun k hk => by rw [clampAt_of_lt (2 ^ m) H hk])
  refine ⟨ampI_valid _ _ _ _ _ hunit _, ?_, ?_, ?_, ?_, ?_, hdeg⟩
  · unfold simCircuitT; rw [hc1]; ring
  · unfold simCircuitT; rw [hc2]; ring
  · unfold simCircuitT
    refine hc3.trans (le_of_eq_of_le ?_ hgb)
    ring
  · rw [card_wire]; ring
  · have hio : runT UJ (clampAt (2 ^ m) D) (simCircuitT a τ Q qbar ε m) ∘L io =
        AMPT (K := a + m + 2 * simR Q τ qbar ε) (m := m) (simL Q τ qbar ε) (labLen Q τ qbar ε)
          (labWt Q τ qbar ε) (CayleyTransfer.c (stepW τ m)) (CayleyTransfer.sigma (stepW τ m))
          UJ (clampAt (2 ^ m) D) (2 * fDeg Q τ qbar ε) ∘L io := by
      unfold simCircuitT
      refine ContinuousLinearMap.ext (fun ψ => ?_)
      rw [comp_apply, comp_apply, io_apply]
      exact hagree _ (supp_bas _ (fun w _ => rfl) ψ)
    rw [hrunD, hio, hevol]
    exact herr

end

end SparseHamiltonian.GateCircuit.SlotSim
