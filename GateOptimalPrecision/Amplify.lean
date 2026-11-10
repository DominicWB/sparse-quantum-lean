import GateEfficientHamiltonian.Circuit.Theorem
import GateEfficientNative.Hamiltonian.Macro
import SignedFactorSimulation.Amplify

/-!
# Iterated oblivious amplification on the gate register

The signed-factor construction (Section `gate:sec:signed`) prepares a block `s₀ Q̂` with
`s₀ ≤ 1/Ā` for an absolute constant `Ā`, and amplifies it with a fixed number of rounds of
oblivious amplitude amplification. As in the query proof (`SignedFactorSimulation.Amplify`),
`k_o = 3^R`: `R` repetitions of the released single round `L ↦ -(L Z L† Z L)` with the clean
reflection `Z` of the released gate register.

* `ampIt l k`: the instruction list of `k` rounds over a base circuit `l` (each round is the
  previous circuit, the clean reflection, its literal inverse, the clean reflection, the previous
  circuit and the global phase `-1`, exactly as the released single round `Sim.ampI`);
* `ampOp X k`: the ideal operator; `ampIt_agrees`: the circuit agrees with it on clean
  configurations when the base circuit does; `ampOp_isUnitary`, `pres2_ampOp`;
* `ampOp_io`: on clean inputs `ampOp X k` is the iterated released amplification
  `SignedFactorSimulation.ampIter io (X ∘ io) k`;
* `ampOp_error`: if the initial block `io† X io` is within `e₀` of `sin(π/(2·3^R)) W` for a
  unitary `W`, the full output after `R` rounds is within `√(2·7^R e₀)` of `io W`;
* counts: `nPriv (ampIt l k) = 3^k nPriv l`, `nUJ (ampIt l k) = 3^k nUJ l` and
  `2 nGates (ampIt l k) + c = 3^k (2 nGates l + c)` with `c = 2 |zrG| + 1` (`ampIt_counts`);
  validity and sector controls are preserved (`ampIt_valid`, `secOK_ampIt`).
-/

set_option autoImplicit false

namespace GateOptimalPrecision

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
open scoped InnerProduct

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-! ### The circuits and the ideal operators -/

/-- `k` rounds of oblivious amplification of the circuit `l`. -/
def ampIt (l : List (Instr (Wire a m r K))) : ℕ → List (Instr (Wire a m r K))
  | 0 => l
  | k + 1 => ampIt l k ++ ofGates zrG ++ invList (ampIt l k) ++ ofGates zrG ++ ampIt l k ++
      ofGates [phaseG]

/-- The ideal operator of `k` rounds of amplification of `X`. -/
def ampOp (X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) :
    ℕ → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P
  | 0 => X
  | k + 1 => -(ampOp X k ∘L ZR ∘L (ampOp X k)† ∘L ZR ∘L ampOp X k)

theorem ampOp_zero (X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) : ampOp X 0 = X := rfl

theorem ampOp_succ (X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) (k : ℕ) :
    ampOp X (k + 1) = -(ampOp X k ∘L ZR ∘L (ampOp X k)† ∘L ZR ∘L ampOp X k) := rfl

theorem ampOp_isUnitary {X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P}
    (hX : IsUnitary X) (k : ℕ) : IsUnitary (ampOp X k) := by
  induction k with
  | zero => exact hX
  | succ k ih =>
      exact isUnitary_neg (isUnitary_comp ih (isUnitary_comp ZR_isUnitary
        (isUnitary_comp (isUnitary_adj ih) (isUnitary_comp ZR_isUnitary ih))))

theorem pres2_ampOp {X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P}
    (hX : Pres2 Clean X) (k : ℕ) : Pres2 Clean (ampOp X k) := by
  induction k with
  | zero => exact hX
  | succ k ih => exact (ih.comp (pres2_ZR.comp (ih.adj.comp (pres2_ZR.comp ih)))).neg

/-! ### Validity and sector controls -/

theorem phaseG_valid :
    (Instr.gate (phaseG (a := a) (m := m) (r := r) (K := K))).Valid Wire.anc :=
  ⟨by simp [phaseG], by simp [phaseG], negOne_unitary⟩

theorem ampIt_valid (l : List (Instr (Wire a m r K))) (hl : ∀ i ∈ l, i.Valid Wire.anc) (k : ℕ) :
    ∀ i ∈ ampIt l k, i.Valid Wire.anc := by
  induction k with
  | zero => exact hl
  | succ k ih =>
      intro i hi
      simp only [ampIt, List.mem_append] at hi
      rcases hi with ((((hi | hi) | hi) | hi) | hi) | hi
      · exact ih i hi
      · exact ofGates_valid _ zrG_ok (by norm_num) i hi
      · exact invList_valid _ ih i hi
      · exact ofGates_valid _ zrG_ok (by norm_num) i hi
      · exact ih i hi
      · simp only [ofGates, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hi
        subst hi
        exact phaseG_valid

theorem secOK_ampIt (l : List (Instr (Wire a m r K)))
    (hl : ∀ i ∈ l, GateNative.SecOK (GateNative.wireRel a m r K) i) (k : ℕ) :
    ∀ i ∈ ampIt l k, GateNative.SecOK (GateNative.wireRel a m r K) i := by
  induction k with
  | zero => exact hl
  | succ k ih =>
      intro i hi
      simp only [ampIt, List.mem_append] at hi
      rcases hi with ((((hi | hi) | hi) | hi) | hi) | hi
      · exact ih i hi
      · exact GateNative.secOK_ofGates _ i hi
      · exact GateNative.secOK_invList _ _ ih i hi
      · exact GateNative.secOK_ofGates _ i hi
      · exact ih i hi
      · exact GateNative.secOK_ofGates _ i hi

/-! ### Agreement on clean configurations -/

theorem phaseG_agrees :
    Agrees Clean (gRun (Q := P) [phaseG (a := a) (m := m) (r := r) (K := K)])
      (-1 : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) := by
  rw [gRun_singleton, phaseG_op]
  exact Agrees.refl _ _

/-- **The amplified circuit agrees with the ideal operator** on clean configurations. -/
theorem ampIt_agrees (UJ D : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ) (hD : IsUnitary D)
    (l : List (Instr (Wire a m r K))) (hl : ∀ i ∈ l, i.Valid Wire.anc)
    {X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P} (hX : IsUnitary X)
    (hXp : Pres2 Clean X) (hag : Agrees Clean (run (simSem UJ D) l) X)
    (hK : a + m + 2 * r ≤ K) (k : ℕ) :
    Agrees Clean (run (simSem UJ D) (ampIt l k)) (ampOp X k) := by
  induction k with
  | zero => exact hag
  | succ k ih =>
      have hrunU : IsUnitary (run (simSem (m := m) (r := r) (K := K) UJ D) (ampIt l k)) :=
        run_isUnitary (simSem UJ D) hUJ hD _ (ampIt_valid l hl k)
      have hAu := ampOp_isUnitary hX k
      have hAp := pres2_ampOp hXp k
      have hinv : Agrees Clean (run (simSem UJ D) (invList (ampIt l k))) ((ampOp X k)†) := by
        rw [run_invList]
        exact ih.adjoint hrunU hAu hAp.2
      have hz : Agrees Clean (run (simSem UJ D) (ofGates (zrG (a := a) (m := m) (r := r) (K := K))))
          ZR := by
        rw [run_ofGates]
        exact zr_agrees (by omega)
      have hp : Agrees Clean (run (simSem UJ D)
          (ofGates [phaseG (a := a) (m := m) (r := r) (K := K)]))
          (-1 : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) := by
        rw [run_ofGates]
        exact phaseG_agrees
      rw [ampIt, run_append, run_append, run_append, run_append, run_append]
      have e1 := ih.comp hAp.1 hz
      have e2 := e1.comp (pres2_ZR.comp hAp).1 hinv
      have e3 := e2.comp (hAp.adj.comp (pres2_ZR.comp hAp)).1 hz
      have e4 := e3.comp (pres2_ZR.comp (hAp.adj.comp (pres2_ZR.comp hAp))).1 ih
      have e5 := e4.comp (hAp.comp (pres2_ZR.comp (hAp.adj.comp (pres2_ZR.comp hAp)))).1 hp
      convert e5 using 1
      ext v
      simp [ampOp]

/-! ### Clean inputs: the released amplification -/

/-- On clean inputs, `k` rounds are the iterated released amplification. -/
theorem ampOp_io {X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P} (hX : IsUnitary X)
    (k : ℕ) :
    ampOp X k ∘L io = SignedFactorSimulation.ampIter io (X ∘L io) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change ampOp X (k + 1) ∘L io = reflectedAmplification io
        (SignedFactorSimulation.ampIter io (X ∘L io) k)
      rw [← ih]
      set A := ampOp X k with hA
      have hAA : A ∘L A† = 1 := unitary_comp_adj (ampOp_isUnitary hX k)
      have e : A ∘L ((1 : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P) ∘L A†) = A ∘L A† := by
        ext v; rfl
      have h1 : rangeReflection (A ∘L io) = A ∘L ZR ∘L A† := by
        simp only [rangeReflection, ZR, adjoint_comp, comp_sub, sub_comp, comp_smul, smul_comp,
          comp_assoc]
        rw [e, hAA]
      rw [reflectedAmplification, h1, ampOp_succ]
      simp only [neg_comp, comp_assoc]
      rfl

theorem norm_le_one_of_adjoint_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {V : E →L[ℂ] E} (hV : V† ∘L V = 1) : ‖V‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun x => ?_
  rw [V.norm_map_iff_adjoint_comp_self.mpr hV x, one_mul]

/-- **The full-output error of `R` rounds.** If the initial block `io† X io` is within `e₀` of
`sin(π/(2·3^R)) W` for a unitary `W` and `7^R e₀ ≤ 7/16`, the amplified circuit has full-output
error at most `√(2·7^R e₀)` against `W`. -/
theorem ampOp_error {X : Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P} (hX : IsUnitary X)
    {W : P →L[ℂ] P} (hW : IsUnitary W) (R : ℕ) {e₀ : ℝ}
    (hblock : ‖(io (a := a) (m := m) (r := r) (K := K) (P := P))† ∘L (X ∘L io) -
      (SignedFactorSimulation.ampS R 0 : ℂ) • W‖ ≤ e₀)
    (he : 7 ^ R * e₀ ≤ 7 / 16) :
    ‖ampOp X R ∘L io - io ∘L W‖ ≤ Real.sqrt (2 * (7 ^ R * e₀)) := by
  set J : P →L[ℂ] Reg (Wire a m r K) P := io (a := a) (m := m) (r := r) (K := K) (P := P)
    with hJdef
  have hJ : J† ∘L J = 1 := io_isometry
  have hT : (X ∘L J)† ∘L (X ∘L J) = 1 := isometry_comp X J (unitary_adj_comp hX) hJ
  have hWr : W ∘L W† = 1 := hW.2
  have hWl : W† ∘L W = 1 := hW.1
  have hWn : ‖W‖ ≤ 1 := norm_le_one_of_adjoint_comp hWl
  have h8 := SignedFactorSimulation.ampIter_block_error J (X ∘L J) hJ hT hWr hWn R
    hblock he R le_rfl
  rw [SignedFactorSimulation.ampS_top, Complex.ofReal_one, one_smul] at h8
  have hfull := SignedFactorSimulation.full_output_error J
    (SignedFactorSimulation.ampIter J (X ∘L J) R) hJ
    (SignedFactorSimulation.ampIter_isometry J (X ∘L J) hJ hT R) hWl h8
  have hio : ampOp X R ∘L J = SignedFactorSimulation.ampIter J (X ∘L J) R := ampOp_io hX R
  rw [hio]
  exact hfull

/-! ### Counts -/

theorem ampIt_counts (l : List (Instr (Wire a m r K))) (k : ℕ) :
    nPriv (ampIt l k) = 3 ^ k * nPriv l ∧ nUJ (ampIt l k) = 3 ^ k * nUJ l ∧
      2 * nGates (ampIt l k) + (2 * (zrG (a := a) (m := m) (r := r) (K := K)).length + 1) =
        3 ^ k * (2 * nGates l + (2 * (zrG (a := a) (m := m) (r := r) (K := K)).length + 1)) := by
  induction k with
  | zero => simp [ampIt]
  | succ k ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      simp only [ampIt, nPriv_append, nUJ_append, nGates_append, nPriv_ofGates, nUJ_ofGates,
        nGates_ofGates, nPriv_invList, nUJ_invList, nGates_invList, List.length_cons,
        List.length_nil, h1, h2]
      refine ⟨by ring, by ring, ?_⟩
      rw [pow_succ]
      nlinarith [h3]

/-- The elementary-gate count of `k` rounds. -/
theorem ampIt_nGates_le (l : List (Instr (Wire a m r K))) (k : ℕ) :
    nGates (ampIt l k) ≤ 3 ^ k * (nGates l + 2 * (a + m + 2 * r) + 3) := by
  obtain ⟨-, -, h⟩ := ampIt_counts l k
  have hz := zrG_length (a := a) (m := m) (r := r) (K := K)
  have h3 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have key : 2 * nGates (ampIt l k) ≤ 3 ^ k * (2 * (nGates l + 2 * (a + m + 2 * r) + 3)) := by
    have : 3 ^ k * (2 * nGates l + (2 * (zrG (a := a) (m := m) (r := r) (K := K)).length + 1)) ≤
        3 ^ k * (2 * (nGates l + 2 * (a + m + 2 * r) + 3)) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have : 3 ^ k * (2 * (nGates l + 2 * (a + m + 2 * r) + 3)) =
      2 * (3 ^ k * (nGates l + 2 * (a + m + 2 * r) + 3)) := by ring
  omega

end

end GateOptimalPrecision
