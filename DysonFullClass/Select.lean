import ODELowerBoundExtensions.Dyson.Compile

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The Dyson SELECT on an arbitrary branch register

Manuscript, proof of Lemma `odel:lem:dyson`: "Prepare `k` independent labels [...], sort a
working copy reversibly while retaining the original labels, and select the matrix factors in
chronological order. [...] One degree-`k` selection uses `O(k)` matrix queries, regardless of the
number of possible cell labels." "For ordered labels `j_1 ≤ ⋯ ≤ j_k`, apply each `U_{j_l}` with a
fresh zero work register `a_l`. [...] Distinct work registers prevent a failed earlier factor from
returning to the selected block through a later factor."

The released SELECT (`ODELowerBoundExtensions.Dyson.select`) runs on the branch labels
`Lab K M = Option (Fin M) × LabelI K M`, whose source part is tied to the mesh cells. Here the
same circuit runs on an arbitrary finite branch register `Λ` with a public map
`κ : Λ → LabelI K M` to the Dyson LCU labels (a configuration `c : Cfg K M` or one of the two
padding branches): slot `j` is active on a branch `l` iff `κ l` is a configuration using slot `j`,
and then reads the sample `σ (cell (κ l) j)`. The general-source solver uses
`Λ = Option (Fin m) × (LabelI K M × Bool)` (source label, LCU label, attenuation flag), so source
labels and their number are independent of the mesh. All gates other than the oracle calls are
known; every slot is the six-query block encoding of `NativeSparseBlockEncoding.program`, masked by
the branch, and the fresh flag split of `Flagged.lean`.

* `gSelect`: the physical program, `18 K` native calls for every `Λ`, mesh and cell count
  (`gSelect_count`, `gSelect_cost`);
* `gSelect_compression`: `gEncoding† (gSelect) gEncoding = diag_l gBranchOperator l`, the
  time-ordered product `cfgProduct` of the samples `G̃_{σ r}/(s Λ)` on configuration branches, the
  identity on padding branches (exact, no error, for arbitrary non-commuting samples);
* `gBranchOperator_norm_le`: every selected operator is a contraction.
-/

namespace DysonFullClass

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open SparseHamiltonian.TimeDependent (evolution)
open ODELowerBoundExtensions.Dyson
open scoped InnerProduct BigOperators

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {K M : ℕ}

/-- The branch register: branch label and slot flags. -/
abbrev OmegaG (Λ : Type*) (K : ℕ) : Type _ := Λ × Flags K

/-- Slot `j` is used by branch `l`. -/
def gActive (κ : Λ → LabelI K M) (j : ℕ) (l : Λ) : Bool :=
  match κ l with
  | .inl c => c.active j
  | .inr _ => false

/-- The sample read by slot `j` on branch `l` (public; arbitrary on idle slots). -/
def gTime {Ks : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks) (κ : Λ → LabelI K M) (j : ℕ) (l : Λ) :
    Fin Ks :=
  match κ l with
  | .inl c => σ (c.cell hM j)
  | .inr _ => σ ⟨0, hM⟩

/-- The branch mask of a letter. -/
def gLetterActive (κ : Λ → LabelI K M) : Letter K → OmegaG Λ K → Bool :=
  fun m ω => gActive κ (m.2 : ℕ) ω.1

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- The logical masked letters on the branch register `Λ`. -/
abbrev gLogicalOracle (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) :
    Letter K → X → NativeMaskedOracle.Logical (OmegaG Λ K) (PBasis Ks n Z) →L[ℂ]
      NativeMaskedOracle.Logical (OmegaG Λ K) (PBasis Ks n Z) :=
  NativeMaskedProgram.logicalOracle (timeOracle D) letterLabel (gLetterActive κ)

/-- Masked, time-coherent copy of a native program in slot `j`. -/
def gLiftSlot (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (j : Fin K) :
    MultiOracleCircuit.Program (oracles D) → MultiOracleCircuit.Program (gLogicalOracle D κ)
  | .fixed U hU => .fixed
      (MaskedProgram.masked (fun ω : OmegaG Λ K => gActive κ (j : ℕ) ω.1)
        (TimeDependent.timeIndexed (fun _ : Fin Ks => flatGate U)))
      (MaskedProgram.masked_unitary _ _
        (TimeDependent.timeIndexed_unitary _ (fun _ => IsUnitary.transport hU _)))
  | .query l => .query (l, j)
  | .queryAdjoint l => .queryAdjoint (l, j)
  | .seq p q => .seq (gLiftSlot D κ j p) (gLiftSlot D κ j q)

omit [DecidableEq Λ] [DecidableEq Z] in
theorem gLiftSlot_eval (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (j : Fin K)
    (p : MultiOracleCircuit.Program (oracles D)) (x : X) :
    (gLiftSlot D κ j p).eval x =
      MaskedProgram.masked (fun ω : OmegaG Λ K => gActive κ (j : ℕ) ω.1)
        (TimeDependent.timeIndexed (fun r => flatGate (p.eval (x, r)))) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l =>
      change star (MaskedProgram.masked (fun ω : OmegaG Λ K => gActive κ (j : ℕ) ω.1)
        (TimeDependent.timeIndexed (fun r => flatGate (oracles D l (x, r))))) = _
      rw [star_eq_adjoint, MaskedProgram.masked_adjoint, ← star_eq_adjoint,
        TimeDependent.timeIndexed_star]
      simp only [flatGate, map_star, MultiOracleCircuit.Program.eval_queryAdjoint]
  | seq p q hp hq =>
      change (gLiftSlot D κ j p).eval x * (gLiftSlot D κ j q).eval x = _
      rw [hp, hq, ← MaskedProgram.masked_mul, TimeDependent.timeIndexed_mul]
      simp only [MultiOracleCircuit.Program.eval_seq, flatGate_mul]

omit [DecidableEq Λ] [DecidableEq Z] in
theorem gLiftSlot_cost (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (j : Fin K)
    (p : MultiOracleCircuit.Program (oracles D)) (w : Query → ℕ) :
    (gLiftSlot D κ j p).cost (fun m => w (letterLabel m)) = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (gLiftSlot D κ j p).cost _ + (gLiftSlot D κ j q).cost _ = _
      rw [hp, hq]
      rfl

omit [DecidableEq Λ] [DecidableEq Z] in
theorem gLiftSlot_count (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (j : Fin K)
    (p : MultiOracleCircuit.Program (oracles D)) :
    (gLiftSlot D κ j p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (gLiftSlot D κ j p).count + (gLiftSlot D κ j q).count = _
      rw [hp, hq]
      rfl

/-- The known time gate of slot `j`. -/
def gTimeGate (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (κ : Λ → LabelI K M) (j : ℕ) :
    NativeMaskedOracle.Logical (OmegaG Λ K) (PBasis Ks n Z) →L[ℂ]
      NativeMaskedOracle.Logical (OmegaG Λ K) (PBasis Ks n Z) :=
  WeightedClock.diagonal (fun ω : OmegaG Λ K => timeSwap (n := n) (Z := Z) hK (gTime hM σ κ j ω.1))

omit [DecidableEq Λ] [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem gTimeGate_unitary (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (κ : Λ → LabelI K M)
    (j : ℕ) : IsUnitary (gTimeGate (n := n) (Z := Z) hM hK σ κ j) :=
  CoherentQuerySchedule.diagonal_unitary _ (fun _ => timeSwap_unitary hK _)

/-- **Slot `j`**: time gate, masked six-query block encoding, time gate, flag split. -/
def gSlotProgram (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (κ : Λ → LabelI K M) (j : Fin K) : MultiOracleCircuit.Program (gLogicalOracle D κ) :=
  .seq (.fixed (flagSplit (Λ := Λ) (payloadEncoding hK D) j)
      (flagSplit_unitary _ (payloadEncoding_isometry hK D) j))
    (.seq (.fixed (gTimeGate hM hK σ κ j) (gTimeGate_unitary hM hK σ κ j))
      (.seq (gLiftSlot D κ j (NativeSparseBlockEncoding.program D))
        (.fixed (gTimeGate hM hK σ κ j) (gTimeGate_unitary hM hK σ κ j))))

/-- The first `m` slots (slot `0` executed first). -/
def gSelectUpTo (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (κ : Λ → LabelI K M) : ℕ → MultiOracleCircuit.Program (gLogicalOracle D κ)
  | 0 => MultiOracleCircuit.Program.identity
  | m + 1 =>
      if h : m < K then .seq (gSlotProgram hM hK σ D κ ⟨m, h⟩) (gSelectUpTo hM hK σ D κ m)
      else gSelectUpTo hM hK σ D κ m

/-- The payload operator of slot `j` on branch `l`. -/
def gSlotOperator (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (κ : Λ → LabelI K M) (x : X) (j : ℕ) (l : Λ) :
    EuclideanSpace ℂ (PBasis Ks n Z) →L[ℂ] EuclideanSpace ℂ (PBasis Ks n Z) :=
  timeSwap hK (gTime hM σ κ j l) ∘L
    (if gActive κ j l then
      TimeDependent.timeIndexed
        (fun r => flatGate ((NativeSparseBlockEncoding.program D).eval (x, r)))
    else 1) ∘L timeSwap hK (gTime hM σ κ j l)

omit [DecidableEq Λ] in
theorem gSlotProgram_eval (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (x : X) (j : Fin K) :
    (gSlotProgram hM hK σ D κ j).eval x =
      layer (Λ := Λ) (K := K) (payloadEncoding hK D) (gSlotOperator hM hK σ D κ x j) j := by
  rw [layer, dif_pos j.isLt]
  simp only [gSlotProgram, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_fixed, gLiftSlot_eval, mul_def, Fin.eta]
  congr 1

omit [DecidableEq Λ] in
theorem gSelectUpTo_eval (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (x : X) (m : ℕ) :
    (gSelectUpTo hM hK σ D κ m).eval x =
      evolution (fun j => layer (Λ := Λ) (K := K) (payloadEncoding hK D)
        (gSlotOperator hM hK σ D κ x j) j) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [TimeDependent.evolution_succ, ← ih]
      by_cases h : m < K
      · simp only [gSelectUpTo, dif_pos h, MultiOracleCircuit.Program.eval_seq]
        rw [gSlotProgram_eval]
      · simp only [gSelectUpTo, dif_neg h, layer, one_mul]

omit [Fintype Λ] [DecidableEq Λ] in
/-- One slot compresses to the selected sample when active and to the identity otherwise. -/
theorem gSlotOperator_compression (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (x : X) (j : ℕ) (l : Λ) :
    (payloadEncoding hK D)† ∘L gSlotOperator hM hK σ D κ x j l ∘L payloadEncoding hK D =
      if gActive κ j l then sampleOperator D x (gTime hM σ κ j l) else 1 := by
  cases hl : gActive κ j l
  · simp only [gSlotOperator, hl, Bool.false_eq_true, if_false]
    rw [one_def, id_comp, timeSwap_comp_self]
    simpa only [one_def, id_comp] using payloadEncoding_isometry hK D
  · simp only [gSlotOperator, hl, if_true, comp_assoc]
    exact slot_compression hK D x _

/-- **The selected operator of a branch**: the time-ordered product of the configuration's
samples `G̃_{σ r}/(s Λ)`; the identity on the padding branches. -/
def gBranchOperator (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X)
    (κ : Λ → LabelI K M) (l : Λ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  match κ l with
  | .inl c => cfgProduct (sampleSeq σ D x) c
  | .inr _ => 1

omit [DecidableEq Λ] [Fintype Λ] in
theorem gBranchOperator_norm_le (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X)
    (κ : Λ → LabelI K M) (l : Λ) : ‖gBranchOperator σ D x κ l‖ ≤ 1 := by
  unfold gBranchOperator
  rcases κ l with c | b
  · exact branchOperator_norm_le σ D x ((none, .inl c) : Lab K M)
  · exact ContinuousLinearMap.norm_id_le

omit [DecidableEq Λ] in
/-- **Compression of the logical SELECT**: at all flags zero, the circuit is the branch-diagonal
operator of the selected time-ordered products. -/
theorem gLogicalSelect_compression (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (x : X) :
    (zeroFlags (Λ := Λ) (K := K) (payloadEncoding hK D))† ∘L
        (gSelectUpTo hM hK σ D κ K).eval x ∘L zeroFlags (payloadEncoding hK D) =
      WeightedClock.diagonal (gBranchOperator σ D x κ) := by
  rw [gSelectUpTo_eval]
  refine (flagged_compression _ (payloadEncoding_isometry hK D)
    (fun j => gSlotOperator hM hK σ D κ x j)).trans ?_
  congr 1
  funext l
  refine (TimeDependentExtensions.evolution_congr' _ _ K
    (fun k _ => gSlotOperator_compression hM hK σ D κ x k l)).trans ?_
  unfold gBranchOperator
  cases hκ : κ l with
  | inl c =>
      simp only
      rw [← slot_product hM (sampleSeq σ D x) c]
      congr 1
      funext j
      simp only [gActive, gTime, hκ, sampleSeq, dif_pos (c.cell hM j).isLt, Fin.eta]
  | inr b =>
      simp only [gActive, hκ, Bool.false_eq_true, if_false]
      exact evolution_one K

omit [DecidableEq Λ] in
theorem gSelectUpTo_count (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (m : ℕ) (hm : m ≤ K) :
    (gSelectUpTo hM hK σ D κ m).count = 6 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have h : m < K := hm
      simp only [gSelectUpTo, dif_pos h, MultiOracleCircuit.Program.count_seq, gSlotProgram,
        MultiOracleCircuit.Program.count_fixed, gLiftSlot_count, program_count, ih h.le]
      ring

omit [DecidableEq Λ] in
theorem gSelectUpTo_cost (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (κ : Λ → LabelI K M) (w : Query → ℕ) (m : ℕ) (hm : m ≤ K) :
    (gSelectUpTo hM hK σ D κ m).cost (fun l => w (letterLabel l)) =
      m * (w .rowLocation + w .columnLocation + 4 * w .value) := by
  induction m with
  | zero => simp [gSelectUpTo]
  | succ m ih =>
      have h : m < K := hm
      simp only [gSelectUpTo, dif_pos h, MultiOracleCircuit.Program.cost_seq, gSlotProgram,
        MultiOracleCircuit.Program.cost_fixed, gLiftSlot_cost, program_cost, ih h.le]
      ring

/-! ### The physical SELECT -/

/-- **The physical SELECT on the branch register `Λ`**: the logical SELECT compiled to masked
native calls (`NativeMaskedProgram.compile`, three native calls per letter). -/
def gSelect (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (K : ℕ) (κ : Λ → LabelI K M) : MultiOracleCircuit.Program (matrixOracle (OmegaG Λ K) D) :=
  NativeMaskedProgram.compile (timeOracle D) (cleanTime hK D) letterLabel (gLetterActive κ)
    (gSelectUpTo hM hK σ D κ K)

/-- **The SELECT encoding**: branch `l` at all flags zero, payload encoded by `payloadEncoding`,
then the clean masked-access encoding. -/
def gEncoding (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (K : ℕ) (Λ : Type*) [Fintype Λ]
    [DecidableEq Λ] :
    PiLp 2 (fun _ : Λ => EuclideanSpace ℂ n) →L[ℂ]
      NativeMaskedOracle.Physical (OmegaG Λ K) (PBasis Ks n Z) :=
  (NativeMaskedOracle.input (ι := OmegaG Λ K) (cleanTime hK D)).toContinuousLinearMap ∘L
    zeroFlags (Λ := Λ) (K := K) (payloadEncoding hK D)

theorem gEncoding_isometry (hK : 0 < Ks) (D : Data (X × Fin Ks) n Z s) (K : ℕ) :
    (gEncoding hK D K Λ)† ∘L gEncoding hK D K Λ = 1 :=
  NativeSparseAttenuation.isometry_comp _ _
    (zeroFlags_isometry _ (payloadEncoding_isometry hK D))
    (NativeMaskedOracle.input (ι := OmegaG Λ K) (cleanTime hK D)).adjoint_comp_self

omit [DecidableEq Λ] in
theorem gSelect_unitary (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (κ : Λ → LabelI K M) (x : X) :
    IsUnitary ((gSelect hM hK σ D K κ).eval x) :=
  NativeMaskedProgram.compile_unitary _ (timeOracle_unitary D) _ _ _ _ x

/-- **Exact compression of the physical SELECT** on the branch register `Λ`. -/
theorem gSelect_compression (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (κ : Λ → LabelI K M) (x : X) :
    (gEncoding hK D K Λ)† ∘L (gSelect hM hK σ D K κ).eval x ∘L gEncoding hK D K Λ =
      WeightedClock.diagonal (gBranchOperator σ D x κ) := by
  have hc := NativeMaskedProgram.compile_eval (timeOracle D) (timeOracle_unitary D)
    (cleanTime hK D) (imageTime hK D) (timeOracle_valid hK D) letterLabel
    (gLetterActive (Λ := Λ) (K := K) (M := M) κ) (gSelectUpTo hM hK σ D κ K) x
  have hi := (NativeMaskedOracle.input (ι := OmegaG Λ K) (cleanTime hK D)).adjoint_comp_self
  rw [← gLogicalSelect_compression hM hK σ D κ x]
  refine ContinuousLinearMap.ext fun v => ?_
  have h1 := congrArg (fun f => f (zeroFlags (Λ := Λ) (K := K) (payloadEncoding hK D) v)) hc
  have h2 := congrArg (fun f => f ((gSelectUpTo hM hK σ D κ K).eval x
    (zeroFlags (Λ := Λ) (K := K) (payloadEncoding hK D) v))) hi
  simp only [comp_apply] at h1 h2
  simp only [gEncoding, gSelect, adjoint_comp, comp_apply, h1, h2]
  rfl

omit [DecidableEq Λ] in
/-- `18 K` native matrix calls, for every branch register, mesh and cell count. -/
theorem gSelect_count (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (κ : Λ → LabelI K M) :
    (gSelect hM hK σ D K κ).count = 18 * K := by
  rw [gSelect, NativeMaskedProgram.compile_count, gSelectUpTo_count hM hK σ D κ K le_rfl]
  ring

omit [DecidableEq Λ] in
/-- Per native label: `3 K` row, `3 K` column and `12 K` value calls. -/
theorem gSelect_cost (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (κ : Λ → LabelI K M) (w : Query → ℕ) :
    (gSelect hM hK σ D K κ).cost w =
      3 * K * (w .rowLocation + w .columnLocation + 4 * w .value) := by
  rw [gSelect, NativeMaskedProgram.compile_cost]
  refine (gSelectUpTo_cost hM hK σ D κ (fun l => 3 * w l) K le_rfl).trans ?_
  ring

end

end DysonFullClass
