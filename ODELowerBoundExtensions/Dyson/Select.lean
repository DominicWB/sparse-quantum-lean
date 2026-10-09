import ODELowerBoundExtensions.Dyson.Access
import ODELowerBoundExtensions.Dyson.Flagged
import ODELowerBoundExtensions.Dyson.Slots

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The Dyson SELECT circuit (`odel:lem:dyson`, lines 4198-4214)

"Prepare `k` independent cell labels …, sort a working copy reversibly …, and apply the selected
matrices in chronological order. This uses `O(k)` matrix queries. Fresh encoding ancillas make
the compressed product equal to the product of the compressed matrices" (lines 4204-4206).

The logical circuit acts on the branch register `Omega K M = Lab K M × Flags K`, where an LCU
label `(q, ℓ) : Lab K M` carries a source label `q : Option (Fin M)` (initial state or forcing
cell) and either a configuration `c : Cfg K M` or one of the two cancelling padding branches,
and on the payload `ℂ^{PBasis}` (time address and native register). Slot `j < K`:

1. the known time gate writes the cell `σ (cell c j)` of the slot into the time address
   (`timeGate`, a branch-diagonal swap);
2. the six-query block encoding `NativeSparseBlockEncoding.program D` runs **masked** on the
   branches whose configuration uses slot `j` (`liftSlot`: each native call becomes a logical
   masked letter `(l, j)` of `NativeMaskedProgram.logicalOracle`, each fixed gate its masked
   copy);
3. the time gate is undone and the flag split of slot `j` is applied (`Flagged.lean`).

* `logicalSelect_eval`: the circuit is the product of the flagged layers;
* `logicalSelect_compression`: its all-zero-flag compression is the branch-diagonal operator
  `branchOperator`, the time-ordered product `cfgProduct` of the samples `A_{σ r}/(s Λ)` of the
  configuration (padding branches: identity);
* `logicalSelect_count`: `6 K` logical letters (one row, one column, four value calls per slot).
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open SparseHamiltonian.TimeDependent (evolution)
open scoped InnerProduct BigOperators

/-- The non-source part of an LCU label: a configuration, or one of the two cancelling padding
branches (`inr b`) that double the coefficient mass without changing the selected sum. -/
abbrev LabelI (K M : ℕ) : Type := Cfg K M ⊕ Bool

/-- An LCU label: source label (`none`: initial state; `some q`: forcing of cell `q`) and
configuration or padding. This is the index type of `ODECompiledSource.Branch (LabelI K M) P M`. -/
abbrev Lab (K M : ℕ) : Type := Option (Fin M) × LabelI K M

/-- The logical branch register: LCU label and slot flags. -/
abbrev Omega (K M : ℕ) : Type := Lab K M × Flags K

/-- Slot `j` is used by the label. -/
def labActive {K M : ℕ} (j : ℕ) : Lab K M → Bool
  | (_, .inl c) => c.active j
  | (_, .inr _) => false

/-- The sample read by slot `j` (public; arbitrary on idle slots). -/
def labTime {K M Ks : ℕ} (hM : 0 < M) (σ : Fin M → Fin Ks) (j : ℕ) : Lab K M → Fin Ks
  | (_, .inl c) => σ (c.cell hM j)
  | (_, .inr _) => σ ⟨0, hM⟩

/-- A logical letter: one native label in one slot. -/
abbrev Letter (K : ℕ) : Type := Query × Fin K

/-- The native label of a letter. -/
def letterLabel {K : ℕ} : Letter K → Query := Prod.fst

/-- The branch mask of a letter: the branches whose configuration uses its slot. -/
def letterActive {K M : ℕ} : Letter K → Omega K M → Bool :=
  fun m ω => labActive (m.2 : ℕ) ω.1

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks : ℕ}

/-- The logical masked letters (implemented by `NativeMaskedProgram.compile` with three native
calls each). -/
abbrev logicalOracle (D : Data (X × Fin Ks) n Z s) (K M : ℕ) :
    Letter K → X → NativeMaskedOracle.Logical (Omega K M) (PBasis Ks n Z) →L[ℂ]
      NativeMaskedOracle.Logical (Omega K M) (PBasis Ks n Z) :=
  NativeMaskedProgram.logicalOracle (timeOracle D) letterLabel letterActive

/-- Masked, time-coherent copy of a native program in slot `j` (fixed gates as in the release's
`TimeDependent.liftProgram`, then masked). -/
def liftSlot (D : Data (X × Fin Ks) n Z s) {K M : ℕ} (j : Fin K) :
    MultiOracleCircuit.Program (oracles D) → MultiOracleCircuit.Program (logicalOracle D K M)
  | .fixed U hU => .fixed
      (MaskedProgram.masked (fun ω : Omega K M => labActive (j : ℕ) ω.1)
        (TimeDependent.timeIndexed (fun _ : Fin Ks => flatGate U)))
      (MaskedProgram.masked_unitary _ _
        (TimeDependent.timeIndexed_unitary _ (fun _ => IsUnitary.transport hU _)))
  | .query l => .query (l, j)
  | .queryAdjoint l => .queryAdjoint (l, j)
  | .seq p q => .seq (liftSlot D j p) (liftSlot D j q)

omit [DecidableEq Z] in
/-- A lifted slot program evaluates to the masked, time-coherent flat gate of the program. -/
theorem liftSlot_eval (D : Data (X × Fin Ks) n Z s) {K M : ℕ} (j : Fin K)
    (p : MultiOracleCircuit.Program (oracles D)) (x : X) :
    (liftSlot (M := M) D j p).eval x =
      MaskedProgram.masked (fun ω : Omega K M => labActive (j : ℕ) ω.1)
        (TimeDependent.timeIndexed (fun r => flatGate (p.eval (x, r)))) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l =>
      change star (MaskedProgram.masked (fun ω : Omega K M => labActive (j : ℕ) ω.1)
        (TimeDependent.timeIndexed (fun r => flatGate (oracles D l (x, r))))) = _
      rw [star_eq_adjoint, MaskedProgram.masked_adjoint, ← star_eq_adjoint,
        TimeDependent.timeIndexed_star]
      simp only [flatGate, map_star, MultiOracleCircuit.Program.eval_queryAdjoint]
  | seq p q hp hq =>
      change (liftSlot D j p).eval x * (liftSlot D j q).eval x = _
      rw [hp, hq, ← MaskedProgram.masked_mul, TimeDependent.timeIndexed_mul]
      simp only [MultiOracleCircuit.Program.eval_seq, flatGate_mul]

omit [DecidableEq Z] in
/-- Lifting a slot program preserves its weighted native cost. -/
theorem liftSlot_cost (D : Data (X × Fin Ks) n Z s) {K M : ℕ} (j : Fin K)
    (p : MultiOracleCircuit.Program (oracles D)) (w : Query → ℕ) :
    (liftSlot (M := M) D j p).cost (fun m => w (letterLabel m)) = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (liftSlot D j p).cost _ + (liftSlot D j q).cost _ = _
      rw [hp, hq]
      rfl

omit [DecidableEq Z] in
/-- Lifting a slot program preserves its query count. -/
theorem liftSlot_count (D : Data (X × Fin Ks) n Z s) {K M : ℕ} (j : Fin K)
    (p : MultiOracleCircuit.Program (oracles D)) :
    (liftSlot (M := M) D j p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq =>
      change (liftSlot D j p).count + (liftSlot D j q).count = _
      rw [hp, hq]
      rfl

/-- The known time gate of slot `j`: on every branch, swap the time addresses `0` and
`labTime j`. -/
def timeGate {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (j : ℕ) :
    NativeMaskedOracle.Logical (Omega K M) (PBasis Ks n Z) →L[ℂ]
      NativeMaskedOracle.Logical (Omega K M) (PBasis Ks n Z) :=
  WeightedClock.diagonal (fun ω : Omega K M => timeSwap (n := n) (Z := Z) hK (labTime hM σ j ω.1))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- The time gate of a slot is unitary. -/
theorem timeGate_unitary {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks) (j : ℕ) :
    IsUnitary (timeGate (n := n) (Z := Z) (K := K) (M := M) hM hK σ j) :=
  CoherentQuerySchedule.diagonal_unitary _ (fun _ => timeSwap_unitary hK _)

/-- **Slot `j`**: time gate, masked six-query block encoding, time gate, flag split. -/
def slotProgram {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (j : Fin K) :
    MultiOracleCircuit.Program (logicalOracle D K M) :=
  .seq (.fixed (flagSplit (Λ := Lab K M) (payloadEncoding hK D) j)
      (flagSplit_unitary _ (payloadEncoding_isometry hK D) j))
    (.seq (.fixed (timeGate hM hK σ j) (timeGate_unitary hM hK σ j))
      (.seq (liftSlot D j (NativeSparseBlockEncoding.program D))
        (.fixed (timeGate hM hK σ j) (timeGate_unitary hM hK σ j))))

/-- The first `m` slots (slot `0` executed first). -/
def selectUpTo {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) : ℕ → MultiOracleCircuit.Program (logicalOracle D K M)
  | 0 => MultiOracleCircuit.Program.identity
  | m + 1 =>
      if h : m < K then .seq (slotProgram hM hK σ D ⟨m, h⟩) (selectUpTo hM hK σ D m)
      else selectUpTo hM hK σ D m

/-- **The logical Dyson SELECT** with `K` slots. -/
def logicalSelect {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) : MultiOracleCircuit.Program (logicalOracle D K M) :=
  selectUpTo hM hK σ D K

/-- The payload operator of slot `j` on label `l`. -/
def slotOperator {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (x : X) (j : ℕ) (l : Lab K M) :
    EuclideanSpace ℂ (PBasis Ks n Z) →L[ℂ] EuclideanSpace ℂ (PBasis Ks n Z) :=
  timeSwap hK (labTime hM σ j l) ∘L
    (if labActive j l then
      TimeDependent.timeIndexed
        (fun r => flatGate ((NativeSparseBlockEncoding.program D).eval (x, r)))
    else 1) ∘L timeSwap hK (labTime hM σ j l)

/-- One slot evaluates to the flagged layer of its slot operators: the two time gates and the
masked block encoding form the branch-diagonal operator `slotOperator`, then the flag split. -/
theorem slotProgram_eval {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (x : X) (j : Fin K) :
    (slotProgram hM hK σ D j).eval x =
      layer (Λ := Lab K M) (K := K) (payloadEncoding hK D) (slotOperator hM hK σ D x j) j := by
  rw [layer, dif_pos j.isLt]
  simp only [slotProgram, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_fixed, liftSlot_eval, mul_def, Fin.eta]
  congr 1

/-- The first `m` slots evaluate to the ordered product of the first `m` flagged layers (for
every `m`; the layers beyond `K` are identities). -/
theorem selectUpTo_eval {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (x : X) (m : ℕ) :
    (selectUpTo (K := K) hM hK σ D m).eval x =
      evolution (fun j => layer (Λ := Lab K M) (K := K) (payloadEncoding hK D)
        (slotOperator hM hK σ D x j) j) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [TimeDependent.evolution_succ, ← ih]
      by_cases h : m < K
      · simp only [selectUpTo, dif_pos h, MultiOracleCircuit.Program.eval_seq]
        rw [slotProgram_eval]
      · simp only [selectUpTo, dif_neg h, layer, one_mul]

/-- The circuit is the product of the flagged layers of the slot operators. -/
theorem logicalSelect_eval {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (x : X) :
    (logicalSelect hM hK σ D K).eval x =
      evolution (fun j => layer (Λ := Lab K M) (K := K) (payloadEncoding hK D)
        (slotOperator hM hK σ D x j) j) K :=
  selectUpTo_eval hM hK σ D x K

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
/-- The known time swap is an involution. -/
theorem timeSwap_comp_self (hK : 0 < Ks) (r : Fin Ks) :
    timeSwap (n := n) (Z := Z) hK r ∘L timeSwap hK r = 1 := by
  ext v ⟨a, b⟩
  simp [timeSwap]

/-- One slot compresses to the selected sample when active and to the identity otherwise. -/
theorem slotOperator_compression {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (x : X) (j : ℕ) (l : Lab K M) :
    (payloadEncoding hK D)† ∘L slotOperator hM hK σ D x j l ∘L payloadEncoding hK D =
      if labActive j l then sampleOperator D x (labTime hM σ j l) else 1 := by
  cases hl : labActive j l
  · simp only [slotOperator, hl, Bool.false_eq_true, if_false]
    rw [one_def, id_comp, timeSwap_comp_self]
    simpa only [one_def, id_comp] using payloadEncoding_isometry hK D
  · simp only [slotOperator, hl, if_true, comp_assoc]
    exact slot_compression hK D x _

/-- The samples along the mesh cells: `A_{σ r}/(s Λ)` for `r < M`. -/
def sampleSeq {M : ℕ} (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) :
    ℕ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  fun r => if h : r < M then sampleOperator D x (σ ⟨r, h⟩) else 0

/-- **The selected operator of an LCU label**: the time-ordered product of the configuration's
samples `A_{σ r}/(s Λ)`; the identity on the padding branches. -/
def branchOperator {K M : ℕ} (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X) :
    Lab K M → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n
  | (_, .inl c) => cfgProduct (sampleSeq σ D x) c
  | (_, .inr _) => 1

/-- Every selected operator is a contraction. -/
theorem branchOperator_norm_le {K M : ℕ} (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (x : X) (l : Lab K M) : ‖branchOperator σ D x l‖ ≤ 1 := by
  rcases l with ⟨q, c | b⟩
  · refine cfgProduct_norm_le_one _ (fun r => ?_) c
    unfold sampleSeq
    split_ifs
    · exact sampleOperator_norm_le D x _
    · simp
  · exact ContinuousLinearMap.norm_id_le

omit [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- An ordered product of identities is the identity. -/
theorem evolution_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (m : ℕ) :
    evolution (fun _ => (1 : V →L[ℂ] V)) m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [TimeDependent.evolution_succ, ih, one_mul]

/-- **Compression of the logical SELECT** (lines 4200-4206): at all flags zero, the circuit
is the branch-diagonal operator of the selected time-ordered products. -/
theorem logicalSelect_compression {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (x : X) :
    (zeroFlags (Λ := Lab K M) (K := K) (payloadEncoding hK D))† ∘L
        (logicalSelect hM hK σ D K).eval x ∘L zeroFlags (payloadEncoding hK D) =
      WeightedClock.diagonal (branchOperator (K := K) σ D x) := by
  rw [logicalSelect_eval]
  refine (flagged_compression _ (payloadEncoding_isometry hK D)
    (fun j => slotOperator hM hK σ D x j)).trans ?_
  congr 1
  funext l
  refine (TimeDependentExtensions.evolution_congr' _ _ K
    (fun k _ => slotOperator_compression hM hK σ D x k l)).trans ?_
  rcases l with ⟨q, c | b⟩
  · rw [show branchOperator (K := K) σ D x (q, .inl c) = cfgProduct (sampleSeq σ D x) c from rfl,
      ← slot_product hM (sampleSeq σ D x) c]
    congr 1
    funext j
    show (if c.active j then sampleOperator D x (σ (c.cell hM j)) else 1) =
      if c.active j then sampleSeq σ D x (c.cell hM j) else 1
    simp only [sampleSeq, dif_pos (c.cell hM j).isLt, Fin.eta]
  · show evolution (fun _ => (if false = true then _ else 1)) K = 1
    simp only [Bool.false_eq_true, if_false]
    exact evolution_one K

/-- One slot: six logical letters (`NativeSparseBlockEncoding.program_count`). -/
theorem slotProgram_count {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (j : Fin K) : (slotProgram hM hK σ D j).count = 6 := by
  simp only [slotProgram, MultiOracleCircuit.Program.count_seq,
    MultiOracleCircuit.Program.count_fixed, liftSlot_count, program_count]

/-- One slot: one row, one column and four value letters. -/
theorem slotProgram_cost {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (j : Fin K) (w : Query → ℕ) :
    (slotProgram hM hK σ D j).cost (fun m => w (letterLabel m)) =
      w .rowLocation + w .columnLocation + 4 * w .value := by
  simp only [slotProgram, MultiOracleCircuit.Program.cost_seq,
    MultiOracleCircuit.Program.cost_fixed, liftSlot_cost, program_cost]
  ring

/-- The first `m ≤ K` slots: `6 m` logical letters. -/
theorem selectUpTo_count {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (m : ℕ) (hm : m ≤ K) :
    (selectUpTo (K := K) hM hK σ D m).count = 6 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      have h : m < K := hm
      simp only [selectUpTo, dif_pos h, MultiOracleCircuit.Program.count_seq,
        slotProgram_count, ih h.le]
      ring

/-- The first `m ≤ K` slots: `m` row, `m` column and `4 m` value letters. -/
theorem selectUpTo_cost {K M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (w : Query → ℕ) (m : ℕ) (hm : m ≤ K) :
    (selectUpTo (K := K) hM hK σ D m).cost (fun l => w (letterLabel l)) =
      m * (w .rowLocation + w .columnLocation + 4 * w .value) := by
  induction m with
  | zero => simp [selectUpTo]
  | succ m ih =>
      have h : m < K := hm
      simp only [selectUpTo, dif_pos h, MultiOracleCircuit.Program.cost_seq,
        slotProgram_cost, ih h.le]
      ring

/-- `6 K` logical letters in total. -/
theorem logicalSelect_count {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) :
    (logicalSelect hM hK σ D K).count = 6 * K :=
  selectUpTo_count hM hK σ D K le_rfl

/-- Per native label: `K` row, `K` column and `4 K` value letters. -/
theorem logicalSelect_cost {M : ℕ} (hM : 0 < M) (hK : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (w : Query → ℕ) :
    (logicalSelect hM hK σ D K).cost (fun m => w (letterLabel m)) =
      K * (w .rowLocation + w .columnLocation + 4 * w .value) :=
  selectUpTo_cost hM hK σ D w K le_rfl

end

end ODELowerBoundExtensions.Dyson
