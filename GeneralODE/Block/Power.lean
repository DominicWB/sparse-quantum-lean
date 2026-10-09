import GeneralODE.Block.Selected

/-!
# Products of block encodings with fresh ancillas

`powOp fac k` applies the factors `fac 0, …, fac (k-1)` in this order, each on
the system and its own fresh copy of the ancilla register `ν`.  Its block for
the clean ancilla state is the ordered product of the factor blocks
`blk (fac (k-1)) ⋯ blk (fac 0)`.  The corresponding programs are built by
lifting the factor programs; the `i`-th factor queries the labels `(i, l)`, and
every such oracle sends the fixed valid basis state to a basis state when the
factor oracles do.
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators ComplexConjugate

variable {σ ν : Type} [Fintype σ] [Fintype ν] [DecidableEq σ] [DecidableEq ν]

/-- Ancilla registers for `k` fresh factors. -/
def Anc (ν : Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => Anc ν k × ν

instance instFintypeAnc : ∀ k, Fintype (Anc ν k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => @instFintypeProd _ _ (instFintypeAnc k) _

instance instDecidableEqAnc : ∀ k, DecidableEq (Anc ν k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => @instDecidableEqProd _ _ (instDecidableEqAnc k) _

/-- The clean ancilla configuration. -/
def cleanAnc (n0 : ν) : ∀ k, Anc ν k
  | 0 => ()
  | k + 1 => (cleanAnc n0 k, n0)

theorem single_pair {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (a : α) (b : β) :
    (EuclideanSpace.single (a, b) (1 : ℂ) : EuclideanSpace ℂ (α × β)) =
      tens (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
  ext ⟨a', b'⟩
  simp only [tens_apply, PiLp.single_apply, Prod.mk.injEq]
  by_cases ha : a' = a <;> by_cases hb : b' = b <;> simp [ha, hb]

/-- The ordered product of `k` fresh factors. -/
def powOp (fac : ℕ → (EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν))) :
    ∀ k, EuclideanSpace ℂ (σ × Anc ν k) →L[ℂ] EuclideanSpace ℂ (σ × Anc ν k)
  | 0 => 1
  | k + 1 => onFactor (secondFrame σ (Anc ν k) ν) (fac k) *
      onFactor (firstFrame σ (Anc ν k) ν) (powOp fac k)

/-- Ordered product of operators. -/
def ordProd (B : ℕ → (EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ σ)) :
    ℕ → (EuclideanSpace ℂ σ →L[ℂ] EuclideanSpace ℂ σ)
  | 0 => 1
  | k + 1 => B k * ordProd B k

omit [DecidableEq σ] in
theorem blk_one_unit :
    blk (EuclideanSpace.single () 1) (EuclideanSpace.single () 1)
      (1 : EuclideanSpace ℂ (σ × Unit) →L[ℂ] EuclideanSpace ℂ (σ × Unit)) = 1 := by
  unfold blk
  ext1 v
  rw [comp_apply, one_comp_eq, braR_ketR]
  simp

omit [DecidableEq σ] in
/-- Block of a fresh-ancilla product. -/
theorem blk_powOp (fac : ℕ → (EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν)))
    (n0 : ν) (k : ℕ) :
    blk (EuclideanSpace.single (cleanAnc n0 k) 1) (EuclideanSpace.single (cleanAnc n0 k) 1)
        (powOp fac k) =
      ordProd (fun i => blk (EuclideanSpace.single n0 1) (EuclideanSpace.single n0 1) (fac i)) k := by
  induction k with
  | zero => exact blk_one_unit
  | succ k ih =>
      change blk (EuclideanSpace.single (cleanAnc n0 k, n0) 1)
          (EuclideanSpace.single (cleanAnc n0 k, n0) 1)
          (onFactor (secondFrame σ (Anc ν k) ν) (fac k) *
            onFactor (firstFrame σ (Anc ν k) ν) (powOp fac k)) = _
      rw [single_pair, blk_mul_fresh, ih]
      rfl

omit [DecidableEq σ] [DecidableEq ν] in
theorem powOp_unitary (fac : ℕ → (EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν)))
    (hfac : ∀ i, IsUnitary (fac i)) (k : ℕ) : IsUnitary (powOp fac k) := by
  induction k with
  | zero => exact isUnitary_one
  | succ k ih => exact (onFactor_unitary _ (hfac k)).mul (onFactor_unitary _ ih)

/-- Ordered products of selected maps are selected ordered products. -/
theorem ordProd_selMap {C α : Type} [Fintype C] [Fintype α]
    (G : ℕ → C → (EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ α)) :
    ∀ k, ordProd (fun i => selMap (G i)) k = selMap (fun c => ordProd (fun i => G i c) k)
  | 0 => selMap_one.symm
  | k + 1 => by
      change selMap (G k) * ordProd (fun i => selMap (G i)) k =
        selMap (fun c => G k c * ordProd (fun i => G i c) k)
      rw [ordProd_selMap G k]
      exact selMap_comp _ _

section Programs

variable {X L : Type*}

/-- Oracle family of the power circuit: label `(i, l)` is the factor oracle `l`
on the `i`-th fresh copy. -/
def powOracle (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν)) :
    ∀ k, (Fin k × L) → X →
      EuclideanSpace ℂ (σ × Anc ν k) →L[ℂ] EuclideanSpace ℂ (σ × Anc ν k)
  | 0 => fun _ _ => 1
  | k + 1 => fun il x =>
      if h : il.1 = Fin.last k then onFactor (secondFrame σ (Anc ν k) ν) (F il.2 x)
      else onFactor (firstFrame σ (Anc ν k) ν)
        (powOracle F k (il.1.castPred h, il.2) x)

omit [DecidableEq σ] [DecidableEq ν] in
theorem powOracle_unitary (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν))
    (hF : ∀ l x, IsUnitary (F l x)) : ∀ k il x, IsUnitary (powOracle F k il x)
  | 0, _, _ => isUnitary_one
  | k + 1, il, x => by
      unfold powOracle
      split_ifs with h
      · exact onFactor_unitary _ (hF _ _)
      · exact onFactor_unitary _ (powOracle_unitary F hF k _ x)

/-- The power program from factor programs. -/
def powProg (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν))
    (facP : ℕ → MultiOracleCircuit.Program F) :
    ∀ k, MultiOracleCircuit.Program (powOracle F k)
  | 0 => .fixed 1 isUnitary_one
  | k + 1 => .seq
      (MultiOracleCircuit.Program.mapHom (onFactor (secondFrame σ (Anc ν k) ν))
        (fun l => (Fin.last k, l)) (facP k))
      (MultiOracleCircuit.Program.mapHom (onFactor (firstFrame σ (Anc ν k) ν))
        (fun il : Fin k × L => (il.1.castSucc, il.2)) (powProg F facP k))

omit [DecidableEq σ] [DecidableEq ν] in
theorem powProg_eval (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν))
    (facP : ℕ → MultiOracleCircuit.Program F) (k : ℕ) (x : X) :
    (powProg F facP k).eval x = powOp (fun i => (facP i).eval x) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (MultiOracleCircuit.Program.mapHom _ _ (facP k)).eval x *
        (MultiOracleCircuit.Program.mapHom _ _ (powProg F facP k)).eval x = _
      rw [MultiOracleCircuit.Program.eval_mapHom _ _ (fun l y => dif_pos rfl),
        MultiOracleCircuit.Program.eval_mapHom _ _ (fun il y => by
          change (if h : il.1.castSucc = Fin.last k then _ else _) = _
          rw [dif_neg (Fin.castSucc_ne_last il.1)]
          simp only [Fin.castPred_castSucc]
          rfl), ih]
      rfl

omit [DecidableEq σ] [DecidableEq ν] in
theorem powProg_count (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν))
    (facP : ℕ → MultiOracleCircuit.Program F) (k : ℕ) :
    (powProg F facP k).count = ∑ i ∈ Finset.range k, (facP i).count := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (MultiOracleCircuit.Program.mapHom _ _ (facP k)).count +
        (MultiOracleCircuit.Program.mapHom _ _ (powProg F facP k)).count = _
      rw [MultiOracleCircuit.Program.count_mapHom, MultiOracleCircuit.Program.count_mapHom, ih,
        Finset.sum_range_succ, add_comm]

omit [DecidableEq σ] [DecidableEq ν] in
/-- Weighted costs for label weights depending only on the factor label. -/
theorem powProg_cost (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν))
    (facP : ℕ → MultiOracleCircuit.Program F) (w : L → ℕ) (k : ℕ) :
    (powProg F facP k).cost (fun il => w il.2) = ∑ i ∈ Finset.range k, (facP i).cost w := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (MultiOracleCircuit.Program.mapHom _ _ (facP k)).cost
          (fun il : Fin (k + 1) × L => w il.2) +
        (MultiOracleCircuit.Program.mapHom _ _ (powProg F facP k)).cost
          (fun il : Fin (k + 1) × L => w il.2) = _
      rw [MultiOracleCircuit.Program.cost_mapHom, MultiOracleCircuit.Program.cost_mapHom]
      rw [show (fun il : Fin k × L => w (il.1.castSucc, il.2).2) = fun il => w il.2 from rfl, ih,
        Finset.sum_range_succ, add_comm]

/-- Basis-state validity propagates to the power oracles. -/
theorem powOracle_single
    (F : L → X → EuclideanSpace ℂ (σ × ν) →L[ℂ] EuclideanSpace ℂ (σ × ν))
    (s0 : σ) (n0 : ν) (img : L → X → ν)
    (hF : ∀ l x, F l x (EuclideanSpace.single (s0, n0) 1) =
      EuclideanSpace.single (s0, img l x) 1) :
    ∀ k (il : Fin k × L) x, ∃ a' : Anc ν k,
      powOracle F k il x (EuclideanSpace.single (s0, cleanAnc n0 k) 1) =
        EuclideanSpace.single (s0, a') 1
  | 0, il, _ => il.1.elim0
  | k + 1, il, x => by
      unfold powOracle
      split_ifs with h
      · refine ⟨(cleanAnc n0 k, img il.2 x), ?_⟩
        have := onFactor_single (secondFrame σ (Anc ν k) ν) (F il.2 x) (s0, n0) (s0, img il.2 x)
          1 (hF il.2 x) (cleanAnc n0 k)
        exact this
      · obtain ⟨a', ha'⟩ := powOracle_single F s0 n0 img hF k (il.1.castPred h, il.2) x
        refine ⟨(a', n0), ?_⟩
        have := onFactor_single (firstFrame σ (Anc ν k) ν)
          (powOracle F k (il.1.castPred h, il.2) x) (s0, cleanAnc n0 k) (s0, a') 1 ha' n0
        exact this

end Programs

end

end SparseHamiltonian.GeneralODE.Registers
