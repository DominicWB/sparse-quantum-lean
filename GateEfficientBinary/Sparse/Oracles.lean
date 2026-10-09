import GateEfficientBinary.Sparse.Layout
import GateEfficientBinary.Sparse.Gadget
import GateEfficientBinary.Cordic.Arith

/-!
# The compute circuit of the private operation from binary sparse oracles

The native sparse oracles of `NativeSparseBlockEncoding.Data`, with `k`-bit indices and entries
stored as two `b`-bit two's complement components, act as qubit primitives on an edge register
and `2b` value wires (`prims`): the row and column location oracles on the edge register, the
value oracle by XOR-ing the stored bits of the entry into the value wires.

The public compute circuit (`computeV`) of the private operation

1. writes the images of the all-zero edge under the row and the column location oracle into two
   reference registers (one call each);
2. applies the row location oracle to the index wires when the orientation wire is `0` and the
   column location oracle when it is `1`, by the controlled-call gadget of `Sparse/Gadget` with
   a shared dummy register (one call each, `7 · 2k` elementary gates each);
3. XORs the stored entry of the located edge into the value wires (one value call).

On clean scratch it acts as the qubit lift of the full locator followed by a permutation of
basis configurations (`compute_cleanEmb`), and the decoded rotation commutes past that
permutation into the lifted edge action (`rdec_sigma`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinary

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out localOp_localOp'
  update_comp_injective)
open scoped InnerProduct

/-! ### Permutations of configurations -/

section Perm

variable {A C W : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype W] [DecidableEq W]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- XOR a function `f` of the `A`-part into the `C`-part (an involution). -/
def xorEquiv (f : Cfg A → Cfg C) : Cfg (A ⊕ C) ≃ Cfg (A ⊕ C) where
  toFun y := Sum.elim (fun a => y (Sum.inl a))
    (fun c => y (Sum.inr c) ^^ f (fun a => y (Sum.inl a)) c)
  invFun y := Sum.elim (fun a => y (Sum.inl a))
    (fun c => y (Sum.inr c) ^^ f (fun a => y (Sum.inl a)) c)
  left_inv y := by
    funext w
    rcases w with a | c <;> simp
  right_inv y := by
    funext w
    rcases w with a | c <;> simp

omit [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] in
@[simp] theorem xorEquiv_inl (f : Cfg A → Cfg C) (y : Cfg (A ⊕ C)) (a : A) :
    xorEquiv f y (Sum.inl a) = y (Sum.inl a) := rfl

omit [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] in
@[simp] theorem xorEquiv_inr (f : Cfg A → Cfg C) (y : Cfg (A ⊕ C)) (c : C) :
    xorEquiv f y (Sum.inr c) = (y (Sum.inr c) ^^ f (fun a => y (Sum.inl a)) c) := rfl

omit [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] in
theorem xorEquiv_symm (f : Cfg A → Cfg C) : (xorEquiv f).symm = xorEquiv f := rfl

omit [DecidableEq A] [Fintype W] in
theorem comp_overwrite {ι : A → W} (hι : Function.Injective ι) (y : Cfg W) (d : Cfg A) :
    (fun a => overwrite ι y d (ι a)) = d :=
  funext (overwrite_apply_ι hι y d)

omit [DecidableEq A] [Fintype W] in
theorem overwrite_self {ι : A → W} (hι : Function.Injective ι) (y : Cfg W) :
    overwrite ι y (fun a => y (ι a)) = y :=
  joinCfg_self hι y

omit [DecidableEq A] [Fintype W] in
theorem overwrite_update_out {ι : A → W} (hι : Function.Injective ι) (y : Cfg W) (d : Cfg A)
    (w : W) (v : Bool) (hw : ∀ a, ι a ≠ w) :
    overwrite ι (Function.update y w v) d = Function.update (overwrite ι y d) w v := by
  funext u
  by_cases hu : ∃ a, ι a = u
  · obtain ⟨a, rfl⟩ := hu
    rw [overwrite_apply_ι hι, Function.update_of_ne (hw a), overwrite_apply_ι hι]
  · have hu' : ∀ a, ι a ≠ u := fun a ha => hu ⟨a, ha⟩
    rw [overwrite_apply_out ι _ d u hu']
    by_cases huw : u = w
    · subst huw
      simp
    · rw [Function.update_of_ne huw, Function.update_of_ne huw, overwrite_apply_out ι _ d u hu']

/-- A permutation of the configurations of the wires `ι`, at fixed other wires. -/
def alongEquiv (ι : A ↪ W) (e : Cfg A ≃ Cfg A) : Cfg W ≃ Cfg W where
  toFun y := overwrite ι y (e (fun a => y (ι a)))
  invFun y := overwrite ι y (e.symm (fun a => y (ι a)))
  left_inv y := by
    simp only [comp_overwrite ι.injective, overwrite_overwrite, Equiv.symm_apply_apply]
    exact overwrite_self ι.injective y
  right_inv y := by
    simp only [comp_overwrite ι.injective, overwrite_overwrite, Equiv.apply_symm_apply]
    exact overwrite_self ι.injective y

omit [CompleteSpace R] in
theorem permOp_bas (e : Cfg W ≃ Cfg W) (y : Cfg W) (q : R) :
    permOp e (bas y q) = bas (e y) q :=
  perm_bas e y q

/-- A primitive permutation placed on the wires `ι` is a permutation of the register. -/
theorem localOp_permOp (ι : A ↪ W) (e : Cfg A ≃ Cfg A) :
    localOp ι ι.injective (fun _ => permOp (Q := R) e) = permOp (alongEquiv ι e) := by
  apply ext_bas_clm
  intro y q
  rw [localOp_bas, permOp_bas, put_bas, permOp_bas]
  rfl

end Perm

/-! ### Clean embeddings and lifted operators -/

section Clean

variable {B X : Type*} [Fintype B] [DecidableEq B] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [CompleteSpace R] in
/-- Two maps out of a register agree once they agree on basis vectors. -/
theorem ext_bas_clm' {W K : Type*} [Fintype W] [DecidableEq W] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (f g : Reg W R →L[ℂ] K) (h : ∀ x q, f (bas x q) = g (bas x q)) :
    f = g :=
  ContinuousLinearMap.coe_injective (ext_bas (f : Reg W R →ₗ[ℂ] K) g h)

omit [DecidableEq B] [DecidableEq X] [CompleteSpace R] in
theorem cleanEmb_bas (c : Cfg B) (q : R) :
    cleanEmb (X := X) (bas c q) = bas (Sum.elim c (fun _ => false)) q := by
  apply PiLp.ext
  intro y
  rw [cleanEmb_apply, bas_apply]
  by_cases h : (fun x => y (Sum.inr x)) = fun _ => false
  · rw [if_pos h, bas_apply]
    by_cases hc : (fun b => y (Sum.inl b)) = c
    · rw [if_pos hc, if_pos]
      funext w
      rcases w with b | x
      · exact congrFun hc b
      · exact congrFun h x
    · rw [if_neg hc, if_neg]
      intro hy
      apply hc
      rw [hy]
      rfl
  · rw [if_neg h, bas_apply, if_neg]
    intro hy
    apply h
    rw [hy]
    rfl

/-- An operator on the `B`-wires commutes with XOR-ing a constant into the work wires. -/
theorem liftB_comm_xor (O : Reg B R →L[ℂ] Reg B R) (κ : Cfg X) :
    liftB (X := X) O ∘L permOp (xorEquiv (fun _ : Cfg B => κ)) =
      permOp (xorEquiv (fun _ : Cfg B => κ)) ∘L liftB O := by
  have h1 : ∀ (z : Cfg (B ⊕ X)) (d : Cfg B),
      (xorEquiv (fun _ : Cfg B => κ)).symm (overwrite Sum.inl z d) =
        overwrite Sum.inl ((xorEquiv (fun _ : Cfg B => κ)).symm z) d := by
    intro z d
    rw [xorEquiv_symm]
    funext w
    rcases w with a | x
    · rw [xorEquiv_inl, overwrite_apply_ι Sum.inl_injective, overwrite_apply_ι Sum.inl_injective]
    · rw [xorEquiv_inr, overwrite_apply_out Sum.inl z d _ (fun a h => by cases h),
        overwrite_apply_out Sum.inl _ d _ (fun a h => by cases h), xorEquiv_inr]
  ext ψ z
  have hs : slice Sum.inl (permOp (xorEquiv (fun _ : Cfg B => κ)) ψ) z =
      slice Sum.inl ψ ((xorEquiv (fun _ : Cfg B => κ)).symm z) := by
    apply PiLp.ext
    intro d
    simp only [slice_apply, permOp_apply, h1]
  have hz : (fun a => (xorEquiv (fun _ : Cfg B => κ)).symm z (Sum.inl a)) =
      fun a => z (Sum.inl a) := rfl
  simp only [comp_apply, permOp_apply, liftB, localOp_apply, hs, hz]

end Clean

/-! ### Wires of the private operation -/

/-- The value wires: the real part (`inl`) and the imaginary part (`inr`) of an entry. -/
abbrev VW (b : ℕ) := Fin b ⊕ Fin b

/-- The register of the primitive oracles: an edge register and the value wires. -/
abbrev PY (k b : ℕ) := EW k ⊕ VW b

/-- The scratch wires: a dummy edge register, the row and the column reference registers and
the value wires. -/
abbrev SZ (k b : ℕ) := ((EW k ⊕ EW k) ⊕ EW k) ⊕ VW b

/-- The base wires of the private operation (no selection wires). -/
abbrev BW (k b : ℕ) := NB Empty (PR k) (SZ k b)

section Wires

variable {k b : ℕ}

/-- The orientation wire. -/
def oB : BW k b := Sum.inl (Sum.inr (oPR k))

/-- The index wires. -/
def tB (e : EW k) : BW k b := Sum.inl (Sum.inr (ixPR k e))

/-- The dummy register. -/
def dmB (e : EW k) : BW k b := Sum.inr (Sum.inl (Sum.inl (Sum.inl e)))

/-- The row reference register. -/
def rrB (e : EW k) : BW k b := Sum.inr (Sum.inl (Sum.inl (Sum.inr e)))

/-- The column reference register. -/
def rcB (e : EW k) : BW k b := Sum.inr (Sum.inl (Sum.inr e))

/-- The value wires. -/
def vB (v : VW b) : BW k b := Sum.inr (Sum.inr v)

theorem tB_injective : Function.Injective (tB (k := k) (b := b)) := by
  intro e e' h
  exact ixPR_injective k (Sum.inr_injective (Sum.inl_injective h))

theorem dmB_injective : Function.Injective (dmB (k := k) (b := b)) := by
  intro e e' h
  simpa [dmB] using h

theorem rrB_injective : Function.Injective (rrB (k := k) (b := b)) := by
  intro e e' h
  simpa [rrB] using h

theorem rcB_injective : Function.Injective (rcB (k := k) (b := b)) := by
  intro e e' h
  simpa [rcB] using h

theorem vB_injective : Function.Injective (vB (k := k) (b := b)) := by
  intro v v' h
  simpa [vB] using h

theorem tB_ne_oB (e : EW k) : tB (b := b) e ≠ oB := by
  intro h
  exact ixPR_ne_o k e (Sum.inr_injective (Sum.inl_injective h))

@[simp] theorem tB_ne_dmB (e e' : EW k) : tB (b := b) e ≠ dmB e' := by simp [tB, dmB]
@[simp] theorem tB_ne_rrB (e e' : EW k) : tB (b := b) e ≠ rrB e' := by simp [tB, rrB]
@[simp] theorem tB_ne_rcB (e e' : EW k) : tB (b := b) e ≠ rcB e' := by simp [tB, rcB]
@[simp] theorem tB_ne_vB (e : EW k) (v : VW b) : tB e ≠ vB v := by simp [tB, vB]
@[simp] theorem dmB_ne_oB (e : EW k) : dmB (b := b) e ≠ oB := by simp [dmB, oB]
@[simp] theorem rrB_ne_oB (e : EW k) : rrB (b := b) e ≠ oB := by simp [rrB, oB]
@[simp] theorem rcB_ne_oB (e : EW k) : rcB (b := b) e ≠ oB := by simp [rcB, oB]
@[simp] theorem vB_ne_oB (v : VW b) : vB (k := k) v ≠ oB := by simp [vB, oB]
@[simp] theorem dmB_ne_rrB (e e' : EW k) : dmB (b := b) e ≠ rrB e' := by simp [dmB, rrB]
@[simp] theorem dmB_ne_rcB (e e' : EW k) : dmB (b := b) e ≠ rcB e' := by simp [dmB, rcB]
@[simp] theorem rrB_ne_rcB (e e' : EW k) : rrB (b := b) e ≠ rcB e' := by simp [rrB, rcB]
@[simp] theorem rrB_ne_vB (e : EW k) (v : VW b) : rrB e ≠ vB v := by simp [rrB, vB]
@[simp] theorem rcB_ne_vB (e : EW k) (v : VW b) : rcB e ≠ vB v := by simp [rcB, vB]
@[simp] theorem dmB_ne_vB (e : EW k) (v : VW b) : dmB e ≠ vB v := by simp [dmB, vB]

/-- The positions of a call on the index wires and the value wires. -/
def posT : PY k b ↪ BW k b :=
  ⟨Sum.elim tB vB, tB_injective.sumElim vB_injective tB_ne_vB⟩

/-- The positions of a call on the row reference register and the value wires. -/
def posRR : PY k b ↪ BW k b :=
  ⟨Sum.elim rrB vB, rrB_injective.sumElim vB_injective rrB_ne_vB⟩

/-- The positions of a call on the column reference register and the value wires. -/
def posRC : PY k b ↪ BW k b :=
  ⟨Sum.elim rcB vB, rcB_injective.sumElim vB_injective rcB_ne_vB⟩

/-- A configuration of the base wires is determined by its parts. -/
theorem bw_ext {y y' : Cfg (BW k b)} (hp : ∀ p, y (Sum.inl p) = y' (Sum.inl p))
    (hd : ∀ e, y (dmB e) = y' (dmB e)) (hr : ∀ e, y (rrB e) = y' (rrB e))
    (hc : ∀ e, y (rcB e) = y' (rcB e)) (hv : ∀ v, y (vB v) = y' (vB v)) : y = y' := by
  funext w
  rcases w with p | (((e | e) | e) | v)
  · exact hp p
  · exact hd e
  · exact hr e
  · exact hc e
  · exact hv v

end Wires

/-! ### Updates and permutations -/

section PermUpdate

variable {A C W : Type*} [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
  [Fintype W] [DecidableEq W]

omit [Fintype A] [Fintype C] in
theorem xorEquiv_update_inl (κ : Cfg C) (y : Cfg (A ⊕ C)) (a : A) (v : Bool) :
    xorEquiv (fun _ : Cfg A => κ) (Function.update y (Sum.inl a) v) =
      Function.update (xorEquiv (fun _ : Cfg A => κ) y) (Sum.inl a) v := by
  funext w
  rcases w with a' | c
  · by_cases ha : a' = a
    · subst ha
      simp
    · have hne : (Sum.inl a' : A ⊕ C) ≠ Sum.inl a := fun h => ha (Sum.inl_injective h)
      rw [xorEquiv_inl, Function.update_of_ne hne, Function.update_of_ne hne, xorEquiv_inl]
  · have hne : (Sum.inr c : A ⊕ C) ≠ Sum.inl a := fun h => by cases h
    rw [xorEquiv_inr, Function.update_of_ne hne, Function.update_of_ne hne, xorEquiv_inr]

omit [Fintype W] in
theorem alongEquiv_apply_in (ι : A ↪ W) (e : Cfg A ≃ Cfg A) (y : Cfg W) (a : A) :
    alongEquiv ι e y (ι a) = e (fun a => y (ι a)) a :=
  overwrite_apply_ι ι.injective _ _ a

omit [Fintype W] in
theorem alongEquiv_apply_out (ι : A ↪ W) (e : Cfg A ≃ Cfg A) (y : Cfg W) (w : W)
    (hw : ∀ a, ι a ≠ w) : alongEquiv ι e y w = y w :=
  overwrite_apply_out ι _ _ w hw

omit [Fintype W] in
theorem alongEquiv_update_out (ι : A ↪ W) (e : Cfg A ≃ Cfg A) (y : Cfg W) (w : W) (v : Bool)
    (hw : ∀ a, ι a ≠ w) :
    alongEquiv ι e (Function.update y w v) = Function.update (alongEquiv ι e y) w v := by
  have h : (fun a => Function.update y w v (ι a)) = fun a => y (ι a) := by
    funext a
    exact Function.update_of_ne (hw a) _ _
  change overwrite ι (Function.update y w v) (e (fun a => Function.update y w v (ι a))) = _
  rw [h, overwrite_update_out ι.injective _ _ _ _ hw]
  rfl

end PermUpdate

/-! ### The primitive oracles -/

section Prims

open NativeSparseBlockEncoding (Data Query)

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- A stored entry as the Gaussian integer `X + i Y` of its two's complement components. -/
def gauss (z : Cfg (VW b)) : ℂ :=
  (twos (B := VW b) Sum.inl z : ℂ) + (twos (B := VW b) Sum.inr z : ℂ) * Complex.I

/-- The value oracle as a permutation of the primitive register: the stored bits of the entry
of the edge are XOR-ed into the value wires. -/
def valPerm (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Cfg (PY k b) ≃ Cfg (PY k b) :=
  xorEquiv (fun d => D.table x (phiE en d))

/-- **The primitive oracles** on an edge register and the value wires: the row and the column
location oracle on the edge register and the value oracle. -/
def prims (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R
  | .rowLocation =>
      localOp Sum.inl Sum.inl_injective (fun _ => qlift (phiE en) (D.rowOracle x))
  | .columnLocation =>
      localOp Sum.inl Sum.inl_injective (fun _ => qlift (phiE en) (D.columnOracle x))
  | .value => permOp (valPerm D en x)

theorem prims_row (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    prims (R := R) D en x Query.rowLocation =
      localOp Sum.inl Sum.inl_injective (fun _ => qlift (R := R) (phiE en) (D.rowOracle x)) := by
  simp only [prims]

theorem prims_col (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    prims (R := R) D en x Query.columnLocation =
      localOp Sum.inl Sum.inl_injective
        (fun _ => qlift (R := R) (phiE en) (D.columnOracle x)) := by
  simp only [prims]

theorem prims_val (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    prims (R := R) D en x Query.value = permOp (valPerm D en x) := by
  simp only [prims]

theorem prims_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X)
    (j : Query) : IsUnitary (prims (R := R) D en x j) := by
  cases j with
  | rowLocation =>
      rw [prims_row]
      exact localOp_isUnitary _ _ (fun _ => qlift_isUnitary (phiE en) (D.row_unitary x))
  | columnLocation =>
      rw [prims_col]
      exact localOp_isUnitary _ _ (fun _ => qlift_isUnitary (phiE en) (D.column_unitary x))
  | value =>
      rw [prims_val]
      exact isUnitary_permOp _

/-- **The compute circuit** of the private operation. -/
def computeV (k b : ℕ) : List (NInstr (BW k b) (PY k b) Query) :=
  [NInstr.call Query.rowLocation false posRR, NInstr.call Query.columnLocation false posRC] ++
    gadget oB false tB dmB rrB [NInstr.call Query.rowLocation false posT] ++
    gadget oB true tB dmB rcB [NInstr.call Query.columnLocation false posT] ++
    [NInstr.call Query.value false posT]

/-- **The native private operation**: the compute circuit, the orientation wire and the decoder
`κ (X + i Y)` of the value wires. -/
def sparseOp (k b : ℕ) (κ : ℝ) : NativeOp Empty (PR k) (SZ k b) (PY k b) Query where
  V := computeV k b
  o := oPR k
  dec := binDec (fun i => vB (Sum.inl i)) (fun i => vB (Sum.inr i)) κ

theorem computeV_valid (k b : ℕ) : ∀ i ∈ computeV k b, i.Valid := by
  have hc : ∀ (j : Query) (pos : PY k b ↪ BW k b),
      ∀ i ∈ [NInstr.call (V := BW k b) j false pos], i.Valid := by
    intro j pos i hi
    rw [List.mem_singleton] at hi
    subst hi
    trivial
  intro i hi
  simp only [computeV, List.mem_append] at hi
  rcases hi with ((h | h) | h) | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> trivial
  · exact gadget_valid _ _ _ _ _ tB_ne_dmB tB_ne_rrB tB_ne_oB dmB_ne_oB _ (hc _ _) i h
  · exact gadget_valid _ _ _ _ _ tB_ne_dmB tB_ne_rcB tB_ne_oB dmB_ne_oB _ (hc _ _) i h
  · exact hc _ _ i h

theorem twos_update {B : Type*} [Fintype B] [DecidableEq B] {m : ℕ} (r : Fin m → B)
    (x : Cfg B) (w : B) (v : Bool) (hw : ∀ i, r i ≠ w) :
    twos r (Function.update x w v) = twos r x := by
  unfold twos
  congr 2
  funext j
  split_ifs with h
  · exact Function.update_of_ne (hw _) _ _
  · rfl

/-- The compute circuit is valid and the decoder does not read the orientation wire. -/
theorem sparseOp_public (k b : ℕ) (κ : ℝ) : (sparseOp k b κ).Public where
  valid := computeV_valid k b
  dec_indep x v := by
    simp only [sparseOp, binDec]
    rw [twos_update _ x (Sum.inl (Sum.inr (oPR k))) v (fun i => vB_ne_oB _),
      twos_update _ x (Sum.inl (Sum.inr (oPR k))) v (fun i => vB_ne_oB _)]

theorem computeV_nGates (k b : ℕ) : nGatesN (computeV k b) = 28 * k := by
  simp only [computeV, nGatesN_append, gadget_nGates, Fintype.card_sum, Fintype.card_fin]
  simp [nGatesN, NInstr.isGate]
  ring

theorem computeV_nCalls (k b : ℕ) (p : Query → Bool) :
    nCallsN p (computeV k b) = 2 * (if p Query.rowLocation then 1 else 0) +
      2 * (if p Query.columnLocation then 1 else 0) + (if p Query.value then 1 else 0) := by
  simp only [computeV, nCallsN_append, gadget_nCalls]
  cases h1 : p Query.rowLocation <;> cases h2 : p Query.columnLocation <;>
    cases h3 : p Query.value <;> simp [nCallsN, NInstr.isCall, h1, h2, h3]

end Prims

/-! ### The compute circuit on clean scratch -/

section Compute

open NativeSparseBlockEncoding (Data Query)

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The all-zero index. -/
def zIdx (en : Cfg (Fin k) ≃ n) : n := en (fun _ => false)

/-- The row reference: the image of the all-zero edge under the row location oracle. -/
def refRow (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (EW k) :=
  (phiE en).symm (zIdx en, D.rowloc x (zIdx en) k0)

/-- The column reference: the image of the all-zero edge under the column location oracle. -/
def refCol (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (EW k) :=
  (phiE en).symm (D.colloc x (zIdx en) k0, zIdx en)

theorem phiE_zero (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) : phiE en (fun _ => false) = (zIdx en, D.slot k0) := by
  rw [hk0]
  rfl

theorem qlift_bas_single {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
    (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (c : Cfg V) (e : ι)
    (h : A (EuclideanSpace.single (φ c) 1) = EuclideanSpace.single e 1) (q : R) :
    qlift φ A (bas c q) = bas (φ.symm e) q := by
  apply PiLp.ext
  intro y
  rw [qlift_bas_apply, h, bas_apply]
  by_cases hy : y = φ.symm e
  · subst hy
    simp
  · have he : φ y ≠ e := fun h' => hy (by rw [← h', Equiv.symm_apply_apply])
    simp [hy, he]

theorem row_zero (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (q : R) :
    qlift (phiE en) (D.rowOracle x) (bas (fun _ => false) q) = bas (refRow D en k0 x) q :=
  qlift_bas_single _ _ _ _ (by rw [phiE_zero D en k0 hk0]; exact D.row_valid x (zIdx en) k0) q

theorem col_zero (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (q : R) :
    qlift (phiE en) (D.columnOracle x) (bas (fun _ => false) q) = bas (refCol D en k0 x) q :=
  qlift_bas_single _ _ _ _ (by rw [phiE_zero D en k0 hk0]; exact D.column_valid x (zIdx en) k0)
    q

/-- A call of a primitive acting on the edge register, placed with the edge register on `T`. -/
theorem eval_call_edge (prim : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R) (j : Query)
    (G : Reg (EW k) R →L[ℂ] Reg (EW k) R)
    (hj : prim j = localOp Sum.inl Sum.inl_injective (fun _ => G))
    (pos : PY k b ↪ BW k b) (T : EW k → BW k b) (hT : Function.Injective T)
    (hpos : ∀ e, pos (Sum.inl e) = T e) :
    (NInstr.call j false pos).eval prim = localOp T hT (fun _ => G) := by
  rw [NInstr.eval_call, hj]
  simp only [GateODE.adjIf, Bool.false_eq_true, if_false]
  exact localOp_localOp' pos.injective Sum.inl_injective T hT (fun e => (hpos e).symm)
    (fun _ _ => G)

/-- An operator on clean exposed wires that writes a basis state. -/
theorem localOp_bas_clean {A W : Type*} [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]
    {ι : A → W} (hι : Function.Injective ι) (G : Reg A R →L[ℂ] Reg A R) (y : Cfg W)
    (hy : ∀ a, y (ι a) = false) (y0 : Cfg A) (hG : ∀ q, G (bas (fun _ => false) q) = bas y0 q)
    (q : R) : localOp ι hι (fun _ => G) (bas y q) = bas (overwrite ι y y0) q := by
  rw [localOp_bas hι, show (fun a => y (ι a)) = fun _ => false from funext hy]
  beta_reduce
  rw [hG, put_bas]

/-- The scratch written by the reference calls. -/
def refCfg (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (SZ k b) :=
  Sum.elim (Sum.elim (Sum.elim (fun _ => false) (refRow D en k0 x)) (refCol D en k0 x))
    (fun _ => false)

/-- The permutation of the reference calls: the references are XOR-ed into their registers. -/
def sigRef (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (BW k b) ≃ Cfg (BW k b) :=
  xorEquiv (fun _ => refCfg D en k0 x)

/-- The two reference calls act on clean scratch as the permutation `sigRef`. -/
theorem refs_cleanEmb (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    nrun (prims (R := R) D en x)
        [NInstr.call Query.rowLocation false posRR, NInstr.call Query.columnLocation false posRC] ∘L
      cleanEmb (X := SZ k b) = permOp (sigRef D en k0 x) ∘L cleanEmb := by
  have hR := eval_call_edge (prims (R := R) D en x) Query.rowLocation _ (prims_row D en x) posRR
    rrB rrB_injective (fun _ => rfl)
  have hC := eval_call_edge (prims (R := R) D en x) Query.columnLocation _ (prims_col D en x)
    posRC rcB rcB_injective (fun _ => rfl)
  apply ext_bas_clm'
  intro c q
  rw [nrun_cons, nrun_cons, nrun_nil, hR, hC]
  simp only [comp_apply, one_apply_eq_self, cleanEmb_bas, permOp_bas]
  rw [localOp_bas_clean rrB_injective _ _ (fun _ => rfl) _ (row_zero D en k0 hk0 x),
    localOp_bas_clean rcB_injective _ _ (fun e => by
      rw [overwrite_apply_out rrB _ _ _ (fun e' => rrB_ne_rcB e' e)]
      rfl) _ (col_zero D en k0 hk0 x)]
  congr 1
  apply bw_ext
  · intro p
    rw [overwrite_apply_out rcB _ _ _ (fun e h => by simp [rcB] at h),
      overwrite_apply_out rrB _ _ _ (fun e h => by simp [rrB] at h)]
    rfl
  · intro e
    rw [overwrite_apply_out rcB _ _ _ (fun e' => (dmB_ne_rcB e e').symm),
      overwrite_apply_out rrB _ _ _ (fun e' => (dmB_ne_rrB e e').symm)]
    simp [sigRef, refCfg, dmB]
  · intro e
    rw [overwrite_apply_out rcB _ _ _ (fun e' => (rrB_ne_rcB e e').symm),
      overwrite_apply_ι rrB_injective]
    simp [sigRef, refCfg, rrB]
  · intro e
    rw [overwrite_apply_ι rcB_injective]
    simp [sigRef, refCfg, rcB]
  · intro v
    rw [overwrite_apply_out rcB _ _ _ (fun e' => (rcB_ne_vB e' v)),
      overwrite_apply_out rrB _ _ _ (fun e' => (rrB_ne_vB e' v))]
    simp [sigRef, refCfg, vB]

/-- Clean dummy register and reference registers holding the references. -/
def RefOK (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (BW k b)) : Prop :=
  (∀ e, y (dmB e) = false) ∧ (∀ e, y (rrB e) = refRow D en k0 x e) ∧
    (∀ e, y (rcB e) = refCol D en k0 x e)

/-- The lifted locator on the base wires: the row or the column location oracle on the index
wires, selected by the orientation wire. -/
def Lfull (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (BW k b) R →L[ℂ] Reg (BW k b) R :=
  localOp tB tB_injective (fun y => if y oB then qlift (phiE en) (D.columnOracle x)
    else qlift (phiE en) (D.rowOracle x))

/-- **The two gadgets** act as the lifted locator on scratch holding the references. -/
theorem gadgets_agree (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    Agrees (RefOK D en k0 x)
      (nrun (prims (R := R) D en x)
        (gadget oB false tB dmB rrB [NInstr.call Query.rowLocation false posT] ++
          gadget oB true tB dmB rcB [NInstr.call Query.columnLocation false posT]))
      (Lfull D en x) := by
  have hcR : nrun (prims (R := R) D en x) [NInstr.call Query.rowLocation false posT] =
      localOp tB tB_injective (fun _ => qlift (phiE en) (D.rowOracle x)) := by
    rw [nrun_singleton]
    exact eval_call_edge _ _ _ (prims_row D en x) posT tB tB_injective (fun _ => rfl)
  have hcC : nrun (prims (R := R) D en x) [NInstr.call Query.columnLocation false posT] =
      localOp tB tB_injective (fun _ => qlift (phiE en) (D.columnOracle x)) := by
    rw [nrun_singleton]
    exact eval_call_edge _ _ _ (prims_col D en x) posT tB tB_injective (fun _ => rfl)
  have h1 := gadget_agrees (prims (R := R) D en x) (qlift (phiE en) (D.rowOracle x))
    (refRow D en k0 x) (row_zero D en k0 hk0 x) oB false tB dmB rrB tB_injective dmB_injective
    tB_ne_dmB tB_ne_rrB dmB_ne_rrB tB_ne_oB dmB_ne_oB _ hcR
  have h2 := gadget_agrees (prims (R := R) D en x) (qlift (phiE en) (D.columnOracle x))
    (refCol D en k0 x) (col_zero D en k0 hk0 x) oB true tB dmB rcB tB_injective dmB_injective
    tB_ne_dmB tB_ne_rcB dmB_ne_rcB tB_ne_oB dmB_ne_oB _ hcC
  have hp : Preserves (RefOK D en k0 x) (localOp tB tB_injective
      (fun y => if y oB = false then qlift (phiE en) (D.rowOracle x) else 1) :
        Reg (BW k b) R →L[ℂ] Reg (BW k b) R) := by
    apply preserves_localOp
    rintro y d ⟨hd, hr, hc⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · rw [overwrite_apply_out tB y d _ (fun e' => tB_ne_dmB e' e)]
      exact hd e
    · rw [overwrite_apply_out tB y d _ (fun e' => tB_ne_rrB e' e)]
      exact hr e
    · rw [overwrite_apply_out tB y d _ (fun e' => tB_ne_rcB e' e)]
      exact hc e
  have h := Agrees.comp (Sim.Agrees.mono h1 (fun y hy => ⟨hy.1, hy.2.1⟩)) hp
    (Sim.Agrees.mono h2 (fun y hy => ⟨hy.1, hy.2.2⟩))
  have hC : (localOp tB tB_injective
      (fun y => if y oB = true then qlift (phiE en) (D.columnOracle x) else 1) :
        Reg (BW k b) R →L[ℂ] Reg (BW k b) R) ∘L localOp tB tB_injective
      (fun y => if y oB = false then qlift (phiE en) (D.rowOracle x) else 1) = Lfull D en x := by
    rw [localOp_comp]
    unfold Lfull
    congr 1
    funext y
    cases y oB <;> simp [Sim.one_comp', Sim.comp_one']
  rw [nrun_append, ← hC]
  exact h

/-- The lifted locator on the private register, without selection wires. -/
def Fq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Reg (Empty ⊕ PR k) R →L[ℂ] Reg (Empty ⊕ PR k) R :=
  liftE (qlift (phiPR en) (FixedLocatorConjugation.locator D x))

theorem Lfull_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    Lfull (R := R) (b := b) D en x = liftB (X := SZ k b) (Fq D en x) := by
  have hρ : Function.Injective (fun e : EW k => (Sum.inr (ixPR k e) : Empty ⊕ PR k)) :=
    Sum.inr_injective.comp (ixPR_injective k)
  have e1 : Fq (R := R) D en x = localOp (fun e : EW k => (Sum.inr (ixPR k e) : Empty ⊕ PR k)) hρ
      (fun z => if z (Sum.inr (oPR k)) then qlift (phiE en) (D.columnOracle x)
        else qlift (phiE en) (D.rowOracle x)) := by
    unfold Fq liftE
    rw [show FixedLocatorConjugation.locator D x =
      FixedLocatorConjugation.block (D.rowOracle x) (D.columnOracle x) from rfl, qlift_block,
      localOp_localOp' Sum.inr_injective (ixPR_injective k) _ hρ (fun _ => rfl)
        (fun _ c => if c (oPR k) then qlift (phiE en) (D.columnOracle x)
          else qlift (phiE en) (D.rowOracle x))]
    apply localOp_congr
    intro z
    rw [clearCfg_apply_out _ _ _ (ixPR_ne_o k)]
  have e2 : (liftB (X := SZ k b) (localOp (fun e : EW k => (Sum.inr (ixPR k e) : Empty ⊕ PR k)) hρ
      (fun z => if z (Sum.inr (oPR k)) then qlift (R := R) (phiE en) (D.columnOracle x)
        else qlift (phiE en) (D.rowOracle x)))) = Lfull D en x := by
    unfold liftB Lfull
    rw [localOp_localOp' Sum.inl_injective hρ tB tB_injective (fun _ => rfl)
      (fun _ z => if z (Sum.inr (oPR k)) then qlift (R := R) (phiE en) (D.columnOracle x)
        else qlift (phiE en) (D.rowOracle x))]
    apply localOp_congr
    intro w
    rw [clearCfg_apply_out _ _ _ (fun e h => ixPR_ne_o k e (Sum.inr_injective h))]
    rfl
  rw [e1, e2]

omit [CompleteSpace R] in
theorem supp_sigRef (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (ψ : Reg (Empty ⊕ PR k) R) :
    Supp (RefOK D en k0 x) (permOp (sigRef D en k0 x) (cleanEmb (X := SZ k b) ψ)) := by
  intro y hy
  rw [permOp_apply]
  apply supp_cleanEmb ψ
  intro hc
  apply hy
  have hy' : y = sigRef D en k0 x ((sigRef D en k0 x).symm y) := (Equiv.apply_symm_apply _ y).symm
  generalize (sigRef D en k0 x).symm y = z at hc hy'
  subst hy'
  have hz : ∀ w, z (Sum.inr w) = false := hc
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    simp [sigRef, refCfg, dmB, rrB, rcB, hz]

/-- The permutation written by the compute circuit: the references and the stored entry of
the located edge. -/
def sigma (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (BW k b) ≃ Cfg (BW k b) :=
  (sigRef D en k0 x).trans (alongEquiv posT (valPerm D en x))

/-- **The compute circuit on clean scratch** is the lifted locator followed by a permutation of
basis configurations. -/
theorem compute_cleanEmb (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    nrun (prims (R := R) D en x) (computeV k b) ∘L cleanEmb (X := SZ k b) =
      permOp (sigma D en k0 x) ∘L cleanEmb ∘L Fq D en x := by
  have hV : computeV k b =
      [NInstr.call Query.rowLocation false posRR, NInstr.call Query.columnLocation false posRC] ++
        (gadget oB false tB dmB rrB [NInstr.call Query.rowLocation false posT] ++
          gadget oB true tB dmB rcB [NInstr.call Query.columnLocation false posT]) ++
        [NInstr.call Query.value false posT] := by
    simp only [computeV, List.append_assoc]
  have hval : nrun (prims (R := R) D en x) [NInstr.call Query.value false posT] =
      permOp (alongEquiv posT (valPerm D en x)) := by
    rw [nrun_singleton, NInstr.eval_call, prims_val]
    simp only [GateODE.adjIf, Bool.false_eq_true, if_false]
    exact localOp_permOp posT (valPerm D en x)
  have hrefs := refs_cleanEmb (R := R) D en k0 hk0 x
  have hgad := gadgets_agree (R := R) D en k0 hk0 x
  have hcomm : liftB (X := SZ k b) (Fq (R := R) D en x) ∘L permOp (sigRef D en k0 x) =
      permOp (sigRef D en k0 x) ∘L liftB (Fq D en x) :=
    liftB_comm_xor (Fq (R := R) D en x) (refCfg D en k0 x)
  have hlc := liftB_cleanEmb (X := SZ k b) (Fq (R := R) D en x)
  apply ContinuousLinearMap.ext
  intro ψ
  have h1 : nrun (prims (R := R) D en x)
      [NInstr.call Query.rowLocation false posRR, NInstr.call Query.columnLocation false posRC]
        (cleanEmb ψ) = permOp (sigRef D en k0 x) (cleanEmb ψ) := by
    rw [← comp_apply (nrun (prims (R := R) D en x) [NInstr.call Query.rowLocation false posRR,
      NInstr.call Query.columnLocation false posRC]) (cleanEmb (X := SZ k b)) ψ, hrefs,
      comp_apply]
  have h2 : liftB (X := SZ k b) (Fq D en x) (permOp (sigRef D en k0 x) (cleanEmb ψ)) =
      permOp (sigRef D en k0 x) (cleanEmb (Fq D en x ψ)) := by
    rw [← comp_apply (liftB (X := SZ k b) (Fq (R := R) D en x)) (permOp (sigRef D en k0 x)), hcomm,
      comp_apply, ← comp_apply (liftB (X := SZ k b) (Fq (R := R) D en x)) cleanEmb, hlc,
      comp_apply]
  rw [hV, nrun_append, nrun_append, comp_apply, comp_apply, comp_apply, h1,
    hgad _ (supp_sigRef D en k0 x ψ), Lfull_eq, h2, hval]
  rfl

/-! ### The decoded rotation -/

/-- An enabled one-qubit operation without selection wires. -/
theorem liftE_condOp {W : Type*} [Fintype W] [DecidableEq W] (t : W)
    (u : Cfg W → Matrix Bool Bool ℂ) :
    liftE (condOp (Q := R) t u) = condOp (Sum.inr t) (fun z => u (fun w => z (Sum.inr w))) := by
  unfold liftE condOp
  rw [localOp_localOp' Sum.inr_injective (single_injective t) (fun _ => Sum.inr t)
    (single_injective _) (fun _ => rfl) (fun _ c => matOp (qubitMat (u c)))]
  apply localOp_congr
  intro z
  simp only [clearCfg_single, update_comp_injective Sum.inr_injective, Function.update_idem]

/-- The rescaled entry `γ √s H_e` of the edge `e` held by a configuration of the private
register. -/
def edgeVal (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ)
    (c : Cfg (PR k)) : ℂ :=
  ((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) *
    D.matrix x (phiE en (fun e => c (ixPR k e))).1 (phiE en (fun e => c (ixPR k e))).2

/-- The lifted edge action on the private register, without selection wires. -/
def Aq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    Reg (Empty ⊕ PR k) R →L[ℂ] Reg (Empty ⊕ PR k) R :=
  liftE (qlift (phiPR en) (OrientedEdgeCayley.action (D.matrix x) s γ))

theorem Aq_eq (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) (γ : ℝ) :
    Aq (R := R) D en x γ = condOp (Sum.inr (oPR k))
      (fun z => edgeMat (edgeVal D en x γ (fun w => z (Sum.inr w)))) := by
  unfold Aq
  rw [show OrientedEdgeCayley.action (D.matrix x) s γ = OrientedEdgeCayley.lift (fun e =>
      ExactEdgeCayley.action (((γ * Real.sqrt (s : ℝ) : ℝ) : ℂ) * D.matrix x e.1 e.2)) from rfl,
    qlift_lift, liftE_condOp]
  simp only [qmat_action]
  rfl

theorem posT_ne_oB (a : PY k b) : posT a ≠ oB := by
  rcases a with e | v
  · exact tB_ne_oB e
  · exact vB_ne_oB v

theorem sigma_oB (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (BW k b)) : sigma D en k0 x y oB = y oB := by
  rw [sigma, Equiv.trans_apply, alongEquiv_apply_out posT _ _ oB posT_ne_oB]
  rfl

theorem sigma_update_oB (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (x : X) (y : Cfg (BW k b)) (v : Bool) :
    sigma D en k0 x (Function.update y oB v) = Function.update (sigma D en k0 x y) oB v := by
  have h1 : sigRef D en k0 x (Function.update y oB v) =
      Function.update (sigRef D en k0 x y) oB v :=
    xorEquiv_update_inl _ y (Sum.inr (oPR k)) v
  rw [sigma, Equiv.trans_apply, Equiv.trans_apply, h1,
    alongEquiv_update_out posT _ _ oB v posT_ne_oB]

theorem sigma_val (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (Empty ⊕ PR k)) (w : VW b) :
    sigma D en k0 x (Sum.elim c (fun _ => false)) (vB w) =
      D.table x (phiE en (fun e => c (Sum.inr (ixPR k e)))) w := by
  rw [sigma, Equiv.trans_apply, show (vB w : BW k b) = posT (Sum.inr w) from rfl,
    alongEquiv_apply_in]
  simp [valPerm, posT, sigRef, refCfg, tB, vB]

/-- **The decoded rotation** of the private operation commutes past the permutation of the
compute circuit into the lifted edge action. -/
theorem rdec_sigma (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (γ c0 : ℝ) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) :
    Rdec (R := R) (sparseOp k b (γ * Real.sqrt s * c0)) ∘L permOp (sigma D en k0 x) ∘L
        cleanEmb (X := SZ k b) =
      permOp (sigma D en k0 x) ∘L cleanEmb ∘L Aq D en x γ := by
  have hR : Rdec (R := R) (sparseOp k b (γ * Real.sqrt s * c0)) = condOp oB (fun y => edgeMat
      (binDec (fun i => vB (Sum.inl i)) (fun i => vB (Sum.inr i)) (γ * Real.sqrt s * c0) y)) :=
    rfl
  have hdi := (sparseOp_public k b (γ * Real.sqrt s * c0)).dec_indep
  apply ext_bas_clm'
  intro c q
  rw [comp_apply, comp_apply, comp_apply, comp_apply, cleanEmb_bas, permOp_bas, hR, condOp_bas,
    Aq_eq, condOp_bas, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul, map_smul, cleanEmb_bas, permOp_bas]
  have hcfg : (Sum.elim (Function.update c (Sum.inr (oPR k)) v) (fun _ => false) : Cfg (BW k b)) =
      Function.update (Sum.elim c (fun _ => false)) oB v := by
    funext w
    rcases w with p | z
    · by_cases hp : p = Sum.inr (oPR k)
      · subst hp
        simp [oB]
      · have hne : (Sum.inl p : BW k b) ≠ oB := fun h => hp (Sum.inl_injective h)
        rw [Function.update_of_ne hne]
        simp [Function.update_of_ne hp]
    · have hne : (Sum.inr z : BW k b) ≠ oB := fun h => by cases h
      rw [Function.update_of_ne hne]
      rfl
  rw [hcfg, sigma_update_oB, sigma_oB]
  congr 2
  -- the entries agree
  have hix : (fun e => (fun w => Function.update c (Sum.inr (oPR k)) false (Sum.inr w))
      (ixPR k e)) = fun e => c (Sum.inr (ixPR k e)) := by
    funext e
    exact Function.update_of_ne (fun h => ixPR_ne_o k e (Sum.inr_injective h)) _ _
  have hval : (fun w => sigma D en k0 x (Sum.elim c (fun _ => false)) (vB w)) =
      D.table x (phiE en (fun e => c (Sum.inr (ixPR k e)))) := by
    funext w
    exact sigma_val D en k0 x c w
  have hdec' : binDec (fun i => vB (Sum.inl i)) (fun i => vB (Sum.inr i)) (γ * Real.sqrt s * c0)
      (sigma D en k0 x (Sum.elim c (fun _ => false))) =
      ((γ * Real.sqrt s * c0 : ℝ) : ℂ) *
        gauss (D.table x (phiE en (fun e => c (Sum.inr (ixPR k e))))) := by
    rw [← hval]
    rfl
  have hent := D.decoded x (phiE en (fun e => c (Sum.inr (ixPR k e)))).1
    (phiE en (fun e => c (Sum.inr (ixPR k e)))).2
  rw [hdec, Prod.mk.eta] at hent
  have hu := hdi (sigma D en k0 x (Sum.elim c (fun _ => false))) false
  change binDec _ _ _ (Function.update (sigma D en k0 x (Sum.elim c (fun _ => false))) oB false) =
    binDec _ _ _ (sigma D en k0 x (Sum.elim c (fun _ => false))) at hu
  unfold edgeVal
  rw [hu, hdec', hix, ← hent]
  push_cast
  ring

end Compute

end

end SparseHamiltonian.GateBinary
