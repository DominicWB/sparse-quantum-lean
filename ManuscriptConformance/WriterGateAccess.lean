import GeneralSparseAccess.ImplOK
import GeneralSparseAccess.ImplE

/-!
# Gate-level value access by a writer on valid clean inputs (handover item B4)

Section `hs:sec:control` lets the value oracle be any reversible writer of the stored word into a
clean target register, with its supplied inverse; XOR-writing is an example. The gate theorems of
general size (`GeneralSparseAccess.QData`) take the XOR-writing value oracle `QData.prims` on every
pair of `k`-bit index words. Here the value oracle is replaced by a **writer** `W` on the qubit
register `PY k b` (the edge register and the value wires) that is specified only on the valid clean
inputs:

  `W |i, j, 0⟩ = c_{ij} |i, j, w_{ij}⟩`  for `i, j < N`, with any phases `c_{ij}`,

(`QData.Writer`, the stored word `w_{ij}` of the data), and is otherwise an arbitrary unitary:
on an invalid pair of index words, or on a dirty target, its action is unconstrained. Its inverse is
its literal adjoint (an inverse call of the gate model).

The padded value oracle of the general-size gate theorems already writes the stored word into a
clean scratch register, copies it into the value wires on a valid pair (the public zero word
otherwise) and uncomputes it (`GeneralSparseAccess.implVal`, two calls). With the writer, the first
call is the writer and the second its inverse (`implValW`): the same gates and the same number of
calls, so the general-size gate theorems keep their bounds (`implPW`, with the locator
implementations of `implP` unchanged):

* on a valid pair the writer puts `c_{ij}` times the amplitude on the stored word in the scratch
  register, the copy is that of the XOR oracle, and the inverse call returns the scratch register
  to its clean word with the phase `c̄_{ij}`: the phases cancel (`wmid_valid`);
* on an invalid pair the copy is masked by the validity flag, which the writer does not touch: the
  value wires receive the public zero word whatever the writer did on its wires, and the inverse
  call undoes the writer exactly (`wmid_invalid`). No controlled access to the writer is assumed,
  and no routing of invalid index words is needed, since the writer acts unitarily on the full
  register and its inverse is its literal adjoint.

`implValW_clean`, `implOKW`: on clean ancillas each implementation acts as the padded primitive, for
every unitary action of the writer outside its valid clean inputs and of the locators outside their
valid list inputs; `kindOK_implPW`, `nGatesN_implPW_le`: at most three calls of the corresponding
primitive and `implG k b` elementary gates, as for `implP`.

For a general decoder, which need not have a zero word, the released padded data with a validity
decoder (`QData.padDataE`) store the supplied word of the low index words on every pair, which a
writer specified on valid pairs only cannot supply. `QData.padDataEW` is `padDataE` with the masked
table (the stored word on a valid pair, the all-zero word otherwise): the validity decoder ignores
the word of an invalid pair, so its matrix, decoder, slots and locators are those of `padDataE`
(`padDataEW_matrix`, `padDataEW_decode`), and `implOKEW`: the writer implementations with the
all-zero word act on clean ancillas as its primitives.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateODE (put put_apply overwrite_apply_ι overwrite_apply_out adjIf
  localOp_put)
open SparseHamiltonian.GatePointerEncoding (wordValue)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct
open IW

/-! ### The writer -/

namespace QData

variable {X : Type*} {N s k b : ℕ}

/-- **A writer of the stored words on valid clean inputs** (Section `hs:sec:control`; handover item
B4): a unitary on the edge register and the value wires that maps the clean input of every valid
pair `i, j < N` to the stored word of the pair, `W|i, j, 0⟩ = c_{ij}|i, j, w_{ij}⟩`, with any phases
`c_{ij}`. Its action on an invalid pair of index words and on a dirty target is arbitrary. -/
structure Writer (D : QData X N s k b) where
  /-- The writer on every instance. -/
  op : X → EuclideanSpace ℂ (Cfg (PY k b)) →L[ℂ] EuclideanSpace ℂ (Cfg (PY k b))
  /-- The phases of the written words. -/
  phase : X → Fin N → Fin N → ℂ
  unitary : ∀ x, IsUnitary (op x)
  write : ∀ x (i j : Fin N),
    op x (EuclideanSpace.single (Sum.elim (edgeW k (binW k i) (binW k j)) (fun _ => false)) 1) =
      phase x i j • EuclideanSpace.single
        (Sum.elim (edgeW k (binW k i) (binW k j)) (D.table x (edgeW k (binW k i) (binW k j)))) 1

namespace Writer

variable {D : QData X N s k b} (Wr : D.Writer)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The primitive oracles of the writer model** on the register `PY k b`: the supplied row and
column locators, and the writer in the place of the value oracle. -/
def prims (x : X) : Query → Reg (PY k b) R →L[ℂ] Reg (PY k b) R
  | .rowLocation => D.prims x Query.rowLocation
  | .columnLocation => D.prims x Query.columnLocation
  | .value => qlift (Equiv.refl (Cfg (PY k b))) (Wr.op x)

theorem prims_row (x : X) :
    Wr.prims (R := R) x Query.rowLocation = localOp Sum.inl Sum.inl_injective
      (fun _ => qlift (R := R) (Equiv.refl (Cfg (EW k))) (D.rowOracle x)) := by
  simp only [prims]
  exact D.prims_row x

theorem prims_col (x : X) :
    Wr.prims (R := R) x Query.columnLocation = localOp Sum.inl Sum.inl_injective
      (fun _ => qlift (R := R) (Equiv.refl (Cfg (EW k))) (D.columnOracle x)) := by
  simp only [prims]
  exact D.prims_col x

theorem prims_value (x : X) :
    Wr.prims (R := R) x Query.value = qlift (Equiv.refl (Cfg (PY k b))) (Wr.op x) := rfl

theorem prims_isUnitary (x : X) (j : Query) : IsUnitary (Wr.prims (R := R) x j) := by
  cases j with
  | rowLocation => exact D.prims_isUnitary x Query.rowLocation
  | columnLocation => exact D.prims_isUnitary x Query.columnLocation
  | value => exact qlift_isUnitary _ (Wr.unitary x)

theorem adjoint_comp_self (x : X) : (Wr.op x)† ∘L Wr.op x = 1 := by
  have h := (Wr.unitary x).1
  rwa [star_eq_adjoint, mul_def] at h

/-- The phases of a writer have modulus one. -/
theorem norm_phase (x : X) (i j : Fin N) : ‖Wr.phase x i j‖ = 1 := by
  have h := ((Wr.op x).norm_map_iff_adjoint_comp_self.mpr (Wr.adjoint_comp_self x))
    (EuclideanSpace.single (Sum.elim (edgeW k (binW k i) (binW k j)) (fun _ => false)) 1)
  rw [Wr.write, norm_smul] at h
  simpa using h

/-- **The inverse writer on a written word**: the clean input with the conjugate phase. -/
theorem adjoint_write (x : X) (i j : Fin N) :
    ((Wr.op x)†) (EuclideanSpace.single
        (Sum.elim (edgeW k (binW k i) (binW k j)) (D.table x (edgeW k (binW k i) (binW k j)))) 1) =
      (starRingEnd ℂ) (Wr.phase x i j) •
        EuclideanSpace.single (Sum.elim (edgeW k (binW k i) (binW k j)) (fun _ => false)) 1 := by
  set c := Wr.phase x i j with hc
  have h1 : ((Wr.op x)†) (Wr.op x (EuclideanSpace.single
      (Sum.elim (edgeW k (binW k i) (binW k j)) (fun _ => false)) 1)) =
      EuclideanSpace.single (Sum.elim (edgeW k (binW k i) (binW k j)) (fun _ => false)) 1 := by
    rw [← comp_apply, Wr.adjoint_comp_self, one_apply_eq_self]
  rw [Wr.write, map_smul, ← hc] at h1
  have hcc : (starRingEnd ℂ) c * c = 1 := by
    rw [Complex.conj_mul', hc, Wr.norm_phase]
    norm_num
  calc ((Wr.op x)†) (EuclideanSpace.single
        (Sum.elim (edgeW k (binW k i) (binW k j)) (D.table x (edgeW k (binW k i) (binW k j)))) 1)
      = ((starRingEnd ℂ) c * c) • ((Wr.op x)†) (EuclideanSpace.single
        (Sum.elim (edgeW k (binW k i) (binW k j)) (D.table x (edgeW k (binW k i) (binW k j)))) 1) :=
        by rw [hcc, one_smul]
    _ = _ := by rw [mul_smul, h1]

end Writer

end QData

/-! ### The basis action of a lifted operator -/

section Lift

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The lift of an operator mapping a basis vector to a multiple of a basis vector. -/
theorem qlift_refl_bas (A : EuclideanSpace ℂ (Cfg V) →L[ℂ] EuclideanSpace ℂ (Cfg V))
    (d d' : Cfg V) (c : ℂ) (h : A (EuclideanSpace.single d 1) = c • EuclideanSpace.single d' 1)
    (q : R) : qlift (Equiv.refl (Cfg V)) A (bas d q) = bas d' (c • q) := by
  apply PiLp.ext
  intro y
  rw [qlift_bas_apply, Equiv.refl_apply, Equiv.refl_apply, h, bas_apply]
  by_cases hy : y = d'
  · subst hy
    simp
  · simp [hy]

end Lift

/-! ### The implementation of the padded value oracle from the writer -/

section WriterValue

variable {X : Type*} {N s k b : ℕ} {D : QData X N s k b} (Wr : D.Writer)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The implementation of the padded value oracle from the writer**: the validity flag, the
writer on the low edge wires and the clean scratch register, the copy of the scratch word on a
valid pair (of the public zero word `z₀` otherwise), the inverse writer, and the uncomputation of
the flag. The gates are those of `implVal`. -/
def implValW (N : ℕ) (z₀ : Cfg (VW b)) : List (NInstr (IW k b) (PY k b) Query) :=
  nGatesOf (vflagC N) ++ [NInstr.call Query.value false posV] ++ nGatesOf (copyC z₀) ++
    [NInstr.call Query.value true posV] ++ nGatesOf (vflagC N).reverse

theorem posV_ne_v (a : PY k b) (w : VW b) : (posV a : IW k b) ≠ v w := by
  rcases a with a | a
  · change tl a ≠ v w
    simp [tl, e, v]
  · exact sc_ne_v a w

theorem posV_ne_g₂ (a : PY k b) : (posV a : IW k b) ≠ g₂ := by
  rcases a with a | a
  · change tl a ≠ g₂
    simp [tl, e, g₂]
  · change sc a ≠ g₂
    simp [sc, g₂]

theorem tl_ne_sc (a : EW k) (w : VW b) : (tl a : IW k b) ≠ sc w := by
  simp [tl, e, sc]

/-- A call of the writer, or of its inverse, on a basis vector. -/
theorem nrun_wCall (x : X) (adj : Bool) (z : Cfg (IW k b)) (q : R) :
    nrun (Wr.prims (R := R) x) [NInstr.call Query.value adj posV] (bas z q) =
      put posV posV.injective z (adjIf adj (qlift (Equiv.refl _) (Wr.op x))
        (bas (fun a => z (posV a)) q)) := by
  rw [nrun_singleton, NInstr.eval_call, localOp_bas]
  rfl

/-- The copy of the stored word leaves every wire other than the value wires unchanged. -/
theorem cfgRun_copyC_out (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (u : IW k b) (hu : ∀ w, u ≠ v w) :
    cfgRun (copyC z₀) z u = z u :=
  (cfgRun_copyList z₀ ((Finset.univ : Finset (VW b)).toList) (Finset.nodup_toList _) z).2 u
    (fun w _ => hu w)

theorem cfgRun_copyC_v (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (w : VW b) :
    cfgRun (copyC z₀) z (v w) = (z (v w) ^^ copyBit z₀ z w) :=
  (cfgRun_copyList z₀ ((Finset.univ : Finset (VW b)).toList) (Finset.nodup_toList _) z).1 w
    (Finset.mem_toList.mpr (Finset.mem_univ w))

theorem copyBit_of_false (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (w : VW b) (hg : z g₂ = false) :
    copyBit z₀ z w = z₀ w := by
  unfold copyBit
  rw [hg]
  simp

/-- **On an invalid pair the copy does not read the writer's wires**: with the flag clear, the copy
commutes with overwriting the wires of a writer call. -/
theorem cfgRun_copyC_overwrite (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (hg : z g₂ = false)
    (d : Cfg (PY k b)) :
    cfgRun (copyC z₀) (overwrite posV z d) = overwrite posV (cfgRun (copyC z₀) z) d := by
  have hg' : overwrite posV z d g₂ = false := by
    rw [overwrite_apply_out posV z d g₂ posV_ne_g₂]
    exact hg
  funext u
  by_cases hu : ∃ a, posV a = u
  · obtain ⟨a, rfl⟩ := hu
    rw [cfgRun_copyC_out z₀ _ _ (fun w => posV_ne_v a w), overwrite_apply_ι posV.injective,
      overwrite_apply_ι posV.injective]
  · have hu' : ∀ a, posV a ≠ u := fun a h => hu ⟨a, h⟩
    rw [overwrite_apply_out posV _ d u hu']
    by_cases hv : ∃ w, v w = u
    · obtain ⟨w, rfl⟩ := hv
      rw [cfgRun_copyC_v, cfgRun_copyC_v, copyBit_of_false z₀ _ w hg',
        copyBit_of_false z₀ _ w hg, overwrite_apply_out posV z d _ hu']
    · have hv' : ∀ w, u ≠ v w := fun w h => hv ⟨w, h.symm⟩
      rw [cfgRun_copyC_out z₀ _ _ hv', cfgRun_copyC_out z₀ _ _ hv',
        overwrite_apply_out posV z d u hu']

/-- The copy on a vector placed on the wires of a writer call, with the flag clear. -/
theorem gRun_copyC_put (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (hg : z g₂ = false)
    (φ : Reg (PY k b) R) :
    gRun (copyC z₀) (put posV posV.injective z φ) =
      put posV posV.injective (cfgRun (copyC z₀) z) φ := by
  rw [put_eq_sum_bas, put_eq_sum_bas, map_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [gRun_classical_bas _ (classical_copyC z₀), cfgRun_copyC_overwrite z₀ z hg d]

/-- The XOR oracle twice around the copy, with the flag clear, is the copy. -/
theorem valMap_copyC_valMap (x : X) (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (hg : z g₂ = false) :
    valMap D x (cfgRun (copyC z₀) (valMap D x z)) = cfgRun (copyC z₀) z := by
  have hvg : valMap D x z g₂ = false := by
    rw [valMap_out D x z g₂ (fun w => by simp [sc, g₂])]
    exact hg
  funext u
  by_cases hs : ∃ w, sc w = u
  · obtain ⟨w, rfl⟩ := hs
    have htl : (fun a => cfgRun (copyC z₀) (valMap D x z) (tl a)) = fun a => z (tl a) := by
      funext a
      rw [cfgRun_copyC_out z₀ _ _ (fun w' => by simp [tl, e, v]),
        valMap_out D x z _ (fun w' => (tl_ne_sc a w').symm)]
    rw [valMap_sc, htl, cfgRun_copyC_out z₀ _ _ (fun w' => sc_ne_v w w'), valMap_sc,
      cfgRun_copyC_out z₀ _ _ (fun w' => sc_ne_v w w'), Bool.xor_assoc, Bool.xor_self,
      Bool.xor_false]
  · have hs' : ∀ w, sc w ≠ u := fun w h => hs ⟨w, h⟩
    rw [valMap_out D x _ u hs']
    by_cases hv : ∃ w, v w = u
    · obtain ⟨w, rfl⟩ := hv
      rw [cfgRun_copyC_v, cfgRun_copyC_v, copyBit_of_false z₀ _ w hvg, copyBit_of_false z₀ _ w hg,
        valMap_out D x z _ hs']
    · have hv' : ∀ w, u ≠ v w := fun w h => hv ⟨w, h.symm⟩
      rw [cfgRun_copyC_out z₀ _ _ hv', cfgRun_copyC_out z₀ _ _ hv', valMap_out D x z u hs']

/-- **The writer, the copy and the inverse writer on an invalid pair**: with the flag clear, the
inverse call undoes the writer whatever it did, and the result is that of the XOR oracle. -/
theorem wmid_invalid (x : X) (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (q : R) (hg : z g₂ = false) :
    nrun (Wr.prims (R := R) x) [NInstr.call Query.value true posV]
        (gRun (copyC z₀) (nrun (Wr.prims (R := R) x) [NInstr.call Query.value false posV]
          (bas z q))) =
      bas (valMap D x (cfgRun (copyC z₀) (valMap D x z))) q := by
  set U := qlift (R := R) (Equiv.refl (Cfg (PY k b))) (Wr.op x) with hU
  have hUu : U† ∘L U = 1 := by
    have h := (qlift_isUnitary (R := R) (Equiv.refl (Cfg (PY k b))) (Wr.unitary x)).1
    rwa [star_eq_adjoint, mul_def] at h
  have hloc : (fun a => cfgRun (copyC z₀) z (posV a)) = fun a => z (posV a) :=
    funext fun a => cfgRun_copyC_out z₀ z _ (fun w => posV_ne_v a w)
  rw [nrun_wCall, gRun_copyC_put z₀ z hg, nrun_singleton, NInstr.eval_call, localOp_put]
  change put posV posV.injective (cfgRun (copyC z₀) z) ((U†) (U (bas (fun a => z (posV a)) q))) = _
  rw [← comp_apply (U†) U, hUu, one_apply_eq_self, put_bas, ← hloc,
    overwrite_self posV.injective, valMap_copyC_valMap x z₀ z hg]

/-- **The writer, the copy and the inverse writer on a valid pair**: the writer puts the phase
times the amplitude on the stored word in the clean scratch register, the copy is that of the XOR
oracle, and the inverse writer returns the scratch register to its clean word with the conjugate
phase. -/
theorem wmid_valid (x : X) (z₀ : Cfg (VW b)) (z : Cfg (IW k b)) (q : R) (i j : Fin N)
    (hsc : ∀ w, z (sc w) = false) (had : (fun a => z (tl a)) = edgeW k (binW k i) (binW k j)) :
    nrun (Wr.prims (R := R) x) [NInstr.call Query.value true posV]
        (gRun (copyC z₀) (nrun (Wr.prims (R := R) x) [NInstr.call Query.value false posV]
          (bas z q))) =
      bas (valMap D x (cfgRun (copyC z₀) (valMap D x z))) q := by
  have hloc : (fun a => z (posV a)) =
      Sum.elim (edgeW k (binW k i) (binW k j)) (fun _ => false) := by
    funext a
    rcases a with a | w
    · exact congrFun had a
    · exact hsc w
  have hx1 : overwrite posV z (Sum.elim (edgeW k (binW k i) (binW k j))
      (D.table x (edgeW k (binW k i) (binW k j)))) = valMap D x z := by
    change _ = overwrite posV z (xorEquiv (fun d => D.table x d) (fun a => z (posV a)))
    rw [hloc]
    congr 1
    funext a
    rcases a with a | w <;> simp [xorEquiv]
  have hloc3 : (fun a => cfgRun (copyC z₀) (valMap D x z) (posV a)) =
      Sum.elim (edgeW k (binW k i) (binW k j)) (D.table x (edgeW k (binW k i) (binW k j))) := by
    funext a
    rcases a with a | w
    · change cfgRun (copyC z₀) (valMap D x z) (tl a) = edgeW k (binW k i) (binW k j) a
      rw [cfgRun_copyC_out z₀ _ _ (fun w' => by simp [tl, e, v]),
        valMap_out D x z _ (fun w' => (tl_ne_sc a w').symm)]
      exact congrFun had a
    · change cfgRun (copyC z₀) (valMap D x z) (sc w) = D.table x (edgeW k (binW k i) (binW k j)) w
      rw [cfgRun_copyC_out z₀ _ _ (fun w' => sc_ne_v w w'), valMap_sc, hsc, had, Bool.false_xor]
  have hx3 : overwrite posV (cfgRun (copyC z₀) (valMap D x z))
      (Sum.elim (edgeW k (binW k i) (binW k j)) (fun _ => false)) =
      valMap D x (cfgRun (copyC z₀) (valMap D x z)) := by
    change _ = overwrite posV (cfgRun (copyC z₀) (valMap D x z))
      (xorEquiv (fun d => D.table x d) (fun a => cfgRun (copyC z₀) (valMap D x z) (posV a)))
    rw [hloc3]
    congr 1
    funext a
    rcases a with a | w <;> simp [xorEquiv]
  have hcc : (starRingEnd ℂ) (Wr.phase x i j) * Wr.phase x i j = 1 := by
    rw [Complex.conj_mul', Wr.norm_phase]
    norm_num
  rw [nrun_wCall, hloc]
  rw [show adjIf false (qlift (R := R) (Equiv.refl (Cfg (PY k b))) (Wr.op x)) =
    qlift (Equiv.refl (Cfg (PY k b))) (Wr.op x) from rfl]
  rw [qlift_refl_bas _ _ _ _ (Wr.write x i j), put_bas, hx1,
    gRun_classical_bas _ (classical_copyC z₀), nrun_wCall, hloc3]
  rw [show adjIf true (qlift (R := R) (Equiv.refl (Cfg (PY k b))) (Wr.op x)) =
    (qlift (Equiv.refl (Cfg (PY k b))) (Wr.op x))† from rfl]
  rw [← qlift_adjoint, qlift_refl_bas _ _ _ _ (Wr.adjoint_write x i j), put_bas, hx3, smul_smul,
    hcc, one_smul]

/-- **The writer implementation on clean basis inputs** acts as the implementation from the XOR
oracle. -/
theorem implValW_bas (hN : N < 2 ^ (k + 1)) (z₀ : Cfg (VW b)) (x : X) (y : Cfg (PY (k + 1) b))
    (q : R) :
    nrun (Wr.prims (R := R) x) (implValW N z₀) (bas (Sum.elim y (fun _ => false)) q) =
      nrun (D.prims (R := R) x) (implVal N z₀) (bas (Sum.elim y (fun _ => false)) q) := by
  unfold implValW implVal
  simp only [nrun_append, comp_apply, nrun_nGatesOf]
  rw [gRun_classical_bas _ (classical_vflagC N)]
  set z : Cfg (IW k b) := Sum.elim y (fun _ => false) with hz
  set z1 := cfgRun (vflagC N) z with hz1
  obtain ⟨hg2, hout⟩ := cfgRun_vflagC (k := k) (b := b) hN z (fun j => rfl) (fun j => rfl) rfl rfl
  rw [← hz1] at hg2 hout
  have hz1sc : ∀ w, z1 (sc w) = false := fun w => by
    rw [hout _ (fun j => by simp [bA, sc]) (fun j => by simp [bB, sc]) (by simp [g₁, sc])
      (by simp [g₂, sc])]
    rfl
  have hz1tl : ∀ a, z1 (tl a) = z (tl a) := fun a =>
    hout _ (fun j => by simp [bA, tl, e]) (fun j => by simp [bB, tl, e]) (by simp [g₁, tl, e])
      (by simp [g₂, tl, e])
  rw [nrun_valCall, gRun_classical_bas _ (classical_copyC z₀), nrun_valCall]
  congr 1
  by_cases hv : z1 g₂ = true
  · have hvp : vpair N z = true := by rw [← hg2]; exact hv
    unfold vpair at hvp
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hvp
    obtain ⟨⟨⟨-, h1⟩, -⟩, h2⟩ := hvp
    have had : (fun a => z1 (tl a)) =
        edgeW k (binW k (⟨_, h1⟩ : Fin N)) (binW k (⟨_, h2⟩ : Fin N)) := by
      funext a
      rw [hz1tl]
      rcases a with a | a
      · change z (xA a) = binW k (wordValue (fun i => z (xA i))) a
        rw [binW_wordValue]
      · change z (xB a) = binW k (wordValue (fun i => z (xB i))) a
        rw [binW_wordValue]
    have := wmid_valid Wr x z₀ z1 q ⟨_, h1⟩ ⟨_, h2⟩ hz1sc had
    rw [this]
  · rw [Bool.not_eq_true] at hv
    rw [wmid_invalid Wr x z₀ z1 q hv]

/-- **The padded value oracle from the writer on clean ancillas**: the XOR of the padded stored
word, for every action of the writer outside its valid clean inputs. -/
theorem implValW_clean (hN : N < 2 ^ (k + 1)) (z₀ : Cfg (VW b)) (x : X) :
    nrun (Wr.prims (R := R) x) (implValW N z₀) ∘L cleanEmb (X := AW k b) =
      cleanEmb ∘L permOp (xorEquiv (fun d => D.ptable z₀ x (phiE (Equiv.refl _) d))) := by
  rw [← implVal_clean D hN z₀ x]
  apply ext_bas_clm'
  intro y q
  rw [comp_apply, comp_apply, cleanEmb_bas]
  exact implValW_bas Wr hN z₀ x y q

end WriterValue

/-! ### The implementations of the padded primitives from the writer -/

section WriterImpl

variable {k b : ℕ}

/-- **The implementations of the padded primitives in the writer model**: the padded locators of
`implP`, and the padded value oracle from the writer (`implValW`). -/
def implPW (N s : ℕ) (z₀ : Cfg (VW b)) : Query → List (NInstr (IW k b) (PY k b) Query)
  | .rowLocation => implLoc N s Query.rowLocation
  | .columnLocation => implLoc N s Query.columnLocation ++ nGatesOf (swapRegs k b)
  | .value => implValW N z₀

theorem valid_implValW (N : ℕ) (z₀ : Cfg (VW b)) : ∀ i ∈ implValW (k := k) N z₀, i.Valid := by
  intro i hi
  unfold implValW at hi
  simp only [List.mem_append, List.mem_singleton] at hi
  rcases hi with (((h | h) | h) | h) | h
  · exact valid_nGatesOf _ (gateOK_vflagC N) i h
  · subst h
    trivial
  · exact valid_nGatesOf _ (gateOK_copyC z₀) i h
  · subst h
    trivial
  · exact valid_nGatesOf _ (fun g hg => gateOK_vflagC N g (List.mem_reverse.mp hg)) i h

/-- **The implementations are valid circuits.** -/
theorem valid_implPW (N s : ℕ) (z₀ : Cfg (VW b)) :
    ∀ j, ∀ i ∈ implPW (k := k) (b := b) N s z₀ j, i.Valid := by
  intro j
  cases j with
  | rowLocation => exact valid_implLoc N s _
  | columnLocation =>
      intro i hi
      rcases List.mem_append.mp hi with h | h
      · exact valid_implLoc N s _ i h
      · exact valid_nGatesOf _ gateOK_swapRegs i h
  | value => exact valid_implValW N z₀

theorem callsOf_implValW (N : ℕ) (z₀ : Cfg (VW b)) :
    CallsOf Query.value (implValW (k := k) N z₀) := by
  unfold implValW
  exact callsOf_append (callsOf_append (callsOf_append (callsOf_append (callsOf_nGatesOf _ _)
    (callsOf_call _ _ _)) (callsOf_nGatesOf _ _)) (callsOf_call _ _ _)) (callsOf_nGatesOf _ _)

/-- **Every implementation makes at most three calls, all of the corresponding primitive** (the
writer for the value oracle: one call and one inverse call). -/
theorem kindOK_implPW (N s : ℕ) (z₀ : Cfg (VW b)) :
    KindOK (implPW (k := k) (b := b) N s z₀) id 3 where
  kind_eq j := by
    cases j with
    | rowLocation => exact callsOf_implLoc N s _
    | columnLocation => exact callsOf_append (callsOf_implLoc N s _) (callsOf_nGatesOf _ _)
    | value => exact callsOf_implValW N z₀
  count j := by
    cases j with
    | rowLocation => exact (kindOK_implP (k := k) (b := b) N s z₀).count Query.rowLocation
    | columnLocation => exact (kindOK_implP (k := k) (b := b) N s z₀).count Query.columnLocation
    | value =>
        simp only [implPW, implValW, nCallsN_append, nCallsN_nGatesOf, nCallsN_call]
        omega

/-- **The writer implementations have the gates of the implementations from the XOR oracle**,
hence at most `implG k b` elementary gates. -/
theorem nGatesN_implPW_eq (N s : ℕ) (z₀ : Cfg (VW b)) (j : Query) :
    nGatesN (implPW (k := k) (b := b) N s z₀ j) = nGatesN (implP (k := k) (b := b) N s z₀ j) := by
  cases j with
  | rowLocation => rfl
  | columnLocation => rfl
  | value =>
      simp only [implPW, implP, implValW, implVal, nGatesN_append, nGatesN_nGatesOf, nGatesN_call]

theorem nGatesN_implPW_le (N s : ℕ) (z₀ : Cfg (VW b)) (j : Query) :
    nGatesN (implPW (k := k) (b := b) N s z₀ j) ≤ implG k b := by
  rw [nGatesN_implPW_eq]
  exact nGatesN_implP_le N s z₀ j

end WriterImpl

section WriterClean

variable {X : Type*} {N s k b : ℕ} {D : QData X N s k b} (Wr : D.Writer)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The implementations act as the padded primitives on clean ancillas**, for every unitary
action of the writer outside its valid clean inputs and of the locators outside their valid list
inputs. -/
theorem implOKW (z₀ : Cfg (VW b)) (hz₀ : D.val z₀ = 0) (x : X) :
    ImplOK (Wr.prims (R := R) x) (GateBinary.prims (R := R) (D.padData z₀ hz₀) (Equiv.refl _) x)
      (implPW N s z₀) where
  valid := valid_implPW N s z₀
  clean j := by
    cases j with
    | rowLocation =>
        change nrun (Wr.prims (R := R) x) (implLoc N s Query.rowLocation) ∘L cleanEmb = _
        rw [prims_pad_row]
        exact maskCtrl_clean (D.rowOracle x) (D.row_unitary x) (D.rowloc x) D.N_pos D.slots_pos
          (D.row_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ
          (Wr.prims x) Query.rowLocation (Wr.prims_row x)
    | columnLocation =>
        change nrun (Wr.prims (R := R) x) (implLoc N s Query.columnLocation ++
          nGatesOf (swapRegs k b)) ∘L cleanEmb = _
        unfold implLoc
        rw [prims_pad_col, nrun_append, nrun_nGatesOf, comp_assoc,
          maskCtrl_clean (D.columnOracle x) (D.column_unitary x) (D.colloc x) D.N_pos D.slots_pos
            (D.column_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ
            (Wr.prims x) Query.columnLocation (Wr.prims_col x),
          ← comp_assoc (gRun (Q := R) (swapRegs k b)), gRun_swapRegs_cleanEmb, comp_assoc]
    | value =>
        change nrun (Wr.prims (R := R) x) (implValW N z₀) ∘L cleanEmb = _
        rw [GateBinary.prims_val]
        exact implValW_clean Wr D.N_lt_pow_succ z₀ x

end WriterClean

/-! ### The padded data with a validity decoder and a masked table -/

namespace QData

variable {X : Type*} {N s k b : ℕ} (D : QData X N s k b)

/-- The validity decoder ignores the word of an invalid pair. -/
theorem pdecode_ptable_false (x : X) (y y' : Cfg (Fin (k + 1))) :
    D.pdecode (y, y') (D.ptable (fun _ => false) x (y, y')) =
      D.pdecode (y, y') (D.ptableE x (y, y')) := by
  unfold pdecode ptable ptableE
  dsimp only
  by_cases h : PValid N y ∧ PValid N y'
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-- **The padded data with a validity decoder and a masked table**: `padDataE` with the stored word
of the low index words on a valid pair and the all-zero word on an invalid pair. -/
def padDataEW : NativeSparseBlockEncoding.Data X (Cfg (Fin (k + 1))) (Cfg (VW b)) (sP s) :=
  { D.padDataE with
    table := fun x e => D.ptable (fun _ => false) x e
    decoded := fun x y y' => D.pdecode_ptable_false x y y' }

theorem padDataEW_matrix : D.padDataEW.matrix = D.padDataE.matrix := rfl

theorem padDataEW_decode : D.padDataEW.decode = D.padDataE.decode := rfl

theorem padDataEW_table (x : X) : D.padDataEW.table x = D.ptable (fun _ => false) x := rfl

end QData

section WriterCleanE

variable {X : Type*} {N s k b : ℕ} {D : QData X N s k b} (Wr : D.Writer)
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

theorem prims_padEW_row (x : X) :
    GateBinary.prims (R := R) D.padDataEW (Equiv.refl _) x Query.rowLocation =
      GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x Query.rowLocation := rfl

theorem prims_padEW_col (x : X) :
    GateBinary.prims (R := R) D.padDataEW (Equiv.refl _) x Query.columnLocation =
      GateBinary.prims (R := R) D.padDataE (Equiv.refl _) x Query.columnLocation := rfl

theorem prims_padEW_val (x : X) :
    GateBinary.prims (R := R) D.padDataEW (Equiv.refl _) x Query.value =
      permOp (xorEquiv (fun d => D.ptable (fun _ => false) x (phiE (Equiv.refl _) d))) := by
  rw [GateBinary.prims_val]
  rfl

/-- **The writer implementations act as the primitives of `padDataEW` on clean ancillas**, for
every unitary action of the writer outside its valid clean inputs and of the locators outside their
valid list inputs. -/
theorem implOKEW (x : X) :
    ImplOK (Wr.prims (R := R) x) (GateBinary.prims (R := R) D.padDataEW (Equiv.refl _) x)
      (implPW N s (fun _ => false)) where
  valid := valid_implPW N s _
  clean j := by
    cases j with
    | rowLocation =>
        change nrun (Wr.prims (R := R) x) (implLoc N s Query.rowLocation) ∘L cleanEmb = _
        rw [prims_padEW_row, prims_padE_row]
        exact maskCtrl_clean (D.rowOracle x) (D.row_unitary x) (D.rowloc x) D.N_pos D.slots_pos
          (D.row_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ
          (Wr.prims x) Query.rowLocation (Wr.prims_row x)
    | columnLocation =>
        change nrun (Wr.prims (R := R) x) (implLoc N s Query.columnLocation ++
          nGatesOf (swapRegs k b)) ∘L cleanEmb = _
        unfold implLoc
        rw [prims_padEW_col, prims_padE_col, nrun_append, nrun_nGatesOf, comp_assoc,
          maskCtrl_clean (D.columnOracle x) (D.column_unitary x) (D.colloc x) D.N_pos D.slots_pos
            (D.column_valid x ⟨0, D.N_pos⟩ ⟨0, D.slots_pos⟩) D.N_lt_pow_succ D.s_lt_pow_succ
            (Wr.prims x) Query.columnLocation (Wr.prims_col x),
          ← comp_assoc (gRun (Q := R) (swapRegs k b)), gRun_swapRegs_cleanEmb, comp_assoc]
    | value =>
        change nrun (Wr.prims (R := R) x) (implValW N (fun _ => false)) ∘L cleanEmb = _
        rw [prims_padEW_val]
        exact implValW_clean Wr D.N_lt_pow_succ (fun _ => false) x

end WriterCleanE

end

end SparseHamiltonian.GeneralSparseAccess
