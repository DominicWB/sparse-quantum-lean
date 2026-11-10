import GateEfficientBinary.Sparse.Native

/-!
# The native private operation of binary sparse oracles with a general decoder

`GateBinary.sparse_nativeOK` proves the native identity `V† R_val V = D` for the compute circuit
`computeV` of the binary sparse oracles and the decoder `γ √s c₀ (X + i Y)` of the value wires.
The decoder enters the proof only through the decoded rotation (`GateBinary.rdec_sigma`). Here the
same identity is proved for the public decoder of the data itself, which may depend on the edge
(`NativeSparseBlockEncoding.Data.decode`): `sparseOpD D en κ` is the native private operation
whose decoder reads the edge on the index wires (`eword`) and the stored word on the value wires
(`vword`) and returns `κ · decode(e, w)`, and `sparse_nativeOKD` is its native identity for
`κ = γ √s`. The manuscript selects the rotation of an invalid index pair "independently of the
returned encoding" from a validity predicate computed on the indices (Section `hs:sec:gates`,
paragraph *Entry arithmetic and the precise resource bound*); an edge-dependent decoder is how the
padded data express this.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The value word held by the value wires of a configuration of the base wires. -/
def vword (y : Cfg (BW k b)) : Cfg (VW b) := fun w => y (vB w)

/-- The edge word held by the index wires of a configuration of the base wires. -/
def eword (y : Cfg (BW k b)) : Cfg (EW k) := fun e => y (tB e)

theorem vword_update_oB (y : Cfg (BW k b)) (v : Bool) :
    vword (Function.update y oB v) = vword y := by
  funext w
  exact Function.update_of_ne (vB_ne_oB w) _ _

theorem eword_update_oB (y : Cfg (BW k b)) (v : Bool) :
    eword (Function.update y oB v) = eword y := by
  funext e
  exact Function.update_of_ne (tB_ne_oB e) _ _

/-- **The native private operation with the decoder of the data**: the compute circuit of the
binary sparse oracles, the orientation wire and the decoder `κ · decode(e, w)` of the edge on the
index wires and the stored word on the value wires. -/
def sparseOpD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (κ : ℝ) :
    NativeOp Empty (PR k) (SZ k b) (PY k b) Query where
  V := computeV k b
  o := oPR k
  dec := fun y => (κ : ℂ) * D.decode (phiE en (eword y)) (vword y)

/-- The compute circuit is valid and the decoder does not read the orientation wire. -/
theorem sparseOpD_public (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (κ : ℝ) :
    (sparseOpD D en κ).Public where
  valid := computeV_valid k b
  dec_indep y v := by
    show (κ : ℂ) * D.decode (phiE en (eword (Function.update y oB v)))
        (vword (Function.update y oB v)) = (κ : ℂ) * D.decode (phiE en (eword y)) (vword y)
    rw [vword_update_oB, eword_update_oB]

theorem sparseOpD_V (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (κ : ℝ) :
    (sparseOpD D en κ).V = computeV k b :=
  rfl

/-- The compute circuit does not change the index wires. -/
theorem sigma_tB (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (Empty ⊕ PR k)) (e : EW k) :
    sigma D en k0 x (Sum.elim c (fun _ => false)) (tB e) = c (Sum.inr (ixPR k e)) := by
  rw [sigma, Equiv.trans_apply, show (tB e : BW k b) = posT (Sum.inl e) from rfl,
    alongEquiv_apply_in]
  simp [valPerm, posT, sigRef, refCfg, tB]

/-- **The decoded rotation** of the private operation with the decoder `γ √s decode` commutes
past the permutation of the compute circuit into the lifted edge action. -/
theorem rdec_sigmaD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (γ : ℝ) :
    Rdec (R := R) (sparseOpD D en (γ * Real.sqrt s)) ∘L permOp (sigma D en k0 x) ∘L
        cleanEmb (X := SZ k b) =
      permOp (sigma D en k0 x) ∘L cleanEmb ∘L Aq D en x γ := by
  have hR : Rdec (R := R) (sparseOpD D en (γ * Real.sqrt s)) =
      condOp oB (fun y => edgeMat (((γ * Real.sqrt s : ℝ) : ℂ) *
        D.decode (phiE en (eword y)) (vword y))) :=
    rfl
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
  have hval : vword (sigma D en k0 x (Sum.elim c (fun _ => false))) =
      D.table x (phiE en (fun e => c (Sum.inr (ixPR k e)))) := by
    funext w
    exact sigma_val D en k0 x c w
  have hedge : eword (sigma D en k0 x (Sum.elim c (fun _ => false))) =
      fun e => c (Sum.inr (ixPR k e)) := by
    funext e
    exact sigma_tB D en k0 x c e
  have hent := D.decoded x (phiE en (fun e => c (Sum.inr (ixPR k e)))).1
    (phiE en (fun e => c (Sum.inr (ixPR k e)))).2
  rw [Prod.mk.eta] at hent
  unfold edgeVal
  rw [vword_update_oB, eword_update_oB, hval, hedge, hix, ← hent]

/-- **The native identity from binary sparse oracles with the decoder of the data.** For indices
given by `k`-bit words (`en`) with the all-zero word a slot (`hk0`), the compute circuit
`computeV` with the decoder `γ √s decode` of the edge and the stored word satisfies the native
identity `V† R_val V = D` on clean scratch, for the qubit lift `D` of the private Cayley
operation `FixedNativeCayleySimulation.action D x γ`. -/
theorem sparse_nativeOKD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (γ : ℝ) :
    NativeOK (prims (R := R) D en x) (sparseOpD D en (γ * Real.sqrt s))
      (selOp (fun _ : Cfg Empty =>
        unconj (qlift (R := R) (phiPR en) (FixedNativeCayleySimulation.action D x γ)))) := by
  have hK1 := compute_cleanEmb (R := R) (b := b) D en k0 hk0 x
  have hK2 := rdec_sigmaD (R := R) D en k0 x γ
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (computeV k b)) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (computeV_valid k b)
  have hFu : IsUnitary (Fq (R := R) D en x) :=
    liftE_isUnitary (qlift_isUnitary _ (FixedLocatorConjugation.locator_unitary D x))
  have hVV : (nrun (prims (R := R) D en x) (computeV k b))† ∘L
      nrun (prims (R := R) D en x) (computeV k b) = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : Fq (R := R) D en x ∘L (Fq D en x)† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold NativeOK
  rw [selOp_unconj, liftE_action]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

end

end SparseHamiltonian.GeneralDecoder
