import GeneralDecoder.Native
import GateOptimalBinary.Main

/-!
# The native data of Theorem `gate:thm:main` with the decoder of the data

`GateOptimalBinary` builds the native data of the three regimes of Theorem `gate:thm:main` for
entries decoded as `c₀ (X + iY)`. The decoder enters only through the decoded entries of the native
operations: here they are the decoded entries of the data itself, which may depend on the edge
(`NativeSparseBlockEncoding.Data.decode`), read from the index wires (`edgeBF`) and the value wires
(`GateOptimalBinary.valF`), with the scalar arithmetic supplied on the base wires:

* bounded regime: `boundedNativeD`, the native private operation `sparseOpD` of the normalised data
  at the rescaling `γ √s` (`γ = bdGamma σ θ ε`) and a supplied angle arithmetic of the decoded entry
  `(γ √s/η) decode(e, w)`;
* signed-factor regime: `sgFOD`, the native factor with the decoded entry
  `clip(decode(e, w)/μ)` (`sgDec`), and `signedNativeD`;
* clipped regime: `clFOD`, the native factor with the decoded correction entry `[g] c₂`
  (`cfdecD`), `clNDD`, the native rotation with the decoded value `y(g, f, c₁, c₂)` (`ckdecD`), with
  `c₁`, `c₂` the clipped and correction entries of `decode(e, w)`, and `clipNativeD`.

The native identities (`sgFOD_native`, `clFOD_native`, `clNDD_native`) hold for every decoder:
the stored word of the located edge decodes to its entry (`Data.decoded`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section

open ContinuousLinearMap SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary GateOptimalPrecision
open GateOptimalBinary (PRf ιS ιS_injective ιF ιF_injective ιE ιE_injective ιEe ιB ιB_injective ιBe
  locF vF valF locBF locBF_injective sigF sigF_val sigF_overwrite sigF_locBF edgeF edgeF_overwrite
  cvF locE locE_injective overwrite_locBF_elim valF_overwrite_locBF liftE_FuF liftE_AuF
  sel_liftA_sgU put_sum_smul_bas sgU sgUJg sgUJg_ok signedIface gBF locBF_ne_gBF sigF_gBF cFE
  liftE_AF clW_compute FL FL_isUnitary liftE_LD yCfg sigF_update_o sigF_o update_locBF_eq
  edge_ne_locF gW_ne_locF exists_zero_slot clippedIface clUJg clUJg_ok clD_split Uf_isUnitary
  Cf_isUnitary boundedIface bdK bdPriv_elift normD yC gW cl1 cl2 sysH)
open NativeSparseBlockEncoding (Data Query)
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)
open LargeSparsityCore.Native (cclip ccorr)
open LargeSparsityCore.Parameters (hval qval)
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The bounded regime -/

/-- The decoder of the native private operation of the normalised data at the rescaling `c`: the
decoder of the data rescaled by `c/η`. -/
theorem sparseOpD_normD_dec (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) {η : ℝ}
    (hη : 0 < η) (c : ℝ) :
    (sparseOpD (normD D η hη) en c).dec =
      fun y => ((c / η : ℝ) : ℂ) * D.decode (phiE en (eword y)) (vword y) := by
  funext y
  change ((c : ℝ) : ℂ) * (((η⁻¹ : ℝ) : ℂ) * D.decode _ _) = _
  push_cast
  ring

/-- **The native data of the bounded regime with the decoder of the data**: `U_J = hadUJ`, the
compute circuit `computeV`, the native private operation `sparseOpD` of the normalised data at the
rescaling `γ √s` (`γ = bdGamma σ θ ε`), and a supplied angle arithmetic `ar` of its decoded entry
`(γ √s/η) decode(e, w)` at accuracy `ζ`. -/
def boundedNativeD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {η μ σ θ ε ζ : ℝ} (hη : 0 < η) (hμ : 0 ≤ μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ)
    (ar : Arith (BW k b))
    (har : ArithOK ar (Sum.inl (Sum.inr (oPR k)))
      (fun y => ((bdGamma σ θ ε * Real.sqrt s / η : ℝ) : ℂ) *
        D.decode (phiE en (eword y)) (vword y)) ζ) :
    CayleyNative (prims (R := R) D en x)
      (boundedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hcol hent).UJ
      (bdPriv (boundedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hcol hent).K
        σ θ ε) (SZ k b) ζ where
  UJg := hadUJ k sb hsb
  ok := hadUJ_ok sb hsb
  boundary := rfl
  nd := sparseOpD (normD D η hη) en (bdGamma σ θ ε * Real.sqrt s)
  pub := sparseOpD_public _ en _
  ar := ar
  arith := by
    rw [sparseOpD_normD_dec D en hη]
    exact har
  native := by
    obtain ⟨k0, hk0⟩ := exists_zero_slot D en sb hrange
    have h := sparse_nativeOKD (R := R) (normD D η hη) en k0 hk0 x (bdGamma σ θ ε)
    change NativeOK (prims (R := R) D en x)
      (sparseOpD (normD D η hη) en (bdGamma σ θ ε * Real.sqrt s))
      (selOp (fun _ : Cfg Empty => bdPriv (bdK (R := R) D en η hη x) σ θ ε))
    rw [bdK, bdPriv_elift]
    exact h

/-! ### The edge and the decoded entry on the base wires of the native factor -/

/-- The edge held by the index wires of a configuration of the base wires of the native factor. -/
def edgeBF (en : Cfg (Fin k) ≃ n) (y : Cfg (NB Empty (PRf k) (SZ k b))) : n × n :=
  edgeF en (fun p => y (Sum.inl p))

omit [Fintype n] [DecidableEq n] in
/-- The edge does not read the local qubits. -/
theorem edgeBF_overwrite (en : Cfg (Fin k) ≃ n) (y : Cfg (NB Empty (PRf k) (SZ k b)))
    (d : Cfg (Fin 3)) : edgeBF en (overwrite (locBF k) y d) = edgeBF en y := by
  unfold edgeBF edgeF
  congr 1
  funext e
  exact overwrite_apply_out _ _ _ _
    (fun i h => edge_ne_locF k i e (Sum.inr_injective (Sum.inl_injective h)))

/-- **The compute circuit does not change the index wires.** -/
theorem sigF_edge (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (Empty ⊕ PRf k)) :
    edgeBF en (sigF D en k0 x (Sum.elim c (fun _ => false))) = edgeF en c := by
  unfold edgeBF edgeF
  congr 1
  funext e
  change alongEquiv (ιBe k b) (sigma D en k0 x) (Sum.elim c (fun _ => false))
    (ιBe k b (tB e)) = _
  rw [alongEquiv_apply_in]
  have hY : (fun a => (Sum.elim c (fun _ => false) : Cfg (NB Empty (PRf k) (SZ k b)))
      (ιBe k b a)) = Sum.elim (fun p => c (ιE k p)) (fun _ => false) := by
    funext a
    rcases a with a | a <;> rfl
  rw [hY, sigma_tB]
  rfl

/-- The entry `decode(e, w)` of the edge `e` on the index wires and the stored word `w` on the value
wires. -/
def entD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) : ℂ :=
  D.decode (edgeBF en y) (valF y)

theorem entD_overwrite (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) (d : Cfg (Fin 3)) :
    entD D en (overwrite (locBF k) y d) = entD D en y := by
  unfold entD
  rw [edgeBF_overwrite, valF_overwrite_locBF]

theorem entD_update (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) (v : Bool) :
    entD D en (Function.update y (locBF k 1) v) = entD D en y := by
  rw [update_locBF_eq, entD_overwrite]

/-- **The decoded entry of the computed words is the entry of the located edge.** -/
theorem entD_sig (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (Empty ⊕ PRf k)) :
    entD D en (sigF D en k0 x (Sum.elim c (fun _ => false))) =
      D.matrix x (edgeF en c).1 (edgeF en c).2 := by
  unfold entD
  rw [sigF_edge, sigF_val]
  have h := D.decoded x (edgeF en c).1 (edgeF en c).2
  rw [Prod.mk.eta] at h
  exact h

/-! ### The signed-factor regime -/

/-- **The decoded entry of the native factor with the decoder of the data**: `clip(decode(e, w)/μ)`
of the edge `e` on the index wires and the stored word `w` on the value wires. -/
def sgDec (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) : ℂ :=
  NativeSignedFactor.entry D μ (edgeBF en y, valF y)

/-- **The native factor of the signed-factor regime with the decoder of the data**: the compute
circuit of the bounded regime on the bounded wires, the local qubits `(f, o, z)`, the decoded entry
`sgDec` and a supplied factor arithmetic `(circ, tw, pw)` on the base wires. -/
def sgFOD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    FactorOp (PRf k) (SZ k b) (PY k b) Query bT bP A where
  W := (computeV k b).map (NInstr.map (ιBe k b))
  loc := locF k
  dec := sgDec D en μ
  circ := circ
  tw := tw
  pw := pw

/-- The public conditions of the native factor. -/
theorem sgFOD_public (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    (sgFOD D en μ circ tw pw).Public where
  valid := valid_map_list (ιBe k b) (computeV k b) (computeV_valid k b)
  dec_indep y c := by
    change sgDec D en μ (overwrite (locBF k) y c) = sgDec D en μ y
    unfold sgDec
    rw [edgeBF_overwrite, valF_overwrite_locBF]
  dec_le y := NativeSignedFactor.norm_entry_le _ _ _

theorem Udec_sgFOD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    Udec (R := R) (sgFOD D en μ circ tw pw) = localOp (locBF (b := b) k) (locBF_injective k)
      (fun y => matOp (blk (uMat (sgDec D en μ y)))) := rfl

/-- The decoded entry of the computed words, with the local qubits cleared, is the entry of the
located edge. -/
theorem sgDec_sig (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ : ℝ) (c : Cfg (Empty ⊕ PRf k)) :
    sgDec D en μ (clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false)))) =
      cvF D en μ x (clearCfg (locE k) c) := by
  unfold sgDec cvF
  rw [edgeBF_overwrite, valF_overwrite_locBF, sigF_edge, sigF_val, edgeF_overwrite]

/-- **The decoded factor commutes past the permutation** into the lifted local factor of the
located edge. -/
theorem sgFOD_dec_comm (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ : ℝ) {bT bP A : ℕ} (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    Udec (R := R) (sgFOD D en μ circ tw pw) ∘L permOp (sigF D en k0 x) ∘L
        cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L
        liftE (localOp (ιS k) (ιS_injective k) (fun _ => GateOptimalBinary.AuF (R := R) D en μ x)) := by
  rw [Udec_sgFOD, liftE_AuF]
  apply ext_bas_clm'
  intro c q
  simp only [comp_apply]
  rw [cleanEmb_bas, permOp_bas, localOp_bas, localOp_bas, matOp_bas', matOp_bas',
    put_sum_smul_bas, put_sum_smul_bas, map_sum, map_sum]
  have hd0 : (fun a => sigF D en k0 x (Sum.elim c (fun _ => false)) (locBF k a)) =
      fun a => c (locE k a) := by
    rw [sigF_locBF]
    rfl
  rw [hd0, sgDec_sig D en k0 x μ c]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_smul, map_smul, cleanEmb_bas, permOp_bas, ← overwrite_locBF_elim, sigF_overwrite]

/-- **The native identity of the signed factor with the decoder of the data**
(`FactorNativeOK`): `W† U(c) W` acts on clean scratch as the factor `U_B = sgU` of `signedIface`,
lifted past the attenuation wire. -/
theorem sgFOD_native (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (μ : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    FactorNativeOK (prims (R := R) D en x) (sgFOD D en μ circ tw pw)
      (selOp (fun _ : Cfg Empty => liftA (sgU (R := R) D en μ x))) := by
  have hK1 : nrun (prims (R := R) D en x) (sgFOD D en μ circ tw pw).W ∘L cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L
        liftE (localOp (ιS k) (ιS_injective k)
          (fun _ => GateOptimalBinary.FuF (R := R) D en x)) :=
    clW_compute (R := R) (b := b) D en k0 hk0 x
  have hK2 := sgFOD_dec_comm (R := R) D en k0 x μ circ tw pw
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (sgFOD D en μ circ tw pw).W) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (sgFOD_public D en μ circ tw pw).valid
  have hFu : IsUnitary (liftE (localOp (ιS k) (ιS_injective k)
      (fun _ => GateOptimalBinary.FuF (R := R) D en x))) :=
    liftE_isUnitary (localOp_isUnitary _ _ (fun _ => GateOptimalBinary.FuF_isUnitary D en x))
  have hVV : (nrun (prims (R := R) D en x) (sgFOD D en μ circ tw pw).W)† ∘L
      nrun (prims (R := R) D en x) (sgFOD D en μ circ tw pw).W = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : liftE (localOp (ιS k) (ιS_injective k)
      (fun _ => GateOptimalBinary.FuF (R := R) D en x)) ∘L
      (liftE (localOp (ιS k) (ιS_injective k)
        (fun _ => GateOptimalBinary.FuF (R := R) D en x)))† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold FactorNativeOK
  rw [sel_liftA_sgU]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

/-- **The native data of the signed-factor regime with the decoder of the data**: the boundary
gates of `signedIface`, the native factor `sgFOD` with a supplied factor arithmetic
`(circ, tw, pw)` of accuracy `ξ` (`FactorArithOK`), and its public and native conditions. -/
def signedNativeD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {η μ σ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) {ξ : ℝ} {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (har : FactorArithOK (sgFOD D en μ circ tw pw) ξ) :
    FactorNative (prims (R := R) D en x)
      (signedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hent).UJ
      (signedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hent).U (SZ k b) bT bP A ξ
    where
  UJg := sgUJg k sb hsb
  ok := sgUJg_ok sb hsb
  boundary := rfl
  fo := sgFOD D en μ circ tw pw
  pub := sgFOD_public D en μ circ tw pw
  arith := har
  native := by
    obtain ⟨k0, hk0⟩ := exists_zero_slot D en sb hrange
    exact sgFOD_native D en k0 hk0 x μ circ tw pw

/-! ### The clipped regime -/

/-- **The decoded correction entry with the decoder of the data**: `[g] c₂` of the branch `g` and
`c₂ = ccorr_{μ,β}(decode(e, w))`. -/
def cfdecD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) : ℂ :=
  if y (gBF k b) then ccorr μ β (entD D en y) else 0

/-- **The decoded value with the decoder of the data**: `y(g, f, c₁, c₂)` of the branch, the flag
and `c₁ = cclip_{μ,β}(decode(e, w))`, `c₂ = ccorr_{μ,β}(decode(e, w))`. -/
def ckdecD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) : ℂ :=
  yC q (y (gBF k b)) (y (locBF k 0)) (cclip μ β (entD D en y)) (ccorr μ β (entD D en y))

theorem norm_cfdecD_le (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) : ‖cfdecD D en μ β y‖ ≤ 1 := by
  unfold cfdecD
  split_ifs
  · exact LargeSparsityCore.Native.norm_ccorr_le_one _
  · simp

/-- **The native factor of the clipped regime with the decoder of the data**: the compute circuit
of the signed regime, the local qubits `(f, o, z)`, the decoded correction entry `cfdecD` and a
supplied factor arithmetic `(circ, tw, pw)` on the base wires. -/
def clFOD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    FactorOp (PRf k) (SZ k b) (PY k b) Query bT bP A where
  W := (computeV k b).map (NInstr.map (ιBe k b))
  loc := locF k
  dec := cfdecD D en μ β
  circ := circ
  tw := tw
  pw := pw

/-- **The native rotation of the clipped regime with the decoder of the data**: the compute
circuit of the signed regime, the orientation `o` and the decoded value `ckdecD`. -/
def clNDD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) :
    NativeOp Empty (PRf k) (SZ k b) (PY k b) Query where
  V := (computeV k b).map (NInstr.map (ιBe k b))
  o := locF k 1
  dec := ckdecD D en μ β q

/-- The public conditions of the native factor. -/
theorem clFOD_public (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    (clFOD D en μ β circ tw pw).Public where
  valid := valid_map_list (ιBe k b) (computeV k b) (computeV_valid k b)
  dec_indep y c := by
    change cfdecD D en μ β (overwrite (locBF k) y c) = cfdecD D en μ β y
    unfold cfdecD
    rw [entD_overwrite, overwrite_apply_out _ _ _ _ (fun i => locBF_ne_gBF i)]
  dec_le y := norm_cfdecD_le D en μ β y

/-- The public conditions of the native rotation. -/
theorem clNDD_public (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) :
    (clNDD D en μ β q).Public where
  valid := valid_map_list (ιBe k b) (computeV k b) (computeV_valid k b)
  dec_indep y v := by
    change ckdecD D en μ β q (Function.update y (locBF k 1) v) = ckdecD D en μ β q y
    unfold ckdecD
    rw [entD_update, Function.update_of_ne (Ne.symm (locBF_ne_gBF 1)),
      Function.update_of_ne (fun h => absurd (locBF_injective k h) (by decide))]

theorem Udec_clFOD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    Udec (R := R) (clFOD D en μ β circ tw pw) = localOp (locBF (b := b) k) (locBF_injective k)
      (fun y => matOp (blk (uMat (cfdecD D en μ β y)))) := rfl

/-- The decoded correction entry of the computed words is the correction entry of the located
edge. -/
theorem cfdecD_sig (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β : ℝ) (c : Cfg (Empty ⊕ PRf k)) :
    cfdecD D en μ β (clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false)))) =
      cFE D en μ β x (clearCfg (locE k) c) := by
  have hg : clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false))) (gBF k b) =
      c (Sum.inr (gW k)) := by
    rw [clearCfg_apply_out _ _ _ (fun i => locBF_ne_gBF i), sigF_gBF]
    rfl
  have he : entD D en (clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false)))) =
      D.matrix x (edgeF en c).1 (edgeF en c).2 := by
    rw [entD_overwrite, entD_sig]
  have hg' : clearCfg (locE k) c (Sum.inr (gW k)) = c (Sum.inr (gW k)) :=
    clearCfg_apply_out _ _ _ (fun i h => gW_ne_locF k i (Sum.inr_injective h))
  unfold cfdecD cFE
  rw [hg, hg', he, edgeF_overwrite]
  rfl

/-- **The decoded factor commutes past the permutation** into the lifted factor of the frame. -/
theorem clFOD_dec_comm (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β : ℝ) {bT bP A : ℕ} (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    Udec (R := R) (clFOD D en μ β circ tw pw) ∘L permOp (sigF D en k0 x) ∘L
        cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L liftE (GateOptimalBinary.AF (R := R) D en μ β x) := by
  rw [Udec_clFOD, liftE_AF]
  apply ext_bas_clm'
  intro c q
  simp only [comp_apply]
  rw [cleanEmb_bas, permOp_bas, localOp_bas, localOp_bas, matOp_bas', matOp_bas',
    put_sum_smul_bas, put_sum_smul_bas, map_sum, map_sum]
  have hd0 : (fun a => sigF D en k0 x (Sum.elim c (fun _ => false)) (locBF k a)) =
      fun a => c (locE k a) := by
    rw [sigF_locBF]
    rfl
  rw [hd0, cfdecD_sig D en k0 x μ β c]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_smul, map_smul, cleanEmb_bas, permOp_bas, ← overwrite_locBF_elim, sigF_overwrite]

/-- **The native identity of the clipped factor with the decoder of the data**
(`FactorNativeOK`): `W† U(c) W` acts on clean scratch as the factor `U_f`. -/
theorem clFOD_native (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (μ β : ℝ) {bT bP A : ℕ}
    (circ : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (tw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (pw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool) :
    FactorNativeOK (prims (R := R) D en x) (clFOD D en μ β circ tw pw)
      (selOp (fun _ : Cfg Empty => GateOptimalBinary.Uf (R := R) D en μ β x)) := by
  have hK1 := clW_compute (R := R) (b := b) D en k0 hk0 x
  have hK2 := clFOD_dec_comm (R := R) D en k0 x μ β circ tw pw
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (clFOD D en μ β circ tw pw).W) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (clFOD_public D en μ β circ tw pw).valid
  have hFu : IsUnitary (liftE (FL (R := R) D en x)) := liftE_isUnitary (FL_isUnitary D en x)
  have hVV : (nrun (prims (R := R) D en x) (clFOD D en μ β circ tw pw).W)† ∘L
      nrun (prims (R := R) D en x) (clFOD D en μ β circ tw pw).W = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : liftE (FL (R := R) D en x) ∘L (liftE (FL (R := R) D en x))† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold FactorNativeOK
  rw [GateOptimalBinary.Uf, selOp_unconj, liftE_comp, liftE_comp, liftE_adjoint]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

theorem Rdec_clNDD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) :
    Rdec (R := R) (clNDD D en μ β q) =
      condOp (locBF k 1) (fun y => edgeMat (ckdecD D en μ β q y)) := rfl

/-- The decoded value of the computed words is the value of the located edge. -/
theorem ckdecD_sig (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β q : ℝ) (c : Cfg (Empty ⊕ PRf k)) :
    ckdecD D en μ β q (Function.update (sigF D en k0 x (Sum.elim c (fun _ => false)))
        (locBF k 1) false) =
      yCfg D en μ β q x (fun w => Function.update c (Sum.inr (locF k 1)) false (Sum.inr w)) := by
  have hu : ckdecD D en μ β q (Function.update (sigF D en k0 x (Sum.elim c (fun _ => false)))
      (locBF k 1) false) = ckdecD D en μ β q (sigF D en k0 x (Sum.elim c (fun _ => false))) :=
    (clNDD_public D en μ β q).dec_indep _ false
  rw [hu]
  have hg : sigF D en k0 x (Sum.elim c (fun _ => false)) (gBF k b) = c (Sum.inr (gW k)) := by
    rw [sigF_gBF]
    rfl
  have hf : sigF D en k0 x (Sum.elim c (fun _ => false)) (locBF k 0) = c (locE k 0) := by
    rw [congrFun (sigF_locBF D en k0 x (Sum.elim c (fun _ => false))) 0]
    rfl
  have hg' : Function.update c (Sum.inr (locF k 1)) false (Sum.inr (gW k)) = c (Sum.inr (gW k)) :=
    Function.update_of_ne (fun h => gW_ne_locF k 1 (Sum.inr_injective h).symm) _ _
  have hf' : Function.update c (Sum.inr (locF k 1)) false (Sum.inr (locF k 0)) = c (locE k 0) :=
    Function.update_of_ne (fun h => absurd ((locF k).injective (Sum.inr_injective h))
      (by decide)) _ _
  have he' : GateOptimalBinary.edgeC en
      (fun w => Function.update c (Sum.inr (locF k 1)) false (Sum.inr w)) = edgeF en c := by
    unfold GateOptimalBinary.edgeC edgeF
    congr 1
    funext e
    exact Function.update_of_ne (fun h => edge_ne_locF k 1 e (Sum.inr_injective h).symm) _ _
  unfold ckdecD yCfg
  dsimp only
  rw [hg, hf, entD_sig, hg', hf', he']
  rfl

/-- **The decoded rotation commutes past the permutation** into the lifted edge rotation. -/
theorem clNDD_rdec (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β q : ℝ) :
    Rdec (R := R) (clNDD D en μ β q) ∘L permOp (sigF D en k0 x) ∘L cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L liftE (GateOptimalBinary.LD (R := R) D en μ β q x) := by
  rw [Rdec_clNDD, liftE_LD]
  apply ext_bas_clm'
  intro c q'
  rw [comp_apply, comp_apply, comp_apply, comp_apply, cleanEmb_bas, permOp_bas, condOp_bas,
    condOp_bas, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [map_smul, map_smul, cleanEmb_bas, permOp_bas]
  have hcfg : (Sum.elim (Function.update c (Sum.inr (locF k 1)) v) (fun _ => false) :
      Cfg (NB Empty (PRf k) (SZ k b))) =
      Function.update (Sum.elim c (fun _ => false)) (locBF k 1) v := by
    funext w
    rcases w with p | z
    · by_cases hp : p = Sum.inr (locF k 1)
      · subst hp
        simp [locBF]
      · have hne : (Sum.inl p : NB Empty (PRf k) (SZ k b)) ≠ locBF k 1 :=
          fun h => hp (Sum.inl_injective h)
        rw [Function.update_of_ne hne]
        simp [Function.update_of_ne hp]
    · have hne : (Sum.inr z : NB Empty (PRf k) (SZ k b)) ≠ locBF k 1 := fun h => by cases h
      rw [Function.update_of_ne hne]
      rfl
  rw [hcfg, sigF_update_o, sigF_o, ckdecD_sig D en k0 x μ β q c]
  rfl

/-- **The native identity of the clipped rotation with the decoder of the data** (`NativeOK`):
`V† R V` acts on clean scratch as the rotation `C`. -/
theorem clNDD_native (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (μ β q : ℝ) :
    NativeOK (prims (R := R) D en x) (clNDD D en μ β q)
      (selOp (fun _ : Cfg Empty => GateOptimalBinary.Cf (R := R) D en μ β q x)) := by
  have hK1 := clW_compute (R := R) (b := b) D en k0 hk0 x
  have hK2 := clNDD_rdec (R := R) D en k0 x μ β q
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (clNDD D en μ β q).V) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (clNDD_public D en μ β q).valid
  have hFu : IsUnitary (liftE (FL (R := R) D en x)) := liftE_isUnitary (FL_isUnitary D en x)
  have hVV : (nrun (prims (R := R) D en x) (clNDD D en μ β q).V)† ∘L
      nrun (prims (R := R) D en x) (clNDD D en μ β q).V = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : liftE (FL (R := R) D en x) ∘L (liftE (FL (R := R) D en x))† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold NativeOK
  rw [GateOptimalBinary.Cf, selOp_unconj, liftE_comp, liftE_comp, liftE_adjoint]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

/-- **The native data of the clipped regime with the decoder of the data**: the boundary gates of
`clippedIface`, the split `D = U_f† C U_f`, the native factor `clFOD` with a supplied factor
arithmetic `(fcirc, ftw, fpw)` of accuracy `ξ` and the native rotation `clNDD` with a supplied
angle arithmetic `(acirc, atw, apw)` of accuracy `ζ` on the same arithmetic wires, with their
public and native conditions. -/
def clipNativeD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {σ θ ε μ η : ℝ} (Rg : LargeSparsityCore.Parameters.Regime σ θ ε) (hμ : 0 < μ)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ)
    {ξ ζ : ℝ} {bT bP A : ℕ}
    (fcirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (ftw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (fpw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (acirc : List (Gate (NB Empty (PRf k) (SZ k b) ⊕ AWr bT bP A)))
    (atw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bT → Bool)
    (apw : Cfg (NB Empty (PRf k) (SZ k b)) → Fin bP → Bool)
    (haf : FactorArithOK (clFOD D en μ (hval θ ε) fcirc ftw fpw) ξ)
    (haa : ArithOK (⟨bT, bP, A, acirc, atw, apw⟩ : Arith (NB Empty (PRf k) (SZ k b)))
      (Sum.inl (Sum.inr (locF k 1))) (ckdecD D en μ (hval θ ε) (qval σ θ ε)) ζ) :
    GateOptimalBinary.ClipNative (prims (R := R) D en x)
      (clippedIface (R := R) D en sb hsb hs hrange Rg hμ hσ x hH hrow hcol hent).UJ
      (clippedIface (R := R) D en sb hsb hs hrange Rg hμ hσ x hH hrow hcol hent).D (SZ k b)
      bT bP A ξ ζ where
  UJg := clUJg k sb hsb
  ok := clUJg_ok sb hsb
  boundary := rfl
  Uf := GateOptimalBinary.Uf (R := R) D en μ (hval θ ε) x
  Cf := GateOptimalBinary.Cf (R := R) D en μ (hval θ ε) (qval σ θ ε) x
  unitaryU := Uf_isUnitary D en μ _ x
  unitaryC := Cf_isUnitary D en μ _ _ x
  split := clD_split D en μ _ _ x
  fo := clFOD D en μ (hval θ ε) fcirc ftw fpw
  fpub := clFOD_public D en μ _ fcirc ftw fpw
  farith := haf
  fnative := by
    obtain ⟨k0, hk0⟩ := exists_zero_slot D en sb hrange
    exact clFOD_native D en k0 hk0 x μ _ fcirc ftw fpw
  nd := clNDD D en μ (hval θ ε) (qval σ θ ε)
  cpub := clNDD_public D en μ _ _
  circ := acirc
  tw := atw
  pw := apw
  carith := haa
  cnative := by
    obtain ⟨k0, hk0⟩ := exists_zero_slot D en sb hrange
    exact clNDD_native D en k0 hk0 x μ _ _

end

end SparseHamiltonian.GeneralDecoder
