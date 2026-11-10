import GateOptimalBinary.ClipCore
import GateOptimalBinary.ClipTransfer

/-!
# The native clipped private operation from binary sparse oracles

The native form of the private Cayley unitary `D` of the clipped joint representation
(`clippedIface`), as the factor-conjugated native call of `ClipTransfer` (Section `gate:sec:native`,
paragraph "Sparse preparation and the joint private operation": "We compute the value word while
retaining the entry indices, perform the local operation on its three separate qubits, and
uncompute the value"):

* the split `D = U_f† C U_f` (`clD_split`): the factor `U_f = F† A F` (`Uf`) and the rotation
  `C = F† D(y) F` (`Cf`), both conjugated by the lifted locator `F`;
* the native factor `clFO`: the compute circuit of the signed regime, the decoder `[g] c₂` of the
  branch and the value word (`cfdec`), the local qubits `(f, o, z)` and the scalar arithmetic of the
  hypothesis `ClipFactorArith` on the branch and value wires;
* the native rotation `clND`: the same compute circuit, the orientation `o`, the decoder
  `y(g, f, c₁, c₂)` of the branch, the flag and the value word (`ckdec`), and the angle arithmetic
  of the hypothesis `ClipAngleArith` on the branch, flag and value wires;
* `clFO_native` (`FactorNativeOK`) and `clND_native` (`NativeOK`): the native identities;
* `clipNative`: the native data `ClipNative` of the clipped regime.

The arithmetic hypotheses are the scalar-arithmetic assumption of Section `gate:sec:native`
("Standard efficiently decoded binary or fixed-point data satisfy the scalar-arithmetic
assumption") for the two decoded scalars.

The quoted sentence computes the value word once. The native call of `ClipTransfer` computes it
three times instead (in the native factor, the native rotation and the inverse native factor): six
compute circuits, `30` oracle calls per private call, where one computation would use `10`. The
difference is a constant factor; a fused call, which would need its own approximation lemma, is not
formalised.

References to the manuscript use its labels.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace GateOptimalBinary

noncomputable section

open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateBinary GateOptimalPrecision
open NativeSparseBlockEncoding (Data Query)
open SparseHamiltonian.GateODE (put put_apply localOp_put bas_eq_put overwrite_apply_ι
  overwrite_apply_out localOp_localOp')
open LargeSparsityCore.Native (cclip ccorr)
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### The inputs of the arithmetic -/

/-- The branch wire among the base wires. -/
def gBF (k b : ℕ) : NB Empty (PRf k) (SZ k b) := Sum.inl (Sum.inr (gW k))

theorem gBF_ne_vF (v : VW b) : gBF k b ≠ vF k b v := by
  simp [gBF, vF]

theorem locBF_ne_gBF (i : Fin 3) : locBF (b := b) k i ≠ gBF k b :=
  fun h => gW_ne_locF k i (Sum.inr_injective (Sum.inl_injective h))

theorem locBF_ne_vF (i : Fin 3) (v : VW b) : locBF (b := b) k i ≠ vF k b v := by
  simp [locBF, vF]

theorem ιB_ne_gBF (a : BW k b) : ιB k b a ≠ gBF k b := by
  rcases a with (e | p) | z
  · exact e.elim
  · intro h
    exact ιS_ne_gW k (ιU k p) (Sum.inr_injective (Sum.inl_injective h))
  · intro h
    cases h

/-- The inputs of the factor arithmetic: the branch and the value word. -/
def ιFin (k b : ℕ) : Unit ⊕ VW b → NB Empty (PRf k) (SZ k b) :=
  Sum.elim (fun _ => gBF k b) (vF k b)

theorem ιFin_injective : Function.Injective (ιFin k b) := by
  rintro (u | v) (u' | v') h
  · cases u
    cases u'
    rfl
  · exact absurd h (gBF_ne_vF v')
  · exact absurd h.symm (gBF_ne_vF v)
  · exact congrArg Sum.inr (vF_injective k b h)

/-- The inputs of the angle arithmetic: the branch, the flag and the value word. -/
def ιCin (k b : ℕ) : (Unit ⊕ Unit) ⊕ VW b → NB Empty (PRf k) (SZ k b) :=
  Sum.elim (Sum.elim (fun _ => gBF k b) (fun _ => locBF k 0)) (vF k b)

theorem ιCin_injective : Function.Injective (ιCin k b) := by
  rintro ((u | u) | v) ((u' | u') | v') h
  · cases u
    cases u'
    rfl
  · exact absurd h.symm (locBF_ne_gBF 0)
  · exact absurd h (gBF_ne_vF v')
  · exact absurd h (locBF_ne_gBF 0)
  · cases u
    cases u'
    rfl
  · exact absurd h (locBF_ne_vF 0 v')
  · exact absurd h.symm (gBF_ne_vF v)
  · exact absurd h.symm (locBF_ne_vF 0 v)
  · exact congrArg Sum.inr (vF_injective k b h)

theorem locBF_ne_ιFin (i : Fin 3) (a : Unit ⊕ VW b) : locBF (b := b) k i ≠ ιFin k b a := by
  rcases a with u | v
  · exact locBF_ne_gBF i
  · exact locBF_ne_vF i v

theorem locBF1_ne_ιCin (a : (Unit ⊕ Unit) ⊕ VW b) : locBF (b := b) k 1 ≠ ιCin k b a := by
  rcases a with (u | u) | v
  · exact locBF_ne_gBF 1
  · intro h
    exact absurd (locBF_injective k h) (by decide)
  · exact locBF_ne_vF 1 v

/-- The inputs of the factor arithmetic read from a configuration of the base wires. -/
def inF (y : Cfg (NB Empty (PRf k) (SZ k b))) : Cfg (Unit ⊕ VW b) := fun a => y (ιFin k b a)

/-- The inputs of the angle arithmetic read from a configuration of the base wires. -/
def inC (y : Cfg (NB Empty (PRf k) (SZ k b))) : Cfg ((Unit ⊕ Unit) ⊕ VW b) :=
  fun a => y (ιCin k b a)

theorem inF_overwrite (y : Cfg (NB Empty (PRf k) (SZ k b))) (d : Cfg (Fin 3)) :
    inF (overwrite (locBF k) y d) = inF y := by
  funext a
  exact overwrite_apply_out _ _ _ _ (fun i => locBF_ne_ιFin i a)

theorem inC_update (y : Cfg (NB Empty (PRf k) (SZ k b))) (v : Bool) :
    inC (Function.update y (locBF k 1) v) = inC y := by
  funext a
  exact Function.update_of_ne (fun h => locBF1_ne_ιCin a h.symm) _ _

/-! ### The decoders and the arithmetic hypotheses -/

/-- **The decoded correction entry** `[g] c₂` of the branch `g` and a value word, with
`c₂ = ccorr_{μ,β}(c₀(X + iY))`. -/
def cfdec (μ β c0 : ℝ) (w : Cfg (Unit ⊕ VW b)) : ℂ :=
  if w (Sum.inl ()) then ccorr μ β ((c0 : ℂ) * gauss (fun v => w (Sum.inr v))) else 0

/-- **The decoded value** `y(g, f, c₁, c₂)` of the branch, the flag and a value word, with
`c₁ = cclip_{μ,β}(c₀(X + iY))` and `c₂ = ccorr_{μ,β}(c₀(X + iY))`. -/
def ckdec (μ β q c0 : ℝ) (w : Cfg ((Unit ⊕ Unit) ⊕ VW b)) : ℂ :=
  yC q (w (Sum.inl (Sum.inl ()))) (w (Sum.inl (Sum.inr ())))
    (cclip μ β ((c0 : ℂ) * gauss (fun v => w (Sum.inr v))))
    (ccorr μ β ((c0 : ℂ) * gauss (fun v => w (Sum.inr v))))

theorem norm_cfdec_le (μ β c0 : ℝ) (w : Cfg (Unit ⊕ VW b)) : ‖cfdec μ β c0 w‖ ≤ 1 := by
  unfold cfdec
  split_ifs
  · exact LargeSparsityCore.Native.norm_ccorr_le_one _
  · simp

/-- **The scalar-arithmetic hypothesis of the clipped factor** (Section `gate:sec:native`): a
reversible circuit of controlled NOT gates with at most three controls on the branch, the value
word and `b_T + b_P + A` arithmetic wires that writes an angle word and a phase word for the
decoded correction entry `c = [g] c₂` (`cfdec`), restoring its work wires, with either the
threshold `|c| ≤ ξ²/16` and angle zero, or `|sin² α - |c|| ≤ ξ²` and `|e^{iφ} - c/|c|| ≤ ξ`. -/
structure ClipFactorArith (b : ℕ) (μ β c0 ξ : ℝ) (bT bP A : ℕ) where
  /-- The circuit. -/
  circ : List (Gate ((Unit ⊕ VW b) ⊕ AWr bT bP A))
  /-- The angle word. -/
  tw : Cfg (Unit ⊕ VW b) → Fin bT → Bool
  /-- The phase word. -/
  pw : Cfg (Unit ⊕ VW b) → Fin bP → Bool
  elem : ∀ g ∈ circ, g.cs.length ≤ 3
  classical : Classical circ
  compute : ∀ w : Cfg (Unit ⊕ VW b), cfgRun circ (Sum.elim w (fun _ => false)) =
    Sum.elim w (Sum.elim (Sum.elim (tw w) (pw w)) (fun _ => false))
  acc : ∀ w, (‖cfdec μ β c0 w‖ ≤ ξ ^ 2 / 16 ∧ alphaVal (tw w) = 0) ∨
    (|Real.sin (alphaVal (tw w)) ^ 2 - ‖cfdec μ β c0 w‖| ≤ ξ ^ 2 ∧
      ‖Complex.exp (phiVal (pw w) * Complex.I) - NativeSignedFactor.phase (cfdec μ β c0 w)‖ ≤ ξ)

/-- **The angle-arithmetic hypothesis of the clipped rotation** (Section `gate:sec:native`): a
reversible circuit of controlled NOT gates with at most three controls on the branch, the flag,
the value word and `b_T + b_P + A` arithmetic wires that writes the angle word of
`θ = 2 arctan |y|` and the phase word of `φ = arg y` within `ζ` for the decoded value
`y = y(g, f, c₁, c₂)` (`ckdec`), restoring its work wires. -/
structure ClipAngleArith (b : ℕ) (μ β q c0 ζ : ℝ) (bT bP A : ℕ) where
  /-- The circuit. -/
  circ : List (Gate (((Unit ⊕ Unit) ⊕ VW b) ⊕ AWr bT bP A))
  /-- The angle word. -/
  tw : Cfg ((Unit ⊕ Unit) ⊕ VW b) → Fin bT → Bool
  /-- The phase word. -/
  pw : Cfg ((Unit ⊕ Unit) ⊕ VW b) → Fin bP → Bool
  elem : ∀ g ∈ circ, g.cs.length ≤ 3
  classical : Classical circ
  compute : ∀ w : Cfg ((Unit ⊕ Unit) ⊕ VW b), cfgRun circ (Sum.elim w (fun _ => false)) =
    Sum.elim w (Sum.elim (Sum.elim (tw w) (pw w)) (fun _ => false))
  theta : ∀ w, |thetaVal (tw w) - 2 * Real.arctan ‖ckdec μ β q c0 w‖| ≤ ζ
  phi : ∀ w, ckdec μ β q c0 w ≠ 0 →
    ∃ m : ℤ, |phiVal (pw w) - Complex.arg (ckdec μ β q c0 w) - 2 * Real.pi * m| ≤ ζ

/-! ### The native factor and the native rotation -/

/-- **The native factor** of the clipped regime: the compute circuit of the signed regime, the
local qubits `(f, o, z)`, the decoder `[g] c₂` and the factor arithmetic placed on the branch and
value wires. -/
def clFO (k b : ℕ) {μ β c0 ξ : ℝ} {bT bP A : ℕ} (ar : ClipFactorArith b μ β c0 ξ bT bP A) :
    FactorOp (PRf k) (SZ k b) (PY k b) Query bT bP A where
  W := (computeV k b).map (NInstr.map (ιBe k b))
  loc := locF k
  dec := fun y => cfdec μ β c0 (inF y)
  circ := ar.circ.map (GateODE.Gate.map (Sum.map (ιFin k b) id))
  tw := fun y => ar.tw (inF y)
  pw := fun y => ar.pw (inF y)

/-- **The native rotation** of the clipped regime: the compute circuit of the signed regime, the
orientation `o` and the decoder `y(g, f, c₁, c₂)`. -/
def clND (k b : ℕ) (μ β q c0 : ℝ) : NativeOp Empty (PRf k) (SZ k b) (PY k b) Query where
  V := (computeV k b).map (NInstr.map (ιBe k b))
  o := locF k 1
  dec := fun y => ckdec μ β q c0 (inC y)

/-- The angle arithmetic placed on the branch, flag and value wires. -/
abbrev clAr (k b : ℕ) {μ β q c0 ζ : ℝ} {bT bP A : ℕ} (aa : ClipAngleArith b μ β q c0 ζ bT bP A) :
    Arith (NB Empty (PRf k) (SZ k b)) :=
  ⟨bT, bP, A, aa.circ.map (GateODE.Gate.map (Sum.map (ιCin k b) id)), fun y => aa.tw (inC y),
    fun y => aa.pw (inC y)⟩

theorem clFO_locB (k b : ℕ) {μ β c0 ξ : ℝ} {bT bP A : ℕ} (ar : ClipFactorArith b μ β c0 ξ bT bP A) :
    (clFO k b ar).locB = locBF k := rfl

/-- The public conditions of the native factor. -/
theorem clFO_public (k b : ℕ) {μ β c0 ξ : ℝ} {bT bP A : ℕ}
    (ar : ClipFactorArith b μ β c0 ξ bT bP A) : (clFO k b ar).Public where
  valid := valid_map_list (ιBe k b) (computeV k b) (computeV_valid k b)
  dec_indep x c := by
    change cfdec μ β c0 (inF (overwrite (clFO k b ar).locB x c)) = cfdec μ β c0 (inF x)
    rw [clFO_locB, inF_overwrite]
  dec_le x := norm_cfdec_le μ β c0 _

/-- Running a classical circuit placed on input wires on clean arithmetic wires. -/
theorem cfgRun_placed {I : Type*} [Fintype I] [DecidableEq I] {bT bP A : ℕ}
    (ι : I → NB Empty (PRf k) (SZ k b)) (hι : Function.Injective ι)
    (circ : List (Gate (I ⊕ AWr bT bP A))) (tw : Cfg I → Fin bT → Bool) (pw : Cfg I → Fin bP → Bool)
    (hcomp : ∀ w : Cfg I, cfgRun circ (Sum.elim w (fun _ => false)) =
      Sum.elim w (Sum.elim (Sum.elim (tw w) (pw w)) (fun _ => false)))
    (x : Cfg (NB Empty (PRf k) (SZ k b))) :
    cfgRun (circ.map (GateODE.Gate.map (Sum.map ι id))) (Sum.elim x (fun _ => false)) =
      Sum.elim x (Sum.elim (Sum.elim (tw (fun a => x (ι a))) (pw (fun a => x (ι a))))
        (fun _ => false)) := by
  have he : Function.Injective (Sum.map ι (id : AWr bT bP A → AWr bT bP A)) :=
    Sum.map_injective.mpr ⟨hι, Function.injective_id⟩
  have h1 : (fun a => (Sum.elim x (fun _ => false) : Cfg (NB Empty (PRf k) (SZ k b) ⊕
      AWr bT bP A)) (Sum.map ι id a)) = Sum.elim (fun a => x (ι a)) (fun _ => false) := by
    funext a
    rcases a with v | a <;> rfl
  rw [cfgRun_map he, h1, hcomp]
  funext w
  rcases w with m | a
  · by_cases hm : ∃ v, ι v = m
    · obtain ⟨v, rfl⟩ := hm
      exact overwrite_apply_ι he _ _ (Sum.inl v)
    · push Not at hm
      refine overwrite_apply_out _ _ _ _ ?_
      rintro (v | a) h
      · exact hm v (Sum.inl_injective h)
      · cases h
  · exact overwrite_apply_ι he _ _ (Sum.inr a)

/-- **The arithmetic conditions** of the native factor, from the scalar-arithmetic hypothesis. -/
theorem clFO_arith (k b : ℕ) {μ β c0 ξ : ℝ} {bT bP A : ℕ}
    (ar : ClipFactorArith b μ β c0 ξ bT bP A) : FactorArithOK (clFO k b ar) ξ where
  elem g hg := by
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    simpa [GateODE.Gate.map] using ar.elem g' hg'
  classical := classical_map (Sum.map_injective.mpr ⟨ιFin_injective, Function.injective_id⟩)
    ar.classical
  compute x := cfgRun_placed (ιFin k b) ιFin_injective ar.circ ar.tw ar.pw ar.compute x
  tw_indep x c := by
    change ar.tw (inF (overwrite (clFO k b ar).locB x c)) = ar.tw (inF x)
    rw [clFO_locB, inF_overwrite]
  pw_indep x c := by
    change ar.pw (inF (overwrite (clFO k b ar).locB x c)) = ar.pw (inF x)
    rw [clFO_locB, inF_overwrite]
  acc x := ar.acc (inF x)

/-- The public conditions of the native rotation. -/
theorem clND_public (k b : ℕ) (μ β q c0 : ℝ) : (clND k b μ β q c0).Public where
  valid := valid_map_list (ιBe k b) (computeV k b) (computeV_valid k b)
  dec_indep x v := by
    change ckdec μ β q c0 (inC (Function.update x (locBF k 1) v)) = ckdec μ β q c0 (inC x)
    rw [inC_update]

/-- **The arithmetic conditions** of the native rotation, from the angle-arithmetic hypothesis. -/
theorem clND_arith (k b : ℕ) {μ β q c0 ζ : ℝ} {bT bP A : ℕ}
    (aa : ClipAngleArith b μ β q c0 ζ bT bP A) :
    ArithOK (clAr k b aa) (Sum.inl (Sum.inr (clND k b μ β q c0).o)) (clND k b μ β q c0).dec ζ where
  elem g hg := by
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    simpa [GateODE.Gate.map] using aa.elem g' hg'
  classical := classical_map (Sum.map_injective.mpr ⟨ιCin_injective, Function.injective_id⟩)
    aa.classical
  compute x := cfgRun_placed (ιCin k b) ιCin_injective aa.circ aa.tw aa.pw aa.compute x
  tw_indep x v := by
    change aa.tw (inC (Function.update x (locBF k 1) v)) = aa.tw (inC x)
    rw [inC_update]
  pw_indep x v := by
    change aa.pw (inC (Function.update x (locBF k 1) v)) = aa.pw (inC x)
    rw [inC_update]
  theta x := aa.theta (inC x)
  phi x hx := aa.phi (inC x) hx

/-! ### The split of the private operation -/

/-- **The factor** `U_f = F† A F`: the stable signed factor `U(c₂)` of the correction branch
conjugated by the lifted locator. -/
def Uf (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  unconj ((FL (R := R) D en x)† ∘L AF D en μ β x ∘L FL D en x)

/-- **The rotation** `C = F† D(y) F`: the edge rotation of the located value conjugated by the
lifted locator. -/
def Cf (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    Anc (k + 3 + 1) (Reg (Fin k) R) →L[ℂ] Anc (k + 3 + 1) (Reg (Fin k) R) :=
  unconj ((FL (R := R) D en x)† ∘L LD D en μ β q x ∘L FL D en x)

/-- The algebra of the split: `(A F)† L (A F) = (F† A F)† (F† L F) (F† A F)` for `F F† = 1`. -/
theorem conj_split {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (F A L : V →L[ℂ] V) (hF : F ∘L F† = 1) :
    (A ∘L F)† ∘L L ∘L (A ∘L F) = (F† ∘L A ∘L F)† ∘L ((F† ∘L L ∘L F) ∘L (F† ∘L A ∘L F)) := by
  have hc : ∀ T : V →L[ℂ] V, F ∘L (F† ∘L T) = T := by
    intro T
    rw [← comp_assoc, hF, LargeSparsityCore.CayleyBlocks.one_comp]
  rw [adjoint_comp, adjoint_comp, adjoint_comp, adjoint_adjoint]
  simp only [comp_assoc]
  rw [hc, hc]

theorem FL_comp_adj (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    FL (R := R) D en x ∘L (FL (R := R) D en x)† = 1 := by
  have h := (FL_isUnitary (R := R) D en x).2
  rwa [star_eq_adjoint, mul_def] at h

/-- **The split of the private Cayley unitary** `D = U_f† C U_f`. -/
theorem clD_split (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    clD (R := R) D en μ β q x =
      (Uf (R := R) D en μ β x)† ∘L Cf (R := R) D en μ β q x ∘L Uf (R := R) D en μ β x := by
  rw [clD, Uf, Cf, ← unconj_adjoint, ← unconj_comp, ← unconj_comp, WF]
  exact congrArg unconj (conj_split _ _ _ (FL_comp_adj D en x))

theorem Uf_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    IsUnitary (Uf (R := R) D en μ β x) := by
  rw [Uf]
  apply unconj_isUnitary
  have hF := FL_isUnitary (R := R) D en x
  have hFa : IsUnitary ((FL (R := R) D en x)†) := by
    simpa [star_eq_adjoint] using hF.adjoint
  have h := (hFa.mul (AF_isUnitary (R := R) D en μ β x)).mul hF
  rwa [mul_def, mul_def] at h

theorem LD_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    IsUnitary (LD (R := R) D en μ β q x) := by
  rw [LD]
  exact condOp_isUnitary _ _ (fun y => ⟨edgeMat_unitary _, mul_eq_one_comm.1 (edgeMat_unitary _)⟩)

theorem Cf_isUnitary (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    IsUnitary (Cf (R := R) D en μ β q x) := by
  rw [Cf]
  apply unconj_isUnitary
  have hF := FL_isUnitary (R := R) D en x
  have hFa : IsUnitary ((FL (R := R) D en x)†) := by
    simpa [star_eq_adjoint] using hF.adjoint
  have h := (hFa.mul (LD_isUnitary (R := R) D en μ β q x)).mul hF
  rwa [mul_def, mul_def] at h

/-! ### The compute circuit -/

/-- **The compute circuit on clean scratch** is the lifted locator followed by the transported
permutation (`sgFO_compute`). -/
theorem clW_compute (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) :
    nrun (prims (R := R) D en x) ((computeV k b).map (NInstr.map (ιBe k b))) ∘L
        cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L liftE (FL (R := R) D en x) := by
  have h := compute_transport (Z := SZ k b) (ιEe k) _ _ _
    (compute_cleanEmb (R := R) (b := b) D en k0 hk0 x)
  have hV : nrun (prims (R := R) D en x) ((computeV k b).map (NInstr.map (ιBe k b))) =
      localOp (mapId (S := SZ k b) (ιEe k)) (mapId_injective (ιEe k).injective)
        (fun _ => nrun (prims (R := R) D en x) (computeV k b)) :=
    nrun_map _ (ιBe k b) (computeV k b)
  have hP : localOp (mapId (S := SZ k b) (ιEe k)) (mapId_injective (ιEe k).injective)
      (fun _ => permOp (Q := R) (sigma D en k0 x)) = permOp (sigF D en k0 x) :=
    localOp_permOp (ιBe k b) (sigma D en k0 x)
  have hF : localOp (ιEe k) (ιEe k).injective (fun _ => Fq (R := R) D en x) =
      liftE (FL (R := R) D en x) :=
    (liftE_FuF D en x).symm
  rw [hV, h, hP, hF]

/-- The transported permutation does not touch the branch wire. -/
theorem sigF_gBF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) : sigF D en k0 x y (gBF k b) = y (gBF k b) :=
  alongEquiv_apply_out _ _ _ _ (fun a => ιB_ne_gBF a)

/-! ### The native factor -/

/-- The correction entry of the located edge on the private register: `c₂` on the correction
branch, `0` on the bulk branch. -/
def cFE (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (z : Cfg (Empty ⊕ PRf k)) : ℂ :=
  if z (Sum.inr (gW k)) then cl2 D μ β x (edgeF en z) else 0

theorem cF_clear (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X)
    (w : Cfg (Empty ⊕ PRf k)) :
    cF D en μ β x (clearCfg (locF k) (fun a => w (Sum.inr a))) = cFE D en μ β x w := by
  have hg : clearCfg (locF k) (fun a => w (Sum.inr a)) (gW k) = w (Sum.inr (gW k)) :=
    clearCfg_apply_out _ _ _ (gW_ne_locF k)
  have he : edgeC en (clearCfg (locF k) (fun a => w (Sum.inr a))) = edgeF en w := by
    unfold edgeC edgeF
    congr 1
    funext e
    exact clearCfg_apply_out _ _ _ (fun i => edge_ne_locF k i e)
  unfold cF cFE
  rw [hg, he]

/-- The lifted factor of the frame on the private register. -/
theorem liftE_AF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β : ℝ) (x : X) :
    liftE (AF (R := R) D en μ β x) =
      localOp (locE k) (locE_injective k) (fun z => matOp (blk (uMat (cFE D en μ β x z)))) := by
  unfold liftE AF
  rw [localOp_localOp' Sum.inr_injective (locF k).injective (locE k) (locE_injective k)
      (fun _ => rfl) (fun _ y => matOp (blk (uMat (cF D en μ β x y))))]
  apply localOp_congr
  intro z
  rw [cF_clear]

theorem Udec_clFO {μ β c0 ξ : ℝ} {bT bP A : ℕ} (ar : ClipFactorArith b μ β c0 ξ bT bP A) :
    Udec (R := R) (clFO k b ar) = localOp (locBF (b := b) k) (locBF_injective k)
      (fun y => matOp (blk (uMat (cfdec μ β c0 (inF y))))) := rfl

/-- The entry of a matrix through the decoder of its value words. -/
theorem matrix_eq_gauss (D : Data X n (Cfg (VW b)) s) {c0 : ℝ}
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (x : X) (e : n × n) :
    (c0 : ℂ) * gauss (D.table x e) = D.matrix x e.1 e.2 := by
  rw [← hdec, ← D.decoded x e.1 e.2]

/-- The decoded correction entry of the computed value word is the correction entry of the
located edge. -/
theorem cfdec_sig (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β c0 : ℝ) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (c : Cfg (Empty ⊕ PRf k)) :
    cfdec μ β c0 (inF (clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false))))) =
      cFE D en μ β x (clearCfg (locE k) c) := by
  have hg : inF (clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false)))) (Sum.inl ()) =
      c (Sum.inr (gW k)) := by
    change clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false))) (gBF k b) = _
    rw [clearCfg_apply_out _ _ _ (fun i => locBF_ne_gBF i), sigF_gBF]
    rfl
  have hv : (fun v => inF (clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false))))
      (Sum.inr v)) = D.table x (edgeF en c) := by
    change valF (clearCfg (locBF k) (sigF D en k0 x (Sum.elim c (fun _ => false)))) = _
    rw [valF_overwrite_locBF, sigF_val]
  have hg' : clearCfg (locE k) c (Sum.inr (gW k)) = c (Sum.inr (gW k)) :=
    clearCfg_apply_out _ _ _ (fun i h => gW_ne_locF k i (Sum.inr_injective h))
  unfold cfdec cFE
  rw [hg, hg', hv, edgeF_overwrite, matrix_eq_gauss D hdec]
  rfl

/-- **The decoded factor commutes past the permutation** into the lifted factor of the frame. -/
theorem clFO_dec_comm (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β c0 : ℝ) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) {ξ : ℝ} {bT bP A : ℕ}
    (ar : ClipFactorArith b μ β c0 ξ bT bP A) :
    Udec (R := R) (clFO k b ar) ∘L permOp (sigF D en k0 x) ∘L cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L liftE (AF (R := R) D en μ β x) := by
  rw [Udec_clFO, liftE_AF]
  apply ext_bas_clm'
  intro c q
  simp only [comp_apply]
  rw [cleanEmb_bas, permOp_bas, localOp_bas, localOp_bas, matOp_bas', matOp_bas',
    put_sum_smul_bas, put_sum_smul_bas, map_sum, map_sum]
  have hd0 : (fun a => sigF D en k0 x (Sum.elim c (fun _ => false)) (locBF k a)) =
      fun a => c (locE k a) := by
    rw [sigF_locBF]
    rfl
  rw [hd0, cfdec_sig D en k0 x μ β c0 hdec c]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_smul, map_smul, cleanEmb_bas, permOp_bas, ← overwrite_locBF_elim, sigF_overwrite]

/-- **The native identity of the clipped factor** (`FactorNativeOK`): `W† U(c) W` acts on clean
scratch as the factor `U_f`. -/
theorem clFO_native (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (μ β c0 : ℝ)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) {ξ : ℝ} {bT bP A : ℕ}
    (ar : ClipFactorArith b μ β c0 ξ bT bP A) :
    FactorNativeOK (prims (R := R) D en x) (clFO k b ar)
      (selOp (fun _ : Cfg Empty => Uf (R := R) D en μ β x)) := by
  have hK1 := clW_compute (R := R) (b := b) D en k0 hk0 x
  have hK2 := clFO_dec_comm (R := R) D en k0 x μ β c0 hdec ar
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (clFO k b ar).W) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (clFO_public k b ar).valid
  have hFu : IsUnitary (liftE (FL (R := R) D en x)) := liftE_isUnitary (FL_isUnitary D en x)
  have hVV : (nrun (prims (R := R) D en x) (clFO k b ar).W)† ∘L
      nrun (prims (R := R) D en x) (clFO k b ar).W = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : liftE (FL (R := R) D en x) ∘L (liftE (FL (R := R) D en x))† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold FactorNativeOK
  rw [Uf, selOp_unconj, liftE_comp, liftE_comp, liftE_adjoint]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

/-! ### The native rotation -/

theorem liftE_LD (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ β q : ℝ) (x : X) :
    liftE (LD (R := R) D en μ β q x) = condOp (Sum.inr (locF k 1))
      (fun z => edgeMat (yCfg D en μ β q x (fun w => z (Sum.inr w)))) := by
  rw [LD]
  exact liftE_condOp _ _

theorem Rdec_clND (μ β q c0 : ℝ) :
    Rdec (R := R) (clND k b μ β q c0) =
      condOp (locBF k 1) (fun y => edgeMat (ckdec μ β q c0 (inC y))) := rfl

theorem update_locBF_eq (y : Cfg (NB Empty (PRf k) (SZ k b))) (v : Bool) :
    Function.update y (locBF k 1) v =
      overwrite (locBF k) y (Function.update (fun i => y (locBF k i)) 1 v) := by
  funext w
  by_cases hw : ∃ i, locBF (b := b) k i = w
  · obtain ⟨i, rfl⟩ := hw
    rw [overwrite_apply_ι (locBF_injective k)]
    by_cases hi : i = 1
    · subst hi
      simp
    · rw [Function.update_of_ne (fun h => hi (locBF_injective k h)), Function.update_of_ne hi]
  · push Not at hw
    rw [Function.update_of_ne (fun h => hw 1 h.symm), overwrite_apply_out _ _ _ _ hw]

/-- The transported permutation commutes with updating the orientation. -/
theorem sigF_update_o (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) (v : Bool) :
    sigF D en k0 x (Function.update y (locBF k 1) v) =
      Function.update (sigF D en k0 x y) (locBF k 1) v := by
  rw [update_locBF_eq, sigF_overwrite, update_locBF_eq (sigF D en k0 x y), sigF_locBF]

theorem sigF_o (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) : sigF D en k0 x y (locBF k 1) = y (locBF k 1) :=
  congrFun (sigF_locBF D en k0 x y) 1

/-- The decoded value of the computed words is the value of the located edge. -/
theorem ckdec_sig (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β q c0 : ℝ) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (c : Cfg (Empty ⊕ PRf k)) :
    ckdec μ β q c0 (inC (Function.update (sigF D en k0 x (Sum.elim c (fun _ => false)))
        (locBF k 1) false)) =
      yCfg D en μ β q x (fun w => Function.update c (Sum.inr (locF k 1)) false (Sum.inr w)) := by
  rw [inC_update]
  have hg : inC (sigF D en k0 x (Sum.elim c (fun _ => false))) (Sum.inl (Sum.inl ())) =
      c (Sum.inr (gW k)) := by
    change sigF D en k0 x (Sum.elim c (fun _ => false)) (gBF k b) = _
    rw [sigF_gBF]
    rfl
  have hf : inC (sigF D en k0 x (Sum.elim c (fun _ => false))) (Sum.inl (Sum.inr ())) =
      c (locE k 0) := by
    change sigF D en k0 x (Sum.elim c (fun _ => false)) (locBF k 0) = _
    rw [congrFun (sigF_locBF D en k0 x (Sum.elim c (fun _ => false))) 0]
    rfl
  have hv : (fun v => inC (sigF D en k0 x (Sum.elim c (fun _ => false))) (Sum.inr v)) =
      D.table x (edgeF en c) := by
    change valF (sigF D en k0 x (Sum.elim c (fun _ => false))) = _
    exact sigF_val D en k0 x c
  have hg' : Function.update c (Sum.inr (locF k 1)) false (Sum.inr (gW k)) = c (Sum.inr (gW k)) :=
    Function.update_of_ne (fun h => gW_ne_locF k 1 (Sum.inr_injective h).symm) _ _
  have hf' : Function.update c (Sum.inr (locF k 1)) false (Sum.inr (locF k 0)) = c (locE k 0) :=
    Function.update_of_ne (fun h => absurd ((locF k).injective (Sum.inr_injective h))
      (by decide)) _ _
  have he' : edgeC en (fun w => Function.update c (Sum.inr (locF k 1)) false (Sum.inr w)) =
      edgeF en c := by
    unfold edgeC edgeF
    congr 1
    funext e
    exact Function.update_of_ne (fun h => edge_ne_locF k 1 e (Sum.inr_injective h).symm) _ _
  unfold ckdec yCfg
  dsimp only
  rw [hg, hf, hv, hg', hf', he', matrix_eq_gauss D hdec]
  rfl

/-- **The decoded rotation commutes past the permutation** into the lifted edge rotation. -/
theorem clND_rdec (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ β q c0 : ℝ) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) :
    Rdec (R := R) (clND k b μ β q c0) ∘L permOp (sigF D en k0 x) ∘L cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L liftE (LD (R := R) D en μ β q x) := by
  rw [Rdec_clND, liftE_LD]
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
  rw [hcfg, sigF_update_o, sigF_o, ckdec_sig D en k0 x μ β q c0 hdec c]
  rfl

/-- **The native identity of the clipped rotation** (`NativeOK`): `V† R V` acts on clean scratch
as the rotation `C`. -/
theorem clND_native (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (μ β q c0 : ℝ)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) :
    NativeOK (prims (R := R) D en x) (clND k b μ β q c0)
      (selOp (fun _ : Cfg Empty => Cf (R := R) D en μ β q x)) := by
  have hK1 := clW_compute (R := R) (b := b) D en k0 hk0 x
  have hK2 := clND_rdec (R := R) D en k0 x μ β q c0 hdec
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (clND k b μ β q c0).V) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (clND_public k b μ β q c0).valid
  have hFu : IsUnitary (liftE (FL (R := R) D en x)) := liftE_isUnitary (FL_isUnitary D en x)
  have hVV : (nrun (prims (R := R) D en x) (clND k b μ β q c0).V)† ∘L
      nrun (prims (R := R) D en x) (clND k b μ β q c0).V = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : liftE (FL (R := R) D en x) ∘L (liftE (FL (R := R) D en x))† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold NativeOK
  rw [Cf, selOp_unconj, liftE_comp, liftE_comp, liftE_adjoint]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

/-! ### The native data of the clipped regime -/

theorem exists_zero_slot (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)) :
    ∃ m, D.slot m = zIdx en := by
  refine (hrange _).2 ⟨fun _ => false, ?_⟩
  unfold zIdx
  congr 1
  funext i
  simp [lowWord]

/-- **The native data of the clipped regime from binary sparse oracles**: the boundary gates of
`clippedIface`, the split `D = U_f† C U_f`, the native factor `clFO` with the factor arithmetic
`af` and the native rotation `clND` with the angle arithmetic `aa`, with their public, arithmetic
and native conditions, for entries stored as `b`-bit two's complement components with decoder
`c₀ (X + iY)` (`hdec`). -/
def clipNative (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {σ θ ε μ η : ℝ} (Rg : LargeSparsityCore.Parameters.Regime σ θ ε) (hμ : 0 < μ)
    (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ)
    {c0 : ℝ} (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) {ξ ζ : ℝ} {bT bP A : ℕ}
    (af : ClipFactorArith b μ (LargeSparsityCore.Parameters.hval θ ε) c0 ξ bT bP A)
    (aa : ClipAngleArith b μ (LargeSparsityCore.Parameters.hval θ ε)
      (LargeSparsityCore.Parameters.qval σ θ ε) c0 ζ bT bP A) :
    ClipNative (prims (R := R) D en x)
      (clippedIface (R := R) D en sb hsb hs hrange Rg hμ hσ x hH hrow hcol hent).UJ
      (clippedIface (R := R) D en sb hsb hs hrange Rg hμ hσ x hH hrow hcol hent).D (SZ k b)
      bT bP A ξ ζ where
  UJg := clUJg k sb hsb
  ok := clUJg_ok sb hsb
  boundary := rfl
  Uf := Uf (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε) x
  Cf := Cf (R := R) D en μ (LargeSparsityCore.Parameters.hval θ ε)
    (LargeSparsityCore.Parameters.qval σ θ ε) x
  unitaryU := Uf_isUnitary D en μ _ x
  unitaryC := Cf_isUnitary D en μ _ _ x
  split := clD_split D en μ _ _ x
  fo := clFO k b af
  fpub := clFO_public k b af
  farith := clFO_arith k b af
  fnative := by
    obtain ⟨k0, hk0⟩ := exists_zero_slot D en sb hrange
    exact clFO_native D en k0 hk0 x μ _ c0 hdec af
  nd := clND k b μ (LargeSparsityCore.Parameters.hval θ ε)
    (LargeSparsityCore.Parameters.qval σ θ ε) c0
  cpub := clND_public k b _ _ _ _
  circ := (clAr k b aa).circ
  tw := (clAr k b aa).tw
  pw := (clAr k b aa).pw
  carith := clND_arith k b aa
  cnative := by
    obtain ⟨k0, hk0⟩ := exists_zero_slot D en sb hrange
    exact clND_native D en k0 hk0 x μ _ _ c0 hdec

end

end GateOptimalBinary
