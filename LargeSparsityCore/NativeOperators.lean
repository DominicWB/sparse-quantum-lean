import LargeSparsityCore.NativeLocal
import LargeSparsityCore.CayleyBlocks
import SparseHamiltonian.NativeCleanConjugation

set_option autoImplicit false

/-!
# The joint private operators on the native workspace

The private space of the large-sparsity core is the released logical native workspace
(`SparseHamiltonian.OrientedNativeLayout.Space`): an orientation bit, an edge, a value word and a
three-valued flag. The flags `0, 1` carry the signed correction factor (success and failure, as in
`NativeSignedFactor`), the flag `2` carries the clipped edge generator.

The construction uses one unitary frame `𝒰(x) = G ∘ V(x) ∘ L(x)` (`U`; `G` is `frame`): the two
locators `L(x)`, the value oracle `V(x)` computing the entry word, and the known word-controlled
local gate `G` with `NativeSignedFactor.localOp c₂` at every address (`c₂` the correction entry
of the word). In this frame every private operator is a known diagonal operator (`dg`), with
eigenvalues (`kappa`)

* `±2q` on the success flag, according to the orientation (the `±` label of the local factor),
* `0` on the failure flag,
* `±2q |c₁|` on the clipped flag `2`.

Accordingly (`opt:eq:joint-lift`) the generator is `K(x) = 𝒰† Λ_K 𝒰` (`Kop`), its Cayley transform
`D(x) = 𝒰† Λ_D 𝒰` (`Dop`, with `Λ_D = λ(Λ_K)`, `λ(κ) = 1 - 2/(1 + iκ)`), and the isolated
spectral projections are `P_± = 𝒰† Π_± 𝒰` on the two success labels (`Ppl`, `Pmi`). The block
structure `CayleyBlocks.Spectral` holds exactly (`spectral`), `D` is unitary (`Dop_isometry`) and
the bulk satisfies `‖R₁ P₀‖ ≤ (1 + 2q/β)/2` (`norm_R1_bulk_le`), since `β |c₁| ≤ 1`.

`D(x)` is the evaluation of an explicit logical program (`logicalProgram`): the two locators, the
value oracle, the known gate `G† Λ_D G`, the inverse value oracle and the two inverse locators,
six masked native calls (`logicalProgram_eval`, `logicalProgram_count`).
-/

namespace LargeSparsityCore.Native

noncomputable section

open ContinuousLinearMap SparseHamiltonian NativeSignedFactor OrientedNativeLayout
open NativeSparseBlockEncoding OracleCircuit CayleyBlocks
open scoped InnerProduct ComplexConjugate

/-! ### Conjugation of the block structure -/

section Conj

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The block structure is invariant under conjugation by a unitary. -/
theorem spectral_conj {K D Pp Pm U : V →L[ℂ] V} {q : ℝ} (h : Spectral K D Pp Pm q)
    (hU1 : U† ∘L U = 1) (hU2 : U ∘L U† = 1) :
    Spectral (U† ∘L K ∘L U) (U† ∘L D ∘L U) (U† ∘L Pp ∘L U) (U† ∘L Pm ∘L U) q := by
  have key : ∀ A B : V →L[ℂ] V, (U† ∘L A ∘L U) ∘L (U† ∘L B ∘L U) = U† ∘L (A ∘L B) ∘L U := by
    intro A B
    calc (U† ∘L A ∘L U) ∘L (U† ∘L B ∘L U) = U† ∘L A ∘L (U ∘L U†) ∘L B ∘L U := by
          simp only [comp_assoc]
      _ = _ := by rw [hU2, CayleyBlocks.one_comp]; simp only [comp_assoc]
  have hadj : ∀ A : V →L[ℂ] V, IsSelfAdjoint A → IsSelfAdjoint (U† ∘L A ∘L U) := by
    intro A hA
    change (U† ∘L A ∘L U)† = U† ∘L A ∘L U
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, hA.adjoint_eq, comp_assoc]
  have hone : U† ∘L (1 : V →L[ℂ] V) ∘L U = 1 := by
    rw [CayleyBlocks.one_comp, hU1]
  have hR1 : R1 (U† ∘L K ∘L U) = U† ∘L R1 K ∘L U := by
    simp only [R1, comp_smul, smul_comp, comp_add, add_comp, hone]
  have hsub : ∀ A : V →L[ℂ] V, 1 - U† ∘L A ∘L U = U† ∘L (1 - A) ∘L U := by
    intro A
    rw [sub_comp, comp_sub, hone]
  refine ⟨hadj K h.self, ?_, ?_, hadj Pp h.pp_adj, hadj Pm h.pm_adj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [key, h.pp_idem]
  · rw [key, h.pm_idem]
  · rw [key, h.pp_pm, zero_comp, comp_zero]
  · rw [key, h.pm_pp, zero_comp, comp_zero]
  · rw [key, h.k_pp, smul_comp, comp_smul]
  · rw [key, h.k_pm, smul_comp, comp_smul]
  · rw [hR1, hsub, key, h.cayley_right, hone]
  · rw [hR1, hsub, key, h.cayley_left, hone]

theorem conj_comp {W A B : V →L[ℂ] V} (hW2 : W ∘L W† = 1) :
    (W† ∘L A ∘L W) ∘L (W† ∘L B ∘L W) = W† ∘L (A ∘L B) ∘L W := by
  calc (W† ∘L A ∘L W) ∘L (W† ∘L B ∘L W) = W† ∘L A ∘L (W ∘L W†) ∘L B ∘L W := by
        simp only [comp_assoc]
    _ = _ := by rw [hW2, CayleyBlocks.one_comp]; simp only [comp_assoc]

theorem conj_one {W : V →L[ℂ] V} (hW1 : W† ∘L W = 1) : W† ∘L (1 : V →L[ℂ] V) ∘L W = 1 := by
  rw [CayleyBlocks.one_comp, hW1]

theorem conj_sub (W A B : V →L[ℂ] V) : W† ∘L (A - B) ∘L W = W† ∘L A ∘L W - W† ∘L B ∘L W := by
  rw [sub_comp, comp_sub]

theorem conj_isometry {W A : V →L[ℂ] V} (hW1 : W† ∘L W = 1) (hW2 : W ∘L W† = 1)
    (hA : A† ∘L A = 1) : (W† ∘L A ∘L W)† ∘L (W† ∘L A ∘L W) = 1 := by
  have e : (W† ∘L A ∘L W)† = W† ∘L A† ∘L W := by
    rw [adjoint_comp, adjoint_comp, adjoint_adjoint, comp_assoc]
  rw [e, conj_comp hW2, hA, conj_one hW1]

theorem R1_conj {W K : V →L[ℂ] V} (hW1 : W† ∘L W = 1) :
    R1 (W† ∘L K ∘L W) = W† ∘L R1 K ∘L W := by
  simp only [R1, comp_smul, smul_comp, comp_add, add_comp, conj_one hW1]

theorem bulk_conj {W A B : V →L[ℂ] V} (hW1 : W† ∘L W = 1) :
    CayleyBlocks.bulk (W† ∘L A ∘L W) (W† ∘L B ∘L W) = W† ∘L CayleyBlocks.bulk A B ∘L W := by
  rw [CayleyBlocks.bulk, CayleyBlocks.bulk, conj_sub, conj_sub, conj_one hW1]

end Conj

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-! ### Diagonal operators -/

/-- Multiplication by `m b a f` on the basis state with orientation `b`, address `a` and flag
`f`. -/
def dg (m : Bool → Adr n Z → Fin 3 → ℂ) : Space n Z →L[ℂ] Space n Z :=
  WeightedClock.diagonal (fun b => RelativeAmplitudeError.complexDiagonal
    (fun a : NativeSparseMaskedAccess.Basis n Z => m b a.1 a.2))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem dg_apply (m : Bool → Adr n Z → Fin 3 → ℂ) (v : Space n Z) (b : Bool)
    (a : Adr n Z) (f : Fin 3) : dg m v b (a, f) = m b a f * v b (a, f) := rfl

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_comp (m m' : Bool → Adr n Z → Fin 3 → ℂ) :
    dg m ∘L dg m' = dg (fun b a f => m b a f * m' b a f) := by
  ext v b x
  rcases x with ⟨a, f⟩
  simp only [comp_apply, dg_apply]
  ring

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_adjoint (m : Bool → Adr n Z → Fin 3 → ℂ) :
    (dg m)† = dg (fun b a f => star (m b a f)) := by
  unfold dg
  rw [WeightedClock.diagonal_adjoint]
  congr 1
  funext b
  rw [RelativeAmplitudeError.complexDiagonal_adjoint]

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_one : dg (fun _ _ _ => (1 : ℂ)) = (1 : Space n Z →L[ℂ] Space n Z) := by
  ext v b x
  rcases x with ⟨a, f⟩
  simp

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_zero : dg (fun _ _ _ => (0 : ℂ)) = (0 : Space n Z →L[ℂ] Space n Z) := by
  ext v b x
  rcases x with ⟨a, f⟩
  simp

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_add (m m' : Bool → Adr n Z → Fin 3 → ℂ) :
    dg m + dg m' = dg (fun b a f => m b a f + m' b a f) := by
  ext v b x
  rcases x with ⟨a, f⟩
  simp only [add_apply, PiLp.add_apply, dg_apply]
  ring

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_sub (m m' : Bool → Adr n Z → Fin 3 → ℂ) :
    dg m - dg m' = dg (fun b a f => m b a f - m' b a f) := by
  ext v b x
  rcases x with ⟨a, f⟩
  simp only [sub_apply, PiLp.sub_apply, dg_apply]
  ring

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_smul (c : ℂ) (m : Bool → Adr n Z → Fin 3 → ℂ) :
    c • dg m = dg (fun b a f => c * m b a f) := by
  ext v b x
  rcases x with ⟨a, f⟩
  simp only [smul_apply, PiLp.smul_apply, dg_apply, smul_eq_mul]
  ring

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem dg_congr {m m' : Bool → Adr n Z → Fin 3 → ℂ} (h : ∀ b a f, m b a f = m' b a f) :
    dg m = dg m' := by
  congr 1
  funext b a f
  exact h b a f

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
theorem norm_dg_le (m : Bool → Adr n Z → Fin 3 → ℂ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ b a f, ‖m b a f‖ ≤ δ) : ‖dg m‖ ≤ δ :=
  WeightedClock.norm_diagonal_le _ δ hδ (fun b =>
    RelativeAmplitudeError.norm_complexDiagonal_le _ δ hδ (fun x => h b x.1 x.2))

/-! ### The eigenvalues -/

/-- The orientation sign: `+1` on the row orientation (`false`), `-1` on the column orientation. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- The clipped entry `c₁` of the word at an address. -/
def c1 (D : Data X n Z s) (η β : ℝ) (a : Adr n Z) : ℂ := cclip η β (D.decode a.1 a.2)

/-- The correction entry `c₂` of the word at an address. -/
def c2 (D : Data X n Z s) (η β : ℝ) (a : Adr n Z) : ℂ := ccorr η β (D.decode a.1 a.2)

/-- The eigenvalues of the private generator in the local frame: `2q s(b)` on the success
flag `0`, zero on the failure flag `1` and `2q|c₁| s(b)` on the clipped flag `2`. -/
def kappa (D : Data X n Z s) (η β q : ℝ) (b : Bool) (a : Adr n Z) (f : Fin 3) : ℝ :=
  if f = 0 then 2 * q * sgn b else if f = 1 then 0 else 2 * q * ‖c1 D η β a‖ * sgn b

/-- The Cayley eigenvalue `λ(κ) = 1 - 2/(1 + iκ)`. -/
def cay (κ : ℝ) : ℂ := 1 - 2 / (1 + κ * Complex.I)

/-- The indicator of the `+` success label. -/
def ipl (b : Bool) (f : Fin 3) : ℂ := if b = false ∧ f = 0 then 1 else 0

/-- The indicator of the `-` success label. -/
def imi (b : Bool) (f : Fin 3) : ℂ := if b = true ∧ f = 0 then 1 else 0

theorem one_add_ne_zero (κ : ℝ) : 1 + (κ : ℂ) * Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem cay_cayley (κ : ℝ) : (1 - cay κ) * ((2 : ℂ)⁻¹ * (1 + Complex.I * κ)) = 1 := by
  have h := one_add_ne_zero κ
  unfold cay
  field_simp
  ring

theorem star_cay_mul (κ : ℝ) : star (cay κ) * cay κ = 1 := by
  have h := one_add_ne_zero κ
  have h' : (1 - (κ : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  have e : cay κ = ((κ : ℂ) * Complex.I - 1) / (1 + (κ : ℂ) * Complex.I) := by
    unfold cay
    field_simp
    ring
  have es : star (cay κ) = (-(κ : ℂ) * Complex.I - 1) / (1 - (κ : ℂ) * Complex.I) := by
    rw [e, Complex.star_def, map_div₀, map_sub, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, map_one]
    ring
  rw [es, e, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero h' h)]
  ring

/-! ### The frame -/

/-- The value-controlled local frame: the correction factor's local gate `localOp c₂` at every
address. -/
def frame (D : Data X n Z s) (η β : ℝ) : Space n Z →L[ℂ] Space n Z :=
  (addrLayout (n := n) (Z := Z)).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun a : Adr n Z => localOp (c2 D η β a)))

omit [AddCommGroup Z] [DecidableEq Z] in
theorem frame_unitary (D : Data X n Z s) (η β : ℝ) : IsUnitary (frame D η β) := by
  have h : IsUnitary (WeightedClock.diagonal (fun a : Adr n Z => localOp (c2 D η β a))) :=
    NativeMaskedOracle.diagonal_unitary _
      (fun a => localOp_unitary (norm_ccorr_le_one (η := η) (β := β) (D.decode a.1 a.2)))
  exact h.transport addrLayout.symm

omit [AddCommGroup Z] [DecidableEq Z] in
theorem frame_apply (D : Data X n Z s) (η β : ℝ) (v : Space n Z) (b : Bool) (e : n × n) (z : Z)
    (f : Fin 3) :
    frame D η β v b ((e, z), f) = ∑ b', ∑ f', orient (c2 D η β (e, z)) b b' *
      flagRot (c2 D η β (e, z)) f f' * v b' ((e, z), f') := by
  change localOp (c2 D η β (e, z)) (addrLayout v (e, z)) (b, f) = _
  rw [localOp_apply]
  rfl

/-- The frame `𝒰(x) = G ∘ V(x) ∘ L(x)`. -/
def U (D : Data X n Z s) (η β : ℝ) (x : X) : Space n Z →L[ℂ] Space n Z :=
  frame D η β ∘L logicalOracle D .value x ∘L (locatorProgram D).eval x

omit [DecidableEq Z] in
theorem U_unitary (D : Data X n Z s) (η β : ℝ) (x : X) : IsUnitary (U D η β x) :=
  (frame_unitary D η β).mul ((logicalOracle_unitary D .value x).mul
    ((locatorProgram D).eval_unitary (logicalOracle_unitary D) x))

omit [DecidableEq Z] in
theorem U_isometry (D : Data X n Z s) (η β : ℝ) (x : X) :
    (U D η β x)† ∘L U D η β x = 1 := (U_unitary D η β x).1

omit [DecidableEq Z] in
theorem U_coisometry (D : Data X n Z s) (η β : ℝ) (x : X) :
    U D η β x ∘L (U D η β x)† = 1 := (U_unitary D η β x).2

/-! ### The private operators -/

/-- The diagonal generator `Λ_K`. -/
def LamK (D : Data X n Z s) (η β q : ℝ) : Space n Z →L[ℂ] Space n Z :=
  dg (fun b a f => (kappa D η β q b a f : ℂ))

/-- The diagonal Cayley transform `Λ_D = λ(Λ_K)`. -/
def LamD (D : Data X n Z s) (η β q : ℝ) : Space n Z →L[ℂ] Space n Z :=
  dg (fun b a f => cay (kappa D η β q b a f))

/-- The diagonal projection on the `+` success label. -/
def LamP : Space n Z →L[ℂ] Space n Z := dg (fun b _ f => ipl b f)

/-- The diagonal projection on the `-` success label. -/
def LamM : Space n Z →L[ℂ] Space n Z := dg (fun b _ f => imi b f)

/-- The private generator `K(x) = 𝒰† Λ_K 𝒰` (`opt:eq:joint-lift`). -/
def Kop (D : Data X n Z s) (η β q : ℝ) (x : X) : Space n Z →L[ℂ] Space n Z :=
  (U D η β x)† ∘L LamK D η β q ∘L U D η β x

/-- The private Cayley operator `D(x) = 𝒰† λ(Λ_K) 𝒰`. -/
def Dop (D : Data X n Z s) (η β q : ℝ) (x : X) : Space n Z →L[ℂ] Space n Z :=
  (U D η β x)† ∘L LamD D η β q ∘L U D η β x

/-- The isolated projection `P₊`. -/
def Ppl (D : Data X n Z s) (η β : ℝ) (x : X) : Space n Z →L[ℂ] Space n Z :=
  (U D η β x)† ∘L LamP ∘L U D η β x

/-- The isolated projection `P₋`. -/
def Pmi (D : Data X n Z s) (η β : ℝ) (x : X) : Space n Z →L[ℂ] Space n Z :=
  (U D η β x)† ∘L LamM ∘L U D η β x

omit [AddCommGroup Z] [DecidableEq Z] in
theorem R1_LamK (D : Data X n Z s) (η β q : ℝ) :
    R1 (LamK D η β q) = dg (fun b a f => (2 : ℂ)⁻¹ * (1 + Complex.I * kappa D η β q b a f)) := by
  rw [R1, LamK, dg_smul, ← dg_one, dg_add, dg_smul]

omit [AddCommGroup Z] [DecidableEq Z] in
/-- The block structure of the diagonal data. -/
theorem spectral_diag (D : Data X n Z s) (η β q : ℝ) :
    Spectral (LamK D η β q) (LamD D η β q) LamP LamM q := by
  have hself : ∀ m : Bool → Adr n Z → Fin 3 → ℂ, (∀ b a f, star (m b a f) = m b a f) →
      IsSelfAdjoint (dg m) := by
    intro m hm
    change (dg m)† = dg m
    rw [dg_adjoint]
    exact dg_congr hm
  refine ⟨hself _ (fun b a f => Complex.conj_ofReal _), ?_, ?_,
    hself _ (fun b a f => by unfold ipl; split_ifs <;> simp),
    hself _ (fun b a f => by unfold imi; split_ifs <;> simp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [LamP, dg_comp]
    exact dg_congr (fun b a f => by unfold ipl; split_ifs <;> simp)
  · rw [LamM, dg_comp]
    exact dg_congr (fun b a f => by unfold imi; split_ifs <;> simp)
  · rw [LamP, LamM, dg_comp, ← dg_zero]
    exact dg_congr (fun b a f => by unfold ipl imi; cases b <;> simp)
  · rw [LamP, LamM, dg_comp, ← dg_zero]
    exact dg_congr (fun b a f => by unfold ipl imi; cases b <;> simp)
  · rw [LamK, LamP, dg_comp, dg_smul]
    refine dg_congr (fun b a f => ?_)
    unfold ipl kappa sgn
    by_cases hb : b = false <;> by_cases hf : f = 0 <;> simp [hb, hf]
  · rw [LamK, LamM, dg_comp, dg_smul]
    refine dg_congr (fun b a f => ?_)
    unfold imi kappa sgn
    by_cases hb : b = true <;> by_cases hf : f = 0 <;> simp [hb, hf]
  · rw [R1_LamK, LamD, ← dg_one, dg_sub, dg_comp]
    exact dg_congr (fun b a f => cay_cayley _)
  · rw [R1_LamK, LamD, ← dg_one, dg_sub, dg_comp]
    exact dg_congr (fun b a f => by rw [mul_comm]; exact cay_cayley _)

omit [DecidableEq Z] in
/-- **The block structure of the joint representation.** -/
theorem spectral (D : Data X n Z s) (η β q : ℝ) (x : X) :
    Spectral (Kop D η β q x) (Dop D η β q x) (Ppl D η β x) (Pmi D η β x) q :=
  spectral_conj (spectral_diag D η β q) (U_isometry D η β x) (U_coisometry D η β x)

omit [AddCommGroup Z] [DecidableEq Z] in
theorem LamD_isometry (D : Data X n Z s) (η β q : ℝ) : (LamD D η β q)† ∘L LamD D η β q = 1 := by
  rw [LamD, dg_adjoint, dg_comp, ← dg_one]
  exact dg_congr (fun b a f => star_cay_mul _)

omit [AddCommGroup Z] [DecidableEq Z] in
theorem LamD_coisometry (D : Data X n Z s) (η β q : ℝ) :
    LamD D η β q ∘L (LamD D η β q)† = 1 := by
  rw [LamD, dg_adjoint, dg_comp, ← dg_one]
  exact dg_congr (fun b a f => by rw [mul_comm]; exact star_cay_mul _)

omit [DecidableEq Z] in
theorem Dop_isometry (D : Data X n Z s) (η β q : ℝ) (x : X) :
    (Dop D η β q x)† ∘L Dop D η β q x = 1 :=
  conj_isometry (U_isometry D η β x) (U_coisometry D η β x) (LamD_isometry D η β q)

/-- The norm of a conjugate by a unitary is at most the norm of the operator. -/
theorem norm_conj_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (W A : V →L[ℂ] V) (hW : W† ∘L W = 1) : ‖W† ∘L A ∘L W‖ ≤ ‖A‖ := by
  have hWn : ‖W‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro v
    have hh := (norm_map_iff_adjoint_comp_self W).mpr hW v
    simpa only [one_mul] using hh.le
  have hWa : ‖W†‖ ≤ 1 := by rw [LinearIsometryEquiv.norm_map]; exact hWn
  calc ‖W† ∘L A ∘L W‖ ≤ ‖W†‖ * (‖A‖ * ‖W‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by gcongr
    _ = ‖A‖ := by ring

omit [DecidableEq Z] in
/-- **The bulk bound**: `‖R₁ P₀‖ ≤ (1 + 2q/β)/2`, since `β |c₁| ≤ 1` on every word. -/
theorem norm_R1_bulk_le (D : Data X n Z s) {η β q : ℝ} (hη : 0 < η) (hβ : 0 < β)
    (hq : 0 ≤ q) (x : X) :
    ‖R1 (Kop D η β q x) ∘L CayleyBlocks.bulk (Ppl D η β x) (Pmi D η β x)‖ ≤
      (1 + 2 * q / β) / 2 := by
  have hprod : R1 (Kop D η β q x) ∘L CayleyBlocks.bulk (Ppl D η β x) (Pmi D η β x) =
      (U D η β x)† ∘L (R1 (LamK D η β q) ∘L (1 - LamP - LamM)) ∘L U D η β x := by
    rw [Kop, Ppl, Pmi, R1_conj (U_isometry D η β x), bulk_conj (U_isometry D η β x),
      conj_comp (U_coisometry D η β x), CayleyBlocks.bulk]
  rw [hprod]
  refine (norm_conj_le _ _ (U_isometry D η β x)).trans ?_
  rw [R1_LamK, LamP, LamM, ← dg_one, dg_sub, dg_sub, dg_comp]
  apply norm_dg_le _ (by positivity)
  intro b a f
  have hc := mul_norm_cclip_le (z := D.decode a.1 a.2) hη hβ.le
  have hc0 : 0 ≤ ‖c1 D η β a‖ := norm_nonneg _
  have hcq : 2 * q * ‖c1 D η β a‖ ≤ 2 * q / β := by
    rw [le_div_iff₀ hβ]
    have : β * ‖c1 D η β a‖ ≤ 1 := hc
    nlinarith
  have hI : ∀ t : ℝ, ‖(2 : ℂ)⁻¹ * (1 + Complex.I * t)‖ ≤ (1 + |t|) / 2 := by
    intro t
    rw [norm_mul, norm_inv, Complex.norm_two]
    have h1 : ‖(1 : ℂ) + Complex.I * t‖ ≤ 1 + |t| := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith
  show ‖(2 : ℂ)⁻¹ * (1 + Complex.I * (kappa D η β q b a f : ℂ)) * (1 - ipl b f - imi b f)‖ ≤ _
  by_cases hf0 : f = 0
  · have hz : (1 : ℂ) - ipl b f - imi b f = 0 := by
      subst hf0
      cases b <;> simp [ipl, imi]
    rw [hz, mul_zero, norm_zero]
    positivity
  · have hz : (1 : ℂ) - ipl b f - imi b f = 1 := by simp [ipl, imi, hf0]
    rw [hz, mul_one]
    refine (hI _).trans ?_
    have hk : |kappa D η β q b a f| ≤ 2 * q / β := by
      unfold kappa
      rw [if_neg hf0]
      split_ifs with hf1
      · rw [abs_zero]
        positivity
      · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * q * ‖c1 D η β a‖)]
        have : |sgn b| = 1 := by unfold sgn; split_ifs <;> simp
        rw [this, mul_one]
        exact hcq
    linarith

/-! ### The logical program -/

/-- The known gate `G† Λ_D G` on the computed word. -/
def phaseGate (D : Data X n Z s) (η β q : ℝ) : Space n Z →L[ℂ] Space n Z :=
  (frame D η β)† ∘L LamD D η β q ∘L frame D η β

omit [AddCommGroup Z] [DecidableEq Z] in
theorem phaseGate_unitary (D : Data X n Z s) (η β q : ℝ) : IsUnitary (phaseGate D η β q) := by
  have hF := frame_unitary D η β
  have hLU : IsUnitary (LamD D η β q) := ⟨LamD_isometry D η β q, LamD_coisometry D η β q⟩
  have hFa : IsUnitary ((frame D η β)†) := hF.adjoint
  exact hFa.mul (hLU.mul hF)

/-- Compute the entry word, apply the known gate, uncompute: two value calls. -/
def valueProgram (D : Data X n Z s) (η β q : ℝ) :
    MultiOracleCircuit.Program (logicalOracle D) :=
  .seq (.queryAdjoint .value) (.seq (.fixed (phaseGate D η β q) (phaseGate_unitary D η β q))
    (.query .value))

section Generic

variable {K L Y : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Evaluation of a conjugated value program, for an arbitrary oracle family. -/
theorem eval_conj_program {O : L → Y → K →L[ℂ] K} (pF : MultiOracleCircuit.Program O)
    (G : K →L[ℂ] K) (hG : IsUnitary G) (l : L) (y : Y) :
    (NativeCleanConjugation.program pF
      (.seq (.queryAdjoint l) (.seq (.fixed G hG) (.query l)))).eval y =
        (pF.eval y)† ∘L (O l y)† ∘L G ∘L O l y ∘L pF.eval y := by
  rw [NativeCleanConjugation.program, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_adjoint, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_queryAdjoint,
    MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
    MultiOracleCircuit.Program.eval_query]
  simp only [mul_def, ContinuousLinearMap.star_eq_adjoint, comp_assoc]

end Generic

/-- The logical program of the private Cayley operator: the locators, the value program and the
inverse locators. -/
def logicalProgram (D : Data X n Z s) (η β q : ℝ) :
    MultiOracleCircuit.Program (logicalOracle D) :=
  NativeCleanConjugation.program (locatorProgram D) (valueProgram D η β q)

omit [DecidableEq Z] in
@[simp] theorem logicalProgram_count (D : Data X n Z s) (η β q : ℝ) :
    (logicalProgram D η β q).count = 6 := by
  rw [logicalProgram, NativeCleanConjugation.program_count, locatorProgram_count]
  rfl

omit [DecidableEq Z] in
/-- Two row-locator, two column-locator and two value calls. -/
theorem logicalProgram_cost (D : Data X n Z s) (η β q : ℝ) (w : Query → ℕ) :
    (logicalProgram D η β q).cost w =
      2 * w .rowLocation + 2 * w .columnLocation + 2 * w .value := by
  rw [logicalProgram, NativeCleanConjugation.program_cost, locatorProgram_cost]
  change 2 * (w .rowLocation + w .columnLocation) + (w .value + (0 + w .value)) = _
  ring

omit [DecidableEq Z] in
/-- The logical program evaluates to the private Cayley operator. -/
theorem logicalProgram_eval (D : Data X n Z s) (η β q : ℝ) (x : X) :
    (logicalProgram D η β q).eval x = Dop D η β q x := by
  rw [logicalProgram, valueProgram, eval_conj_program]
  unfold Dop U phaseGate
  rw [adjoint_comp, adjoint_comp, comp_assoc, comp_assoc, comp_assoc, comp_assoc]

end

end LargeSparsityCore.Native
