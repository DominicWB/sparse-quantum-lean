import GateEfficientBinaryODE.Native

/-!
# The decoder of the four-sector private operation

The decoder `decO` of `Arith` reads, after the compute circuit, the stored entries `W₁` of the
located edge `(i, j)` and `W₂` of the transposed edge `(j, i)`, the part and the tag bit and the
label. With the decoder scale `c₀` of the stored entries (`M_ij = c₀ (X + i Y)`) every value of
the edgewise Cayley gate of the four-sector operation is

`γ' √(4s) / ρ · c₀ / 4 · μ' · c_t (A_x + i A_y)`  (`core_identity`),

for the Cayley parameter `γ'`, with `μ' = k_w` (the LCHS node) on the dissipative and `1` on the
Hamiltonian part. For the public parameters `p` of the solver (`layOf`: the LCHS grid of `p`, a
rounded LCHS step `Hn ≈ 2^F h`), the LCHS node of a label is `k_w = n_w h` (`nodeW_eq`) and its
Cayley parameter is `γ' = γ dur / T = γ d / 2^(k_T)` (`dur_div`; `k_T = p.k` the node bits), so
the decoder with scale `κ = γ √(4s) c₀ / (2^(k_T + F + 10) ρ)` and factor `ρ_L = 2^F h / Hn`
satisfies the decoder hypothesis `DecOK` (`decOK`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary
open SparseHamiltonian.GateODE (Params Label padIdx)
open NativeSparseBlockEncoding (Data)
open GatePointerEncoding (wordValue)

section Entries

variable {n : Type*}

/-- The tag split of the entries `M i j`, `M j i`, as a number. -/
def ctC (M : Matrix n n ℂ) (i j : n) : ℂ :=
  (if M i j = 0 then 0 else 1) * (2 - (if M j i = 0 then 0 else 1))

theorem tagZero_eq (M K : Matrix n n ℂ) (i j : n) :
    ODETaggedSupport.tagZero M K i j = ctC M i j / 2 * K i j := by
  unfold ODETaggedSupport.tagZero ctC
  by_cases h1 : M i j = 0 <;> by_cases h2 : M j i = 0 <;> simp [h1, h2]
  ring

theorem tagOne_swap_eq (M K : Matrix n n ℂ) (i j : n) :
    ODETaggedSupport.tagOne M K j i = ctC M i j / 2 * K j i := by
  unfold ODETaggedSupport.tagOne ctC
  by_cases h1 : M i j = 0 <;> by_cases h2 : M j i = 0 <;> simp [h1, h2]
  ring

theorem gauss_eq_zero (c0 : ℝ) (hc0 : c0 ≠ 0) (X Y : ℤ) :
    (c0 : ℂ) * ((X : ℂ) + (Y : ℂ) * Complex.I) = 0 ↔ X = 0 ∧ Y = 0 := by
  rw [mul_eq_zero]
  simp only [Complex.ofReal_eq_zero, hc0, false_or]
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    exact ⟨hre, him⟩
  · rintro ⟨rfl, rfl⟩
    simp

theorem ctC_eq (M : Matrix n n ℂ) (i j : n) (c0 : ℝ) (hc0 : c0 ≠ 0) (X1 Y1 X2 Y2 : ℤ)
    (h1 : M i j = (c0 : ℂ) * ((X1 : ℂ) + (Y1 : ℂ) * Complex.I))
    (h2 : M j i = (c0 : ℂ) * ((X2 : ℂ) + (Y2 : ℂ) * Complex.I)) :
    ctC M i j = ((chi X1 Y1 * (2 - chi X2 Y2) : ℤ) : ℂ) := by
  unfold ctC chi
  simp only [h1, h2, gauss_eq_zero c0 hc0]
  split_ifs <;> push_cast <;> ring

theorem core_identity (M : Matrix n n ℂ) (i j : n) (c0 : ℝ) (hc0 : c0 ≠ 0)
    (X1 Y1 X2 Y2 : ℤ) (h1 : M i j = (c0 : ℂ) * ((X1 : ℂ) + (Y1 : ℂ) * Complex.I))
    (h2 : M j i = (c0 : ℂ) * ((X2 : ℂ) + (Y2 : ℂ) * Complex.I)) (pt tg : Bool) (kn : ℝ) (s : ℕ)
    (ρ γ : ℝ) :
    ODETaggedCayley.scaledEntries M (partK M kn pt) s ρ (Real.sqrt 2 * γ)
        (swapTag (if tg then .inr (i, j) else .inl (i, j))) =
      ((γ * Real.sqrt (4 * s) / ρ * c0 / 4 * (if pt then kn else 1) : ℝ) : ℂ) *
        ((chi X1 Y1 * (2 - chi X2 Y2) : ℤ) : ℂ) *
        (((if pt then X1 + X2 else Y1 + Y2 : ℤ) : ℂ) +
          (((if pt then Y1 - Y2 else X2 - X1) * (if tg then -1 else 1) : ℤ) : ℂ) *
            Complex.I) := by
  have hsq : Real.sqrt 2 * γ * (Real.sqrt (2 * (s : ℝ)) / ρ) = γ * Real.sqrt (4 * s) / ρ := by
    rw [← sqrt_two_mul_sqrt]
    ring
  have hct := ctC_eq M i j c0 hc0 X1 Y1 X2 Y2 h1 h2
  unfold ODETaggedCayley.scaledEntries
  rw [hsq]
  cases tg
  · simp only [Bool.false_eq_true, if_false, swapTag, ODETaggedCayley.entries_inl, tagZero_eq,
      hct]
    cases pt
    · simp only [partK_false, ODEMatrixEnergy.hamiltonianPart_apply, h1, h2, if_false,
        Bool.false_eq_true]
      simp only [star_mul', Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I, map_intCast]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    · simp only [partK_true, Matrix.smul_apply, smul_eq_mul,
        ODEMatrixEnergy.dissipativePart_apply, h1, h2, if_true]
      simp only [star_mul', Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I, map_intCast]
      push_cast
      ring_nf
  · simp only [if_true, swapTag, ODETaggedCayley.entries_inr, tagOne_swap_eq, hct]
    cases pt
    · simp only [partK_false, ODEMatrixEnergy.hamiltonianPart_apply, h1, h2, if_false,
        Bool.false_eq_true]
      simp only [star_mul', Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I, map_intCast]
      push_cast
      ring_nf
      simp only [Complex.I_sq]
      ring
    · simp only [partK_true, Matrix.smul_apply, smul_eq_mul,
        ODEMatrixEnergy.dissipativePart_apply, h1, h2, if_true]
      simp only [star_mul', Complex.star_def, map_add, map_mul, Complex.conj_ofReal,
        Complex.conj_I, map_intCast]
      push_cast
      ring_nf

end Entries

/-! ### The values written by the compute circuit -/

section Sigma

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b kq lq : ℕ}

theorem alongEquiv_xor_in {A C W : Type*} [Fintype A] [DecidableEq A] [Fintype C]
    [DecidableEq C] [DecidableEq W] (ι : A ⊕ C ↪ W)
    (f : Cfg A → Cfg C) (y : Cfg W) (c : C) :
    alongEquiv ι (xorEquiv f) y (ι (Sum.inr c)) =
      (y (ι (Sum.inr c)) ^^ f (fun a => y (ι (Sum.inl a))) c) := by
  rw [alongEquiv_apply_in, xorEquiv_inr]

theorem alongEquiv_xor_out {A C W : Type*} [Fintype A] [DecidableEq A] [Fintype C]
    [DecidableEq C] [DecidableEq W] (ι : A ⊕ C ↪ W)
    (f : Cfg A → Cfg C) (y : Cfg W) (w : W) (hw : ∀ c, ι (Sum.inr c) ≠ w) :
    alongEquiv ι (xorEquiv f) y w = y w := by
  by_cases h : ∃ a, ι (Sum.inl a) = w
  · obtain ⟨a, rfl⟩ := h
    rw [alongEquiv_apply_in, xorEquiv_inl]
  · exact alongEquiv_apply_out ι _ y w (by
      rintro (a | c) h'
      · exact h ⟨a, h'⟩
      · exact hw c h')

theorem sigma4_inl (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (LabW kq lq ⊕ PR4 k)) (q : LabW kq lq ⊕ PR4 k) :
    sigma4 D en k0 x (Sum.elim c (fun _ => false)) (Sum.inl q) = c q := by
  rw [sigma4, Equiv.trans_apply, Equiv.trans_apply]
  unfold valPerm
  rw [alongEquiv_xor_out posS4 _ _ _ (fun v h => by simp [posS4, v24] at h),
    alongEquiv_xor_out posT4 _ _ _ (fun v h => by simp [posT4, v14] at h)]
  rfl

theorem sigma4_v14 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (LabW kq lq ⊕ PR4 k)) (v : VW b) :
    sigma4 D en k0 x (Sum.elim c (fun _ => false)) (v14 v) =
      D.table x (phiE en (fun e => c (Sum.inr (ix4 k e)))) v := by
  rw [sigma4, Equiv.trans_apply, Equiv.trans_apply]
  unfold valPerm
  rw [alongEquiv_xor_out posS4 _ _ _ (fun v' h => by simp [posS4, v24, v14] at h)]
  rw [show (v14 v : BW4 k b kq lq) = posT4 (Sum.inr v) from rfl, alongEquiv_xor_in]
  simp [sigRef4, refCfg4, posT4, xB4, v14]

theorem sigma4_v24 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (LabW kq lq ⊕ PR4 k)) (v : VW b) :
    sigma4 D en k0 x (Sum.elim c (fun _ => false)) (v24 v) =
      D.table x (phiE en (fun e => c (Sum.inr (ix4 k (swE e))))) v := by
  rw [sigma4, Equiv.trans_apply, Equiv.trans_apply]
  unfold valPerm
  rw [show (v24 v : BW4 k b kq lq) = posS4 (Sum.inr v) from rfl, alongEquiv_xor_in]
  have hidx : (fun e => (alongEquiv posT4 (xorEquiv (fun d => D.table x (phiE en d)))
      (sigRef4 D en k0 x (Sum.elim c (fun _ => false))))
        (posS4 (kq := kq) (lq := lq) (Sum.inl e))) =
      fun e => c (Sum.inr (ix4 k (swE e))) := by
    funext e
    rw [alongEquiv_xor_out posT4 _ _ _ (fun v' h => by simp [posT4, posS4, v14, xB4] at h)]
    rfl
  rw [alongEquiv_xor_out posT4 _ _ _ (fun v' h => by simp [posT4, posS4, v14, v24] at h),
    hidx]
  simp [sigRef4, refCfg4, posS4, v24]

omit [Fintype n] [DecidableEq n] in
theorem phiE_swE (en : Cfg (Fin k) ≃ n) (d : Cfg (EW k)) :
    phiE en (fun e => d (swE e)) = ((phiE en d).2, (phiE en d).1) := rfl

end Sigma

/-! ### The public parameters -/

section Params

variable (p : Params)

/-- The step of the public LCHS grid. -/
abbrev hStep : ℝ := GateODE.AnalyticLCHS.step (p.T * p.lamD) p.g p.ε

/-- The rounded LCHS step `Hn = round (2^F h)`. -/
def hRound (F : ℕ) : ℕ := ⌊2 ^ F * hStep p + 1 / 2⌋₊

/-- The integer layout of the arithmetic for the public parameters `p`, `b` stored bits and `F`
fractional bits of the LCHS step. -/
def layOf (b F : ℕ) : Lay where
  b := b
  kq := p.k
  lq := p.l
  K := GateODE.AnalyticLCHS.halfCount (p.T * p.lamD) p.g p.ε
  J := p.J
  F := F
  Hn := hRound p F

/-- The decoder scale `κ = γ √(4s) c₀ / (2^(k_T + F + 10) ρ)`, `k_T = p.k` the node bits. -/
def kapOf (s : ℕ) (c0 ρ γ : ℝ) (F : ℕ) : ℝ :=
  γ * Real.sqrt (4 * s) * c0 / (2 ^ (p.k + F + 10) * ρ)

/-- The factor of the dissipative part, `ρ_L = 2^F h / Hn`. -/
def rhoL (F : ℕ) : ℝ := 2 ^ F * hStep p / hRound p F

theorem nodeW_eq (w : Fin p.l → Bool) :
    p.nodeW w = ((if wordValue w < p.J then (wordValue w : ℤ) -
      GateODE.AnalyticLCHS.halfCount (p.T * p.lamD) p.g p.ε else 0 : ℤ) : ℝ) * hStep p := by
  unfold Params.nodeW padIdx
  by_cases h : wordValue w < p.J
  · simp [h, ODECoefficientPadding.paddedNodes, GateODE.AnalyticLCHS.nodes]
  · by_cases h2 : wordValue w = p.J
    · simp [h2, ODECoefficientPadding.paddedNodes]
    · by_cases h3 : wordValue w = p.J + 1
      · simp [h3, ODECoefficientPadding.paddedNodes]
      · simp [h, h2, h3]

theorem dur_div (hT : p.T ≠ 0) (z : Bool × (Fin p.k → Bool)) :
    p.dur z / p.T = ((if z.1 then (wordValue z.2 : ℤ) else 2 ^ p.k : ℤ) : ℝ) / 2 ^ p.k := by
  unfold Params.dur
  split_ifs
  · push_cast
    field_simp
  · push_cast
    field_simp

theorem scale_eq (γ sq c0 ρ h dv nv Hn : ℝ) (k F : ℕ) (hHn : Hn ≠ 0) (hρ : ρ ≠ 0)
    (pt : Bool) :
    γ * sq * c0 / (2 ^ (k + F + 10) * ρ) * (if pt then 2 ^ F * h / Hn else 1) *
        (256 * (dv * (if pt then nv * Hn else 2 ^ F))) =
      γ * (dv / 2 ^ k) * sq / ρ * c0 / 4 * (if pt then nv * h else 1) := by
  cases pt
  · simp only [Bool.false_eq_true, if_false]
    rw [pow_add, pow_add]
    field_simp
    ring
  · simp only [if_true]
    rw [pow_add, pow_add]
    field_simp
    ring

end Params

section Dec

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}

theorem twos_sigma4 (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    {kq lq : ℕ} (c : Cfg (LabW kq lq ⊕ PR4 k)) (W : Cfg (VW b)) (f : VW b → BW4 k b kq lq)
    (hf : ∀ v, sigma4 D en k0 x (Sum.elim c (fun _ => false)) (f v) = W v) (side : Bool) :
    twos (fun i : Fin b => f (if side then .inr i else .inl i))
        (sigma4 D en k0 x (Sum.elim c (fun _ => false))) =
      twos (B := VW b) (fun i => if side then .inr i else .inl i) W := by
  unfold twos
  congr 2
  funext j
  split_ifs <;> simp [hf]

/-- **The decoder hypothesis** for the public parameters: with the LCHS node `nodeW` and the
rescaling `γ dur / T` of each label, the decoder `decO` with scale `kapOf` and factor `rhoL`
takes, after the compute circuit, the value of the label-selected edgewise gate. -/
theorem decOK (p : Params) (hT : p.T ≠ 0) (D : Data X n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) (c0 : ℝ) (hc0 : c0 ≠ 0)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) (ρ γ : ℝ) (hρ : ρ ≠ 0) (F : ℕ)
    (hHn : hRound p F ≠ 0) :
    DecOK D en k0 x (fun z => p.nodeW z.2) (fun z => γ * p.dur z.1 / p.T) ρ
      (decO (inp4 k (layOf p b F)) (kapOf p s c0 ρ γ F) (rhoL p F)) := by
  intro c
  set y := sigma4 D en k0 x (Sum.elim c (fun _ => false)) with hy
  set d : Cfg (EW k) := fun e => c (Sum.inr (ix4 k e)) with hd
  have hij : phiE en d = ((phiE en d).1, (phiE en d).2) := rfl
  set i := (phiE en d).1 with hi
  set j := (phiE en d).2 with hj
  have hv1 : ∀ v, y (v14 v) = D.table x (i, j) v := fun v => by
    rw [hy, sigma4_v14, ← hd, hij]
  have hv2 : ∀ v, y (v24 v) = D.table x (j, i) v := fun v => by
    rw [hy, sigma4_v24]
    rfl
  have hlab : ∀ q, y (Sum.inl q) = c q := fun q => sigma4_inl D en k0 x c q
  have hM1 : D.matrix x i j = (c0 : ℂ) * (((twos (B := VW b) Sum.inl (D.table x (i, j)) : ℤ) : ℂ)
      + ((twos (B := VW b) Sum.inr (D.table x (i, j)) : ℤ) : ℂ) * Complex.I) := by
    rw [← D.decoded, hdec]
    rfl
  have hM2 : D.matrix x j i = (c0 : ℂ) * (((twos (B := VW b) Sum.inl (D.table x (j, i)) : ℤ) : ℂ)
      + ((twos (B := VW b) Sum.inr (D.table x (j, i)) : ℤ) : ℂ) * Complex.I) := by
    rw [← D.decoded, hdec]
    rfl
  have hX1 : (inp4 k (layOf p b F)).X1 y = twos (B := VW b) Sum.inl (D.table x (i, j)) :=
    twos_sigma4 D en k0 x c (D.table x (i, j)) v14 hv1 false
  have hY1 : (inp4 k (layOf p b F)).Y1 y = twos (B := VW b) Sum.inr (D.table x (i, j)) :=
    twos_sigma4 D en k0 x c (D.table x (i, j)) v14 hv1 true
  have hX2 : (inp4 k (layOf p b F)).X2 y = twos (B := VW b) Sum.inl (D.table x (j, i)) :=
    twos_sigma4 D en k0 x c (D.table x (j, i)) v24 hv2 false
  have hY2 : (inp4 k (layOf p b F)).Y2 y = twos (B := VW b) Sum.inr (D.table x (j, i)) :=
    twos_sigma4 D en k0 x c (D.table x (j, i)) v24 hv2 true
  set I := inp4 k (layOf p b F) with hI
  have hpt : y I.pt = c (Sum.inr (pW k)) := hlab _
  have htg : y I.tg = c (Sum.inr (tW k)) := hlab _
  have hini : y I.ini = c (Sum.inl (Sum.inl (Sum.inl ()))) := hlab _
  have hU : I.U y = wordValue (fun j => c (Sum.inl (Sum.inl (Sum.inr j)))) := by
    unfold Inp.U
    congr 1
    funext j
    exact hlab _
  have hV : I.V y = wordValue (fun j => c (Sum.inl (Sum.inr j))) := by
    unfold Inp.V
    congr 1
    funext j
    exact hlab _
  have hte : te en (fun w => c (Sum.inr w)) =
      if c (Sum.inr (tW k)) then Sum.inr (i, j) else Sum.inl (i, j) := by
    unfold te
    rw [← hij]
  have hkn : p.nodeW (labOfW fun s => c (Sum.inl s)).2 = ((I.nv y : ℤ) : ℝ) * hStep p := by
    rw [nodeW_eq]
    unfold Inp.nv
    rw [hV]
    rfl
  have hγ : γ * p.dur (labOfW fun s => c (Sum.inl s)).1 / p.T =
      γ * (((I.dv y : ℤ) : ℝ) / 2 ^ p.k) := by
    rw [mul_div_assoc, dur_div p hT]
    unfold Inp.dv
    rw [hini, hU]
    rfl
  show decO I (kapOf p s c0 ρ γ F) (rhoL p F) y = val4 D en x
    (p.nodeW (labOfW fun s => c (Sum.inl s)).2) ρ
    (γ * p.dur (labOfW fun s => c (Sum.inl s)).1 / p.T) fun w => c (Sum.inr w)
  unfold val4
  rw [hkn, hγ, hte, core_identity (D.matrix x) i j c0 hc0 _ _ _ _ hM1 hM2]
  unfold decO Inp.zx Inp.zy Inp.ct Inp.mu Inp.ax Inp.ay
  rw [hX1, hY1, hX2, hY2, hpt, htg]
  have hHnR : (hRound p F : ℝ) ≠ 0 := by exact_mod_cast hHn
  have hs := scale_eq γ (Real.sqrt (4 * s)) c0 ρ (hStep p)
    ((I.dv y : ℤ) : ℝ) ((I.nv y : ℤ) : ℝ) (hRound p F : ℝ) p.k F hHnR hρ (c (Sum.inr (pW k)))
  change _ = ((γ * (((I.dv y : ℤ) : ℝ) / 2 ^ p.k) * Real.sqrt (4 * s) / ρ * c0 / 4 *
    (if c (Sum.inr (pW k)) = true then ((I.nv y : ℤ) : ℝ) * hStep p else 1) : ℝ) : ℂ) * _ * _
  rw [← hs]
  unfold kapOf rhoL
  rw [show (layOf p b F).Hn = hRound p F from rfl, show (layOf p b F).F = F from rfl]
  beta_reduce
  cases c (Sum.inr (pW k)) <;> cases c (Sum.inr (tW k)) <;>
    simp only [Bool.false_eq_true, if_false, if_true] <;> push_cast <;> ring

end Dec

end

end SparseHamiltonian.GateBinaryODE
