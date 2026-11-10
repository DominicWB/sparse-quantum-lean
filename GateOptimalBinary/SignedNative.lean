import GateOptimalBinary.SignedIface

/-!
# The native signed factor from binary sparse oracles

The native form of the factor `U_B` of the signed-factor regime
(`GateOptimalPrecision.FactorNative`, Section `gate:sec:native`, paragraph "Sparse preparation and
the joint private operation": "We compute the value word while retaining the entry indices,
perform the local operation on its three separate qubits, and uncompute the value"), for the binary
sparse oracles of `GateEfficientBinary`:

* the private register `PRf k`: an attenuation wire and the `k + 3` ancillas of the factor
  (`ιS`, as in `GateOptimalPrecision.liftA`), with the system;
* the compute circuit (the field `W` of `sgFO`): the compute circuit `GateBinary.computeV` of the
  bounded regime on the bounded wires (two row, two column and one value call, `28 k` gates);
* the decoder `c = clip(κ (X + i Y))` of the value word (`wdec`) and the local qubits
  `(f, o, z)` (`locF`);
* the reversible arithmetic: the hypothesis `FactorWordArith` (Section `gate:sec:native`, "Standard
  efficiently decoded binary or fixed-point data satisfy the scalar-arithmetic assumption"): a
  circuit of controlled NOT gates on the value word and the arithmetic wires computing the angle
  and phase words of `c`, placed on the value wires (`sgFO`);
* `sgFO_public`, `sgFO_arith`: the public and arithmetic conditions of
  `GateOptimalPrecision.signed_transfer`;
* `sgFO_native` (`FactorNativeOK`): `W† U(c) W` acts on clean scratch as the factor `U_B = sgU` of
  `signedIface`, lifted past the attenuation wire;
* `signedNative`: the native data of the signed-factor regime.

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
open scoped InnerProduct Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n] {s k b : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-! ### Mapped classical gate lists -/

section MapCfg

variable {A W : Type*} [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]

omit [Fintype W] in
theorem overwrite_update_in {e : A → W} (he : Function.Injective e) (y : Cfg W) (c : Cfg A)
    (t : A) (v : Bool) :
    overwrite e y (Function.update c t v) = Function.update (overwrite e y c) (e t) v := by
  funext w
  by_cases hw : ∃ a, e a = w
  · obtain ⟨a, rfl⟩ := hw
    rw [overwrite_apply_ι he]
    by_cases ha : a = t
    · subst ha
      simp
    · rw [Function.update_of_ne ha, Function.update_of_ne (fun h => ha (he h)),
        overwrite_apply_ι he]
  · push Not at hw
    have hwt : w ≠ e t := fun h => hw t h.symm
    rw [overwrite_apply_out e _ _ w hw, Function.update_of_ne hwt, overwrite_apply_out e _ _ w hw]

omit [Fintype W] in
theorem flipCfg_map {e : A → W} (he : Function.Injective e) (cs : List (A × Bool)) (t : A)
    (y : Cfg W) :
    flipCfg (cs.map (fun c => (e c.1, c.2))) (e t) y =
      overwrite e y (flipCfg cs t (fun a => y (e a))) := by
  unfold flipCfg
  rw [GateODE.ctrlOK_map]
  split_ifs
  · rw [overwrite_update_in he, overwrite_self he]
  · rw [overwrite_self he]

omit [Fintype W] in
/-- **A classical gate list on embedded wires** acts on the embedded wires. -/
theorem cfgRun_map {e : A → W} (he : Function.Injective e) (gs : List (Gate A)) (y : Cfg W) :
    cfgRun (gs.map (GateODE.Gate.map e)) y = overwrite e y (cfgRun gs (fun a => y (e a))) := by
  induction gs generalizing y with
  | nil => exact (overwrite_self he y).symm
  | cons g gs ih =>
      change cfgRun (gs.map (GateODE.Gate.map e))
          (flipCfg (g.cs.map (fun c => (e c.1, c.2))) (e g.t) y) =
        overwrite e y (cfgRun gs (flipCfg g.cs g.t (fun a => y (e a))))
      rw [ih, flipCfg_map he, comp_overwrite he, overwrite_overwrite]

omit [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W] in
theorem classical_map {e : A → W} (he : Function.Injective e) {gs : List (Gate A)}
    (h : Classical gs) : Classical (gs.map (GateODE.Gate.map e)) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
  obtain ⟨hu, hc⟩ := h g' hg'
  refine ⟨hu, ?_⟩
  intro c hc'
  simp only [GateODE.Gate.map, List.mem_map] at hc'
  obtain ⟨c', hc'', rfl⟩ := hc'
  exact fun h' => hc c' hc'' (he h')

end MapCfg

/-! ### Wires of the native factor -/

/-- The private register of the native factor: the attenuation wire `0`, the `k + 3` ancillas of
the factor on the wires `1, …, k + 3`, and the system. -/
abbrev PRf (k : ℕ) := Fin (k + 3 + 1) ⊕ Fin k

/-- The factor register inside the private register (`liftA`: ancilla `i` on wire `i + 1`). -/
abbrev ιS (k : ℕ) : GU k → PRf k := mapId (S := Fin k) Fin.succ

theorem ιS_injective (k : ℕ) : Function.Injective (ιS k) :=
  mapId_injective (Fin.succ_injective _)

/-- The bounded private register inside the private register of the native factor. -/
def ιF (k : ℕ) (p : PR k) : PRf k := ιS k (ιU k p)

theorem ιF_injective (k : ℕ) : Function.Injective (ιF k) :=
  (ιS_injective k).comp (ιU_injective k)

/-- The bounded private register with its (empty) selection wires. -/
def ιE (k : ℕ) : Empty ⊕ PR k → Empty ⊕ PRf k := Sum.map id (ιF k)

theorem ιE_injective (k : ℕ) : Function.Injective (ιE k) :=
  Sum.map_injective.mpr ⟨Function.injective_id, ιF_injective k⟩

/-- `ιE` as an embedding. -/
def ιEe (k : ℕ) : Empty ⊕ PR k ↪ Empty ⊕ PRf k := ⟨ιE k, ιE_injective k⟩

/-- The base wires of the bounded native operation inside those of the native factor. -/
abbrev ιB (k b : ℕ) : BW k b → NB Empty (PRf k) (SZ k b) := mapId (S := SZ k b) (ιE k)

theorem ιB_injective (k b : ℕ) : Function.Injective (ιB k b) := mapId_injective (ιE_injective k)

/-- `ιB` as an embedding. -/
def ιBe (k b : ℕ) : BW k b ↪ NB Empty (PRf k) (SZ k b) := ⟨ιB k b, ιB_injective k b⟩

/-- The local qubits `(f, o, z)` of the native factor. -/
def locF (k : ℕ) : Fin 3 ↪ PRf k :=
  ⟨fun i => ιS k (locU k i), (ιS_injective k).comp (locU_injective k)⟩

/-- The value wires among the base wires. -/
def vF (k b : ℕ) (v : VW b) : NB Empty (PRf k) (SZ k b) := Sum.inr (Sum.inr v)

theorem vF_injective (k b : ℕ) : Function.Injective (vF k b) :=
  fun _ _ h => Sum.inr_injective (Sum.inr_injective h)

/-- The value word of a configuration of the base wires. -/
def valF (y : Cfg (NB Empty (PRf k) (SZ k b))) : Cfg (VW b) := fun v => y (vF k b v)

/-! ### The decoder and the arithmetic hypothesis -/

/-- **The decoded entry** `c = clip(κ (X + i Y))` of a value word. -/
def wdec (κ : ℝ) (w : Cfg (VW b)) : ℂ := NativeSignedFactor.clip ((κ : ℂ) * gauss w)

/-- **The scalar-arithmetic hypothesis of the signed factor** (Section `gate:sec:native`): a
reversible circuit of controlled NOT gates with at most three controls on the value word and
`b_T + b_P + A` arithmetic wires that writes an angle word and a phase word for the decoded entry
`c = clip(κ (X + i Y))` of every value word, restoring its work wires, with either the threshold
`|c| ≤ ξ²/16` and angle zero, or `|sin² α - |c|| ≤ ξ²` and `|e^{iφ} - c/|c|| ≤ ξ`. -/
structure FactorWordArith (b : ℕ) (κ ξ : ℝ) (bT bP A : ℕ) where
  /-- The circuit. -/
  circ : List (Gate (VW b ⊕ AWr bT bP A))
  /-- The angle word. -/
  tw : Cfg (VW b) → Fin bT → Bool
  /-- The phase word. -/
  pw : Cfg (VW b) → Fin bP → Bool
  elem : ∀ g ∈ circ, g.cs.length ≤ 3
  classical : Classical circ
  compute : ∀ w : Cfg (VW b), cfgRun circ (Sum.elim w (fun _ => false)) =
    Sum.elim w (Sum.elim (Sum.elim (tw w) (pw w)) (fun _ => false))
  acc : ∀ w, (‖wdec κ w‖ ≤ ξ ^ 2 / 16 ∧ alphaVal (tw w) = 0) ∨
    (|Real.sin (alphaVal (tw w)) ^ 2 - ‖wdec κ w‖| ≤ ξ ^ 2 ∧
      ‖Complex.exp (phiVal (pw w) * Complex.I) - NativeSignedFactor.phase (wdec κ w)‖ ≤ ξ)

/-- **The native factor** of the signed-factor regime from binary sparse oracles, with the decoder
scale `κ` and the arithmetic `ar` placed on the value wires. -/
def sgFO (k b : ℕ) (κ : ℝ) {ξ : ℝ} {bT bP A : ℕ} (ar : FactorWordArith b κ ξ bT bP A) :
    FactorOp (PRf k) (SZ k b) (PY k b) Query bT bP A where
  W := (computeV k b).map (NInstr.map (ιBe k b))
  loc := locF k
  dec := fun y => wdec κ (valF y)
  circ := ar.circ.map (GateODE.Gate.map (Sum.map (vF k b) id))
  tw := fun y => ar.tw (valF y)
  pw := fun y => ar.pw (valF y)

theorem locB_ne_vF (k b : ℕ) {κ ξ : ℝ} {bT bP A : ℕ} (ar : FactorWordArith b κ ξ bT bP A)
    (i : Fin 3) (v : VW b) : (sgFO k b κ ar).locB i ≠ vF k b v := by
  simp [FactorOp.locB, vF]

theorem valF_overwrite_locB (k b : ℕ) {κ ξ : ℝ} {bT bP A : ℕ}
    (ar : FactorWordArith b κ ξ bT bP A) (y : Cfg (NB Empty (PRf k) (SZ k b))) (c : Cfg (Fin 3)) :
    valF (overwrite (sgFO k b κ ar).locB y c) = valF y := by
  funext v
  exact overwrite_apply_out _ _ _ _ (fun i => locB_ne_vF k b ar i v)

/-- The public conditions of the native factor. -/
theorem sgFO_public (k b : ℕ) {κ ξ : ℝ} {bT bP A : ℕ} (ar : FactorWordArith b κ ξ bT bP A) :
    (sgFO k b κ ar).Public where
  valid := valid_map_list (ιBe k b) (computeV k b) (computeV_valid k b)
  dec_indep x c := by
    change wdec κ (valF (overwrite (sgFO k b κ ar).locB x c)) = wdec κ (valF x)
    rw [valF_overwrite_locB]
  dec_le x := NativeSignedFactor.norm_clip_le _

/-- **The arithmetic conditions** of the native factor, from the scalar-arithmetic hypothesis. -/
theorem sgFO_arith (k b : ℕ) {κ ξ : ℝ} {bT bP A : ℕ} (ar : FactorWordArith b κ ξ bT bP A) :
    FactorArithOK (sgFO k b κ ar) ξ where
  elem g hg := by
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    simpa [GateODE.Gate.map] using ar.elem g' hg'
  classical := classical_map (Sum.map_injective.mpr ⟨vF_injective k b, Function.injective_id⟩)
    ar.classical
  compute x := by
    change cfgRun (ar.circ.map (GateODE.Gate.map (Sum.map (vF k b) id)))
        (Sum.elim x (fun _ => false)) =
      Sum.elim x (Sum.elim (Sum.elim (ar.tw (valF x)) (ar.pw (valF x))) (fun _ => false))
    have he : Function.Injective (Sum.map (vF k b) (id : AWr bT bP A → AWr bT bP A)) :=
      Sum.map_injective.mpr ⟨vF_injective k b, Function.injective_id⟩
    have h1 : (fun a => (Sum.elim x (fun _ => false) : Cfg (NB Empty (PRf k) (SZ k b) ⊕
        AWr bT bP A)) (Sum.map (vF k b) id a)) = Sum.elim (valF x) (fun _ => false) := by
      funext a
      rcases a with v | a <;> rfl
    rw [cfgRun_map he, h1, ar.compute]
    funext w
    rcases w with m | a
    · by_cases hm : ∃ v, vF k b v = m
      · obtain ⟨v, rfl⟩ := hm
        exact overwrite_apply_ι he _ _ (Sum.inl v)
      · push Not at hm
        refine overwrite_apply_out _ _ _ _ ?_
        rintro (v | a) h
        · exact hm v (Sum.inl_injective h)
        · cases h
    · exact overwrite_apply_ι he _ _ (Sum.inr a)
  tw_indep x c := by
    change ar.tw (valF (overwrite (sgFO k b κ ar).locB x c)) = ar.tw (valF x)
    rw [valF_overwrite_locB]
  pw_indep x c := by
    change ar.pw (valF (overwrite (sgFO k b κ ar).locB x c)) = ar.pw (valF x)
    rw [valF_overwrite_locB]
  acc x := ar.acc (valF x)

/-! ### Transport of the compute circuit -/

section Transport

variable {B B' Z : Type*} [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype Z] [DecidableEq Z]

omit [CompleteSpace R] in
/-- The clean embedding of a vector placed at an outside configuration. -/
theorem cleanEmb_put {ι : B → B'} (hι : Function.Injective ι) (c : Cfg B') (φ : Reg B R) :
    cleanEmb (X := Z) (put ι hι c φ) =
      put (mapId (S := Z) ι) (mapId_injective hι) (Sum.elim c (fun _ => false))
        (cleanEmb φ) := by
  apply PiLp.ext
  intro y
  rw [cleanEmb_apply, put_apply, put_apply, cleanEmb_apply]
  have hout : outPart (mapId (S := Z) ι) y =
      outPart (mapId (S := Z) ι) (Sum.elim c (fun _ => false)) ↔
      outPart ι (fun b => y (Sum.inl b)) = outPart ι c := by
    constructor
    · intro h
      funext ⟨w, hw⟩
      have hw' : ∀ a, mapId (S := Z) ι a ≠ Sum.inl w := by
        rintro (a | a) h'
        · exact hw a (Sum.inl_injective h')
        · cases h'
      exact congrFun h ⟨Sum.inl w, hw'⟩
    · intro h
      funext ⟨w, hw⟩
      rcases w with w | z
      · have hw' : ∀ a, ι a ≠ w := fun a h' => hw (Sum.inl a) (by rw [← h']; rfl)
        exact congrFun h ⟨w, hw'⟩
      · exact absurd rfl (hw (Sum.inr z))
  have h1 : (fun x => (fun a => y (mapId (S := Z) ι a)) (Sum.inr x)) = fun x => y (Sum.inr x) :=
    rfl
  have h2 : (fun b => (fun a => y (mapId (S := Z) ι a)) (Sum.inl b)) =
      fun b => y (Sum.inl (ι b)) := rfl
  rw [h1, h2]
  by_cases hz : (fun x => y (Sum.inr x)) = fun _ => false
  · rw [if_pos hz]
    by_cases ho : outPart ι (fun b => y (Sum.inl b)) = outPart ι c
    · rw [if_pos ho, if_pos (hout.2 ho), if_pos hz]
    · rw [if_neg ho, if_neg (fun h => ho (hout.1 h))]
  · rw [if_neg hz]
    by_cases ho : outPart ι (fun b => y (Sum.inl b)) = outPart ι c
    · rw [if_pos (hout.2 ho), if_neg hz]
    · rw [if_neg (fun h => ho (hout.1 h))]

/-- **Transport of a compute identity** `V ι₀ = P ι₀ F` along an embedding of the base wires. -/
theorem compute_transport (ι : B ↪ B') (V P : Reg (B ⊕ Z) R →L[ℂ] Reg (B ⊕ Z) R)
    (F : Reg B R →L[ℂ] Reg B R) (h : V ∘L cleanEmb = P ∘L cleanEmb ∘L F) :
    localOp (mapId (S := Z) ι) (mapId_injective ι.injective) (fun _ => V) ∘L cleanEmb =
      localOp (mapId (S := Z) ι) (mapId_injective ι.injective) (fun _ => P) ∘L cleanEmb ∘L
        localOp ι ι.injective (fun _ => F) := by
  apply ext_bas_clm'
  intro c q
  simp only [comp_apply]
  rw [cleanEmb_bas, localOp_bas, localOp_bas, cleanEmb_put, localOp_put]
  congr 1
  have hY : (fun a => (Sum.elim c (fun _ => false) : Cfg (B' ⊕ Z)) (mapId (S := Z) ι a)) =
      Sum.elim (fun b => c (ι b)) (fun _ => false) := by
    funext a
    rcases a with a | a <;> rfl
  rw [hY, ← cleanEmb_bas, ← comp_apply V, h]
  rfl

end Transport

/-! ### The transported permutation -/

/-- The local qubits among the base wires. -/
def locBF (k : ℕ) (i : Fin 3) : NB Empty (PRf k) (SZ k b) := Sum.inl (Sum.inr (locF k i))

theorem locBF_injective (k : ℕ) : Function.Injective (locBF (b := b) k) :=
  fun _ _ h => (locF k).injective (Sum.inr_injective (Sum.inl_injective h))

theorem ιB_oB (k b : ℕ) : ιB k b oB = locBF k 1 := rfl

theorem ιF_ne_locF (k : ℕ) (p : PR k) (i : Fin 3) (hi : i ≠ 1) : ιF k p ≠ locF k i := by
  intro h
  have h' : ιU k p = locU k i := ιS_injective k h
  fin_cases i
  · exact ιU_ne_f k p h'
  · exact hi rfl
  · exact ιU_ne_z k p h'

theorem ιB_ne_locBF (k b : ℕ) (a : BW k b) (i : Fin 3) (hi : i ≠ 1) :
    ιB k b a ≠ locBF k i := by
  rcases a with (e | p) | z
  · exact e.elim
  · intro h
    exact ιF_ne_locF k p i hi (Sum.inr_injective (Sum.inl_injective h))
  · intro h
    cases h

theorem locBF_mem_range_iff (k b : ℕ) (i : Fin 3) :
    (∃ a, ιB k b a = locBF k i) ↔ i = 1 := by
  constructor
  · rintro ⟨a, ha⟩
    by_contra hi
    exact ιB_ne_locBF k b a i hi ha
  · rintro rfl
    exact ⟨oB, ιB_oB k b⟩

/-- The base configurations through the bounded wires, with the local qubits overwritten. -/
theorem overwrite_locBF_comp (k b : ℕ) (y : Cfg (NB Empty (PRf k) (SZ k b))) (d : Cfg (Fin 3)) :
    (fun a => overwrite (locBF k) y d (ιB k b a)) =
      Function.update (fun a => y (ιB k b a)) oB (d 1) := by
  funext a
  by_cases ha : a = oB
  · subst ha
    rw [Function.update_self, ιB_oB, overwrite_apply_ι (locBF_injective k)]
  · rw [Function.update_of_ne ha]
    refine overwrite_apply_out _ _ _ _ ?_
    intro i hi
    by_cases h1 : i = 1
    · subst h1
      exact ha ((ιB_injective k b) (by rw [ιB_oB]; exact hi.symm))
    · exact ιB_ne_locBF k b a i h1 hi.symm

/-- The permutation of the compute circuit on the base wires of the native factor. -/
abbrev sigF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X) :
    Cfg (NB Empty (PRf k) (SZ k b)) ≃ Cfg (NB Empty (PRf k) (SZ k b)) :=
  alongEquiv (ιBe k b) (sigma D en k0 x)

/-- **The permutation commutes with overwriting the local qubits.** -/
theorem sigF_overwrite (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) (d : Cfg (Fin 3)) :
    sigF D en k0 x (overwrite (locBF k) y d) = overwrite (locBF k) (sigF D en k0 x y) d := by
  funext w
  by_cases hw : ∃ i, locBF k i = w
  · obtain ⟨i, rfl⟩ := hw
    rw [overwrite_apply_ι (locBF_injective k)]
    by_cases h1 : i = 1
    · subst h1
      change alongEquiv (ιBe k b) (sigma D en k0 x) (overwrite (locBF k) y d) (ιBe k b oB) = d 1
      rw [alongEquiv_apply_in, sigma_oB]
      change overwrite (locBF k) y d (ιB k b oB) = d 1
      rw [ιB_oB, overwrite_apply_ι (locBF_injective k)]
    · rw [alongEquiv_apply_out _ _ _ _ (fun a => ιB_ne_locBF k b a i h1),
        overwrite_apply_ι (locBF_injective k)]
  · push Not at hw
    rw [overwrite_apply_out _ _ _ _ hw]
    by_cases hw' : ∃ a, ιB k b a = w
    · obtain ⟨a, rfl⟩ := hw'
      have ha : a ≠ oB := fun h => hw 1 (by rw [h, ιB_oB])
      change alongEquiv (ιBe k b) (sigma D en k0 x) (overwrite (locBF k) y d) (ιBe k b a) =
        alongEquiv (ιBe k b) (sigma D en k0 x) y (ιBe k b a)
      rw [alongEquiv_apply_in, alongEquiv_apply_in]
      change sigma D en k0 x (fun a => overwrite (locBF k) y d (ιB k b a)) a =
        sigma D en k0 x (fun a => y (ιB k b a)) a
      rw [overwrite_locBF_comp, sigma_update_oB, Function.update_of_ne ha]
    · push Not at hw'
      rw [alongEquiv_apply_out _ _ _ _ hw', alongEquiv_apply_out _ _ _ _ hw',
        overwrite_apply_out _ _ _ _ hw]

theorem sigF_locBF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (y : Cfg (NB Empty (PRf k) (SZ k b))) :
    (fun i => sigF D en k0 x y (locBF k i)) = fun i => y (locBF k i) := by
  have h := sigF_overwrite D en k0 x y (fun i => y (locBF k i))
  rw [overwrite_self (locBF_injective k)] at h
  funext i
  conv_rhs => rw [← overwrite_apply_ι (locBF_injective k) (sigF D en k0 x y)
    (fun i => y (locBF k i)) i]
  rw [← h]

/-- The edge held by a configuration of the private register of the native factor. -/
def edgeF (en : Cfg (Fin k) ≃ n) (c : Cfg (Empty ⊕ PRf k)) : n × n :=
  phiE en (fun e => c (Sum.inr (ιF k (ixPR k e))))

/-- **The value word computed on clean scratch** is the stored entry of the located edge. -/
theorem sigF_val (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (c : Cfg (Empty ⊕ PRf k)) :
    valF (sigF D en k0 x (Sum.elim c (fun _ => false))) = D.table x (edgeF en c) := by
  funext v
  change alongEquiv (ιBe k b) (sigma D en k0 x) (Sum.elim c (fun _ => false)) (ιBe k b (vB v)) = _
  rw [alongEquiv_apply_in]
  have hY : (fun a => (Sum.elim c (fun _ => false) : Cfg (NB Empty (PRf k) (SZ k b)))
      (ιBe k b a)) = Sum.elim (fun p => c (ιE k p)) (fun _ => false) := by
    funext a
    rcases a with a | a <;> rfl
  rw [hY, sigma_val]
  rfl

/-! ### The native identity -/

/-- The entry `clip(H_e/μ)` of the edge held by a configuration of the private register. -/
def cvF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X)
    (c : Cfg (Empty ⊕ PRf k)) : ℂ :=
  NativeSignedFactor.entry D μ (edgeF en c, D.table x (edgeF en c))

/-- The local qubits on the private register with its (empty) selection wires. -/
def locE (k : ℕ) (i : Fin 3) : Empty ⊕ PRf k := Sum.inr (locF k i)

theorem locE_injective (k : ℕ) : Function.Injective (locE k) :=
  fun _ _ h => (locF k).injective (Sum.inr_injective h)

/-- The wires of the bounded register inside the private register of the factor. -/
def ιFE (k : ℕ) (p : PR k) : Empty ⊕ PRf k := Sum.inr (ιF k p)

theorem ιFE_injective (k : ℕ) : Function.Injective (ιFE k) :=
  Sum.inr_injective.comp (ιF_injective k)

/-- The lifted locator of the factor on the private register. -/
theorem liftE_FuF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (x : X) :
    liftE (localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)) =
      localOp (ιE k) (ιE_injective k) (fun _ => Fq (R := R) D en x) := by
  unfold liftE FuF Fq liftE
  rw [localOp_localOp' (ιS_injective k) (ιU_injective k) (ιF k) (ιF_injective k) (fun _ => rfl)
      (fun _ _ => qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x)),
    localOp_localOp' Sum.inr_injective (ιF_injective k) (ιFE k) (ιFE_injective k) (fun _ => rfl)
      (fun _ _ => qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x)),
    localOp_localOp' (ιE_injective k) Sum.inr_injective (ιFE k) (ιFE_injective k) (fun _ => rfl)
      (fun _ _ => qlift (R := R) (phiPR en) (FixedLocatorConjugation.locator D x))]

omit [Fintype n] [DecidableEq n] in
/-- The edge of a configuration read through the local qubits of the factor. -/
theorem edgeU_clear (en : Cfg (Fin k) ≃ n) (z : Cfg (Empty ⊕ PRf k)) :
    edgeU en (clearCfg (locU k) (fun a => clearCfg (locF k) (fun a' => z (Sum.inr a'))
      (ιS k a))) = edgeF en z := by
  unfold edgeU edgeF
  congr 1
  funext e
  rw [clearCfg_apply_out _ _ _ (fun i => locU_ne_ixPR k i e)]
  have h1 : ∀ i, (locF k) i ≠ ιS k (ιU k (ixPR k e)) :=
    fun i h => locU_ne_ixPR k i e ((ιS_injective k) h)
  rw [clearCfg_apply_out _ _ _ h1]
  rfl

/-- The stable signed factor of the located edge on the private register. -/
theorem liftE_AuF (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    liftE (localOp (ιS k) (ιS_injective k) (fun _ => AuF (R := R) D en μ x)) =
      localOp (locE k) (locE_injective k) (fun z => matOp (blk (uMat (cvF D en μ x z)))) := by
  unfold liftE AuF
  rw [localOp_localOp' (ιS_injective k) (locU_injective k) (locF k) (locF k).injective
      (fun _ => rfl) (fun _ y => matOp (blk (uMat (cvU D en μ x y)))),
    localOp_localOp' Sum.inr_injective (locF k).injective (locE k) (locE_injective k)
      (fun _ => rfl)]
  apply localOp_congr
  intro z
  unfold cvU cvF
  rw [edgeU_clear]

/-- The selected private operation of a constant family. -/
theorem selOp_const {S : Type*} [Fintype S] [DecidableEq S] {a : ℕ}
    (O : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) :
    selOp (Sel := Empty) (fun _ => O) = liftE (conj O) := rfl

/-- The private operation of the factor in terms of the bounded locator and the local factor. -/
theorem sel_liftA_sgU (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (μ : ℝ) (x : X) :
    selOp (Sel := Empty) (a := k + 3 + 1) (S := Fin k) (R := R)
        (fun _ => liftA (P := Reg (Fin k) R) (a := k + 3) (sgU (R := R) D en μ x)) =
      (liftE (localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)))† ∘L
        liftE (localOp (ιS k) (ιS_injective k) (fun _ => AuF (R := R) D en μ x)) ∘L
        liftE (localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)) := by
  rw [selOp_const, liftA, conj_localOp, sgU, conj_unconj, UF, ← liftE_adjoint, ← liftE_comp,
    ← liftE_comp, localOp_adjoint, localOp_comp, localOp_comp]

omit [CompleteSpace R] in
/-- A vector placed at an outside configuration, expanded in basis vectors. -/
theorem put_sum_smul_bas {A W : Type*} [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]
    {ι : A → W} (hι : Function.Injective ι) (y : Cfg W) (a : Cfg A → ℂ) (q : R) :
    put ι hι y (∑ d, a d • bas d q) = ∑ d, a d • bas (overwrite ι y d) q := by
  have hadd : ∀ φ φ' : Reg A R, put ι hι y (φ + φ') = put ι hι y φ + put ι hι y φ' := by
    intro φ φ'
    simp only [put, Pi.single_add, WithLp.toLp_add, map_add]
  have hsmul : ∀ (c : ℂ) (φ : Reg A R), put ι hι y (c • φ) = c • put ι hι y φ := by
    intro c φ
    simp only [put, Pi.single_smul, WithLp.toLp_smul, map_smul]
  have hzero : put ι hι y (0 : Reg A R) = 0 := by
    simp only [put, Pi.single_zero, WithLp.toLp_zero, map_zero]
  have key : ∀ t : Finset (Cfg A),
      put ι hι y (∑ d ∈ t, a d • bas d q) = ∑ d ∈ t, a d • bas (overwrite ι y d) q := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, hzero]
    | insert d t hd ih => rw [Finset.sum_insert hd, Finset.sum_insert hd, hadd, hsmul, put_bas, ih]
  exact key Finset.univ

omit [Fintype n] [DecidableEq n] in
/-- The located edge does not read the local qubits. -/
theorem edgeF_overwrite (en : Cfg (Fin k) ≃ n) (c : Cfg (Empty ⊕ PRf k)) (d : Cfg (Fin 3)) :
    edgeF en (overwrite (locE k) c d) = edgeF en c := by
  unfold edgeF
  congr 1
  funext e
  exact overwrite_apply_out _ _ _ _
    (fun i h => locU_ne_ixPR k i e ((ιS_injective k) (Sum.inr_injective h)))

/-- The local qubits of the base wires on clean scratch. -/
theorem overwrite_locBF_elim (c : Cfg (Empty ⊕ PRf k)) (d : Cfg (Fin 3)) :
    overwrite (locBF (b := b) k)
        (Sum.elim c (fun _ => false) : Cfg (NB Empty (PRf k) (SZ k b))) d =
      Sum.elim (overwrite (locE k) c d) (fun _ => false) := by
  funext w
  rcases w with p | z
  · by_cases hp : ∃ i, locE k i = p
    · obtain ⟨i, rfl⟩ := hp
      rw [show (Sum.inl (locE k i) : NB Empty (PRf k) (SZ k b)) = locBF k i from rfl,
        overwrite_apply_ι (locBF_injective k)]
      exact (overwrite_apply_ι (locE_injective k) _ _ i).symm
    · push Not at hp
      rw [overwrite_apply_out (locBF k) _ _ _ (fun i h => hp i (Sum.inl_injective h))]
      exact (overwrite_apply_out _ _ _ _ hp).symm
  · rw [overwrite_apply_out _ _ _ _ (fun i h => by simp [locBF] at h)]
    rfl

/-- The value word does not read the local qubits. -/
theorem valF_overwrite_locBF (y : Cfg (NB Empty (PRf k) (SZ k b))) (d : Cfg (Fin 3)) :
    valF (overwrite (locBF (b := b) k) y d) = valF y := by
  funext v
  exact overwrite_apply_out _ _ _ _ (fun i h => by simp [locBF, vF] at h)

/-- The decoded factor of the native factor on the base wires. -/
theorem Udec_sgFO (κ : ℝ) {ξ : ℝ} {bT bP A : ℕ} (ar : FactorWordArith b κ ξ bT bP A) :
    Udec (R := R) (sgFO k b κ ar) = localOp (locBF (b := b) k) (locBF_injective k)
      (fun y => matOp (blk (uMat (wdec κ (valF y))))) := rfl

/-- **The compute circuit of the native factor on clean scratch** is the lifted locator followed
by the transported permutation. -/
theorem sgFO_compute (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (κ : ℝ) {ξ : ℝ} {bT bP A : ℕ}
    (ar : FactorWordArith b κ ξ bT bP A) :
    nrun (prims (R := R) D en x) (sgFO k b κ ar).W ∘L cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L
        liftE (localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)) := by
  have h := compute_transport (Z := SZ k b) (ιEe k) _ _ _
    (compute_cleanEmb (R := R) (b := b) D en k0 hk0 x)
  have hV : nrun (prims (R := R) D en x) (sgFO k b κ ar).W =
      localOp (mapId (S := SZ k b) (ιEe k)) (mapId_injective (ιEe k).injective)
        (fun _ => nrun (prims (R := R) D en x) (computeV k b)) :=
    nrun_map _ (ιBe k b) (computeV k b)
  have hP : localOp (mapId (S := SZ k b) (ιEe k)) (mapId_injective (ιEe k).injective)
      (fun _ => permOp (Q := R) (sigma D en k0 x)) = permOp (sigF D en k0 x) :=
    localOp_permOp (ιBe k b) (sigma D en k0 x)
  have hF : localOp (ιEe k) (ιEe k).injective (fun _ => Fq (R := R) D en x) =
      liftE (localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)) :=
    (liftE_FuF D en x).symm
  rw [hV, h, hP, hF]

/-- **The decoded factor commutes past the permutation** into the lifted local factor of the
located edge, for the decoder scale `κ = c₀/μ`. -/
theorem sgFO_dec_comm (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s) (x : X)
    (μ c0 : ℝ) (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) {ξ : ℝ} {bT bP A : ℕ}
    (ar : FactorWordArith b (c0 / μ) ξ bT bP A) :
    Udec (R := R) (sgFO k b (c0 / μ) ar) ∘L permOp (sigF D en k0 x) ∘L cleanEmb (X := SZ k b) =
      permOp (sigF D en k0 x) ∘L cleanEmb ∘L
        liftE (localOp (ιS k) (ιS_injective k) (fun _ => AuF (R := R) D en μ x)) := by
  rw [Udec_sgFO, liftE_AuF]
  apply ext_bas_clm'
  intro c q
  simp only [comp_apply]
  rw [cleanEmb_bas, permOp_bas, localOp_bas, localOp_bas, matOp_bas', matOp_bas',
    put_sum_smul_bas, put_sum_smul_bas, map_sum, map_sum]
  have hd0 : (fun a => sigF D en k0 x (Sum.elim c (fun _ => false)) (locBF k a)) =
      fun a => c (locE k a) := by
    rw [sigF_locBF]
    rfl
  have hval : wdec (c0 / μ) (valF (clearCfg (locBF k)
      (sigF D en k0 x (Sum.elim c (fun _ => false))))) = cvF D en μ x (clearCfg (locE k) c) := by
    unfold wdec cvF NativeSignedFactor.entry
    rw [valF_overwrite_locBF, sigF_val, edgeF_overwrite, hdec]
    congr 1
    push_cast
    ring
  rw [hd0, hval]
  apply Finset.sum_congr rfl
  intro d _
  rw [map_smul, map_smul, cleanEmb_bas, permOp_bas, ← overwrite_locBF_elim, sigF_overwrite]

/-- **The native identity of the signed factor** (`FactorNativeOK`): `W† U(c) W` acts on clean
scratch as the factor `U_B` of `signedIface`, lifted past the attenuation wire. -/
theorem sgFO_native (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (k0 : Fin s)
    (hk0 : D.slot k0 = zIdx en) (x : X) (μ c0 : ℝ)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) {ξ : ℝ} {bT bP A : ℕ}
    (ar : FactorWordArith b (c0 / μ) ξ bT bP A) :
    FactorNativeOK (prims (R := R) D en x) (sgFO k b (c0 / μ) ar)
      (selOp (fun _ : Cfg Empty => liftA (sgU (R := R) D en μ x))) := by
  have hK1 := sgFO_compute (R := R) D en k0 hk0 x (c0 / μ) ar
  have hK2 := sgFO_dec_comm (R := R) D en k0 x μ c0 hdec ar
  have hVu : IsUnitary (nrun (prims (R := R) D en x) (sgFO k b (c0 / μ) ar).W) :=
    nrun_isUnitary _ (prims_isUnitary D en x) _ (sgFO_public k b ar).valid
  have hFu : IsUnitary (liftE (localOp (ιS k) (ιS_injective k)
      (fun _ => FuF (R := R) D en x))) :=
    liftE_isUnitary (localOp_isUnitary _ _ (fun _ => FuF_isUnitary D en x))
  have hVV : (nrun (prims (R := R) D en x) (sgFO k b (c0 / μ) ar).W)† ∘L
      nrun (prims (R := R) D en x) (sgFO k b (c0 / μ) ar).W = 1 := by
    have h := hVu.1
    rwa [star_eq_adjoint, mul_def] at h
  have hFF : liftE (localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)) ∘L
      (liftE (localOp (ιS k) (ιS_injective k) (fun _ => FuF (R := R) D en x)))† = 1 := by
    have h := hFu.2
    rwa [star_eq_adjoint, mul_def] at h
  unfold FactorNativeOK
  rw [sel_liftA_sgU]
  exact nativeOK_of _ _ _ _ _ hK1 hK2 hVV hFF

/-- **The native data of the signed-factor regime from binary sparse oracles**: the boundary
gates of `signedIface`, the native factor `sgFO` with the decoder `clip((c₀/μ)(X + i Y))` and the
scalar arithmetic `ar`, and its public, arithmetic and native conditions. -/
def signedNative (D : Data X n (Cfg (VW b)) s) (en : Cfg (Fin k) ≃ n) (sb : ℕ) (hsb : sb ≤ k)
    (hs : s = 2 ^ sb)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u))
    {η μ σ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (hσ : (s : ℝ) * μ ^ 2 = σ * η ^ 2) (x : X)
    (hH : (D.matrix x).IsHermitian) (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hent : ∀ i j, ‖D.matrix x i j‖ ≤ μ) (k0 : Fin s) (hk0 : D.slot k0 = zIdx en) (c0 : ℝ)
    (hdec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z) {ξ : ℝ} {bT bP A : ℕ}
    (ar : FactorWordArith b (c0 / μ) ξ bT bP A) :
    FactorNative (prims (R := R) D en x)
      (signedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hent).UJ
      (signedIface (R := R) D en sb hsb hs hrange hη hμ hσ x hH hrow hent).U (SZ k b) bT bP A ξ
    where
  UJg := sgUJg k sb hsb
  ok := sgUJg_ok sb hsb
  boundary := rfl
  fo := sgFO k b (c0 / μ) ar
  pub := sgFO_public k b ar
  arith := sgFO_arith k b ar
  native := sgFO_native D en k0 hk0 x μ c0 hdec ar

end

end GateOptimalBinary
