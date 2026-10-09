import DeferredMeasurementLowerBounds.Deferral.Defer

set_option autoImplicit false

/-!
# The heralded output of the deferred program

A record `r` determines a transcript of the measured algorithm; `leafAt` is its output
isometry when the transcript ends in `output`, and `none` when it ends in `reject` or `r` is not
a transcript. The **output records** `OutRec W M k` are the records with an output leaf. The
deferred output isometry `deferOutput : Joint (OutRec W M k) E → Joint (Rec W k) K` applies, at
every output record, the isometry of its leaf; its range is the success sector of the deferred
program, so rejected transcripts are heralded as failures.

Decoding the purification (`purify`) gives the vector `a` of decoded branch outputs indexed by
the output records (the records stay in the output as a classical register): the sum of the
projectors `|a_r⟩⟨a_r|` is the heralded output of the measured algorithm
(`sum_pure_deferOutput`) and `‖a‖²` is its success mass (`norm_sq_deferOutput`).
-/

namespace DeferredMeasurementLowerBounds.Deferral

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct

variable {K E X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {O : L → X → K →L[ℂ] K}

/-- The output isometry of the transcript of a record, if it ends in `output`. -/
def leafAt (W : ℕ) : Measured O E → (k : ℕ) → Rec W k → Option {o : E →L[ℂ] K // o† ∘L o = 1}
  | .output out h, _, _ => some ⟨out, h⟩
  | .reject, _, _ => none
  | .call _ _ next, k, r => leafAt W next k r
  | .instrument _ _ _ _, 0, _ => none
  | .instrument n _ _ next, k + 1, r => match r 0 with
      | none => none
      | some v => if h : v.val < n then leafAt W (next ⟨v.val, h⟩) k (Fin.tail r) else none

/-- The records whose transcript ends in an output. -/
abbrev OutRec (W : ℕ) (M : Measured O E) (k : ℕ) : Type :=
  {r : Rec W k // (leafAt W M k r).isSome}

/-- The output isometry at an output record. -/
def leafOut (W : ℕ) (M : Measured O E) (k : ℕ) (r : OutRec W M k) : E →L[ℂ] K :=
  ((leafAt W M k r.1).get r.2).1

/-- **The deferred output isometry**: the leaf isometry at every output record. -/
def deferOutput (W : ℕ) (M : Measured O E) (k : ℕ) :
    Joint (OutRec W M k) E →L[ℂ] Joint (Rec W k) K :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Rec W k => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun r =>
      if h : (leafAt W M k r).isSome then leafOut W M k ⟨r, h⟩ ∘L Joint.proj ⟨r, h⟩ else 0

/-- Coordinates of the deferred output isometry. -/
theorem deferOutput_apply (W : ℕ) (M : Measured O E) (k : ℕ) (a : Joint (OutRec W M k) E)
    (r : Rec W k) :
    deferOutput W M k a r =
      if h : (leafAt W M k r).isSome then leafOut W M k ⟨r, h⟩ (a ⟨r, h⟩) else 0 := by
  change (if h : (leafAt W M k r).isSome then leafOut W M k ⟨r, h⟩ ∘L Joint.proj ⟨r, h⟩
    else 0 : Joint (OutRec W M k) E →L[ℂ] K) a = _
  split_ifs <;> rfl

/-- The leaf isometry at an output record preserves norms. -/
theorem norm_leafOut (W : ℕ) (M : Measured O E) (k : ℕ) (r : OutRec W M k) (v : E) :
    ‖leafOut W M k r v‖ = ‖v‖ :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).2 ((leafAt W M k r.1).get r.2).2 v

/-- A sum over all records of a function vanishing off the output records is the sum over the
output records. -/
theorem sum_outRec {T : Type*} [AddCommMonoid T] (W : ℕ) (M : Measured O E) (k : ℕ)
    (g : Rec W k → T) (hg : ∀ r, (leafAt W M k r).isSome = false → g r = 0) :
    ∑ r : OutRec W M k, g r.1 = ∑ r, g r := by
  have h0 : ∑ r : {r : Rec W k // ¬ (leafAt W M k r).isSome = true}, g r.1 = 0 :=
    Finset.sum_eq_zero fun r _ => hg r.1 (by simpa only [Bool.not_eq_true] using r.2)
  rw [← Fintype.sum_subtype_add_sum_subtype (fun r => (leafAt W M k r).isSome = true) g, h0,
    add_zero]

/-- The deferred output is an isometry. -/
theorem deferOutput_isometry (W : ℕ) (M : Measured O E) (k : ℕ) :
    (deferOutput W M k)† ∘L deferOutput W M k = 1 := by
  refine (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).1 fun a => ?_
  have hsq : ‖deferOutput W M k a‖ ^ 2 = ‖a‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2,
      ← sum_outRec W M k (fun r => ‖deferOutput W M k a r‖ ^ 2) (fun r hr => by
        rw [deferOutput_apply, dif_neg (by simp [hr])]
        simp)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [deferOutput_apply, dif_pos r.2, norm_leafOut]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

/-- Decoding at an output record applies the adjoint of its leaf isometry. -/
theorem adjoint_deferOutput_apply (W : ℕ) (M : Measured O E) (k : ℕ)
    (Ψ : Joint (Rec W k) K) (r : OutRec W M k) :
    (((deferOutput W M k)†) Ψ) r = ((leafOut W M k r)†) (Ψ r.1) := by
  refine ext_inner_left ℂ fun v => ?_
  have h := ContinuousLinearMap.adjoint_inner_right (deferOutput W M k)
    (WithLp.toLp 2 (Pi.single r v) : Joint (OutRec W M k) E) Ψ
  rw [PiLp.inner_apply, Finset.sum_eq_single r
    (fun i _ hi => by rw [PiLp.toLp_apply, Pi.single_apply, if_neg hi, inner_zero_left])
    (fun h' => absurd (Finset.mem_univ r) h'), PiLp.toLp_apply, Pi.single_eq_same] at h
  rw [h, PiLp.inner_apply, Finset.sum_eq_single r.1, deferOutput_apply, dif_pos r.2,
    Subtype.coe_eta, PiLp.toLp_apply, Pi.single_eq_same, ContinuousLinearMap.adjoint_inner_right]
  · intro i _ hi
    rw [deferOutput_apply]
    split_ifs with hs
    · rw [PiLp.toLp_apply, Pi.single_apply,
        if_neg (fun e => hi (congrArg Subtype.val e)), map_zero, inner_zero_left]
    · exact inner_zero_left _
  · intro h'
    exact absurd (Finset.mem_univ _) h'

/-! ### Sums over transcripts and over records -/

/-- The sum over all transcripts of a function of the output isometry and the unnormalised branch
vector (rejected transcripts contribute zero). -/
def transcriptSum {T : Type*} [AddCommMonoid T] (f : (E →L[ℂ] K) → K → T) :
    Measured O E → X → K → T
  | .output out _, _, φ => f out φ
  | .reject, _, _ => 0
  | .call l b next, x, φ => transcriptSum f next x (queryOp O l b x φ)
  | .instrument _ A _ next, x, φ => ∑ j, transcriptSum f (next j) x (A j φ)

/-- The term of a record: the function of its output isometry and its purification coordinate,
zero if the record has no output leaf. -/
def recordTerm {T : Type*} [AddCommMonoid T] (f : (E →L[ℂ] K) → K → T) (W : ℕ)
    (M : Measured O E) (k : ℕ) (x : X) (φ : K) (r : Rec W k) : T :=
  match leafAt W M k r with
  | none => 0
  | some o => f o.1 (purify W M k x φ r)

/-- The leaf of a record after an instrument is the leaf of the remaining record in the
continuation of its first register. -/
theorem leafAt_instrument_cons (W : ℕ) {n : ℕ} (A : Fin n → K →L[ℂ] K)
    (hA : ∑ j, (A j)† ∘L A j = 1) (next : Fin n → Measured O E) (k : ℕ) (v : Option (Fin W))
    (r : Rec W k) :
    leafAt W (.instrument n A hA next) (k + 1) (Fin.cons v r) =
      match v with
      | none => none
      | some v => if h : v.val < n then leafAt W (next ⟨v.val, h⟩) k r else none := by
  simp only [leafAt, Fin.cons_zero, Fin.tail_cons]

/-- The purification after an instrument, at a record with first register `v`. -/
theorem purify_instrument_cons (W : ℕ) {n : ℕ} (A : Fin n → K →L[ℂ] K)
    (hA : ∑ j, (A j)† ∘L A j = 1) (next : Fin n → Measured O E) (k : ℕ) (x : X) (φ : K)
    (v : Option (Fin W)) (r : Rec W k) :
    purify W (.instrument n A hA next) (k + 1) x φ (Fin.cons v r) =
      match v with
      | none => 0
      | some v => if h : v.val < n then purify W (next ⟨v.val, h⟩) k x (A ⟨v.val, h⟩ φ) r
        else 0 := by
  rw [← split_apply W k (purify W (.instrument n A hA next) (k + 1) x φ) v r]
  simp only [purify, LinearIsometryEquiv.apply_symm_apply]
  rcases v with _ | v
  · rfl
  · by_cases h : v.val < n
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      rfl

/-- The record term after an instrument, at a record with first register `v`. -/
theorem recordTerm_instrument_cons {T : Type*} [AddCommMonoid T] (f : (E →L[ℂ] K) → K → T)
    (W : ℕ) {n : ℕ} (A : Fin n → K →L[ℂ] K) (hA : ∑ j, (A j)† ∘L A j = 1)
    (next : Fin n → Measured O E) (k : ℕ) (x : X) (φ : K) (v : Option (Fin W)) (r : Rec W k) :
    recordTerm f W (.instrument n A hA next) (k + 1) x φ (Fin.cons v r) =
      match v with
      | none => 0
      | some v => if h : v.val < n then recordTerm f W (next ⟨v.val, h⟩) k x (A ⟨v.val, h⟩ φ) r
        else 0 := by
  unfold recordTerm
  rw [leafAt_instrument_cons, purify_instrument_cons]
  rcases v with _ | v
  · rfl
  · by_cases h : v.val < n
    · simp only [dif_pos h]
    · simp only [dif_neg h]

/-- Summing a dependent family over the values `v < n` of `Fin W`. -/
theorem sum_fin_dite {T : Type*} [AddCommMonoid T] {n W : ℕ} (hn : n ≤ W) (S : Fin n → T) :
    ∑ v : Fin W, (if h : v.val < n then S ⟨v.val, h⟩ else 0) = ∑ j, S j := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Fin.sum_univ_add]
  simp

/-- **Sum over records**: summing the record terms over all records gives the sum over all
transcripts, when every transcript has at most `k` instruments of at most `W` outcomes. -/
theorem sum_recordTerm {T : Type*} [AddCommMonoid T] (f : (E →L[ℂ] K) → K → T)
    (hf : ∀ o, f o 0 = 0) (W : ℕ) (M : Measured O E) (k : ℕ) (hd : M.depth ≤ k)
    (hw : M.width ≤ W) (x : X) (φ : K) :
    ∑ r, recordTerm f W M k x φ r = transcriptSum f M x φ := by
  induction M generalizing k φ with
  | output out h =>
    have hr : ∀ r, recordTerm f W (.output out h : Measured O E) k x φ r =
        f out (if r = Rec.fresh W k then φ else 0) := by
      intro r
      simp only [recordTerm, leafAt, purify, freshInj_apply]
    simp only [hr]
    rw [Finset.sum_eq_single (Rec.fresh W k)]
    · simp only [if_true]
      rfl
    · intro r _ hr'
      rw [if_neg hr', hf]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  | reject =>
    simp only [recordTerm, leafAt, Finset.sum_const_zero]
    rfl
  | call l b next ih =>
    exact ih k hd hw _
  | instrument n A hA next ih =>
    simp only [Measured.depth, Measured.width] at hd hw
    cases k with
    | zero => omega
    | succ k =>
      have hn : n ≤ W := le_trans (le_max_left _ _) hw
      have hdj : ∀ j, (next j).depth ≤ k := fun j =>
        le_trans (Finset.le_sup (f := fun j => (next j).depth) (Finset.mem_univ j)) (by omega)
      have hwj : ∀ j, (next j).width ≤ W := fun j =>
        le_trans (Finset.le_sup (f := fun j => (next j).width) (Finset.mem_univ j))
          (le_trans (le_max_right _ _) hw)
      have key : ∀ v : Option (Fin W),
          (∑ r, recordTerm f W (.instrument n A hA next) (k + 1) x φ (Fin.cons v r)) =
            match v with
            | none => 0
            | some v => if h : v.val < n then
                transcriptSum f (next ⟨v.val, h⟩) x (A ⟨v.val, h⟩ φ) else 0 := by
        intro v
        simp only [recordTerm_instrument_cons]
        rcases v with _ | v
        · simp
        · by_cases h : v.val < n
          · simp only [dif_pos h]
            exact ih _ k (hdj _) (hwj _) _
          · simp only [dif_neg h, Finset.sum_const_zero]
      rw [← Fintype.sum_equiv (Fin.consEquiv fun _ : Fin (k + 1) => Option (Fin W))
        (fun p => recordTerm f W (.instrument n A hA next) (k + 1) x φ (Fin.cons p.1 p.2)) _
        (fun _ => rfl), Fintype.sum_prod_type]
      simp only [key]
      rw [Fintype.sum_option]
      simp only [zero_add]
      exact sum_fin_dite hn (fun j => transcriptSum f (next j) x (A j φ))

/-- The term of an output record. -/
theorem recordTerm_outRec {T : Type*} [AddCommMonoid T] (f : (E →L[ℂ] K) → K → T) (W : ℕ)
    (M : Measured O E) (k : ℕ) (x : X) (φ : K) (r : OutRec W M k) :
    recordTerm f W M k x φ r.1 = f (leafOut W M k r) (purify W M k x φ r.1) := by
  obtain ⟨r, hr⟩ := r
  show (match leafAt W M k r with
    | none => 0
    | some o => f o.1 (purify W M k x φ r)) = f ((leafAt W M k r).get hr).1 (purify W M k x φ r)
  revert hr
  generalize leafAt W M k r = l
  intro hr
  cases l with
  | none => exact absurd hr (by simp)
  | some o => rfl

/-- Records without an output leaf have term zero. -/
theorem recordTerm_of_isSome_eq_false {T : Type*} [AddCommMonoid T] (f : (E →L[ℂ] K) → K → T)
    (W : ℕ) (M : Measured O E) (k : ℕ) (x : X) (φ : K) (r : Rec W k)
    (hr : (leafAt W M k r).isSome = false) : recordTerm f W M k x φ r = 0 := by
  unfold recordTerm
  rw [Option.not_isSome_iff_eq_none.1 (by simp [hr] : ¬ (leafAt W M k r).isSome)]

/-- The decoded purification, summed through `f` over the output records, is the sum over
transcripts. -/
theorem sum_deferOutput (W : ℕ) (M : Measured O E) (k : ℕ) (hd : M.depth ≤ k)
    (hw : M.width ≤ W) (x : X) (φ : K) {T : Type*} [AddCommMonoid T]
    (f : (E →L[ℂ] K) → K → T) (hf : ∀ o, f o 0 = 0) :
    ∑ r, f (leafOut W M k r) (purify W M k x φ r.1) = transcriptSum f M x φ := by
  rw [← sum_recordTerm f hf W M k hd hw x φ,
    ← sum_outRec W M k _ (recordTerm_of_isSome_eq_false f W M k x φ)]
  exact Finset.sum_congr rfl fun r _ => (recordTerm_outRec f W M k x φ r).symm

/-- The heralded output is the transcript sum of the decoded branch projectors. -/
theorem successDensity_eq_transcriptSum (M : Measured O E) (x : X) (φ : K) :
    M.successDensity x φ =
      transcriptSum (fun o ψ => ODEMixedOutput.pureOperator ((o†) ψ)) M x φ := by
  induction M generalizing φ with
  | output out h => rfl
  | reject => rfl
  | call l b next ih => exact ih _
  | instrument n A hA next ih => exact Finset.sum_congr rfl fun j _ => ih j _

/-- The success mass is the transcript sum of the decoded squared norms. -/
theorem successMass_eq_transcriptSum (M : Measured O E) (x : X) (φ : K) :
    M.successMass x φ = transcriptSum (fun o ψ => ‖(o†) ψ‖ ^ 2) M x φ := by
  induction M generalizing φ with
  | output out h => rfl
  | reject => rfl
  | call l b next ih => exact ih _
  | instrument n A hA next ih => exact Finset.sum_congr rfl fun j _ => ih j _

/-- **The decoded purification is the heralded output**: the sum over output records of the
decoded branch projectors is the heralded output of the measured algorithm. -/
theorem sum_pure_deferOutput (W : ℕ) (M : Measured O E) (k : ℕ) (hd : M.depth ≤ k)
    (hw : M.width ≤ W) (x : X) (φ : K) :
    ∑ r, ODEMixedOutput.pureOperator ((((deferOutput W M k)†) (purify W M k x φ)) r) =
      M.successDensity x φ := by
  simp only [adjoint_deferOutput_apply]
  rw [successDensity_eq_transcriptSum]
  exact sum_deferOutput W M k hd hw x φ (fun o ψ => ODEMixedOutput.pureOperator ((o†) ψ))
    fun o => by simp [ODEMixedOutput.pureOperator]

/-- **The decoded purification has the success mass** of the measured algorithm. -/
theorem norm_sq_deferOutput (W : ℕ) (M : Measured O E) (k : ℕ) (hd : M.depth ≤ k)
    (hw : M.width ≤ W) (x : X) (φ : K) :
    ‖((deferOutput W M k)†) (purify W M k x φ)‖ ^ 2 = M.successMass x φ := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [adjoint_deferOutput_apply]
  rw [successMass_eq_transcriptSum]
  exact sum_deferOutput W M k hd hw x φ (fun o ψ => ‖(o†) ψ‖ ^ 2) fun o => by simp

end

end DeferredMeasurementLowerBounds.Deferral
