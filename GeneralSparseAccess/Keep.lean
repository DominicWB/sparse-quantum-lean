import GeneralSparseAccess.ImplOK
import GateEfficientSynthesis.Circuit

/-!
# Synthesis of the gates outside a finite gate set

`keepC hS ζ C` replaces every elementary gate of the native circuit `C` outside the finite gate set
`𝒢` by its synthesis at accuracy `ζ` (`GateSynth.synthRep`) and keeps the gates of `𝒢` and the
calls: every gate of the result is a gate of `𝒢` (`keepC_spec`), the result has at most
`nGatesN C + nGatesOut 𝒢 C · L ζ` gates and exactly the calls of `C`, and on clean ancillas its
full-output error exceeds that of `C` by at most `nGatesN C · ζ` (`keepC_error`).

`nGatesOut_subst_le`: substituting implementations with at most `G` gates into a circuit over `𝒢`
leaves at most `G` gates outside `𝒢` per call.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralSparseAccess

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth
open SparseHamiltonian.OracleCircuit
open scoped InnerProduct

/-! ### Gates outside the gate set -/

section Out

variable {V Y J : Type*}

open Classical in
/-- Is an elementary gate outside the gate set `𝒢`. -/
def isOut (𝒢 : Set Kind) : NInstr V Y J → Bool
  | .gate g => !decide (GateOf 𝒢 g)
  | .call _ _ _ => false

/-- The number of elementary gates outside the gate set `𝒢`. -/
def nGatesOut (𝒢 : Set Kind) (is : List (NInstr V Y J)) : ℕ := is.countP (isOut 𝒢)

theorem nGatesOut_append (𝒢 : Set Kind) (is js : List (NInstr V Y J)) :
    nGatesOut 𝒢 (is ++ js) = nGatesOut 𝒢 is + nGatesOut 𝒢 js := List.countP_append ..

theorem nGatesOut_le (𝒢 : Set Kind) (is : List (NInstr V Y J)) : nGatesOut 𝒢 is ≤ nGatesN is := by
  unfold nGatesOut nGatesN
  apply List.countP_mono_left
  intro i _ hi
  cases i with
  | gate g => rfl
  | call j adj pos => simp [isOut] at hi

theorem nGatesOut_cons (𝒢 : Set Kind) (i : NInstr V Y J) (is : List (NInstr V Y J)) :
    nGatesOut 𝒢 (i :: is) = nGatesOut 𝒢 is + (if isOut 𝒢 i then 1 else 0) := by
  unfold nGatesOut
  rw [List.countP_cons]

/-- **Gates outside `𝒢` after a substitution**: substituting implementations with at most `G`
gates into a circuit over `𝒢` leaves at most `G` gates outside `𝒢` per call. -/
theorem nGatesOut_subst_le {Y' J' A : Type*} (𝒢 : Set Kind) (impl : J' → List (NInstr (Y' ⊕ A) Y J)) (G : ℕ)
    (hG : ∀ j, nGatesN (impl j) ≤ G) (C : List (NInstr V Y' J'))
    (hC : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g) :
    nGatesOut 𝒢 (subst impl C) ≤ G * nCallsN (fun _ => true) C := by
  induction C with
  | nil => simp [nGatesOut, nCallsN]
  | cons i C ih =>
      have hC' : ∀ g, NInstr.gate g ∈ C → GateOf 𝒢 g :=
        fun g hg => hC g (List.mem_cons_of_mem _ hg)
      rw [subst_cons, nGatesOut_append]
      cases i with
      | gate g =>
          have hg : GateOf 𝒢 (GateODE.Gate.map (Sum.inl : V → V ⊕ A) g) :=
            (hC g List.mem_cons_self).map (⟨Sum.inl, Sum.inl_injective⟩ : V ↪ V ⊕ A)
          have h1 : nGatesOut 𝒢 (substI impl (NInstr.gate g : NInstr V Y' J')) = 0 := by
            change nGatesOut 𝒢 [NInstr.gate (GateODE.Gate.map Sum.inl g)] = 0
            simp [nGatesOut, isOut, hg]
          have h2 : nCallsN (fun _ => true) (NInstr.gate g :: C) =
              nCallsN (fun _ => true) C := by
            simp [nCallsN, NInstr.isCall]
          rw [h1, h2, zero_add]
          exact ih hC'
      | call j adj pos =>
          have h1 : nGatesOut 𝒢 (substI impl (NInstr.call j adj pos : NInstr V Y' J')) ≤ G := by
            refine (nGatesOut_le 𝒢 _).trans ?_
            change nGatesN ((implAdj impl j adj).map (NInstr.map (callEmb pos))) ≤ G
            rw [nGatesN_map]
            unfold implAdj
            cases adj
            · exact hG j
            · rw [if_pos rfl, nGatesN_ninv]
              exact hG j
          have h2 : nCallsN (fun _ => true) (NInstr.call j adj pos :: C) =
              nCallsN (fun _ => true) C + 1 := by
            simp [nCallsN, NInstr.isCall]
          rw [h2, mul_add, mul_one]
          have := ih hC'
          omega

end Out

/-! ### Synthesis of the gates outside the gate set -/

section Keep

variable {V Y J X : Type*} [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
  [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

open Classical in
/-- A gate of `𝒢` is kept; any other gate is synthesised at accuracy `ζ`. -/
def keepRep (hS : Synthesis 𝒢 X L) (ζ : ℝ) (g : Gate V) : List (Gate (V ⊕ X)) :=
  if GateOf 𝒢 g then [GateODE.Gate.map Sum.inl g] else synthRep hS ζ g

/-- **The synthesis of the gates outside `𝒢`**: every gate of `𝒢` and every call kept, every other
gate synthesised at accuracy `ζ`. -/
def keepC (hS : Synthesis 𝒢 X L) (ζ : ℝ) (C : List (NInstr V Y J)) : List (NInstr (V ⊕ X) Y J) :=
  replace (keepRep hS ζ) C

theorem length_synthRep_le (hS : Synthesis 𝒢 X L) (ζ : ℝ) (g : Gate V) :
    (synthRep hS ζ g).length ≤ L ζ := by
  unfold synthRep
  split_ifs with h
  · exact (Classical.choose_spec (exists_rep hS g h.1 h.2)).2.1
  · simp

omit [Fintype Y] [DecidableEq Y] in
theorem length_keepRep_le (hS : Synthesis 𝒢 X L) (ζ : ℝ) (g : Gate V) :
    (keepRep hS ζ g).length ≤ 1 + (if isOut 𝒢 (NInstr.gate g : NInstr V Y J) then L ζ else 0) := by
  classical
  unfold keepRep
  by_cases hg : GateOf 𝒢 g
  · simp [hg]
  · have h1 : isOut 𝒢 (NInstr.gate g : NInstr V Y J) = true := by simp [isOut, hg]
    rw [if_neg hg, if_pos h1]
    have := length_synthRep_le hS ζ g
    omega

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

omit [Fintype Y] [DecidableEq Y] in
theorem keepRep_spec (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (g : Gate V) (hg : GateOK 3 g) :
    (∀ h ∈ keepRep hS ζ g, GateOK 3 h ∧ GateOf 𝒢 h) ∧
      ApproxOn (Q := R) CleanX (gRun (keepRep hS ζ g)) (liftB (X := X) (Gate.op g)) ζ := by
  classical
  unfold keepRep
  by_cases hG : GateOf 𝒢 g
  · rw [if_pos hG]
    refine ⟨?_, ?_⟩
    · intro h hh
      rw [List.mem_singleton] at hh
      subst hh
      exact ⟨gateOK_map ⟨Sum.inl, Sum.inl_injective⟩ hg, hG.map ⟨Sum.inl, Sum.inl_injective⟩⟩
    · refine (ApproxOn.of_agrees (fun ψ _ => ?_)).mono hζ.le
      rw [liftB_op_eq]
  · rw [if_neg hG]
    have hsp := synthRep_spec hS hζ g hg
    exact ⟨hsp.1, approxOn_rep g hg _ (fun h hh => (hsp.1 h hh).1) hζ.le hsp.2.2⟩

omit [Fintype Y] [DecidableEq Y] in
/-- **Validity, gate set and counts of the synthesis of the gates outside `𝒢`.** -/
theorem keepC_spec (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) :
    (∀ i ∈ keepC hS ζ C, i.Valid) ∧ (∀ g, NInstr.gate g ∈ keepC hS ζ C → GateOf 𝒢 g) ∧
      nGatesN (keepC hS ζ C) ≤ nGatesN C + nGatesOut 𝒢 C * L ζ ∧
      ∀ p : J → Bool, nCallsN p (keepC hS ζ C) = nCallsN p C := by
  have hgv : ∀ g, NInstr.gate g ∈ C → GateOK 3 g := fun g hg => hC _ hg
  refine ⟨replace_valid _ C hC
    (fun g hg h hh => ((keepRep_spec (R := ℂ) hS hζ g (hgv g hg)).1 h hh).1), ?_, ?_,
    fun p => nCallsN_replace _ p C⟩
  · intro h hh
    obtain ⟨g, hg, hh'⟩ := mem_replace_gate _ C h hh
    exact ((keepRep_spec (R := ℂ) hS hζ g (hgv g hg)).1 h hh').2
  · clear hgv hC
    induction C with
    | nil => simp [keepC, replace, nGatesN, nGatesOut]
    | cons i is ih =>
        cases i with
        | gate g =>
            have hl := length_keepRep_le (Y := Y) (J := J) hS ζ g
            have e1 : nGatesN (NInstr.gate g :: is : List (NInstr V Y J)) = nGatesN is + 1 := by
              simp [nGatesN, NInstr.isGate]
            have e2 : nGatesOut 𝒢 (NInstr.gate g :: is : List (NInstr V Y J)) =
                nGatesOut 𝒢 is + (if isOut 𝒢 (NInstr.gate g : NInstr V Y J) then 1 else 0) :=
              nGatesOut_cons 𝒢 _ is
            change nGatesN (nGatesOf (keepRep hS ζ g) ++ keepC hS ζ is) ≤ _
            rw [nGatesN_append, nGatesN_nGatesOf, e1, e2]
            have ih' := ih
            split_ifs at hl ⊢ with h
            · rw [add_mul, one_mul]
              omega
            · rw [add_zero]
              omega
        | call j adj pos =>
            have e1 : nGatesN (NInstr.call j adj pos :: is : List (NInstr V Y J)) = nGatesN is := by
              simp [nGatesN, NInstr.isGate]
            have e2 : nGatesOut 𝒢 (NInstr.call j adj pos :: is : List (NInstr V Y J)) =
                nGatesOut 𝒢 is := by
              rw [nGatesOut_cons]
              simp [isOut]
            have e3 : nGatesN (keepC hS ζ (NInstr.call j adj pos :: is)) =
                nGatesN (keepC hS ζ is) := by
              simp [keepC, replace, nGatesN, NInstr.isGate]
            rw [e3, e1, e2]
            exact ih

variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

/-- The synthesis of the gates outside `𝒢` approximates the circuit within `nGatesN C * ζ` on clean
ancillas. -/
theorem keepC_approxOn (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) :
    ApproxOn CleanX (nrun prim (keepC hS ζ C)) (liftB (X := X) (nrun prim C))
      (nGatesN C * ζ) := by
  have hgv : ∀ g, NInstr.gate g ∈ C → GateOK 3 g := fun g hg => hC _ hg
  refine approxOn_replace prim hprim _ hζ.le C hC
    (fun g hg h hh => ((keepRep_spec (R := ℂ) hS hζ g (hgv g hg)).1 h hh).1) ?_
  intro g hg
  exact (keepRep_spec hS hζ g (hgv g hg)).2

/-- **The full-output error of the synthesis of the gates outside `𝒢`**: on clean ancillas it adds
at most `nGatesN C * ζ` to the full-output error of `C` along every contractive embedding `E` of
the system register. -/
theorem keepC_error (hS : Synthesis 𝒢 X L) {ζ : ℝ} (hζ : 0 < ζ) (C : List (NInstr V Y J))
    (hC : ∀ i ∈ C, i.Valid) (hprim : ∀ j, IsUnitary (prim j)) {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℂ P]
    (E : P →L[ℂ] Reg V R) (hE : ∀ p, ‖E p‖ ≤ ‖p‖) (U : P →L[ℂ] P) :
    ‖nrun prim (keepC hS ζ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U‖ ≤
      ‖nrun prim C ∘L E - E ∘L U‖ + nGatesN C * ζ := by
  have hδ : 0 ≤ (nGatesN C : ℝ) * ζ := mul_nonneg (Nat.cast_nonneg _) hζ.le
  have h1 := norm_sub_cleanEmb_le (keepC_approxOn prim hS hζ C hC hprim) hδ
  have hEn : ‖E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p => by rw [one_mul]; exact hE p)
  have hcn : ‖(cleanEmb (X := X) : Reg V R →L[ℂ] Reg (V ⊕ X) R)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun ψ => by rw [one_mul, norm_cleanEmb])
  have e : nrun prim (keepC hS ζ C) ∘L (cleanEmb (X := X) ∘L E) - (cleanEmb ∘L E) ∘L U =
      (nrun prim (keepC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C) ∘L E +
        cleanEmb ∘L (nrun prim C ∘L E - E ∘L U) := by
    ext p
    simp only [sub_apply, comp_apply, add_apply, map_sub]
    exact (sub_add_sub_cancel _ _ _).symm
  rw [e]
  calc ‖(nrun prim (keepC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C) ∘L E +
        cleanEmb (X := X) ∘L (nrun prim C ∘L E - E ∘L U)‖
      ≤ ‖nrun prim (keepC hS ζ C) ∘L cleanEmb - cleanEmb ∘L nrun prim C‖ * ‖E‖ +
          ‖(cleanEmb (X := X) : Reg V R →L[ℂ] Reg (V ⊕ X) R)‖ *
            ‖nrun prim C ∘L E - E ∘L U‖ :=
        (norm_add_le _ _).trans (add_le_add (opNorm_comp_le _ _) (opNorm_comp_le _ _))
    _ ≤ (nGatesN C * ζ) * 1 + 1 * ‖nrun prim C ∘L E - E ∘L U‖ := by
        gcongr
    _ = ‖nrun prim C ∘L E - E ∘L U‖ + nGatesN C * ζ := by ring

end Keep

end

end SparseHamiltonian.GeneralSparseAccess
