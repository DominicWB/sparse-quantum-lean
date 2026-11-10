import GeneralDecoder.Native
import GateOptimalBinary.SignedNative

/-!
# The rotation arithmetic of a general decoder

The arithmetic hypothesis of the native theorem (`GateNative.ArithOK`) is stated on all base wires
of the private operation. For the binary sparse oracles the decoded entry is a function of the
value word only, and the arithmetic of the manuscript (Section `gate:sec:result`: "The decoder and
reversible scalar arithmetic must evaluate ... local rotation parameters specified in Section
`gate:sec:native` to accuracy `ξ`") acts on the value word. `RotWordArith b dec ζ bT bP A` is such
an arithmetic for a decoder `dec` of the value words: a reversible circuit of controlled NOT gates
with at most three controls on the value word and `bT + bP + A` arithmetic wires that writes the
angle words of `θ = 2 arctan |dec w|` and `φ = arg (dec w)` within `ζ` and restores its work wires.
`RotWordArith.lift` places it on the value wires of the base wires; `RotWordArith.lift_ok` is the
arithmetic hypothesis of the native theorem for the decoder `dec` of the value word.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GeneralDecoder

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open GateOptimalBinary (cfgRun_map classical_map)
open SparseHamiltonian.GateODE (overwrite_apply_ι overwrite_apply_out)

variable {k b : ℕ}

/-- **The rotation arithmetic of a decoder on the value word**: a reversible circuit of controlled
NOT gates with at most three controls on the value word and `bT + bP + A` arithmetic wires that
writes the angle word of `θ = 2 arctan |dec w|` and the phase word of `φ = arg (dec w)` (for
`dec w ≠ 0`, modulo `2π`) within `ζ`, restoring its work wires. As `GateNative.ArithOK`, it asks
the phase of every nonzero decoded value, also of values whose angle rounds to zero, where the
rotation does not depend on the phase. -/
structure RotWordArith (b : ℕ) (dec : Cfg (VW b) → ℂ) (ζ : ℝ) (bT bP A : ℕ) where
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
  theta : ∀ w, |thetaVal (tw w) - 2 * Real.arctan ‖dec w‖| ≤ ζ
  phi : ∀ w, dec w ≠ 0 →
    ∃ m : ℤ, |phiVal (pw w) - Complex.arg (dec w) - 2 * Real.pi * m| ≤ ζ

theorem vB_injective : Function.Injective (vB (k := k) (b := b)) :=
  fun _ _ h => Sum.inr_injective (Sum.inr_injective h)

/-- **The rotation arithmetic on the base wires**: the circuit placed on the value wires. -/
def RotWordArith.lift (k : ℕ) {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}
    (ar : RotWordArith b dec ζ bT bP A) : Arith (BW k b) where
  bT := bT
  bP := bP
  A := A
  circ := ar.circ.map (GateODE.Gate.map (Sum.map vB id))
  tw := fun y => ar.tw (vword y)
  pw := fun y => ar.pw (vword y)

@[simp] theorem RotWordArith.lift_bT (k : ℕ) {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}
    (ar : RotWordArith b dec ζ bT bP A) : (ar.lift k).bT = bT := rfl

@[simp] theorem RotWordArith.lift_bP (k : ℕ) {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}
    (ar : RotWordArith b dec ζ bT bP A) : (ar.lift k).bP = bP := rfl

@[simp] theorem RotWordArith.lift_A (k : ℕ) {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}
    (ar : RotWordArith b dec ζ bT bP A) : (ar.lift k).A = A := rfl

@[simp] theorem RotWordArith.lift_length (k : ℕ) {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}
    (ar : RotWordArith b dec ζ bT bP A) : (ar.lift k).circ.length = ar.circ.length := by
  simp [RotWordArith.lift]

/-- **The arithmetic hypothesis of the native theorem** for the decoder `dec` of the value word,
from a rotation arithmetic on the value word. -/
theorem RotWordArith.lift_ok (k : ℕ) {dec : Cfg (VW b) → ℂ} {ζ : ℝ} {bT bP A : ℕ}
    (ar : RotWordArith b dec ζ bT bP A) :
    ArithOK (ar.lift k) (Sum.inl (Sum.inr (oPR k))) (fun y => dec (vword y)) ζ where
  elem g hg := by
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    simpa [GateODE.Gate.map] using ar.elem g' hg'
  classical := classical_map (Sum.map_injective.mpr ⟨vB_injective, Function.injective_id⟩)
    ar.classical
  compute x := by
    change cfgRun (ar.circ.map (GateODE.Gate.map (Sum.map vB id)))
        (Sum.elim x (fun _ => false)) =
      Sum.elim x (Sum.elim (Sum.elim (ar.tw (vword x)) (ar.pw (vword x))) (fun _ => false))
    have he : Function.Injective (Sum.map (vB (k := k) (b := b))
        (id : AWr bT bP A → AWr bT bP A)) :=
      Sum.map_injective.mpr ⟨vB_injective, Function.injective_id⟩
    have h1 : (fun a => (Sum.elim x (fun _ => false) : Cfg (BW k b ⊕ AWr bT bP A))
        (Sum.map vB id a)) = Sum.elim (vword x) (fun _ => false) := by
      funext a
      rcases a with v | a <;> rfl
    rw [cfgRun_map he, h1, ar.compute]
    funext w
    rcases w with m | a
    · by_cases hm : ∃ v, vB v = m
      · obtain ⟨v, rfl⟩ := hm
        exact overwrite_apply_ι he _ _ (Sum.inl v)
      · push Not at hm
        refine overwrite_apply_out _ _ _ _ ?_
        rintro (v | a) h
        · exact hm v (Sum.inl_injective h)
        · cases h
    · exact overwrite_apply_ι he _ _ (Sum.inr a)
  tw_indep x c := by
    change ar.tw (vword (Function.update x oB c)) = ar.tw (vword x)
    rw [vword_update_oB]
  pw_indep x c := by
    change ar.pw (vword (Function.update x oB c)) = ar.pw (vword x)
    rw [vword_update_oB]
  theta x := ar.theta (vword x)
  phi x hx := ar.phi (vword x) hx

end

end SparseHamiltonian.GeneralDecoder
