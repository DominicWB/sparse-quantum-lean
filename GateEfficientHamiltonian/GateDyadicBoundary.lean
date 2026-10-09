import SparseHamiltonian.ImprovedSparseHamiltonian
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
/-!
# Exact compression of the chronological star-rotation boundary network

This file uses a recursive coordinate model of a binary slot register.  There
is one distinguished root slot in each half-register.  `chronological` is
specified by its actual chronological action: first the left half of the
slots, then the right half, sharing the public coordinate.  It is not defined
using the compressed circuit.

`inputFrame` and `outputFrame` are independently defined by one root mixing
followed by the same frame in both halves.  `compressed` uses one central
rotation between the public coordinate and the root.  The principal identity
`chronological_eq_compressed` proves that this circuit is exact.  The recursive
coordinate representation is naturally a binary slot register with `2^m`
leaves; it avoids choosing a particular endianness for that register.

Status: compiles with Lean/Mathlib 4.32.1.
-/

namespace SparseHamiltonian.GateDyadicBoundary

noncomputable section

/-- The normalisation of the two input/output root frames. -/
def rootDenominator (z : ℝ) : ℝ := Real.sqrt (1 + z ^ 2)

theorem rootDenominator_pos (z : ℝ) : 0 < rootDenominator z := by
  unfold rootDenominator
  apply Real.sqrt_pos.2
  positivity

theorem rootDenominator_ne_zero (z : ℝ) : rootDenominator z ≠ 0 :=
  ne_of_gt (rootDenominator_pos z)

theorem rootDenominator_sq (z : ℝ) :
    rootDenominator z ^ 2 = 1 + z ^ 2 := by
  unfold rootDenominator
  apply Real.sq_sqrt
  positivity

/-- Rotation of two complex amplitudes with real cosine and sine. -/
def rotation (z v : ℝ) (p a : ℂ) : ℂ × ℂ :=
  ((z : ℂ) * p - (v : ℂ) * a, (v : ℂ) * p + (z : ℂ) * a)

/-- The input root frame appearing in the dyadic factorisation. -/
def inputMix (z : ℝ) (a b : ℂ) : ℂ × ℂ :=
  (((z : ℂ) * a - b) / (rootDenominator z : ℂ),
    (a + (z : ℂ) * b) / (rootDenominator z : ℂ))

/-- The inverse of the input root frame. -/
def inputUnmix (z : ℝ) (a b : ℂ) : ℂ × ℂ :=
  (((z : ℂ) * a + b) / (rootDenominator z : ℂ),
    (-a + (z : ℂ) * b) / (rootDenominator z : ℂ))

/-- The output root frame appearing in the dyadic factorisation. -/
def outputMix (z : ℝ) (a b : ℂ) : ℂ × ℂ :=
  ((a - (z : ℂ) * b) / (rootDenominator z : ℂ),
    ((z : ℂ) * a + b) / (rootDenominator z : ℂ))

/-- The inverse of the output root frame. -/
def outputUnmix (z : ℝ) (a b : ℂ) : ℂ × ℂ :=
  ((a + (z : ℂ) * b) / (rootDenominator z : ℂ),
    (-(z : ℂ) * a + b) / (rootDenominator z : ℂ))

private theorem rootDenominator_complex_sq (z : ℝ) :
    (rootDenominator z : ℂ) ^ 2 = 1 + (z : ℂ) ^ 2 := by
  exact_mod_cast rootDenominator_sq z

private theorem rootDenominator_complex_ne_zero (z : ℝ) :
    (rootDenominator z : ℂ) ≠ 0 := by
  exact_mod_cast rootDenominator_ne_zero z

theorem inputUnmix_inputMix (z : ℝ) (a b : ℂ) :
    inputUnmix z (inputMix z a b).1 (inputMix z a b).2 = (a, b) := by
  have hd := rootDenominator_complex_ne_zero z
  have hd2 := rootDenominator_complex_sq z
  apply Prod.ext <;> simp only [inputUnmix, inputMix]
  · field_simp
    linear_combination -a * hd2
  · field_simp
    linear_combination -b * hd2

theorem inputMix_inputUnmix (z : ℝ) (a b : ℂ) :
    inputMix z (inputUnmix z a b).1 (inputUnmix z a b).2 = (a, b) := by
  have hd := rootDenominator_complex_ne_zero z
  have hd2 := rootDenominator_complex_sq z
  apply Prod.ext <;> simp only [inputUnmix, inputMix]
  · field_simp
    linear_combination -a * hd2
  · field_simp
    linear_combination -b * hd2

theorem outputUnmix_outputMix (z : ℝ) (a b : ℂ) :
    outputUnmix z (outputMix z a b).1 (outputMix z a b).2 = (a, b) := by
  have hd := rootDenominator_complex_ne_zero z
  have hd2 := rootDenominator_complex_sq z
  apply Prod.ext <;> simp only [outputUnmix, outputMix]
  · field_simp
    linear_combination -a * hd2
  · field_simp
    linear_combination -b * hd2

theorem outputMix_outputUnmix (z : ℝ) (a b : ℂ) :
    outputMix z (outputUnmix z a b).1 (outputUnmix z a b).2 = (a, b) := by
  have hd := rootDenominator_complex_ne_zero z
  have hd2 := rootDenominator_complex_sq z
  apply Prod.ext <;> simp only [outputUnmix, outputMix]
  · field_simp
    linear_combination -a * hd2
  · field_simp
    linear_combination -b * hd2

/-- The three-mode calculation underlying the exact dyadic identity.  The
left side applies the input mixing and then the two chronological rotations.
The right side applies the single doubled rotation and output mixing. -/
theorem two_halves_identity (z v : ℝ) (hunit : z ^ 2 + v ^ 2 = 1)
    (p a b : ℂ) :
    let ab := inputMix z a b
    let pa := rotation z v p ab.1
    let qb := rotation z v pa.1 ab.2
    (qb.1, pa.2, qb.2) =
      let qa := rotation (z * z) (v * rootDenominator z) p a
      let ab' := outputMix z qa.2 b
      (qa.1, ab'.1, ab'.2) := by
  have hd := rootDenominator_complex_ne_zero z
  have hd2 := rootDenominator_complex_sq z
  have hu : (z : ℂ) ^ 2 + (v : ℂ) ^ 2 = 1 := by
    exact_mod_cast hunit
  dsimp only
  apply Prod.ext
  · simp only [rotation, inputMix, Complex.ofReal_mul]
    field_simp
    linear_combination (v : ℂ) * a * hd2
  · apply Prod.ext
    · simp only [rotation, inputMix, outputMix,
        Complex.ofReal_mul]
      field_simp
      ring
    · simp only [rotation, inputMix, outputMix,
        Complex.ofReal_mul]
      field_simp
      linear_combination (b - (z : ℂ) * a) * hu

/-- Cosine of the central rotation for a block of `2^m` slots. -/
def centralCosine (c : ℝ) : ℕ → ℝ
  | 0 => c
  | m + 1 => centralCosine c m * centralCosine c m

/-- Sine of the central rotation, computed with the nonnegative root frame
normalisations.  This equals the positive square root under the unit-circle
and nonnegativity assumptions proved below. -/
def centralSine (c σ : ℝ) : ℕ → ℝ
  | 0 => σ
  | m + 1 => centralSine c σ m * rootDenominator (centralCosine c m)

theorem centralCosine_eq_pow (c : ℝ) (m : ℕ) :
    centralCosine c m = c ^ (2 ^ m) := by
  induction m with
  | zero => simp [centralCosine]
  | succ m ih =>
      rw [centralCosine, ih, pow_succ, pow_mul, pow_two]

theorem central_unit (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) :
    centralCosine c m ^ 2 + centralSine c σ m ^ 2 = 1 := by
  induction m with
  | zero => exact hunit
  | succ m ih =>
      simp only [centralCosine, centralSine, mul_pow, rootDenominator_sq]
      linear_combination (1 + centralCosine c m ^ 2) * ih

theorem centralSine_nonneg (c σ : ℝ) (hσ : 0 ≤ σ) (m : ℕ) :
    0 ≤ centralSine c σ m := by
  induction m with
  | zero => exact hσ
  | succ m ih =>
      exact mul_nonneg ih (le_of_lt (rootDenominator_pos _))

theorem centralSine_eq_sqrt (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (hσ : 0 ≤ σ) (m : ℕ) :
    centralSine c σ m = Real.sqrt (1 - (c ^ (2 ^ m)) ^ 2) := by
  have hu := central_unit c σ hunit m
  have hn := centralSine_nonneg c σ hσ m
  rw [← centralCosine_eq_pow c m]
  have hnonneg : 0 ≤ 1 - centralCosine c m ^ 2 := by nlinarith
  have hroot := Real.sq_sqrt hnonneg
  have hrootnonneg := Real.sqrt_nonneg (1 - centralCosine c m ^ 2)
  nlinarith

/-- A root-separated recursive coordinate system for all the remaining slots.
At successor depth the left root is the overall root, while the right root is
stored alongside the two half-block remainders. -/
def Remainder : ℕ → Type
  | 0 => PUnit
  | m + 1 => Remainder m × (ℂ × Remainder m)

abbrev Private (m : ℕ) := ℂ × Remainder m
abbrev State (m : ℕ) := ℂ × Private m

/-- Split a private register into its two chronological half-blocks. -/
def splitPrivate {m : ℕ} (u : Private (m + 1)) : Private m × Private m :=
  ((u.1, u.2.1), u.2.2)

/-- Join two half-blocks, keeping the left root as the distinguished root. -/
def joinPrivate {m : ℕ} (u v : Private m) : Private (m + 1) :=
  (u.1, u.2, v)

@[simp] theorem splitPrivate_joinPrivate {m : ℕ} (u v : Private m) :
    splitPrivate (joinPrivate u v) = (u, v) := by
  cases u
  rfl

@[simp] theorem joinPrivate_splitPrivate {m : ℕ} (u : Private (m + 1)) :
    joinPrivate (splitPrivate u).1 (splitPrivate u).2 = u := by
  cases u with
  | mk a tail => cases tail; rfl

/-- Binary words, with bit `m` the high bit in a register of width `m+1`. -/
abbrev Word (m : ℕ) := Fin m → Bool

def snocWord {m : ℕ} (b : Bool) (w : Word m) : Word (m + 1) :=
  Fin.lastCases b w

def tailWord {m : ℕ} (w : Word (m + 1)) : Word m :=
  fun j => w j.castSucc

@[simp] theorem snocWord_last {m : ℕ} (b : Bool) (w : Word m) :
    snocWord b w (Fin.last m) = b := by simp [snocWord]

@[simp] theorem tailWord_snocWord {m : ℕ} (b : Bool) (w : Word m) :
    tailWord (snocWord b w) = w := by
  funext j
  simp [tailWord, snocWord]

theorem snocWord_tailWord {m : ℕ} (w : Word (m + 1)) :
    snocWord (w (Fin.last m)) (tailWord w) = w := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [snocWord]
  | cast j => simp [snocWord, tailWord]

/-- Ordinary word amplitudes of the recursive private coordinate register. -/
def readPrivate : (m : ℕ) → Private m → Word m → ℂ
  | 0, u, _ => u.1
  | m + 1, (a, l, b, r), w =>
      if w (Fin.last m) then readPrivate m (b, r) (tailWord w)
      else readPrivate m (a, l) (tailWord w)

/-- Reconstruct the recursive private register from all binary-word amplitudes. -/
def makePrivate : (m : ℕ) → (Word m → ℂ) → Private m
  | 0, f => (f (fun j => Fin.elim0 j), PUnit.unit)
  | m + 1, f => joinPrivate
      (makePrivate m (fun w => f (snocWord false w)))
      (makePrivate m (fun w => f (snocWord true w)))

@[simp] theorem readPrivate_join_false {m : ℕ} (u v : Private m) (w : Word m) :
    readPrivate (m + 1) (joinPrivate u v) (snocWord false w) = readPrivate m u w := by
  rcases u with ⟨a, l⟩
  rcases v with ⟨b, r⟩
  simp [readPrivate, joinPrivate]

@[simp] theorem readPrivate_join_true {m : ℕ} (u v : Private m) (w : Word m) :
    readPrivate (m + 1) (joinPrivate u v) (snocWord true w) = readPrivate m v w := by
  rcases u with ⟨a, l⟩
  rcases v with ⟨b, r⟩
  simp [readPrivate, joinPrivate]

/-- The coordinate representation loses no amplitudes. -/
theorem readPrivate_makePrivate (m : ℕ) (f : Word m → ℂ) (w : Word m) :
    readPrivate m (makePrivate m f) w = f w := by
  induction m with
  | zero =>
      exact congrArg f (Subsingleton.elim _ _)
  | succ m ih =>
      have hw := snocWord_tailWord w
      cases hb : w (Fin.last m) with
      | false =>
          have hww : snocWord false (tailWord w) = w := by simpa [hb] using hw
          rw [← hww]
          simp only [makePrivate, readPrivate_join_false]
          rw [ih]
      | true =>
          have hww : snocWord true (tailWord w) = w := by simpa [hb] using hw
          rw [← hww]
          simp only [makePrivate, readPrivate_join_true]
          rw [ih]

/-- Reconstructing the recursive coordinates is also exact. -/
theorem makePrivate_readPrivate (m : ℕ) (u : Private m) :
    makePrivate m (readPrivate m u) = u := by
  induction m with
  | zero =>
      rcases u with ⟨a, r⟩
      cases r
      rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      have hleft : (fun w => readPrivate (m + 1) (a, l, b, r)
          (snocWord false w)) = readPrivate m (a, l) := by
        funext w
        exact readPrivate_join_false (a, l) (b, r) w
      have hright : (fun w => readPrivate (m + 1) (a, l, b, r)
          (snocWord true w)) = readPrivate m (b, r) := by
        funext w
        exact readPrivate_join_true (a, l) (b, r) w
      simp only [makePrivate, hleft, hright, ih, joinPrivate]

/-- Explicit register-coordinate equivalence used to connect the dyadic
factorisation to the bit-gate implementation. -/
def privateWordEquiv (m : ℕ) : Private m ≃ (Word m → ℂ) where
  toFun := readPrivate m
  invFun := makePrivate m
  left_inv := makePrivate_readPrivate m
  right_inv := fun f => funext (readPrivate_makePrivate m f)

/-- The distinguished root is the all-zero word. -/
theorem readPrivate_zero (m : ℕ) (u : Private m) :
    readPrivate m u (fun _ => false) = u.1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      change readPrivate m (a, l) (fun _ => false) = a
      exact ih (a, l)

/-- Changing only the distinguished root changes only the all-zero word
amplitude.  This is the coordinate fact used by the bit-gate bridge. -/
theorem readPrivate_replace_root (m : ℕ) (u : Private m) (a' : ℂ)
    (w : Word m) :
    readPrivate m (a', u.2) w =
      if w = (fun _ => false) then a' else readPrivate m u w := by
  classical
  induction m with
  | zero =>
      have hw : w = (fun _ => false) := Subsingleton.elim _ _
      simp only [readPrivate, hw, ↓reduceIte]
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      cases hb : w (Fin.last m) with
      | false =>
          have hz : w = (fun _ => false) ↔ tailWord w = (fun _ => false) := by
            constructor
            · intro hw
              subst w
              rfl
            · intro ht
              funext j
              induction j using Fin.lastCases with
              | last => exact hb
              | cast j => exact congrFun ht j
          simp only [readPrivate, hb, Bool.false_eq_true, ↓reduceIte, hz]
          exact ih (a, l) (tailWord w)
      | true =>
          have hz : w ≠ (fun _ => false) := by
            intro hw
            have h := congrFun hw (Fin.last m)
            rw [hb] at h
            cases h
          simp only [readPrivate, hb, ↓reduceIte, hz]

/-- Chronological star rotations: apply every left-half rotation before every
right-half rotation.  Both halves act on the same public coordinate. -/
def chronological (c σ : ℝ) : (m : ℕ) → State m → State m
  | 0, (p, a, r) =>
      let q := rotation c σ p a
      (q.1, q.2, r)
  | m + 1, (p, a, l, b, r) =>
      let left := chronological c σ m (p, a, l)
      let right := chronological c σ m (left.1, b, r)
      (right.1, left.2.1, left.2.2, right.2)

/-- Input frame: one mix of the half-block roots, followed by the identical
smaller frame on each half.  The latter is one common bit schedule, not a
list of separately charged gates for each branch. -/
def inputFrame (c : ℝ) : (m : ℕ) → Private m → Private m
  | 0, u => u
  | m + 1, (a, l, b, r) =>
      let roots := inputMix (centralCosine c m) a b
      joinPrivate (inputFrame c m (roots.1, l)) (inputFrame c m (roots.2, r))

/-- Explicit inverse input frame; no abstract inverse is postulated. -/
def inputFrameInverse (c : ℝ) : (m : ℕ) → Private m → Private m
  | 0, u => u
  | m + 1, (a, l, b, r) =>
      let left := inputFrameInverse c m (a, l)
      let right := inputFrameInverse c m (b, r)
      let roots := inputUnmix (centralCosine c m) left.1 right.1
      (roots.1, left.2, roots.2, right.2)

/-- Output frame, with its independent one-root mixing coefficients. -/
def outputFrame (c : ℝ) : (m : ℕ) → Private m → Private m
  | 0, u => u
  | m + 1, (a, l, b, r) =>
      let roots := outputMix (centralCosine c m) a b
      joinPrivate (outputFrame c m (roots.1, l)) (outputFrame c m (roots.2, r))

/-- Explicit inverse output frame. -/
def outputFrameInverse (c : ℝ) : (m : ℕ) → Private m → Private m
  | 0, u => u
  | m + 1, (a, l, b, r) =>
      let left := outputFrameInverse c m (a, l)
      let right := outputFrameInverse c m (b, r)
      let roots := outputUnmix (centralCosine c m) left.1 right.1
      (roots.1, left.2, roots.2, right.2)

/-- Central rotation acts only on the public mode and distinguished root. -/
def central (c σ : ℝ) (m : ℕ) (x : State m) : State m :=
  let q := rotation (centralCosine c m) (centralSine c σ m) x.1 x.2.1
  (q.1, q.2, x.2.2)

/-- Actual compact circuit, including the explicit inverse input frame. -/
def compressed (c σ : ℝ) (m : ℕ) (x : State m) : State m :=
  let input := inputFrameInverse c m x.2
  let q := central c σ m (x.1, input)
  (q.1, outputFrame c m q.2)

/-- The input frame and its explicitly constructed inverse cancel. -/
theorem inputFrameInverse_inputFrame (c : ℝ) (m : ℕ) (u : Private m) :
    inputFrameInverse c m (inputFrame c m u) = u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      simp only [inputFrame, inputFrameInverse, joinPrivate, ih]
      have h := inputUnmix_inputMix (centralCosine c m) a b
      exact congrArg (fun roots : ℂ × ℂ => (roots.1, l, roots.2, r)) h

/-- Cancellation in the other order, needed to express the chronological
network as the compact circuit on an arbitrary input. -/
theorem inputFrame_inputFrameInverse (c : ℝ) (m : ℕ) (u : Private m) :
    inputFrame c m (inputFrameInverse c m u) = u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      simp only [inputFrameInverse, inputFrame]
      have h := inputMix_inputUnmix (centralCosine c m)
        (inputFrameInverse c m (a, l)).1 (inputFrameInverse c m (b, r)).1
      change joinPrivate
        (inputFrame c m ((inputMix (centralCosine c m)
          (inputUnmix (centralCosine c m)
            (inputFrameInverse c m (a, l)).1
            (inputFrameInverse c m (b, r)).1).1
          (inputUnmix (centralCosine c m)
            (inputFrameInverse c m (a, l)).1
            (inputFrameInverse c m (b, r)).1).2).1,
          (inputFrameInverse c m (a, l)).2))
        (inputFrame c m ((inputMix (centralCosine c m)
          (inputUnmix (centralCosine c m)
            (inputFrameInverse c m (a, l)).1
            (inputFrameInverse c m (b, r)).1).1
          (inputUnmix (centralCosine c m)
            (inputFrameInverse c m (a, l)).1
            (inputFrameInverse c m (b, r)).1).2).2,
          (inputFrameInverse c m (b, r)).2)) = (a, l, b, r)
      rw [h]
      simp only [Prod.mk.eta, ih, joinPrivate]; rfl

/-- The output frame and its explicit inverse cancel. -/
theorem outputFrameInverse_outputFrame (c : ℝ) (m : ℕ) (u : Private m) :
    outputFrameInverse c m (outputFrame c m u) = u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      simp only [outputFrame, outputFrameInverse, joinPrivate, ih]
      have h := outputUnmix_outputMix (centralCosine c m) a b
      exact congrArg (fun roots : ℂ × ℂ => (roots.1, l, roots.2, r)) h

/-- Compression expressed without abstract adjoints: input framing followed
by all chronological rotations equals the single central rotation followed
by output framing. -/
theorem chronological_inputFrame (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) (p : ℂ) (u : Private m) :
    chronological c σ m (p, inputFrame c m u) =
      let q := central c σ m (p, u)
      (q.1, outputFrame c m q.2) := by
  induction m generalizing p with
  | zero =>
      rcases u with ⟨a, r⟩
      rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      simp only [inputFrame, chronological, joinPrivate]
      rw [ih, ih]
      simp only [central, centralCosine, centralSine, outputFrame, joinPrivate]
      have h := two_halves_identity (centralCosine c m) (centralSine c σ m)
        (central_unit c σ hunit m) p a b
      exact congrArg (fun q : ℂ × ℂ × ℂ =>
        (q.1, joinPrivate (outputFrame c m (q.2.1, l))
          (outputFrame c m (q.2.2, r)))) h

/-- Exact dyadic boundary-circuit identity on every input.  No assumption on
an underlying private walk, and in particular no involution condition, occurs
in this theorem. -/
theorem chronological_eq_compressed (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) (x : State m) :
    chronological c σ m x = compressed c σ m x := by
  rcases x with ⟨p, u⟩
  have h := chronological_inputFrame c σ hunit m p (inputFrameInverse c m u)
  rw [inputFrame_inputFrameInverse] at h
  exact h

/-- Square-root parametrisation used in the manuscript; it produces exactly
the central cosine `c^(2^m)` and the nonnegative corresponding sine. -/
theorem chronological_sqrt_eq_compressed (c : ℝ) (hc : c ^ 2 ≤ 1)
    (m : ℕ) (x : State m) :
    chronological c (Real.sqrt (1 - c ^ 2)) m x =
      compressed c (Real.sqrt (1 - c ^ 2)) m x := by
  apply chronological_eq_compressed
  rw [Real.sq_sqrt (sub_nonneg.mpr hc)]
  ring

/-- Total squared amplitude of a private binary register. -/
def privateEnergy : (m : ℕ) → Private m → ℝ
  | 0, (a, _) => ‖a‖ ^ 2
  | m + 1, (a, l, b, r) =>
      privateEnergy m (a, l) + privateEnergy m (b, r)

def stateEnergy (m : ℕ) (x : State m) : ℝ :=
  ‖x.1‖ ^ 2 + privateEnergy m x.2

theorem rotation_energy (z v : ℝ) (hunit : z ^ 2 + v ^ 2 = 1)
    (p a : ℂ) :
    ‖(rotation z v p a).1‖ ^ 2 + ‖(rotation z v p a).2‖ ^ 2 =
      ‖p‖ ^ 2 + ‖a‖ ^ 2 := by
  have h := LocalRotation.rotation_energy z v a p (by linarith)
  simpa only [rotation, smul_eq_mul, add_comm] using h

/-- Energy conservation of the actual chronological network, before using
its compressed implementation. -/
theorem chronological_energy (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (m : ℕ) (x : State m) :
    stateEnergy m (chronological c σ m x) = stateEnergy m x := by
  induction m with
  | zero =>
      rcases x with ⟨p, a, r⟩
      exact rotation_energy c σ hunit p a
  | succ m ih =>
      rcases x with ⟨p, a, l, b, r⟩
      have hl := ih (p, a, l)
      have hr := ih ((chronological c σ m (p, a, l)).1, b, r)
      simp only [stateEnergy, privateEnergy, chronological] at hl hr ⊢
      linarith

/-- The compact circuit preserves exactly the same total squared amplitude
as the chronological sequence. -/
theorem compressed_energy (c σ : ℝ) (hunit : c ^ 2 + σ ^ 2 = 1)
    (m : ℕ) (x : State m) :
    stateEnergy m (compressed c σ m x) = stateEnergy m x := by
  rw [← chronological_eq_compressed c σ hunit]
  exact chronological_energy c σ hunit m x

end

end SparseHamiltonian.GateDyadicBoundary
