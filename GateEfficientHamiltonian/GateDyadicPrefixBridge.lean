import GateEfficientHamiltonian.GatePrefixInverse
/-!
# Exact identification of dyadic frames with clean prefix circuits

The recursive dyadic coordinates are converted to ordinary binary-word
amplitudes.  The two-root action at depth `m+1` is exactly the rotation of
bit `m` conditioned on all lower bits being zero.  The smaller frames act
on both values of the spectator high bit.  Thus the recursive frame is
the descending prefix-controlled schedule, whose elementary implementation
and clean ancillas were established independently.

New source; compilation remains to be checked.
-/

namespace SparseHamiltonian.GateDyadicPrefixBridge

noncomputable section

open scoped BigOperators

/-- The amplitude vector, in the ordinary computational basis. -/
def amplitudes (m : ℕ) (u : GateDyadicBoundary.Private m) : GatePrefixCircuit.SlotState m :=
  Finsupp.equivFunOnFinite.symm (GateDyadicBoundary.readPrivate m u)

@[simp] theorem amplitudes_apply (m : ℕ) (u : GateDyadicBoundary.Private m) (w : GatePrefixCircuit.Word m) :
    amplitudes m u w = GateDyadicBoundary.readPrivate m u w := rfl

theorem amplitudes_injective (m : ℕ) : Function.Injective (amplitudes m) := by
  intro u v h
  have hc : GateDyadicBoundary.readPrivate m u = GateDyadicBoundary.readPrivate m v := by
    funext w
    exact congrArg (fun f : GatePrefixCircuit.SlotState m => f w) h
  have hh := congrArg (GateDyadicBoundary.makePrivate m) hc
  simpa only [GateDyadicBoundary.makePrivate_readPrivate] using hh

theorem prefix_snoc_true_iff {m : ℕ} (b : Bool) (w : GatePrefixCircuit.Word m) :
    GatePrefixCircuit.prefixBit (GateDyadicBoundary.snocWord b w) m = true ↔
      w = (fun _ => false) := by
  change GatePrefixCircuit.prefixBit (GatePrefixCircuit.withHigh b w) m = true ↔ _
  rw [GatePrefixCircuit.prefix_withHigh w b m le_rfl,
    GatePrefixCircuit.prefix_true_iff w m le_rfl]
  constructor
  · intro h
    funext j
    exact h j j.isLt
  · intro h j hj
    simp [h]

theorem update_high_snoc {m : ℕ} (b t : Bool) (w : GatePrefixCircuit.Word m) :
    Function.update (GateDyadicBoundary.snocWord b w) (Fin.last m) t =
      GateDyadicBoundary.snocWord t w := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [GateDyadicBoundary.snocWord]
  · simp [GateDyadicBoundary.snocWord]

/-- Ordinary row-by-column action of a two-by-two coefficient array. -/
def matrixMix (a : GatePrefixCircuit.Coefficients) (u v : ℂ) : ℂ × ℂ :=
  (a false false * u + a false true * v,
   a true false * u + a true true * v)

/-- Only the roots of the two half-blocks are changed by a high-bit rotation. -/
def topMix (a : GatePrefixCircuit.Coefficients) {m : ℕ} (u : GateDyadicBoundary.Private (m + 1)) :
    GateDyadicBoundary.Private (m + 1) :=
  let roots := matrixMix a u.1 u.2.2.1
  GateDyadicBoundary.joinPrivate (roots.1, u.2.1) (roots.2, u.2.2.2)

/-- Generic recursive frame, allowing independent known rotations at each bit. -/
def frame (a : ℕ → GatePrefixCircuit.Coefficients) : (m : ℕ) → GateDyadicBoundary.Private m → GateDyadicBoundary.Private m
  | 0, u => u
  | m + 1, u =>
      let roots := topMix (a m) u
      let halves := GateDyadicBoundary.splitPrivate roots
      GateDyadicBoundary.joinPrivate (frame a m halves.1) (frame a m halves.2)

def half {m : ℕ} (b : Bool) (u : GateDyadicBoundary.Private (m + 1)) :
    GateDyadicBoundary.Private m :=
  if b then (GateDyadicBoundary.splitPrivate u).2 else (GateDyadicBoundary.splitPrivate u).1

theorem read_snoc {m : ℕ} (b : Bool) (u : GateDyadicBoundary.Private (m + 1))
    (w : GatePrefixCircuit.Word m) :
    GateDyadicBoundary.readPrivate (m + 1) u (GateDyadicBoundary.snocWord b w) =
      GateDyadicBoundary.readPrivate m (half b u) w := by
  rcases u with ⟨a, l, c, r⟩
  cases b <;> simp [half, GateDyadicBoundary.readPrivate,
    GateDyadicBoundary.splitPrivate, GateDyadicBoundary.snocWord]

def slice {m : ℕ} (b : Bool) (f : GatePrefixCircuit.SlotState (m + 1)) :
    GatePrefixCircuit.SlotState m :=
  Finsupp.equivFunOnFinite.symm (fun w => f (GateDyadicBoundary.snocWord b w))

theorem slice_amplitudes {m : ℕ} (b : Bool) (u : GateDyadicBoundary.Private (m + 1)) :
    slice b (amplitudes (m + 1) u) = amplitudes m (half b u) := by
  ext w
  exact read_snoc b u w

theorem frame_snoc (a : ℕ → GatePrefixCircuit.Coefficients) {m : ℕ}
    (b : Bool) (u : GateDyadicBoundary.Private (m + 1)) (w : GatePrefixCircuit.Word m) :
    GateDyadicBoundary.readPrivate (m + 1) (frame a (m + 1) u)
        (GateDyadicBoundary.snocWord b w) =
      GateDyadicBoundary.readPrivate m (frame a m (half b (topMix (a m) u))) w := by
  cases b <;> simp [frame, half, GateDyadicBoundary.readPrivate_join_false,
    GateDyadicBoundary.readPrivate_join_true]

/-- The high-bit ideal step is precisely the independently defined two-root
mix, including its action on every non-root amplitude. -/
theorem amplitudes_topMix {m : ℕ} (a : GatePrefixCircuit.Coefficients)
    (u : GateDyadicBoundary.Private (m + 1)) :
    amplitudes (m + 1) (topMix a u) =
      GatePrefixCircuit.idealStep (Fin.last m) a (amplitudes (m + 1) u) := by
  classical
  rcases u with ⟨p, l, q, r⟩
  have hslice (b : Bool) (x : GatePrefixCircuit.Word m) :
      amplitudes (m + 1) (topMix a (p, l, q, r)) (GateDyadicBoundary.snocWord b x) =
        GatePrefixCircuit.idealStep (Fin.last m) a
          (amplitudes (m + 1) (p, l, q, r)) (GateDyadicBoundary.snocWord b x) := by
    rw [GatePrefixCircuit.idealStep_apply]
    by_cases hx : x = (fun _ => false)
    · have hp : GatePrefixCircuit.prefixBit (GateDyadicBoundary.snocWord b x) m = true :=
        (prefix_snoc_true_iff b x).2 hx
      rw [Fin.val_last, hp]
      subst x
      cases b <;>
        simp [topMix, matrixMix, GateDyadicBoundary.joinPrivate, update_high_snoc,
          GateDyadicBoundary.snocWord_last, read_snoc, half,
          GateDyadicBoundary.splitPrivate, GateDyadicBoundary.readPrivate_zero,
          add_comm]
    · have hp : GatePrefixCircuit.prefixBit (GateDyadicBoundary.snocWord b x) m = false := by
        cases h : GatePrefixCircuit.prefixBit (GateDyadicBoundary.snocWord b x) m
        · rfl
        · exact False.elim (hx ((prefix_snoc_true_iff b x).1 h))
      rw [Fin.val_last, hp]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases b
      · simp only [amplitudes_apply, topMix, GateDyadicBoundary.joinPrivate,
          read_snoc, half, GateDyadicBoundary.splitPrivate, Bool.false_eq_true, if_false]
        have hh := GateDyadicBoundary.readPrivate_replace_root m (p, l)
          (matrixMix a p q).1 x
        simpa only [hx, if_false] using hh
      · simp only [amplitudes_apply, topMix, GateDyadicBoundary.joinPrivate,
          read_snoc, half, GateDyadicBoundary.splitPrivate, if_true]
        have hh := GateDyadicBoundary.readPrivate_replace_root m (q, r)
          (matrixMix a p q).2 x
        simpa only [hx, if_false] using hh
  ext w
  have h := hslice (w (Fin.last m)) (GateDyadicBoundary.tailWord w)
  simpa only [GateDyadicBoundary.snocWord_tailWord] using h

/-- The complete descending ideal schedule equals the recursive dyadic frame
on arbitrary binary-word amplitudes. -/
theorem amplitudes_frame (a : ℕ → GatePrefixCircuit.Coefficients)
    (m : ℕ) (u : GateDyadicBoundary.Private m) :
    amplitudes m (frame a m u) =
      GatePrefixCircuit.ideal (fun j : Fin m => a j.val) m le_rfl (amplitudes m u) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [GatePrefixCircuit.ideal, LinearMap.comp_apply]
      change amplitudes (m + 1) (frame a (m + 1) u) =
        GatePrefixCircuit.ideal (fun j : Fin (m + 1) => a j.val) m (by omega)
          (GatePrefixCircuit.idealStep (Fin.last m) (a m) (amplitudes (m + 1) u))
      rw [← amplitudes_topMix]
      have hslice (b : Bool) (x : GatePrefixCircuit.Word m) :
          amplitudes (m + 1) (frame a (m + 1) u) (GateDyadicBoundary.snocWord b x) =
            GatePrefixCircuit.ideal (fun j : Fin (m + 1) => a j.val) m (by omega)
              (amplitudes (m + 1) (topMix (a m) u)) (GateDyadicBoundary.snocWord b x) := by
        rw [amplitudes_apply, frame_snoc]
        change amplitudes m (frame a m (half b (topMix (a m) u))) x = _
        rw [ih]
        have h := GatePrefixCircuit.ideal_restrictHigh
          (fun j : Fin (m + 1) => a j.val) b m le_rfl
          (amplitudes (m + 1) (topMix (a m) u)) x
        change _ = GatePrefixCircuit.ideal (fun j : Fin m => a j.val) m le_rfl
          (slice b (amplitudes (m + 1) (topMix (a m) u))) x at h
        rw [slice_amplitudes] at h
        exact h.symm
      ext w
      have h := hslice (w (Fin.last m)) (GateDyadicBoundary.tailWord w)
      simpa only [GateDyadicBoundary.snocWord_tailWord] using h

def inputCoefficients (z : ℝ) : GatePrefixCircuit.Coefficients := fun row col =>
  match row, col with
  | false, false => (z : ℂ) / (GateDyadicBoundary.rootDenominator z : ℂ)
  | false, true => -1 / (GateDyadicBoundary.rootDenominator z : ℂ)
  | true, false => 1 / (GateDyadicBoundary.rootDenominator z : ℂ)
  | true, true => (z : ℂ) / (GateDyadicBoundary.rootDenominator z : ℂ)

def outputCoefficients (z : ℝ) : GatePrefixCircuit.Coefficients := fun row col =>
  match row, col with
  | false, false => 1 / (GateDyadicBoundary.rootDenominator z : ℂ)
  | false, true => -(z : ℂ) / (GateDyadicBoundary.rootDenominator z : ℂ)
  | true, false => (z : ℂ) / (GateDyadicBoundary.rootDenominator z : ℂ)
  | true, true => 1 / (GateDyadicBoundary.rootDenominator z : ℂ)

theorem matrixMix_input (z : ℝ) (u v : ℂ) :
    matrixMix (inputCoefficients z) u v = GateDyadicBoundary.inputMix z u v := by
  apply Prod.ext <;> simp only [matrixMix, inputCoefficients, GateDyadicBoundary.inputMix] <;> ring

theorem matrixMix_output (z : ℝ) (u v : ℂ) :
    matrixMix (outputCoefficients z) u v = GateDyadicBoundary.outputMix z u v := by
  apply Prod.ext <;> simp only [matrixMix, outputCoefficients, GateDyadicBoundary.outputMix] <;> ring

/-- The generic frame specialised to the actual dyadic input matrices. -/
theorem frame_input (c : ℝ) (m : ℕ) (u : GateDyadicBoundary.Private m) :
    frame (fun j => inputCoefficients (GateDyadicBoundary.centralCosine c j)) m u =
      GateDyadicBoundary.inputFrame c m u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      simp only [frame, topMix, GateDyadicBoundary.splitPrivate_joinPrivate, matrixMix_input,
        GateDyadicBoundary.inputFrame, ih]

/-- The generic frame specialised to the actual dyadic output matrices. -/
theorem frame_output (c : ℝ) (m : ℕ) (u : GateDyadicBoundary.Private m) :
    frame (fun j => outputCoefficients (GateDyadicBoundary.centralCosine c j)) m u =
      GateDyadicBoundary.outputFrame c m u := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rcases u with ⟨a, l, b, r⟩
      simp only [frame, topMix, GateDyadicBoundary.splitPrivate_joinPrivate, matrixMix_output,
        GateDyadicBoundary.outputFrame, ih]

/-- The actual three-gates-per-bit clean circuit implements the dyadic input
frame exactly, on every private amplitude vector. -/
theorem input_circuit_correct (c : ℝ) (m : ℕ) (u : GateDyadicBoundary.Private m) :
    GatePrefixCircuit.run (GatePrefixCircuit.circuit
      (fun j : Fin m => inputCoefficients (GateDyadicBoundary.centralCosine c j.val)))
      (GatePrefixCircuit.embed 0 (amplitudes m u)) =
        GatePrefixCircuit.embed 0 (amplitudes m (GateDyadicBoundary.inputFrame c m u)) := by
  have h := LinearMap.congr_fun (GatePrefixCircuit.circuit_correct
    (fun j : Fin m => inputCoefficients (GateDyadicBoundary.centralCosine c j.val)))
    (amplitudes m u)
  simp only [LinearMap.comp_apply] at h
  rw [← amplitudes_frame (fun j => inputCoefficients (GateDyadicBoundary.centralCosine c j)) m u,
    frame_input] at h
  exact h

/-- The same clean circuit, with the independent output matrices, implements
the dyadic output frame exactly. -/
theorem output_circuit_correct (c : ℝ) (m : ℕ) (u : GateDyadicBoundary.Private m) :
    GatePrefixCircuit.run (GatePrefixCircuit.circuit
      (fun j : Fin m => outputCoefficients (GateDyadicBoundary.centralCosine c j.val)))
      (GatePrefixCircuit.embed 0 (amplitudes m u)) =
        GatePrefixCircuit.embed 0 (amplitudes m (GateDyadicBoundary.outputFrame c m u)) := by
  have h := LinearMap.congr_fun (GatePrefixCircuit.circuit_correct
    (fun j : Fin m => outputCoefficients (GateDyadicBoundary.centralCosine c j.val)))
    (amplitudes m u)
  simp only [LinearMap.comp_apply] at h
  rw [← amplitudes_frame (fun j => outputCoefficients (GateDyadicBoundary.centralCosine c j)) m u,
    frame_output] at h
  exact h

/-- The explicitly reversed elementary circuit realises the inverse input
frame.  The matrix-validity premise is discharged for the concrete dyadic
matrices in `GateDyadicUnitary`; it is not an inverse-frame assumption. -/
theorem input_inverse_circuit_correct_of_unitary (c : ℝ) (m : ℕ)
    (u : GateDyadicBoundary.Private m)
    (ha : ∀ j : Fin m,
      (inputCoefficients (GateDyadicBoundary.centralCosine c j.val)).IsUnitary) :
    GatePrefixCircuit.run (GatePrefixInverse.circuit
      (fun j : Fin m => inputCoefficients (GateDyadicBoundary.centralCosine c j.val)))
      (GatePrefixCircuit.embed 0 (amplitudes m u)) =
        GatePrefixCircuit.embed 0
          (amplitudes m (GateDyadicBoundary.inputFrameInverse c m u)) := by
  have h := LinearMap.congr_fun (GatePrefixInverse.circuit_inverse_clean
    (fun j : Fin m => inputCoefficients (GateDyadicBoundary.centralCosine c j.val)) ha)
    (amplitudes m (GateDyadicBoundary.inputFrameInverse c m u))
  simp only [LinearMap.comp_apply] at h
  rw [← amplitudes_frame (fun j => inputCoefficients (GateDyadicBoundary.centralCosine c j))
      m (GateDyadicBoundary.inputFrameInverse c m u),
    frame_input, GateDyadicBoundary.inputFrame_inputFrameInverse] at h
  exact h

end
end SparseHamiltonian.GateDyadicPrefixBridge
