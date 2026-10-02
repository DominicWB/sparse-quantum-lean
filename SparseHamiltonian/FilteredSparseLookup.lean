import SparseHamiltonian.PostprocessedLookup

/-!
# Exact sparse magnitude filtering through two ordinary value queries

A finite additive value code has a fixed decoder into complex numbers, with
zero decoding to zero. Magnitude filters retain the original code or replace
it by zero. Their decoded entries agree exactly with the existing matrix-band
and tail definitions, with no precision or rounding assumption. The original
location lists still cover every retained nonzero entry; only values change.
The oracle certificates concern a fixed clean value-scratch subspace.
-/

namespace SparseHamiltonian.FilteredSparseLookup

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

section Codes
variable {A X Z : Type*} [Zero Z]

/-- Keep codes whose decoded magnitude lies in `(a/2,a]`, otherwise return zero. -/
def bandCode (decode : Z → ℂ) (a : ℝ) (z : Z) : Z := by
  classical
  exact if a / 2 < ‖decode z‖ ∧ ‖decode z‖ ≤ a then z else 0

/-- Keep codes whose decoded magnitude is at most `a`, otherwise return zero. -/
def tailCode (decode : Z → ℂ) (a : ℝ) (z : Z) : Z := by
  classical
  exact if ‖decode z‖ ≤ a then z else 0

@[simp] theorem bandCode_zero (decode : Z → ℂ) (a : ℝ) : bandCode decode a 0 = 0 := by
  simp [bandCode]

@[simp] theorem tailCode_zero (decode : Z → ℂ) (a : ℝ) : tailCode decode a 0 = 0 := by
  simp [tailCode]

/-- Decoding an exact filtered code gives the existing magnitude-band mask. -/
theorem decode_bandCode (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : A → Z) (i : A) :
    decode (bandCode decode a (f i)) = magnitudeBand a (fun j => decode (f j)) i := by
  classical
  unfold bandCode magnitudeBand
  split_ifs <;> simp [hzero]

/-- Decoding an exact tail code gives the existing magnitude-tail mask. -/
theorem decode_tailCode (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : A → Z) (i : A) :
    decode (tailCode decode a (f i)) = magnitudeTail a (fun j => decode (f j)) i := by
  classical
  unfold tailCode magnitudeTail
  split_ifs <;> simp [hzero]

/-- Filtering retains the original address and changes only its value code. -/
def bandTable (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) (x : X) (i : A) : Z :=
  bandCode decode a (f x i)

/-- The low-magnitude value table on the same address type. -/
def tailTable (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) (x : X) (i : A) : Z :=
  tailCode decode a (f x i)

/-- Exact decoded table equality, uniformly for all unknown oracle inputs. -/
theorem decode_bandTable (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : X → A → Z) (x : X) (i : A) :
    decode (bandTable decode a f x i) = magnitudeBand a (fun j => decode (f x j)) i :=
  decode_bandCode decode hzero a (f x) i

/-- Exact decoded tail table equality, uniformly for all unknown oracle inputs. -/
theorem decode_tailTable (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : X → A → Z) (x : X) (i : A) :
    decode (tailTable decode a f x i) = magnitudeTail a (fun j => decode (f x j)) i :=
  decode_tailCode decode hzero a (f x) i

/-- Filtering cannot create a new nonzero decoded entry. -/
theorem band_nonzero_original (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (z : Z) (hz : decode (bandCode decode a z) ≠ 0) : decode z ≠ 0 := by
  classical
  unfold bandCode at hz
  split_ifs at hz with h
  · exact hz
  · exact False.elim (hz hzero)

/-- The exact tail also cannot create a new nonzero decoded entry. -/
theorem tail_nonzero_original (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (z : Z) (hz : decode (tailCode decode a z) ≠ 0) : decode z ≠ 0 := by
  classical
  unfold tailCode at hz
  split_ifs at hz with h
  · exact hz
  · exact False.elim (hz hzero)

/-- The same locator already covers every retained band entry. No compacted
location list or new locator oracle is needed for the value-filtering step. -/
theorem band_locator_coverage {L : Type*} (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : X → A → Z) (loc : X → L → A)
    (hCover : ∀ x i, decode (f x i) ≠ 0 → ∃ l, loc x l = i) :
    ∀ x i, decode (bandTable decode a f x i) ≠ 0 → ∃ l, loc x l = i := by
  intro x i hi
  exact hCover x i (band_nonzero_original decode hzero a (f x i) hi)

/-- Tail values use that very same original locator map. -/
theorem tail_locator_coverage {L : Type*} (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : X → A → Z) (loc : X → L → A)
    (hCover : ∀ x i, decode (f x i) ≠ 0 → ∃ l, loc x l = i) :
    ∀ x i, decode (tailTable decode a f x i) ≠ 0 → ∃ l, loc x l = i := by
  intro x i hi
  exact hCover x i (tail_nonzero_original decode hzero a (f x i) hi)

/-- Row-and-column addresses decode to the actual matrix magnitude band. -/
theorem decode_bandMatrix {n : Type*} (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : X → (n × n) → Z) (x : X) (i j : n) :
    decode (bandTable decode a f x (i, j)) =
      bandMatrix a (fun r c => decode (f x (r, c))) i j := by
  exact decode_bandCode decode hzero a (fun c => f x (i, c)) j

/-- Row-and-column addresses decode to the actual low-magnitude matrix tail. -/
theorem decode_tailMatrix {n : Type*} (decode : Z → ℂ) (hzero : decode 0 = 0)
    (a : ℝ) (f : X → (n × n) → Z) (x : X) (i j : n) :
    decode (tailTable decode a f x (i, j)) =
      tailMatrix a (fun r c => decode (f x (r, c))) i j := by
  exact decode_tailCode decode hzero a (fun c => f x (i, c)) j

end Codes

section Queries
variable {A X Z : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The actual logical addition query for the finite-code magnitude band. -/
def bandLookup (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (A × Z) →L[ℂ] EuclideanSpace ℂ (A × Z) :=
  PostprocessedLookup.logical (fun _ => bandCode decode a) f x

/-- The actual logical addition query for the finite-code tail. -/
def tailLookup (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) (x : X) :
    EuclideanSpace ℂ (A × Z) →L[ℂ] EuclideanSpace ℂ (A × Z) :=
  PostprocessedLookup.logical (fun _ => tailCode decode a) f x

omit [DecidableEq Z] in
/-- Band queries are genuine unitaries, even though decoding need not be injective. -/
theorem bandLookup_unitary (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) (x : X) :
    IsUnitary (bandLookup decode a f x) :=
  PostprocessedLookup.logical_unitary (fun _ => bandCode decode a) f x

omit [DecidableEq Z] in
/-- Tail queries are genuine unitaries on the encoded value register. -/
theorem tailLookup_unitary (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) (x : X) :
    IsUnitary (tailLookup decode a f x) :=
  PostprocessedLookup.logical_unitary (fun _ => tailCode decode a) f x

/-- Every band threshold uses two calls to the same original value lookup.
The fixed zero-scratch encoding is also independent of the threshold. -/
theorem band_two_queries (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) :
    EncodedOracle.ImplementsOn (PostprocessedLookup.oracle (W := Z) f)
      (bandLookup decode a f)
      (PostprocessedLookup.cleanEmbedding (A := A) (W := Z) (Z := Z)).toContinuousLinearMap 2 :=
  PostprocessedLookup.postprocessed_two_queries (fun _ => bandCode decode a) f

/-- The tail has the same two-query cost under that original value oracle. -/
theorem tail_two_queries (decode : Z → ℂ) (a : ℝ) (f : X → A → Z) :
    EncodedOracle.ImplementsOn (PostprocessedLookup.oracle (W := Z) f)
      (tailLookup decode a f)
      (PostprocessedLookup.cleanEmbedding (A := A) (W := Z) (Z := Z)).toContinuousLinearMap 2 :=
  PostprocessedLookup.postprocessed_two_queries (fun _ => tailCode decode a) f

/-- A q-query band-value program compiles into at most 2q original-value queries. -/
theorem compile_band_program (decode : Z → ℂ) (a : ℝ) (f : X → A → Z)
    {F : X → EuclideanSpace ℂ (A × Z) →L[ℂ] EuclideanSpace ℂ (A × Z)} {q : ℕ}
    (h : Implements (bandLookup decode a f) F q) :
    EncodedOracle.ImplementsOn (PostprocessedLookup.oracle (W := Z) f) F
      (PostprocessedLookup.cleanEmbedding (A := A) (W := Z) (Z := Z)).toContinuousLinearMap
      (2 * q) :=
  PostprocessedLookup.compile_processed_program (fun _ => bandCode decode a) f h

/-- A q-query tail-value program has the same factor-two compilation bound. -/
theorem compile_tail_program (decode : Z → ℂ) (a : ℝ) (f : X → A → Z)
    {F : X → EuclideanSpace ℂ (A × Z) →L[ℂ] EuclideanSpace ℂ (A × Z)} {q : ℕ}
    (h : Implements (tailLookup decode a f) F q) :
    EncodedOracle.ImplementsOn (PostprocessedLookup.oracle (W := Z) f) F
      (PostprocessedLookup.cleanEmbedding (A := A) (W := Z) (Z := Z)).toContinuousLinearMap
      (2 * q) :=
  PostprocessedLookup.compile_processed_program (fun _ => tailCode decode a) f h

end Queries
end
end SparseHamiltonian.FilteredSparseLookup
