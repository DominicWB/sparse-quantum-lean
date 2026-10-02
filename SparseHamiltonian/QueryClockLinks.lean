import SparseHamiltonian.QueryNormalForm

/-!
# Uniform individual clock links from oracle syntax

Normal-form links are placed in chronological order.  Each link is a fixed
unitary followed by at most one oracle or adjoint-oracle call.  Their prefix
gauge has exactly the original program's semantics.  The gauge certifies the
identity only; it is not a free implementation of the unknown computation.
-/

namespace SparseHamiltonian.QueryClockLinks

open OracleCircuit QueryNormalForm

noncomputable section

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*}

/-- All free gates and query polarities are fixed before the oracle input is known. -/
abbrev LinkData (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] := FixedGate K × Option Bool

/-- A padding link is the identity, with no query. -/
def identityData : LinkData K := (⟨1, isUnitary_one⟩, none)

/-- Read the gate and query-direction data from the normal form. -/
def dataLinks : NormalForm K → List (LinkData K)
  | .done U => [(U, none)]
  | .step U b p => (U, some b) :: dataLinks p

@[simp] theorem length_dataLinks (p : NormalForm K) :
    (dataLinks p).length = p.count + 1 := by
  induction p with
  | done U => rfl
  | step U b p hp => simp only [dataLinks, List.length_cons, hp, NormalForm.count]

/-- Optional forward or inverse query. -/
def optionalQuery (O : X → K →L[ℂ] K) (b : Option Bool) (x : X) : K →L[ℂ] K :=
  match b with
  | none => 1
  | some c => NormalForm.queryOperator O c x

/-- Its syntactic implementation uses at most one query. -/
def optionalQueryProgram (O : X → K →L[ℂ] K) (b : Option Bool) : Program O :=
  match b with
  | none => Program.identity
  | some c => NormalForm.queryProgram O c

@[simp] theorem eval_optionalQueryProgram (O : X → K →L[ℂ] K)
    (b : Option Bool) (x : X) :
    (optionalQueryProgram O b).eval x = optionalQuery O b x := by
  cases b <;> simp [optionalQueryProgram, optionalQuery]

theorem count_optionalQueryProgram_le_one (O : X → K →L[ℂ] K) (b : Option Bool) :
    (optionalQueryProgram O b).count ≤ 1 := by
  cases b <;> simp [optionalQueryProgram]

/-- A normalised individual link. -/
def dataProgram (O : X → K →L[ℂ] K) (a : LinkData K) : Program O :=
  .seq (.fixed a.1.val a.1.property) (optionalQueryProgram O a.2)

@[simp] theorem eval_dataProgram (O : X → K →L[ℂ] K) (a : LinkData K) (x : X) :
    (dataProgram O a).eval x = a.1.val * optionalQuery O a.2 x := by
  simp [dataProgram]

theorem count_dataProgram_le_one (O : X → K →L[ℂ] K) (a : LinkData K) :
    (dataProgram O a).count ≤ 1 := by
  simpa only [dataProgram, Program.count_seq, Program.count_fixed, zero_add] using
    count_optionalQueryProgram_le_one O a.2

/-- Retaining an explicit identity after the trailing gate changes no semantics. -/
theorem prod_dataLinks (O : X → K →L[ℂ] K) (p : NormalForm K) (x : X) :
    ((dataLinks p).map (fun a => (dataProgram O a).eval x)).prod = p.eval O x := by
  induction p with
  | done U => simp [dataLinks, optionalQuery, NormalForm.eval]
  | step U b p hp =>
      simp only [dataLinks, List.map_cons, List.prod_cons, hp, NormalForm.eval]
      rw [eval_dataProgram]
      rfl

/-- Canonical conversion of a proved unitary operator into a Hilbert equivalence. -/
def unitaryEquiv (U : K →L[ℂ] K) (hU : IsUnitary U) : K ≃ₗᵢ[ℂ] K :=
  Unitary.linearIsometryEquiv ⟨U, Unitary.mem_iff.mpr hU⟩

@[simp] theorem unitaryEquiv_apply (U : K →L[ℂ] K) (hU : IsUnitary U) (v : K) :
    unitaryEquiv U hU v = U v := rfl

/-- The actual unitary equivalence implemented by one link. -/
def dataEquiv (O : X → K →L[ℂ] K) (hO : ∀ x, IsUnitary (O x))
    (a : LinkData K) (x : X) : K ≃ₗᵢ[ℂ] K :=
  unitaryEquiv ((dataProgram O a).eval x) ((dataProgram O a).eval_unitary hO x)

@[simp] theorem dataEquiv_apply (O : X → K →L[ℂ] K) (hO : ∀ x, IsUnitary (O x))
    (a : LinkData K) (x : X) (v : K) :
    dataEquiv O hO a x v = (a.1.val * optionalQuery O a.2 x) v := by
  change (dataProgram O a).eval x v = _
  rw [eval_dataProgram]

/-- Chronological accumulation multiplies the last executed link on the left. -/
theorem prefixGauge_data (O : X → K →L[ℂ] K) (hO : ∀ x, IsUnitary (O x))
    (ds : List (LinkData K)) (x : X) (n : ℕ) (hn : n ≤ ds.length) (v : K) :
    ClockGauge.prefixGauge (fun j => dataEquiv O hO (ds.getD j identityData) x) n v =
      (((ds.take n).reverse.map (fun a => (dataProgram O a).eval x)).prod) v := by
  induction n with
  | zero => simp [ClockGauge.prefixGauge]
  | succ n ih =>
      have hlt : n < ds.length := by omega
      have hn' : n ≤ ds.length := by omega
      rw [List.take_succ_eq_append_getElem hlt, List.reverse_append,
        List.map_append, List.prod_append]
      simp only [List.reverse_singleton, List.map_singleton, List.prod_singleton]
      change dataEquiv O hO (ds.getD n identityData) x
        (ClockGauge.prefixGauge (fun j => dataEquiv O hO (ds.getD j identityData) x) n v) = _
      rw [ih hn']
      have hd : ds.getD n identityData = ds[n] := by
        simp [List.getD_eq_getElem?_getD, hlt]
      rw [hd]
      rfl

/-- Fixed classical data for the chronological clock links of a program. -/
def clockLinkData {O : X → K →L[ℂ] K} (p : Program O) (j : ℕ) : LinkData K :=
  (dataLinks (normalize p)).reverse.getD j identityData

/-- The associated Hilbert-space links, evaluated at the unknown input. -/
def clockLinkEquiv {O : X → K →L[ℂ] K} (p : Program O)
    (hO : ∀ x, IsUnitary (O x)) (x : X) (j : ℕ) : K ≃ₗᵢ[ℂ] K :=
  dataEquiv O hO (clockLinkData p j) x

/-- Uniform one-query factorization at every link, including padded indices. -/
theorem clockLinkEquiv_factor {O : X → K →L[ℂ] K} (p : Program O)
    (hO : ∀ x, IsUnitary (O x)) (x : X) (j : ℕ) :
    (clockLinkEquiv p hO x j).toContinuousLinearEquiv.toContinuousLinearMap =
      (clockLinkData p j).1.val * optionalQuery O (clockLinkData p j).2 x := by
  ext v
  exact dataEquiv_apply O hO _ x v

/-- The prefix product is exactly the original oracle computation. -/
theorem prefixGauge_clockLinkEquiv {O : X → K →L[ℂ] K} (p : Program O)
    (hO : ∀ x, IsUnitary (O x)) (x : X) (v : K) :
    ClockGauge.prefixGauge (clockLinkEquiv p hO x) (p.count + 1) v = p.eval x v := by
  have hlen : (dataLinks (normalize p)).reverse.length = p.count + 1 := by simp
  have h := prefixGauge_data O hO (dataLinks (normalize p)).reverse x
    (p.count + 1) (by omega) v
  change ClockGauge.prefixGauge
    (fun j => dataEquiv O hO ((dataLinks (normalize p)).reverse.getD j identityData) x)
    (p.count + 1) v = p.eval x v
  simpa only [← hlen, List.take_length, List.reverse_reverse, prod_dataLinks,
    eval_normalize] using h

/-- A clock adds one return slot to its `q+1` links, at most doubling `q+1`. -/
theorem clock_slots_le_twice (q : ℕ) : q + 2 ≤ 2 * (q + 1) := by omega

end

end SparseHamiltonian.QueryClockLinks
