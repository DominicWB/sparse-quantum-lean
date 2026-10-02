import SparseHamiltonian.MultiQueryNormalForm

/-!
# Genuine distributed clocks extracted from mixed native program syntax

One fixed gate and at most one named forward or inverse query are extracted
for each link. The distributed-clock gauge certifies the identity only; it is
never granted as a gate. Each clock step factors into one fixed routing unitary
and an explicitly selected optional native letter.
-/
namespace SparseHamiltonian.MultiQueryClock

noncomputable section
open ContinuousLinearMap OracleCircuit ClockStepQuery MultiQueryNormalForm
open scoped InnerProduct

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X L : Type*} {O : L → X → K →L[ℂ] K}

abbrev optionalQuery := @MultiQueryNormalForm.optionalQuery

/-- Fixed chronological link data, including identity beyond the program. -/
def clockLinkData (p : MultiOracleCircuit.Program O) (j : ℕ) : LinkData K L :=
  (dataLinks (normalize p)).reverse.getD j identityData

/-- The actual unitary equivalence represented by an extracted mixed link. -/
def dataEquiv (O : L → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (a : LinkData K L) (x : X) : K ≃ₗᵢ[ℂ] K :=
  QueryClockLinks.unitaryEquiv ((dataProgram O a).eval x) ((dataProgram O a).eval_unitary hO x)

@[simp] theorem dataEquiv_apply (O : L → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (a : LinkData K L) (x : X) (v : K) :
    dataEquiv O hO a x v = (a.1.val * optionalQuery O a.2 x) v := by
  change (dataProgram O a).eval x v = _
  rw [dataProgram_eval]

/-- Chronological accumulation of the actual mixed-label links. -/
theorem prefixGauge_data (O : L → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (ds : List (LinkData K L)) (x : X) (n : ℕ) (hn : n ≤ ds.length) (v : K) :
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
    have hd : ds.getD n identityData = ds[n] := by simp [List.getD_eq_getElem?_getD, hlt]
    rw [hd]
    rfl

def clockLinkEquiv (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (x : X) (j : ℕ) : K ≃ₗᵢ[ℂ] K :=
  dataEquiv O hO (clockLinkData p j) x

/-- Every clock link contains its actual fixed native label and query direction. -/
theorem clockLinkEquiv_factor (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (x : X) (j : ℕ) :
    (clockLinkEquiv p hO x j).toContinuousLinearEquiv.toContinuousLinearMap =
      (clockLinkData p j).1.val * optionalQuery O (clockLinkData p j).2 x := by
  ext v
  exact dataEquiv_apply O hO _ x v

/-- The link gauge has exactly the original mixed program's evaluation. -/
theorem prefixGauge_clockLinkEquiv (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (x : X) (v : K) :
    ClockGauge.prefixGauge (clockLinkEquiv p hO x) (p.count + 1) v = p.eval x v := by
  have hlen : (dataLinks (normalize p)).reverse.length = p.count + 1 := by simp
  have h := prefixGauge_data O hO (dataLinks (normalize p)).reverse x
    (p.count + 1) (by omega) v
  change ClockGauge.prefixGauge
    (fun j => dataEquiv O hO ((dataLinks (normalize p)).reverse.getD j identityData) x)
      (p.count + 1) v = p.eval x v
  simpa only [← hlen, List.take_length, List.reverse_reverse, prod_dataLinks,
    eval_normalize] using h

/-- Unitarity plus the proved involution equation implies self-adjointness. -/
theorem program_hermitian (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) (v w : K) :
    inner ℂ (p.eval x v) w = inner ℂ v (p.eval x w) := by
  have hSelf := QueryClockStep.unitary_involution_selfAdjoint (p.eval x)
    (p.eval_unitary hO x) (hInv x)
  rw [← adjoint_inner_right]
  have hAdjoint : (p.eval x)† = p.eval x := hSelf
  rw [hAdjoint]

/-- The actual distributed involution clock, with query-count-plus-two slots. -/
def programClock (p : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    ClockOperators.H (p.count + 1) K →L[ℂ] ClockOperators.H (p.count + 1) K :=
  ClockGauge.distributedClock (p.eval x).toLinearMap (p.count + 1)
    (hInv x) (program_hermitian p hO hInv x)
    (fun j => ClockGauge.prefixGauge (clockLinkEquiv p hO x) j.val)

/-- Fixed selected gates and fixed phased shift; no unknown matrix data. -/
def fixedClockGate (p : MultiOracleCircuit.Program O) :
    ClockOperators.H (p.count + 1) K →L[ℂ] ClockOperators.H (p.count + 1) K :=
  phasedShift (p.count + 1) ∘L
    paddedSelect (p.count + 1) (fun j => (clockLinkData p j.val).1.val)

theorem fixedClockGate_unitary (p : MultiOracleCircuit.Program O) : IsUnitary (fixedClockGate p) :=
  (phasedShift_unitary _).mul
    (paddedSelect_unitary _ _ (fun j => (clockLinkData p j.val).1.property))

/-- Fixed optional label/polarity, with no query on the return slot. -/
def clockChoice (p : MultiOracleCircuit.Program O) : Fin (p.count + 1 + 1) → Option (L × Bool) :=
  Fin.lastCases none (fun j : Fin (p.count + 1) => (clockLinkData p j.val).2)

theorem selected_eq_padded (p : MultiOracleCircuit.Program O) (x : X) :
    WeightedClock.diagonal (fun i => optionalQuery O (clockChoice p i) x) =
      paddedSelect (p.count + 1) (fun j => optionalQuery O (clockLinkData p j.val).2 x) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [clockChoice, paddedSelect, optionalQuery, MultiQueryNormalForm.optionalQuery]
  · simp [clockChoice, paddedSelect]

/-- Concrete factorization needed by native masked-query compilation. -/
theorem programClock_factor (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    programClock p hO hInv x = fixedClockGate p ∘L
      WeightedClock.diagonal (fun i => optionalQuery O (clockChoice p i) x) := by
  rw [programClock, ClockStepQuery.prefix_distributedClock_factor _ _ _ _ _
    (fun v => (prefixGauge_clockLinkEquiv p hO x v).symm)]
  rw [ClockStepQuery.linkSelect_factor (p.count + 1) (clockLinkEquiv p hO x)
    (fun j => (clockLinkData p j.val).1.val)
    (fun j => optionalQuery O (clockLinkData p j.val).2 x)
    (fun j => clockLinkEquiv_factor p hO x j.val)]
  rw [selected_eq_padded]
  exact (comp_assoc _ _ _).symm

/-- Full clock unitarity follows from the counted factorization's actual gates. -/
theorem programClock_unitary (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    IsUnitary (programClock p hO hInv x) := by
  rw [programClock_factor, selected_eq_padded]
  exact (fixedClockGate_unitary p).mul
    (paddedSelect_unitary _ _ (fun j => optionalQuery_unitary O hO _ x))

/-- Isometry in the form used by the analytic weighted-clock bounds. -/
theorem programClock_isometry (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (programClock p hO hInv x)† ∘L programClock p hO hInv x = 1 :=
  (programClock_unitary p hO hInv x).1

/-- Actual clock length, including the terminal fixed link and return edge. -/
def slots (p : MultiOracleCircuit.Program O) : ℕ := p.count + 2

theorem slots_le_twice (p : MultiOracleCircuit.Program O) : slots p ≤ 2 * (p.count + 1) := by
  simp only [slots]
  omega

variable [FiniteDimensional ℂ K]

/-- Actual inverse of one minus the mixed-label program clock. -/
def programResolvent (p : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    ClockOperators.H (p.count + 1) K →L[ℂ] ClockOperators.H (p.count + 1) K :=
  ClockGauge.distributedResolvent (p.eval x).toLinearMap (p.count + 1) (hInv x)
    (fun j => ClockGauge.prefixGauge (clockLinkEquiv p hO x) j.val)

/-- Both resolvent identities, with no supplied inverse oracle. -/
theorem programResolvent_inverse (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (1 - programClock p hO hInv x) ∘L programResolvent p hO hInv x = 1 ∧
      programResolvent p hO hInv x ∘L (1 - programClock p hO hInv x) = 1 :=
  ClockGauge.distributedResolvent_inverse _ _ _ _ _

/-- The norm bound uses the original mixed program's query count plus two. -/
theorem programResolvent_norm_le (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    ‖programResolvent p hO hInv x‖ ≤ (slots p : ℝ) :=
  ClockGauge.distributedResolvent_norm_le (p.eval x).toLinearMap (p.count + 1)
    (hInv x) (program_hermitian p hO hInv x) _

/-- Exact endpoint energy supplies the heterogeneous weighted catalyst budget. -/
theorem programResolvent_endpoint_energy (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) (v : K) :
    ‖(programResolvent p hO hInv x ∘L ClockOperators.boundary (p.count + 1)) v‖ ^ 2 =
      (slots p : ℝ) / 2 * ‖v‖ ^ 2 :=
  ClockGauge.distributedResolvent_endpoint_energy (p.eval x).toLinearMap (p.count + 1)
    (hInv x) (program_hermitian p hO hInv x) _ rfl v

/-- Compression recovers the exact source program as the clock generator. -/
theorem programResolvent_compression (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v) (x : X) :
    (ClockOperators.boundary (p.count + 1))† ∘L programResolvent p hO hInv x ∘L
      ClockOperators.boundary (p.count + 1) =
      (2 : ℂ)⁻¹ • (1 + Complex.I • p.eval x) :=
  ClockGauge.distributedResolvent_compression (p.eval x).toLinearMap (p.count + 1)
    (hInv x) _ rfl

end
end SparseHamiltonian.MultiQueryClock
