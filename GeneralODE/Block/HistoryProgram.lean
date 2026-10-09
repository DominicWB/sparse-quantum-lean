import GeneralODE.Block.HistoryEncoding

/-!
# Programs for the history block encoding

A program `qP` over an oracle family `O` on `PB` gives, with the fixed
standard-form gates, a program for each power factor, the power program with
fresh copies of `PB`, and finally the program of the history unitary.  The
history program queries the original labels on the `K` copies, so its query
count is exactly `K` times that of `qP`.  If every oracle of `O` sends one
fixed basis vector to a basis vector, so does every oracle of the history
program; this is the hypothesis of the native control compiler.
-/

namespace SparseHamiltonian.GeneralODE.Registers

noncomputable section
open ContinuousLinearMap OracleCircuit History
open scoped InnerProduct BigOperators ComplexConjugate
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {n PB : Type} [Fintype n] [DecidableEq n] [Fintype PB] [DecidableEq PB]
variable {X L : Type}

section Factor

variable (m K : ℕ)

/-- Lift of an operator on `PB` to a factor workspace. -/
def facHom :
    (EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) →⋆ₐ[ℂ]
      (EuclideanSpace ℂ ((Ctl m K × n) × (Ctl m K × PB)) →L[ℂ]
        EuclideanSpace ℂ ((Ctl m K × n) × (Ctl m K × PB))) :=
  (specHom (Ctl m K × n) (Ctl m K × PB)).comp (specHom (Ctl m K) PB)

/-- Oracle family of one factor. -/
def facOracle (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) :
    L → X → EuclideanSpace ℂ ((Ctl m K × n) × (Ctl m K × PB)) →L[ℂ]
      EuclideanSpace ℂ ((Ctl m K × n) × (Ctl m K × PB)) :=
  fun l x => facHom (n := n) m K (O l x)

variable {m K}

/-- The program of the `i`-th factor. -/
def facProg (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) (i : ℕ) :
    MultiOracleCircuit.Program (facOracle (n := n) m K O) :=
  .seq (.fixed _ (standardLoad_spec (((0 : Fin (K + 1)), (none : Slot m)), i0)
      (((0 : Fin (K + 1)), (none : Slot m)), pb0) (facEnc m K Eout i)
      (facEnc_isometry Eout hout i)).1.adjoint)
    (.seq (MultiOracleCircuit.Program.mapHom (facHom (n := n) m K) id qP)
      (.fixed _ (standardLoad_spec (((0 : Fin (K + 1)), (none : Slot m)), i0)
        (((0 : Fin (K + 1)), (none : Slot m)), pb0) (facEnc m K Ein i)
        (facEnc_isometry Ein hin i)).1))

theorem facProg_eval (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) (i : ℕ) (x : X) :
    (facProg (m := m) (K := K) i0 pb0 Ein Eout hin hout qP i).eval x =
      factor (m := m) (K := K) i0 pb0 Ein Eout hin hout (qP.eval x) i := by
  change star _ * ((MultiOracleCircuit.Program.mapHom (facHom (n := n) m K) id qP).eval x * _) = _
  rw [MultiOracleCircuit.Program.eval_mapHom (facHom (n := n) m K) id (fun l y => rfl) qP x]
  unfold factor standardForm
  rw [mul_assoc]
  rfl

@[simp] theorem facProg_count (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) (i : ℕ) :
    (facProg (m := m) (K := K) i0 pb0 Ein Eout hin hout qP i).count = qP.count := by
  change 0 + ((MultiOracleCircuit.Program.mapHom (facHom (n := n) m K) id qP).count + 0) = _
  rw [MultiOracleCircuit.Program.count_mapHom]
  omega

@[simp] theorem facProg_cost (i0 : n) (pb0 : PB)
    (Ein Eout : Bool → (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ PB))
    (hin : ∀ b, (Ein b)† ∘L Ein b = 1) (hout : ∀ b, (Eout b)† ∘L Eout b = 1)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) (i : ℕ) (w : L → ℕ) :
    (facProg (m := m) (K := K) i0 pb0 Ein Eout hin hout qP i).cost w = qP.cost w := by
  change 0 + ((MultiOracleCircuit.Program.mapHom (facHom (n := n) m K) id qP).cost w + 0) = _
  rw [MultiOracleCircuit.Program.cost_mapHom]
  simp

end Factor

section History

/-- Lift of an operator on the power workspace to the history workspace. -/
def histHom (H : HistData n PB) :
    (EuclideanSpace ℂ ((Ctl H.m H.K × n) × PowAnc PB H.m H.K) →L[ℂ]
        EuclideanSpace ℂ ((Ctl H.m H.K × n) × PowAnc PB H.m H.K)) →⋆ₐ[ℂ]
      (EuclideanSpace ℂ (H.Sys × H.Anc) →L[ℂ] EuclideanSpace ℂ (H.Sys × H.Anc)) :=
  (specHom H.Sys H.Anc).comp (specHom Term ((Ctl H.m H.K × n) × PowAnc PB H.m H.K))

/-- Oracle family of the history program: original labels on the `K` copies. -/
def histOracle (H : HistData n PB) (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB) :
    (Fin H.K × L) → X →
      EuclideanSpace ℂ (H.Sys × H.Anc) →L[ℂ] EuclideanSpace ℂ (H.Sys × H.Anc) :=
  fun il x => histHom H (powOracle (facOracle (n := n) H.m H.K O) H.K il x)

/-- The fixed slot part of the history core. -/
def slotPart (H : HistData n PB) :
    EuclideanSpace ℂ (Term × ((Ctl H.m H.K × n) × PowAnc PB H.m H.K)) →L[ℂ]
      EuclideanSpace ℂ (Term × ((Ctl H.m H.K × n) × PowAnc PB H.m H.K)) :=
  selMap (fun t => actLeft (α := PowAnc PB H.m H.K)
    (liftSlot (n := n) (P := Fin (H.K + 1)) (slotUnitaries H.Rc t)))

theorem slotPart_unitary (H : HistData n PB) : IsUnitary (slotPart H) :=
  selMap_unitary _ (fun t => isUnitary_map _ (isUnitary_map _
    (slotUnitaries_unitary H.Rc H.Rc_unitary t)))

/-- The power program over the factor oracle family. -/
def powProgram (H : HistData n PB) {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) :
    MultiOracleCircuit.Program (powOracle (facOracle (n := n) H.m H.K O) H.K) :=
  powProg (facOracle (n := n) H.m H.K O)
    (facProg (m := H.m) (K := H.K) H.i0 H.pb0 H.Ein H.Eout H.hin H.hout qP) H.K

theorem powProgram_eval (H : HistData n PB)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) (x : X) :
    (powProgram H qP).eval x = H.pow (qP.eval x) := by
  unfold powProgram HistData.pow powCircuit
  rw [powProg_eval]
  congr 1
  funext i
  exact facProg_eval _ _ _ _ _ _ qP i x

/-- The program of the history unitary. -/
def histProgram (H : HistData n PB) {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) : MultiOracleCircuit.Program (histOracle H O) :=
  .seq (.fixed _ (standardLoad_spec ((none : Slot H.m), H.i0) H.clean H.outEnc
      H.outEnc_isometry).1.adjoint)
    (.seq (.fixed _ (isUnitary_map (specHom H.Sys H.Anc) (slotPart_unitary H)))
      (.seq (MultiOracleCircuit.Program.mapHom (histHom H) id (powProgram H qP))
        (.fixed _ (standardLoad_spec ((none : Slot H.m), H.i0) H.clean H.inEnc
          H.inEnc_isometry).1)))

theorem histProgram_eval (H : HistData n PB)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) (x : X) :
    (histProgram H qP).eval x = H.unitary (qP.eval x) := by
  change star _ * (specHom H.Sys H.Anc (slotPart H) *
    ((MultiOracleCircuit.Program.mapHom (histHom H) id (powProgram H qP)).eval x * _)) = _
  rw [MultiOracleCircuit.Program.eval_mapHom (histHom H) id (fun l y => rfl) (powProgram H qP) x,
    powProgram_eval]
  unfold HistData.unitary standardForm histCore histHom
  simp only [StarAlgHom.coe_comp, Function.comp_apply, map_mul, mul_assoc]
  rfl

@[simp] theorem histProgram_count (H : HistData n PB)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) :
    (histProgram H qP).count = H.K * qP.count := by
  change 0 + (0 + ((MultiOracleCircuit.Program.mapHom (histHom H) id (powProgram H qP)).count + 0)) = _
  rw [MultiOracleCircuit.Program.count_mapHom]
  unfold powProgram
  rw [powProg_count]
  simp

/-- Weighted cost for weights depending only on the original label. -/
theorem histProgram_cost (H : HistData n PB)
    {O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB}
    (qP : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (histProgram H qP).cost (fun il => w il.2) = H.K * qP.cost w := by
  change 0 + (0 + ((MultiOracleCircuit.Program.mapHom (histHom H) id (powProgram H qP)).cost
    (fun il => w il.2) + 0)) = _
  rw [MultiOracleCircuit.Program.cost_mapHom]
  unfold powProgram
  rw [show (fun l : Fin H.K × L => w (id l).2) = (fun il => w il.2) from rfl, powProg_cost]
  simp

theorem histOracle_unitary (H : HistData n PB)
    (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (hO : ∀ l x, IsUnitary (O l x)) (il : Fin H.K × L) (x : X) :
    IsUnitary (histOracle H O il x) :=
  isUnitary_map _ (powOracle_unitary _ (fun l y => isUnitary_map _ (hO l y)) H.K il x)

/-- The common basis vector used by the native control compiler; its system
component `sys` is arbitrary because the history oracles never act on it. -/
def HistData.validBasis (H : HistData n PB) (sys : H.Sys) : H.Sys × H.Anc :=
  (sys, (Term.id, ((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0),
    powClean (m := H.m) (K := H.K) H.pb0)))

/-- Basis-image validity transfers from the base oracles to the history oracles. -/
theorem histOracle_valid (H : HistData n PB)
    (O : L → X → EuclideanSpace ℂ PB →L[ℂ] EuclideanSpace ℂ PB)
    (img : L → X → PB)
    (hO : ∀ l x, O l x (EuclideanSpace.single H.pb0 1) = EuclideanSpace.single (img l x) 1)
    (sys : H.Sys) (il : Fin H.K × L) (x : X) :
    ∃ a : H.Sys × H.Anc, histOracle H O il x (EuclideanSpace.single (H.validBasis sys) 1) =
      EuclideanSpace.single a 1 := by
  have hfac : ∀ l y, facOracle (n := n) H.m H.K O l y
      (EuclideanSpace.single (((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0)),
        facClean (m := H.m) (K := H.K) H.pb0) 1) =
      EuclideanSpace.single (((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0)),
        (((0 : Fin (H.K + 1)), (none : Slot H.m)), img l y)) 1 := by
    intro l y
    change specHom (Ctl H.m H.K × n) (Ctl H.m H.K × PB) (specHom (Ctl H.m H.K) PB (O l y))
      (EuclideanSpace.single (((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0)),
        (((0 : Fin (H.K + 1)), (none : Slot H.m)), H.pb0)) 1) = _
    rw [specHom_eq, LookupFromBasisOracle.spectator_single _ _ (((0 : Fin (H.K + 1)), (none : Slot H.m)), img l y) 1]
    rw [specHom_eq]
    exact LookupFromBasisOracle.spectator_single _ _ _ 1 (hO l y) _
  obtain ⟨a', ha'⟩ := powOracle_single (facOracle (n := n) H.m H.K O)
    ((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0))
    (facClean (m := H.m) (K := H.K) H.pb0)
    (fun l y => (((0 : Fin (H.K + 1)), (none : Slot H.m)), img l y)) hfac H.K il x
  refine ⟨(sys, (Term.id, ((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0), a'))), ?_⟩
  unfold histOracle histHom HistData.validBasis
  simp only [StarAlgHom.coe_comp, Function.comp_apply]
  rw [specHom_eq, LookupFromBasisOracle.spectator_single _ _
    (Term.id, ((((0 : Fin (H.K + 1)), (none : Slot H.m)), H.i0), a')) 1]
  rw [specHom_eq]
  exact LookupFromBasisOracle.spectator_single _ _ _ 1 ha' _

end History

end

end SparseHamiltonian.GeneralODE.Registers
