import SparseODE.ODESourceTransport

/-!
# Counted input and forcing preparation calls

The matrix oracle vocabulary is extended by two supplied source oracles.
The explicit preparation circuit uses each source oracle once, with fixed
routing before and after the source calls. Amplification reverses this whole
preparation circuit: the prepared-state reflection is therefore not free.
The fixed seed and routing are independent of the unknown input.

This section counts the supplied source interfaces, including inverse calls.
Its geometric action is connected to source loading in the companion sections.
-/

namespace SparseHamiltonian.ODESourceQueryBudget

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {P K X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- Matrix calls and the two supplied source interfaces have disjoint labels. -/
def oracle (O : L → X → K →L[ℂ] K) (S : Bool → X → K →L[ℂ] K) :
    L ⊕ Bool → X → K →L[ℂ] K := Sum.elim O S

def matrixWeight (w : L → ℕ) : L ⊕ Bool → ℕ := Sum.elim w (fun _ => 0)

def sourceWeight (b : Bool) : L ⊕ Bool → ℕ :=
  Sum.elim (fun _ => 0) (fun c => if c = b then 1 else 0)

def sourceTotalWeight : L ⊕ Bool → ℕ := Sum.elim (fun _ => 0) (fun _ => 1)

theorem oracle_unitary (S : Bool → X → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x)) :
    ∀ l x, IsUnitary (oracle O S l x) := by
  intro l x
  cases l with
  | inl l => exact hO l x
  | inr b => exact hS b x

/-- Routing conjugates the two source calls; the matrix program follows.
The rightmost source (`true`) executes first. -/
def preparation (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R) :
    MultiOracleCircuit.Program (oracle O S) :=
  .seq (MultiOracleCircuit.Program.relabel (F := oracle O S) Sum.inl p)
    (.seq (.fixed R hR)
      (.seq (.seq (.query (Sum.inr false)) (.query (Sum.inr true)))
        (.fixed (star R) hR.adjoint)))

theorem preparation_eval (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R) (x : X) :
    (preparation p S R hR).eval x =
      p.eval x * R * (S false x * S true x) * star R := by
  simp only [preparation, MultiOracleCircuit.Program.eval_seq,
    MultiOracleCircuit.Program.eval_relabel, MultiOracleCircuit.Program.eval_fixed,
    MultiOracleCircuit.Program.eval_query, oracle, Sum.elim_inr, mul_assoc]
  rfl

/-- A single preparation charges the matrix program plus one call of each
source interface, for any assignment of the individual oracle costs. -/
theorem preparation_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (w : L → ℕ) (v : Bool → ℕ) :
    (preparation p S R hR).cost (Sum.elim w v) = p.cost w + v false + v true := by
  simp [preparation, MultiOracleCircuit.Program.cost_relabel, Nat.add_assoc]
  rfl

theorem preparation_matrix_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (w : L → ℕ) :
    (preparation p S R hR).cost (matrixWeight w) = p.cost w := by
  simpa only [matrixWeight, Nat.add_zero] using
    preparation_cost p S R hR w (fun _ => 0)

theorem preparation_source_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (b : Bool) :
    (preparation p S R hR).cost (sourceWeight b) = 1 := by
  rw [sourceWeight, preparation_cost]
  cases b <;> simp

theorem preparation_source_total_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R) :
    (preparation p S R hR).cost sourceTotalWeight = 2 := by
  rw [sourceTotalWeight, preparation_cost]
  simp

/-- The reflection about the loaded source is implemented by the whole
counted preparation and its adjoint, starting from a fixed seed. -/
def trial (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1) (j : ℕ) :
    MultiOracleCircuit.Program (oracle O S) :=
  ODECountedAmplification.program (preparation p S R hR) F hF ψ hψ j

theorem trial_matrix_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (j : ℕ) (w : L → ℕ) :
    (trial p S R hR F hF ψ hψ j).cost (matrixWeight w) = (2 * j + 1) * p.cost w := by
  rw [trial, ODECountedAmplification.cost_eq, preparation_matrix_cost]

theorem trial_source_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (j : ℕ) (b : Bool) :
    (trial p S R hR F hF ψ hψ j).cost (sourceWeight b) = 2 * j + 1 := by
  rw [trial, ODECountedAmplification.cost_eq, preparation_source_cost, Nat.mul_one]

theorem trial_source_total_cost (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (j : ℕ) :
    (trial p S R hR F hF ψ hψ j).cost sourceTotalWeight = (2 * j + 1) * 2 := by
  rw [trial, ODECountedAmplification.cost_eq, preparation_source_total_cost]

theorem trial_matrix_bound (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (g : ℝ) (hg : 1 ≤ g) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations g) (w : L → ℕ) :
    ((trial p S R hR F hF ψ hψ j).cost (matrixWeight w) : ℝ) ≤
      10 * g * (p.cost w : ℝ) := by
  simpa only [trial, preparation_matrix_cost] using
    ODECountedAmplification.cost_le (preparation p S R hR) F hF ψ hψ
      g hg j hj (matrixWeight w)

theorem trial_source_bound (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (g : ℝ) (hg : 1 ≤ g) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations g) (b : Bool) :
    ((trial p S R hR F hF ψ hψ j).cost (sourceWeight b) : ℝ) ≤ 10 * g := by
  simpa only [trial, preparation_source_cost, Nat.cast_one, mul_one] using
    ODECountedAmplification.cost_le (preparation p S R hR) F hF ψ hψ
      g hg j hj (sourceWeight b)

theorem trial_source_total_bound (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (g : ℝ) (hg : 1 ≤ g) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations g) :
    ((trial p S R hR F hF ψ hψ j).cost sourceTotalWeight : ℝ) ≤ 20 * g := by
  have h := ODECountedAmplification.cost_le (preparation p S R hR) F hF ψ hψ
    g hg j hj sourceTotalWeight
  rw [preparation_source_total_cost] at h
  change ((trial p S R hR F hF ψ hψ j).cost sourceTotalWeight : ℝ) ≤ 10 * g * (2 : ℝ) at h
  nlinarith

/-- The matrix bound remains separate from the source-interface budget. -/
theorem selected_matrix_bound (p : MultiOracleCircuit.Program O)
    (S : Bool → X → K →L[ℂ] K) (R : K →L[ℂ] K) (hR : IsUnitary R)
    (F : P →L[ℂ] K) (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (s Θ ell g : ℝ) (hg : 1 ≤ g) (j : ℕ)
    (hj : j < ODEGroverAverage.chosenIterations g)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :
    ((trial p S R hR F hF ψ hψ j).cost (matrixWeight (fun _ => 1)) : ℝ) ≤
      106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by
  have hg0 : 0 ≤ g := by linarith
  have hCount :
      ((trial p S R hR F hF ψ hψ j).cost (matrixWeight (fun _ => 1)) : ℝ) ≤
        10 * g * (p.count : ℝ) := by
    simpa using trial_matrix_bound p S R hR F hF ψ hψ g hg j hj (fun _ => 1)
  calc
    _ ≤ 10 * g * (p.count : ℝ) := hCount
    _ ≤ 10 * g * (10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) hg0)
    _ = _ := by ring

end
end SparseHamiltonian.ODESourceQueryBudget
