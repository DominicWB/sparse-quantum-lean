import GateEfficientHamiltonian.Circuit.GSim

/-!
# Instruction counts

The amplified circuit with `N ≤ 2^r` reuse steps calls the private Cayley
operation exactly `3N` times and `U_J` (or its adjoint) exactly `6N` times.
Its number of elementary gates is at most
`3·(2·2^r(2r+1) + 2L(8r+2) + N(4a+8m+7r+5)) + 2(2(a+m+2r)+2) + 1`.
-/

namespace SparseHamiltonian.GateCircuit.Sim

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators

variable {a m r K : ℕ}

/-! ### Lengths of the network gate lists -/

theorem compL_length (n : ℕ) : (compL (a := a) (m := m) (r := r) (K := K) n).length ≤ 1 := by
  cases n with
  | zero => simp [compL]
  | succ k => simp only [compL]; split_ifs <;> simp

theorem rotL_length (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) :
    (rotL (a := a) (m := m) (r := r) (K := K) R n).length ≤ 1 := by
  simp only [rotL]; split_ifs <;> simp

theorem chainUp_length (n : ℕ) : (chainUp (a := a) (m := m) (r := r) (K := K) n).length ≤ n := by
  induction n with
  | zero => simp [chainUp]
  | succ n ih =>
      rw [chainUp, List.length_append]
      have := compL_length (a := a) (m := m) (r := r) (K := K) (n + 1)
      omega

theorem chainDown_length (n : ℕ) : (chainDown (a := a) (m := m) (r := r) (K := K) n).length ≤ n := by
  induction n with
  | zero => simp [chainDown]
  | succ n ih =>
      rw [chainDown, List.length_append]
      have := compL_length (a := a) (m := m) (r := r) (K := K) (n + 1)
      omega

theorem ascCore_length (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) :
    (ascCore (a := a) (m := m) (r := r) (K := K) R n).length ≤ 2 * n := by
  induction n with
  | zero => simp [ascCore]
  | succ n ih =>
      rw [ascCore, List.length_append, List.length_append]
      have := compL_length (a := a) (m := m) (r := r) (K := K) n
      have := rotL_length (a := a) (m := m) (r := r) (K := K) R n
      omega

theorem descCore_length (R : ℕ → Matrix Bool Bool ℂ) (n : ℕ) :
    (descCore (a := a) (m := m) (r := r) (K := K) R n).length ≤ 2 * n := by
  induction n with
  | zero => simp [descCore]
  | succ n ih =>
      rw [descCore, List.length_append, List.length_append]
      have := compL_length (a := a) (m := m) (r := r) (K := K) n
      have := rotL_length (a := a) (m := m) (r := r) (K := K) R n
      omega

theorem ascFull_length (R : ℕ → Matrix Bool Bool ℂ) :
    (ascFull (a := a) (m := m) (r := r) (K := K) R).length ≤ 3 * m := by
  rw [ascFull, List.length_append]
  have := ascCore_length (a := a) (m := m) (r := r) (K := K) R m
  have := chainDown_length (a := a) (m := m) (r := r) (K := K) (m - 1)
  omega

theorem descFull_length (R : ℕ → Matrix Bool Bool ℂ) :
    (descFull (a := a) (m := m) (r := r) (K := K) R).length ≤ 3 * m := by
  rw [descFull, List.length_append]
  have := descCore_length (a := a) (m := m) (r := r) (K := K) R m
  have := chainUp_length (a := a) (m := m) (r := r) (K := K) (m - 1)
  omega

theorem hfC_length (j : Fin (cap r + 1)) :
    (hfC (a := a) (m := m) (K := K) j).length ≤ 2 * (a + r) + 1 := by
  have := mcGate_length_le (hfLits (a := a) (m := m) (K := K) j) wkList Wire.hf pauliX
  rwa [hfLits_length] at this

theorem cenG_length (zz vv : ℝ) :
    (cenG (a := a) (m := m) (r := r) (K := K) zz vv).length ≤ 2 * m + 3 := by
  have := mcGate_length_le (cenLits (a := a) (m := m) (r := r) (K := K)) wkList Wire.sec
    (rotMat zz vv)
  rw [cenLits_length] at this
  unfold cenG
  omega

theorem netGates_length (j : Fin (cap r + 1)) (c σ : ℝ) :
    (netGates (a := a) (m := m) (K := K) j c σ).length ≤ 4 * a + 4 * r + 8 * m + 5 := by
  simp only [netGates, List.length_append]
  have := hfC_length (a := a) (m := m) (K := K) j
  have := ascFull_length (a := a) (m := m) (r := r) (K := K) (Sim.unMats c)
  have := cenG_length (a := a) (m := m) (r := r) (K := K) (GateDyadicBoundary.centralCosine c m)
    (GateDyadicBoundary.centralSine c σ m)
  have := descFull_length (a := a) (m := m) (r := r) (K := K) (Sim.outMats c)
  omega

/-! ### Oracle and gate counts -/

theorem nPriv_single_priv : nPriv [privI (a := a) (m := m) (r := r) (K := K)] = 1 := rfl
theorem nUJ_single_priv : nUJ [privI (a := a) (m := m) (r := r) (K := K)] = 0 := rfl
theorem nGates_single_priv : nGates [privI (a := a) (m := m) (r := r) (K := K)] = 0 := rfl
theorem nPriv_single_uj (b : Bool) : nPriv [ujI (a := a) (m := m) (r := r) (K := K) b] = 0 := rfl
theorem nUJ_single_uj (b : Bool) : nUJ [ujI (a := a) (m := m) (r := r) (K := K) b] = 1 := rfl
theorem nGates_single_uj (b : Bool) : nGates [ujI (a := a) (m := m) (r := r) (K := K) b] = 0 := rfl

theorem stepI_counts (j : Fin (cap r + 1)) (c σ : ℝ) :
    nPriv (stepI (a := a) (m := m) (K := K) j c σ) = 1 ∧
    nUJ (stepI (a := a) (m := m) (K := K) j c σ) = 2 ∧
    nGates (stepI (a := a) (m := m) (K := K) j c σ) ≤ 4 * a + 8 * m + 7 * r + 5 := by
  have hn := netGates_length (a := a) (m := m) (K := K) j c σ
  have hi := incGates_length (a := a) (m := m) (r := r) (K := K)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [stepI, bnetI, nPriv_append, nUJ_append, nGates_append, nPriv_ofGates, nUJ_ofGates,
      nGates_ofGates, nPriv_single_priv, nUJ_single_priv, nGates_single_priv, nPriv_single_uj,
      nUJ_single_uj, nGates_single_uj]
  omega

theorem selectI_counts (c σ : ℝ) (n : ℕ) (hn : n ≤ cap r + 1) :
    nPriv (selectI (a := a) (m := m) (r := r) (K := K) c σ n) = n ∧
    nUJ (selectI (a := a) (m := m) (r := r) (K := K) c σ n) = 2 * n ∧
    nGates (selectI (a := a) (m := m) (r := r) (K := K) c σ n) ≤ n * (4 * a + 8 * m + 7 * r + 5) := by
  induction n with
  | zero => exact ⟨rfl, rfl, by simp [selectI, nGates]⟩
  | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      rw [selectI, dif_pos (show n < cap r + 1 by omega), nPriv_append, nUJ_append, nGates_append]
      obtain ⟨s1, s2, s3⟩ := stepI_counts (a := a) (m := m) (r := r) (K := K) ⟨n, by omega⟩ c σ
      refine ⟨by omega, by omega, ?_⟩
      rw [Nat.succ_mul]
      omega

variable {L : ℕ}

theorem lcuI_counts (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ)
    (hN : N ≤ cap r + 1) :
    nPriv (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N) = N ∧
    nUJ (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N) = 2 * N ∧
    nGates (lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N) ≤
      2 * (2 ^ r * (2 * r + 1)) + 2 * (L * (8 * r + 2)) + N * (4 * a + 8 * m + 7 * r + 5) := by
  obtain ⟨h1, h2, h3⟩ := selectI_counts (a := a) (m := m) (r := r) (K := K) c σ N hN
  simp only [lcuI, nPriv_append, nUJ_append, nGates_append, nPriv_ofGates, nUJ_ofGates,
    nGates_ofGates, gInv_length]
  have p1 := prepG_length (a := a) (m := m) (r := r) (K := K) (fIn wt)
  have p2 := prepG_length (a := a) (m := m) (r := r) (K := K) (fOut wt)
  have q1 := rangeG_length (a := a) (m := m) (K := K) hL nOf
  refine ⟨by omega, by omega, by omega⟩

theorem ampI_counts (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ)
    (hN : N ≤ cap r + 1) :
    nPriv (ampI (a := a) (m := m) (K := K) hL nOf wt c σ N) = 3 * N ∧
    nUJ (ampI (a := a) (m := m) (K := K) hL nOf wt c σ N) = 6 * N ∧
    nGates (ampI (a := a) (m := m) (K := K) hL nOf wt c σ N) ≤
      3 * (2 * (2 ^ r * (2 * r + 1)) + 2 * (L * (8 * r + 2)) +
        N * (4 * a + 8 * m + 7 * r + 5)) + 2 * (2 * (a + m + 2 * r) + 2) + 1 := by
  obtain ⟨h1, h2, h3⟩ := lcuI_counts (a := a) (m := m) (K := K) hL nOf wt c σ N hN
  simp only [ampI, nPriv_append, nUJ_append, nGates_append, nPriv_ofGates, nUJ_ofGates,
    nGates_ofGates, nPriv_invList, nUJ_invList, nGates_invList]
  have z := zrG_length (a := a) (m := m) (r := r) (K := K)
  simp only [List.length_cons, List.length_nil]
  refine ⟨by omega, by omega, by omega⟩

end

end SparseHamiltonian.GateCircuit.Sim
