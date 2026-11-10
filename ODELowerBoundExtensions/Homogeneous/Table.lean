import ODELowerBoundExtensions.Homogeneous.Defs

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The flag-extended joint index exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Proposition `odel:rem:homogeneous`: the stage tables and the decode

Manuscript: Proposition `odel:rem:homogeneous`, with the encoding of the construction before
Theorem `odel:thm:joint` ("All entries are complex dyadic numbers [...]. A value query computes
one relevant membership bit, writes the known entry and uncomputes the bit. It therefore uses at
most two membership queries"). The words follow `SparseLowerBounds.ODE.jointData`:

* **Words** `Word μ`, one stage-indexed one-bit table `homTable k`
  (`SparseLowerBounds.Hamiltonian.BitTable`): on a hidden stage `k < n` the flag-one block
  carries the joint table `jointTable` (its word at address `((1,i),(1,i'))` depends only on the
  membership bit `(a, k, ·)` that `jointTable` selects); every other word is known
  (`addr = none`): the unit word `2^μ` on the pulse, `Y` and dissipation addresses, `0` elsewhere.
* **Decode** `homPhase (i, i') · valMinAbs z / 2^μ`, with a fixed unit phase per address
  (`-i` on flag-one diagonal addresses, `1` on flag-zero diagonal addresses, `∓1` on the
  flag-flip addresses `((1,c),(0,c))`/`((0,c),(1,c))`, `i` elsewhere). A per-address decode is
  allowed by `NativeSparseBlockEncoding.Data` (the decoder is fixed independently of the input
  and the stage); `homGen_decoded` shows that decoding the stage table recovers the generator
  `homGen` of `ODELowerBoundExtensions.Homogeneous.Defs`.
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian NativeSparseBlockEncoding
open scoped InnerProductSpace

variable {M n μ s : ℕ}

/-! ### Words and decode -/

/-- **The stage-`k` bit table**: the joint table on the flag-one block of a hidden stage; known
unit words `2^μ` on the pulse (`((1,i),(1,i))`), `Y` (`((f,i),(!f,i))`) and dissipation
(`((0,i),(0,i))`) addresses; `0` elsewhere. -/
def homTable (M n μ s : ℕ) (k : Fin (n + 4)) :
    Hamiltonian.BitTable (Fin M × Fin (2 ^ μ)) (HomIndex M μ s × HomIndex M μ s) where
  addr ad :=
    if (k : ℕ) < n ∧ ad.1.1 = true ∧ ad.2.1 = true then (jointTable M μ s).addr (ad.1.2, ad.2.2)
    else none
  word ad bit :=
    if (k : ℕ) < n then
      (if ad.1.1 = true ∧ ad.2.1 = true then (jointTable M μ s).word (ad.1.2, ad.2.2) bit else 0)
    else if (k : ℕ) = n then (if ad.1 = ad.2 ∧ ad.1.1 = true then 2 ^ μ else 0)
    else if (k : ℕ) = n + 1 then (if ad.1.2 = ad.2.2 ∧ ad.1.1 ≠ ad.2.1 then 2 ^ μ else 0)
    else if (k : ℕ) = n + 2 then (if ad.1 = ad.2 ∧ ad.1.1 = false then 2 ^ μ else 0)
    else 0

/-- The membership bits read on stage `k`: those of the hidden stage `k < n`
(`stageBits`), none on the known stages. -/
def homBits (x : Promised M n (2 ^ μ)) (k : Fin (n + 4)) : Fin M × Fin (2 ^ μ) → Bool :=
  if hk : (k : ℕ) < n then stageBits x ⟨k, hk⟩ else fun _ => false

/-- **The fixed unit phase of the decode at an address**: `-i` (flag-one diagonal), `1`
(flag-zero diagonal), `-1` / `1` (flag flips from flag one / zero), `i` elsewhere. -/
def homPhase (ad : HomIndex M μ s × HomIndex M μ s) : ℂ :=
  if ad.1 = ad.2 then (if ad.1.1 = true then -Complex.I else 1)
  else if ad.1.2 = ad.2.2 then (if ad.1.1 = true then -1 else 1)
  else Complex.I

/-- Every decoded word lies in the unit disc (decode scale `1`). -/
theorem homDecode_bound (ad : HomIndex M μ s × HomIndex M μ s) (z : Hamiltonian.Word μ) :
    ‖homPhase ad * Hamiltonian.wordDecode μ z‖ ≤ 1 := by
  have h : ‖homPhase ad‖ = 1 := by unfold homPhase; split_ifs <;> simp
  rw [norm_mul, h, one_mul]
  exact Hamiltonian.norm_wordDecode_le μ z

/-- Every word of every stage table lies in `(-2^μ, 2^μ]`. -/
theorem homTable_word_mem (hμ : 1 ≤ μ) (k : Fin (n + 4))
    (ad : HomIndex M μ s × HomIndex M μ s) (bit : Bool) :
    -(2 : ℤ) ^ μ < (homTable M n μ s k).word ad bit ∧ (homTable M n μ s k).word ad bit ≤ 2 ^ μ := by
  have h2 : (2 : ℤ) ≤ 2 ^ μ := by exact_mod_cast two_le_two_pow hμ
  have hj := jointTable_word_mem (M := M) (s := s) hμ (ad.1.2, ad.2.2) bit
  simp only [homTable]
  split_ifs <;> first | exact hj | (constructor <;> linarith)

/-- On a hidden stage `k < n` the stage table reads the joint table on the flag-one block and
`0` elsewhere. -/
theorem homTable_value_hidden (x : Promised M n (2 ^ μ)) {k : Fin (n + 4)} (hk : (k : ℕ) < n)
    (i i' : HomIndex M μ s) :
    (homTable M n μ s k).value (homBits x k) (i, i') =
      if i.1 = true ∧ i'.1 = true then
        (jointTable M μ s).value (stageBits x ⟨k, hk⟩) (i.2, i'.2)
      else 0 := by
  have hb : homBits x k = stageBits x ⟨k, hk⟩ := dif_pos hk
  rw [hb]
  by_cases hf : i.1 = true ∧ i'.1 = true
  · have ha : (homTable M n μ s k).addr (i, i') = (jointTable M μ s).addr (i.2, i'.2) := by
      simp only [homTable]; rw [if_pos ⟨hk, hf⟩]
    rw [if_pos hf, Hamiltonian.BitTable.value, Hamiltonian.BitTable.value,
      Hamiltonian.BitTable.bit, Hamiltonian.BitTable.bit, ha]
    simp only [homTable]; rw [if_pos hk, if_pos hf]
  · have ha : (homTable M n μ s k).addr (i, i') = none := by
      simp only [homTable]; rw [if_neg (fun h => hf h.2)]
    rw [if_neg hf, Hamiltonian.BitTable.value, Hamiltonian.BitTable.bit_of_addr_none _ _ ha]
    simp only [homTable]; rw [if_pos hk, if_neg hf]

/-- On a known stage `n ≤ k` no address reads a bit: the stage table is its `false` word. -/
theorem homTable_value_known {k : Fin (n + 4)} (hk : ¬ (k : ℕ) < n) (y : Fin M × Fin (2 ^ μ) → Bool)
    (ad : HomIndex M μ s × HomIndex M μ s) :
    (homTable M n μ s k).value y ad = (homTable M n μ s k).word ad false := by
  have ha : (homTable M n μ s k).addr ad = none := by
    simp only [homTable]; rw [if_neg (fun h => hk h.1)]
  rw [Hamiltonian.BitTable.value, Hamiltonian.BitTable.bit_of_addr_none _ _ ha]

/-- The diagonal of the joint stage Hamiltonian vanishes. -/
theorem stageHam_diag (j : Positions M n (2 ^ μ)) (k : Fin n) (c : JointIndex M μ s) :
    stageHam (s := s) j k c c = 0 := by
  by_contra h
  obtain ⟨a, β, b, c', h1, h2⟩ := stageHam_support h
  rw [h1] at h2
  cases β <;> simp at h2

/-- **Decoding the stage table recovers the generator** (`decoded` of `homData`). -/
theorem homGen_decoded (hμ : 1 ≤ μ) (x : Promised M n (2 ^ μ)) (k : Fin (n + 4))
    (i i' : HomIndex M μ s) :
    homPhase (i, i') * Hamiltonian.wordDecode μ
        ((((homTable M n μ s k).value (homBits x k) (i, i') : ℤ)) : Hamiltonian.Word μ) =
      homGen x.1 k i i' := by
  by_cases hk : (k : ℕ) < n
  · rw [homTable_value_hidden x hk]
    have hgen : homGen x.1 k i i' = Complex.I *
        (if i.1 = true ∧ i'.1 = true then stageHam (s := s) x.1 ⟨k, hk⟩ i.2 i'.2 else 0) := by
      simp only [homGen, if_neg (show (k : ℕ) ≠ n + 2 by omega), homHam, dif_pos hk,
        Matrix.smul_apply, smul_eq_mul, flagHam, Matrix.of_apply]
    rw [hgen]
    by_cases hf : i.1 = true ∧ i'.1 = true
    · rw [if_pos hf, if_pos hf, wordDecode_stage hμ]
      by_cases h2 : i.2 = i'.2
      · have hii : i = i' := Prod.ext (hf.1.trans hf.2.symm) h2
        subst hii
        rw [stageHam_diag, mul_zero, mul_zero]
      · have hne : i ≠ i' := fun h => h2 (congrArg Prod.snd h)
        have hp : homPhase (i, i') = Complex.I := by
          simp only [homPhase]; rw [if_neg hne, if_neg h2]
        rw [hp]
    · rw [if_neg hf, if_neg hf]
      simp [Hamiltonian.wordDecode]
  · rw [homTable_value_known hk]
    have hb := homTable_word_mem (M := M) (s := s) hμ k (i, i') false
    rw [Hamiltonian.wordDecode_intCast _ hb.1 hb.2]
    have hpow : (2 : ℂ) ^ μ ≠ 0 := pow_ne_zero _ two_ne_zero
    obtain ⟨f, c⟩ := i
    obtain ⟨f', c'⟩ := i'
    rcases (show (k : ℕ) = n ∨ (k : ℕ) = n + 1 ∨ (k : ℕ) = n + 2 ∨ (k : ℕ) = n + 3 by omega)
      with h | h | h | h
    · simp only [homTable, homGen, homHam, pulseHam, homPhase, h, lt_irrefl, if_false,
        if_true, Matrix.smul_apply, smul_eq_mul,
        show n ≠ n + 2 by omega]
      by_cases hc : c = c' <;> cases f <;> cases f' <;> simp [hc, hpow]
    · simp only [homTable, homGen, homHam, yHam, homPhase, h, show ¬ n + 1 < n by omega,
        show n + 1 ≠ n by omega, show n + 1 ≠ n + 2 by omega, if_false, if_true, dif_neg,
        not_false_eq_true, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
      by_cases hc : c = c' <;> cases f <;> cases f' <;> simp [hc, hpow]
    · simp only [homTable, homGen, homPhase, rejectProj, h, show ¬ n + 2 < n by omega,
        show n + 2 ≠ n by omega, show n + 2 ≠ n + 1 by omega, if_false, if_true,
        Matrix.diagonal_apply]
      by_cases hc : c = c' <;> cases f <;> cases f' <;> simp [hc, hpow]
    · simp only [homTable, homGen, homHam, h, show ¬ n + 3 < n by omega,
        show n + 3 ≠ n by omega, show n + 3 ≠ n + 1 by omega, show n + 3 ≠ n + 2 by omega,
        if_false, dif_neg, not_false_eq_true, Matrix.smul_apply, smul_eq_mul,
        Matrix.zero_apply]
      simp

end

end ODELowerBoundExtensions.Homogeneous
