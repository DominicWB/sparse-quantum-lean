import ODELowerBoundExtensions.Psd.SearchBound

/-!
# The scalar-family bound of Theorem `odel:thm:psd`

Manuscript: the proof of Theorem `odel:thm:psd`. The scalar family has the same
positive endpoint correlation (`psd_scalar_corr`, heralded: `psd_heralded_corr`). After `q`
Boolean queries any unconditional observable expectation has multilinear degree at most `2q`,
so positive uniform correlation with the full `n`-bit parity requires `2q ≥ n`
(`Hamiltonian.precision_cost_of_corr`, the polynomial method of `hsl:lem:precision`). The
success flag is part of the unconditional observable `Π (e† (M ⊗ 1) e) Π`; the polynomial
method is not applied to a postselected ratio (proof of Theorem `odel:thm:psd`).

* `psd_scalar_cost`: Boolean cost `q ≥ n/2` for any labelled family implementable by bit
  queries;
* `psd_scalar_forces_quarter`: `Q_A ≥ n/4` (`q ≤ 2 Q_A`, proof of Theorem `odel:thm:psd`);
* `psd_scalar_forces`: `Q_A ≥ r/32` (`n ≥ r/8`);
* `psd_scalar_forces_sqrt`: for `s < 512n/τ`, `Q_A > √(sτr)/256` (proof of Theorem `odel:thm:psd`;
  stated with `≥`).

The paper's scalar family is three-sparse and its bound `r/32` needs no condition on `s`. Here it
is stated on the padded family (maximum sparsity exactly `s`) under `PsdRange`, so at `s ≥ 32`:
the construction needs only `3 ≤ s` (`psdScalarData`), and `s ≥ 32` is inherited from
`Hamiltonian.HSRange` through `rbound` and `precN_range`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian SparseLowerBounds.ODE Readout
open scoped InnerProduct InnerProductSpace

set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ} {K K' G L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Scalar-family bound, Boolean-cost form** (proof of Theorem `odel:thm:psd`): any heralded
program over a labelled oracle family implementable with `w l` bit queries, heralded-accurate for
the normalised endpoints of the scalar family, has Boolean cost `p.cost w ≥ n/2`. -/
theorem psd_scalar_cost (h : PsdRange τ s ε) (P : ProjFamily K' (Fin (precN τ ε)))
    (E : K →L[ℂ] K') (hE : E† ∘L E = 1) (O : L → (Fin (precN τ ε) → Bool) → K →L[ℂ] K)
    (hO : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hw : ∀ l, EncodedOracle.ImplementsOn (bitOracle P) (O l) E (w l))
    (p : MultiOracleCircuit.Program O) (φ₀ : K)
    (e : K →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) G) (he : e† ∘L e = 1)
    (herald : K →L[ℂ] K) (hherald : IsStarProjection herald)
    (hsucc : ∀ x, 2 / 3 ≤ ‖herald (p.eval x φ₀)‖ ^ 2)
    (hacc : ∀ x, HeraldedAccurate e herald (p.eval x φ₀)
      (ODEStateNormalization.unitDirection
        (heat (psdScalarMat (precN τ ε) s (τ / 2) x) τ (scalarInput (precN τ ε) s))) ε) :
    (precN τ ε : ℝ) / 2 ≤ p.cost w := by
  have hn1 := h.one_le_precN
  have hτ0 : 0 < τ := by linarith [h.one_le_tau]
  have ha8 := eight_eps_le_psdAmp h
  have hapos := psdAmp_pos hn1 (by linarith : (0 : ℝ) < τ / 2)
  have hobs := psdScalarObs_contraction (precN τ ε) s
  -- Eq. `odel:eq:heraldcorr`: the heralded parity correlation is at least `a/4 > 0`.
  have hpos : ∀ x, 0 < BitDegree.bitParity x *
      (⟪p.eval x φ₀, (herald ∘L outObs e (psdScalarObs (precN τ ε) s) ∘L herald)
        (p.eval x φ₀)⟫_ℂ).re := by
    intro x
    have h1 := psd_heralded_corr h.eps_pos.le ha8 e he herald hherald (p.eval x φ₀) _ (hsucc x)
      (hacc x) _ hobs.1 hobs.2 (BitDegree.abs_bitParity x).le
      (psd_scalar_corr (s := s) hn1 hτ0 x)
    linarith
  exact precision_cost_of_corr P E hE O hO w hw p φ₀ _
    (Finset.sum_pos (fun x _ => hpos x) Finset.univ_nonempty)

/-- **`Q_A ≥ n/4`** (proof of Theorem `odel:thm:psd`): every heralded solver of the scalar family
makes at least `n/4` value queries (and as many matrix queries). -/
theorem psd_scalar_forces_quarter (h : PsdRange τ s ε) :
    (psdScalarFamilyAt h).Forces ε ((precN τ ε : ℝ) / 4) := by
  intro ι _ G _ _ _ A
  exact forces_of_spec_heat (psdScalarDataAt h) τ _ (scalarInput (precN τ ε) s) A
    fun p hsucc hacc => native_bound_of_cost (b := (precN τ ε : ℝ) / 4) p (by
      linarith [psd_scalar_cost h
        (psdScalarSpecBoolean (ι × Fin 1) (precN τ ε) s (τ / 2)) (ancillaEmbed _)
        ancillaEmbed_isometry (specOracles (ι × Fin 1) (psdScalarDataAt h))
        (specOracles_unitary _ _) hardCost
        (implementsOn_psdScalarData_spec (ι × Fin 1) h.one_le_precN
          (by have := h.s_ge; omega))
        p A.seed A.out A.out_isometry A.herald A.herald_proj hsucc hacc])

/-- **`Q_A ≥ r/32`** (proof of Theorem `odel:thm:psd`). -/
theorem psd_scalar_forces (h : PsdRange τ s ε) :
    (psdScalarFamilyAt h).Forces ε (hsR τ ε / 32) := by
  intro ι _ G _ _ _ A
  have hb := psd_scalar_forces_quarter h ι G A
  have ha := rbound h.toHSRange h.hL
  exact ⟨ha.trans hb.1, ha.trans hb.2⟩

/-- **Small sparsity** (proof of Theorem `odel:thm:psd`): for `s < 512n/τ`, every heralded solver of
the scalar family makes at least `√(sτr)/256` value queries (and as many matrix queries). -/
theorem psd_scalar_forces_sqrt (h : PsdRange τ s ε) (hs : (s : ℝ) < 512 * precN τ ε / τ) :
    (psdScalarFamilyAt h).Forces ε (Real.sqrt (s * τ * hsR τ ε) / 256) := by
  intro ι _ G _ _ _ A
  have hb := psd_scalar_forces_quarter h ι G A
  have ha := psd_scalar_sqrt h hs
  exact ⟨ha.trans hb.1, ha.trans hb.2⟩

end

end ODELowerBoundExtensions.Psd
