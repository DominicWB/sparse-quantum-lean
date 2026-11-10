import DysonSingleProgram.Explicit.Dyson
import ODELowerBoundExtensions.Dyson.Family.Theorem
import ODELowerBoundExtensions.Release.Strip

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# The Dyson trials on the ODE lower-bound class, with their amplification shape

Manuscript: Lemma `odel:lem:dyson` (on the class of `odel:thm:combined`,
`SparseLowerBounds.ODE.Family`, `Family.InClass η ḡ`, sampled-time access `Family.access ι`).
`ODELowerBoundExtensions.Dyson.family_dyson` gives, for every family of the class, a public trial
family over the lower-bound access (idle source vocabulary) with the released complete
certificate. `family_dyson_grover` gives the same trial family together with its amplification
shape: a preparation program `a` over the class's own access `F.access ι` (idle vocabulary
removed, `Release.stripIdle`) and three fixed unitaries, so that trial `j` evaluates to
`(U₁ a U₂ a† U₃)^j a` and makes `(2j + 1)` times the calls of `a`.

Proof: the proof of `family_dyson` with `Explicit.dyson_grover` and `Explicit.bound_le_dysonBound`
in place of `Dyson.dyson`.
`sourceFree_grover` is the explicit transport of `Dyson.exists_sourceFree`
(`Dyson.sourceFreeProgram` along `Dyson.familyLayout`, `Dyson.certificate_transport`) with the
shape: the transport and `Release.stripIdle` conjugate evaluations by one fixed isometry and keep
matrix counts (`GroverShape.map`).

`family_dyson_of_grover`: the conclusion of `Dyson.family_dyson` follows from
`family_dyson_grover` by forgetting the preparation, the fixed unitaries and the shape; neither
`Dyson.dyson` nor `Dyson.family_dyson` is used.
-/

namespace DysonSingleProgram.Explicit

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open SparseLowerBounds.ODE ODELowerBoundExtensions ODELowerBoundExtensions.Dyson
open scoped InnerProduct BigOperators

/-- **Public sources with the amplification shape**: the explicit transport of
`ODELowerBoundExtensions.Dyson.exists_sourceFree` (`sourceFreeProgram` along `familyLayout`)
maps a Dyson trial family with amplification shape to a trial family over the family's access
(idle source vocabulary) whose preparation runs over `F.access (Spectator …)` itself
(`Release.stripIdle`), with the conjugated fixed unitaries, carrying every released complete
certificate for every nonzero target. -/
theorem sourceFree_grover {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} (F : Family X N Z K s)
    (D : Data (X × Fin K) N Z s) (hD : oracles D = oracles F.data) (K' M : ℕ)
    (J₀' : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (Jb' : Fin M → EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (hJ₀ : IsUnitary J₀')
    (hJb : ∀ r, IsUnitary (Jb' r))
    (q : ℕ → MultiOracleCircuit.Program (oracle D K' M (fun _ => J₀') (fun _ => Jb')))
    (ψ : DysonSpace K N Z K' M) (Fo : EuclideanSpace ℂ N →L[ℂ] DysonSpace K N Z K' M)
    (a : MultiOracleCircuit.Program (oracle D K' M (fun _ => J₀') (fun _ => Jb')))
    (U₁ U₂ U₃ : DysonSpace K N Z K' M →L[ℂ] DysonSpace K N Z K' M)
    (hshape : GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a
      (ODESourceQueryBudget.matrixWeight (fun _ => 1)) U₁ U₂ U₃) :
    ∃ (q' : ℕ → MultiOracleCircuit.Program
        (ODESourceQueryBudget.oracle (F.access (Spectator K N Z K' M)) (fun _ _ => 1)))
      (ψ' : Workspace (Spectator K N Z K' M) N Z K)
      (out : EuclideanSpace ℂ N →L[ℂ] Workspace (Spectator K N Z K' M) N Z K)
      (a' : MultiOracleCircuit.Program (F.access (Spectator K N Z K' M)))
      (U₁' U₂' U₃' : Workspace (Spectator K N Z K' M) N Z K →L[ℂ]
        Workspace (Spectator K N Z K' M) N Z K),
      GroverShape q' (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a' (fun _ => 1)
          U₁' U₂' U₃' ∧
        ∀ (Mi : ℕ) (x : X) (target : EuclideanSpace ℂ N), target ≠ 0 →
          ∀ (s' Θ ell g ε : ℝ), 0 ≤ ε →
            ODECompleteTrial.Certificate q Mi ψ Fo x target s' Θ ell g ε →
              ODECompleteTrial.Certificate q' Mi ψ' out x target s' Θ ell g ε := by
  have hS := knownSource_unitary (Ks := K) (Z := Z) K' M J₀' Jb' hJ₀ hJb
  have hO' : ∀ l y, F.access (Spectator K N Z K' M) l y =
      (familyLayout (Ks := K) (n := N) (Z := Z) K' M).conjStarAlgEquiv
        (oracle D K' M (fun _ => J₀') (fun _ => Jb') (Sum.inl l) y) := fun l y => by
    rw [familyLayout_matrix D K' M (fun _ => J₀') (fun _ => Jb') l y, hD]
  have hOS : ∀ b y, oracle D K' M (fun _ => J₀') (fun _ => Jb') (Sum.inr b) y =
      knownSource K' M J₀' Jb' b := fun b y => oracle_inr D K' M J₀' Jb' b y
  have hEval := fun (p : MultiOracleCircuit.Program
      (oracle D K' M (fun _ => J₀') (fun _ => Jb'))) (y : X) =>
    sourceFreeProgram_eval (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS hO' hOS p y
  have hMat := fun (p : MultiOracleCircuit.Program
      (oracle D K' M (fun _ => J₀') (fun _ => Jb'))) =>
    sourceFreeProgram_matrix_cost (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS p (fun _ => 1)
  have hsrc := fun (p : MultiOracleCircuit.Program
      (oracle D K' M (fun _ => J₀') (fun _ => Jb'))) =>
    sourceFreeProgram_source_cost (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS p
  refine ⟨fun j => sourceFreeProgram (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS (q j),
    familyLayout K' M ψ, (familyLayout K' M).toLinearIsometry.toContinuousLinearMap ∘L Fo,
    _, _, _, _,
    GroverShape.map hshape (familyLayout K' M)
      (fun p => sourceFreeProgram (O' := F.access (Spectator K N Z K' M))
        (familyLayout K' M) (knownSource K' M J₀' Jb') hS p)
      (fun p => Release.stripIdle (sourceFreeProgram (O' := F.access (Spectator K N Z K' M))
        (familyLayout K' M) (knownSource K' M J₀' Jb') hS p))
      (ODESourceQueryBudget.matrixWeight (fun _ => 1)) (fun _ => 1) hEval
      (fun p y => (Release.stripIdle_eval _ y).trans (hEval p y)) hMat
      (fun p => (Release.stripIdle_cost _ _).trans (hMat p)), ?_⟩
  intro Mi x target htarget s' Θ ell g ε hε hc
  exact certificate_transport (P := EuclideanSpace ℂ N) (R := DysonSpace K N Z K' M)
    (R' := Workspace (Spectator K N Z K' M) N Z K) (X := X) (L := Query)
    (O := oracle D K' M (fun _ => J₀') (fun _ => Jb'))
    (O' := ODESourceQueryBudget.oracle (F.access (Spectator K N Z K' M)) (fun _ _ => 1))
    (familyLayout K' M)
    (fun p => sourceFreeProgram (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS p)
    hEval hMat
    (fun p b => ((MultiOracleCircuit.Program.cost_mono _ (sourceWeight_le_total b)).trans
      (hsrc p).le).trans (Nat.zero_le _))
    (fun p => (hsrc p).le.trans (Nat.zero_le _))
    q Mi ψ Fo x target htarget s' Θ ell g ε hε hc


set_option maxHeartbeats 4000000 in
/-- **The Dyson trials on every family of the ODE lower-bound class, with their amplification
shape** (Lemma `odel:lem:dyson`): for a family in the class `InClass η ḡ` with
`η > 0`, `T > 0`, `ḡ ≥ 1` and `0 < ε ≤ 1`, a public trial family `q` over the lower-bound access
(idle source vocabulary), cutoff `M`, seed `ψ`, output `out` and parameters `g'`, `ℓ` with
`1274019840 g' queryShape s 0 ℓ ≤ dysonBound (s η T) ḡ ε` and the released complete certificate
for every instance, whose amplification shape has its preparation over `F.access ι`. -/
theorem family_dyson_grover {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} (F : Family X N Z K s) (η gbar ε : ℝ)
    (hF : F.InClass η gbar) (hη : 0 < η) (hT : 0 < F.T) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι)
      (q : ℕ → MultiOracleCircuit.Program
        (ODESourceQueryBudget.oracle (F.access ι) (fun _ _ => 1)))
      (M : ℕ) (ψ : Workspace ι N Z K)
      (out : EuclideanSpace ℂ N →L[ℂ] Workspace ι N Z K) (g' ell : ℝ)
      (a : MultiOracleCircuit.Program (F.access ι))
      (U₁ U₂ U₃ : Workspace ι N Z K →L[ℂ] Workspace ι N Z K),
      1274019840 * g' * ImprovedODEQueryBudget.queryShape (s : ℝ) 0 ell ≤
          dysonBound ((s : ℝ) * η * F.T) gbar ε ∧
        GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a (fun _ => 1)
          U₁ U₂ U₃ ∧
        ∀ x sol, F.Solves x sol →
          ODECompleteTrial.Certificate q M ψ out x (sol F.T) (s : ℝ) 0 ell g' ε := by
  classical
  have hz : 0 ≤ (s : ℝ) * η * F.T := by positivity
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · -- No input: the certificate clause is vacuous; the identity program has the trivial shape.
    refine ⟨PUnit, inferInstance, fun _ => MultiOracleCircuit.Program.identity, 0, 0, 0, 0, 0,
      MultiOracleCircuit.Program.identity, 1, 1, 1, ?_, ?_, fun x => isEmptyElim x⟩
    · simpa using dysonBound_nonneg hz hg hε hε1
    · exact { unitary₁ := isUnitary_one, unitary₂ := isUnitary_one, unitary₃ := isUnitary_one
              eval_eq := fun j x => by simp
              cost_eq := fun j => by simp }
  -- An input exists: `B > 0`, `K > 0`, `N` is inhabited.
  have hB := mass_pos_of_inClass F hF x₀
  obtain ⟨sol₀, -, hne₀, -⟩ := hF.solution x₀
  obtain ⟨i₀, -⟩ : ∃ i, sol₀ F.T i ≠ 0 := by
    by_contra h
    exact hne₀ (by ext i; simpa using not_exists.mp h i)
  have hK : 0 < K := Nat.pos_of_ne_zero fun h => by
    subst h; simp [SparseLowerBounds.ODE.Family.T_eq_sum] at hT
  obtain ⟨P, hP, hquad⟩ := exists_refinement F hη hg hε hB
  have hDmat := tail_matrix_of_le F.data η hη (entry_le_of_inClass F hF hη)
  -- The Dyson bound, and the Dyson trials with their amplification shape, on the refined mesh
  -- with the public stage map and public sources.
  have hbound := bound_le_dysonBound (NativeBandEncoding.tail F.data η hη)
    (Release.refineFamily F P).start F.T gbar ε
    ‖F.init‖ (fun r => ‖(Release.refineFamily F P).src r‖) (Release.refine_isMesh F P hP) hT
    hg hε hε1 (norm_nonneg _) (fun _ => norm_nonneg _)
    (by rw [Release.refine_meshMass F P hP]; exact hB)
  obtain ⟨q, ψ, Fo, a, U₁, U₂, U₃, hshape, -, hcert⟩ := dyson_grover
    (NativeBandEncoding.tail F.data η hη)
    (Nat.mul_pos hK hP) (Release.stageOf K P) (Release.refineFamily F P).start F.T gbar ε
    ‖F.init‖ (fun r => ‖(Release.refineFamily F P).src r‖) (Release.refine_isMesh F P hP) hT
    hg hε hε1 (norm_nonneg _) (fun _ => norm_nonneg _)
    (by rw [Release.refine_meshMass F P hP]; exact hB)
    (fun _ => Release.prepUnitary i₀ F.init)
    (fun _ r => Release.prepUnitary i₀ ((Release.refineFamily F P).src r))
    (fun _ => Release.prepUnitary_unitary _ _) (fun _ _ => Release.prepUnitary_unitary _ _)
    (Release.seedVec i₀) (Release.norm_seedVec i₀)
  -- The transport to the lower-bound access with public sources.
  obtain ⟨q', ψ', out', a', U₁', U₂', U₃', hshape', htr⟩ := sourceFree_grover F
    (NativeBandEncoding.tail F.data η hη) (NativeBandEncoding.tail_oracles F.data η hη)
    (dysonDegree (NativeBandEncoding.tail F.data η hη) F.T gbar ε) (K * P)
    (Release.prepUnitary i₀ F.init)
    (fun r => Release.prepUnitary i₀ ((Release.refineFamily F P).src r))
    (Release.prepUnitary_unitary _ _) (fun _ => Release.prepUnitary_unitary _ _) q ψ Fo
    a U₁ U₂ U₃ hshape
  refine ⟨Spectator K N Z (dysonDegree (NativeBandEncoding.tail F.data η hη) F.T gbar ε) (K * P),
    inferInstance, q',
    ODEGroverAverage.chosenIterations (ampFactor (NativeBandEncoding.tail F.data η hη)
      (Release.refineFamily F P).start F.T gbar ε ‖F.init‖
      (fun r => ‖(Release.refineFamily F P).src r‖)),
    ψ', out',
    ampFactor (NativeBandEncoding.tail F.data η hη) (Release.refineFamily F P).start F.T gbar ε
      ‖F.init‖ (fun r => ‖(Release.refineFamily F P).src r‖),
    shapeLength (NativeBandEncoding.tail F.data η hη) F.T gbar ε, a', U₁', U₂', U₃', hbound,
    hshape', ?_⟩
  intro x sol hs
  obtain ⟨sol', hsol', hne', hmass'⟩ := hF.solution x
  have hend := F.solves_endpoint_unique hs hsol'
  have hscale : (NativeBandEncoding.tail F.data η hη).scale = η := rfl
  have hc := hcert x (fun r _ => (Release.refineFamily F P).gen x r)
    (fun r _ => (Release.refineFamily F P).src r) sol (fun r => (Release.refineFamily F P).src r)
    (∑ k, ‖F.src k‖) (fun r _ _ => hF.accretive x (Release.stageOf K P r))
    (fun r => by rw [hDmat]; exact hF.accretive x _)
    (fun _ => intervalIntegrable_const) (fun _ => intervalIntegrable_const)
    (fun r _ _ => Finset.single_le_sum (f := fun k => ‖F.src k‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _))
    (fun r => Release.refine_solves F P hs r) (by rw [hs.1]) (fun _ => rfl)
    (fun h => by rw [hs.1] at h ⊢; exact Release.prepUnitary_seed i₀ h)
    (fun r h => Release.prepUnitary_seed i₀ h)
    (by rw [Release.refine_meshMass F P hP, hend]; exact hmass') (by
      beta_reduce
      simp only [Release.refineFamily_gen]
      simp only [hDmat, hscale, Release.refine_meshMass F P hP, Release.refine_quadrature F P,
        SparseLowerBounds.ODE.Family.gen, sub_self, norm_zero, intervalIntegral.integral_zero,
        Finset.sum_const_zero, mul_zero, zero_add]
      exact hquad)
  have hsolT : sol F.T ≠ 0 := by rw [hend]; exact hne'
  exact htr _ x (sol F.T) hsolT _ _ _ _ ε hε.le hc

/-- **The released class form from its explicit form**: the conclusion of
`ODELowerBoundExtensions.Dyson.family_dyson`, obtained from `family_dyson_grover` (whose bound is
`bound_le_dysonBound`; no use of `Dyson.dyson` or `Dyson.family_dyson`) by forgetting the
preparation, the three fixed unitaries and the amplification shape. The trial family of
`family_dyson_grover` is therefore a trial family for `Dyson.family_dyson`. -/
theorem family_dyson_of_grover {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {K s : ℕ} (F : Family X N Z K s) (η gbar ε : ℝ)
    (hF : F.InClass η gbar) (hη : 0 < η) (hT : 0 < F.T) (hg : 1 ≤ gbar) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι)
      (q : ℕ → MultiOracleCircuit.Program
        (ODESourceQueryBudget.oracle (F.access ι) (fun _ _ => 1)))
      (M : ℕ) (ψ : Workspace ι N Z K)
      (out : EuclideanSpace ℂ N →L[ℂ] Workspace ι N Z K) (g' ell : ℝ),
      1274019840 * g' * ImprovedODEQueryBudget.queryShape (s : ℝ) 0 ell ≤
          dysonBound ((s : ℝ) * η * F.T) gbar ε ∧
        ∀ x sol, F.Solves x sol →
          ODECompleteTrial.Certificate q M ψ out x (sol F.T) (s : ℝ) 0 ell g' ε := by
  obtain ⟨ι, hι, q, M, ψ, out, g', ell, _, _, _, _, hb, _, hc⟩ :=
    family_dyson_grover F η gbar ε hF hη hT hg hε hε1
  exact ⟨ι, hι, q, M, ψ, out, g', ell, hb, hc⟩

end

end DysonSingleProgram.Explicit
