import ODELowerBoundExtensions.Dyson.Family.Transport
import ODELowerBoundExtensions.Dyson.Family.Mesh

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Public sources: the Dyson certificate on the lower-bound access (`odel:lem:dyson`)

Manuscript: Section `odel:sec:main` (public stage sources of the class of `odel:thm:combined`)
and the consequence of eq. `odel:eq:fixed` (stated for that class).

In the class the initial state and the stage sources are public, so the Dyson solver's two
source interfaces are input-independent unitaries `J₀'`, `Jb'`, whose calls are known gates
(`oracle_inr`). For any native data `D` with the primitives of the family
(`oracles D = oracles F.data`, e.g. the release's tail encoding, `NativeBandEncoding.tail_oracles`)
every Dyson matrix call is the family's access `F.access (Spectator …)` after the fixed layout
`familyLayout` (`familyLayout_matrix`). `exists_sourceFree` packages the program map
`sourceFreeProgram` and `certificate_transport`: one public family of programs over
`ODESourceQueryBudget.oracle (F.access (Spectator …)) (fun _ _ => 1)` (idle source vocabulary),
one seed and one readout carry every released complete certificate of the Dyson programs, with
the same matrix calls and no source calls.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct BigOperators

/-- **Transport to the lower-bound access with public sources**: for native data `D` with the
primitives of the family and input-independent unitary source interfaces, every public family of
Dyson programs, seed and readout has a public counterpart over the family's access (spectator
`Spectator K N Z K' M`, idle source vocabulary) satisfying every released complete certificate of
the original, for every nonzero target. -/
theorem exists_sourceFree {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {K s : ℕ} (F : SparseLowerBounds.ODE.Family X N Z K s)
    (D : Data (X × Fin K) N Z s) (hD : oracles D = oracles F.data) (K' M : ℕ)
    (J₀' : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (Jb' : Fin M → EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) (hJ₀ : IsUnitary J₀')
    (hJb : ∀ r, IsUnitary (Jb' r))
    (q : ℕ → MultiOracleCircuit.Program (oracle D K' M (fun _ => J₀') (fun _ => Jb')))
    (ψ : DysonSpace K N Z K' M) (Fo : EuclideanSpace ℂ N →L[ℂ] DysonSpace K N Z K' M) :
    ∃ (q' : ℕ → MultiOracleCircuit.Program
        (ODESourceQueryBudget.oracle (F.access (Spectator K N Z K' M)) (fun _ _ => 1)))
      (ψ' : SparseLowerBounds.ODE.Workspace (Spectator K N Z K' M) N Z K)
      (out : EuclideanSpace ℂ N →L[ℂ] SparseLowerBounds.ODE.Workspace (Spectator K N Z K' M) N Z K),
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
  refine ⟨fun j => sourceFreeProgram (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS (q j),
    familyLayout K' M ψ, (familyLayout K' M).toLinearIsometry.toContinuousLinearMap ∘L Fo, ?_⟩
  intro Mi x target htarget s' Θ ell g ε hε hc
  have hsrc := fun (p : MultiOracleCircuit.Program (oracle D K' M (fun _ => J₀') (fun _ => Jb'))) =>
    sourceFreeProgram_source_cost (O' := F.access (Spectator K N Z K' M))
    (familyLayout K' M) (knownSource K' M J₀' Jb') hS p
  exact certificate_transport (P := EuclideanSpace ℂ N) (R := DysonSpace K N Z K' M)
    (R' := SparseLowerBounds.ODE.Workspace (Spectator K N Z K' M) N Z K) (X := X) (L := Query)
    (O := oracle D K' M (fun _ => J₀') (fun _ => Jb'))
    (O' := ODESourceQueryBudget.oracle (F.access (Spectator K N Z K' M)) (fun _ _ => 1))
    (familyLayout K' M)
    (fun p => sourceFreeProgram (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS p)
    (fun p y => sourceFreeProgram_eval (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS hO' hOS p y)
    (fun p => sourceFreeProgram_matrix_cost (O' := F.access (Spectator K N Z K' M))
      (familyLayout K' M) (knownSource K' M J₀' Jb') hS p (fun _ => 1))
    (fun p b => ((MultiOracleCircuit.Program.cost_mono _ (sourceWeight_le_total b)).trans
      (hsrc p).le).trans (Nat.zero_le _))
    (fun p => (hsrc p).le.trans (Nat.zero_le _))
    q Mi ψ Fo x target htarget s' Θ ell g ε hε hc

end

end ODELowerBoundExtensions.Dyson
