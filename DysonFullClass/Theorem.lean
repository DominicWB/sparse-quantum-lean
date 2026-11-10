import DysonFullClass.Target
import DysonFullClass.Herald
import GeneralSourceODE.Native
import ODELowerBoundExtensions.Dyson.Trials
import DysonSingleProgram.Explicit.Compile

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Lemma `odel:lem:dyson` on the full time-dependent input class

Manuscript, Lemma `odel:lem:dyson`: "Assume the coherent time queries, attainable sample
accuracy and source access of Theorem `ode:thm:time`, including coherent matrix access on every
finite mesh selected from the public error certificate. Assume a supplied common row and column
Euclidean-norm bound `η` for `A(t)`. Put `z := s η T = s τ > 0` and `L_g = log(C ḡ/ε)`. There is a
generic sparse-oracle solver with `Q_A = O(ḡ e^z [1 + z + L_g/log(e + L_g/z)])` (eq.
`odel:eq:dyson`). Only matrix queries are counted."

**Public specification** (fixed before the unknown input `x : X`): the time-indexed native access
`D₀ : Data (X × Fin Kₛ) n Z s` (row, column and value oracles of every sample, the public decoder),
a mesh `t` of `[0, T]` with `M` cells and a cell-to-sample map `σ`, the entry bound `η > 0`,
`ḡ ≥ 1`, `c_q ≥ 1`, `0 < ε ≤ 1`, the source rule (nodes `v_i ∈ [0, T]`, complex weights `ω_i`),
the supplied unitary source preparations `P_w` and `U_load` (functions of the unknown input) and a
unit seed. **Unknown**: the input `x`, and through it the true pieces `G_r`, forcing `b_r`,
solution, forcing samples `b(v_i)`, propagator, source norms and source certificate `ζ`.

**Valid instances** (`FullValid`): the input class of `ManuscriptConformance.ode_thm_time`
(accretive true pieces, integrable, with mesh propagator classical on every closed cell; mild
solution; the weight preparation of the actual source vectors `x₀`, `ω_i b(v_i)`; label-controlled
loading of their directions; `B_q ≤ c_q B`; the propagated source certificate `ζ B`; `x(T) ≠ 0`;
`B ≤ ḡ ‖x(T)‖`), with the Dyson certificate `ζ + c_q (e^{E} - 1) ≤ ε/(2000 ḡ)` on the represented
generator `C_r = p_η(D₀.matrix (x, σ r))` (the radially clipped samples, `Clip.lean`; no clipping
happens if the represented entries are already capped by `η`). No positivity of the represented
samples, no public source norms, no `B ≤ B_q`, no on-mesh source nodes are assumed. Certificates
on the branches `K_{±k} = H ± kD` of two opposite frequencies are covered through the branch
bound `ManuscriptConformance.sampleErr_le_branchSum`
(`ManuscriptConformance.fullValidAt_of_branch_raw`, `fullValidAt_of_branch_clipped`).

**Algorithm** (one public trial family, seed and output for all valid instances): `P_w`, then
`U_load` and the public phases `ω_i/|ω_i|`, then the matrix program `fProgram` (the public
attenuation rotation `attGate` of the source-label-dependent factor, then the Dyson SELECT
`gSelect` of degree `K = truncDegree z (c_q ḡ) ε`, each slot the six-query block encoding of the
clipped decoder on the original access, `18 K` native calls in total), then `P_w†` on the label
only; randomised amplification of this actual preparation with its actual inverse about the public
seed and output flag, at the public parameter `g' = c_q ḡ e^z`, compiled by the released
three-query control compiler, and the four-trial wrapper.

* `fProgram_compression`, `fProgram_count`; `fDecoded`: the decoded vector of the actual
  preparation is `(2 e^z B_q)⁻¹ y_K` (`Target.dysonTarget`), exactly;
* `FullValidAt` (exact preparations `P`, `L`), `FullValid` (the supplied `P_w(x)`, `U_load(x)`);
* `full_dyson_shape`, `full_dyson`: the released complete certificate
  `ODECompleteTrial.Certificate` (success at least
  `2/3`, conditional trace distance at most `ε` after discarding the work registers, worst-case
  matrix queries `1274019840 g' queryShape s 0 (K/589824) = 2160 g' K`, at most `40 g'` calls of
  each counted source interface) for every valid instance, with the amplification shape of one
  public preparation (`DysonSingleProgram.GroverShape`);
* `full_bound`: `2160 g' K ≤ dysonBound z (c_q ḡ) ε = 16000 c_q ḡ e^z (1 + z + L/log(e + L/z))`,
  `L = log(4000 c_q ḡ/ε)` (eq. `odel:eq:dyson`, with `c_q` an absolute model constant).
-/

namespace DysonFullClass

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open MeasureTheory TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale meshScale_nonneg IsMeshPropagator
  endMap endMap_apply)
open SparseHamiltonian.GeneralSourceODE (sources phases phases_norm startTime mass_sources
  phased_prepares phased_isometry)
open SparseHamiltonian.GeneralSourceODE.Compiled (WeightPrep seedCoefficients phased
  publicLogicalTrials sourceFamily)
open ODELowerBoundExtensions.Dyson
open scoped InnerProduct BigOperators ODELowerBoundExtensions.Dyson

/-! ### Public parameters -/

/-- The LCU part of a branch label: Dyson label and attenuation flag. -/
abbrev FIota (K M : ℕ) : Type := LabelI K M × Bool

/-- The branch labels: source label, Dyson label, attenuation flag. -/
abbrev FLab (K M m : ℕ) : Type := Option (Fin m) × FIota K M

/-- The map of a branch label to its Dyson label. -/
def fKappa {K M m : ℕ} : FLab K M m → LabelI K M := fun l => l.2.1

/-- `z = s η T`. -/
def zParam (s : ℕ) (η T : ℝ) : ℝ := (s : ℝ) * η * T

/-- **The public degree** `K = truncDegree z (c_q ḡ) ε` (eq. `odel:eq:degree`). -/
def fullDegree (s : ℕ) (η T g cq ε : ℝ) : ℕ := truncDegree (zParam s η T) (cq * g) ε

/-- **The public amplification parameter** `g' = c_q ḡ e^z`. -/
def fullAmp (s : ℕ) (η T g cq : ℝ) : ℝ := cq * g * Real.exp (zParam s η T)

/-- The shape parameter `ℓ = K/589824` of the released certificate at `Θ = 0`. -/
def fullShape (K : ℕ) : ℝ := (K : ℝ) / 589824

theorem zParam_pos {s : ℕ} (hs : 0 < s) {η T : ℝ} (hη : 0 < η) (hT : 0 < T) :
    0 < zParam s η T := by
  unfold zParam
  have : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  positivity

theorem one_le_fullAmp {s : ℕ} {η T g cq : ℝ} (hη : 0 ≤ η) (hT : 0 ≤ T) (hg : 1 ≤ g)
    (hcq : 1 ≤ cq) : 1 ≤ fullAmp s η T g cq := by
  unfold fullAmp
  have hz : 0 ≤ zParam s η T := by unfold zParam; positivity
  have h1 : 1 ≤ Real.exp (zParam s η T) := Real.one_le_exp hz
  have h2 : 1 ≤ cq * g := by nlinarith
  nlinarith

/-! ### The program -/

variable {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s Ks M m : ℕ}

/-- The common LCU table of a (clipped) input, with the attenuation flag: normalisation
`N_D = 2 e^{s Λ T}`. -/
def fTable (D : Data (X × Fin Ks) n Z s) (t : ℕ → ℝ) (T : ℝ) (K M : ℕ) : FIota K M → ℂ :=
  attTable (dysonTable ((s : ℝ) * D.scale) t K M (2 * Real.exp ((s : ℝ) * D.scale * T)))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem fTable_mass {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T) (D : Data (X × Fin Ks) n Z s)
    (K : ℕ) :
    ODECoherentLCU.coefficientMass (fTable D t T K M) = 2 * Real.exp ((s : ℝ) * D.scale * T) := by
  have hα : 0 ≤ (s : ℝ) * D.scale := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  unfold fTable
  rw [attTable_mass]
  refine dysonTable_mass hmesh hα ((cellMass_le hmesh hα).trans ?_)
  linarith [Real.exp_pos ((s : ℝ) * D.scale * T)]

/-- **The matrix program of the Dyson preparation**: the public attenuation rotation (lifted
through the SELECT encoding, a fixed gate), then the Dyson SELECT on the branch labels
`FLab K M m`. -/
def fProgram (hM : 0 < M) (hKs : 0 < Ks) (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s)
    (K : ℕ) (t : ℕ → ℝ) (v : Fin m → ℝ) :
    MultiOracleCircuit.Program (matrixOracle (OmegaG (FLab K M m) K) D) :=
  .seq (gSelect hM hKs σ D K (fKappa (K := K) (M := M) (m := m)))
    (.fixed (SubspaceOracle.lift (gEncoding hKs D K (FLab K M m))
        (attGate (P := EuclideanSpace ℂ n) (dysonAngle t v)))
      (SubspaceOracle.lift_unitary _ (gEncoding_isometry hKs D K) _ (attGate_unitary _)))

/-- `18 K` native matrix calls per preparation, independent of the mesh, of the number and
placement of the source nodes and of the configurations. -/
theorem fProgram_count (hM : 0 < M) (hKs : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (t : ℕ → ℝ) (v : Fin m → ℝ) :
    (fProgram hM hKs σ D K t v).count = 18 * K := by
  simp only [fProgram, MultiOracleCircuit.Program.count_seq,
    MultiOracleCircuit.Program.count_fixed, gSelect_count, add_zero]

/-- **The compression of the matrix program**: the branch-diagonal selected products after the
attenuation rotation. -/
theorem fProgram_compression (hM : 0 < M) (hKs : 0 < Ks) (σ : Fin M → Fin Ks)
    (D : Data (X × Fin Ks) n Z s) (K : ℕ) (t : ℕ → ℝ) (v : Fin m → ℝ) (x : X) :
    (gEncoding hKs D K (FLab K M m))† ∘L (fProgram hM hKs σ D K t v).eval x ∘L
        gEncoding hKs D K (FLab K M m) =
      WeightedClock.diagonal (gBranchOperator σ D x (fKappa (K := K) (M := M) (m := m))) ∘L
        attGate (P := EuclideanSpace ℂ n) (dysonAngle t v) := by
  have hS := gSelect_compression hM hKs σ D K (fKappa (K := K) (M := M) (m := m)) x
  have hL := lift_comp_self (gEncoding hKs D K (FLab K M m)) (gEncoding_isometry hKs D K)
    (attGate (P := EuclideanSpace ℂ n) (dysonAngle t v))
  rw [← hS]
  simp only [fProgram, MultiOracleCircuit.Program.eval_seq, MultiOracleCircuit.Program.eval_fixed,
    mul_def, comp_assoc, hL]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem gBranchOperator_false (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (x : X)
    {K : ℕ} (a : Option (Fin m)) (l : LabelI K M) :
    gBranchOperator σ D x (fKappa (K := K) (M := M) (m := m)) (a, (l, false)) =
      labelOperator (sampleSeq σ D x) l := by
  cases l <;> rfl

set_option maxHeartbeats 2000000 in
/-- **The decoded vector of the actual Dyson preparation** (proof of Lemma `odel:lem:dyson`): with the actual
source vectors `z` (`P_w` preparing their square-root probabilities, the phased loading their
directions), the selected vector is exactly `(2 e^{s Λ T} B_q)⁻¹ ∑_a nodeSeries(startTime v a) z_a`,
one normalisation for all labels, independent of the hidden source norms. -/
theorem fDecoded {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T) (hM : 0 < M) (hKs : 0 < Ks)
    (σ : Fin M → Fin Ks) (D : Data (X × Fin Ks) n Z s) (K : ℕ) (v : Fin m → ℝ)
    (ω : Fin m → ℂ) (x : X) (Jx : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (z : Option (Fin m) → EuclideanSpace ℂ n) (hz : 0 < ODESourceBranches.mass z)
    (seed : EuclideanSpace ℂ n)
    (hprep : ∀ a, z a ≠ 0 →
      phased Jx (phases ω) a seed = ODEStateNormalization.unitDirection (z a)) :
    ODEActualSourceError.decoded (gEncoding hKs D K (FLab K M m)) z (fTable D t T K M)
        (phased Jx (phases ω)) ((fProgram hM hKs σ D K t v).eval x) seed =
      (((2 * Real.exp ((s : ℝ) * D.scale * T)) * ODESourceBranches.mass z : ℝ) : ℂ)⁻¹ •
        ∑ a, nodeSeries (cellGen σ D x) t K M (startTime v a) (z a) := by
  have hα : 0 ≤ (s : ℝ) * D.scale := mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le
  have hcm : cellMass ((s : ℝ) * D.scale) t K M ≤ 2 * Real.exp ((s : ℝ) * D.scale * T) :=
    (cellMass_le hmesh hα).trans (by linarith [Real.exp_pos ((s : ℝ) * D.scale * T)])
  have hmass := dysonTable_mass hmesh hα hcm
  have hdec := decoded_atten (gEncoding hKs D K (FLab K M m)) ((fProgram hM hKs σ D K t v).eval x)
    (ODESourceBranches.probability z) (ODESourceBranches.probability_nonneg z)
    (ODESourceBranches.sum_probability z hz)
    (dysonTable ((s : ℝ) * D.scale) t K M (2 * Real.exp ((s : ℝ) * D.scale * T)))
    (dysonAngle t v) (gBranchOperator σ D x (fKappa (K := K) (M := M) (m := m)))
    (fProgram_compression hM hKs σ D K t v x) (fun b => phased Jx (phases ω) b.1) seed
  change ODEJointSourceLCU.decoded _ (ODESourceCoefficients.productCoeff
    (ODESourceBranches.probability z) (fTable D t T K M)) (fun b => phased Jx (phases ω) b.1) _
      seed = _
  unfold fTable
  rw [hdec, hmass]
  have hinner : ∀ a : Option (Fin m),
      ∑ l : LabelI K M, (((ODESourceBranches.probability z a *
          Real.cos (dysonAngle t v (a, l)) : ℝ) : ℂ) *
          dysonTable ((s : ℝ) * D.scale) t K M (2 * Real.exp ((s : ℝ) * D.scale * T)) l) •
        gBranchOperator σ D x (fKappa (K := K) (M := M) (m := m)) (a, (l, false))
          (phased Jx (phases ω) a seed) =
      (ODESourceBranches.probability z a : ℂ) •
        nodeSeries (cellGen σ D x) t K M (startTime v a) (phased Jx (phases ω) a seed) := by
    intro a
    rw [← table_sum_eq hmesh (cellGen σ D x) (sampleSeq σ D x) ((s : ℝ) * D.scale)
      (cellGen_eq_smul σ D x) (2 * Real.exp ((s : ℝ) * D.scale * T)) v a]
    rw [sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [gBranchOperator_false, smul_apply, smul_smul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  rw [← ODESourceBranches.rescaled_preparedSum z
    (fun a => nodeSeries (cellGen σ D x) t K M (startTime v a)) (phased Jx (phases ω)) seed hz
    hprep, smul_smul]
  congr 1
  have hm0 : (ODESourceBranches.mass z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hN0 : ((2 * Real.exp ((s : ℝ) * D.scale * T) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.exp ((s : ℝ) * D.scale * T)).ne'
  push_cast at hN0 ⊢
  field_simp

/-! ### The access and the valid instances -/

/-- **The access of the full-class Dyson solver**: masked coherent sampled-time native calls of
`D₀` (labels `inl`, row, column and value oracles with their spectators) and the two counted
interfaces of the supplied source access (labels `inr`: `false` the preparation `P_w`, `U_load` and
the public phases; `true` the label unpreparation `P_w†`). -/
abbrev fullOracle (D : Data (X × Fin Ks) n Z s) (K M m : ℕ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (ω : Fin m → ℂ) :=
  ODECoordinateNativeControl.physicalOracle
    (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
    (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))
    (matrixOracle (OmegaG (FLab K M m) K) D)
    (sourceFamily (ι := FIota K M) Pw J (phases ω))

/-- The physical workspace of the full-class solver. -/
abbrev FSpace (Ks : ℕ) (n Z : Type) [Fintype n] [Fintype Z] (K M m : ℕ) : Type :=
  ODESectorTensor.Physical (GeneralSourceODE.Native.SourceBasis (FIota K M) n m)
    (OmegaG (FLab K M m) K × NativeControlledOracle.Workspace (PBasis Ks n Z))

/-- **The valid instances of the full time-dependent class for exact preparations `P`, `L`**:
`y = x(T)` for an instance of the input class of Theorem `ode:thm:time` on input `x` (accretive
integrable true pieces with mesh propagator classical on the closed cells, mild solution, the
weight preparation `P` of the actual source vectors, loading `L` of their directions, `B_q ≤ c_q B`, the propagated source
certificate `ζ B`, `x(T) ≠ 0`, `B ≤ ḡ ‖x(T)‖`), with the Dyson certificate
`ζ + c_q (e^{E} - 1) ≤ ε/(2000 ḡ)` on the clipped represented samples `p_η(D₀.matrix (x, σ r))`. -/
def FullValidAt (D₀ : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T η g cq ε : ℝ) (hη : 0 < η) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X) (y : EuclideanSpace ℂ n) : Prop :=
  ∃ (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (bv : Fin m → EuclideanSpace ℂ n) (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n)
    (ζ : ℝ),
    (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) ∧
    RepresentedSampleODE.RegularPieces t G ∧
    RepresentedSampleODE.MildSolution t T b sol U ∧
    IsMeshPropagator G t T U ∧
    WeightPrep P (sources (sol 0) bv ω) ∧
    (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) ∧
    (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed = ODEStateNormalization.unitDirection (bv i)) ∧
    ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t ∧
    ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * meshScale sol b t ∧
    sol T ≠ 0 ∧
    meshScale sol b t ≤ g * ‖sol T‖ ∧
    ζ + cq * (Real.exp (cellError σ (clipData D₀ η hη) x t G) - 1) ≤ ε / (2000 * g) ∧
    sol T = y

/-- **The valid instances for the supplied source access**: `FullValidAt` with the supplied
weight preparation `P_w(x)` and loaders `U_load(x)`. -/
def FullValid (D₀ : Data (X × Fin Ks) n Z s) {M : ℕ} (σ : Fin M → Fin Ks) (t : ℕ → ℝ)
    (T η g cq ε : ℝ) (hη : 0 < η) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (x : X) (y : EuclideanSpace ℂ n) : Prop :=
  FullValidAt D₀ σ t T η g cq ε hη v ω (Pw x) (J x) seed x y

/-! ### The theorem -/

omit [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The source scale is positive on a valid instance: `B = 0` would force `B_q = 0` and
`x(T) = 0`. -/
theorem meshScale_pos_of_valid {t : ℕ → ℝ} {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (hU : IsMeshPropagator G t T U)
    (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
    (hmild : RepresentedSampleODE.MildSolution t T b sol U) (hT : 0 ≤ T)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (bv : Fin m → EuclideanSpace ℂ n) (ω : Fin m → ℂ)
    (cq ζ : ℝ)
    (hmass : ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t)
    (hsrc : ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
        ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t)
    (hsol : sol T ≠ 0) : 0 < meshScale sol b t := by
  rcases (meshScale_nonneg hmesh sol b).eq_or_lt with h0 | hpos
  · exfalso
    rw [← h0, mul_zero] at hmass hsrc
    have hz : ∀ a, sources (sol 0) bv ω a = 0 := by
      intro a
      have h := ODESourceBranches.mass_nonneg (sources (sol 0) bv ω)
      have hsum : ∑ a, ‖sources (sol 0) bv ω a‖ = 0 := le_antisymm hmass h
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => norm_nonneg _)).mp hsum a
        (Finset.mem_univ a)
      exact norm_eq_zero.mp this
    have h00 : sol 0 = 0 := hz none
    have hbv : ∀ i, ω i • bv i = 0 := fun i => hz (some i)
    have hzero : ∀ i, ω i • U (v i) (bv i) T = 0 := by
      intro i
      have h := (endMap hmesh hU hG (hv i)).map_smul (ω i) (bv i)
      simp only [endMap_apply] at h
      rw [← h, hbv i]
      exact hU.map_zero hmesh hG (hv i) T ⟨(hv i).2, le_rfl⟩
    have hU0 : U 0 (sol 0) T = 0 := by
      rw [h00]; exact hU.map_zero hmesh hG ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩
    have hsrc0 : (∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) = 0 := by
      have h := norm_le_zero_iff.mp hsrc
      rw [Finset.sum_eq_zero fun i _ => hzero i, sub_zero] at h
      exact h
    apply hsol
    rw [hmild.2, hU0, hsrc0, add_zero]
  · exact hpos

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
/-- **Lemma `odel:lem:dyson` on the full time-dependent class** (eq. `odel:eq:dyson`): for every
public specification there are one public trial family, unit seed and isometric output over
`fullOracle D₀` (native calls of the original access, the supplied source interfaces) such that
every valid instance of `FullValid` carries the released complete certificate with cutoff
`chosenIterations g'`, `g' = fullAmp s η T ḡ c_q = c_q ḡ e^z`, shape `ℓ = K/589824`
(`K = fullDegree`, `18 K` native calls per preparation) and accuracy `ε`. The trials are the
compiled amplification of one public preparation `a` (the compiled source/matrix preparation) with
public fixed reflections `U₁ U₂ U₃` (`DysonSingleProgram.GroverShape` for the matrix weight and for
both source interfaces). -/
theorem full_dyson_shape (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ (q : ℕ → MultiOracleCircuit.Program
        (fullOracle D₀ (fullDegree s η T g cq ε) M m Pw J ω))
      (ψ : FSpace Ks n Z (fullDegree s η T g cq ε) M m)
      (F : EuclideanSpace ℂ n →L[ℂ] FSpace Ks n Z (fullDegree s η T g cq ε) M m)
      (a : MultiOracleCircuit.Program (fullOracle D₀ (fullDegree s η T g cq ε) M m Pw J ω))
      (U₁ U₂ U₃ : FSpace Ks n Z (fullDegree s η T g cq ε) M m →L[ℂ]
        FSpace Ks n Z (fullDegree s η T g cq ε) M m),
      DysonSingleProgram.GroverShape q (ODESourceQueryBudget.matrixWeight (fun _ => 1)) a
        (ODESourceQueryBudget.matrixWeight (fun _ => 1)) U₁ U₂ U₃ ∧
      (∀ b, DysonSingleProgram.GroverShape q (ODESourceQueryBudget.sourceWeight b) a
        (ODESourceQueryBudget.sourceWeight b) U₁ U₂ U₃) ∧
      ‖ψ‖ = 1 ∧ F† ∘L F = 1 ∧
      (∀ j x, IsUnitary ((q j).eval x)) ∧
      ∀ x y, FullValid D₀ σ t T η g cq ε hη v ω Pw J seed x y →
        ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (fullAmp s η T g cq)) ψ F x y
          (s : ℝ) 0 (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε := by
  classical
  obtain ⟨i₀⟩ : Nonempty n := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have h0 : seed = 0 := by
      ext i
      exact isEmptyElim i
    rw [h0, norm_zero] at hSeed
    exact zero_ne_one hSeed
  have hKs : 0 < Ks := Fin.pos (σ ⟨0, hM⟩)
  set D := clipData D₀ η hη with hDdef
  set K := fullDegree s η T g cq ε with hKdef
  set g' := fullAmp s η T g cq with hg'def
  have hs : 0 < s := D₀.slots_pos
  have hz : 0 < zParam s η T := zParam_pos hs hη hT
  have hDscale : D.scale = η := rfl
  have hzD : (s : ℝ) * D.scale * T = zParam s η T := by rw [hDscale]; rfl
  have hg1 : 1 ≤ g' := one_le_fullAmp hη.le hT.le hg hcq
  have hcqg : 1 ≤ cq * g := by nlinarith
  set p : MultiOracleCircuit.Program (matrixOracle (OmegaG (FLab K M m) K) D₀) :=
    fProgram hM hKs σ D K t v with hpdef
  set E := gEncoding hKs D K (FLab K M m) with hEdef
  have hE : E† ∘L E = 1 := gEncoding_isometry hKs D K
  set c := fTable D t T K M with hcdef
  have hcmass : ODECoherentLCU.coefficientMass c = 2 * Real.exp (zParam s η T) := by
    rw [hcdef, fTable_mass hmesh D K, hzD]
  have hc : 0 < ODECoherentLCU.coefficientMass c := by rw [hcmass]; positivity
  have hpos : 0 < ODECoherentLCU.coefficientMass (seedCoefficients (N := m) c) := by
    rw [GeneralSourceODE.Compiled.seedCoefficients_mass]; exact hc
  have hSeedU := ODECompiledSource.seed_unit E (seedCoefficients c) hE hpos seed hSeed
  have hOut := ODECompiledSource.output_isometry E (seedCoefficients c) hE hpos
  have hO : ∀ l x, IsUnitary (matrixOracle (OmegaG (FLab K M m) K) D₀ l x) :=
    matrixOracle_unitary (OmegaG (FLab K M m) K) D₀
  let ω₀ : OmegaG (FLab K M m) K := ((none, (Sum.inr false, false)), fun _ => false)
  let a0 : GeneralSourceODE.Native.SourceBasis (FIota K M) n m := ((none, (Sum.inr false, false)), i₀)
  refine ⟨fun j => ODECoordinateNativeControl.compile
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))
      (matrixOracle (OmegaG (FLab K M m) K) D₀)
      (sourceFamily (ι := FIota K M) Pw J (phases ω)) a0 (matrixClean hKs D₀ ω₀)
      (publicLogicalTrials p Pw J (phases ω) E hE c seed hSeedU hOut j),
    ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀) (ODECompiledSource.seed E (seedCoefficients c) seed),
    ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀) ∘L ODECompiledSource.output E (seedCoefficients c),
    ODECoordinateNativeControl.compile
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))
      (matrixOracle (OmegaG (FLab K M m) K) D₀)
      (sourceFamily (ι := FIota K M) Pw J (phases ω)) a0 (matrixClean hKs D₀ ω₀)
      (GeneralSourceODE.Compiled.program p (sourceFamily (ι := FIota K M) Pw J (phases ω)) E hE),
    SubspaceOracle.lift (ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀)) (-1),
    SubspaceOracle.lift (ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀))
      (PhaseSubspaceGates.phase (ODEGroverRay.projector
        (ODECompiledSource.seed E (seedCoefficients c) seed)) (-1)),
    SubspaceOracle.lift (ODECoordinateNativeControl.input
      (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
      (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
      (matrixClean hKs D₀ ω₀))
      (PhaseSubspaceGates.phase (ODEHeraldedSuccess.successProjector
        (ODECompiledSource.output E (seedCoefficients c))) (-1)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact DysonSingleProgram.Explicit.groverShape_compile
      (ODECoordinateNativeControl.input
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀))
      (ODECoordinateNativeControl.input_isometry
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀))
      (ODECoordinateNativeControl.letter
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))
        (matrixOracle (OmegaG (FLab K M m) K) D₀)
        (sourceFamily (ι := FIota K M) Pw J (phases ω)) (matrixClean hKs D₀ ω₀))
      (GeneralSourceODE.Compiled.program p (sourceFamily (ι := FIota K M) Pw J (phases ω)) E hE)
      (ODEGroverRay.projector (ODECompiledSource.seed E (seedCoefficients c) seed))
      (ODEHeraldedSuccess.successProjector (ODECompiledSource.output E (seedCoefficients c)))
      (ODEGroverRay.projector_isOrthogonalProjection _ hSeedU)
      (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ hOut)
      (ODESourceQueryBudget.matrixWeight (fun _ => 1))
  · intro b
    exact DysonSingleProgram.Explicit.groverShape_compile
      (ODECoordinateNativeControl.input
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀))
      (ODECoordinateNativeControl.input_isometry
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀))
      (ODECoordinateNativeControl.letter
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K))
        (matrixOracle (OmegaG (FLab K M m) K) D₀)
        (sourceFamily (ι := FIota K M) Pw J (phases ω)) (matrixClean hKs D₀ ω₀))
      (GeneralSourceODE.Compiled.program p (sourceFamily (ι := FIota K M) Pw J (phases ω)) E hE)
      (ODEGroverRay.projector (ODECompiledSource.seed E (seedCoefficients c) seed))
      (ODEHeraldedSuccess.successProjector (ODECompiledSource.output E (seedCoefficients c)))
      (ODEGroverRay.projector_isOrthogonalProjection _ hSeedU)
      (ODEHeraldedSuccess.successProjector_isOrthogonalProjection _ hOut)
      (ODESourceQueryBudget.sourceWeight b)
  · exact ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
      (ODECoordinateNativeControl.input_isometry
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀)) _).trans hSeedU
  · exact NativeSparseAttenuation.isometry_comp
      (ODECompiledSource.output E (seedCoefficients c))
      (ODECoordinateNativeControl.input
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀)) hOut
      (ODECoordinateNativeControl.input_isometry
        (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
        (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0
        (matrixClean hKs D₀ ω₀))
  · intro j x
    exact MultiOracleCircuit.Program.eval_unitary _
      (ODECoordinateNativeControl.physicalOracle_unitary _ _ _ _ hO
        (GeneralSourceODE.Compiled.sourceFamily_unitary hPw hJ (phases_norm ω))) x
  rintro x y ⟨G, b, sol, bv, U, ζ, hG, hGint, hmild, hU, hW, hJ0, hJb, hmassB, hsrc, hsolT, hBg,
    hbudget, rfl⟩
  set z := sources (sol 0) bv ω with hzdef
  set B := meshScale sol b t with hBdef
  have hB : 0 < B := meshScale_pos_of_valid hmesh G hG U hU b sol hmild hT.le v hv bv ω cq ζ
    hmassB hsrc hsolT
  set Ecell := cellError σ D x t G with hEcell
  have hE0 : 0 ≤ Ecell := cellError_nonneg σ D x hmesh G
  have hexpE : 0 ≤ Real.exp Ecell - 1 := by linarith [Real.one_le_exp hE0]
  -- the error of the assembled quadrature
  have herr0 := dysonTarget_error hmesh hT.le σ D x G hG hGint U hU b sol hmild v hv bv ω ζ hsrc K
  rw [hzD] at herr0
  have hKtail : expTail (zParam s η T) K ≤ ε / (2000 * (cq * g)) :=
    expTail_truncDegree_le _ _ ε hz hcqg hε hε1
  have hKtail0 : 0 ≤ expTail (zParam s η T) K := expTail_nonneg _ hz.le K
  have hζB : ζ * B + ODESourceBranches.mass z * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) ≤
      ε * B / (1000 * g) := by
    have hBq : ODESourceBranches.mass z * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) ≤
        cq * B * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) :=
      mul_le_mul_of_nonneg_right hmassB (by linarith)
    have hg0 : 0 < g := by linarith
    have htail : cq * B * expTail (zParam s η T) K ≤ ε * B / (2000 * g) := by
      have h := mul_le_mul_of_nonneg_left hKtail (by positivity : (0 : ℝ) ≤ cq * B)
      calc cq * B * expTail (zParam s η T) K ≤ cq * B * (ε / (2000 * (cq * g))) := h
        _ = ε * B / (2000 * g) := by field_simp
    have hbud : ζ * B + cq * B * (Real.exp Ecell - 1) ≤ ε * B / (2000 * g) := by
      have h := mul_le_mul_of_nonneg_right hbudget hB.le
      calc ζ * B + cq * B * (Real.exp Ecell - 1) = (ζ + cq * (Real.exp Ecell - 1)) * B := by ring
        _ ≤ ε / (2000 * g) * B := h
        _ = ε * B / (2000 * g) := by ring
    calc ζ * B + ODESourceBranches.mass z * ((Real.exp Ecell - 1) + expTail (zParam s η T) K)
        ≤ ζ * B + cq * B * ((Real.exp Ecell - 1) + expTail (zParam s η T) K) := by linarith
      _ = (ζ * B + cq * B * (Real.exp Ecell - 1)) + cq * B * expTail (zParam s η T) K := by ring
      _ ≤ ε * B / (2000 * g) + ε * B / (2000 * g) := add_le_add hbud htail
      _ = ε * B / (1000 * g) := by ring
  have herr : ‖dysonTarget σ D x t K v (sol 0) bv ω - sol T‖ ≤ ε * B / (1000 * g) :=
    herr0.trans hζB
  -- positivity of the source mass
  have hy := dysonTarget_norm_le hmesh σ D x K v (sol 0) bv ω
  rw [hzD] at hy
  have hg0 : 0 < g := by linarith
  have hsolT0 : 0 < ‖sol T‖ := norm_pos_iff.mpr hsolT
  have hBsol : ε * B / (1000 * g) ≤ ‖sol T‖ / 1000 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hyne : 0 < ‖dysonTarget σ D x t K v (sol 0) bv ω‖ := by
    have := norm_sub_norm_le (sol T) (dysonTarget σ D x t K v (sol 0) bv ω)
    rw [norm_sub_rev] at this
    linarith
  have hzpos : 0 < ODESourceBranches.mass z := by
    have h1 : 0 < ODESourceBranches.mass z * Real.exp (zParam s η T) := lt_of_lt_of_le hyne hy
    exact pos_of_mul_pos_left h1 (Real.exp_pos _).le
  have hm : 0 < ODESourceBranches.mass z * Real.exp (zParam s η T) := by positivity
  obtain ⟨h1, h2, h3⟩ := herald_window (dysonTarget σ D x t K v (sol 0) bv ω) (sol T)
    (ODESourceBranches.mass z * Real.exp (zParam s η T)) B g ε hB hm hg hε hε1 hBg hy herr
  -- the decoded vector of the actual preparation
  have hprep := phased_prepares (J x) (sol 0) bv ω seed hJ0 hJb
  have hdec : ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed =
      ((2 * (ODESourceBranches.mass z * Real.exp (zParam s η T)) : ℝ) : ℂ)⁻¹ •
        dysonTarget σ D x t K v (sol 0) bv ω := by
    have h := fDecoded hmesh hM hKs σ D K v ω x (J x) z hzpos seed hprep (T := T)
    rw [hzD] at h
    rw [show (2 * (ODESourceBranches.mass z * Real.exp (zParam s η T)) : ℝ) =
      2 * Real.exp (zParam s η T) * ODESourceBranches.mass z by ring]
    exact h
  have hampLe : g * (ODESourceBranches.mass z * Real.exp (zParam s η T)) / B ≤ g' := by
    rw [div_le_iff₀ hB, hg'def, fullAmp]
    have := mul_le_mul_of_nonneg_right hmassB (Real.exp_pos (zParam s η T)).le
    nlinarith [Real.exp_pos (zParam s η T)]
  have hLower : 1 / (4 * g') ≤
      ‖ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed‖ := by
    rw [hdec]
    refine le_trans ?_ h1
    apply one_div_le_one_div_of_le
    · have : 0 < g * (ODESourceBranches.mass z * Real.exp (zParam s η T)) / B := by positivity
      linarith
    · linarith
  have hUpper : ‖ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed‖ ≤
      1 / 2 := by rw [hdec]; exact h2
  have hDir : ‖ODEStateNormalization.unitDirection
      (ODEActualSourceError.decoded E z c (phased (J x) (phases ω)) (p.eval x) seed) -
        ODEStateNormalization.unitDirection (sol T)‖ ≤ ε / 500 := by rw [hdec]; exact h3
  have hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (fullShape K) := by
    have hcount : p.count = 18 * K := fProgram_count hM hKs σ D K t v
    rw [hcount, queryShape_zero]
    unfold fullShape
    push_cast
    apply le_of_eq
    ring
  exact herald_certificate p hO Pw hPw J hJ (phases ω) (phases_norm ω) E hE z c hc seed (sol T)
    hSeed (s : ℝ) 0 (fullShape K) g' ε hg1 hε.le hsolT x hzpos hW hLower hUpper hDir hq
    (GeneralSourceODE.Native.sourceLayout (ι := FIota K M) (n := n) m)
    (matrixLayout (n := n) (Z := Z) (Ks := Ks) (OmegaG (FLab K M m) K)) a0 (matrixClean hKs D₀ ω₀)
    (matrixImage hKs D₀ ω₀) (matrix_valid hKs D₀ ω₀) hSeedU hOut

/-- **Lemma `odel:lem:dyson` on the full time-dependent class** (eq. `odel:eq:dyson`), trial-family
form: `full_dyson_shape` without the amplification shape. -/
theorem full_dyson (D₀ : Data (X × Fin Ks) n Z s) (hM : 0 < M) (σ : Fin M → Fin Ks)
    (t : ℕ → ℝ) (T η g cq ε : ℝ) (hmesh : IsMesh t M T) (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 T) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ∃ (q : ℕ → MultiOracleCircuit.Program
        (fullOracle D₀ (fullDegree s η T g cq ε) M m Pw J ω))
      (ψ : FSpace Ks n Z (fullDegree s η T g cq ε) M m)
      (F : EuclideanSpace ℂ n →L[ℂ] FSpace Ks n Z (fullDegree s η T g cq ε) M m),
      (∀ j x, IsUnitary ((q j).eval x)) ∧
      ∀ x y, FullValid D₀ σ t T η g cq ε hη v ω Pw J seed x y →
        ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (fullAmp s η T g cq)) ψ F x y
          (s : ℝ) 0 (fullShape (fullDegree s η T g cq ε)) (fullAmp s η T g cq) ε := by
  obtain ⟨q, ψ, F, -, -, -, -, -, -, -, -, hU, hC⟩ := full_dyson_shape D₀ hM σ t T η g cq ε hmesh
    hT hη hg hcq hε hε1 v hv ω Pw hPw J hJ seed hSeed
  exact ⟨q, ψ, F, hU, hC⟩

/-- **The paper-form query bound** (eq. `odel:eq:dyson` with explicit constants and `c_q`):
`1274019840 g' queryShape s 0 (K/589824) = 2160 g' K ≤ dysonBound z (c_q ḡ) ε`
`= 16000 c_q ḡ e^z (1 + z + L/log(e + L/z))`, `L = log(4000 c_q ḡ/ε)`. -/
theorem full_bound {s : ℕ} (hs : 0 < s) {T η g cq ε : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hg : 1 ≤ g) (hcq : 1 ≤ cq) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1274019840 * fullAmp s η T g cq *
        ImprovedODEQueryBudget.queryShape (s : ℝ) 0 (fullShape (fullDegree s η T g cq ε)) ≤
      dysonBound (zParam s η T) (cq * g) ε := by
  have hz := zParam_pos hs hη hT
  have hcqg : 1 ≤ cq * g := by nlinarith
  rw [queryShape_zero]
  unfold fullShape fullAmp fullDegree
  have h := cost_le_dysonBound (zParam s η T) (cq * g) ε (Real.exp (zParam s η T)) hz hcqg hε hε1
    le_rfl
  calc 1274019840 * (cq * g * Real.exp (zParam s η T)) *
        ((truncDegree (zParam s η T) (cq * g) ε : ℝ) / 589824)
      = 2160 * (cq * g * Real.exp (zParam s η T)) *
          (truncDegree (zParam s η T) (cq * g) ε : ℝ) := by ring
    _ ≤ _ := h

end

end DysonFullClass
