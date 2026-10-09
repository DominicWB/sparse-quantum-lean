import GateEfficientHamiltonian.Simulator.BlockTransfer

/-!
# Qubit registers with a Hilbert payload

`Reg W Q` is the Hilbert space of a register of qubit wires `W` carrying a
payload Hilbert space `Q`: an `L²` function on computational configurations
`W → Bool`.  Every operation of the gate-level simulator is built from three
exact constructions:

* `localOp ι F`: an operator `F` on the wires in the range of an injection
  `ι`, chosen according to the configuration of the remaining wires;
* `matOp M`: a finite complex matrix on configurations, tensored with the
  identity of the payload;
* `perm e`: a permutation of configurations (reversible classical logic).

Adjoints, products and unitarity follow structurally from Hilbert direct sums
and fixed isometric layout changes; no operator is postulated.
-/

namespace SparseHamiltonian.GateCircuit

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators
set_option synthInstance.maxHeartbeats 200000

/-- Computational-basis configurations of a set of qubit wires. -/
abbrev Cfg (W : Type*) := W → Bool

/-- A register of qubit wires `W` carrying a payload Hilbert space `Q`. -/
abbrev Reg (W : Type*) (Q : Type*) := PiLp 2 (fun _ : Cfg W => Q)

section Basic

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- An operator specified by its output coordinates. -/
def ofCoords (F : Cfg W → (Reg W Q →L[ℂ] Q)) : Reg W Q →L[ℂ] Reg W Q :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg W => Q)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi F

omit [Fintype W] [DecidableEq W] in
@[simp] theorem ofCoords_apply (F : Cfg W → (Reg W Q →L[ℂ] Q)) (ψ : Reg W Q) (x : Cfg W) :
    ofCoords F ψ x = F x ψ := rfl

/-- The coordinate projection at one configuration. -/
abbrev coord (x : Cfg W) : Reg W Q →L[ℂ] Q := PiLp.proj 2 (fun _ : Cfg W => Q) x

omit [Fintype W] [DecidableEq W] in
@[simp] theorem coord_apply (x : Cfg W) (ψ : Reg W Q) : coord x ψ = ψ x := rfl

/-- A computational basis configuration carrying the payload vector `q`. -/
def bas (x : Cfg W) (q : Q) : Reg W Q := WithLp.toLp 2 (fun y => if y = x then q else 0)

omit [DecidableEq W] [InnerProductSpace ℂ Q] in
@[simp] theorem bas_apply (x : Cfg W) (q : Q) (y : Cfg W) :
    bas x q y = if y = x then q else 0 := rfl

omit [DecidableEq W] [InnerProductSpace ℂ Q] in
theorem bas_add (x : Cfg W) (q q' : Q) : bas x (q + q') = bas x q + bas x q' := by
  apply PiLp.ext; intro y; by_cases h : y = x <;> simp [h]

omit [DecidableEq W] in
theorem bas_smul (x : Cfg W) (c : ℂ) (q : Q) : bas x (c • q) = c • bas x q := by
  apply PiLp.ext; intro y; by_cases h : y = x <;> simp [h]

theorem inner_bas_left (x : Cfg W) (q : Q) (ψ : Reg W Q) :
    inner ℂ (bas x q) ψ = inner ℂ q (ψ x) := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ x) h

theorem inner_bas_right (x : Cfg W) (q : Q) (ψ : Reg W Q) :
    inner ℂ ψ (bas x q) = inner ℂ (ψ x) q := by
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy; simp [hy]
  · intro h; exact absurd (Finset.mem_univ x) h

omit [InnerProductSpace ℂ Q] in
theorem norm_bas (x : Cfg W) (q : Q) : ‖bas x q‖ = ‖q‖ := by
  have h : ‖bas x q‖ ^ 2 = ‖q‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd (Finset.mem_univ x) h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

omit [InnerProductSpace ℂ Q] in
/-- Every register vector is the sum of its basis components. -/
theorem sum_bas (ψ : Reg W Q) : ∑ x, bas x (ψ x) = ψ := by
  apply PiLp.ext
  intro y
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro x _ hx; simp [Ne.symm hx]
  · intro h; exact absurd (Finset.mem_univ y) h

/-- Two operators agree once they agree on every basis configuration and payload. -/
theorem ext_bas {K : Type*} [AddCommGroup K] [Module ℂ K]
    (f g : Reg W Q →ₗ[ℂ] K) (h : ∀ x q, f (bas x q) = g (bas x q)) : f = g := by
  apply LinearMap.ext
  intro ψ
  rw [← sum_bas ψ, map_sum, map_sum]
  exact Finset.sum_congr rfl (fun x _ => h x (ψ x))

theorem ext_bas_clm (f g : Reg W Q →L[ℂ] Reg W Q) (h : ∀ x q, f (bas x q) = g (bas x q)) :
    f = g := by
  have := ext_bas (f : Reg W Q →ₗ[ℂ] Reg W Q) (g : Reg W Q →ₗ[ℂ] Reg W Q) h
  exact ContinuousLinearMap.coe_injective this

end Basic

/-! ### Permutations of configurations -/

section Perm

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- Reversible classical logic: a permutation of computational configurations. -/
def perm (e : Cfg W ≃ Cfg W) : Reg W Q ≃ₗᵢ[ℂ] Reg W Q :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ Q e

@[simp] theorem perm_apply (e : Cfg W ≃ Cfg W) (ψ : Reg W Q) (y : Cfg W) :
    perm e ψ y = ψ (e.symm y) := rfl

theorem perm_bas (e : Cfg W ≃ Cfg W) (x : Cfg W) (q : Q) :
    perm e (bas x q) = bas (e x) q := by
  apply PiLp.ext
  intro y
  simp only [perm_apply, bas_apply]
  by_cases h : y = e x
  · subst h; simp
  · have : e.symm y ≠ x := by intro hx; apply h; rw [← hx]; simp
    simp [h, this]

/-- The permutation operator as a continuous linear map. -/
abbrev permOp (e : Cfg W ≃ Cfg W) : Reg W Q →L[ℂ] Reg W Q :=
  (perm (Q := Q) e).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem permOp_apply (e : Cfg W ≃ Cfg W) (ψ : Reg W Q) (y : Cfg W) :
    permOp e ψ y = ψ (e.symm y) := rfl

theorem permOp_comp (e f : Cfg W ≃ Cfg W) :
    permOp (Q := Q) e ∘L permOp f = permOp (f.trans e) := by
  ext ψ y; rfl

theorem permOp_refl : permOp (Q := Q) (Equiv.refl (Cfg W)) = 1 := by
  ext ψ y; rfl

theorem permOp_adjoint [CompleteSpace Q] (e : Cfg W ≃ Cfg W) :
    (permOp (Q := Q) e)† = permOp e.symm := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_right ℂ
  intro φ
  rw [adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply]
  simp only [permOp_apply, Equiv.symm_symm]
  exact (Fintype.sum_equiv e _ _ (fun x => by simp)).symm

end Perm

/-! ### Exposing a set of wires -/

section Layout

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The wires outside the range of `ι`. -/
abbrev Out (ι : A → W) := {w : W // ∀ a, ι a ≠ w}

/-- Glue an outside configuration and a configuration of the exposed wires. -/
def joinCfg (ι : A → W) (x' : Cfg (Out ι)) (b : Cfg A) : Cfg W :=
  fun w => if h : ∃ a, ι a = w then b (Classical.choose h)
    else x' ⟨w, fun a ha => h ⟨a, ha⟩⟩

omit [Fintype W] [DecidableEq A] in
theorem joinCfg_apply_ι {ι : A → W} (hι : Function.Injective ι) (x' : Cfg (Out ι))
    (b : Cfg A) (a : A) : joinCfg ι x' b (ι a) = b a := by
  have h : ∃ a', ι a' = ι a := ⟨a, rfl⟩
  simp only [joinCfg, dif_pos h]
  exact congrArg b (hι (Classical.choose_spec h))

omit [Fintype W] [DecidableEq A] in
theorem joinCfg_apply_out (ι : A → W) (x' : Cfg (Out ι)) (b : Cfg A) (w : Out ι) :
    joinCfg ι x' b w.1 = x' w := by
  have h : ¬ ∃ a, ι a = w.1 := fun ⟨a, ha⟩ => w.2 a ha
  simp only [joinCfg, dif_neg h]

/-- The restriction of a configuration to the outside wires. -/
def outPart (ι : A → W) (x : Cfg W) : Cfg (Out ι) := fun w => x w.1

/-- Split a configuration into its outside and exposed parts. -/
def splitCfg (ι : A → W) (hι : Function.Injective ι) : Cfg W ≃ Cfg (Out ι) × Cfg A where
  toFun x := (outPart ι x, fun a => x (ι a))
  invFun p := joinCfg ι p.1 p.2
  left_inv x := by
    funext w
    by_cases h : ∃ a, ι a = w
    · obtain ⟨a, rfl⟩ := h
      exact joinCfg_apply_ι hι _ _ a
    · exact joinCfg_apply_out ι (outPart ι x) _ ⟨w, fun a ha => h ⟨a, ha⟩⟩
  right_inv p := by
    rcases p with ⟨x', b⟩
    apply Prod.ext
    · funext w
      exact joinCfg_apply_out ι x' b w
    · funext a
      exact joinCfg_apply_ι hι x' b a

omit [Fintype W] [DecidableEq A] in
theorem outPart_joinCfg (ι : A → W) (x' : Cfg (Out ι)) (b : Cfg A) :
    outPart ι (joinCfg ι x' b) = x' := by
  funext w
  exact joinCfg_apply_out ι x' b w

omit [Fintype W] [DecidableEq A] in
theorem joinCfg_self {ι : A → W} (hι : Function.Injective ι) (x : Cfg W) :
    joinCfg ι (outPart ι x) (fun a => x (ι a)) = x :=
  (splitCfg ι hι).left_inv x

/-- Overwrite the exposed wires of `x` by `b`. -/
abbrev overwrite (ι : A → W) (x : Cfg W) (b : Cfg A) : Cfg W := joinCfg ι (outPart ι x) b

/-- The canonical representative with every exposed wire cleared. -/
abbrev clearCfg (ι : A → W) (x : Cfg W) : Cfg W := overwrite ι x (fun _ => false)

/-- The isometric layout exposing the wires in the range of `ι`. -/
def layout (ι : A → W) (hι : Function.Injective ι) :
    Reg W Q ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Cfg (Out ι) => Reg A Q) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ Q
    ((splitCfg ι hι).trans (Equiv.sigmaEquivProd (Cfg (Out ι)) (Cfg A)).symm)).trans
  (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Cfg (Out ι)) (_ : Cfg A) => Q))

omit [CompleteSpace Q] in
theorem layout_apply {ι : A → W} (hι : Function.Injective ι) (ψ : Reg W Q)
    (x' : Cfg (Out ι)) (b : Cfg A) : layout ι hι ψ x' b = ψ (joinCfg ι x' b) := rfl

omit [CompleteSpace Q] in
theorem layout_symm_apply {ι : A → W} (hι : Function.Injective ι)
    (Φ : PiLp 2 (fun _ : Cfg (Out ι) => Reg A Q)) (x : Cfg W) :
    (layout ι hι).symm Φ x = Φ (outPart ι x) (fun a => x (ι a)) := by
  have hψ : layout ι hι (WithLp.toLp 2 (fun y : Cfg W => Φ (outPart ι y) (fun a => y (ι a))))
      = Φ := by
    apply PiLp.ext
    intro x'
    apply PiLp.ext
    intro b
    rw [layout_apply]
    change Φ (outPart ι (joinCfg ι x' b)) (fun a => joinCfg ι x' b (ι a)) = Φ x' b
    rw [outPart_joinCfg]
    have hb : (fun a => joinCfg ι x' b (ι a)) = b := funext (fun a => joinCfg_apply_ι hι x' b a)
    rw [hb]
  have h2 := congrArg (layout ι hι).symm hψ
  rw [LinearIsometryEquiv.symm_apply_apply] at h2
  rw [← h2]

/-- The column of a register vector through the configuration `x`. -/
def slice (ι : A → W) (ψ : Reg W Q) (x : Cfg W) : Reg A Q :=
  WithLp.toLp 2 (fun b => ψ (overwrite ι x b))

omit [Fintype W] [DecidableEq A] [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q] in
@[simp] theorem slice_apply (ι : A → W) (ψ : Reg W Q) (x : Cfg W) (b : Cfg A) :
    slice ι ψ x b = ψ (overwrite ι x b) := rfl

/-- An operator on the exposed wires, selected by the configuration of the
other wires (read through the canonical cleared representative). -/
def localOp (ι : A → W) (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) : Reg W Q →L[ℂ] Reg W Q :=
  (layout ι hι).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun x' : Cfg (Out ι) => F (joinCfg ι x' (fun _ => false))))

theorem localOp_apply {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) (ψ : Reg W Q) (x : Cfg W) :
    localOp ι hι F ψ x = F (clearCfg ι x) (slice ι ψ x) (fun a => x (ι a)) := by
  rw [localOp, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, layout_symm_apply,
    LinearIsometryEquiv.symm_symm, WeightedClock.diagonal_apply]
  rfl

theorem localOp_comp {ι : A → W} (hι : Function.Injective ι)
    (F G : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) :
    localOp ι hι F ∘L localOp ι hι G = localOp ι hι (fun x => F x ∘L G x) := by
  unfold localOp
  rw [← mul_def, ← map_mul, mul_def, WeightedClock.diagonal_comp]

theorem localOp_mul {ι : A → W} (hι : Function.Injective ι)
    (F G : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) :
    localOp ι hι F * localOp ι hι G = localOp ι hι (fun x => F x * G x) :=
  localOp_comp hι F G

theorem localOp_one {ι : A → W} (hι : Function.Injective ι) :
    localOp (Q := Q) ι hι (fun _ => 1) = 1 := by
  unfold localOp
  rw [WeightedClock.diagonal_one, map_one]

theorem localOp_adjoint {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) :
    (localOp ι hι F)† = localOp ι hι (fun x => (F x)†) := by
  unfold localOp
  rw [← star_eq_adjoint, ← map_star, star_eq_adjoint, WeightedClock.diagonal_adjoint]

theorem localOp_star {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) :
    star (localOp ι hι F) = localOp ι hι (fun x => star (F x)) := by
  rw [star_eq_adjoint, localOp_adjoint]
  rfl

theorem localOp_isUnitary {ι : A → W} (hι : Function.Injective ι)
    (F : Cfg W → (Reg A Q →L[ℂ] Reg A Q)) (hF : ∀ x, IsUnitary (F x)) :
    IsUnitary (localOp ι hι F) := by
  constructor
  · rw [localOp_star, localOp_mul]
    simp only [(hF _).1]
    exact localOp_one hι
  · rw [localOp_star, localOp_mul]
    simp only [(hF _).2]
    exact localOp_one hι

theorem localOp_congr {ι : A → W} (hι : Function.Injective ι)
    (F G : Cfg W → (Reg A Q →L[ℂ] Reg A Q))
    (h : ∀ x, F (clearCfg ι x) = G (clearCfg ι x)) :
    localOp ι hι F = localOp ι hι G := by
  ext ψ x
  rw [localOp_apply, localOp_apply, h x]

end Layout

/-! ### Finite matrices tensored with the payload identity -/

section Mat

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A finite matrix on configurations, acting trivially on the payload. -/
def matOp (M : Matrix (Cfg A) (Cfg A) ℂ) : Reg A Q →L[ℂ] Reg A Q :=
  ofCoords (fun b => ∑ c, M b c • coord c)

omit [CompleteSpace Q] in
theorem matOp_apply (M : Matrix (Cfg A) (Cfg A) ℂ) (ψ : Reg A Q) (b : Cfg A) :
    matOp M ψ b = ∑ c, M b c • ψ c := by
  simp [matOp, ofCoords_apply]

omit [CompleteSpace Q] in
theorem matOp_mul (M N : Matrix (Cfg A) (Cfg A) ℂ) :
    matOp (Q := Q) M ∘L matOp N = matOp (M * N) := by
  ext ψ b
  simp only [comp_apply, matOp_apply, Finset.smul_sum, smul_smul, Matrix.mul_apply,
    Finset.sum_smul]
  rw [Finset.sum_comm]

omit [CompleteSpace Q] in
theorem matOp_one : matOp (Q := Q) (1 : Matrix (Cfg A) (Cfg A) ℂ) = 1 := by
  ext ψ b
  rw [matOp_apply, Finset.sum_eq_single b]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · intro h; exact absurd (Finset.mem_univ b) h

theorem matOp_adjoint (M : Matrix (Cfg A) (Cfg A) ℂ) :
    (matOp (Q := Q) M)† = matOp M.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply ext_inner_right ℂ
  intro φ
  rw [adjoint_inner_left, PiLp.inner_apply, PiLp.inner_apply]
  simp only [matOp_apply, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  simp [RCLike.star_def]

theorem matOp_isUnitary (M : Matrix (Cfg A) (Cfg A) ℂ)
    (h1 : M.conjTranspose * M = 1) (h2 : M * M.conjTranspose = 1) :
    IsUnitary (matOp (Q := Q) M) := by
  constructor
  · rw [star_eq_adjoint, matOp_adjoint, mul_def, matOp_mul, h1, matOp_one]
  · rw [star_eq_adjoint, matOp_adjoint, mul_def, matOp_mul, h2, matOp_one]

end Mat

/-! ### Single-wire operations -/

section Qubit

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- A one-qubit matrix as a matrix on the configurations of a single wire. -/
def qubitMat (u : Matrix Bool Bool ℂ) : Matrix (Cfg Unit) (Cfg Unit) ℂ :=
  fun b c => u (b ()) (c ())

theorem sum_cfgUnit {M : Type*} [AddCommMonoid M] (f : Bool → M) :
    (∑ c : Cfg Unit, f (c ())) = ∑ b : Bool, f b :=
  Fintype.sum_equiv (Equiv.funUnique Unit Bool) _ _ (fun _ => rfl)

theorem qubitMat_mul (u v : Matrix Bool Bool ℂ) :
    qubitMat u * qubitMat v = qubitMat (u * v) := by
  funext b c
  simp only [Matrix.mul_apply, qubitMat]
  exact sum_cfgUnit (fun e => u (b ()) e * v e (c ()))

theorem qubitMat_one : qubitMat (1 : Matrix Bool Bool ℂ) = 1 := by
  funext b c
  simp only [qubitMat, Matrix.one_apply]
  have : (b () = c ()) ↔ b = c := by
    constructor
    · intro h; funext u; cases u; exact h
    · intro h; rw [h]
  by_cases h : b = c
  · simp [h]
  · simp [h, this.not.mpr h]

theorem qubitMat_conjTranspose (u : Matrix Bool Bool ℂ) :
    (qubitMat u).conjTranspose = qubitMat u.conjTranspose := by
  funext b c
  rfl

omit [Fintype W] [DecidableEq W] in
theorem single_injective (t : W) : Function.Injective (fun _ : Unit => t) :=
  fun a b _ => Subsingleton.elim a b

omit [Fintype W] in
theorem joinCfg_single (t : W) (x : Cfg W) (c : Cfg Unit) :
    overwrite (fun _ : Unit => t) x c = Function.update x t (c ()) := by
  funext w
  by_cases hw : w = t
  · subst hw
    rw [Function.update_self]
    exact joinCfg_apply_ι (single_injective w) _ c ()
  · rw [Function.update_of_ne hw]
    exact joinCfg_apply_out (fun _ : Unit => t) (outPart _ x) c ⟨w, fun _ h => hw h.symm⟩

omit [Fintype W] in
theorem clearCfg_single (t : W) (x : Cfg W) :
    clearCfg (fun _ : Unit => t) x = Function.update x t false := by
  rw [clearCfg, joinCfg_single]

/-- A one-qubit matrix on wire `t`, chosen by the configuration of the other wires. -/
def condOp (t : W) (u : Cfg W → Matrix Bool Bool ℂ) : Reg W Q →L[ℂ] Reg W Q :=
  localOp (fun _ : Unit => t) (single_injective t) (fun x => matOp (qubitMat (u x)))

theorem condOp_apply (t : W) (u : Cfg W → Matrix Bool Bool ℂ) (ψ : Reg W Q) (x : Cfg W) :
    condOp t u ψ x = ∑ b : Bool, u (Function.update x t false) (x t) b •
      ψ (Function.update x t b) := by
  rw [condOp, localOp_apply, matOp_apply, clearCfg_single]
  simp only [slice_apply, joinCfg_single, qubitMat]
  exact sum_cfgUnit (fun b => u (Function.update x t false) (x t) b •
    ψ (Function.update x t b))

theorem condOp_comp (t : W) (u v : Cfg W → Matrix Bool Bool ℂ) :
    condOp (Q := Q) t u ∘L condOp t v = condOp t (fun x => u x * v x) := by
  unfold condOp
  rw [localOp_comp]
  congr 1
  funext x
  rw [matOp_mul, qubitMat_mul]

theorem condOp_one (t : W) : condOp (Q := Q) t (fun _ => 1) = 1 := by
  unfold condOp
  simp only [qubitMat_one, matOp_one]
  exact localOp_one _

theorem condOp_adjoint (t : W) (u : Cfg W → Matrix Bool Bool ℂ) :
    (condOp (Q := Q) t u)† = condOp t (fun x => (u x).conjTranspose) := by
  unfold condOp
  rw [localOp_adjoint]
  congr 1
  funext x
  rw [matOp_adjoint, qubitMat_conjTranspose]

theorem condOp_isUnitary (t : W) (u : Cfg W → Matrix Bool Bool ℂ)
    (hu : ∀ x, (u x).conjTranspose * u x = 1 ∧ u x * (u x).conjTranspose = 1) :
    IsUnitary (condOp (Q := Q) t u) := by
  unfold condOp
  apply localOp_isUnitary
  intro x
  apply matOp_isUnitary
  · rw [qubitMat_conjTranspose, qubitMat_mul, (hu x).1, qubitMat_one]
  · rw [qubitMat_conjTranspose, qubitMat_mul, (hu x).2, qubitMat_one]

/-- Only the configuration of the other wires selects the matrix. -/
theorem condOp_congr (t : W) (u v : Cfg W → Matrix Bool Bool ℂ)
    (h : ∀ x, u (Function.update x t false) = v (Function.update x t false)) :
    condOp (Q := Q) t u = condOp t v := by
  ext ψ x
  rw [condOp_apply, condOp_apply, h x]

end Qubit

end

end SparseHamiltonian.GateCircuit
