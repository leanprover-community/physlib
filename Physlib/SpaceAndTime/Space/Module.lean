/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Origin
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.Cases
/-!

# The structure of a module on Space

The scope of this module is to define on `Space d` the structure of a `Module`
(aka vector space), a `Norm` and an `InnerProductSpace`, and give properties of these structures.

These instances require certain non-canonical choices to be made, for example the choice
of a zero and for a basis, a choice of orientation.

## Instances in Lean

In Lean, an `instance` supplies a typeclass automatically. When a definition or
theorem needs a structure such as `AddCommGroup (Space d)`, `Module ℝ (Space d)`,
`NormedAddCommGroup (Space d)`, `InnerProductSpace ℝ (Space d)`, or
`MeasurableSpace (Space d)`, typeclass inference searches for the corresponding
instance and inserts it without the user passing it explicitly.

These instances make `Space d` usable with standard mathematical notation and
with the Mathlib API. For example, they allow expressions such as `p + q`,
`c • p`, `‖p‖`, `inner ℝ p q`, and measurable-set arguments involving the Borel
structure. They also make general theorems about modules, normed groups, inner
product spaces, and measurable spaces apply directly to `Space d`.

For `Space d`, these instances are intentional choices rather than inherited
facts: the type was defined as a structure instead of an abbreviation for
Euclidean space. In particular, the additive and module structures choose an
origin, while the norm, inner product, and Borel structure choose the standard
Euclidean coordinate geometry.

-/

@[expose] public section

namespace Space

/-!

## A.1. Instance of an additive commutative monoid

-/

instance {d} : Add (Space d) where
  add p q := ⟨fun i => p.val i + q.val i⟩

@[simp]
lemma add_val {d: ℕ} (x y : Space d) :
    (x + y).val = x.val + y.val := rfl

@[simp]
lemma add_apply {d : ℕ} (x y : Space d) (i : Fin d) :
    (x + y) i = x i + y i := by
  simp

instance {d} : AddCommMonoid (Space d) where
  add_assoc a b c:= by
    apply eq_of_val
    simp only [add_val]
    ring
  zero_add a := by
    apply eq_of_val
    simp only [zero_val, add_val, add_eq_right]
    rfl
  add_zero a := by
    apply eq_of_val
    simp only [zero_val, add_val, add_eq_left]
    rfl
  add_comm a b := by
    apply eq_of_val
    simp only [add_val]
    ring
  nsmul n a := ⟨fun i => n • a.val i⟩

@[simp]
lemma nsmul_val {d : ℕ} (n : ℕ) (a : Space d) :
    (n • a).val = fun i => n • a.val i := rfl

@[simp]
lemma nsmul_apply {d : ℕ} (n : ℕ) (a : Space d) (i : Fin d) :
    (n • a) i = n • (a i) := by rfl

lemma eq_vadd_zero {d} (s : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), s = v +ᵥ (0 : Space d) := by
  obtain ⟨v, rfl⟩ := vadd_transitive 0 s
  exact ⟨v, rfl⟩

@[simp]
lemma add_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    (v1 +ᵥ (0 : Space d)) + (v2 +ᵥ (0 : Space d)) = (v1 + v2) +ᵥ (0 : Space d) := by
  ext i
  simp

/-!

## A.2. Instance of a module over `ℝ`

-/

instance {d} : SMul ℝ (Space d) where
  smul c p := ⟨fun i => c * p.val i⟩

@[simp]
lemma smul_val {d : ℕ} (c : ℝ) (p : Space d) :
    (c • p).val = fun i => c * p.val i := rfl

@[simp]
lemma smul_apply {d : ℕ} (c : ℝ) (p : Space d) (i : Fin d) :
    (c • p) i = c * (p i) := by rfl

@[simp]
lemma smul_vadd_zero {d} (k : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    k • (v +ᵥ (0 : Space d)) = (k • v) +ᵥ (0 : Space d) := by
  ext i
  simp

instance {d} : Module ℝ (Space d) where
  one_smul x := by
    ext i
    simp
  mul_smul a b x := by
    ext i
    simp [mul_assoc]
  smul_add a x y := by
    ext i
    simp [mul_add]
  smul_zero a := by
    ext i
    simp
  add_smul a b x := by
    ext i
    simp [add_mul]
  zero_smul x := by
    ext i
    simp

/-!

## A.3. Instance of an inner product space

-/

noncomputable instance {d} : Norm (Space d) where
  norm p := √ (∑ i, (p i)^2)

lemma norm_eq {d} (p : Space d) : ‖p‖ = √ (∑ i, (p i) ^ 2) := by
  rfl

@[simp]
lemma abs_eval_le_norm {d} (p : Space d) (i : Fin d) :
    |p i| ≤ ‖p‖ := by
  rw [norm_eq]
  exact Real.abs_le_sqrt
    (Finset.single_le_sum (f := fun j => (p j) ^ 2) (fun j _ => by positivity) (Finset.mem_univ i))

lemma norm_sq_eq {d} (p : Space d) :
    ‖p‖ ^ 2 = ∑ i, (p i) ^ 2 := by
  rw [norm_eq]
  exact Real.sq_sqrt (by positivity)

lemma point_dim_zero_eq (p : Space 0) : p = 0 :=
  Subsingleton.elim p 0

@[simp]
lemma norm_vadd_zero {d} (v : EuclideanSpace ℝ (Fin d)) :
    ‖v +ᵥ (0 : Space d)‖ = ‖v‖ := by
  simp [norm_eq, PiLp.norm_eq_of_L2]

instance : Neg (Space d) where
  neg p := ⟨fun i => - (p.val i)⟩

@[simp]
lemma neg_val {d : ℕ} (p : Space d) :
    (-p).val = fun i => - (p.val i) := rfl

@[simp]
lemma neg_apply {d : ℕ} (p : Space d) (i : Fin d) :
    (-p) i = - (p i) := by rfl

noncomputable instance {d} : AddCommGroup (Space d) where
  zsmul z p := ⟨fun i => z • p.val i⟩
  neg_add_cancel p := by
    ext i
    simp

@[simp]
lemma sub_apply {d} (p q : Space d) (i : Fin d) :
    (p - q) i = p i - q i := by
  simp [sub_eq_add_neg]

@[simp]
lemma sub_val {d} (p q : Space d) :
    (p - q).val = fun i => p.val i - q.val i := by rfl

@[simp]
lemma vadd_zero_sub_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    (v1 +ᵥ (0 : Space d)) - (v2 +ᵥ (0 : Space d)) = (v1 - v2) +ᵥ (0 : Space d) := by
  ext i
  simp

@[simp]
lemma dist_eq_norm {d} (p q : Space d) :
    dist p q = ‖p - q‖ := rfl

noncomputable instance {d} : SeminormedAddCommGroup (Space d) where
  dist_eq x y := by
    simp [dist_eq_norm, norm_eq, sub_apply]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)

noncomputable instance : NormedAddCommGroup (Space d) where
  dist_eq x y := by
    simp [dist_eq_norm, norm_eq, sub_apply]
    exact congrArg _ (Finset.sum_congr rfl fun i _ => by ring)

instance {d} : Inner ℝ (Space d) where
  inner p q := ∑ i, p i * q i

@[simp]
lemma inner_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (v1 +ᵥ (0 : Space d)) (v2 +ᵥ (0 : Space d)) = Inner.inner ℝ v1 v2 := by
  simp [inner, vadd_apply, mul_comm]

lemma inner_apply {d} (p q : Space d) :
    inner ℝ p q = ∑ i, p i * q i := by rfl

instance {d} : InnerProductSpace ℝ (Space d) where
  norm_smul_le a x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simpa only [smul_vadd_zero, norm_vadd_zero, Real.norm_eq_abs] using norm_smul_le a v
  norm_sq_eq_re_inner x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simp
  conj_inner_symm x y := by
    simp [inner_apply, mul_comm]
  add_left x y z := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    obtain ⟨v3, rfl⟩ := eq_vadd_zero z
    simpa only [add_vadd_zero, inner_vadd_zero] using InnerProductSpace.add_left v1 v2 v3
  smul_left x y a := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    simpa only [smul_vadd_zero, inner_vadd_zero, conj_trivial]
      using InnerProductSpace.smul_left v1 v2 a

lemma norm_smul_sphere {d : ℕ} (n : ↑(Metric.sphere (0 : Space d) 1))
    {r : ℝ} (hr : 0 ≤ r) :
    ‖(r • (n : Space d))‖ = r := by
  simp [norm_smul, mem_sphere_zero_iff_norm.mp n.2, abs_of_nonneg hr]

/-!

## A.4. Instance of a measurable space

-/

noncomputable instance {d : ℕ} : MeasurableSpace (Space d) := borel (Space d)

instance {d : ℕ} : BorelSpace (Space d) where
  measurable_eq := by rfl

/-!

## The norm on `Space`

-/

/-!

## Inner product

-/

lemma inner_eq_sum {d} (p q : Space d) :
    inner ℝ p q = ∑ i, p i * q i := by
  simp [inner]

@[simp]
lemma sum_apply {ι : Type} [Fintype ι] (f : ι → Space d) (i : Fin d) :
    (∑ x, f x) i = ∑ x, f x i := by
  let P (ι : Type) [Fintype ι] : Prop := ∀ (f : ι → Space d) (i : Fin d), (∑ x, f x) i = ∑ x, f x i
  have h1 : P ι := by
    apply Fintype.induction_empty_option
    · intro α β h e h f i
      rw [← @e.sum_comp _, h, ← @e.sum_comp _]
    · simp [P]
    · intro α _ h f i
      simp only [Fintype.sum_option, add_apply, add_right_inj]
      rw [h]
  exact h1 f i

/-!

## Basis

A basis in Lean is typically represented by `Module.Basis ι R M`: an indexed
family of vectors in an `R`-module `M` such that every element of `M` has a
unique finite linear expansion in those vectors. The index type `ι` names the
basis vectors, and the map `basis.repr` gives the coordinate representation of a
vector with respect to that basis.

For inner product spaces, Lean also has `OrthonormalBasis ι R M`. This is a
basis whose vectors are orthonormal, packaged together with a linear isometric
equivalence between `M` and its coordinate space. It can be coerced to the
underlying `Module.Basis` using `basis.toBasis` when only the linear-algebraic
basis structure is needed.

The standard basis below is indexed by `Fin d`, so the basis vector `basis i`
is the unit vector in the `i`th coordinate direction of `Space d`.

-/

/-- The standard basis of Space based on `Fin d`. -/
noncomputable def basis {d} : OrthonormalBasis (Fin d) ℝ (Space d) where
  repr := {
    toFun p := WithLp.toLp 2 fun i => p i
    invFun := fun v => ⟨v⟩
    left_inv := by
      intro p
      rfl
    right_inv := by
      intro v
      rfl
    map_add' := by
      intro v1 v2
      rfl
    map_smul' := by
      intro c v
      rfl
    norm_map' := by
      intro x
      simp [norm_eq, PiLp.norm_eq_of_L2]}

lemma apply_eq_basis_repr_apply {d} (p : Space d) (i : Fin d) :
    p i = basis.repr p i := by
  simp [basis]

@[simp]
lemma basis_repr_apply {d} (p : Space d) (i : Fin d) :
    basis.repr p i = p i := by
  simp [apply_eq_basis_repr_apply]

@[simp]
lemma basis_repr_symm_apply {d} (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    basis.repr.symm v i = v i := by rfl

lemma basis_apply {d} (i j : Fin d) :
    basis i j = if i = j then 1 else 0 := by
  simp [apply_eq_basis_repr_apply, eq_comm]

@[simp]
lemma basis_self {d} (i : Fin d) : basis i i = 1 := by
  simp [basis_apply]

@[simp high]
lemma inner_basis {d} (p : Space d) (i : Fin d) :
    inner ℝ p (basis i) = p i := by
  simp [inner_eq_sum, basis_apply]

@[simp high]
lemma basis_inner {d} (i : Fin d) (p : Space d) :
    inner ℝ (basis i) p = p i := by
  simp [inner_eq_sum, basis_apply]

open InnerProductSpace

lemma basis_repr_inner_eq {d} (p : Space d) (v : EuclideanSpace ℝ (Fin d)) :
    ⟪basis.repr p, v⟫_ℝ = ⟪p, basis.repr.symm v⟫_ℝ :=
  LinearIsometryEquiv.inner_map_eq_flip basis.repr p v

instance {d : ℕ} : FiniteDimensional ℝ (Space d) :=
  Module.Basis.finiteDimensional_of_finite (h := basis.toBasis)

@[simp]
lemma finrank_eq_dim {d : ℕ} : Module.finrank ℝ (Space d) = d := by
  simp [Module.finrank_eq_nat_card_basis (basis.toBasis)]

@[simp]
lemma rank_eq_dim {d : ℕ} : Module.rank ℝ (Space d) = d := by
  simp [rank_eq_card_basis (basis.toBasis)]

@[simp]
lemma fderiv_basis_repr {d} (p : Space d) :
    fderiv ℝ basis.repr p = basis.repr.toContinuousLinearMap := by
  change fderiv ℝ basis.repr.toContinuousLinearMap p = _
  rw [ContinuousLinearMap.fderiv]

@[simp]
lemma fderiv_basis_repr_symm {d} (v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ basis.repr.symm v = basis.repr.symm.toContinuousLinearMap := by
  change fderiv ℝ basis.repr.symm.toContinuousLinearMap v = _
  rw [ContinuousLinearMap.fderiv]

lemma basis_induction_on {d} {P : Space d → Prop}
    (hb : ∀ i, P (basis i)) (hzero : P 0)
    (hadd : ∀ p1 p2, P p1 → P p2 → P (p1 + p2))
    (hsmul : ∀ (c : ℝ) p, P p → P (c • p)) (p : Space d) : P p := by
  rw [← OrthonormalBasis.sum_repr basis p]
  exact Finset.sum_induction _ P hadd hzero fun i _ => hsmul _ _ (hb i)
/-!

## Coordinates

-/

/-- The standard coordinate functions of Space based on `Fin d`.

The notation `𝔁 μ p` can be used for this. -/
noncomputable def coord (μ : Fin d) (p : Space d) : ℝ :=
  inner ℝ p (basis μ)

lemma coord_apply (μ : Fin d) (p : Space d) :
    coord μ p = p μ := by
  simp [coord]

/-- The standard coordinate functions of Space based on `Fin d`, as a continuous linear map. -/
noncomputable def coordCLM {d} (μ : Fin d) : Space d →L[ℝ] ℝ where
  toFun := coord μ
  map_add' := fun p q => by
    simp [coord, basis, inner_add_left]
  map_smul' := fun c p => by
    simp [coord, basis, inner_smul_left]
  cont := by
    unfold coord
    fun_prop

open ContDiff

@[fun_prop]
lemma coord_contDiff {i} : ContDiff ℝ ∞ (fun x : Space d => x.coord i) :=
  (coordCLM i).contDiff

lemma coordCLM_apply (μ : Fin d) (p : Space d) :
    coordCLM μ p = coord μ p := by
  rfl

@[inherit_doc coord]
scoped notation "𝔁" => coord

@[fun_prop]
lemma eval_continuous {d} (i : Fin d) :
    Continuous (fun p : Space d => p i) := by
  convert (coordCLM i).continuous
  simp [coordCLM_apply, coord]

@[fun_prop]
lemma eval_differentiable {d} (i : Fin d) :
    Differentiable ℝ (fun p : Space d => p i) := by
  convert (coordCLM i).differentiable
  simp [coordCLM_apply, coord]

@[fun_prop]
lemma eval_contDiff {d n} (i : Fin d) :
    ContDiff ℝ n (fun p : Space d => p i) := by
  convert (coordCLM i).contDiff
  simp [coordCLM_apply, coord]

@[fun_prop]
lemma eval_hasTemperateGrowth {d} (i : Fin d) :
    Function.HasTemperateGrowth (fun p : Space d => p i) := by
  convert (coordCLM i).hasTemperateGrowth
  simp [coordCLM_apply, coord]

/-- The continuous linear equivalence between `Space d` and the corresponding `Pi` type. -/
noncomputable def equivPi (d : ℕ) :
    Space d ≃L[ℝ] Π (_ : Fin d), ℝ := LinearEquiv.toContinuousLinearEquiv <|
  {
    toFun := fun p i => p i
    map_add' p1 p2 := by funext i; simp
    map_smul' p r := by funext i; simp
    invFun := fun f => ⟨f⟩
  }

/-!

## Basic differentiablity conditions

-/

@[fun_prop]
lemma mk_continuous {d : ℕ} :
    Continuous (fun (f : Fin d → ℝ) => (⟨f⟩ : Space d)) := (equivPi d).symm.continuous

@[fun_prop]
lemma mk_differentiable {d : ℕ} :
    Differentiable ℝ (fun (f : Fin d → ℝ) => (⟨f⟩ : Space d)) := (equivPi d).symm.differentiable

@[fun_prop]
lemma mk_contDiff {d : ℕ} {n : WithTop ℕ∞}:
    ContDiff ℝ n (fun (f : Fin d → ℝ) => (⟨f⟩ : Space d)) := (equivPi d).symm.contDiff

@[simp]
lemma fderiv_mk {d : ℕ} (f : Fin d → ℝ) :
    fderiv ℝ Space.mk f = (equivPi d).symm := by
  change fderiv ℝ (equivPi d).symm f = _
  rw [ContinuousLinearEquiv.fderiv]

@[simp]
lemma fderiv_val {d : ℕ} (p : Space d) :
    fderiv ℝ Space.val p = (equivPi d) := by
  change fderiv ℝ (equivPi d) p = _
  rw [ContinuousLinearEquiv.fderiv]

@[simp]
lemma fderiv_eval_apply {d : ℕ} (p y : Space d) (i : Fin d) :
    fderiv ℝ (fun p => p.val i) p y = y i := by
  have h : (fun p : Space d => p.val i) = ⇑(coordCLM i) :=
    funext fun q => by simp [coordCLM, coord_apply]
  rw [h, ContinuousLinearMap.fderiv]
  simp [coordCLM, coord_apply]

@[fun_prop]
lemma contDiffOn_vadd (s : Space d) :
    ContDiffOn ℝ ω (fun (v : EuclideanSpace ℝ (Fin d)) => v +ᵥ s) Set.univ :=
  contDiffOn_univ.mpr <| fun_comp (mk_contDiff (n := ω)) (by fun_prop)

@[fun_prop]
lemma vadd_differentiable {d} (s : Space d) :
    Differentiable ℝ (fun (v : EuclideanSpace ℝ (Fin d)) => v +ᵥ s) :=
  mk_differentiable.comp <| by fun_prop

@[fun_prop]
lemma contDiffOn_vsub (s1 : Space d) :
    ContDiffOn ℝ ω (fun (s : Space d) => s -ᵥ s1) Set.univ :=
  contDiffOn_univ.mpr <| fun_comp (PiLp.contDiff_toLp) (by fun_prop)

@[fun_prop]
lemma vsub_differentiable {d} (s1 : Space d) :
    Differentiable ℝ (fun (s : Space d) => s -ᵥ s1) :=
  (PiLp.contDiff_toLp.differentiable (NeZero.ne' 2).symm).comp (by fun_prop)

lemma fderiv_space_components {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : M → Space d) (hf : Differentiable ℝ f) (m dm : M) :
    fderiv ℝ f m dm μ = fderiv ℝ (fun m' => f m' μ) m dm := by
  trans fderiv ℝ (Space.coordCLM μ ∘ fun m' => f m') m dm
  · rw [fderiv_comp _ (by fun_prop) (by fun_prop), ContinuousLinearMap.fderiv,
      ContinuousLinearMap.coe_comp, Function.comp_apply]
    simp [coordCLM, coord_apply]
  · congr
    ext i
    simp [coordCLM, coord_apply]

/-!

## Directions

-/

/-- Notion of direction where `unit` returns a unit vector in the direction specified. -/
structure Direction (d : ℕ := 3) where
  /-- Unit vector specifying the direction. -/
  unit : Space d
  norm : ‖unit‖ = 1

/-- Direction of a `Space` value with respect to the origin. -/
noncomputable def toDirection {d : ℕ} (x : Space d) (h : x ≠ 0) : Direction d where
  unit := (‖x‖⁻¹) • x
  norm := norm_smul_inv_norm h

@[simp]
lemma direction_unit_sq_sum {d} (s : Direction d) :
    ∑ i : Fin d, (s.unit i) ^ 2 = 1 := by
  rw [← norm_sq_eq, s.norm]
  simp

/-!

## One equiv

-/

/-- The linear isometric equivalence between `Space 1` and `ℝ`. -/
noncomputable def oneEquiv : Space 1 ≃ₗᵢ[ℝ] ℝ where
  toFun x := x 0
  invFun x := ⟨fun _ => x⟩
  left_inv x := by
    ext i; fin_cases i; simp
  right_inv x := by simp
  map_add' x y := by rfl
  map_smul' c x := by rfl
  norm_map' x := by
    simp only [Fin.isValue, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
    rw [norm_eq]
    simp only [Fin.isValue, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    exact Eq.symm (Real.sqrt_sq_eq_abs (x 0))

lemma oneEquiv_coe :
    (oneEquiv : Space 1 → ℝ) = fun x => x 0 := by
  rfl

lemma oneEquiv_symm_coe :
    (oneEquiv.symm : ℝ → Space 1) = (fun x => ⟨fun _ => x⟩) := by
  rfl

lemma oneEquiv_symm_apply (x : ℝ) (i : Fin 1) :
    oneEquiv.symm x i = x := by
  rfl

lemma oneEquiv_continuous :
    Continuous (oneEquiv : Space 1 → ℝ) := by
  simp [oneEquiv_coe]
  fun_prop

lemma oneEquiv_symm_continuous :
    Continuous (oneEquiv.symm : ℝ → Space 1) := by
  simp [oneEquiv_symm_coe]
  fun_prop

/-- The continuous linear equivalence between `Space 1` and `ℝ`. -/
noncomputable def oneEquivCLE : Space 1 ≃L[ℝ] ℝ where
  toLinearEquiv := oneEquiv
  continuous_toFun := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    erw [oneEquiv_coe]
    fun_prop
  continuous_invFun := by
    simp only [LinearEquiv.invFun_eq_symm]
    erw [oneEquiv_symm_coe]
    fun_prop

open MeasureTheory
lemma oneEquiv_measurableEmbedding : MeasurableEmbedding oneEquiv where
  injective := oneEquiv.injective
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    change MeasurableSet (⇑oneEquivCLE '' s)
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    exact oneEquiv.symm.continuous.measurable hs

lemma oneEquiv_symm_measurableEmbedding : MeasurableEmbedding oneEquiv.symm where
  injective := oneEquiv.symm.injective
  measurable := by fun_prop
  measurableSet_image' := by
    intro s hs
    change MeasurableSet (⇑oneEquivCLE.symm '' s)
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    exact oneEquiv.continuous.measurable hs

lemma oneEquiv_measurePreserving : MeasurePreserving oneEquiv volume volume :=
  LinearIsometryEquiv.measurePreserving oneEquiv

lemma oneEquiv_symm_measurePreserving : MeasurePreserving oneEquiv.symm volume volume :=
  LinearIsometryEquiv.measurePreserving oneEquiv.symm

/-!

## Relation to tangent space

-/

open Manifold in
/-- A diffeomorphism between the two different manifold structures on `Space d`,
  that equivalent to `𝓡 d` and that equivalent to `𝓘(ℝ, Space d)` -/
noncomputable def modelDiffeo {d} : Diffeomorph (𝓡 d) 𝓘(ℝ, Space d) (Space d) (Space d) ⊤ where
  toFun p := p
  invFun p := p
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine contMDiff_iff.mpr ⟨continuous_id', fun x y => ?_⟩
    simpa [← Function.id_def, homEuclideanSpaceSpace, chartAt_self_eq] using by fun_prop
  contMDiff_invFun := by
    apply contMDiff_iff.mpr ⟨by simpa using by fun_prop, fun x y => ?_⟩
    simpa [homEuclideanSpaceSpace, chartAt_self_eq] using by fun_prop

@[simp]
lemma modelDiffeo_apply {d : ℕ} (p : Space d) :
    modelDiffeo p = p := rfl

set_option backward.isDefEq.respectTransparency false in
open Manifold in
/-- The derivative of `modelDiffeo` provides an equivalence between
  `Space d` and `EuclideanSpace ℝ (Fin d)`. This equivalences takes the basis
  of `EuclideanSpace ℝ (Fin d)` to the basis of `Space d`, and vice versa. -/
lemma basis_eq_mfderiv_modelDiffeo_single (d : ℕ) (μ : Fin d) (x : Space d) :
    basis μ = mfderiv (𝓡 d) 𝓘(ℝ, Space d) (modelDiffeo (d := d)) x
      (EuclideanSpace.single μ 1) := by
  simp only [modelDiffeo_apply, mfderiv, writtenInExtChartAt, extChartAt,
    OpenPartialHomeomorph.extend, OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_source,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, PartialEquiv.refl_coe, Homeomorph.symm_toOpenPartialHomeomorph,
    OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_symm,
    OpenPartialHomeomorph.toFun_eq_coe, Homeomorph.toOpenPartialHomeomorph_apply,
    CompTriple.comp_eq, modelWithCornersSelf_coe, Set.range_id,
    OpenPartialHomeomorph.coe_toPartialEquiv_symm, Homeomorph.toOpenPartialHomeomorph_symm_apply,
    fderivWithin_univ]
  rw [ite_eq_left (modelDiffeo.mdifferentiable (WithTop.top_ne_zero)).mdifferentiableAt]
  ext i
  have h := fderiv_space_components i ((⇑modelDiffeo ∘ ⇑(homEuclideanSpaceSpace d)))
    (by simpa [Function.comp_def, homEuclideanSpaceSpace] using by fun_prop)
    (((homEuclideanSpaceSpace d).symm x)) ((EuclideanSpace.single μ 1))
  convert! h.symm
  simp only [basis_apply, homEuclideanSpaceSpace, PiLp.continuousLinearEquiv_symm_apply,
    Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Function.comp_apply, modelDiffeo_apply,
    PiLp.continuousLinearEquiv_apply, Homeomorph.homeomorph_mk_coe_symm, Equiv.symm_mk]
  change _ = fderiv ℝ (EuclideanSpace.proj i) _ (EuclideanSpace.single μ 1)
  simp only [ContinuousLinearMap.fderiv, PiLp.proj_apply, PiLp.single_apply]
  congr 1
  exact Eq.propIntro (fun a => Eq.symm a) fun a => (Eq.symm a)

/-!

## Properties of vadd with module structure

-/

lemma norm_vadd_le_add {d} (v : EuclideanSpace ℝ (Fin d)) (s : Space d) :
    ‖v +ᵥ s‖ ≤ ‖v‖ + ‖s‖ := by
  trans ‖s - (-v +ᵥ (0 : Space d))‖
  · apply le_of_eq
    congr
    ext i
    simp only [vadd_apply, sub_apply, PiLp.neg_apply, zero_apply, add_zero, sub_neg_eq_add]
    ring
  · apply (norm_sub_le _ _).trans <| le_of_eq _
    simp only [norm_vadd_zero, norm_neg]
    ring

@[fun_prop]
lemma differentiable_vadd {d} (v : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ (fun (s : Space d) => v +ᵥ s) :=
  mk_differentiable.comp <| by fun_prop

@[simp]
lemma fderiv_vadd {d} (v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun s => v +ᵥ s) = fun (_ : Space d) => ContinuousLinearMap.id ℝ _ := by
  ext s ds i
  rw [fderiv_space_components]
  · simp [fderiv_const_add]
  · fun_prop

@[fun_prop]
lemma vadd_hasTemperateGrowth {d} (v : EuclideanSpace ℝ (Fin d)) :
    Function.HasTemperateGrowth (fun s : Space d => v +ᵥ s) := by
  apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖v‖)
  · simp [fderiv_vadd]
  · fun_prop
  · intro x
    simp only [pow_one]
    apply (norm_vadd_le_add _ _).trans
    nlinarith [norm_nonneg v, norm_nonneg x]

end Space
