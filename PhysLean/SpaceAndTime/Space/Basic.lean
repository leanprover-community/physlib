/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.TODO.Basic
import PhysLean.Meta.Linters.Sorry
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Space

In this module, we define the the type `Space d` which corresponds
to `d`-dimensional flat Euclidean space and prove some properties about it.

PhysLean sits downstream of Mathlib, and above we import the necessary Mathlib modules
which contain (perhaps transitively through imports) the definitions and theorems we need.

## Implementation details

The exact implementation of `Space d` into PhysLean is discussed in numerous places
on the Lean Zulip, including:

- https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/Space.20vs.20EuclideanSpace/with/575332888

There is a choice between defining `Space d` as an `abbrev` of `EuclideanSpace ℝ (Fin d)`,
as a `def` of a type with value `EuclideanSpace ℝ (Fin d)` or as a structure
with a field `val : Fin d → ℝ` :

+---------------------------------------------------+---------+-------+-----------+
|                                                   | abbrev  |  def  | structure |
+---------------------------------------------------+---------+-------+-----------+
| allows casting from `EuclideanSpace`              |   yes   |  yes  |    no     |
| carries instances from `EuclideanSpace`           |   yes   |  no   |    no     |
| requires reproving of lemmas from `EuclideanSpace`|   no    |  yes  |    yes    |
+---------------------------------------------------+---------+-------+-----------+

The `structure` is the most conservative choice, as everything needs redefining. However,
there is are two benefits of using it:

1. It allows us to be precise about the instances we define on `Space d`, and makes
  future refactoring of those instances easier.
2. It allows us to give the necessary physics context to results about `Space d`, which
  would not otherwise be possible if we reuse results from Mathlib.

Currently `Space d` has the instances of `Module` (which requires the choice
of a zero), `Norm` and `InnerProductSpace`.
A future refactor should instead give `Space d` the instance of `NormedAddTorsor` and
`MetricSpace` giving it directly the Euclidean distance.

This has not been done yet since `fderiv` requires a `Module` instance.

Because of this, one should be careful to avoid using the explicit zero in `Space d`,
or adding two `Space d` values together. Where possible one should use
the `VAdd (EuclideanSpace ℝ (Fin d)) (Space d)` instance instead.

-/

/-!

## The `Space` type

-/

TODO "HB6RR" "In the above documentation describe the notion of a type, and
  introduce the type `Space d`."

TODO "HB6VC" "Convert `Space` from an `abbrev` to a `def`."

/-- The type `Space d` is the world-volume which corresponds to
 `d` dimensional (flat) Euclidean space with a given (but arbitrary)
choice of length unit, and a given (but arbitrary) choice of zero.

The default value of `d` is `3`. Thus `Space = Space 3`-/
structure Space (d : ℕ := 3) where
  /-- The underlying map `Fin d → ℝ` associated with a point in `Space`. -/
  val : Fin d → ℝ

namespace Space

lemma eq_of_val {d} {p q : Space d} (h : p.val = q.val) :
    p = q := by
  cases p
  cases q
  congr

@[simp]
lemma val_eq_iff {d} {p q : Space d} :
    p.val = q.val ↔ p = q := by
  apply Iff.intro
  · exact eq_of_val
  · intro h
    rw [h]

/-!

## B. Instances on `Space`

-/

/-!

## B.1. Instance of coercion to functions

-/

instance {d} : CoeFun (Space d) (fun _ => Fin d → ℝ) where
  coe p := p.val

@[ext]
lemma eq_of_apply {d} {p q : Space d}
    (h : ∀ i : Fin d, p i = q i) : p = q := by
  apply eq_of_val
  funext i
  exact h i

/-!

## B.1. Instance of an additive commutative monoid

-/

instance {d} : Add (Space d) where
  add p q := ⟨fun i => p.val i + q.val i⟩

@[simp]
lemma add_val {d: ℕ} (x y : Space d) :
    (x + y).val = x.val + y.val := rfl

@[simp]
lemma add_apply {d : ℕ} (x y : Space d) (i : Fin d) :
    (x + y) i = x i + y i := by
  simp [add_val]

instance {d} : Zero (Space d) where
  zero := ⟨fun _ => 0⟩

@[simp]
lemma zero_val {d : ℕ} : (0 : Space d).val = fun _ => 0 := rfl

@[simp]
lemma zero_apply {d : ℕ} (i : Fin d) :
    (0 : Space d) i = 0 := by
  simp [zero_val]

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

/-!

## B.2. Instance of a module over `ℝ`

-/

instance {d} : SMul ℝ (Space d) where
  smul c p := ⟨fun i => c * p.val i⟩

@[simp]
lemma smul_val {d : ℕ} (c : ℝ) (p : Space d) :
    (c • p).val = fun i => c * p.val i := rfl

@[simp]
lemma smul_apply {d : ℕ} (c : ℝ) (p : Space d) (i : Fin d) :
    (c • p) i = c * (p i) := by rfl

instance {d} : Module ℝ (Space d) where
  one_smul x := by
    ext i
    simp
  mul_smul a b x := by
    ext i
    simp only [smul_apply]
    ring
  smul_add a x y := by
    ext i
    simp only [smul_apply, add_apply]
    ring
  smul_zero a := by
    ext i
    simp
  add_smul a b x := by
    ext i
    simp only [smul_apply, add_apply]
    ring
  zero_smul x := by
    ext i
    simp

/-!

## B.3. Addition of Euclidean spaces

-/

noncomputable instance : VAdd (EuclideanSpace ℝ (Fin d)) (Space d) where
  vadd v s := ⟨fun i => v i + s.val i⟩

@[simp]
lemma vadd_val {d} (v : EuclideanSpace ℝ (Fin d)) (s : Space d) :
    (v +ᵥ s).val = fun i => v i + s.val i := rfl

@[simp]
lemma vadd_apply {d} (v : EuclideanSpace ℝ (Fin d))
    (s : Space d) (i : Fin d) :
    (v +ᵥ s) i = v i + s i := by rfl

lemma vadd_transitive {d} (s1 s2 : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), v +ᵥ s1 = s2 := by
  use WithLp.toLp 2 fun i => s2 i - s1 i
  ext i
  simp

lemma eq_vadd_zero {d} (s : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), s = v +ᵥ (0 : Space d) := by
  obtain ⟨v, h⟩ := vadd_transitive 0 s
  use v
  rw [h]

@[simp]
lemma smul_vadd_zero {d} (k : ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    k • (v +ᵥ (0 : Space d)) = (k • v) +ᵥ (0 : Space d) := by
  ext i
  simp

noncomputable instance : AddAction (EuclideanSpace ℝ (Fin d)) (Space d) where
  zero_vadd s := by
    ext i
    simp
  add_vadd v1 v2 s := by
    ext i
    simp only [vadd_apply, PiLp.add_apply]
    ring

@[simp]
lemma add_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    (v1 +ᵥ (0 : Space d)) + (v2 +ᵥ (0 : Space d)) = (v1 + v2) +ᵥ (0 : Space d) := by
  ext i
  simp

/-!

## B.3. Instance of an inner product space

-/

noncomputable instance {d} : Norm (Space d) where
  norm p := √ (∑ i, (p i)^2)

lemma norm_eq {d} (p : Space d) : ‖p‖ = √ (∑ i, (p i) ^ 2) := by
  rfl

@[simp]
lemma abs_eval_le_norm {d} (p : Space d) (i : Fin d) :
    |p i| ≤ ‖p‖ := by
  simp [norm_eq]
  refine Real.abs_le_sqrt ?_
  trans ∑ j ∈ {i}, (p j) ^ 2
  · simp
  refine Finset.sum_le_univ_sum_of_nonneg (fun i => by positivity)

lemma norm_sq_eq {d} (p : Space d) :
    ‖p‖ ^ 2 = ∑ i, (p i) ^ 2 := by
  rw [norm_eq]
  refine Real.sq_sqrt ?_
  positivity

lemma point_dim_zero_eq (p : Space 0) : p = 0 := by
  ext i
  fin_cases i

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
  zsmul z p := ⟨fun i => z * p.val i⟩
  neg_add_cancel p := by
    ext i
    simp
  zsmul_zero' p := by
    ext i
    simp
  zsmul_succ' n p := by
    ext i
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast,
      Int.cast_one, add_apply]
    ring
  zsmul_neg' n p := by
    ext i
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one, neg_add_rev, Nat.succ_eq_add_one,
      Int.cast_add, Int.cast_natCast, Int.cast_one, neg_apply]
    ring

@[simp]
lemma sub_apply {d} (p q : Space d) (i : Fin d) :
    (p - q) i = p i - q i := by
  simp [sub_eq_add_neg, neg_apply, add_apply]

@[simp]
lemma sub_val {d} (p q : Space d) :
    (p - q).val = fun i => p.val i - q.val i := by rfl

@[simp]
lemma vadd_zero_sub_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    (v1 +ᵥ (0 : Space d)) - (v2 +ᵥ (0 : Space d)) = (v1 - v2) +ᵥ (0 : Space d) := by
  ext i
  simp [sub_apply, vadd_apply]

noncomputable instance {d} : SeminormedAddCommGroup (Space d) where
  dist_self x := by
    simp [norm_eq]
  dist_comm x y := by
    simp [norm_eq]
    congr
    funext i
    ring
  dist_triangle := by
    intros x y z
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    obtain ⟨v3, rfl⟩ := eq_vadd_zero z
    simp [vadd_zero_sub_vadd_zero, norm_vadd_zero]
    exact norm_sub_le_norm_sub_add_norm_sub v1 v2 v3

@[simp]
lemma dist_eq {d} (p q : Space d) :
    dist p q = ‖p - q‖ := by
  rfl

noncomputable instance : NormedAddCommGroup (Space d) where
  eq_of_dist_eq_zero := by
    intro x y h
    simp at h
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    simp only [vadd_zero_sub_vadd_zero, norm_vadd_zero] at h
    congr
    exact eq_of_dist_eq_zero h

instance {d} : Inner ℝ (Space d) where
  inner p q := ∑ i, p i * q i

@[simp]
lemma inner_vadd_zero {d} (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (v1 +ᵥ (0 : Space d)) (v2 +ᵥ (0 : Space d)) = Inner.inner ℝ v1 v2 := by
  simp [inner, vadd_apply]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma inner_apply {d} (p q : Space d) :
    inner ℝ p q = ∑ i, p i * q i := by rfl

instance {d} : InnerProductSpace ℝ (Space d) where
  norm_smul_le a x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simp only [smul_vadd_zero, norm_vadd_zero, Real.norm_eq_abs]
    exact norm_smul_le a v
  norm_sq_eq_re_inner x := by
    obtain ⟨v, rfl⟩ := eq_vadd_zero x
    simp
  conj_inner_symm x y := by
    simp [inner_apply]
    congr
    funext i
    ring
  add_left x y z := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    obtain ⟨v3, rfl⟩ := eq_vadd_zero z
    simp only [add_vadd_zero, inner_vadd_zero]
    exact InnerProductSpace.add_left v1 v2 v3
  smul_left x y a := by
    obtain ⟨v1, rfl⟩ := eq_vadd_zero x
    obtain ⟨v2, rfl⟩ := eq_vadd_zero y
    simp only [smul_vadd_zero, inner_vadd_zero, conj_trivial]
    exact InnerProductSpace.smul_left v1 v2 a

/-!

## B.4. Instance of a measurable space

-/

instance {d : ℕ} : MeasurableSpace (Space d) := borel (Space d)

instance {d : ℕ} : BorelSpace (Space d) where
  measurable_eq := by rfl

TODO "HB6YZ" "In the above documentation describe what an instance is, and why
  it is useful to have instances for `Space d`."

TODO "HB6WN" "After TODO 'HB6VC', give `Space d` the necessary instances
  using `inferInstanceAs`."
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

-/

TODO "HB6Z4" "In the above documentation describe the notion of a basis
  in Lean."

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
  simp [apply_eq_basis_repr_apply]
  congr 1
  exact Lean.Grind.eq_congr' rfl rfl

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
    ⟪basis.repr p, v⟫_ℝ = ⟪p, basis.repr.symm v⟫_ℝ := by
  exact LinearIsometryEquiv.inner_map_eq_flip basis.repr p v

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
lemma coord_contDiff {i} : ContDiff ℝ ∞ (fun x : Space d => x.coord i) := by
  change ContDiff ℝ ∞ (coordCLM i)
  fun_prop

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

/-- The continuous linear equivalence between `Space d` and the corresponding `Pi` type. -/
def equivPi (d : ℕ) :
    Space d ≃L[ℝ] Π (_ : Fin d), ℝ := LinearEquiv.toContinuousLinearEquiv <|
  {
    toFun := fun p i => p i
    map_add' p1 p2 := by funext i; simp
    map_smul' p r := by funext i; simp
    invFun := fun f => ⟨f⟩
  }

@[fun_prop]
lemma mk_continuous {d : ℕ} :
    Continuous (fun (f : Fin d → ℝ) => (⟨f⟩ : Space d)) := (equivPi d).symm.continuous

@[fun_prop]
lemma mk_differentiable {d : ℕ} :
    Differentiable ℝ (fun (f : Fin d → ℝ) => (⟨f⟩ : Space d)) := (equivPi d).symm.differentiable

@[fun_prop]
lemma mk_contDiff {d n : ℕ} :
    ContDiff ℝ n (fun (f : Fin d → ℝ) => (⟨f⟩ : Space d)) := (equivPi d).symm.contDiff

@[simp]
lemma fderiv_mk {d : ℕ} (f : Fin d → ℝ) :
    fderiv ℝ Space.mk f = (equivPi d).symm := by
  change fderiv ℝ (equivPi d).symm f = _
  rw [@ContinuousLinearEquiv.fderiv]

@[simp]
lemma fderiv_val {d : ℕ} (p : Space d) :
    fderiv ℝ Space.val p = (equivPi d) := by
  change fderiv ℝ (equivPi d) p = _
  rw [@ContinuousLinearEquiv.fderiv]

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
  trans (‖s.unit‖) ^ 2
  · rw [norm_sq_eq]
  · rw [s.norm]
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
  fin_cases i
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

lemma oneEquiv_symm_measurePreserving : MeasurePreserving oneEquiv.symm volume volume := by
  exact LinearIsometryEquiv.measurePreserving oneEquiv.symm

instance {d : ℕ} : Nontrivial (Space d.succ) := by
  refine { exists_pair_ne := ?_ }
  use 0, basis 0
  simp only [Nat.succ_eq_add_one, ne_eq]
  by_contra hn
  have h0 : (basis 0 : Space d.succ) 0 = 1 := by simp
  rw [← hn] at h0
  simp at h0

instance : Subsingleton (Space 0) := by
  apply Subsingleton.intro
  intro x y
  ext i
  fin_cases i
end Space
