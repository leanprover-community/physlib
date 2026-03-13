/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.SpaceAndTime.Space.Basic
public import Mathlib.Geometry.Manifold.Diffeomorph
/-!

# The structure of a module on Space

The scope of this module is to define on `Space d` the structure of a `Module`
(aka vector space), a `Norm` and an `InnerProductSpace`, and give properties of these structures.

These instances require certain non-canonical choices to be made, for example the choice
of a zero and for a basis, a choice of orientation.

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


lemma eq_vadd_zero {d} (s : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), s = v +ᵥ (0 : Space d) := by
  obtain ⟨v, h⟩ := vadd_transitive 0 s
  use v
  rw [h]

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

## A.3. Instance of an inner product space

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

@[simp]
lemma dist_eq_norm {d} (p q : Space d) :
    dist p q = ‖p - q‖ := rfl

noncomputable instance : NormedAddCommGroup (Space d) where


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

## A.4. Instance of a measurable space

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
lemma mk_contDiff {d  : ℕ} {n : WithTop ℕ∞}:
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

@[fun_prop]
lemma contDiffOn_vadd (s : Space d) :
    ContDiffOn ℝ ω (fun (v : EuclideanSpace ℝ (Fin d)) => v +ᵥ s) Set.univ := by
  rw [contDiffOn_univ]
  refine fun_comp ?_ ?_
  · exact mk_contDiff (n := ω)
  · fun_prop

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
    (μ : Fin d) (f : M → Space d) (hf : Differentiable ℝ f) (m dm : M):
    fderiv ℝ f m dm μ  = fderiv ℝ (fun m' => f m' μ) m dm := by
  trans fderiv ℝ (Space.coordCLM μ ∘ fun m' => f m') m dm
  · rw [fderiv_comp _ (by fun_prop) (by fun_prop), ContinuousLinearMap.fderiv,
      ContinuousLinearMap.coe_comp', Function.comp_apply]
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

/-!

## Relation to tangent space

-/

open Manifold in
/-- A diffeomorphism between the two different manifold structures on `Space d`,
  that equivalent to `manifoldStructure d` and that equivalent to `𝓘(ℝ, Space d)` -/
noncomputable def modelDiffeo {d} :
    Diffeomorph (manifoldStructure d) 𝓘(ℝ, Space d) (Space d) (Space d) ⊤ where
  toFun p :=  p
  invFun p :=  p
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine contMDiff_iff.mpr ⟨continuous_id', fun x y => ?_⟩
    simp [manifoldStructure]
    fun_prop
  contMDiff_invFun := by
    refine contMDiff_iff.mpr ⟨continuous_id', fun x y => ?_⟩
    simp [manifoldStructure]
    fun_prop

@[simp]
lemma modelDiffeo_apply (p : Space d) :
    modelDiffeo p = p := rfl

open Manifold in
/-- The derivative of `modelDiffeo` provides an equivalence between
  `Space d` and `EuclideanSpace ℝ (Fin d)`. This equivalences takes the basis
  of `EuclideanSpace ℝ (Fin d)` to the basis of `Space d`, and vice versa. -/
lemma basis_eq_mfderiv_modelDiffeo_single (d : ℕ) (μ : Fin d) (x : Space d) :
    basis μ = mfderiv (manifoldStructure d) 𝓘(ℝ, Space d) (modelDiffeo (d := d)) x
      (EuclideanSpace.single μ 1) := by
  simp [mfderiv]
  rw [if_pos (modelDiffeo.mdifferentiable (WithTop.top_ne_zero)).mdifferentiableAt]
  change _ = fderiv ℝ (manifoldStructure d).symm (manifoldStructure d x) (EuclideanSpace.single μ 1)
  simp [manifoldStructure]
  ext i
  rw [fderiv_space_components _ _ (by fun_prop)]
  simp only [vadd_apply, fderiv_add_const]
  change _ = fderiv ℝ (EuclideanSpace.proj i) (x -ᵥ Classical.choice _) (EuclideanSpace.single μ 1)
  simp [basis_apply]
  congr 1
  exact Eq.propIntro (fun a => Eq.symm a) fun a => (Eq.symm a)

end Space
